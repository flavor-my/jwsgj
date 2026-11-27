from __future__ import annotations  # noqa: I001
import ast
import difflib
import io
import json
import logging
import os
import re
import tokenize
from collections import Counter
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any, NamedTuple
from jwsgj.build_safe_write import (
    FixSafetyNet,
    normalize_post_write_regression,
    preflight_write_snapshot,
    restore_written_original,
)
from jwsgj.diag_detector_assembly import aaf_verify_diag
from jwsgj.diag_guard_injection_enforce import record_session_write
from jwsgj.diag_guard_io import (
    SourceReadError,
    _inside_any_span,
    _literal_token_spans,
    atomic_replace_bytes,
    check_path_traversal,
    decode_source_strict,
    detect_newline,
    register_l2l3_write_verifier,
    write_backup_bytes,
)
from jwsgj.diag_guard_state import (
    READ_BEFORE_WRITE_GUARD,
    SecurityConstraintSet,
    _contains_sensitive_assignment,
    enforce_read_before_write,
    restore_file_bytes,
    snapshot_file_bytes,
)
from jwsgj.diag_regression_guard import (
    EQUIVALENCE_GUARD_MAX_TEST_CASES,
    EQUIVALENCE_GUARD_TIMEOUT_SEC,
    BehaviorRegressionGuard,
    describe_behavior_regression,
)
from jwsgj.diag_split_gate import (
    aaf_verify_patch_precheck,
    check_fixed_source_syntax,
    comment_docstring_sync_error,
)
from jwsgj.diag_split_plan import detect_new_patch_style_fixes
from jwsgj.diag_symbol_surface import detect_hallucinated_api
from jwsgj.diag_types_defs import aaf_reject
from jwsgj.diag_types_normalize import as_str, strip_bom
from jwsgj.fix_safety_boundary import (
    FixRiskLevel,
    classify_risk,
    normalize_risk_level,
    scan_boundary_guard,
    semantic_rejections,
)
from jwsgj.fix_safety_verify import (
    VERIFY_LAYERS,
    InlineVerifier,
    LayerConfig,
    VerifyStatus,
    post_write_import_check,
    verify_regression,
)
from jwsgj.hallucination_norms import (
    check_process_norms,
    detect_new_p0_api_calls,
    verify_api_existence,
)
from jwsgj.log_config import log_swallowed, safe_write_audit
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.skill_profile import python_import_roots
logger = logging.getLogger(__name__)
_DEFAULT_SOURCE_ENCODING = "utf-8"
_DEFAULT_SKILL_DIR = ""
_DEFAULT_REQUIRE_AI_REVIEW = True
_RISK_GATED_LAYERS: dict[str, tuple[FixRiskLevel, ...]] = {
    "L2_import": (FixRiskLevel.CAUTION, FixRiskLevel.DANGEROUS),
    "L3_test": (FixRiskLevel.DANGEROUS,),
    "L4_runtime": (FixRiskLevel.DANGEROUS,),
}
@dataclass
class FixVerificationResult:
    passed: bool = True
    risk_level: FixRiskLevel = FixRiskLevel.SAFE
    layers: dict[str, dict[str, Any]] = field(default_factory=dict)
    error: str = ""
    rolled_back: bool = False
    filepath: str = ""
    side_effects: list[dict[str, Any]] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "risk_level": self.risk_level.value,
            "layers": dict(self.layers.items()),
            "error": self.error,
            "rolled_back": self.rolled_back,
            "filepath": self.filepath,
            "side_effects": self.side_effects,
            "warnings": self.warnings,
        }
@dataclass(frozen=True)
class _SourceSnapshot:
    text: str
    raw: bytes
    encoding: str
def _read_source(
    filepath: str, context: str,
) -> tuple[_SourceSnapshot | None, str | None]:
    try:
        with open(filepath, "rb") as f:
            raw = f.read()
        text, encoding = decode_source_strict(raw)
        return _SourceSnapshot(text=text, raw=raw, encoding=encoding), None
    except (OSError, SourceReadError) as e:
        logger.warning("%s: 读取原始文件失败: %s", context, e, exc_info=True)
        return None, f"无法读取原始文件: {e}"
def _adapted_source_text(fixed_source: str, original_text: str) -> str:
    if not isinstance(fixed_source, str):
        return fixed_source
    text = strip_bom(fixed_source)
    if not isinstance(original_text, str) or not original_text:
        return text
    eol = detect_newline(original_text)
    return text.replace("\r\n", "\n").replace("\r", "\n").replace("\n", eol)
def _encode_source_payload(fixed_source: str, original_text: str) -> bytes:
    encoding = tokenize.detect_encoding(io.BytesIO(
        fixed_source.encode(_DEFAULT_SOURCE_ENCODING)).readline)[0]
    return _adapted_source_text(fixed_source, original_text).encode(encoding)
def _candidate_bytes_from_snapshot(original_bytes: bytes,
                                   fixed_source: str) -> bytes:
    original_text, _ = decode_source_strict(original_bytes)
    return _encode_source_payload(fixed_source, original_text)
def _candidate_ownership_error(filepath: str,
                               candidate_bytes: bytes) -> str | None:
    try:
        current_bytes = snapshot_file_bytes(filepath)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[FixSafety] 恢复前读取磁盘内容失败 %s: %s",
                       filepath, exc)
        return f"恢复前读取磁盘失败: {exc}"
    if current_bytes != candidate_bytes:
        return "磁盘内容不等于本通道候选，拒绝覆盖可能的并发修改"
    return None
def _atomic_replace_write(
    filepath: str, candidate_bytes: bytes,
) -> tuple[bool, str]:
    try:
        atomic_replace_bytes(
            filepath, candidate_bytes,
            prefix=f".{os.path.basename(filepath)}.safe_fix_",
            label="安全修复临时产物")
    except (OSError, ValueError) as e:
        logger.warning("safe_fix_file: 写入失败: %s", e)
        return False, f"写入失败: {e}"
    return True, ""
@dataclass(frozen=True)
class _RestoreContext:
    net: Any
    filepath: str
    source: _SourceSnapshot
    result: FixVerificationResult
    candidate_bytes: bytes | None = None
    @property
    def original_source(self) -> str:
        return self.source.text
def _restore_original(ctx: _RestoreContext) -> tuple[bool, str, str]:
    restore_ok, channel, restore_err = restore_written_original(
        ctx.net, ctx.filepath, ctx.original_source)
    if restore_ok:
        try:
            restore_file_bytes(ctx.filepath, ctx.source.raw)
        except Exception as exc:  # noqa: BLE001
            ctx.net.mark_backed_up(ctx.filepath)
            return False, channel, f"原字节复核恢复失败: {exc}"
        return True, channel, ""
    try:
        restore_file_bytes(ctx.filepath, ctx.source.raw)
    except Exception as exc:  # noqa: BLE001
        ctx.net.mark_backed_up(ctx.filepath)
        return False, "", f"{restore_err}; 原字节恢复失败: {exc}"
    ctx.net.mark_rolled_back(ctx.filepath)
    return True, "memory", ""
def _restore_after_failure(
    ctx: _RestoreContext,
    stage: str,
    error_label: str,
    primary_error: str,
) -> None:
    filepath, result = ctx.filepath, ctx.result
    if ctx.candidate_bytes is not None:
        ownership_error = _candidate_ownership_error(
            filepath, ctx.candidate_bytes)
        if ownership_error is not None:
            ctx.net.mark_backed_up(filepath)
            result.passed = False
            result.rolled_back = False
            result.error = (
                f"{stage}，未执行恢复: {primary_error}；{ownership_error}")
            logger.error("CRITICAL: %s，%s: %s",
                         stage, filepath, ownership_error)
            return
    restore_ok, channel, restore_err = _restore_original(ctx)
    result.passed = False
    result.rolled_back = restore_ok
    if restore_ok:
        src_desc = "备份" if channel == "backup" else "内存"
        result.error = f"{stage}，已从{src_desc}恢复原始文件: {primary_error}"
        logger.warning("%s，已回滚 %s: %s", stage, filepath, primary_error)
    else:
        result.error = (
            f"{stage}且恢复原始文件也失败: "
            f"{error_label}={primary_error}, 恢复错误={restore_err}"
        )
        logger.error("CRITICAL: %s且恢复失败 %s: %s", stage, filepath, restore_err)
def _post_write_gate(ctx: _RestoreContext, import_timeout: int) -> None:
    filepath, result = ctx.filepath, ctx.result
    try:
        post_passed, post_error = post_write_import_check(
            filepath, import_timeout)
    except Exception as e:  # noqa: BLE001
        logger.warning(
            "safe_fix_file: 写入后验证环境异常(按失败处理): %s", e)
        post_passed, post_error = False, f"写入后验证环境异常: {e}"
    if post_passed is not True:
        if post_passed is not False:
            post_error = (
                f"写入后验证返回形态异常(passed={post_passed!r}): {post_error}")
        post_passed = False
    result.layers["L_post_write"] = {
        "passed": post_passed, "error": post_error
    }
    if not post_passed:
        _restore_after_failure(
            ctx, "写入后验证失败", "验证错误", post_error)
def _cleanup_shared_net(safety_net, net, stage: str) -> None:
    if safety_net is not None:
        return
    try:
        net.cleanup()
    except Exception as cleanup_err:  # noqa: BLE001
        logger.warning("safe_fix_file: %s路径备份清理失败(不影响修复"
                       "结果返回): %s", stage, cleanup_err)
def _regression_failure(reason: str) -> dict[str, Any]:
    return {"passed": False, "layers": {},
            "error": f"回归验证环境异常: {reason}"}
_REGRESSION_VERIFIED_STATUSES = frozenset(("passed",))
def _verify_and_write(file_path: str, fixed_source: str, original_bytes: bytes,
                     *, skill_dir: str) -> tuple[str, str]:
    may_have_written = False
    try:
        verifier = FixSafetyVerifier(skill_dir=skill_dir)
        result = verifier.safe_fix_file(
            file_path, fixed_source, require_ai_review=False,
            expected_original_bytes=original_bytes,
        )
    except Exception as e:
        logger.warning("[FixSafety] 写盘安全验证异常: %s", e, exc_info=True)
        status, reason = "failed", f"安全验证异常: {e}"
        may_have_written = True
    else:
        if getattr(result, "passed", False) is True:
            return "", ""
        detail = str(getattr(result, "error", ""))
        logger.warning("[FixSafety] 写盘验证未通过 %s: %s", file_path, detail)
        status, reason = "rejected", f"安全验证未通过: {detail}"
        layers = getattr(result, "layers", {})
        may_have_written = isinstance(layers, dict) and any(
            key in layers for key in ("L_post_write", "L_regression"))
    if not may_have_written:
        return status, reason
    try:
        current_bytes = snapshot_file_bytes(file_path)
    except Exception as e:  # noqa: BLE001
        logger.warning("[FixSafety] 验证未通过后读取磁盘内容失败: %s", e)
        return "failed", f"{reason}；恢复前读取磁盘失败: {e}"
    if current_bytes == original_bytes:
        return status, reason
    try:
        candidate_bytes = _candidate_bytes_from_snapshot(
            original_bytes, fixed_source)
    except (SourceReadError, UnicodeError, SyntaxError, LookupError) as e:
        logger.warning("[FixSafety] 无法重建候选字节，禁止盲恢复: %s", e)
        return "failed", f"{reason}；无法确认磁盘内容归属，需人工核对"
    if current_bytes != candidate_bytes:
        return "failed", (
            f"{reason}；磁盘内容不等于本通道候选，未覆盖可能的并发修改，"
            "需人工核对")
    try:
        restore_file_bytes(file_path, original_bytes)
    except Exception as e:
        logger.exception("[FixSafety] 验证未成功后恢复原文件失败 %s", file_path)
        return "failed", f"{reason}；恢复原文件失败: {e}"
    return status, f"{reason}，已恢复原文件"
_REGRESSION_FAILED_LABEL = "定向回归失败"
_REGRESSION_UNDECIDED_LABEL = "定向回归无法执行（未获验证结论）"
_REGRESSION_PASSED_LABEL = "定向回归已通过"
def _regression_rollback_reason(
    skill_dir: str, file_path: str, original_bytes: bytes, *,
    security_channel: bool, candidate_bytes: bytes,
) -> tuple[dict, bool, str, str]:
    try:
        result = normalize_post_write_regression(
            skill_dir, file_path, security_channel=security_channel)
    except Exception as exc:
        logger.warning("[FixSafety] 定向回归执行异常，转入候选恢复: %s",
                       exc, exc_info=True)
        result = {
            "status": "error",
            "summary": f"定向回归执行异常({type(exc).__name__}): {exc}",
        }
    if not isinstance(result, dict):
        logger.warning("[FixSafety] 定向回归返回非 dict 形态(%s)，转入候选恢复",
                       type(result).__name__)
        result = {
            "status": "error",
            "summary": f"定向回归返回形态异常({type(result).__name__})",
        }
    status = as_str(result.get("status"))
    ownership_error = _candidate_ownership_error(file_path, candidate_bytes)
    if status in _REGRESSION_VERIFIED_STATUSES:
        if ownership_error is not None:
            return result, False, _REGRESSION_PASSED_LABEL, (
                f"{_REGRESSION_PASSED_LABEL}（磁盘保留非候选内容，人工介入）: "
                f"{ownership_error}")
        return result, False, "", ""
    label = (_REGRESSION_FAILED_LABEL if status == "failed"
             else _REGRESSION_UNDECIDED_LABEL)
    summary = as_str(result.get("summary"))[:150]
    if ownership_error is not None:
        return result, False, label, (
            f"{label}（恢复失败，人工介入）: {summary}；{ownership_error}")
    rollback_ok = _restore_after_regression(
        file_path, original_bytes, security_channel=security_channel)
    return result, rollback_ok, label, (
        f"{label}"
        f"{'，已恢复原文件' if rollback_ok else '（恢复失败，人工介入）'}: "
        f"{summary}")
def _regression_outcome(
    skill_dir: str, file_path: str, original_bytes: bytes, *,
    security_channel: bool, candidate_bytes: bytes,
) -> tuple[RegressionOutcome, str]:
    result, rollback_ok, label, reason = _regression_rollback_reason(
        skill_dir, file_path, original_bytes,
        security_channel=security_channel, candidate_bytes=candidate_bytes)
    if not reason:
        return RegressionOutcome("applied", detail=result), ""
    status = "rejected" if rollback_ok else "failed"
    return RegressionOutcome(status, reason, detail=result), label
def apply_verified_write(skill_dir: str, file_path: str,
                         fixed_source: str) -> tuple[dict, dict | None]:
    original_bytes, error = preflight_write_snapshot(file_path, fixed_source)
    if error is not None:
        return {}, error
    try:
        candidate_bytes = _candidate_bytes_from_snapshot(
            original_bytes, fixed_source)
    except (SourceReadError, UnicodeError, SyntaxError, LookupError) as exc:
        return {}, {"status": "rejected",
                    "reason": f"无法确认候选写盘字节，拒绝写盘: {exc}"}
    status, reason = _verify_and_write(
        file_path, fixed_source, original_bytes, skill_dir=skill_dir)
    if status:
        return {}, {"status": status, "reason": reason}
    outcome, _label = _regression_outcome(
        skill_dir, file_path, original_bytes, security_channel=False,
        candidate_bytes=candidate_bytes)
    if outcome.status == "applied":
        return outcome.detail or {}, None
    return outcome.detail or {}, {"status": outcome.status,
                                 "reason": outcome.reason}
_CREDENTIAL_VALUE_RE = re.compile(r"""['"]([^'"]+)['"]""")
def _credential_literal_value(match: re.Match, source: str) -> Any:
    groups = match.re.groupindex
    if "prefix" in groups and "quote" in groups:
        literal_text = source[match.start("prefix"):match.end()]
        prefix = match.group("prefix") or ""
        if "f" not in prefix.lower():
            try:
                return ast.literal_eval(literal_text)
            except (ValueError, TypeError, SyntaxError,
                    MemoryError, RecursionError) as exc:
                logger.debug("[FixSafety] 凭据字面量语义解析降级(%s)，"
                             "按完整原文比对", type(exc).__name__)
        quote = match.group("quote")
        return source[match.end("quote"):match.end() - len(quote)]
    quoted = _CREDENTIAL_VALUE_RE.findall(match.group(0))
    return quoted[-1] if quoted else match.group(0)
def _credential_literal_counts(
    pattern: str, source: str,
    literal_spans: list[tuple[int, int]] | None = None,
    *,
    seen_match_spans: set[tuple[int, int]] | None = None,
) -> Counter[Any]:
    counts: Counter[Any] = Counter()
    for match in re.finditer(pattern, source, re.IGNORECASE):
        if (literal_spans is not None
                and _inside_any_span(match.start(), literal_spans)):
            continue
        match_span = (match.start(), match.end())
        if seen_match_spans is not None and match_span in seen_match_spans:
            continue
        counts[_credential_literal_value(match, source)] += 1
        if seen_match_spans is not None:
            seen_match_spans.add(match_span)
    return counts
def detect_new_hardcoded_secrets(original_source: str,
                                 fixed_source: str) -> list[str]:
    hits: list[str] = []
    if original_source == fixed_source:
        return hits
    original_spans = _literal_token_spans(original_source)
    fixed_spans = _literal_token_spans(fixed_source)
    if ((fixed_spans is None or original_spans is None)
            and _contains_sensitive_assignment(fixed_source)):
        return ["敏感赋值字面量边界不可判定"]
    # 重叠规则可命中同一赋值；按源码区间去重，不按字面值去重。
    original_match_spans: set[tuple[int, int]] = set()
    fixed_match_spans: set[tuple[int, int]] = set()
    for pattern in SecurityConstraintSet.SENSITIVE_PATTERNS:
        try:
            added = (_credential_literal_counts(
                         pattern, fixed_source, fixed_spans,
                         seen_match_spans=fixed_match_spans)
                     - _credential_literal_counts(
                         pattern, original_source, original_spans,
                         seen_match_spans=original_match_spans))
        except re.error as re_err:
            logger.error("[fix_safety_gate] 凭据检测正则模式失效(失败关闭): "
                         "%s: %s", pattern, re_err)
            hits.append(pattern)
            continue
        hits.extend([pattern] * sum(added.values()))
    return hits
class FixSafetyVerifier:
    def __init__(
        self,
        skill_dir: str = _DEFAULT_SKILL_DIR,
        test_timeout: int = LayerConfig.test_timeout,
        import_timeout: int = LayerConfig.import_timeout,
        llm_call_fn: Callable | None = None,
    ) -> None:
        self._boundary_enforced = bool(skill_dir)
        self.skill_dir = normalize_skill_dir(skill_dir or ".")
        self.test_timeout = test_timeout
        self.import_timeout = import_timeout
        self.llm_call_fn = llm_call_fn
        self._safety_net = None
    def _get_safety_net(self) -> FixSafetyNet:
        if self._safety_net is None:
            self._safety_net = FixSafetyNet(self.skill_dir)
        return self._safety_net
    def cleanup(self) -> int:
        if self._safety_net is None:
            return 0
        return self._safety_net.cleanup()
    def _check_contract_preconditions(
        self, filepath: str, original_source: str, fixed_source: str
    ) -> str | None:
        for _label, _value in (("原始源码", original_source),
                               ("修复后源码", fixed_source)):
            if not isinstance(_value, str):
                return (f"{_label}形态异常({type(_value).__name__})，"
                        f"应为源码全文 str")
        if self._boundary_enforced:
            safe, reason = check_path_traversal(self.skill_dir, filepath)
            if not safe:
                return reason
        return _source_content_gate(original_source, fixed_source, filepath)
    def verify(
        self,
        filepath: str,
        original_source: str,
        fixed_source: str,
        risk_level: FixRiskLevel | None = None,
    ) -> FixVerificationResult:
        result = FixVerificationResult(filepath=filepath)
        try:
            return self._verify_impl(result, filepath, original_source,
                                     fixed_source, risk_level)
        except Exception as e:
            logger.warning("verify: 验证过程异常按失败收口: %s: %s",
                           type(e).__name__, e, exc_info=True)
            result.passed = False
            result.error = f"验证过程异常(fail-closed): {type(e).__name__}: {e}"
            result.layers["L_verify"] = {"passed": False,
                                        "error": str(e)[:200]}
            return result
    def _verify_impl(self, result: FixVerificationResult, filepath: str,
                     original_source: str, fixed_source: str,
                     risk_level: FixRiskLevel | None) -> FixVerificationResult:
        if not self._apply_l0_gate(result, filepath, original_source, fixed_source):
            return result
        risk_level = normalize_risk_level(risk_level, original_source,
                                           fixed_source, filepath)
        result.risk_level = risk_level
        result.side_effects = scan_boundary_guard(original_source,
                                                   fixed_source, filepath)
        if not self._apply_semantic_gate(result, filepath):
            return result
        if not self._run_layer_gates(result, filepath, fixed_source, risk_level):
            return result
        if not self._apply_llm_gate(result, filepath, original_source,
                                    fixed_source, risk_level):
            return result
        result.passed = True
        return result
    def _apply_l0_gate(self, result: FixVerificationResult, filepath: str,
                       original_source: str, fixed_source: str) -> bool:
        l0_error = self._check_contract_preconditions(filepath, original_source,
                                                      fixed_source)
        if l0_error:
            result.layers["L0_contract"] = {"passed": False, "error": l0_error}
            result.passed = False
            result.error = f"L0契约检查失败: {l0_error}"
            return False
        result.layers["L0_contract"] = {"passed": True}
        return True
    def _apply_semantic_gate(self, result: FixVerificationResult,
                             filepath: str) -> bool:
        _semantic_warnings = semantic_rejections(result.side_effects,
                                                  filepath, self.skill_dir)
        if not _semantic_warnings:
            return True
        result.passed = False
        w = _semantic_warnings[0]
        result.layers["TX02_semantic"] = {
            "passed": False,
            "warnings": _semantic_warnings,
        }
        result.error = (f"TX-02 semantic check: "
                        f"{w.get('type', 'unknown')} ({w.get('symbol', '')})")
        return False
    def _run_layer_gates(self, result: FixVerificationResult, filepath: str,
                         fixed_source: str,
                         risk_level: FixRiskLevel) -> bool:
        config = LayerConfig(
            skill_dir=self.skill_dir,
            test_timeout=self.test_timeout,
            import_timeout=self.import_timeout,
        )
        for layer_key, error_prefix, layer_fn in VERIFY_LAYERS:
            gated_levels = _RISK_GATED_LAYERS.get(layer_key)
            if gated_levels is not None and risk_level not in gated_levels:
                continue
            layer_passed, layer_error = layer_fn(filepath, fixed_source, config)
            if layer_passed is not True:
                if layer_passed is not False:
                    layer_error = (
                        f"验证层返回形态异常(passed={layer_passed!r}): "
                        f"{layer_error}")
                layer_passed = False
            result.layers[layer_key] = {"passed": layer_passed,
                                        "error": layer_error}
            if not layer_passed:
                result.passed = False
                result.error = f"{error_prefix}失败: {layer_error}"
                return False
        return True
    def _apply_llm_gate(self, result: FixVerificationResult,
                        filepath: str, original_source: str,
                        fixed_source: str, risk_level: FixRiskLevel) -> bool:
        if (self.llm_call_fn is not None
                and risk_level in (FixRiskLevel.CAUTION, FixRiskLevel.DANGEROUS)):
            l5_passed, l5_error = self._verify_llm_review(
                filepath, original_source, fixed_source)
            result.layers["L5_llm_review"] = {"passed": l5_passed, "error": l5_error}
            if not l5_passed:
                result.passed = False
                result.error = f"L5 LLM语义审查失败: {l5_error}"
                return False
        elif self.llm_call_fn is None and risk_level == FixRiskLevel.DANGEROUS:
            result.layers["L5_llm_review"] = {
                "passed": None,
                "error": "L5_SKIPPED: LLM unavailable, manual review required",
            }
            result.warnings.append(
                "L5_SKIPPED: DANGEROUS fix without LLM review - "
                "manual verification strongly recommended")
        return True
    def _verify_llm_review(self, filepath: str, original_source: str,
                           fixed_source: str) -> tuple[bool, str]:
        prompt = _build_review_prompt(filepath, original_source, fixed_source)
        if prompt is None:
            return True, "no changes"
        try:
            result = self.llm_call_fn(prompt)
        except Exception as e:  # noqa: BLE001
            logger.warning("[L5] LLM review error (fail-closed): %s", e)
            return False, f"LLM review failed: 调用异常: {str(e)[:100]}"
        return _normalize_llm_judgement(result)
    def _gate_regression(self, ctx: _RestoreContext,
                         fixed_source: str) -> None:
        filepath = ctx.filepath
        original_source, result = ctx.original_source, ctx.result
        try:
            regression_result = verify_regression(
                filepath, original_source, fixed_source,
                skill_dir=self.skill_dir,
                test_timeout=self.test_timeout,
                import_timeout=self.import_timeout,
            )
        except Exception as e:
            logger.warning(
                "safe_fix_file: 回归验证环境异常(按验证失败处理): %s", e,
                exc_info=True)
            regression_result = _regression_failure(str(e))
        if not isinstance(regression_result, dict):
            logger.warning(
                "safe_fix_file: 回归验证返回非 dict 形态(%s)，按验证失败处理",
                type(regression_result).__name__)
            regression_result = _regression_failure(
                f"返回值形态异常({type(regression_result).__name__})")
        result.layers["L_regression"] = regression_result
        if regression_result.get("passed") is not True:
            reason = regression_result.get("error") or (
                f"回归结果未明确通过(passed={regression_result.get('passed')!r})")
            _restore_after_failure(
                ctx, "回归验证失败", "回归错误", reason)
            return
        if ctx.candidate_bytes is not None:
            ownership_error = _candidate_ownership_error(
                filepath, ctx.candidate_bytes)
            if ownership_error is not None:
                ctx.net.mark_backed_up(filepath)
                result.passed = False
                result.rolled_back = False
                result.error = (
                    "回归验证通过，但磁盘候选所有权确认失败: "
                    f"{ownership_error}")
                result.layers["L_post_regression_ownership"] = {
                    "passed": False, "error": ownership_error,
                }
                logger.error(
                    "CRITICAL: 回归通过后的候选所有权确认失败 %s: %s",
                    filepath, ownership_error)
    def _verify_candidate(self, filepath: str,
                          source: _SourceSnapshot, fixed_source: str,
                          risk_level) -> FixVerificationResult:
        try:
            return self.verify(filepath, source.text, fixed_source, risk_level)
        except Exception as e:
            logger.warning("safe_fix_file: 验证过程异常，按验证失败处理: %s", e,
                           exc_info=True)
            return FixVerificationResult(
                passed=False, filepath=filepath,
                error=f"验证过程异常: {e}",
            )
    def _preflight_safe_fix(
        self, filepath: str, require_ai_review: bool,
        safety_net: FixSafetyNet | None,
        expected_original_bytes: bytes | None = None,
    ) -> tuple[
        FixVerificationResult | None, _SourceSnapshot | None,
        FixSafetyNet | None]:
        if not self._boundary_enforced:
            return FixVerificationResult(
                passed=False, filepath=filepath,
                error=("写盘安全边界未建立: skill_dir 必须显式提供非空治理根；"
                       "禁止回退到进程工作目录或关闭路径穿越校验"),
            ), None, None
        if require_ai_review:
            return FixVerificationResult(
                passed=False, filepath=filepath,
                error="AI 审核执行锚点强制拦截: safe_fix_file "
                      "写盘必须经由宿主的 AI 审核执行链路触发，"
                      "并显式确认 require_ai_review=False 后才可写码。"
                      "请通过宿主的 AI 审核执行入口提交修复方案。",
                rolled_back=True,
            ), None, None
        source, read_error = _read_source(filepath, "safe_fix_file")
        if read_error is not None or source is None:
            return FixVerificationResult(
                passed=False, filepath=filepath, error=read_error,
            ), None, None
        if (expected_original_bytes is not None
                and source.raw != expected_original_bytes):
            return FixVerificationResult(
                passed=False, filepath=filepath,
                error="原字节快照已过期，拒绝基于并发内容写盘",
            ), None, None
        try:
            net = safety_net or self._get_safety_net()
        except Exception as e:
            logger.exception("safe_fix_file: 安全网初始化失败，拒绝写盘"
                             "(fail-closed)")
            return FixVerificationResult(
                passed=False, filepath=filepath,
                error=f"安全网初始化失败，拒绝写盘(fail-closed): {e}",
            ), None, None
        if not net.create_backup(filepath, source.text):
            logger.error("safe_fix_file: 备份创建失败，拒绝写盘(fail-closed): %s",
                         filepath)
            return FixVerificationResult(
                passed=False, filepath=filepath,
                error="备份创建失败，拒绝写盘(fail-closed): 原始内容无法保障恢复，"
                      "请检查备份目录可写性后重试",
            ), None, None
        return None, source, net
    def safe_fix_file(
        self,
        filepath: str,
        fixed_source: str,
        risk_level: FixRiskLevel | None = None,
        safety_net: FixSafetyNet | None = None,
        require_ai_review: bool = _DEFAULT_REQUIRE_AI_REVIEW,
        expected_original_bytes: bytes | None = None,
    ) -> FixVerificationResult:
        filepath = os.path.abspath(filepath)
        preflight_error, source, net = self._preflight_safe_fix(
            filepath, require_ai_review, safety_net,
            expected_original_bytes)
        if preflight_error is not None:
            return preflight_error
        result = self._verify_candidate(
            filepath, source, fixed_source, risk_level)
        restore_ctx = _RestoreContext(net, filepath, source, result)
        if result.passed:
            try:
                current_bytes = snapshot_file_bytes(filepath)
            except Exception as exc:  # noqa: BLE001
                result.passed = False
                result.error = f"写入前原字节快照失败，拒绝写盘: {exc}"
            else:
                if current_bytes != source.raw:
                    result.passed = False
                    result.error = (
                        "写入前检测到文件已被外部修改，拒绝用过期候选覆盖并发内容")
            if not result.passed:
                result.layers["L_pre_write_snapshot"] = {
                    "passed": False, "error": result.error,
                }
        if not result.passed:
            result.rolled_back = True
            net.mark_rolled_back(filepath)
            logger.warning("修复验证或写前快照未通过，已阻止写入 %s: %s",
                           filepath, result.error)
            _cleanup_shared_net(safety_net, net, "验证或写前快照失败")
            return result
        try:
            candidate_bytes = _encode_source_payload(
                fixed_source, source.text)
            restore_ctx = _RestoreContext(
                net, filepath, source, result, candidate_bytes)
        except (ValueError, SyntaxError, LookupError) as exc:
            logger.warning("safe_fix_file: 候选写盘字节构造失败: %s", exc)
            write_ok, write_error = False, f"写入失败: {exc}"
        else:
            write_ok, write_error = _atomic_replace_write(
                filepath, candidate_bytes)
        if not write_ok:
            result.passed = False
            result.error = write_error
            result.rolled_back = True
            net.mark_rolled_back(filepath)
        else:
            logger.info("修复验证通过，已写入 %s (风险: %s, 原子写入)",
                        filepath, result.risk_level.value)
            _post_write_gate(restore_ctx, self.import_timeout)
        if result.passed:
            self._gate_regression(restore_ctx, fixed_source)
        if result.passed:
            net.mark_committed(filepath)
        _cleanup_shared_net(safety_net, net, "内部共享网收尾")
        return result
def _build_review_prompt(filepath: str, original_source: str,
                         fixed_source: str) -> str | None:
    diff_lines = list(difflib.unified_diff(
        original_source.splitlines(),
        fixed_source.splitlines(),
        fromfile="original",
        tofile="fixed",
        lineterm=""))
    diff_text = "\n".join(diff_lines)
    if not diff_text.strip():
        return None
    if len(diff_text) > 4000:
        diff_text = diff_text[:4000] + "\n... (truncated)"
    return f"""# Code Fix Review

You are reviewing a code fix. Analyze the diff below and determine if the fix is safe.

## Diff
```diff
{diff_text}
```

## File: {os.path.basename(filepath)}

## Questions
1. Does the fix correctly address the intended issue without introducing new bugs?
2. Are there any side effects that could break existing functionality?
3. Is the fix semantically correct (not just syntactically)?

Respond in JSON format only:
{{"safe": true/false, "reason": "brief explanation", "risk": "low/medium/high"}}"""
def _coerce_llm_dict(result: Any) -> tuple[dict[str, Any] | None, str]:
    if isinstance(result, str):
        try:
            result = json.loads(result)
        except (ValueError, RecursionError) as e:
            log_swallowed(__name__, e,
                          context=f"_coerce_llm_dict:{type(e).__name__}")
            return None, f"LLM review failed: 非JSON响应 ({str(e)[:80]})"
    if not isinstance(result, dict):
        return None, f"LLM review failed: 非预期返回类型 {type(result).__name__}"
    return result, ""
def _normalize_llm_judgement(result: Any) -> tuple[bool, str]:
    payload, error_reason = _coerce_llm_dict(result)
    if payload is None:
        return False, error_reason
    safe = payload.get("safe")
    if safe is None:
        return False, "LLM review failed: 响应缺少 safe 判定字段"
    if isinstance(safe, str):
        normalized = safe.strip().lower()
        if normalized in ("true", "1", "yes"):
            safe = True
        elif normalized in ("false", "0", "no"):
            safe = False
        else:
            return False, (f"LLM review failed: safe 判定字段值不可归一 "
                           f"({safe!r})")
    elif isinstance(safe, int) and not isinstance(safe, bool):
        if safe not in (0, 1):
            return False, (f"LLM review failed: safe 判定字段值不可归一 "
                           f"({safe!r})")
        safe = bool(safe)
    elif not isinstance(safe, bool):
        return False, (f"LLM review failed: safe 判定字段类型不可归一 "
                       f"({type(safe).__name__})")
    reason = payload.get("reason", "no reason provided")
    risk = payload.get("risk", "unknown")
    if safe:
        return True, f"LLM review passed: {reason} (risk: {risk})"
    return False, f"LLM review failed: {reason} (risk: {risk})"
def verify_manual_fix(
    filepath: str,
    fixed_source: str,
    skill_dir: str = _DEFAULT_SKILL_DIR,
) -> FixVerificationResult:
    verifier = FixSafetyVerifier(
        skill_dir=skill_dir or os.path.dirname(os.path.abspath(filepath)))
    source, read_error = _read_source(filepath, "verify_manual_fix")
    if read_error is not None or source is None:
        return FixVerificationResult(
            passed=False, filepath=filepath, error=read_error,
        )
    try:
        return verifier.verify(filepath, source.text, fixed_source)
    except Exception as e:
        logger.exception("verify_manual_fix: 验证器内部异常(fail-closed)")
        return FixVerificationResult(
            passed=False, filepath=filepath,
            error=f"验证器内部异常(fail-closed): {e}",
        )
def verify_fix_safety(
    filepath: str,
    fixed_source: str,
    skill_dir: str = _DEFAULT_SKILL_DIR,
    risk_level: FixRiskLevel | None = None,
    require_ai_review: bool = _DEFAULT_REQUIRE_AI_REVIEW,
) -> FixVerificationResult:
    verifier = FixSafetyVerifier(
        skill_dir=skill_dir or os.path.dirname(os.path.abspath(filepath)))
    return verifier.safe_fix_file(
        filepath, fixed_source, risk_level, require_ai_review=require_ai_review
    )
def _normalize_risk_value(risk: Any) -> str:
    if hasattr(risk, "value"):
        return str(risk.value).strip().lower()
    if risk is None:
        return ""
    return str(risk).strip().lower()
def _record_l2_layer(verify_result: Any, details: dict[str, Any]) -> None:
    if "L2_import" in verify_result.layers:
        l2_layer = verify_result.layers.get("L2_import") or {}
        details["L2_import"] = "passed" if l2_layer.get("passed") else "failed"
        if l2_layer:
            details["L2_detail"] = l2_layer
def _record_l3_layer(verify_result: Any, details: dict[str, Any]) -> None:
    l3_layer = verify_result.layers.get("L3_test")
    if l3_layer:
        details["L3_test"] = "passed" if l3_layer.get("passed") else "failed"
def _record_side_effects(verify_result: Any, details: dict[str, Any]) -> None:
    side_effects = getattr(verify_result, "side_effects", None)
    if side_effects:
        details["side_effects"] = side_effects
def _verify_l2_l3(
    filepath: str,
    source: str,
    orig_source: str,
    skill_dir: str,
    details: dict[str, Any],
) -> bool:
    try:
        verifier = FixSafetyVerifier(skill_dir=skill_dir)
        risk = classify_risk(orig_source, source, filepath)
        risk = normalize_risk_level(risk, orig_source, source, filepath)
        risk_val = _normalize_risk_value(risk)
        details["risk_level"] = risk_val
        if risk_val == "safe":
            details["L2_import"] = "skipped (SAFE risk)"
            details["L3_test"] = "skipped (SAFE risk)"
            return True
        verify_result = verifier.verify(
            filepath, orig_source, source, risk_level=risk)
        _record_l2_layer(verify_result, details)
        _record_side_effects(verify_result, details)
        if not verify_result.passed:
            details["error"] = verify_result.error or "安全验证失败"
            return False
        if risk_val == "dangerous":
            _record_l3_layer(verify_result, details)
    except Exception as _e:  # noqa: BLE001
        details["L2_import"] = f"error: {str(_e)[:100]}"
        details["error"] = f"L2/L3 验证基础设施异常: {_e}"
        logger.warning("[Rollback] L2/L3 验证异常（按失败处理）: %s", _e)
        return False
    return True
register_l2l3_write_verifier(_verify_l2_l3)
class RegressionOutcome(NamedTuple):
    status: str
    reason: str = ""
    detail: dict | None = None
def _decode_original_source(
    original_bytes: bytes, context: str,
) -> tuple[str, str | None]:
    try:
        text, encoding = decode_source_strict(original_bytes)
        return text, encoding
    except SourceReadError as exc:
        log_swallowed(__name__, exc, context=context)
        return (original_bytes.decode(_DEFAULT_SOURCE_ENCODING, errors="replace"),
                None)
def empty_fix_rejection(original_source: str, fixed_source: str) -> str | None:
    if not isinstance(fixed_source, str):
        return None
    if fixed_source == original_source or fixed_source.strip():
        return None
    return ("修复后源码为空（或仅空白），拒绝写入：空内容无法被"
            "L2/L3/L4 有效验证，且通常表示修复内容丢失；"
            "如确需清空模块，请提交包含显式说明与验证方案的最小内容")
def _source_content_gate(original_text: str, fixed_source: str,
                         filepath: str) -> str | None:
    _empty_reason = empty_fix_rejection(original_text, fixed_source)
    if _empty_reason:
        return _empty_reason
    new_secrets = detect_new_hardcoded_secrets(original_text, fixed_source)
    if new_secrets:
        return (
            f"修复操作引入了 {len(new_secrets)} 处新的硬编码凭据"
            "（password/api_key/secret/token/private_key/ssh_key 赋值），"
            "请改用 os.environ.get() 等环境变量引用")
    if filepath and os.path.splitext(filepath)[1].lower() != ".py":
        return None
    _patch_hits = detect_new_patch_style_fixes(original_text, fixed_source)
    if _patch_hits:
        return (
            f"修复操作引入了补丁式修复静态形态：{'；'.join(_patch_hits)}。"
            "违反禁止补丁方式修复约束（fix_scope.no_patch_fix）：吞异常"
            "遮蔽/裸捕获属只治症状不除根因，请定位根因后以根因消除"
            "方式重新修复；确属必要的样例/测试场景请附 # nosec 显式"
            "豁免声明")
    return comment_docstring_sync_error(original_text, fixed_source, filepath)
def _write_gate(target: str, fixed_source: str,
                original_text: str) -> str | None:
    if not isinstance(fixed_source, str):
        return (f"语法验证失败，拒绝写盘（请修正后重新提交）: "
                f"修复后源码形态异常({type(fixed_source).__name__})，"
                f"应为修复后源码全文 str")
    if os.path.splitext(target)[1].lower() == ".py":
        _syn_err = check_fixed_source_syntax(fixed_source, target)
        if _syn_err is not None:
            return f"语法验证失败，拒绝写盘（请修正后重新提交）: {_syn_err}"
    return _source_content_gate(original_text, fixed_source, target)
def _restore_after_regression(target: str, original_bytes: bytes,
                              *, security_channel: bool) -> bool:
    try:
        restore_file_bytes(target, original_bytes)
        return True
    except Exception:
        prefix = "AIManualFix" if security_channel else "FixSafety"
        logger.exception("[%s] 定向回归未通过后恢复原文件失败: %s",
                         prefix, target)
        return False
def _post_write_regression(sd: str, target: str,
                           original_bytes: bytes, *,
                           candidate_bytes: bytes) -> RegressionOutcome:
    outcome, label = _regression_outcome(
        sd, target, original_bytes, security_channel=True,
        candidate_bytes=candidate_bytes)
    if outcome.status != "applied":
        logger.warning("[AIManualFix] 安全建议%s，%s: %s", label,
                       "已恢复原文件" if outcome.status == "rejected"
                       else "恢复失败须人工介入",
                       target)
    return outcome
def apply_security_write(sd: str, target: str,
                        fixed_source: str) -> RegressionOutcome:
    try:
        _original_bytes = snapshot_file_bytes(target)
    except OSError as e:
        log_swallowed(__name__, e,
                      context=f"apply_security_write:{type(e).__name__}")
        return RegressionOutcome("failed", f"读取原文件失败: {e}")
    _original_text, _source_encoding = _decode_original_source(
        _original_bytes, f"apply_security_write:{os.path.basename(target)}")
    if _source_encoding is None:
        return RegressionOutcome(
            "rejected",
            "源文件编码声明无法解析，拒绝写盘以免损坏原文件（需人工确认编码后重试）")
    _gate_reason = _write_gate(target, fixed_source, _original_text)
    if _gate_reason is not None:
        return RegressionOutcome("rejected", _gate_reason)
    try:
        current_bytes = snapshot_file_bytes(target)
    except OSError as e:
        log_swallowed(
            __name__, e, context="apply_security_write:pre_write_snapshot")
        return RegressionOutcome("failed", f"写入前原字节快照失败: {e}")
    if current_bytes != _original_bytes:
        return RegressionOutcome(
            "rejected", "写入前检测到文件已被外部修改，拒绝覆盖并发内容")
    try:
        candidate_bytes = _encode_source_payload(
            fixed_source, _original_text)
        atomic_replace_bytes(
            target, candidate_bytes,
            prefix=f".{os.path.basename(target)}.secfix_",
            label="安全建议写盘临时产物")
    except (OSError, ValueError, SyntaxError, LookupError) as e:
        log_swallowed(__name__, e,
                      context=f"apply_security_write:{type(e).__name__}")
        return RegressionOutcome("failed", f"写盘失败: {e}")
    logger.info("[AIManualFix] 安全建议已执行写盘: %s", target)
    return _post_write_regression(
        sd, target, _original_bytes, candidate_bytes=candidate_bytes)
@dataclass
class AafCtx:
    skill_dir: str
    index: int
    item: dict
    file_path: str
    fixed_source: str
    original_source: str
    description: str
    side_effects: list = field(default_factory=list)
def write_fix_file(ctx: AafCtx, safety_ok: bool, *,
                   original_bytes: bytes | None,
                   source_encoding: str,
                   on_content_failure: Callable[[Any], None] | None = None
                   ) -> tuple[dict | None, str]:
    backup_path, backup_written = write_backup_bytes(
        ctx.skill_dir, ctx.file_path, original_bytes)
    process_gate = check_process_norms({
        "operation": "fix",
        "file_path": ctx.file_path,
        "backup_exists": backup_written,
        "test_passed": safety_ok,
        "baseline_compared": True,
    })
    _p0_gate = [v for v in process_gate.get("violations", [])
                if v.get("severity") == "P0"]
    if _p0_gate:
        _gate_reason = "; ".join(
            f"[{v['rule_id']}] {v['detail']}" for v in _p0_gate)
        return _fail_after_audit(
            ctx, status="rejected", event="ai_fix_rejected",
            reason=f"进程铁律门阻断: {_gate_reason}"), backup_path
    rep_report = enforce_read_before_write(ctx.file_path)
    if not rep_report["passed"]:
        _rep_reason = "; ".join(
            f"[{c['rep']}] {c['reason']}"
            for c in rep_report["checks"] if not c["passed"]
        )
        return _fail_after_audit(
            ctx, status="rejected", event="ai_fix_rejected",
            reason=f"REP读写一致性门阻断: {_rep_reason}",
            rep_report=rep_report), backup_path
    if original_bytes is not None:
        try:
            current_bytes = snapshot_file_bytes(ctx.file_path)
        except OSError as exc:
            reason = f"写入前原字节快照失败: {exc}"
            logger.warning("[AIManualFix] %s", reason)
            return _fail_after_audit(
                ctx, status="failed", event="ai_fix_failed",
                reason=reason), backup_path
        if current_bytes != original_bytes:
            reason = "写入前检测到文件已被外部修改，拒绝覆盖并发内容"
            logger.warning("[AIManualFix] %s: %s", reason, ctx.file_path)
            return _fail_after_audit(
                ctx, status="rejected", event="ai_fix_rejected",
                reason=reason), backup_path
    write_error, content_failure = _aaf_atomic_write(ctx, source_encoding)
    if write_error is not None and content_failure and on_content_failure is not None:
        on_content_failure(ctx)
    if write_error is None:
        READ_BEFORE_WRITE_GUARD.mark_read(ctx.file_path)
    return write_error, backup_path
def _aaf_atomic_write(ctx: AafCtx, source_encoding: str) -> tuple[dict | None, bool]:
    try:
        payload = _encode_source_payload(
            ctx.fixed_source, ctx.original_source)
    except (UnicodeEncodeError, SyntaxError, LookupError) as e:
        logger.warning("[AIManualFix] 修复后源码按自身编码声明保存失败(拒绝写入): %s", e)
        return _fail_after_audit(
            ctx, status="rejected", event="ai_fix_rejected",
            reason=("修复后源码编码声明非法或包含其声明编码无法表示的字符"
                    f"（原文件编码为 {source_encoding}），拒绝写入以免损坏文件: {e}")), True
    try:
        atomic_replace_bytes(
            ctx.file_path, payload,
            prefix=os.path.basename(ctx.file_path) + ".aifix_")
    except (OSError, ValueError) as e:
        logger.warning("[AIManualFix] 写入文件失败(已审计留痕并返回failed): %s: %s",
                       type(e).__name__, e, exc_info=True)
        return _fail_after_audit(
            ctx, status="failed", event="ai_fix_failed",
            reason=f"写入文件失败: {e}"), False
    return None, False
def _fail_after_audit(ctx: AafCtx, *, status: str, event: str,
                      reason: str, **extra) -> dict:
    safe_write_audit(event, index=ctx.index, file=ctx.file_path, reason=reason)
    return {"status": status, "reason": reason,
            "regression_verified": False, **extra}
def _resolve_rollback_bytes(ctx: AafCtx, backup_path: str,
                            original_bytes: bytes | None,
                            source_encoding: str) -> bytes | None:
    if original_bytes is not None:
        return original_bytes
    if backup_path and os.path.isfile(backup_path):
        try:
            with open(backup_path, "rb") as f:
                rollback_bytes = f.read()
            if rollback_bytes or not ctx.original_source:
                return rollback_bytes
        except OSError as e:
            logger.warning(
                "[AIManualFix] 回滚备份读取失败(%s)，退化内存原文兜底: %s",
                type(e).__name__, backup_path)
    try:
        return ctx.original_source.encode(source_encoding)
    except (UnicodeEncodeError, LookupError):
        logger.exception("[AIManualFix] 回滚原文无法按原编码重建（需人工介入）: %s",
                         ctx.file_path)
        return None
def _rollback_overwrite(ctx: AafCtx, rollback_bytes: bytes | None) -> bool:
    rollback_ok = False
    try:
        if rollback_bytes is None:
            raise ValueError("回滚内容不可用，拒绝改写目标文件")
        atomic_replace_bytes(
            ctx.file_path, rollback_bytes,
            prefix=os.path.basename(ctx.file_path) + ".trrollback_",
            label="回滚临时产物")
        rollback_ok = True
    except Exception:
        logger.exception("[AIManualFix] 定向回归失败后回滚写盘失败")
    if rollback_ok:
        READ_BEFORE_WRITE_GUARD.mark_read(ctx.file_path)
    return rollback_ok
def rollback_unverified_fix(ctx: AafCtx, backup_path: str, *,
                            original_bytes: bytes | None,
                            source_encoding: str
                            ) -> bool:
    try:
        candidate_bytes = _encode_source_payload(
            ctx.fixed_source, ctx.original_source)
    except (UnicodeEncodeError, SyntaxError, LookupError):
        logger.exception(
            "[AIManualFix] 无法重建候选字节，拒绝回滚（需人工介入）: %s",
            ctx.file_path)
        return False
    ownership_error = _candidate_ownership_error(
        ctx.file_path, candidate_bytes)
    if ownership_error is not None:
        logger.error("[AIManualFix] 回滚前所有权校验失败 %s: %s",
                     ctx.file_path, ownership_error)
        return False
    rollback_bytes = _resolve_rollback_bytes(
        ctx, backup_path, original_bytes, source_encoding)
    return _rollback_overwrite(ctx, rollback_bytes)
def _api_finding_signature(finding: Any) -> tuple[str, str]:
    if isinstance(finding, dict):
        name = finding.get("api_name") or finding.get("title") or ""
        severity = finding.get("severity") or ""
    else:
        name = (getattr(finding, "api_name", "")
                or getattr(finding, "title", ""))
        severity = getattr(finding, "severity", "")
    return str(name), str(severity).upper()
def _new_hallucination_findings(
    written_findings: list, original_source: str, file_path: str,
) -> list:
    if (not written_findings or not isinstance(original_source, str)
            or not original_source):
        return written_findings
    baseline_counts = Counter(
        _api_finding_signature(finding)
        for finding in detect_hallucinated_api(original_source, file_path))
    fresh: list = []
    for finding in written_findings:
        signature = _api_finding_signature(finding)
        if baseline_counts[signature] > 0:
            baseline_counts[signature] -= 1
            continue
        fresh.append(finding)
    return fresh
def _enforce_session_write_budget(ctx: AafCtx) -> None:
    try:
        budget_report = record_session_write(ctx.file_path, ctx.fixed_source)
    except Exception as exc:
        logger.warning("[AIManualFix] 会话预算记账失败，调用方必须回滚: %s",
                       exc, exc_info=True)
        raise RuntimeError(
            f"会话预算记账失败: {type(exc).__name__}: {exc}") from exc
    logger.info(
        "[AIManualFix] 会话预算记账: decision=%s lines=%d session=%d/%d",
        budget_report.decision.value, budget_report.total_lines,
        budget_report.session_quota_used, budget_report.session_quota_max,
    )
    if budget_report.passed is not True:
        reason = (f"会话预算阻断: {budget_report.summary} "
                  f"(decision={budget_report.decision.value})")
        logger.warning("[AIManualFix] %s，调用方必须回滚", reason)
        raise RuntimeError(reason)
def run_post_write_hallucination_check(
        ctx: AafCtx, *, record_budget: bool = True) -> list:
    try:
        hallucination_api_findings = verify_api_existence(ctx.file_path)
        if not isinstance(hallucination_api_findings, list):
            raise TypeError(
                "verify_api_existence 返回形态异常: "
                f"{type(hallucination_api_findings).__name__}")
        hallucination_api_findings = _new_hallucination_findings(
            hallucination_api_findings, ctx.original_source, ctx.file_path)
        if hallucination_api_findings:
            logger.warning(
                "[AIManualFix] 修复后文件新引入疑似幻觉API调用: "
                "index=%d file=%s count=%d",
                ctx.index, ctx.file_path, len(hallucination_api_findings))
    except Exception as exc:
        logger.warning(
            "[AIManualFix] 修复后幻觉API校验执行失败，调用方必须回滚: file=%s",
            ctx.file_path, exc_info=True)
        raise RuntimeError(
            f"修复后幻觉API校验执行失败: {type(exc).__name__}: {exc}") from exc
    if hallucination_api_findings:
        return hallucination_api_findings
    if record_budget:
        _enforce_session_write_budget(ctx)
    return hallucination_api_findings
def _check_fixed_source_shape(ctx: AafCtx) -> dict | None:
    if isinstance(ctx.fixed_source, str):
        return None
    reason = (f"fixed_source 形态异常({type(ctx.fixed_source).__name__})，"
              f"应为修复后源码全文 str")
    logger.warning("[AIManualFix] %s", reason)
    return aaf_reject(ctx, "error", reason, event="ai_fix_error")
def _run_safety_check(ctx: AafCtx) -> tuple[dict | None, bool, list]:
    ctx.side_effects = []
    try:
        vresult = FixSafetyVerifier(skill_dir=ctx.skill_dir).verify(
            ctx.file_path, ctx.original_source, ctx.fixed_source)
        safety_ok = vresult.passed is True
        safety_reason = str(vresult.error)
        side_effects = (vresult.side_effects
                        if isinstance(vresult.side_effects, list) else [])
        ctx.side_effects = side_effects
    except Exception as e:
        logger.warning("[AIManualFix] 安全验证执行异常(按写入失败收口): %s: %s",
                       type(e).__name__, e, exc_info=True)
        return aaf_reject(
            ctx, "failed", f"安全验证异常: {e}",
            event="ai_fix_failed", audit_reason=f"安全验证异常: {e}"), False, []
    if not safety_ok:
        return aaf_reject(
            ctx, "rejected", f"安全验证未通过: {safety_reason}",
            event="ai_fix_rejected",
            audit_reason=f"安全验证未通过: {safety_reason}"), False, side_effects
    return None, safety_ok, side_effects
def _check_fixed_source_syntax(ctx: AafCtx) -> dict | None:
    reason = check_fixed_source_syntax(ctx.fixed_source, ctx.file_path)
    if reason is None:
        return None
    logger.warning("[AIManualFix] 修复后代码存在语法错误(拒绝写入): %s", reason)
    return aaf_reject(ctx, "rejected", reason,
                      event="ai_fix_rejected",
                      audit_reason=reason)
def aaf_verify_syntax_safety(ctx: AafCtx) -> tuple[dict | None, bool, list]:
    reject = _check_fixed_source_shape(ctx)
    if reject:
        return reject, False, []
    reject = _check_fixed_source_syntax(ctx)
    if reject:
        return reject, False, []
    return _run_safety_check(ctx)
def aaf_verify_inline(ctx: AafCtx) -> tuple[dict | None, dict | None, bool]:
    regression_verified = True
    inline_verification = None
    try:
        _iv = InlineVerifier()
        vfix = _iv.verify_and_fix(
            ctx.original_source,
            fixes=[{
                "rule_id": ctx.item.get("rule_id", "AI-FIX"),
                "fix_fn": lambda _c: ctx.fixed_source,
                "description": ctx.description or "AI 手动修复",
            }],
        )
        inline_verification = vfix.summary()
        for step in vfix.steps:
            if not step.rolled_back:
                continue
            status = step.verify_result.status
            if status == VerifyStatus.DEGRADED:
                logger.warning(
                    "[AIManualFix] 修复评分退化(improvement=%.2f)，拒绝已回滚候选",
                    vfix.overall_improvement)
            return (_inline_reject(ctx, step, inline_verification),
                    inline_verification, False)
    except Exception as e:
        reason = (f"内联验证执行异常({type(e).__name__}): {str(e)[:200]}，"
                  "未获得验证通过结论，已拒绝写入")
        logger.warning("[AIManualFix] %s", reason, exc_info=True)
        return (aaf_reject(
            ctx, "failed", reason, event="ai_fix_failed",
            audit_reason=reason, inline_verification=inline_verification),
            inline_verification, False)
    return None, inline_verification, regression_verified
def _inline_reject(ctx: AafCtx, step, inline_verification: dict) -> dict:
    reason = step.rollback_reason[:200]
    status = step.verify_result.status
    if status == VerifyStatus.BLOCKED:
        verdict, audit_label = "红线触发", "内联红线"
    elif status == VerifyStatus.DEGRADED:
        verdict, audit_label = "质量退化", "内联质量退化"
    else:
        verdict, audit_label = "候选未通过", "内联候选未通过"
    return aaf_reject(
        ctx, "rejected", f"内联验证{verdict}: {reason}",
        event="ai_fix_rejected", audit_reason=f"{audit_label}: {reason}",
        inline_verification=inline_verification)
def _aaf_stage_contract_failure(ctx: AafCtx, verifier: Callable,
                                detail: str) -> tuple[dict, dict]:
    stage_name = getattr(verifier, "__name__", type(verifier).__name__)
    reason = (f"验证阶段 {stage_name} {detail}，未获得验证通过结论，"
              "已拒绝写入")
    logger.warning("[AIManualFix] %s", reason)
    return aaf_reject(
        ctx, "failed", reason, event="ai_fix_failed",
        audit_reason=reason), {}
def _run_aaf_verify_stage(ctx: AafCtx, verifier: Callable,
                          result_fields: tuple[str, ...]) -> tuple[dict | None, dict]:
    try:
        outcome = verifier(ctx)
    except Exception as exc:  # noqa: BLE001
        return _aaf_stage_contract_failure(
            ctx, verifier,
            f"执行异常({type(exc).__name__}): {str(exc)[:200]}")
    if not result_fields and (outcome is None or isinstance(outcome, dict)):
        outcome = (outcome,)
    expected_len = len(result_fields) + 1
    if not isinstance(outcome, tuple) or len(outcome) != expected_len:
        actual = (f"tuple/{len(outcome)}" if isinstance(outcome, tuple)
                  else type(outcome).__name__)
        return _aaf_stage_contract_failure(
            ctx, verifier,
            f"返回形态异常(期望 tuple/{expected_len}，实际 {actual})")
    reject, *values = outcome
    if reject is not None and (not isinstance(reject, dict) or not reject):
        return _aaf_stage_contract_failure(
            ctx, verifier,
            f"拒绝结果形态异常({type(reject).__name__})")
    if reject is not None:
        return reject, {}
    return None, dict(zip(result_fields, values, strict=True))
def aaf_verify_hallucination_precheck(ctx: Any) -> dict | None:
    try:
        _new_p0 = detect_new_p0_api_calls(
            ctx.original_source, ctx.fixed_source, ctx.file_path)
    except Exception as exc:
        reason = (f"写前幻觉API预检执行失败({type(exc).__name__}): "
                  f"{str(exc)[:200]}，未获得验证通过结论，已拒绝写入")
        logger.warning("[AIManualFix] %s", reason, exc_info=True)
        return aaf_reject(
            ctx, "failed", reason, event="ai_fix_failed",
            audit_reason=reason, hallucination_precheck="error")
    if not _new_p0:
        return None
    names = ", ".join(sorted({sig[0] for sig in _new_p0})[:8])
    reason = (f"写前幻觉API预检拦截: 修复新引入 {len(_new_p0)} 个 P0 级"
              f"疑似不存在的API调用（{names}），请核对 API 名称/导入后重新提交")
    logger.warning("[AIManualFix] %s", reason)
    return aaf_reject(ctx, "rejected", reason,
                               event="ai_fix_rejected",
                               hallucination_precheck="blocked_p0")
_RESTORE_ERROR_DETAIL_MAX_CHARS = 160
def _aaf_behavior_guard(skill_dir: str) -> BehaviorRegressionGuard:
    import_roots = python_import_roots(skill_dir)
    if not import_roots:
        import_roots = (os.path.dirname(normalize_skill_dir(skill_dir)),)
    return BehaviorRegressionGuard(
        timeout_sec=EQUIVALENCE_GUARD_TIMEOUT_SEC,
        max_test_cases=EQUIVALENCE_GUARD_MAX_TEST_CASES,
        extra_pythonpath=list(import_roots))
def aaf_verify_behavior(ctx: Any) -> tuple[dict | None, dict | None]:
    behavior_regression = None
    if ctx.fixed_source != ctx.original_source:
        try:
            report = _aaf_behavior_guard(ctx.skill_dir).verify(
                ctx.original_source, ctx.fixed_source, filepath=ctx.file_path)
        except Exception as e:
            reason = (f"行为回归验证执行异常({type(e).__name__}): "
                      f"{str(e)[:200]}，未获得验证通过结论，已拒绝写入")
            logger.warning("[AIManualFix] %s", reason, exc_info=True)
            return (aaf_reject(
                ctx, "failed", reason, event="ai_fix_failed",
                audit_reason=reason, behavior_regression=behavior_regression),
                behavior_regression)
        behavior_regression = describe_behavior_regression(report)
        if behavior_regression["restore_failed"]:
            _detail = behavior_regression["error_detail"].strip()
            logger.error(
                "[AIManualFix] 行为回归验证收尾还原失败(磁盘可能停留修复版)，"
                "拒绝写入: %s", _detail[:200])
            return (aaf_reject(
                ctx, "failed",
                f"行为回归验证收尾还原失败({_detail[:_RESTORE_ERROR_DETAIL_MAX_CHARS]})，已拒绝写入："
                f"磁盘可能停留修复版，须先人工恢复原始内容后重新提交修复",
                event="ai_fix_failed",
                audit_reason=f"行为回归还原失败: {_detail[:_RESTORE_ERROR_DETAIL_MAX_CHARS]}",
                behavior_regression=behavior_regression), behavior_regression)
        if (behavior_regression["is_regressed"]
                and behavior_regression["objective_break"]):
            reason = behavior_regression["reject_reason"]
            logger.warning(
                "[AIManualFix] 行为回归验证失败: %s — 拒绝写入（回滚语义）", reason)
            return (aaf_reject(
                ctx, "rejected", f"行为回归验证失败({reason}),已拒绝写入."
                                 "修复未通过等价实现验证,需人工介入.",
                event="ai_fix_rejected",
                audit_reason=f"行为回归退化: {reason}",
                behavior_regression=behavior_regression), behavior_regression)
        if not behavior_regression["equivalent"]:
            detail = (behavior_regression["reject_reason"]
                      or behavior_regression["error_detail"]
                      or f"status={behavior_regression['status']}")
            status = "rejected" if behavior_regression["is_regressed"] else "failed"
            event = "ai_fix_rejected" if status == "rejected" else "ai_fix_failed"
            reason = (f"行为回归验证未明确通过(status={behavior_regression['status']}): "
                      f"{str(detail)[:_RESTORE_ERROR_DETAIL_MAX_CHARS]}，已拒绝写入")
            logger.warning("[AIManualFix] %s", reason)
            return (aaf_reject(
                ctx, status, reason, event=event, audit_reason=reason,
                behavior_regression=behavior_regression), behavior_regression)
        logger.info("[AIManualFix] 行为回归验证通过: %d/%d 测试通过 (%.0fms)",
                    behavior_regression["passed_tests"],
                    behavior_regression["total_tests"],
                    behavior_regression["elapsed_ms"])
    return None, behavior_regression
def run_fix_verify_chain(ctx: AafCtx) -> tuple[dict | None, dict]:
    stages = (
        (aaf_verify_syntax_safety, ("safety_ok", "side_effects")),
        (aaf_verify_hallucination_precheck, ()),
        (aaf_verify_patch_precheck, ()),
        (aaf_verify_inline, ("inline_verification", "regression_verified")),
        (aaf_verify_behavior, ("behavior_regression",)),
        (aaf_verify_diag, ("diag_regression", "degraded")),
    )
    verify = {}
    for verifier, result_fields in stages:
        reject, stage_result = _run_aaf_verify_stage(
            ctx, verifier, result_fields)
        if reject:
            return reject, {}
        ctx.side_effects = stage_result.pop("side_effects", ctx.side_effects)
        verify.update(stage_result)
    degraded = verify.pop("degraded")
    diag_report = verify.get("diag_regression")
    diag_status = (diag_report.get("status")
                   if isinstance(diag_report, dict) else None)
    if (ctx.fixed_source != ctx.original_source
            and diag_status not in {"passed", "degraded"}):
        reason = (f"诊断回归验证未获有效通过结论(status={diag_status!r})，"
                  "已拒绝写入")
        logger.warning("[AIManualFix] %s", reason)
        return aaf_reject(
            ctx, "failed", reason, event="ai_fix_failed",
            audit_reason=reason, diag_regression=diag_report), {}
    if degraded:
        verify["regression_verified"] = False
    return None, verify
__all__ = [
    'AafCtx',
    'FixSafetyNet',
    'FixSafetyVerifier',
    'FixVerificationResult',
    'RegressionOutcome',
    'aaf_verify_behavior',
    'aaf_verify_hallucination_precheck',
    'aaf_verify_inline',
    'aaf_verify_syntax_safety',
    'apply_security_write',
    'apply_verified_write',
    'detect_new_hardcoded_secrets',
    'restore_written_original',
    'rollback_unverified_fix',
    'run_fix_verify_chain',
    'run_post_write_hallucination_check',
    'verify_fix_safety',
    'verify_manual_fix',
    'write_fix_file',
]
logger.info("fix_safety_gate 修复写盘门禁域已加载: %d 项导出", len(__all__))
