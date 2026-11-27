from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys
from collections import Counter
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass
from datetime import date, datetime
from pathlib import Path
from typing import Any

from jwsgj.build_module_topology import build_import_graph
from jwsgj.build_skill_module_scan import (
    scan_file_manifest,
    scan_full_analysis_files,
)
from jwsgj.build_text_document import iter_fence_lines
from jwsgj.diag_guard_io import (
    normalize_out_path,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.log_config import get_module_logger, locked_artifact, log_swallowed
from jwsgj.refactor_split_actions import run_refactor_workflow
from jwsgj.runtime_paths import (
    get_temp_base,
    is_artifact_destination_allowed,
)
from jwsgj.shared_cache import get_warmed_cache

__all__ = [
    'BATCH_WINDOW_SECONDS',
    'FULL_TEMPLATE',
    'SYNC_CHECK_HEADER',
    'TEMPLATE_DIR',
    'TEMPLATE_FILE',
    'TRACKER_FILENAME',
    'AnalysisDocStats',
    'Phase1Tracker',
    'check_doc_kg_sync',
    'enforce_phase1_sequential',
    'generate_analysis_doc',
    'generate_knowledge_graph',
    'integrate_with_refactor',
    'main',
    'run_full_analysis',
]
_log = get_module_logger(__name__, __file__)
_log.info("build_full_analysis 已加载: %d 项导出", len(__all__))
TEMPLATE_DIR = Path(__file__).resolve().parent / "cankaowendang"
TEMPLATE_FILE = TEMPLATE_DIR / "全量分析模板_通用.md"
_DEFAULT_DRY_RUN = True
_DEFAULT_SKIP_DOCS = False
_DEFAULT_ENFORCE_PHASE1_GUARD = True
_TRUE_FLAGS = frozenset({"1", "true", "yes", "on"})
_FALSE_FLAGS = frozenset({"0", "false", "no", "off"})
def _coerce_flag(value: object, default: bool, label: str,
                 errors: list[str]) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        text = value.strip().lower()
        if text in _TRUE_FLAGS:
            return True
        if text in _FALSE_FLAGS:
            return False
    _log.warning("%s 非法布尔值(%r)，回落默认 %s", label, value, default)
    errors.append(f"{label} 非法布尔值: {value!r}，已回落默认 {default}")
    return default
@dataclass(frozen=True)
class AnalysisDocStats:
    total_file_count: int = 0
    analyzed_count: int = 0
    pending_count: int = 0
    oversized_count: int = 0
    hub_nodes: str = "（Phase 1 完成后填充）"
_PATH_COMPONENT_HAZARD_RE = re.compile(r'[\x00-\x1f\x7f/\\:<>"|?*]')
_WINDOWS_RESERVED_NAMES = frozenset({
    "CON", "PRN", "AUX", "NUL",
    *(f"COM{index}" for index in range(1, 10)),
    *(f"LPT{index}" for index in range(1, 10)),
})
def _validate_filename_component(value: str, what: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"非法{what}（须为字符串，得到 {type(value).__name__}）")
    if (not value or value in (".", "..")
            or _PATH_COMPONENT_HAZARD_RE.search(value) is not None
            or value != value.rstrip(" .")):
        raise ValueError(
            f"非法{what}（不得含路径分隔符/上跳段/盘符/控制字符/"
            f"Windows 保留字符或尾随点/空格）: {value!r}")
    if value.split(".", 1)[0].upper() in _WINDOWS_RESERVED_NAMES:
        raise ValueError(
            f"非法{what}（不得使用 Windows 设备名，含带扩展名形态）: {value!r}")
    return value
def generate_analysis_doc(
    skill_name: str,
    output_dir: str | None = None,
    target_date: str | None = None,
    stats: AnalysisDocStats | None = None,
) -> str:
    if stats is not None and not isinstance(stats, AnalysisDocStats):
        raise TypeError(
            f"stats 须为 AnalysisDocStats，得到 {type(stats).__name__}")
    _stats = stats if stats is not None else AnalysisDocStats()
    _output_dir, _date, _doc_path = _prepare_doc_target(
        skill_name, normalize_out_path(output_dir), target_date, "全量分析")
    content = _substitute(_read_template(), {
        "{skill_name}": skill_name,
        "{output_path}": _output_dir.as_posix(),
        "{date}": _date,
        "{total_file_count}": str(_stats.total_file_count),
        "{analyzed_count}": str(_stats.analyzed_count),
        "{pending_count}": str(_stats.pending_count),
        "{oversized_count}": str(_stats.oversized_count),
        "{hub_nodes}": _stats.hub_nodes,
    })
    return _write_doc_once(_doc_path, content, "全量分析文档")
def generate_knowledge_graph(
    skill_name: str,
    output_dir: str | None = None,
    target_date: str | None = None,
) -> str:
    _output_dir, _date, _kg_path = _prepare_doc_target(
        skill_name, normalize_out_path(output_dir), target_date, "知识图谱")
    template_content = _read_template()
    kg_section = _extract_kg_section(template_content)
    if kg_section is None:
        raise ValueError(
            "分析模板缺少知识图谱章节（需 '# …知识图谱…' 一级标题），"
            "拒绝生成空壳知识图谱")
    content = _substitute(kg_section, {
        "{skill_name}": skill_name,
        "{output_path}": _output_dir.as_posix(),
        "{date}": _date,
    })
    return _write_doc_once(_kg_path, content, "知识图谱文档")
def _prepare_doc_target(skill_name: str, output_dir: str | None,
                        target_date: str | None, doc_label: str,
                        ) -> tuple[Path, str, Path]:
    _validate_filename_component(skill_name, "技能名")
    if target_date is not None:
        _validate_filename_component(target_date, "日期字符串")
    _date = target_date or date.today().strftime("%Y%m%d")
    out_dir = _resolve_output_dir(output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    return out_dir, _date, out_dir / f"{skill_name}_{doc_label}_{_date}.md"
def _write_doc_once(doc_path: Path, content: str, doc_label: str) -> str:
    created = False
    try:
        with open(doc_path, "x", encoding="utf-8", newline="\n") as _fh:
            created = True
            _fh.write(content)
    except FileExistsError:
        if not doc_path.is_file():
            raise
        try:
            existing_size = doc_path.stat().st_size
        except OSError:
            existing_size = -1
        if existing_size < 0:
            raise OSError(
                f"既有{doc_label}大小无法确认，拒绝复用（避免返回不存在产物）: "
                f"{doc_path}") from None
        if existing_size == 0:
            _log.warning("检测到 0 字节残留%s，按崩溃残留重写: %s",
                         doc_label, doc_path)
            try:
                with open(doc_path, "w", encoding="utf-8", newline="\n") as _fh:
                    _fh.write(content)
            except (OSError, UnicodeError) as _we:
                _discard_partial_doc(doc_path, _we)
                raise
            _log.info("%s已重写: %s", doc_label, doc_path)
            return str(doc_path)
        _log.info("同日%s已存在，复用不覆盖: %s", doc_label, doc_path)
        return str(doc_path)
    except (OSError, UnicodeError) as _we:
        if created:
            _discard_partial_doc(doc_path, _we)
        raise
    _log.info("%s已生成: %s", doc_label, doc_path)
    return str(doc_path)
def _discard_partial_doc(doc_path: Path, exc: Exception) -> None:
    try:
        if doc_path.exists() and not safe_delete(str(doc_path)):
            _log.warning("半写文档产物回收失败（需人工清理）: %s (%s)",
                         doc_path, exc)
    except OSError:
        _log.warning("半写文档产物回收异常: %s", doc_path, exc_info=True)
def _resolve_output_dir(output_dir: str | None) -> Path:
    if output_dir:
        cand = Path(output_dir).resolve()
        if not is_artifact_destination_allowed(str(cand)):
            raise RuntimeError(
                f"输出目录落点非法: {cand}——过程产物（分析文档/知识图谱）"
                "落点只能是会话工作空间（Temp 治理契约，不设其他位置兜底）；"
                "请省略 output_dir 走 get_temp_base() 归口，或传入会话"
                "工作空间内的目录。")
        return cand
    return Path(get_temp_base()).resolve()
def _read_template() -> str:
    try:
        if TEMPLATE_FILE.exists():
            text = TEMPLATE_FILE.read_text(encoding="utf-8-sig")
            if text.strip():
                return text
            _log.warning("模板文件为空（无有效骨架），回退内嵌模板: %s",
                         TEMPLATE_FILE)
    except (OSError, ValueError) as e:
        _log.warning("读取模板文件失败: %s", e)
    _log.info("使用内嵌模板（代码级固定）")
    return FULL_TEMPLATE
def _substitute(template: str, replacements: dict[str, str]) -> str:
    if not replacements:
        return template
    pattern = re.compile("|".join(re.escape(k) for k in replacements))
    return pattern.sub(
        lambda match: str(replacements[match.group(0)]), template)
def _extract_kg_section(full_content: str) -> str | None:
    lines = full_content.splitlines()
    fence_states = [in_fence for _line, in_fence in iter_fence_lines(lines)]
    start = next((i for i, line in enumerate(lines)
                  if line.lstrip().startswith("# ") and "知识图谱" in line), None)
    if start is None:
        return None
    started_in_fence = fence_states[start]
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if started_in_fence:
            if not fence_states[index]:
                end = index
                break
        elif not fence_states[index] and _is_kg_section_end(lines[index]):
            end = index
            break
    return "\n".join(lines[start:end])
def _is_kg_section_end(line: str) -> bool:
    stripped = line.strip()
    return (stripped.startswith("# ")
            or re.match(r"#{1,2}\s*Phase\b", stripped, re.IGNORECASE) is not None)
_OVERSIZED_BYTES = 250 * 1024
_SMALL_FILE_BYTES = 20 * 1024
def _entry_size_bytes(entry: dict[str, Any]) -> int | None:
    if not isinstance(entry, dict):
        return None
    size_bytes = entry.get("size_bytes")
    if isinstance(size_bytes, int) and not isinstance(size_bytes, bool):
        return size_bytes if size_bytes >= 0 else None
    size_kb = entry.get("size_kb")
    if size_kb is None or isinstance(size_kb, bool):
        return None
    try:
        kb_value = float(size_kb)
    except (TypeError, ValueError, OverflowError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_entry_size_bytes:invalid_size')
        return None
    if not math.isfinite(kb_value) or kb_value < 0:
        return None
    bytes_value = kb_value * 1024
    return int(bytes_value) if math.isfinite(bytes_value) else None
def _is_oversized_entry(entry: dict[str, Any]) -> bool:
    size = _entry_size_bytes(entry)
    return size is not None and size > _OVERSIZED_BYTES
def _is_small_entry(entry: dict[str, Any]) -> bool:
    size = _entry_size_bytes(entry)
    return size is not None and size < _SMALL_FILE_BYTES
def _generate_docs_stage(
    skill_name: str,
    output_dir: str | None,
    skip_docs: bool,
    result: dict[str, Any],
) -> None:
    if skip_docs:
        _log.info("跳过文档生成（skip_docs=True），直接执行核心分析")
        return
    target_date = date.today().strftime("%Y%m%d")
    stats = _analysis_doc_stats(result.get("file_manifest") or [],
                                result.get("phase1_guard") or {})
    result["analysis_doc"] = _generate_doc_artifact(
        result, "分析文档", "文档生成跳过",
        lambda: generate_analysis_doc(
            skill_name, output_dir, target_date=target_date, stats=stats))
    result["knowledge_graph"] = _generate_doc_artifact(
        result, "知识图谱", "知识图谱生成跳过",
        lambda: generate_knowledge_graph(
            skill_name, output_dir, target_date=target_date))
def _analysis_doc_stats(
    manifest: list[dict[str, Any]],
    phase1_guard: dict[str, Any],
) -> AnalysisDocStats:
    readiness = (phase1_guard.get("readiness")
                 if isinstance(phase1_guard, dict) else None)
    analyzed: object = 0
    if isinstance(readiness, dict):
        analyzed = readiness.get("analyzed_count") or 0
    try:
        analyzed = (0 if isinstance(analyzed, bool)
                    else min(max(int(analyzed), 0), len(manifest)))
    except (TypeError, ValueError, OverflowError) as exc:
        log_swallowed(
            __name__, exc, context="_analysis_doc_stats:analyzed_count")
        analyzed = 0
    return AnalysisDocStats(
        total_file_count=len(manifest),
        analyzed_count=analyzed,
        pending_count=len(manifest) - analyzed,
        oversized_count=sum(1 for entry in manifest
                            if _is_oversized_entry(entry)),
    )
def _generate_doc_artifact(
    result: dict[str, Any],
    label: str,
    error_prefix: str,
    generator: Callable[[], str],
) -> str:
    try:
        return generator()
    except (OSError, ValueError, RuntimeError) as e:
        _log.warning("%s生成失败（跳过，继续核心分析）: %s", label, e)
        result["errors"].append(f"{error_prefix}: {e}")
        return ""
def _init_phase1_guard_stage(
    skill_dir: str,
    enforce_phase1_guard: bool,
    result: dict[str, Any],
) -> None:
    if not (enforce_phase1_guard and skill_dir and os.path.isdir(skill_dir)):
        return
    try:
        tracker = Phase1Tracker(skill_dir)
        readiness = tracker.check_phase1_readiness()
    except (OSError, ValueError, RuntimeError, TypeError,
            RecursionError) as exc:
        _log.warning("Phase1 守卫初始化失败（降级跳过）: %s", exc, exc_info=True)
        result["errors"].append(f"Phase1 守卫初始化失败: {exc}")
        return
    result["phase1_guard"] = {
        "tracker_path": tracker.tracker_path,
        "total_files": tracker.total_files,
        "readiness": readiness,
    }
    _log.info("Phase1Tracker 就绪: %d 个文件待分析", tracker.total_files)
def run_full_analysis(
    skill_name: str,
    skill_dir: str,
    output_dir: str | None = None,
    dry_run: bool = _DEFAULT_DRY_RUN,
    skip_docs: bool = _DEFAULT_SKIP_DOCS,
    enforce_phase1_guard: bool = _DEFAULT_ENFORCE_PHASE1_GUARD,
) -> dict[str, Any]:
    result: dict[str, Any] = {
        "ok": True, "analysis_doc": "", "knowledge_graph": "",
        "file_manifest": [], "plan": {}, "errors": [],
        "phase1_guard": {},
        "data_profile": {},
    }
    root_text = normalize_out_path(skill_dir)
    if root_text is None or not os.path.isdir(root_text):
        result["ok"] = False
        result["errors"].append(
            f"skill_dir 非法或不是目录: {skill_dir!r}")
        return result
    try:
        _validate_filename_component(skill_name, "技能名")
    except (TypeError, ValueError) as exc:
        result["ok"] = False
        result["errors"].append(f"skill_name 非法: {exc}")
        return result
    output_dir = normalize_out_path(output_dir)
    dry_run = _coerce_flag(
        dry_run, _DEFAULT_DRY_RUN, "dry_run", result["errors"])
    skip_docs = _coerce_flag(
        skip_docs, _DEFAULT_SKIP_DOCS, "skip_docs", result["errors"])
    enforce_phase1_guard = _coerce_flag(
        enforce_phase1_guard, _DEFAULT_ENFORCE_PHASE1_GUARD,
        "enforce_phase1_guard", result["errors"])
    try:
        get_warmed_cache(root_text)
    except Exception as _warm_exc:
        log_swallowed(__name__, _warm_exc,
                      context="run_full_analysis:warm_cache")
        result["errors"].append(f"缓存预热失败（降级继续）: {_warm_exc}")
    _init_phase1_guard_stage(root_text, enforce_phase1_guard, result)
    _scan_stage(root_text, result)
    if not result["ok"]:
        return result
    _generate_docs_stage(skill_name, output_dir, skip_docs, result)
    result["plan"] = _integrate_refactor_stage(
        result["analysis_doc"], root_text, dry_run, result)
    return result
def _scan_stage(skill_dir: str, result: dict[str, Any]) -> None:
    try:
        manifest, data_profile = scan_full_analysis_files(skill_dir)
    except (OSError, ValueError) as e:
        _log.error("扫描文件清单失败: %s", e, exc_info=True)
        result["errors"].append(f"文件扫描失败: {e}")
        result["ok"] = False
        return
    result["file_manifest"] = manifest
    result["data_profile"] = data_profile
def _integrate_refactor_stage(analysis_doc: str, skill_dir: str,
                              dry_run: bool,
                              result: dict[str, Any]) -> dict[str, Any]:
    try:
        return integrate_with_refactor(analysis_doc, skill_dir, dry_run,
                                       manifest=result["file_manifest"] or None)
    except Exception as e:
        _log.warning("集成重构管线异常: %s", e)
        result["errors"].append(f"重构管线集成异常: {e}")
        return {}
def integrate_with_refactor(
    analysis_doc_path: str,
    skill_dir: str,
    dry_run: bool = _DEFAULT_DRY_RUN,
    manifest: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    refactor_result = _try_call_refactor(skill_dir, dry_run)
    if refactor_result is not None:
        return refactor_result
    return _generate_basic_plan_from_doc(analysis_doc_path, skill_dir, dry_run,
                                         manifest=_manifest_entries(manifest))
def _try_call_refactor(skill_dir: str, dry_run: bool) -> dict[str, Any] | None:
    try:
        result = run_refactor_workflow(skill_dir, dry_run=dry_run)
        if result is not None and not isinstance(result, dict):
            _log.warning(
                "_try_call_refactor: 返回契约异常(%s)，走文档基线降级",
                type(result).__name__)
            return None
        return result
    except Exception:
        _log.warning("_try_call_refactor: 重构管线调用失败，走文档基线降级",
                     exc_info=True)
        return None
def _generate_basic_plan_from_doc(
    doc_path: str, skill_dir: str, dry_run: bool,
    manifest: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    if manifest is None:
        manifest = scan_file_manifest(skill_dir)
    return {
        "ok": True,
        "skill_dir": skill_dir,
        "analysis_doc": doc_path,
        "dry_run": dry_run,
        "status": "preview" if dry_run else "ready",
        "actions": [],
        "observations": _plan_observations(manifest),
    }
def _manifest_entries(
    manifest: object,
) -> list[dict[str, Any]] | None:
    if manifest is None:
        return None
    if not isinstance(manifest, (list, tuple)):
        _log.warning("manifest 非序列形态（%s），按未提供处理",
                     type(manifest).__name__)
        return None
    return [item for item in manifest if isinstance(item, dict)]
def _plan_observations(manifest: list[dict[str, Any]]) -> dict[str, Any]:
    entries = []
    for item in manifest:
        if not isinstance(item, dict):
            continue
        filename = item.get("filename")
        if not isinstance(filename, str) or not filename.strip():
            continue
        entries.append((item, filename.strip()))
    oversized = [name for item, name in entries
                 if _is_oversized_entry(item)]
    small_files = [name for item, name in entries
                   if _is_small_entry(item)]
    return {
        "total_files": len(entries),
        "oversized_files": len(oversized),
        "small_files": len(small_files),
        "oversized_details": oversized,
        "small_details": small_files,
    }
def main() -> int:
    parser = argparse.ArgumentParser(description="全量分析模板引擎")
    parser.add_argument("--skill", required=True, help="目标技能名称")
    parser.add_argument("--dir", required=True, help="技能目录路径")
    parser.add_argument("--output", default=None, help="输出目录（默认经 get_temp_base() 归口）")
    parser.add_argument("--dry-run", action=argparse.BooleanOptionalAction,
                        default=_DEFAULT_DRY_RUN,
                        help="仅预览不修改（默认开启；--no-dry-run 实际执行）")
    parser.add_argument("--skip-docs", action="store_true",
                        default=_DEFAULT_SKIP_DOCS,
                        help="跳过文档生成，直接执行核心分析（文档不存在时使用）")
    args = parser.parse_args()
    try:
        result = run_full_analysis(
            skill_name=args.skill,
            skill_dir=args.dir,
            output_dir=args.output,
            dry_run=args.dry_run,
            skip_docs=args.skip_docs,
        )
    except Exception as e:
        _log.error("全量分析执行异常: %s", e, exc_info=True)
        print(json.dumps({"ok": False, "errors": [f"执行异常: {e}"]},
                         indent=2, ensure_ascii=False, default=str))
        return 1
    print(json.dumps(result, indent=2, ensure_ascii=False, default=str))
    return 0 if result["ok"] else 1
FULL_TEMPLATE = r"""# {skill_name} 全量分析模板（通用版）

> 本模板是通用的全量分析文档模板，通过 `{skill_name}` 参数化适配不同技能。
> 由全量分析引擎驱动，可与通用重构引擎协同工作。

***

## 核心方向与目标

对 `{skill_name}` 本目录的所有文件进行全面读取分析，以**上下文内聚重组**为导向——核心标准是**跨文件引用最少、同文件上下文消费最充分、单文件低复杂度**。通过上下文消费分析→文件的治理与合并、代码的迁入与迁出，实现每个文件对外依赖最小化，达到线性或简单网状消费。找出最佳的治理/迁入/迁出/合并方案。对于循环依赖，通过代码结构重构来消除。只合并高度内聚，跨文件消费的函数执行迁移。类聚复杂的文件按非拆分治理收敛复杂度。执行任务前必须先评估利弊关系。只有利大于弊才能执行。增加或者减少文件不能算成坏处或者好处。

### 三阶段

| 阶段 | 名称 | 核心操作 |
|------|------|----------|
| Phase 0 | 创建空白文档 + 知识图谱 | 创建空白进度追踪文档和知识图谱文件，定义好结构 |
| Phase 1 | 逐文件全读 + 即时登记 | 一次 bash 读一个文件，分析五项内容，即时写入文档+KG |
| Phase 2 | 基于完整数据执行任务 | 文档+KG已完备，评估利弊后逐步执行合并/迁入/迁出/修复/清理/非拆分治理 |

***

## Phase 0 — 创建空白文档 + 知识图谱

### 0.1 创建空白进度追踪文档

文件路径：`{output_path}/{skill_name}_全量分析_{date}.md`

文档结构如下（创建时只保留骨架，逐文件填充）。**模板设计原则是"信息密度最大化"——每个表格的列都经过精心设计，确保 Phase 2 做决策时有足够的证据支撑，无需回头重读源码。**

```markdown
# {skill_name} 全量分析进度追踪（{date}）

## 一、全量文件清单（待填充）

| 文件名 | 大小(KB) | 行数 | 功能域 | 入度 | 出度 | 跨文件import行数 | 公开符号数 | 分析状态 | 缺陷数 | 死代码数 | 是否超250KB |
|--------|---------|------|--------|------|------|----------------|-----------|---------|--------|---------|-------------|
| （Phase 1 逐文件填充） | | | | | | | | | | | |

## 二、逐文件分析记录（Phase 1 逐文件追加）

### 文件: xxx.py

#### 基本信息
| 字段 | 值 |
|------|-----|
| 大小 | N KB |
| 行数 | N |
| 功能域 | xxx |
| 公开符号数 | N（__all__ 中 N 个） |
| 超250KB | 是/否 |
| 缺陷总数 | N（P0:P1:P2 = N:N:N） |
| 死代码数 | N（HIGH:MEDIUM = N:N） |

#### 入度符号（谁从本文件 import 了什么）
| 符号名 | 消费者文件 | 导入方式 | 消费行号 | 消费次数 | 是否在__all__ | 是否被re-export |
|--------|-----------|---------|---------|---------|-------------|----------------|
| func_a | B.py | from A import func_a | 42 | 3 | 是 | 否 |
| ClassX | B.py, C.py | from A import ClassX | 15, 88 | 2 | 是 | 否 |

#### 出度符号（本文件从谁 import 了什么）
| 符号名 | 定义源文件 | 符号类型 | 导入方式 | 导入行号 | 本文件内使用频次 | 全库消费者数 | 消费判定 | 是否在__all__ | 是否在lazy_imports |
|--------|-----------|---------|---------|---------|----------------|-------------|---------|-------------|-------------------|
| func_y | B.py | 函数 | from B import func_y | 10 | 5 | 1 | 独占 | 否 | 否 |
| ClassZ | C.py | 类 | from C import ClassZ | 12 | 2 | 3 | 共享(3) | 是 | 否 |
| BaseType | L0.py | 类 | from L0 import BaseType | 5 | 8 | 112 | 底座(112) | 是 | 否 |
| Registry | build.py | 函数 | from build import Registry | 20 | 1 | 15 | 枢纽(15) | 是 | 否 |

**消费判定规则**：
- **独占**：全库仅本文件 import → 强迁入候选
- **共享(N)**：被 N 个文件 import（2 ≤ N ≤ 4）→ 中迁入候选
- **底座(N)**：被 N 个模块 import（N ≥ 5）→ 保留
- **枢纽(N)**：注册器/调度器/枢纽函数（N ≥ 5）→ 保留

#### 出度符号详细依赖链（迁入证据）
对每个独占/共享消费的符号，追踪其内部调用链，评估迁入可行性：

| 符号名 | 依赖的内部符号 | 依赖的共享工具 | 依赖的共享工具全库消费者数 | 依赖链评估 |
|--------|--------------|---------------|------------------------|-----------|
| func_y | _helper_a, _helper_b | format_report (build_utils) | 23 | 依赖共享工具format_report，迁入时需函数级导入 |
| ClassZ | _validate, _transform | 无 | 0 | 无共享依赖，可直接迁入 |

#### 循环依赖检测（本文件参与）
| 环编号 | 环路径 | 环类型 | 参与方 | 建议消除方案 |
|--------|--------|--------|--------|-------------|
| 环1 | A.py → B.py → C.py → A.py | 多节点聚合 | A.py (本文件), B.py, C.py | 提取共享定义到 L0 底座 |
| 环2 | A.py → D.py → A.py | 简单双向 | A.py (本文件), D.py | 提取共享定义到 L0 底座 |

#### 逻辑缺陷
| 优先级 | 行号 | 缺陷类型 | 缺陷描述 | 根因 | 影响范围 | 修复方案 | 修复复杂度 |
|--------|------|---------|---------|------|---------|---------|-----------|
| P0 | 120 | 跨函数参数错位 | _validate() 调用 _check() 时实参顺序与签名不匹配 | 调用方未按命名参数传参，依赖位置匹配 | 该函数路径全部调用方 | 改为关键字参数 | 低 |
| P1 | 200 | 空壳桩函数 | fallback_handler() 返回 None 而非有效结果对象 | 可选依赖降级时未提供有效 fallback | 所有调用方在降级路径触发 AttributeError | 返回有效空对象 | 低 |

#### 代码缺陷
| 优先级 | 行号 | 缺陷类型 | 缺陷描述 | 根因 | 影响范围 | 修复方案 | 修复复杂度 |
|--------|------|---------|---------|------|---------|---------|-----------|
| P0 | 55 | @dataclass 缺失 | class Config 定义类型注解字段但未加 @dataclass | 类定义时遗漏装饰器 | 实例化时 TypeError | 添加 @dataclass | 低 |
| P1 | 88 | 同名import覆盖本地定义 | 本地定义 class Optimizer 后被 from X import Optimizer 覆盖 | import 在定义之后，模块加载顺序覆盖 | 所有使用本地 Optimizer 的代码 | 别名化 import 或删除无消费者 import | 中 |

#### 其他BUG
| 优先级 | 行号 | BUG类型 | BUG描述 | 根因 | 影响范围 | 修复方案 | 修复复杂度 |
|--------|------|---------|---------|------|---------|---------|-----------|
| P1 | 150 | 变量名不一致 | exception 变量捕获时用 _rb_err，后续引用用 rollback_error | 同一回滚错误两个变量名 | 日志记录路径静默失败 | 统一变量名 | 低 |
| P2 | 300 | finally块掩盖异常 | finally 中执行清理时抛出异常，掩盖了 try 块中的原始异常 | 清理代码未做异常隔离 | 调试时丢失原始异常上下文 | finally 内加 try/except | 低 |

#### 死代码
| 优先级 | 行号 | 符号名 | 类型 | 引擎A(静态引用) | 引擎B(诊断调用图) | 交叉验证 | 是否在__all__ | 是否被测试引用 | 是否动态注册 | 综合判定 |
|--------|------|--------|------|----------------|------------------|---------|-------------|-------------|-------------|---------|
| HIGH | 45 | unused_func | 函数 | 0引用 | 0引用 | 一致零引用 | 否 | 否 | 否 | 可清理 |
| HIGH | 78 | old_constant | 变量 | 0引用 | 0引用 | 一致零引用 | 否 | 否 | 否 | 可清理 |
| MEDIUM | 120 | _legacy_helper | 函数 | 0引用 | 2引用(字符串) | 引擎A零/引擎B有 | 否 | 否 | 是(globals()) | 需复核 |
| MEDIUM | 200 | DeprecatedClass | 类 | 0引用 | 0引用 | 一致零引用 | 是 | 否 | 否 | 需复核(__all__中有) |

#### 合并/治理证据（预评估）
| 维度 | 内容 |
|------|------|
| 本文件功能域 | xxx |
| 同域候选文件 | A.py, B.py（同属 xxx 域） |
| 与候选的符号重叠 | func_a 与 A.py 的 func_b 属同一业务流程 |
| 与候选的依赖方向 | 本文件 → A.py（3条import），A.py → 本文件（1条import） |
| 合并后大小预估 | 本文件 120KB + A.py 80KB = 200KB（未超250KB） |
| 合并后内聚度变化 | 提升（func_a 和 func_b 同属验证流程，合并后消除跨文件调用） |
| 合并风险 | 无命名冲突，logger 均为 `__name__` 标准格式 |

#### 迁入/迁出证据（预评估）
| 维度 | 内容 |
|------|------|
| 本文件独占消费的符号 | func_y（来自 B.py，全库仅本文件 import） |
| 本文件共享消费的符号 | ClassZ（来自 C.py，本文件 + D.py 共 2 个消费者） |
| 迁入收益 | 迁入 func_y 减少 1 条跨文件引用；迁入 ClassZ 再减少 1 条 |
| 迁入后文件大小 | 当前 120KB + func_y 2KB + ClassZ 3KB = 125KB（未超250KB） |
| 迁入风险 | func_y 依赖共享工具 format_report，需函数级导入 |

#### 备注
- 过渡性备注、跨批协调、特殊说明
- 本文件与 D.py 存在双向紧耦合，建议将 D.py 移入本批

### 文件: yyy.py
...

## 三、全量依赖矩阵（Phase 1 逐文件追加）

### 3.1 模块级依赖图（有向边列表）
| 源文件 | 目标文件 | 导入符号 | 符号类型 | 消费性质 | 导入行号 | 是否函数级导入 |
|--------|---------|---------|---------|---------|---------|--------------|
| A.py | B.py | func_y | 函数 | 独占 | 10 | 否 |
| A.py | C.py | ClassZ, func_w | 类, 函数 | 共享(3) | 12, 15 | 否 |
| A.py | L0.py | BaseType | 类 | 底座(112) | 5 | 否 |

### 3.2 循环依赖链（Phase 1 逐文件检测，发现即登记）
| 环编号 | 环路径 | 环类型 | 参与文件 | 关键边 | 建议消除方案 | 消除优先级 |
|--------|--------|--------|---------|--------|-------------|-----------|
| 环1 | A → B → C → A | 多节点聚合 | A, B, C | A→B: func_y, B→C: ClassZ, C→A: func_x | 提取 func_x 到 L0 底座 | P0 |
| 环2 | A → D → A | 简单双向 | A, D | A→D: helper, D→A: validate | 提取 validate 到 L0 底座 | P0 |

### 3.3 枢纽节点（入度≥5 或 出度≥5）
| 文件名 | 入度 | 出度 | 公开符号数 | 大小(KB) | 角色说明 |
|--------|------|------|-----------|---------|---------|
| A.py | N | N | N | N | 核心共享模块，按目标项目实测结果评估 |
| B.py | N | N | N | N | 调度枢纽，按目标项目实测结果评估 |
| C.py | N | N | N | N | 注册枢纽，按目标项目实测结果评估 |

## 四、迁入候选清单（Phase 1 逐文件追加）

### 4.1 独占消费迁入候选（P0）
| 优先级 | 源文件 | 符号名 | 符号类型 | 消费者文件 | 源文件行号 | 依赖链评估 | 迁入后大小 | 预计净减依赖 | 决策备注 |
|--------|--------|-------|---------|-----------|-----------|-----------|-----------|------------|---------|
| P0 | B.py | func_y | 函数 | A.py | 45 | 依赖共享工具 format_report，需函数级导入 | 120KB→122KB | -1 | 评估后执行 |
| P0 | C.py | _helper_transform | 函数 | A.py | 120 | 无共享依赖 | 122KB→123KB | -1 | 评估后执行 |

### 4.2 共享消费迁入候选（P1）
| 优先级 | 源文件 | 符号名 | 符号类型 | 消费者文件 | 源文件行号 | 全库消费者数 | 上下文贴合度 | 依赖链评估 | 迁入后大小 | 预计净减依赖 | 决策备注 |
|--------|--------|-------|---------|-----------|-----------|------------|------------|-----------|-----------|------------|---------|
| P1 | C.py | ClassZ | 类 | A.py, D.py | 200 | 2 | 高（本文件与A.py同属验证域） | 依赖共享工具 validate，需函数级导入 | 123KB→126KB | -1 | 评估后执行 |
| P1 | E.py | format_item | 函数 | A.py, D.py, F.py | 55 | 3 | 中（本文件与A.py分属不同域） | 无共享依赖 | 126KB→127KB | -1 | 需评估上下文贴合度 |

### 4.3 不迁入候选（记录理由）
| 源文件 | 符号名 | 符号类型 | 消费者文件 | 不迁入原因 |
|--------|-------|---------|-----------|-----------|
| L0.py | BaseType | 类 | A.py, B.py, C.py, ... (112个) | 底座消费，5+ 模块共享 |
| build.py | Registry | 函数 | A.py, D.py, ... (15个) | 枢纽消费，注册器/调度器 |

## 五、缺陷修复清单（Phase 1 逐文件追加）

| 优先级 | 文件 | 行号 | 缺陷类型 | 缺陷子类 | 缺陷描述 | 根因 | 影响范围 | 修复方案 | 修复复杂度 | 是否热路径 | 是否有测试覆盖 | 决策备注 |
|--------|------|------|---------|---------|---------|------|---------|---------|-----------|-----------|--------------|---------|
| P0 | xxx.py | 120 | 逻辑缺陷 | 跨函数参数错位 | _validate() 调用 _check() 时实参顺序与签名不匹配 | 调用方未按命名参数传参，依赖位置匹配 | 该函数路径全部调用方 | 改为关键字参数 | 低 | 是 | 有 | 必须修 |
| P0 | xxx.py | 55 | 代码缺陷 | @dataclass缺失 | class Config 定义类型注解字段但未加 @dataclass | 类定义时遗漏装饰器 | 实例化时 TypeError | 添加 @dataclass | 低 | 是 | 有 | 必须修 |
| P1 | yyy.py | 200 | 逻辑缺陷 | 空壳桩函数 | fallback_handler() 返回 None 而非有效结果对象 | 可选依赖降级时未提供有效 fallback | 所有调用方在降级路径触发 AttributeError | 返回有效空对象 | 低 | 否 | 无 | 评估后修 |
| P2 | xxx.py | 300 | 其他BUG | finally掩盖异常 | finally 中执行清理时抛出异常，掩盖了 try 块中的原始异常 | 清理代码未做异常隔离 | 调试时丢失原始异常上下文 | finally 内加 try/except | 低 | 否 | 无 | 无害冗余，记录 |

## 六、死代码清理清单（Phase 1 逐文件追加）

| 优先级 | 文件 | 行号 | 符号名 | 类型 | 引擎A(静态引用) | 引擎B(诊断调用图) | 交叉验证 | 是否在__all__ | 是否被测试引用 | 是否动态注册 | 是否re-export | 综合判定 | 决策备注 |
|--------|------|------|--------|------|----------------|------------------|---------|-------------|-------------|-------------|-------------|---------|---------|
| HIGH | xxx.py | 45 | unused_func | 函数 | 0引用 | 0引用 | 一致零引用 | 否 | 否 | 否 | 否 | 可清理 | 直接清理 |
| HIGH | xxx.py | 78 | old_constant | 变量 | 0引用 | 0引用 | 一致零引用 | 否 | 否 | 否 | 否 | 可清理 | 直接清理 |
| MEDIUM | xxx.py | 120 | _legacy_helper | 函数 | 0引用 | 2引用(字符串) | 不一致 | 否 | 否 | 是(globals()) | 否 | 需复核 | 字符串引用，不清理 |
| MEDIUM | yyy.py | 200 | DeprecatedClass | 类 | 0引用 | 0引用 | 一致零引用 | 是 | 否 | 否 | 否 | 需复核 | __all__ 中有，先检查消费者 |

## 七、执行计划（Phase 2 生成）

### 7.1 合并候选
| 优先级 | 操作 | 源文件1 | 源文件2 | 目标文件 | 源文件1大小 | 源文件2大小 | 合并后大小 | 预计净减引用 | 命名冲突 | 利弊评估 | 风险 |
|--------|------|---------|---------|---------|-----------|-----------|-----------|------------|---------|---------|------|
| P0 | 合并 | A.py | B.py | A.py | 120KB | 45KB | 165KB | -3 | 无 | 利: 减少跨文件引用3条, 同域内聚提升 / 弊: 增大目标文件45KB | 无 |
| P1 | 合并 | C.py | D.py | C.py | 80KB | 35KB | 115KB | -2 | 无 | 利: 减少跨文件引用2条 / 弊: 无 | 无 |

### 7.2 治理候选（GOV-01：禁止拆分文件/模块）
| 优先级 | 操作 | 目标文件 | 治理手段 | 复杂度来源 | 预计 API 变化 | 预计新增依赖 | 利弊评估 | 风险 |
|--------|------|---------|---------|-----------|--------------|------------|---------|------|
| P0 | 治理 | big.py | 消除重复 + 提取同模块私有实现 | 6 组重复实现、4 个超长函数 | 0（不新增导出） | 0 | 利: 类聚复杂度降低、单文件维持既有边界 / 弊: 单文件仍较大但职责收敛 | 需逐段回归，禁止为降行数新建文件 |

### 7.3 迁入/迁出执行项
| 优先级 | 操作 | 目标文件 | 源文件 | 符号 | 符号类型 | 源文件行号 | 迁入后大小 | 预计净减依赖 | 依赖链评估 | 利弊评估 | 风险 |
|--------|------|---------|--------|------|---------|-----------|-----------|------------|-----------|---------|------|
| P0 | 迁入 | A.py | B.py | func_y | 函数 | 45 | 120KB→122KB | -1 | 依赖共享工具 format_report，需函数级导入 | 利: 减少跨文件引用 / 弊: 引入函数级导入1条 | 低 |
| P1 | 迁入 | A.py | C.py | ClassZ | 类 | 200 | 122KB→125KB | -1 | 依赖共享工具 validate，需函数级导入 | 利: 减少跨文件引用 / 弊: 引入函数级导入1条 | 低 |

### 7.4 缺陷修复项
| 优先级 | 引用 | 文件 | 行号 | 缺陷类型 | 修复方案 | 利弊评估 |
|--------|------|------|------|---------|---------|---------|
| P0 | 五 | xxx.py | 120 | 逻辑缺陷 | 改为关键字参数 | 利: 消除BUG / 弊: 无 |
| P0 | 五 | xxx.py | 55 | 代码缺陷 | 添加 @dataclass | 利: 消除BUG / 弊: 无 |

### 7.5 死代码清理项
| 优先级 | 引用 | 文件 | 行号 | 符号名 | 类型 | 利弊评估 |
|--------|------|------|------|--------|------|---------|
| HIGH | 六 | xxx.py | 45 | unused_func | 函数 | 利: 减少冗余 / 弊: 无 |
| HIGH | 六 | xxx.py | 78 | old_constant | 变量 | 利: 减少冗余 / 弊: 无 |

## 八、执行进度

| 序号 | 操作类型 | 操作详情 | 文件 | 利弊评估结论 | 状态 | 完成时间 |
|------|---------|---------|------|------------|------|---------|
| 1 | 迁入 | 迁入 func_y (B.py→A.py) | A.py | 利大于弊 → 执行 | 待执行 | |
| 2 | 治理 | 治理 big.py（消除重复 + 提取私有实现，不拆分） | big.py | 利大于弊 → 执行 | 待执行 | |
| 3 | 合并 | 合并 B.py → A.py | A.py | 利大于弊 → 执行 | 待执行 | |
| 4 | 修复 | 修复 @dataclass 缺失 | xxx.py | 利大于弊 → 执行 | 待执行 | |
| ... | ... | ... | ... | ... | ... | |

## 九、汇总统计

### 基线数据（Phase 1 完成后）
| 指标 | 迁移前 | 迁移后 | 净变化 |
|------|--------|--------|--------|
| 模块总数 | （Phase 1 完成后填充） | （Phase 2 完成后更新） | |
| 总大小 | （Phase 1 完成后填充） | | |
| 跨文件引用总数 | （Phase 1 完成后填充） | | |
| 循环依赖数 | （Phase 1 完成后填充） | | |
| 超250KB文件数 | （Phase 1 完成后填充） | | |
| 缺陷总数 | （Phase 1 完成后填充） | | |
| 死代码总数 | （Phase 1 完成后填充） | | |

### 关键质量指标
| 指标 | 目标值 | 当前值 |
|------|--------|--------|
| 最大文件大小 | ≤250KB | |
| 模块级0环 | 是 | |
| 跨文件引用净减少 | 正数 | |
| 全库import 0失败 | 是 | |
| 全量pytest回归通过 | 是 | |
```

### 0.2 创建空白知识图谱文件

文件路径：`{output_path}/{skill_name}_知识图谱_{date}.md`

知识图谱的核心作用是**可查询的依赖拓扑**——Phase 1 逐文件填充，Phase 2 基于图谱做决策。

```markdown
# {skill_name} 知识图谱（{date}）

## 节点定义
每个 `.py` 文件 = 一个节点

## 边定义
每条 `from X import Y` 关系 = 一条有向边（源文件→目标文件）

## 一、节点列表（Phase 1 逐文件追加）

| 文件名 | 域 | 大小(KB) | 行数 | 公开符号数 | 入度 | 出度 | 总缺陷数 | 死代码数 |
|--------|-----|---------|------|-----------|------|------|---------|---------|
| | | | | | | | | |

## 二、边列表（有向边，Phase 1 逐文件追加）

| 源文件 | 目标文件 | 导入符号 | 符号类型 | 消费性质 | 备注 |
|--------|---------|---------|---------|---------|------|
| A.py | B.py | func_x, func_y | 函数/类/变量 | 独占/共享(N)/枢纽/底座 | |
| A.py | L0.py | BaseType | 类 | 底座(15+) | L0共享 |

## 三、符号索引（Phase 1 逐文件追加）

| 符号名 | 定义文件 | 类型 | 消费者列表 | 消费性质 | 是否在__all__ |
|--------|---------|------|-----------|---------|-------------|
| func_x | B.py | 函数 | A.py, C.py | 共享(2) | 是 |
| BaseType | L0.py | 类 | A.py, B.py, C.py, D.py, E.py, ... | 底座(15+) | 是 |

## 四、循环依赖图（Phase 1 检测到即登记）

### 环1: A.py → B.py → C.py → A.py
- 边: A.py from B import func_y
- 边: B.py from C import ClassZ
- 边: C.py from A import func_x
- 消除方案: 提取 func_x 到 L0 底座，或重构 A 消除对 C 的依赖

### 环2: ...
- 消除方案: ...

## 五、枢纽节点（Phase 1 逐文件更新）

| 文件名 | 入度 | 出度 | 角色说明 |
|--------|------|------|---------|
| A.py | N | N | 核心共享模块，按目标项目实测结果评估 |
| B.py | N | N | 调度枢纽，按目标项目实测结果评估 |

## 六、消费聚类（Phase 1 完成后生成）

### 聚类1: 示例功能域
- 文件: A.py, B.py, C.py, ...
- 总大小: N KB
- 内部依赖: 高度内聚
- 外部依赖: → D.py, → E.py

### 聚类2: 另一功能域
...
```

***

## Phase 1 — 逐文件全读 + 即时登记

### 1.1 读取顺序

按**入口→被消费最多的核心→外围**的顺序读取，确保依赖信息在登记时已有上下文：

1. 先扫描全量文件清单（统计大小/行数/功能域），写入文档"一、全量文件清单"的骨架
2. 按依赖层级：目标项目实测入口文件 → 实测被消费最多的核心文件 → 外围文件
3. 每个文件为一次独立的 bash 调用

### 1.2 单文件读取与分析流程

对每个文件，用 bash 一次读取全文并执行以下分析：

**步骤1：bash 全读**
执行 `python -c "..."` 或 `cat 文件名.py` 读取全文，同时运行 AST 分析脚本提取结构化信息。

**步骤2：提取五项分析结果**

使用 Python 脚本分析（写入 .py 文件后执行）：

```
① 上下文消费关系：
   - 入度符号：grep 全库 "from 本文件 import" / "from 本文件.xx import"
   - 出度符号：本文件所有 from X import Y，按 Y 被全库消费数判定消费性质
     - Y 仅被本文件 import → 独占消费 → 强迁入候选
     - Y 被 2-4 个文件 import → 共享消费 → 中迁入候选
     - Y 被 5+ 模块 import → 底座消费 → 保留
     - Y 是注册器/调度器/枢纽函数 → 枢纽消费 → 保留
   - 导出符号列表：本文件 __all__ 或模块级公开符号

② 逻辑缺陷：
   - 函数签名参数与调用方实参位置错位
   - 跨函数统计口径不一致（相同指标不同计算方式）
   - 常量语义跨域误用
   - 异常降级返回类型不一致
   - 空壳桩函数返回 None 而非有效结果对象

③ 代码缺陷：
   - @dataclass 装饰器缺失
   - 双重 __init__ 方法覆盖
   - 同名 import 覆盖本地定义
   - import 被 docstring 吞掉
   - 模块级别名缺失（_ast, _re, _dcv 等）
   - 前向引用（类/函数定义前使用）

④ 其他BUG：
   - 变量名不一致（同一概念不同变量名）
   - 异常变量作用域错误
   - finally 块掩盖异常
   - 空转未接入（函数体为空或仅 pass）
   - 键名口径不一致

⑤ 死代码：
   - 函数/类/变量在模块内和全库均无引用
   - 未被 __all__ 导出且无消费者
   - 交叉验证：引擎A（静态引用链） + 引擎B（诊断调用图D1）双引擎一致零引用 → HIGH
   - 单引擎检出 → MEDIUM
```

**步骤3：即时写入文档 + 知识图谱**

每分析完一个文件，立即执行：

1. 追加到文档"二、逐文件分析记录"的对应条目
2. 更新文档"三、全量依赖矩阵"的相应行
3. 追加到知识图谱"二、边列表"和"三、符号索引"
4. 检测到循环依赖时，立即登记到知识图谱"四、循环依赖图"
5. 检测到迁入候选时，立即追加到文档"四、迁入候选清单"
6. 检测到缺陷时，立即追加到文档"五、缺陷修复清单"
7. 检测到死代码时，立即追加到文档"六、死代码清理清单"

### 1.3 单次 bash 调用模板

```bash
# 1. 读取文件全文
cat /path/to/file.py

# 2. 运行 AST 分析脚本提取结构化信息
python /path/to/analyze_single_file.py --file /path/to/file.py

# 3. 运行消费关系分析
python /path/to/consumption_analysis.py --file /path/to/file.py

# 4. 运行死代码检测
python /path/to/deadcode_check.py --file /path/to/file.py
```

> **约束**：一次 bash 调用只分析一个文件。多个文件的分析必须分开调用，确保每次的结果都能即时登记到文档和知识图谱后再处理下一个。

### 1.4 全量读取完成信号

当文档"一、全量文件清单"中所有文件的分析状态都变为"已完成"时，Phase 1 结束。此时进入 Phase 2。

***

## Phase 2 — 基于完整文档+知识图谱执行任务

此时文档和知识图谱已包含：

* 全量依赖图（所有边）
* 完整循环依赖链
* 迁入候选清单（已按优先级排序）
* 缺陷修复清单（已按严重度排序）
* 死代码清理清单（已按可信度排序）
* 消费聚类分组（Phase 1 完成后生成）

### 2.1 核心原则：利弊评估先行

**每项操作（合并/迁入/迁出/修复/清理/非拆分治理）执行前，必须先评估利弊关系，只有利大于弊才能执行。**

**利弊评估维度**（仅以下维度计入利弊，不得引入其他主观标准）：

| 维度 | 利（正面） | 弊（负面） |
|------|-----------|-----------|
| 跨文件引用 | 减少跨文件引用数 | 增加跨文件引用数 |
| 上下文消费 | 符号同文件化，消费更充分 | 符号被分散到不同文件 |
| 内聚性 | 功能域内聚度提升 | 内聚度降低 |
| 类聚复杂度 | 文件内类聚复杂度降低 | 类聚复杂度升高 |
| 文件大小 | 超过250KB的文件降至范围内 | 未超限的文件无谓增大 |
| 循环依赖 | 消除循环依赖 | 引入新的循环依赖 |
| 缺陷与死代码 | 修复缺陷、清理死代码（净减少） | — |

**不计入利弊的维度**：

* 文件数量变化（增加或减少文件**不能算成坏处或者好处**）
* 代码行数变化（纯迁移导致的行数变化不计）

**评估记录格式**：

```
操作: 合并 A.py → B.py
利:
  - 减少跨文件引用 3 条
  - B.py 内聚度提升（原A.py的XX函数与B.py的YY类同属ZZ功能域）
弊:
  - B.py 增大 12KB（当前 180KB，合后 192KB，未超250KB限）
评估结论: 利大于弊 → 执行
```

**不执行的判定**：如果弊大于利或利弊相当，放弃该操作，在文档备注记录"评估放弃"并说明原因。

### 2.2 生成执行计划（基于文档+KG）

从文档和知识图谱中提取所有候选操作，按优先级排序，逐项评估利弊后决定是否执行：

| 优先级 | 操作类型 | 说明 |
|--------|---------|------|
| P0 | 超大文件非拆分治理 | 超250KB且功能混杂的文件，按 GOV-01 消除重复/提取模块内私有实现/收敛依赖 |
| P0 | 循环依赖消除 | 通过代码结构重构消除循环 |
| P0 | 独占消费迁入 | 迁入候选清单中"独占消费"的函数符号，净减跨文件依赖 |
| P1 | 共享消费迁入 | 2-4个消费者、上下文贴合度高的函数迁入 |
| P1 | 高度内聚合并 | 同域文件高度内聚、合并模拟无环、合后不超250KB |
| P1 | 死代码清理 | HIGH可信度的死代码清理 |
| P2 | 缺陷修复 | P0/P1缺陷修复 |
| P2 | 裂变引擎自包含化 | 向引擎文件迁入其独占消费的符号 |

### 2.3 执行顺序策略

**策略A：按依赖拓扑从下往上执行**

* 先处理 L0 底座（只被消费，不消费其他模块）
* 再处理 L1 守卫层
* 再处理 L2-L5 上层模块
* 确保下层模块变更后，上层模块的验证能捕获所有影响

**策略B：按聚类执行**

* 按知识图谱"六、消费聚类"中的聚类分组
* 一次处理一个聚类，确保该聚类内所有文件高度内聚后再处理下一个

**策略依据**：如果聚类依赖关系清晰（无环或简单网状），用策略B；如果依赖关系复杂，用策略A。

***

### 2.4 合并执行

**合并判定原则**：只合并高度内聚的文件。判定标准：

* 同功能域（前缀相同或功能紧密相关）
* 合并模拟无环（Tarjan SCC 检测通过）
* 合并后不超过 250KB
* 合并后内聚度提升（跨文件引用减少）
* 无命名冲突或冲突可解决

**合并判定流程**：

1. 从知识图谱"六、消费聚类"中识别同域小文件候选
2. 检查内聚度：候选文件间的符号消费关系是否紧密（跨文件引用占比高）
3. Tarjan SCC 合并模拟：将候选文件合并为一个节点，跑 SCC 检测
4. 合并后成环 → 放弃合并，改用"归位到主要使用方"
5. 合并后超 250KB → 放弃合并
6. 合并前检查命名冲突（同名私有helper/同名公开符号/同名类型定义/logger命名）
7. 冲突处理：私有helper重命名其一；公开符号重命名次要方；logger统一；同名类型定义不合并
8. **利弊评估**：只有利大于弊才能执行

**合并执行步骤**：

1. 备份源文件和目标文件到 <会话工作空间>/Temp/_backups/
2. 检查目标文件顶部是否有 `from __future__ import annotations`
3. 追加内容到目标文件末尾（最可靠，无行号偏移风险）
4. 移除合并内容中的 `from __future__ import annotations`
5. 合并/去重 `__all__` 定义（两个列表拼接后去重）
6. 更新所有消费者的 import（指向目标文件）
7. 更新 lazy\_imports 映射（指向目标文件）
8. 验证语法：`compile(src, name, 'exec')`
9. 删除源文件
10. 全库 grep 已删除模块名，确认无残留引用
11. 清理 __pycache__

***

### 2.5 超大文件治理（GOV-01：禁止拆分）

**治理判定原则**：超 250KB 或类聚复杂的文件按非拆分治理收敛复杂度，禁止用拆分文件/模块降分。判定标准：

* 文件大小超过 250KB，或类聚复杂度显著高于同域均值
* 复杂度来源可定位（重复实现、超长函数、深嵌套、耦合扇出）
* 治理后公开面与文件边界保持既有形态（不新增模块、不制造门面桩）

**治理判定流程**：

1. 从文档"一、全量文件清单"中识别超 250KB 的文件
2. 用 AST 分析定位复杂度来源（重复实现簇/超长函数/深嵌套/扇出）
3. 治理收益评估：下沉函数级或常量级能否消除重复与热点
4. 设计治理动作：消除重复、提取模块内私有实现、收敛依赖、常量 SSOT 化
5. **利弊评估**：只有利大于弊才能执行

**治理执行步骤**：

1. 备份原文件到 <会话工作空间>/Temp/_backups/
2. 按复杂度来源逐项治理（消除重复实现 → 提取模块内私有实现 → 收敛依赖）
3. 公开面保持既有形态：__all__ 项数不膨胀、不新增模块
4. 全量语法编译验证（`compile(src, name, 'exec')`）
5. 定向回归验证行为不变（导入面 + 受影响套件）
6. 记录治理前后复杂度与行数变化

***

### 2.6 迁入/迁出执行

**迁入判定原则**：跨文件消费的函数执行迁移。判定标准：

* 函数符号被当前文件独占消费或少量共享消费（≤4个消费者）
* 迁入后减少跨文件引用
* 迁入后目标文件不超过 250KB
* 依赖链可管理（共享工具改为函数级导入）

**迁入判定**（依据文档"四、迁入候选清单"）：

1. 独占消费（仅被当前文件 import）→ 评估后执行
2. 共享消费（2-4 个消费者，上下文贴合）→ 评估后执行
3. 底座消费（5+ 模块共享）→ 不执行
4. 枢纽消费（注册器/调度器）→ 不执行
5. 类/变量符号：评估迁入收益，通常保留（类通常有多个方法，迁入破坏内聚性）
6. 函数符号：优先迁入（跨文件消费的函数是迁移的主要目标）

**迁入执行步骤**：

1. 全读源文件（跨批只读），确认符号上下文及依赖关系
2. 追踪候选符号的**内部调用链**，识别其依赖的共享工具函数
3. 备份当前文件+源文件到 <会话工作空间>/Temp/_backups/
4. **利弊评估**：只有利大于弊才能执行
5. 将符号定义从源文件复制到当前文件（含完整依赖 import）
6. 若依赖共享工具（5+ 模块消费），改为函数级导入
7. 更新所有消费者 import：直接指向迁入后的当前文件（S01：默认不加兼容桩）；例外：外部消费者或 10+ 内部消费者时在源文件加桩并标注 `# TEMPORARY COMPAT STUB`
8. 更新源文件 __all__：符号已迁出且未加桩时从 __all__ 移除声明；加桩场景保留声明
9. 更新 lazy\_imports 映射：若符号在其中，指向当前文件
10. 验证：import 当前文件不报错；未加桩时全库 grep 确认无残留旧路径引用（加桩时验证源文件桩通路不报错）
11. 记录：当前文件减少 N 个跨文件依赖

**迁出**：当前文件内代码被其他文件集中消费时，迁出到目标文件。流程同迁入（反向操作）。

***

### 2.7 缺陷修复（依据文档"五、缺陷修复清单"）

**修复执行闭环（七步）**：

1. 理解语义：阅读缺陷上下文，理解该符号的业务含义
2. 备份：备份到 <会话工作空间>/Temp/_backups/
3. **利弊评估**：修复是否引入新的跨文件引用？若引入，评估是否可接受
4. 一次一缺陷：每次只修复一个缺陷，不批量
5. 验证：触发实际调用路径，防 @dataclass 缺失/模块级变量提取丢失
6. 留痕：在文档备注列记录修复内容和影响
7. 回滚准备：修复失败即时回滚

**内聚护栏**：修复优先采用本文件内补逻辑/补 import 的本地化方式；确需新增跨文件 import 时，评估该 import 是否可被迁移/收拢纳入内聚范围。

***

### 2.8 死代码清理（依据文档"六、死代码清理清单"）

**清理优先级**：

* HIGH（双引擎一致零引用）→ 评估后清理
* MEDIUM（单引擎检出）→ 复核后评估

**清理执行步骤**：

1. 备份文件到 <会话工作空间>/Temp/_backups/
2. **利弊评估**：确认清理不影响任何消费通路
3. AST 精确定位，从后往前删（避免行号偏移）
4. 验证语法：`compile(src, name, 'exec')`
5. 验证 import 通路
6. 全量 pytest 回归
7. 记录清理结果

***

### 2.9 循环依赖消除

**消除优先级**（按核心记忆循环导入处理规则）：

1. ① 重构代码结构 → 合并形成环，分析成环根因，通过代码结构重构彻底消除
2. ② TYPE\_CHECKING + 字符串注解
3. ③ 提取共享依赖到独立模块后模块级导入
4. ④ 函数级懒加载兜底

**从知识图谱中识别循环类型**：

* 简单双向环（A↔B）：③ 提取共享定义到 L0 底座
* 自注册环（A→B→A，B注册回调到A）：① 重构代码结构，注册回调反转
* 多节点聚合环（A→B→C→A）：① 重构代码结构，找"最弱小"边切断
* 深层注入环（A→...→B→A）：③ 提取共享到 L0 底座

**利弊评估**：只有利大于弊才能执行。消除循环的收益（消除隐患、简化依赖图）通常大于代价（增加底座模块）。但若消除方案引入大量新跨文件引用，需重新评估。

***

## 阶段E：强制验证清单（每项操作后执行）

1. **逐模块 import**（0 失败）
2. **模块级 SCC 复查**（环数不新增）
3. **残留引用 grep**（被删/被迁移文件名不再被 import）
4. **更新 lazy\_imports + \_\_init\_\_ re-export 检查**
5. **清理 \_\_pycache\_\_**
6. **全量 pytest 回归**
7. **功能实例化验证**——必须触发实际调用路径，防 @dataclass 缺失/模块级变量提取丢失/合并文件调全库不存在的方法
8. **跨文件消费净变化核验**：每文件重算三项基线，与迁移前对比，汇总"本批净减少 N 处跨文件引用/净提升 M 个符号同文件化"写入备注；未减少且无收拢动作时须备注原因
9. **文件大小复核**：所有文件不超过 250KB，超限的标记为待治理

***

## 安全与协作约束

1. 每次修改前备份到 <会话工作空间>/Temp/_backups/，失败立即回滚
2. 回滚触发：回归失败或实例化异常即回滚，回滚后重过阶段E
3. **一次 bash 调用仅执行一项独立任务**，禁止合并或并行（P0 强制规则）
4. 迁移前检查命名冲突与 re-export hub 结构，冲突时重命名或放弃
5. 删除/覆盖前向用户说明
6. 每完成一个操作更新文档"八、执行进度"状态
7. 全部操作完成后做一次整体复核并汇总报告

***

## 收尾

1. 统一流程：Phase 0（创建空白文档+KG）→ Phase 1（逐文件全读+即时登记）→ Phase 2（基于完整数据执行，每步利弊评估先行）→ 阶段E验证 → 汇报结果
2. 续接场景：桌面已有 `{skill_name}_全量分析_*.md` 时，以该文档为唯一事实来源，先读取文档+KG恢复完整认知，然后从文档标记的"最后已读文件"之后继续 Phase 1，或直接进入 Phase 2 执行
3. 报告包含：迁出/迁入/合并明细、跨文件引用净变化、缺陷修复清单、死代码清理清单、阶段E验证结果、文件大小分布变化、剩余操作概览

***

## 附录：文档与知识图谱的关系

| 维度 | 进度追踪文档 | 知识图谱 |
|------|-------------|---------|
| 核心用途 | 逐文件分析记录 + 执行计划 | 依赖拓扑查询 + 决策依据 |
| 数据来源 | Phase 1 逐文件分析 | Phase 1 逐文件分析 |
| 主要查询 | "这个文件有哪些缺陷？" | "这个符号被谁消费？" |
| 决策用途 | 修复优先级、清理清单、利弊评估依据 | 合并/治理决策、迁入候选、消费性质判定 |
| 更新频率 | 每读一个文件更新一次 | 每读一个文件更新一次 |
| Phase 2 角色 | 执行清单，追踪进度，记录利弊评估 | 查询依赖，检查环，辅助利弊评估 |

## 附录：利弊评估速查表

| 操作 | 利（正面） | 弊（负面） |
|------|-----------|-----------|
| 合并 | 减少跨文件引用、同文件消费更充分、消除跨文件跳转 | 增大目标文件（但文件数量变化不计入利弊） |
| 非拆分治理 | 降低类聚复杂度、职责更单一 | 单文件仍较大（文件数量变化不计入） |
| 迁入 | 减少跨文件引用、符号同文件化 | 增大目标文件、可能引入循环依赖 |
| 迁出 | 减少目标文件大小、职责聚焦 | 增加跨文件引用 |
| 循环消除 | 消除隐患、简化依赖图、打破循环 | 可能增加底座模块（但文件数量变化不计入） |
| 缺陷修复 | 消除BUG、提升代码质量 | 极小概率引入新问题 |
| 死代码清理 | 减少冗余、降低维护成本 | 极小概率误删（但交叉验证可规避） |

## 附录：知识图谱快照

> 本附录是知识图谱文件的同步快照，用于快速验证两个文档的一致性。
> **更新规则**：每次 Phase 1 更新知识图谱后，必须同步刷新本附录的计数和枢纽节点列表。

### A. 节点统计对比

| 维度 | 进度文档 | 知识图谱 | 一致性 |
|------|---------|---------|--------|
| 总文件数 | {total_file_count} | {total_file_count} | ✓ |
| 已完成分析 | {analyzed_count} | {analyzed_count} | ✓ |
| 待分析 | {pending_count} | {pending_count} | ✓ |
| 超250KB文件 | {oversized_count} | {oversized_count} | ✓ |

### B. 枢纽节点快照（入度≥5 或 出度≥5）

| 文件名 | 入度 | 出度 | 角色说明 |
|--------|------|------|---------|
| {hub_nodes} | | | |

### C. 同步验证检查点

**每次更新后必须检查以下三项，任一项不通过即视为违规：**

1. **文件数一致**：进度文档"一、全量文件清单"中已完成数 + 待分析数 = 知识图谱"一、节点列表"的总行数
2. **枢纽节点一致**：两文档"枢纽节点"中文件名和出入度完全一致
3. **更新时间一致**：两文档的更新时间戳（文档标题日期）相同

> 当前检查时间：{date}，状态：✓ 通过
"""
TRACKER_FILENAME = "_phase1_tracker.json"
BATCH_WINDOW_SECONDS = 2.0
_L0_MIN_FAN_IN = 5
def _module_key_index(skill_dir: str) -> dict[str, str]:
    index: dict[str, str] = {}
    for entry in scan_file_manifest(os.path.abspath(skill_dir)):
        filename = str(entry.get("filename") or "").replace("\\", "/")
        if not filename.lower().endswith(".py"):
            continue
        index[filename[:-3]] = filename
    return index
def _top_level_fan_in(
    graph: dict[str, list[str]], module_index: dict[str, str],
) -> Counter[str]:
    fan_in: Counter[str] = Counter()
    for importer, dependencies in graph.items():
        if importer not in module_index:
            continue
        fan_in.update({
            dependency for dependency in dependencies
            if dependency in module_index and dependency != importer
        })
    return fan_in
def _discover_l0_base_files(skill_dir: str) -> tuple[str, ...]:
    root = os.path.abspath(skill_dir)
    module_index = _module_key_index(root)
    graph = build_import_graph(Path(root))
    fan_in = _top_level_fan_in(graph, module_index)
    return tuple(sorted(
        module_index[module] for module, count in fan_in.items()
        if count >= _L0_MIN_FAN_IN))
class Phase1Tracker:
    def __init__(self, skill_dir: str):
        root_text = normalize_out_path(skill_dir)
        if (root_text is None
                or not os.path.isdir(os.path.realpath(root_text))):
            raise ValueError(
                f"[Phase1Tracker] 技能目录为空、非法或不存在: {skill_dir!r}")
        self.skill_dir = os.path.abspath(root_text)
        self.tracker_path = os.path.join(get_temp_base(self.skill_dir), TRACKER_FILENAME)
        self._l0_base_files: tuple[str, ...] | None = None
        self._state = self._load_or_init()
    @property
    def total_files(self) -> int:
        return len(self._state["all_files"])
    @property
    def analyzed_count(self) -> int:
        return self._state["analyzed_count"]
    @property
    def analyzed_files(self) -> tuple[str, ...]:
        return tuple(self._state["analyzed_files"])
    def register_file(self, filename: str, ai_analysis: dict | None = None) -> dict:
        filename = self._normalize_registration_path(filename)
        with locked_artifact(self.tracker_path) as locked:
            if not locked:
                raise RuntimeError(
                    "[Phase1Tracker] 追踪状态写锁不可用，拒绝无锁读改写: "
                    f"{self.tracker_path}")
            self._state = self._load_or_init()
            self._ensure_file_registered(filename)
            identity = _sync_file_identity(filename)
            filename = next(
                (registered for registered in self._state["all_files"]
                 if _sync_file_identity(registered) == identity), filename)
            self._state["analyzed_files"][filename] = {
                "timestamp": datetime.now().isoformat(),
                "status": "completed",
                "analysis": ai_analysis or {},
                "has_ai_understanding": _has_functional_understanding(ai_analysis),
            }
            self._state["analyzed_count"] = len(self._state["analyzed_files"])
            self._save()
            return self._state
    def check_sequential(self) -> dict:
        analyzed = list(self._state["analyzed_files"].keys())
        batch_size = self._detect_batch()
        try:
            violations = self._sequential_violations(analyzed)
        except (OSError, ValueError, RecursionError) as exc:
            log_swallowed(
                __name__, exc, context="check_sequential:l0_discovery")
            violations = [{
                "type": "base_discovery_failed",
                "detail": f"L0 底座依赖图不可用，无法验证读取顺序: {exc}",
                "severity": "P1",
            }]
        return {
            "pass": not violations,
            "violations": violations,
            "warnings": self._sequential_warnings(batch_size),
            "batch_size": batch_size,
            "analyzed_count": len(analyzed),
        }
    def _sequential_warnings(self, batch_size: int) -> list[dict]:
        if batch_size <= 1:
            return []
        return [{
            "type": "batch_read_suspected",
            "detail": (f"{batch_size} 个文件在 {BATCH_WINDOW_SECONDS:g} 秒窗口内登记；"
                       "时间接近不能证明同批读取，需结合操作记录复核"),
            "severity": "P3",
        }]
    def _sequential_violations(self, analyzed: list[str]) -> list[dict]:
        violations = []
        violations.extend(self._unread_base_violations(set(analyzed)))
        violations.extend(self._late_base_violations(analyzed))
        return violations
    def _l0_bases(self) -> tuple[str, ...]:
        if self._l0_base_files is None:
            self._l0_base_files = _discover_l0_base_files(self.skill_dir)
        return self._l0_base_files
    def _unread_base_violations(self, analyzed: set[str]) -> list[dict]:
        analyzed_ids = {_sync_file_identity(filename) for filename in analyzed}
        bases = self._l0_bases()
        base_ids = {_sync_file_identity(base) for base in bases}
        if not analyzed_ids - base_ids:
            return []
        return [
            {
                "type": "skip_base",
                "detail": f"L0 底座文件 {base} 尚未读取",
                "severity": "P1",
            }
            for base in bases
            if _sync_file_identity(base) not in analyzed_ids
            and os.path.isfile(os.path.join(self.skill_dir, base))
        ]
    def _late_base_violations(self, analyzed: list[str]) -> list[dict]:
        base_by_id = {
            _sync_file_identity(base): base for base in self._l0_bases()
        }
        violations = []
        for index, filename in enumerate(analyzed):
            identity = _sync_file_identity(filename)
            if identity not in base_by_id:
                continue
            earlier_non_base = next(
                (candidate for candidate in analyzed[:index]
                 if _sync_file_identity(candidate) not in base_by_id), None)
            if earlier_non_base is not None:
                violations.append({
                    "type": "skip_base",
                    "detail": (f"L0 底座文件 {base_by_id[identity]} 在外围文件 "
                               f"{earlier_non_base} 之后读取"),
                    "severity": "P1",
                })
        return violations
    def check_completeness(self) -> dict:
        all_files = self._state["all_files"]
        analyzed_files = self._state["analyzed_files"]
        analyzed_ids = _sync_file_set(analyzed_files)
        remaining = sorted(
            (filename for filename in all_files
             if _sync_file_identity(filename) not in analyzed_ids),
            key=_sync_file_identity,
        )
        no_ai_understanding = _dedup_sync_files(
            filename for filename, info in analyzed_files.items()
            if not info.get("has_ai_understanding")
        )
        return {
            "pass": (bool(_sync_file_set(all_files))
                     and not remaining and not no_ai_understanding),
            "total": len(_sync_file_set(all_files)),
            "analyzed": len(analyzed_ids),
            "remaining": remaining,
            "no_ai_understanding": no_ai_understanding,
        }
    def check_phase1_readiness(self) -> dict:
        with locked_artifact(self.tracker_path) as locked:
            if not locked:
                raise RuntimeError(
                    "[Phase1Tracker] 追踪状态写锁不可用，拒绝无锁读改写: "
                    f"{self.tracker_path}")
            self._state = self._load_or_init()
            self._reconcile_file_inventory(self._discover_py_files())
            self._prune_stale_registrations()
            if self._state["analyzed_files"] or os.path.isfile(self.tracker_path):
                self._save()
            return {
                "pass": True,
                "blocking_reasons": [],
                "analyzed_count": self._state["analyzed_count"],
                "total_files": len(self._state["all_files"]),
            }
    def _reconcile_file_inventory(self, discovered: list[str]) -> None:
        discovered_files = _dedup_sync_files(
            os.path.normpath(filename) for filename in discovered)
        discovered_ids = _sync_file_set(discovered_files)
        retained = []
        for filename in self._state["all_files"]:
            normalized = os.path.normpath(filename)
            if (_sync_file_identity(normalized) not in discovered_ids
                    and self._is_in_root(normalized)
                    and os.path.isfile(os.path.join(self.skill_dir, normalized))):
                retained.append(normalized)
        self._state["all_files"] = sorted(
            _dedup_sync_files([*discovered_files, *retained]),
            key=_sync_file_identity,
        )
    def _prune_stale_registrations(self) -> None:
        all_ids = _sync_file_set(self._state["all_files"])
        analyzed_files = {}
        for filename, info in self._state["analyzed_files"].items():
            normalized = os.path.normpath(filename)
            if _sync_file_identity(normalized) in all_ids:
                analyzed_files[normalized] = info
        self._state["analyzed_files"] = _normalize_analyzed_files(
            analyzed_files)
        self._state["analyzed_count"] = len(self._state["analyzed_files"])
    def cleanup(self) -> bool:
        with locked_artifact(self.tracker_path) as locked:
            if not locked:
                _log.warning(
                    "[Phase1Tracker] 追踪状态写锁不可用，保留追踪文件: %s",
                    self.tracker_path)
                return False
            if not os.path.isfile(self.tracker_path):
                return False
            self._state = self._load_or_init()
            self._reconcile_file_inventory(self._discover_py_files())
            self._prune_stale_registrations()
            if not self.check_completeness()["pass"]:
                self._save()
                _log.info(
                    "[Phase1Tracker] 清理前发现未完成或新增进度，保留追踪文件: %s",
                    self.tracker_path)
                return False
            if safe_delete(self.tracker_path):
                _log.info(
                    "[Phase1Tracker] 追踪文件已消费完毕并清理: %s",
                    self.tracker_path)
                return True
            _log.warning("[Phase1Tracker] 清理追踪文件失败: %s", self.tracker_path)
            return False
    def _normalize_registration_path(self, filename: str) -> str:
        # Tracker 的 all_files/analyzed_files 以「相对技能根的 normpath 路径」为键
        # （_sync_file_identity 只做 normcase(normpath())，不解析绝对路径），
        # 因此技能目录内的绝对路径必须先归一为相对路径；根外/跨盘符路径保持拒绝。
        if not os.path.isabs(filename):
            return os.path.normpath(filename)
        root = os.path.realpath(self.skill_dir)
        candidate = os.path.realpath(filename)
        try:
            relative = os.path.relpath(candidate, root)
        except ValueError as exc:
            raise FileNotFoundError(
                f"[Phase1Tracker] 打卡文件不在技能目录内: {filename!r} "
                f"(skill_dir={self.skill_dir})"
            ) from exc
        return os.path.normpath(relative)
    def _ensure_file_registered(self, filename: str) -> None:
        if not filename.lower().endswith(".py"):
            raise FileNotFoundError(
                f"[Phase1Tracker] 打卡文件不是 Python 源文件: {filename!r}")
        if not (self._is_in_root(filename) and os.path.isfile(
                os.path.join(self.skill_dir, filename))):
            raise FileNotFoundError(
                f"[Phase1Tracker] 打卡文件不在技能目录内: {filename!r} "
                f"(skill_dir={self.skill_dir})"
            )
        if _sync_file_identity(filename) not in _sync_file_set(
                self._state["all_files"]):
            self._state["all_files"].append(filename)
    def _is_in_root(self, filename: str) -> bool:
        if os.path.isabs(filename):
            return False
        root = os.path.realpath(self.skill_dir)
        candidate = os.path.realpath(os.path.join(self.skill_dir, filename))
        try:
            return (os.path.normcase(os.path.commonpath([candidate, root]))
                    == os.path.normcase(root))
        except ValueError:
            _log.debug(
                "[Phase1Tracker] 打卡路径与技能根跨盘符无法公共化，按根外拒绝: "
                "%r (skill_dir=%s)", filename, self.skill_dir
            )
            return False
    def _load_or_init(self) -> dict:
        state = self._read_snapshot()
        if state is None:
            return self._init_state()
        state["all_files"] = sorted(
            _dedup_sync_files(
                os.path.normpath(filename) for filename in state["all_files"]),
            key=_sync_file_identity,
        )
        state["analyzed_files"] = _normalize_analyzed_files(
            state["analyzed_files"])
        state["analyzed_count"] = len(state["analyzed_files"])
        return state
    def _read_snapshot(self) -> dict | None:
        if not os.path.isfile(self.tracker_path):
            return None
        try:
            with open(self.tracker_path, encoding="utf-8-sig") as f:
                state = json.load(f)
        except OSError:
            _log.warning(
                "[Phase1Tracker] 追踪文件读取失败，保留原状态并中止",
                exc_info=True)
            raise
        except (json.JSONDecodeError, UnicodeDecodeError, RecursionError) as exc:
            message = "[Phase1Tracker] 追踪文件损坏，保留原状态并中止"
            _log.warning(message)
            raise ValueError(message) from exc
        if not _is_valid_state(state):
            message = "[Phase1Tracker] 追踪文件结构异常，保留原状态并中止"
            _log.warning(message)
            raise ValueError(message)
        snapshot_dir = state.get("skill_dir")
        if not isinstance(snapshot_dir, str) or not snapshot_dir.strip():
            message = ("[Phase1Tracker] 追踪文件缺少有效技能目录归属，"
                       "保留原状态并中止")
            _log.warning(message)
            raise ValueError(message)
        if (_sync_directory_identity(snapshot_dir)
                != _sync_directory_identity(self.skill_dir)):
            message = (f"[Phase1Tracker] 追踪文件归属其他技能目录({snapshot_dir})，"
                       "保留原状态并中止")
            _log.warning(message)
            raise ValueError(message)
        return state
    def _init_state(self) -> dict:
        return {
            "created_at": datetime.now().isoformat(),
            "skill_dir": self.skill_dir,
            "all_files": self._discover_py_files(),
            "analyzed_files": {},
            "analyzed_count": 0,
        }
    def _discover_py_files(self) -> list[str]:
        return sorted(
            os.path.normpath(entry["filename"])
            for entry in scan_file_manifest(self.skill_dir)
        )
    def _naive_timestamps(self) -> list[datetime]:
        timestamps: list[datetime] = []
        for info in self._state["analyzed_files"].values():
            try:
                ts = datetime.fromisoformat(info["timestamp"])
            except (KeyError, TypeError, ValueError) as e:
                _log.debug("格式解析失败（跳过条目）: %s", e)
                continue
            timestamps.append(ts.replace(tzinfo=None))
        timestamps.sort()
        return timestamps
    def _detect_batch(self) -> int:
        timestamps = self._naive_timestamps()
        if not timestamps:
            return 0
        max_batch = 1
        left = 0
        for right in range(1, len(timestamps)):
            while (timestamps[right] - timestamps[left]).total_seconds() > BATCH_WINDOW_SECONDS:
                left += 1
            max_batch = max(max_batch, right - left + 1)
        return max_batch
    def _save(self) -> None:
        os.makedirs(os.path.dirname(self.tracker_path), exist_ok=True)
        write_json_artifact(self.tracker_path, self._state, indent=2)
def _has_functional_understanding(ai_analysis: object) -> bool:
    if not isinstance(ai_analysis, dict):
        return False
    value = ai_analysis.get("功能理解")
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (bool, int, float)) or value is None:
        return False
    if isinstance(value, (list, tuple, dict, set, frozenset)):
        return bool(value)
    return True
def _is_valid_state(state: object) -> bool:
    if not isinstance(state, dict):
        return False
    all_files = state.get("all_files")
    analyzed = state.get("analyzed_files")
    return (isinstance(all_files, list)
            and all(isinstance(f, str) for f in all_files)
            and isinstance(analyzed, dict)
            and all(isinstance(filename, str) for filename in analyzed)
            and all(isinstance(info, dict) for info in analyzed.values()))
def _blocked_result(message: str, details: dict, action: str) -> dict:
    return {
        "status": "blocked",
        "message": message,
        "details": details,
        "action_required": action,
    }
def enforce_phase1_sequential(
    skill_dir: str,
    progress_doc_path: str | None = None,
    kg_doc_path: str | None = None,
) -> dict:
    if bool(progress_doc_path) != bool(kg_doc_path):
        return _blocked_result(
            "进度文档与知识图谱路径必须成对提供",
            {
                "progress_doc_provided": bool(progress_doc_path),
                "kg_doc_provided": bool(kg_doc_path),
            },
            "同时提供进度文档和知识图谱路径，或两者均省略")
    root_text = normalize_out_path(skill_dir)
    if root_text is None or not os.path.isdir(root_text):
        return _blocked_result(
            "skill_dir 非法或不是目录",
            {"skill_dir": repr(skill_dir)},
            "提供有效的技能目录后重试")
    try:
        tracker = Phase1Tracker(root_text)
        tracker.check_phase1_readiness()
    except (OSError, ValueError, RuntimeError, TypeError,
            RecursionError) as exc:
        log_swallowed(__name__, exc,
                      context="enforce_phase1_sequential:tracker")
        return _blocked_result(
            "Phase1 追踪状态不可用（技能目录或临时根不可读取/写入）",
            {"skill_dir": root_text},
            "检查技能目录与临时根可写性后重试")
    sequential = tracker.check_sequential()
    if not sequential["pass"]:
        return _blocked_result(
            "检测到违规行为（批量读取/跳过底座）", sequential,
            "立即停止当前操作，按 P0 违规处理")
    if progress_doc_path and kg_doc_path:
        sync = check_doc_kg_sync(
            skill_dir, progress_doc_path, kg_doc_path, tracker=tracker)
        if not sync["pass"]:
            return _blocked_result(
                SYNC_CHECK_HEADER.strip(), sync,
                "立即更新知识图谱或进度文档，保持两者一致")
    completeness = tracker.check_completeness()
    if completeness["pass"]:
        cleaned = tracker.cleanup()
        latest_completeness = (
            completeness if cleaned else tracker.check_completeness())
        if not latest_completeness["pass"]:
            return {
                "status": "in_progress",
                "message": ("Phase 1 进行中: "
                            f"{latest_completeness['analyzed']}/"
                            f"{latest_completeness['total']}"),
                "details": latest_completeness,
            }
        return {
            "status": "phase1_complete",
            "message": "Phase 1 所有文件已逐文件分析完成",
            "details": latest_completeness,
            "tracker_cleaned": cleaned,
        }
    return {
        "status": "in_progress",
        "message": f"Phase 1 进行中: {completeness['analyzed']}/{completeness['total']}",
        "details": completeness,
    }
def check_doc_kg_sync(
    skill_dir: str,
    progress_doc_path: str,
    kg_doc_path: str,
    tracker: Phase1Tracker | None = None,
) -> dict:
    violations = []
    checks = {}
    root_text = normalize_out_path(skill_dir) or ""
    progress_text = normalize_out_path(progress_doc_path) or ""
    kg_text = normalize_out_path(kg_doc_path) or ""
    progress_exists = os.path.isfile(progress_text)
    kg_exists = os.path.isfile(kg_text)
    checks["progress_exists"] = progress_exists
    checks["kg_exists"] = kg_exists
    if not progress_exists or not kg_exists:
        return _sync_result(checks, ["进度文档或知识图谱文件不存在"])
    facts = _sync_document_facts(progress_text, kg_text)
    violations.extend(facts.violations)
    checks["doc_analyzed_count"] = facts.analyzed_count
    checks["kg_node_count"] = facts.kg_node_count
    tracker_checks, tracker_error = _check_tracker_consistency(
        tracker, root_text, facts.analyzed_count, facts.progress_read_ok,
        facts.progress_files)
    checks.update(tracker_checks)
    if tracker_error is not None:
        violations.append(tracker_error)
    return _sync_result(checks, violations)
def _sync_result(checks: dict, violations: list[str]) -> dict:
    return {
        "pass": not violations,
        "checks": checks,
        "violations": violations,
    }
@dataclass(frozen=True)
class _DocumentSyncFacts:
    analyzed_count: int
    kg_node_count: int
    progress_read_ok: bool
    progress_files: tuple[str, ...]
    violations: tuple[str, ...]
def _sync_document_facts(
    progress_doc_path: str, kg_doc_path: str,
) -> _DocumentSyncFacts:
    progress_files, progress_error = _read_progress_completed(progress_doc_path)
    kg_files, kg_error = _read_kg_nodes(kg_doc_path)
    violations = [error for error in (progress_error, kg_error)
                  if error is not None]
    progress_read_ok = progress_error is None
    kg_read_ok = kg_error is None
    analyzed_count = len(progress_files)
    kg_node_count = len(kg_files)
    if progress_read_ok and kg_read_ok:
        if analyzed_count != kg_node_count:
            violations.append(
                f"文档已完成数({analyzed_count}) ≠ 知识图谱节点数({kg_node_count})"
            )
        if _sync_file_set(progress_files) != _sync_file_set(kg_files):
            violations.append(_sync_identity_violation(
                "进度文档", progress_files, "知识图谱", kg_files))
    return _DocumentSyncFacts(
        analyzed_count=analyzed_count,
        kg_node_count=kg_node_count,
        progress_read_ok=progress_read_ok,
        progress_files=tuple(progress_files),
        violations=tuple(violations),
    )
def _sync_file_identity(filename: str) -> str:
    return os.path.normcase(os.path.normpath(filename))
def _sync_directory_identity(path: str) -> str:
    return _sync_file_identity(os.path.realpath(os.path.abspath(path)))
def _dedup_sync_files(files: Iterable[str]) -> list[str]:
    unique: list[str] = []
    seen: set[str] = set()
    for filename in files:
        identity = _sync_file_identity(filename)
        if identity not in seen:
            seen.add(identity)
            unique.append(filename)
    return unique
def _normalize_analyzed_files(
    entries: dict[str, dict],
) -> dict[str, dict]:
    normalized: dict[str, dict] = {}
    keys_by_identity: dict[str, str] = {}
    for filename, info in entries.items():
        filename = os.path.normpath(filename)
        identity = _sync_file_identity(filename)
        key = keys_by_identity.setdefault(identity, filename)
        normalized[key] = info
    return normalized
def _sync_file_set(files: Iterable[str]) -> set[str]:
    return {_sync_file_identity(filename) for filename in files if filename}
def _sync_identity_violation(
    left_label: str, left_files: Iterable[str],
    right_label: str, right_files: Iterable[str],
) -> str:
    left_set = _sync_file_set(left_files)
    right_set = _sync_file_set(right_files)
    details = []
    left_only = sorted(left_set - right_set)
    right_only = sorted(right_set - left_set)
    if left_only:
        details.append(f"仅{left_label}: {', '.join(left_only)}")
    if right_only:
        details.append(f"仅{right_label}: {', '.join(right_only)}")
    return (f"{left_label}与{right_label}文件集合不一致"
            f"（{'；'.join(details)}）")
_COMPLETION_MARKERS = ("[x]", "✅", "✔", "✓")
_COMPLETION_WORD_RE = re.compile(r"\b(?:completed|complete|done)\b", re.IGNORECASE)
_COMPLETION_NEGATION_RE = re.compile(r"\b(?:not|pending)\b", re.IGNORECASE)
_COMPLETION_NEGATION_MARKERS = ("未完成", "待完成", "尚未完成", "没有完成")
_KG_SECTION_TOKENS = ("节点", "node list", "node table", "nodes")
_KG_NON_NODE_SECTION_TOKENS = (
    "节点定义", "边定义", "枢纽节点", "node definition",
    "edge definition", "hub node", "hub nodes",
)
_PY_FILE_CELL_RE = re.compile(
    r"^[^,;，；、|*?<>\"']+\.(?:py|pyi|pyw)$", re.IGNORECASE)
_BULLET_FILE_ROW_RE = re.compile(
    r"^(?P<filename>.+\.(?:py|pyi|pyw))[`*]*(?:\s+(?P<status>.*))?$",
    re.IGNORECASE)
_BULLET_STATUS_PREFIX_RE = re.compile(
    r"^(?P<status>\[[ x]\]|✅|✔️?|✓)\s+(?P<body>.+)$",
    re.IGNORECASE)
def _clean_sync_cell(value: str) -> str:
    return value.strip().strip("`*").strip()
def _row_cells(line: str) -> list[str]:
    stripped = line.strip()
    if not stripped:
        return []
    if stripped.startswith(("- ", "* ", "+ ")):
        body = stripped[2:].strip()
        prefix_status = ""
        prefix = _BULLET_STATUS_PREFIX_RE.match(body)
        if prefix is not None:
            prefix_status = prefix.group("status")
            body = prefix.group("body").strip()
        match = _BULLET_FILE_ROW_RE.match(body)
        if match is not None:
            cells = [_clean_sync_cell(match.group("filename"))]
            cells.extend(
                _clean_sync_cell(status)
                for status in (prefix_status, match.group("status"))
                if status)
            return cells
        cells = [_clean_sync_cell(token) for token in body.split()]
        if prefix_status:
            cells.append(_clean_sync_cell(prefix_status))
        return cells
    if "|" not in stripped:
        return []
    return [_clean_sync_cell(cell)
            for cell in stripped.strip("|").split("|")]
def _is_py_file_cell(cell: str) -> bool:
    text = _clean_sync_cell(str(cell or ""))
    return bool(text) and _PY_FILE_CELL_RE.match(text) is not None
def _is_completion_cell(cell: str) -> bool:
    normalized = _clean_sync_cell(cell).lower()
    if (any(marker in normalized for marker in _COMPLETION_NEGATION_MARKERS)
            or _COMPLETION_NEGATION_RE.search(normalized) is not None):
        return False
    if any(marker in normalized for marker in _COMPLETION_MARKERS):
        return True
    if "已完成" in normalized or normalized == "完成":
        return True
    return _COMPLETION_WORD_RE.search(normalized) is not None
def _is_completed_row(line: str) -> bool:
    cells = _row_cells(line)
    if not any(_is_py_file_cell(cell) for cell in cells):
        return False
    status_cells = [cell for cell in cells if not _is_py_file_cell(cell)]
    return any(_is_completion_cell(cell) for cell in status_cells)
def _is_kg_section_heading(heading: str) -> bool:
    lowered = heading.lower()
    if any(token in lowered for token in _KG_NON_NODE_SECTION_TOKENS):
        return False
    for token in _KG_SECTION_TOKENS:
        if token.isascii():
            if re.search(
                    rf"(?<![a-z0-9]){re.escape(token)}(?![a-z0-9])", lowered):
                return True
        elif token in lowered:
            return True
    return False
def _iter_sync_document_lines(content: str) -> Iterator[str]:
    for line, in_fence in iter_fence_lines(content.splitlines()):
        if not in_fence:
            yield line
_PROGRESS_INVENTORY_TOKENS = (
    "全量文件清单", "文件清单", "file inventory", "file manifest", "file list",
)
_PROGRESS_HEADING_RE = re.compile(r"^(#{1,6})\s+")
def _iter_progress_file_lines(content: str) -> Iterator[str]:
    lines = list(_iter_sync_document_lines(content))
    inventory_level: int | None = None
    for line in lines:
        heading = _PROGRESS_HEADING_RE.match(line.strip())
        if heading is not None:
            level = len(heading.group(1))
            if inventory_level is not None and level <= inventory_level:
                break
            title = line.strip()[heading.end():].lower()
            if (inventory_level is None
                    and any(token in title
                            for token in _PROGRESS_INVENTORY_TOKENS)):
                inventory_level = level
            continue
        if inventory_level is not None:
            yield line
    if inventory_level is None:
        yield from lines
def _read_progress_completed(
    progress_doc_path: str,
) -> tuple[list[str], str | None]:
    content, error = _read_doc_text(progress_doc_path, "进度文档")
    if error is not None:
        return [], error
    return _dedup_sync_files(
        _markdown_row_file(line)
        for line in _iter_progress_file_lines(content)
        if _is_completed_row(line)
    ), None
def _read_kg_nodes(kg_doc_path: str) -> tuple[list[str], str | None]:
    kg_content, error = _read_doc_text(kg_doc_path, "知识图谱")
    if error is not None:
        return [], error
    return _dedup_sync_files(
        _markdown_row_file(line) for line in _iter_kg_node_lines(kg_content)), None
def _markdown_row_file(line: str) -> str:
    cells = _row_cells(line)
    return next((cell for cell in cells if _is_py_file_cell(cell)),
                cells[0] if cells else "")
def _read_doc_text(path: str, label: str) -> tuple[str | None, str | None]:
    try:
        with open(path, encoding="utf-8-sig") as f:
            return f.read(), None
    except (OSError, UnicodeDecodeError) as e:
        log_swallowed(__name__, e, context=f"_read_doc_text:{type(e).__name__}")
        return None, f"读取{label}失败: {e}"
_KG_HEADING_RE = re.compile(r"^(#{1,6})\s+(.*)$")
def _iter_kg_node_lines(content: str):
    in_node_section = False
    node_level = 0
    for line in _iter_sync_document_lines(content):
        heading = _KG_HEADING_RE.match(line.strip())
        if heading is not None:
            level = len(heading.group(1))
            if in_node_section:
                if level <= node_level:
                    break
                continue
            if level >= 2 and _is_kg_section_heading(heading.group(2)):
                in_node_section = True
                node_level = level
            continue
        if (in_node_section
                and any(_is_py_file_cell(cell) for cell in _row_cells(line))):
            yield line
def _check_tracker_consistency(
    tracker: Phase1Tracker | None,
    skill_dir: str,
    analyzed_count: int,
    progress_read_ok: bool,
    progress_files: Iterable[str],
) -> tuple[dict, str | None]:
    checks: dict = {}
    if tracker is None and not skill_dir:
        return checks, "skill_dir 非法，无法校验 Tracker 状态"
    try:
        if tracker is None:
            tracker = Phase1Tracker(skill_dir)
        checks["tracker_analyzed"] = tracker.analyzed_count
        checks["tracker_total"] = tracker.total_files
        if progress_read_ok and tracker.analyzed_count != analyzed_count:
            return checks, (
                f"Tracker已分析数({tracker.analyzed_count}) ≠ 文档已完成数({analyzed_count})"
            )
        tracker_files = tracker.analyzed_files
        if (progress_read_ok
                and _sync_file_set(tracker_files) != _sync_file_set(progress_files)):
            return checks, _sync_identity_violation(
                "Tracker", tracker_files, "进度文档", progress_files)
        return checks, None
    except (OSError, ValueError, RuntimeError, TypeError) as e:
        log_swallowed(
            __name__, e,
            context=f"_check_tracker_consistency:{type(e).__name__}")
        return checks, f"读取Tracker状态失败: {e}"
SYNC_CHECK_HEADER = """
## ⚠️ 三步联动验证失败

Phase 1 要求每读一个文件后必须同时更新：
  1. ✅ 打卡（Phase1Tracker.register_file）
  2. ✅ 进度文档（已完成的逐文件分析记录）
  3. ✅ 知识图谱（与进度记录对应的节点列表）

当前检测到违规项，请立即修正。
"""
if __name__ == "__main__":
    sys.exit(main())
