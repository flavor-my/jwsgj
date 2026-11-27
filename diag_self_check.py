from __future__ import annotations

import ast
import ctypes
import importlib.util
import logging
import os
import platform
import re
import shutil
import subprocess
import sys
import threading
import time
from collections.abc import Callable, Iterable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from datetime import datetime, timezone
from importlib.metadata import PackageNotFoundError, distribution
from pathlib import Path
from typing import Any

from jwsgj.diag_guard_state import (
    read_json_artifact,
)
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    is_type_checking_guard,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_source_core import read_source_interpreter_encoding
from jwsgj.diag_symbol_surface import (
    DEP_MODULE_MAP,
    MIN_PYTHON,
    TOOLCHAIN_PACKAGES,
    pip_pkg_to_module,
    spec_exists,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_paths import (
    get_temp_base,
    lifecycle_state_dir,
    resolve_workspace_root,
    skill_search_roots,
    subprocess_noartifact_env,
)
from jwsgj.runtime_scope import (
    PACKAGE_VERSION,
    RUNTIME_DIR_NAME,
    SKILL_LOG_DIR_NAME,
    STATE_DIR_NAME,
    TEST_ARTIFACT_DIRS,
    is_backup_snapshot_dir,
    is_pruned_scan_dir,
    is_scan_py_name,
    scan_exclude_dirs,
)
from jwsgj.skill_profile import detect_layout

__all__ = ['REQUIRED_DEPENDENCIES', 'REQUIRED_TOOLS', 'RUNTIME_DEPS', 'DependencyCheckResult', 'DependencyManager', 'DependencySpec', 'HealthStatus', 'HealthVital', 'available_memory_bytes', 'check_dependencies', 'check_missing', 'check_python_deps', 'check_system_tools', 'clean_pkg_name', 'current_process_rss_mb', 'dedup_path_insert', 'dep_pkg_list', 'ensure_available', 'ensure_dependencies', 'ensure_deps', 'ensure_tool', 'get_platform_info', 'get_tool_package', 'guard_package', 'guard_subpackage', 'has_missing', 'install_tool', 'list_shadow_packages', 'maint_health_check', 'module_available', 'normalize_check_items', 'quick_self_check', 'resolve_tool_path', 'run_health', 'run_tool_process', 'verify_tool']
logger = logging.getLogger(__name__)
_PACKAGE_DIR = Path(__file__).resolve().parent
_PACKAGE_NAME = __package__ or _PACKAGE_DIR.name
def _swallow(function_name: str, exc: BaseException) -> None:
    log_swallowed(__name__, exc,
                  context=f"{function_name}:{type(exc).__name__}")
def _module_names(value: Any, package_name: str | None = None, *,
                  deduplicate: bool = True) -> tuple[str, ...]:
    source = _FACADE_MODULES if value is None else value
    if isinstance(source, str):
        raw: tuple[Any, ...] = (source,)
    elif isinstance(source, (set, frozenset)):
        raw = tuple(sorted(source, key=str))
    elif isinstance(source, (list, tuple)):
        raw = tuple(source)
    else:
        return ()
    names: list[str] = []
    for item in raw:
        name = _facade_module_name(item, package_name)
        if name and (not deduplicate or name not in names):
            names.append(name)
    return tuple(names)
def _facade_module_name(value: Any, package_name: str | None) -> str:
    if not isinstance(value, str):
        return ""
    name = value.strip().lstrip(".")
    if not name:
        return ""
    if package_name:
        if name == package_name:
            return ""
        name = name.removeprefix(f"{package_name}.")
    return name
try:
    import psutil as _psutil
except ImportError as _imp_err:
    logger.debug("[diag_self_check] psutil 导入失败，体征采集降级: %s", _imp_err)
    _psutil = None
_DEFAULT_INSTALL_TIMEOUT = 300
_DEFAULT_PIP_TIMEOUT = 600
RUNTIME_DEPS: list[str] = list(DEP_MODULE_MAP.keys())
REQUIRED_DEPENDENCIES: dict[str, str] = {v: k for k, v in DEP_MODULE_MAP.items()}
REQUIRED_TOOLS: dict[str, str] = {
    "pytest": "pip install pytest",
    "ruff": "pip install ruff",
    "git": "系统级工具：https://git-scm.com/downloads（回归 CV 必需）",
}
_AUTO_INSTALL_HINT = f"；运行 python -m {_PACKAGE_NAME} deps --install 自动补装"
def _tool_available(tool: str) -> bool:
    return resolve_tool_path(tool) is not None
def has_missing(missing: dict[str, Any]) -> bool:
    return bool(missing.get("missing_modules") or missing.get("missing_tools")
                or missing.get("missing_toolchain"))
def check_missing() -> dict[str, Any]:
    missing_modules = [name for name in REQUIRED_DEPENDENCIES if not spec_exists(name)]
    missing_tools = [tool for tool in REQUIRED_TOOLS if not _tool_available(tool)]
    missing_toolchain = [name for name in TOOLCHAIN_PACKAGES if not spec_exists(name)]
    pip_installable = [REQUIRED_DEPENDENCIES[name] for name in missing_modules]
    pip_installable.extend(TOOLCHAIN_PACKAGES[name] for name in missing_toolchain)
    pip_installable.extend(t for t in missing_tools if t in ("pytest", "ruff"))
    return {
        "missing_modules": missing_modules,
        "missing_tools": missing_tools,
        "missing_toolchain": missing_toolchain,
        "pip_installable": list(dict.fromkeys(pip_installable)),
    }
def _missing_summary(missing: dict[str, Any]) -> str:
    kinds = (("missing_modules", "缺失模块"), ("missing_tools", "缺失工具"),
             ("missing_toolchain", "缺失测试工具链"))
    parts = [f"{label}: {', '.join(missing[key])}"
             for key, label in kinds if missing.get(key)]
    return "；".join(parts) if parts else "依赖齐备"
def _run_pip_install(pkgs: list[str], timeout: int) -> subprocess.CompletedProcess:
    cmd = [sys.executable, "-m", "pip", "install",
           "--disable-pip-version-check", "--", *pkgs]
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
        check=False,
    )
def ensure_dependencies(auto_install: bool = True,
                        timeout: int = _DEFAULT_PIP_TIMEOUT) -> dict[str, Any]:
    try:
        auto_install = _flag_enabled(auto_install, default=True)
        missing = check_missing()
        if not has_missing(missing):
            return {"status": "ok", "data": missing, "message": "依赖齐备，无需安装"}
        if not auto_install:
            message = _missing_summary(missing) + _AUTO_INSTALL_HINT
            return {"status": "error", "data": missing, "message": message}
        install_error, installed = _attempt_pip_install(missing, timeout)
        if install_error is not None:
            return install_error
        if installed:
            importlib.invalidate_caches()
        return _assemble_ensure_result(check_missing(), installed)
    except OSError as exc:
        logger.warning("环境异常: %s", exc)
        return {"status": "error", "data": {}, "message": f"环境异常: {exc}"}
    except Exception as exc:
        logger.warning("依赖自举未预期异常，降级返回 error: %s", exc)
        return {"status": "error", "data": {}, "message": f"依赖自举未预期异常: {exc}"}
def _attempt_pip_install(
    missing: dict[str, Any], timeout: int,
) -> tuple[dict[str, Any] | None, list[str]]:
    pip_pkgs = missing["pip_installable"]
    installed: list[str] = []
    if not pip_pkgs:
        return None, installed
    if not spec_exists("pip"):
        return ({"status": "error", "data": missing,
                 "message": "当前解释器无 pip，无法自动补装"
                            "（可先 python -m ensurepip，或改用带 pip 的环境运行）"},
                installed)
    try:
        proc = _run_pip_install(pip_pkgs, timeout)
    except subprocess.TimeoutExpired:
        logger.warning("pip 安装超时（>%ss）", timeout)
        return ({"status": "error",
                 "data": dict(missing, pip_failed=pip_pkgs),
                 "message": f"pip 安装超时（>{timeout}s），可重试或手动 pip install"},
                installed)
    if proc.returncode != 0:
        tail_lines = (proc.stderr or proc.stdout or "").strip().splitlines()
        pip_tail = tail_lines[-5:]
        message = (
            "pip 安装失败（若为 PEP 668 外部管理环境，请改用虚拟环境或追加 --user）"
            + "；" + _missing_summary(missing)
        )
        return ({"status": "error",
                 "data": dict(missing, pip_failed=pip_pkgs, pip_tail=pip_tail),
                 "message": message}, installed)
    return None, pip_pkgs
def _assemble_ensure_result(after: dict[str, Any], installed: list[str]) -> dict[str, Any]:
    status = "ok" if not has_missing(after) else "error"
    message = _missing_summary(after)
    if installed:
        message = "已安装: " + ", ".join(installed) + "；" + message
    if after["missing_tools"]:
        hints = [f"{tool} ({REQUIRED_TOOLS[tool]})" for tool in after["missing_tools"]]
        message += "；需手动处理: " + "; ".join(hints)
    return {"status": status, "data": dict(after, installed=installed), "message": message}
def _pip_install(pkg: str) -> None:
    logger.info("%s dep_installer: 检测到外部依赖缺失，自动安装 %s",
                _PACKAGE_NAME, pkg)
    try:
        proc = _run_pip_install([pkg], timeout=_DEFAULT_PIP_TIMEOUT)
    except Exception as e:
        raise RuntimeError(
            f"自动安装外部依赖失败: {pkg}（无法启动 pip: {e}）"
        ) from e
    if proc.returncode != 0:
        raise RuntimeError(
            f"自动安装外部依赖失败: {pkg}（pip 退出码 {proc.returncode}）\n"
            f"stdout: {proc.stdout[-1500:]}\n"
            f"stderr: {proc.stderr[-1500:]}"
        )
    logger.info("%s dep_installer: 外部依赖 %s 安装成功",
                _PACKAGE_NAME, pkg)
def _resolve_missing_packages(pkgs: list[str]) -> tuple[list[str], list[str]]:
    missing: list[str] = []
    unresolvable: list[str] = []
    for pkg in pkgs:
        if not isinstance(pkg, str) or not clean_pkg_name(pkg):
            unresolvable.append(str(pkg))
            continue
        if not module_available(pkg):
            missing.append(pkg)
    if unresolvable:
        logger.warning(
            "%s dep_installer: 包名 %s 无法解析（非 str 或空模块名形态）",
            _PACKAGE_NAME, ", ".join(unresolvable))
    return missing, unresolvable
def _install_packages(
    missing: list[str],
) -> tuple[list[str], list[str], list[str]]:
    installed: list[str] = []
    install_failed: list[str] = []
    not_attempted: list[str] = []
    for index, pkg in enumerate(missing):
        try:
            _pip_install(pkg)
            installed.append(pkg)
        except RuntimeError as exc:
            logger.warning("%s dep_installer: %s", _PACKAGE_NAME, exc)
            logger.warning(
                "外部依赖 %s 安装失败，包加载继续（相关功能自动降级）；"
                "补装：python -m %s deps --install",
                pkg, _PACKAGE_NAME,
            )
            install_failed.append(pkg)
            not_attempted = missing[index + 1:]
            break
    if installed:
        importlib.invalidate_caches()
    return installed, install_failed, not_attempted
def ensure_deps(packages: list[str] | None = None) -> dict:
    pkgs: list[str] = (list(normalize_check_items(packages))
                       if packages is not None else RUNTIME_DEPS)
    missing, unresolvable = _resolve_missing_packages(pkgs)
    installed, install_failed, not_attempted = _install_packages(missing)
    post_install_missing = (
        _resolve_missing_packages(installed)[0] if installed else [])
    failed = list(dict.fromkeys(
        unresolvable + install_failed + not_attempted + post_install_missing))
    if not failed:
        return {"status": "ok", "installed": installed}
    segments: list[str] = []
    if unresolvable:
        segments.append(
            "无法解析模块名的未登记包名: " + ", ".join(unresolvable))
    if install_failed or post_install_missing:
        segments.append(
            "依赖自动补装失败或安装后仍不可用: "
            + ", ".join(dict.fromkeys(install_failed + post_install_missing)))
    if not_attempted:
        segments.append("首个补装失败后未尝试: " + ", ".join(not_attempted))
    return {
        "status": "error",
        "installed": installed,
        "failed": failed,
        "not_attempted": not_attempted,
        "message": "；".join(segments) + "（包加载继续，功能降级）",
    }
_REQUIREMENT_PARSER_UNAVAILABLE = object()
def _parse_pep508_requirement(pkg_name: Any) -> Any | None:
    if not isinstance(pkg_name, str) or not pkg_name.strip():
        return None
    try:
        from packaging.requirements import InvalidRequirement, Requirement
    except ImportError as exc:
        _swallow('_parse_pep508_requirement', exc)
        return _REQUIREMENT_PARSER_UNAVAILABLE
    try:
        return Requirement(pkg_name)
    except InvalidRequirement:
        return None
def _installed_version_matches(requirement: Any | None) -> bool:
    if requirement is None or not requirement.specifier:
        return True
    try:
        installed_version = distribution(requirement.name).version
    except PackageNotFoundError:
        return False
    return requirement.specifier.contains(installed_version, prereleases=True)
def module_available(pkg_name: str) -> bool:
    try:
        requirement = _parse_pep508_requirement(pkg_name)
        if requirement is None:
            return False
        if requirement is _REQUIREMENT_PARSER_UNAVAILABLE:
            requirement = None
        elif (requirement.marker is not None
                and not requirement.marker.evaluate()):
            return True
        p = clean_pkg_name(pkg_name)
        m = p and pip_pkg_to_module(p)
        if m:
            if not spec_exists(m):
                return False
        elif not p:
            return False
        else:
            try:
                distribution(p)
            except PackageNotFoundError:  # jwsgj:silent-ok
                return False
        return _installed_version_matches(requirement)
    except (ImportError, ValueError, TypeError, OSError) as _swallowed_exc:
        _swallow('module_available', _swallowed_exc)
        return False
def _probe_items(items: Any, probe: Callable[[str], bool]) -> dict[str, bool]:
    results: dict[str, bool] = {}
    for item in normalize_check_items(items):
        results[str(item)] = probe(item) if isinstance(item, str) else False
    return results
def check_python_deps(dependencies: list) -> dict:
    return _probe_items(dependencies, module_available)
def check_system_tools(tools: list) -> dict:
    return _probe_items(tools, _tool_available)
@dataclass
class DependencySpec:
    bins: list[str] = field(default_factory=list)
    packages: dict[str, Any] = field(default_factory=dict)
    env: list[str] = field(default_factory=list)
    config: dict[str, str] = field(default_factory=dict)
    @classmethod
    def from_frontmatter(cls, frontmatter: dict) -> DependencySpec:
        if not isinstance(frontmatter, dict):
            frontmatter = {}
        deps = frontmatter.get("dependencies", {})
        if isinstance(deps, (list, str)):
            return cls(packages={"pip": _dedup_str_items(dep_pkg_list(deps))})
        if not isinstance(deps, dict):
            return cls(packages={})
        return _parse_dep_mapping(deps)
    @staticmethod
    def python_compatibility(spec: Any) -> tuple[bool, str]:
        config = getattr(spec, "config", None)
        raw = (spec.get("python") if isinstance(spec, dict)
               else config.get("python") if isinstance(config, dict) else None)
        constraint = (raw.strip() if isinstance(raw, str)
                      else "" if raw is None else str(raw).strip())
        if not constraint or constraint == "*":
            return True, "compatible"
        requirement = _parse_pep508_requirement(
            f"python{_requirement_operator(constraint)}{constraint}")
        if requirement is _REQUIREMENT_PARSER_UNAVAILABLE:
            return False, (f"Python requirement {constraint!r} cannot be verified: "
                           "packaging is unavailable")
        if requirement is None:
            return False, f"Invalid Python requirement: {constraint}"
        if requirement.marker is not None and not requirement.marker.evaluate():
            return True, "compatible"
        current = platform.python_version()
        compatible = requirement.specifier.contains(current, prereleases=True)
        return (compatible, "compatible" if compatible else
                f"Requires Python {constraint}, current is {current}")
    @staticmethod
    def platform_compatibility(spec: Any) -> tuple[bool, str]:
        return _check_hw_compat(
            _hw_requirement(spec, ("os", "platform"), "platform"),
            _PLATFORM_ALIASES, _CURRENT_OS)
    @staticmethod
    def arch_compatibility(spec: Any) -> tuple[bool, str]:
        return _check_hw_compat(
            _hw_requirement(spec, ("arch",), "arch"),
            _ARCH_ALIASES, _CURRENT_ARCH)
@dataclass
class DependencyCheckResult:
    skill_name: str = ""
    passed: bool = True
    missing_bins: list[str] = field(default_factory=list)
    missing_packages: list[str] = field(default_factory=list)
    missing_env: list[str] = field(default_factory=list)
    missing_config: list[str] = field(default_factory=list)
    platform_compatible: bool = True
    arch_compatible: bool = True
    details: dict[str, str] = field(default_factory=dict)
    def record_packages(self, packages: Any,
                        check_packages: Callable[[Any], list[str]]) -> None:
        pkg_map = (packages if isinstance(packages, dict)
                   else {"pip": packages}
                   if isinstance(packages, (str, list, tuple)) else {})
        for pkg_manager, pkgs in pkg_map.items():
            if str(pkg_manager).lower() != "pip":
                names = ([str(p) for p in pkgs] if isinstance(pkgs, (list, tuple))
                         else _split_pkg_list(pkgs) if isinstance(pkgs, str)
                         else [str(k) for k in pkgs] if isinstance(pkgs, dict)
                         else [str(pkgs)])
                if names:
                    self.details[f"{pkg_manager}_unverified"] = (
                        f"packages not verified (needs {pkg_manager}): "
                        + ", ".join(names))
                continue
            missing = (check_packages(_dedup_str_items(_manager_pkg_list("pip", pkgs)))
                       if isinstance(pkgs, (list, tuple, set, frozenset, str, dict))
                       else None)
            if missing is None:
                self.details[f"{pkg_manager}_unverified"] = (
                    f"packages not verified (unparseable value: "
                    f"{type(pkgs).__name__})")
            else:
                self.missing_packages.extend(missing)
        if self.missing_packages:
            self.passed = False
    def install_commands(self) -> list[str]:
        cmds = [f"# install missing binary: {b}" for b in self.missing_bins]
        cmds.extend(
            f'pip install "{pkg}"'
            if re.search(r"[<>=!~;\[\]\s]", str(pkg)) else f"pip install {pkg}"
            for pkg in self.missing_packages)
        env_setter = "set" if os.name == "nt" else "export"
        cmds.extend(f"# set env var: {env_setter} {e}=..."
                    for e in self.missing_env)
        return cmds
_PACKAGE_NAME_START_RE = re.compile(
    r"[A-Za-z0-9](?:[A-Za-z0-9._-]*[A-Za-z0-9])?")
_REQUIREMENT_CONTINUATION_CHARS = frozenset("<>=!~@;,")
_LIST_SEPARATOR_EDGE_RE = re.compile(r"^[\s,]+|[\s,]+$")
def _strip_list_separators(item: str) -> str:
    """剥离列表项两端的空白与逗号。

    逗号只作列表分隔符，不属于 PEP 508 说明符。切分仅依赖「分隔符后紧跟
    包名开头」，尾随/连续逗号（多行折叠的 ``"a,\nb,"``）会并入相邻项，
    使已安装依赖被判缺失并生成 ``pip install b,`` 这类错误命令。
    """
    return _LIST_SEPARATOR_EDGE_RE.sub("", item)
def _split_pkg_list(raw: str) -> list[str]:
    items: list[str] = []
    buf: list[str] = []
    quote = ""
    escaped = False
    bracket_depth = 0
    in_environment_marker = False
    for index, char in enumerate(raw):
        if quote:
            buf.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = ""
            continue
        if char in ("'", '"'):
            quote = char
            buf.append(char)
            continue
        if char == "[":
            bracket_depth += 1
        elif char == "]" and bracket_depth:
            bracket_depth -= 1
        if bracket_depth:
            buf.append(char)
            continue
        if char == ";":
            in_environment_marker = True
            buf.append(char)
            continue
        if char == "," or char.isspace():
            remainder = raw[index + 1:].lstrip()
            starts_package = bool(_PACKAGE_NAME_START_RE.match(remainder))
            previous = next(
                (part for part in reversed(buf) if not part.isspace()), "")
            whitespace_boundary = (
                not in_environment_marker
                and previous not in _REQUIREMENT_CONTINUATION_CHARS
            )
            if (buf and starts_package
                    and (char == "," or whitespace_boundary)):
                item = _strip_list_separators("".join(buf))
                if item:
                    items.append(item)
                buf = []
                in_environment_marker = False
                continue
        buf.append(char)
    item = _strip_list_separators("".join(buf))
    if item:
        items.append(item)
    return items
def normalize_check_items(items: Any) -> list:
    if isinstance(items, str):
        return _split_pkg_list(items)
    if isinstance(items, (list, tuple)):
        return list(items)
    if isinstance(items, (set, frozenset)):
        return sorted(items, key=lambda item: (type(item).__name__, str(item)))
    if isinstance(items, Iterable) and not isinstance(
            items, (bytes, bytearray, dict)):
        return list(items)
    return []
def clean_pkg_name(pkg_name: str) -> str:
    return re.split(r"[<>=!~;\[(@]", pkg_name, maxsplit=1)[0].strip()
def _dep_str_list(v) -> list[str]:
    if isinstance(v, str):
        return _split_pkg_list(v)
    if isinstance(v, (set, frozenset)):
        return [p.strip() for p in sorted(v, key=str)
                if isinstance(p, str) and p.strip()]
    if isinstance(v, (list, tuple)):
        return [p.strip() for p in v if isinstance(p, str) and p.strip()]
    return []
def dep_pkg_list(v) -> list[str]:
    return ([k for k in v if isinstance(k, str) and k.strip()]
            if isinstance(v, dict) else _dep_str_list(v))
def _merge_pkg_list(target: list[str], extra: list[str]) -> None:
    for p in extra:
        if p not in target:
            target.append(p)
def _dedup_str_items(items: Any) -> list[str]:
    if isinstance(items, (set, frozenset)):
        items = sorted(items, key=str)
    if not isinstance(items, (list, tuple, set, frozenset)):
        return []
    return list(dict.fromkeys(
        item for item in items if isinstance(item, str)))
def _norm_hw_token(value: str, aliases: dict[str, str]) -> str:
    v = value.strip().lower()
    return aliases.get(v, v)
def _check_hw_compat(req: Any, aliases: dict[str, str],
                     current: str) -> tuple[bool, str]:
    allowed = _norm_hw_values(req, aliases)
    return (False, f"Requires {allowed}, current is {current}"
            ) if allowed and current not in allowed else (True, "compatible")
def _norm_hw_values(req: Any, aliases: dict[str, str]) -> list[str]:
    items = ([req] if isinstance(req, str)
             else req if isinstance(req, (list, tuple)) else ())
    return [_norm_hw_token(x, aliases)
            for x in items if isinstance(x, str) and x.strip()]
def _parse_config_key(spec: DependencySpec, v: Any) -> None:
    if not isinstance(v, dict):
        return
    for ck, cv in v.items():
        if not isinstance(ck, str):
            continue
        ckl = ck.lower()
        if ckl == "os":
            _parse_hw_key(spec, "platform", cv)
        elif ckl == "platform":
            _parse_hw_key(spec, "platform", cv, overwrite=False)
        elif ckl == "arch":
            _parse_hw_key(spec, "arch", cv)
        else:
            spec.config[ck] = cv if isinstance(cv, str) else str(cv)
def _parse_packages_key(pkgs: dict, v: Any) -> None:
    if isinstance(v, dict):
        for mgr, mgr_pkgs in v.items():
            if not isinstance(mgr, str):
                continue
            manager = mgr.strip().lower()
            _merge_pkg_list(pkgs.setdefault(manager, []),
                            _manager_pkg_list(manager, mgr_pkgs))
    elif isinstance(v, (str, list, tuple, set, frozenset)):
        _merge_pkg_list(pkgs.setdefault("pip", []), dep_pkg_list(v))
def _parse_hw_key(spec: DependencySpec, field: str, v: Any, *,
                  overwrite: bool = True) -> None:
    current, aliases = _HW_DECL_SPECS[field]
    items = _norm_hw_values(v, aliases)
    picked = current if current in items else items[0] if items else None
    if picked is None:
        return
    if overwrite or field not in spec.config:
        spec.config[field] = picked
def _apply_structured_dep_key(spec: DependencySpec, pkgs: dict,
                              kl: str, v: Any) -> None:
    if kl in ("bins", "env"):
        setattr(spec, kl, _dep_str_list(v))
        return
    if kl == "config":
        _parse_config_key(spec, v)
        return
    if kl == "packages":
        _parse_packages_key(pkgs, v)
        return
    if kl == "os":
        _parse_hw_key(spec, "platform", v)
        return
    if kl == "platform":
        _parse_hw_key(spec, "platform", v, overwrite=False)
        return
    if kl == "python":
        spec.config["python"] = v if isinstance(v, str) else str(v)
        return
    _parse_hw_key(spec, "arch", v)
_REQUIREMENT_OPERATOR_CHARS = frozenset("<>=!~@")


def _requirement_operator(constraint: str) -> str:
    """约束已带运算符/URL 标记时原样拼接，否则按 PEP 508 裸版本补 ``==``。

    不能只认数字开头：``v3.9`` 这类裸版本若不补 ``==`` 会被解析成包名
    ``pythonv3.9``（空说明符），Python 兼容性检查就会对任何解释器判"兼容"。
    """
    return "" if constraint[0] in _REQUIREMENT_OPERATOR_CHARS else "=="


def _dependency_requirement(name: str, value: Any) -> str:
    requirement = name.strip()
    if not requirement or not isinstance(value, str):
        return requirement
    constraint = value.strip()
    if not constraint or constraint == "*":
        return requirement
    return f"{requirement}{_requirement_operator(constraint)}{constraint}"
def _manager_pkg_list(manager: str, value: Any) -> list[str]:
    if manager.strip().lower() == "pip" and isinstance(value, dict):
        return [_dependency_requirement(key, constraint)
                for key, constraint in value.items()
                if isinstance(key, str) and key.strip()]
    return dep_pkg_list(value)
def _parse_dep_mapping(deps: dict) -> DependencySpec:
    pkgs: dict = {}
    spec = DependencySpec()
    for k, v in deps.items():
        if not isinstance(k, str):
            continue
        kl = k.lower()
        if kl in _DEP_STRUCTURED_KEYS:
            _apply_structured_dep_key(spec, pkgs, kl, v)
            continue
        if kl in _DEPENDENCY_MANAGERS:
            _merge_pkg_list(pkgs.setdefault(kl, []), _manager_pkg_list(kl, v))
        else:
            _merge_pkg_list(
                pkgs.setdefault("pip", []), [_dependency_requirement(k, v)])
    spec.packages = pkgs
    return spec
def _hw_requirement(spec: Any, dict_keys: tuple[str, ...],
                    spec_key: str) -> Any:
    config = getattr(spec, "config", None)
    return (next((spec[k] for k in dict_keys if spec.get(k)), None)
            if isinstance(spec, dict)
            else config.get(spec_key) if isinstance(config, dict) else None)
_DEPENDENCY_MANAGERS = {"pip", "npm", "pnpm", "yarn", "uv", "poetry",
                        "conda", "apt", "brew", "cargo", "go", "gem"}
_DEP_STRUCTURED_KEYS = {"bins", "env", "config", "packages",
                        "platform", "arch", "os", "python"}
_PLATFORM_ALIASES = {
    "win": "win32", "win32": "win32",
    "windows": "win32", "windows_nt": "win32",
    "mac": "darwin", "darwin": "darwin",
    "macos": "darwin", "macosx": "darwin", "osx": "darwin",
    "linux": "linux",
}
_ARCH_ALIASES = {
    "x86": "x86",
    "i386": "x86", "i486": "x86", "i586": "x86", "i686": "x86",
    "x64": "amd64", "x86_64": "amd64", "amd64": "amd64",
    "arm": "arm", "armv6l": "arm", "armv7l": "arm",
    "arm64": "arm64", "aarch64": "arm64",
}
_CURRENT_OS = _norm_hw_token(sys.platform, _PLATFORM_ALIASES)
_CURRENT_ARCH = _norm_hw_token(platform.machine(), _ARCH_ALIASES)
_HW_DECL_SPECS: dict[str, tuple[str, dict[str, str]]] = {
    "platform": (_CURRENT_OS, _PLATFORM_ALIASES),
    "arch": (_CURRENT_ARCH, _ARCH_ALIASES),
}
class DependencyManager:
    def check_bins(self, bins: list[str]) -> list[str]:
        return [b for b, ok in check_system_tools(bins).items() if not ok]
    def check_packages(self, packages: Any) -> list[str]:
        missing: list[str] = []
        for pkg_name in _manager_pkg_list("pip", packages):
            if not isinstance(pkg_name, str):
                continue
            if (not clean_pkg_name(pkg_name)
                    or not module_available(pkg_name)):
                missing.append(pkg_name)
        return missing
    def check_env(self, env_vars: list[str]) -> tuple[list[str], list[str]]:
        avail: list[str] = []
        missing: list[str] = []
        for var_name in normalize_check_items(env_vars):
            if not isinstance(var_name, str):
                missing.append(str(var_name))
                continue
            if var_name in os.environ:
                avail.append(var_name)
            else:
                missing.append(var_name)
        return avail, missing
    def check_skill_dependencies(self, skill_name: str, spec: Any) -> DependencyCheckResult:
        if isinstance(spec, dict):
            spec = DependencySpec.from_frontmatter(spec)
        elif not isinstance(spec, DependencySpec):
            spec = DependencySpec()
        result = DependencyCheckResult(skill_name=skill_name)
        self._record_hw_compat(
            result, "platform", *DependencySpec.platform_compatibility(spec))
        python_compatible, python_reason = DependencySpec.python_compatibility(spec)
        if not python_compatible:
            result.passed = False
            result.details["python"] = python_reason
        self._record_hw_compat(
            result, "arch", *DependencySpec.arch_compatibility(spec))
        if spec.bins:
            result.missing_bins = self.check_bins(spec.bins)
            if result.missing_bins:
                result.passed = False
        result.record_packages(spec.packages, self.check_packages)
        if spec.env:
            _avail, missing = self.check_env(spec.env)
            result.missing_env = missing
            if result.missing_env:
                result.passed = False
        return result
    @staticmethod
    def _record_hw_compat(result: DependencyCheckResult, label: str,
                          compat: bool, reason: str) -> None:
        setattr(result, f"{label}_compatible", compat)
        if not compat:
            result.passed = False
            result.details[label] = reason
_TOOL_PACKAGES: dict[str, str] = {
    "ruff": "ruff",
    "bandit": "bandit",
    "mypy": "mypy",
    "pylint": "pylint",
    "black": "black",
    "isort": "isort",
    "flake8": "flake8",
    "vulture": "vulture",
}
_INSTALL_LOCK = threading.Lock()
_ATTEMPTED_INSTALL: set[tuple[str, str]] = set()
def get_tool_package(tool_name: str) -> str:
    return (_TOOL_PACKAGES.get(tool_name, tool_name)
            if isinstance(tool_name, str) and tool_name else "")
def resolve_tool_path(tool_name: str) -> str | None:
    if not isinstance(tool_name, str) or not tool_name.strip():
        return None
    found = shutil.which(tool_name)
    if found:
        return found
    for cand in _tool_candidates(tool_name):
        if os.path.isfile(cand) and (os.name == "nt" or os.access(cand, os.X_OK)):
            return cand
    return None
def run_tool_process(cmd: list[str], *, env: dict[str, str] | None = None,
                     cwd: str, timeout: int = 120) -> subprocess.CompletedProcess:
    run_env = subprocess_noartifact_env() if env is None else env
    cmd = [cmd] if isinstance(cmd, str) else list(cmd)
    return subprocess.run(  # jwsgj:suppress SYM-TAINT
        cmd, check=False, capture_output=True, text=True, timeout=timeout,
        encoding="utf-8", errors="replace", env=run_env, cwd=cwd)
def _tool_candidates(tool_name: str) -> list[str]:
    exe_dir = os.path.dirname(sys.executable)
    suffixes = ((".exe", ".cmd", ".bat", "") if os.name == "nt"
                else ("", ".exe", ".cmd", ".bat"))
    bases = (os.path.join(exe_dir, "Scripts"), exe_dir,
             os.path.join(exe_dir, "bin"))
    return [os.path.join(base, tool_name + suffix)
            for base in bases for suffix in suffixes]
def _probe_cwd() -> str:
    try:
        import tempfile as _tempfile  # lazy-by-design
        return _tempfile.gettempdir()
    except Exception:  # noqa: BLE001  # jwsgj:silent-ok
        return os.getcwd()
def verify_tool(tool_name: str) -> tuple[bool, str]:
    tool_path = resolve_tool_path(tool_name)
    if tool_path is None:
        return False, ""
    try:
        proc = subprocess.run(  # jwsgj:suppress SYM-TAINT
            [tool_path, "--version"],
            capture_output=True, text=True, timeout=10,
            encoding="utf-8", errors="replace", check=False,
            env=subprocess_noartifact_env(),
            cwd=_probe_cwd(),
        )
        if proc.returncode != 0:
            logger.debug("[ToolInstaller] %s --version exit=%s",
                          tool_name, proc.returncode)
            return False, ""
        version = ((proc.stdout or "").strip()
                   or (proc.stderr or "").strip())
        return True, version
    except (subprocess.TimeoutExpired, OSError) as e:
        logger.debug("[ToolInstaller] %s --version failed: %s", tool_name, e)
        return False, ""
def _install_package(package_spec: str, timeout: int) -> tuple[bool, str]:
    logger.info("[ToolInstaller] installing: %s (timeout=%ds)",
                 package_spec, timeout)
    try:
        proc = _run_pip_install([package_spec], timeout)
    except subprocess.TimeoutExpired:
        logger.exception("[ToolInstaller] install timeout(%ds): %s",
                      timeout, package_spec)
        return False, f"timeout({timeout}s)"
    except OSError as e:
        logger.exception("[ToolInstaller] process launch failed: %s",
                      package_spec)
        return False, str(e)
    if proc.returncode == 0:
        logger.info("[ToolInstaller] install ok: %s", package_spec)
        return True, "installed"
    err_tail = _pip_error_tail(proc)
    logger.error("[ToolInstaller] install failed: %s: %s",
                  package_spec, err_tail)
    return False, err_tail
def _pip_error_tail(proc) -> str:
    stderr_tail = (proc.stderr or "").strip()
    stdout_tail = (proc.stdout or "").strip()
    tail = (stderr_tail or stdout_tail)[-500:]
    return tail or f"pip returncode={proc.returncode}"
def _install_result(status: str, tool_name: str, version: str = "",
                    error: str = "") -> dict:
    return {"status": status, "tool": tool_name,
            "version": version, "error": error}
def install_tool(tool_name: str, pip_packages: str | None = None,
                 timeout: int = _DEFAULT_INSTALL_TIMEOUT) -> dict:
    if not isinstance(tool_name, str) or not tool_name.strip():
        return _install_result("error", str(tool_name or "")[:60],
                               error="tool_name 必须为非空字符串")
    package = pip_packages or get_tool_package(tool_name)
    start = time.perf_counter()
    with _INSTALL_LOCK:
        attempt_key = (tool_name, package)
        if attempt_key in _ATTEMPTED_INSTALL:
            avail, ver = verify_tool(tool_name)
            if avail:
                return _install_result("ok", tool_name, ver)
            return _install_result(
                "error", tool_name,
                error="install attempted in this process but tool unavailable")
        _ATTEMPTED_INSTALL.add(attempt_key)
        ok, msg = _install_package(package, timeout=timeout)
        if not ok:
            return _install_result("error", tool_name, error=msg)
    avail, ver = verify_tool(tool_name)
    elapsed = round((time.perf_counter() - start) * 1000, 1)
    if avail:
        logger.info("[ToolInstaller] %s install+verify ok (%.1fms): %s",
                     tool_name, elapsed, ver)
        return _install_result("ok", tool_name, ver)
    logger.error("[ToolInstaller] %s installed but verify failed", tool_name)
    return _install_result("error", tool_name,
                           error="installed but not found in PATH")
def ensure_tool(tool_name: str, pip_packages: str | None = None,
                install_timeout: int = _DEFAULT_INSTALL_TIMEOUT) -> dict:
    avail, ver = verify_tool(tool_name)
    if avail:
        return _install_result("ok", tool_name, ver)
    logger.warning("[ToolInstaller] tool %s missing, installing...",
                    tool_name)
    result = install_tool(tool_name, pip_packages, timeout=install_timeout)
    if result["status"] == "ok":
        result["status"] = "installed"
    return result
def ensure_available(tool_name: str) -> bool:
    result = ensure_tool(tool_name)
    return result["status"] in ("ok", "installed")
def _module_present(directory: Path, name: str) -> bool:
    parts = str(name or "").split(".")
    if not parts or any(not part.isidentifier() for part in parts):
        return False
    base = directory.joinpath(*parts)
    return base.with_suffix(".py").is_file() or (base / "__init__.py").is_file()
def _walk_module_scope(tree: ast.Module, *,
                       include_try: bool = True) -> Iterator[ast.AST]:
    typing_aliases = typing_guard_aliases(tree)
    type_checking_names = typing_type_checking_names(tree) or None
    stack: list[ast.AST] = list(reversed(tree.body))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        if not include_try and isinstance(node, TRY_NODE_TYPES):
            stack.extend(reversed(node.finalbody))
            continue
        if (isinstance(node, ast.If)
                and is_type_checking_guard(
                    node.test, typing_aliases, type_checking_names)):
            stack.extend(reversed(list(node.orelse)))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _import_module_names(
    nodes: Iterable[ast.AST], package_name: str | None = None, *,
    directory: Path | None = None,
) -> Iterator[str]:
    prefix = f"{package_name}." if package_name else ""
    for node in nodes:
        if isinstance(node, ast.ImportFrom):
            module = node.module or ""
            if node.level:
                if node.level != 1:
                    continue
                if module:
                    yield module.split(".", 1)[0]
                else:
                    for alias in node.names:
                        name = alias.name.split(".", 1)[0]
                        if directory is None or _module_present(directory, name):
                            yield name
                        else:
                            yield "__init__"
                continue
            if package_name and module == package_name:
                for alias in node.names:
                    name = alias.name.split(".", 1)[0]
                    if directory is None or _module_present(directory, name):
                        yield name
                    else:
                        yield "__init__"
            elif prefix and module.startswith(prefix):
                yield module[len(prefix):].split(".", 1)[0]
            continue
        if isinstance(node, ast.Import) and prefix:
            for alias in node.names:
                if alias.name.startswith(prefix):
                    yield alias.name[len(prefix):].split(".", 1)[0]
def _read_entry_tree(directory: Path) -> ast.Module | None:
    try:
        entry = str(directory / "__init__.py")
        source = read_source_interpreter_encoding(entry)
        return ast.parse(source, filename=entry)
    except (OSError, UnicodeError, LookupError, SyntaxError, ValueError,
            RecursionError, MemoryError) as exc:
        _swallow('_read_entry_tree', exc)
        return None
def _present_module_names(directory: Path, names: Iterable[str]) -> list[str]:
    present: list[str] = []
    for name in names:
        if name not in present and _module_present(directory, name):
            present.append(name)
    return present
def _discover_entry_modules(
    package_dir: str | Path | None = None,
    package_name: str | None = None,
) -> tuple[tuple[str, ...], tuple[str, ...]]:
    directory = _PACKAGE_DIR if package_dir is None else Path(package_dir)
    package = package_name or directory.name
    tree = _read_entry_tree(directory)
    facades: list[str] = []
    immediate: list[str] = []
    if tree is not None:
        facades = _present_module_names(
            directory, _import_module_names(_walk_module_scope(tree), package))
        immediate = list(dict.fromkeys(_import_module_names(
            _walk_module_scope(tree, include_try=False),
            package, directory=directory)))
        for name in immediate:
            if name not in facades:
                facades.append(name)
    elif (directory / "__init__.py").is_file():
        facades.append("__init__")
        immediate.append("__init__")
    if (directory / "__main__.py").is_file() and "__main__" not in facades:
        facades.insert(0, "__main__")
    core = tuple(f"{package}.{name}" for name in immediate) or (package,)
    return tuple(facades), core
class _MemStatus(ctypes.Structure):
    _fields_ = [
        ("dwLength", ctypes.c_ulong),
        ("dwMemoryLoad", ctypes.c_ulong),
        ("ullTotalPhys", ctypes.c_uint64),
        ("ullAvailPhys", ctypes.c_uint64),
        ("ullTotalPageFile", ctypes.c_uint64),
        ("ullAvailPageFile", ctypes.c_uint64),
        ("ullTotalVirtual", ctypes.c_uint64),
        ("ullAvailVirtual", ctypes.c_uint64),
        ("ullAvailExtendedVirtual", ctypes.c_uint64),
    ]
def _available_via_psutil() -> int | None:
    if _psutil is None:
        logger.debug("[mem_guard] psutil 未安装，跳过 psutil 读取，走系统 API 降级链")
        return None
    try:
        return _psutil.virtual_memory().available
    except Exception:
        logger.debug("[mem_guard] psutil 读取失败，回退系统 API 降级链",
                     exc_info=True)
        return None
def _available_via_win32() -> int | None:
    if os.name != "nt":
        return None
    try:
        _ms = _MemStatus()
        _ms.dwLength = ctypes.sizeof(_MemStatus)
        if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(_ms)):
            return int(_ms.ullAvailPhys)
    except Exception as _e:
        _swallow('_available_via_win32', _e)
    return None
def _parse_meminfo_available(text: str) -> int | None:
    for line in text.splitlines():
        fields = line.split()
        if len(fields) < 2 or fields[0] != "MemAvailable:":
            continue
        try:
            return int(fields[1]) * 1024
        except ValueError as exc:
            _swallow('_parse_meminfo_available', exc)
            return None
    return None
def _available_via_meminfo() -> int | None:
    if os.name == "nt":
        return None
    try:
        with open("/proc/meminfo", encoding="ascii") as _f:  # jwsgj:suppress 供应链安全-敏感路径
            _text = _f.read()
    except (OSError, ValueError) as exc:
        _swallow('_available_via_meminfo', exc)
        return None
    return _parse_meminfo_available(_text)
def available_memory_bytes() -> int | None:
    for _probe in (_available_via_psutil, _available_via_win32,
                   _available_via_meminfo):
        _avail = _probe()
        if _avail is not None:
            return _avail
    return None
def current_process_rss_mb() -> float:
    if _psutil is None:
        return 0.0
    try:
        return _psutil.Process().memory_info().rss / (1024 * 1024)
    except Exception as _e:
        _swallow('current_process_rss_mb', _e)
        return 0.0
def _run_sub_checks(
    probes: Iterable[tuple[str, Callable[[], Any]]], *,
    degrade_status: str, payload_key: str, log_label: str,
) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    for name, probe in probes:
        try:
            checks[name] = probe()
        except Exception as exc:
            logger.warning("%s 子检查 %s 执行失败（降级 %s）: %s",
                         log_label, name, degrade_status, exc)
            checks[name] = {"status": degrade_status,
                            payload_key: f"子检查异常: {str(exc)[:200]}"}
    return checks
def _workspace_dir() -> str:
    try:
        return resolve_workspace_root()
    except (RuntimeError, ValueError) as _e:
        _swallow('_workspace_dir', _e)
        return ""
def _workspace_source_hint() -> str:
    return "" if os.environ.get("WORKSPACE_DIR") else "WORKSPACE_DIR not set（按 cwd 推断）; "
def _count_skill_dirs(skills_dir: str) -> int:
    return len([d for d in os.listdir(skills_dir)
                if not d.startswith('.') and d != '__pycache__'
                and os.path.isfile(os.path.join(skills_dir, d, 'SKILL.md'))])
def _skill_root_candidates(ws: str) -> list[str]:
    candidates = [os.path.join(ws, 'skills')] if ws else []
    try:
        candidates.extend(skill_search_roots())
    except (OSError, RuntimeError, ValueError, TypeError) as _e:
        _swallow('_skill_root_candidates', _e)
    ordered: list[str] = []
    seen: set[str] = set()
    for cand in candidates:
        key = os.path.normcase(os.path.abspath(cand))
        if key in seen or not os.path.isdir(cand):
            continue
        seen.add(key)
        ordered.append(cand)
    return ordered
def _check_skills_dir() -> dict:
    roots = _skill_root_candidates(_workspace_dir())
    if not roots:
        return {"status": "warn",
                "reason": _workspace_source_hint() + "未发现可检索的技能根"}
    measured: list[tuple[str, int]] = []
    failures: list[str] = []
    for root in roots:
        try:
            measured.append((root, _count_skill_dirs(root)))
        except OSError as _e:  # jwsgj:silent-ok
            failures.append(f"{root}: {_e}")
    if failures:
        _swallow('_check_skills_dir', OSError("; ".join(failures[:3])))
        return {"status": "warn",
                "reason": "技能根列举失败: " + "; ".join(failures[:3])}
    path, skills = measured[0]
    return {"status": "ok", "path": path, "skills": skills}
def _resolve_state_dir() -> tuple[str | None, str | None]:
    try:
        return lifecycle_state_dir(str(_PACKAGE_DIR)), None
    except RuntimeError as _e:
        _swallow('_resolve_state_dir', _e)
        return None, str(_e)
def _state_dir_guard() -> tuple[Path | None, dict | None]:
    resolved, err = _resolve_state_dir()
    if resolved is None:
        return None, {"status": "warn",
                      "reason": f"{STATE_DIR_NAME} 归口不可用: {err}"}
    state_dir = Path(resolved)
    if not state_dir.is_dir():
        return None, {"status": "missing", "path": str(state_dir),
                      "reason": f"状态目录尚未创建（{STATE_DIR_NAME} 状态面未初始化）"}
    return state_dir, None
def _check_state_dir() -> dict:
    state_dir, payload = _state_dir_guard()
    return payload or {"status": "ok", "path": str(state_dir)}
def _check_version() -> dict:
    return {"status": "ok", "version": PACKAGE_VERSION}
def _check_runtime() -> dict:
    _version = f"{sys.version_info.major}.{sys.version_info.minor}"
    if sys.version_info[:2] < MIN_PYTHON:
        return {
            "status": "warn",
            "python": _version,
            "reason": (f"Python {_version} 低于基线 "
                       f"{MIN_PYTHON[0]}.{MIN_PYTHON[1]}"),
        }
    if not sys.executable:
        return {"status": "warn", "python": _version,
                "reason": "sys.executable 为空，无法派生子进程验证"}
    return {"status": "ok", "python": _version}
def _check_log_channel() -> dict:
    log_dir = _PACKAGE_DIR / SKILL_LOG_DIR_NAME
    if not log_dir.is_dir():
        defect = "缺失"
    elif not os.access(log_dir, os.W_OK):
        defect = "不可写"
    else:
        return {"status": "ok", "path": str(log_dir)}
    return {"status": "warn", "path": str(log_dir),
            "reason": f"日志目录{defect}（运维留痕将静默降级）"}
def _read_json_status(path: Path) -> str | None:
    _data, status, error = read_json_artifact(str(path))
    if status == "ok":
        return None
    detail = error or "文件不存在"
    logger.warning("健康检查: 状态文件不可用 %s: %s", path.name, detail)
    return f"{path.name}: {detail[:120]}"
def _check_state_files() -> dict:
    state_dir, payload = _state_dir_guard()
    if payload is not None:
        return {**payload, "json_files": 0, "broken": []}
    json_files = sorted(state_dir.glob("*.json"))
    broken = [err for err in (_read_json_status(p) for p in json_files)
              if err is not None]
    result = {
        "status": "warn" if broken else "ok",
        "path": str(state_dir),
        "json_files": len(json_files),
        "broken": broken,
    }
    if broken:
        result["reason"] = f"{len(broken)} 个状态文件结构损坏"
    return result
def _check_workspace_temp() -> dict:
    workspace = _workspace_dir()
    if not workspace:
        return {"status": "warn",
                "reason": "WORKSPACE_DIR not set（无产物落点）"}
    try:
        temp_dir = get_temp_base()
    except (RuntimeError, ValueError) as _e:
        _swallow('_check_workspace_temp', _e)
        return {"status": "warn",
                "reason": f"产物根解析失败（不设其他位置兜底）: {_e}"}
    if not os.path.isdir(temp_dir):
        defect, hint = "缺失", _workspace_source_hint()
    elif not os.access(temp_dir, os.W_OK):
        defect, hint = "不可写", ""
    else:
        return {"status": "ok", "path": temp_dir}
    return {"status": "warn", "path": temp_dir,
            "reason": f"{hint}{RUNTIME_DIR_NAME} 目录{defect}"}
def maint_health_check() -> dict:
    checks = _run_sub_checks(
        (
            ("skills_dir", _check_skills_dir),
            ("state_dir", _check_state_dir),
            ("version", _check_version),
            ("runtime", _check_runtime),
            ("log_channel", _check_log_channel),
            ("state_files", _check_state_files),
            ("workspace_temp", _check_workspace_temp),
        ),
        degrade_status="warn", payload_key="reason", log_label="maint")
    all_ok = all(v.get("status") == "ok" for v in checks.values())
    result = {"status": "ok" if all_ok else "degraded", "checks": checks}
    if all_ok:
        logger.info("maint_health_check: status=%s", result["status"])
    else:
        _degraded = {k: v.get("reason", v.get("status"))
                     for k, v in checks.items() if v.get("status") != "ok"}
        logger.warning("maint_health_check: status=%s, degraded=%s", result["status"], _degraded)
    return result
def run_health(base: Any = None) -> dict:
    result = maint_health_check()
    result["system_health"] = _safe_section(
        "系统健康自检", lambda: HealthStatus().check())
    result["runtime_vitals"] = _safe_section(
        "运行时体征", HealthVital.capture)
    all_green = (
        result["status"] == "ok"
        and result["system_health"].get("status") == "healthy"
        and result["runtime_vitals"].get("status") == "ok"
    )
    if not all_green:
        result["status"] = "degraded"
    if base:
        result["base"] = str(base)
    return result
def _safe_section(label: str, collect: Callable[[], dict[str, Any]]) -> dict[str, Any]:
    try:
        return collect()
    except Exception as e:
        logger.warning("run_health: %s失败: %s", label, e)
        return {"status": "error", "error": str(e)[:200]}
def _vital_error(ts: float, e: BaseException) -> dict[str, Any]:
    return {"timestamp": ts, "status": "error", "error": str(e)[:200]}
class HealthVital:
    @classmethod
    def is_available(cls) -> bool:
        return hasattr(_psutil, "cpu_percent")
    @classmethod
    def capture(cls) -> dict[str, Any]:
        ts = time.time()
        if not cls.is_available():
            logger.warning(
                "psutil 不可用，健康体征采集降级（补装：python -m %s deps --install）",
                _PACKAGE_NAME)
            return {
                "timestamp": ts,
                "status": "error",
                "error": f"psutil 不可用: 运行 python -m {_PACKAGE_NAME} deps --install 补装",
            }
        psutil_error = getattr(_psutil, "Error", None)
        except_bases: tuple[type, ...] = (OSError, RuntimeError, AttributeError)
        if isinstance(psutil_error, type) and issubclass(psutil_error, BaseException):
            except_bases = (*except_bases, psutil_error)
        try:
            cpu_percent = _psutil.cpu_percent(interval=0.1)
            mem = _psutil.virtual_memory()
            return {
                "timestamp": ts,
                "status": "ok",
                "cpu_percent": cpu_percent,
                "memory_percent": mem.percent,
                "memory_available_mb": round(mem.available / (1024 * 1024), 1),
                "memory_total_mb": round(mem.total / (1024 * 1024), 1),
                "process_count": len(_psutil.pids()),
            }
        except Exception as e:
            logger.warning("健康体征采集失败%s: %s",
                         "" if isinstance(e, except_bases)
                         else "（契约外形态，降级）", e)
            return _vital_error(ts, e)
_IMPORT_LINE_RE = re.compile(
    r"^[ \t]*(?:from[ \t]+([.\w]+)[ \t]+import[ \t]+(\([^)]*\)|[^\n(]+)"
    r"|import[ \t]+([\w., \t]+))",
    re.MULTILINE,
)
_STR_MODULE_REF_RE = re.compile(r"['\"]([A-Za-z_]\w*)\.(\w+)")
_STR_BARE_MODULE_REF_RE = re.compile(
    r"['\"]([A-Za-z_]\w*)(?::[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)?['\"]")
def _string_module_refs(text: str, package_name: str,
                        known_modules: frozenset[str] | None = None) -> set[str]:
    refs = {match.group(2) for match in _STR_MODULE_REF_RE.finditer(text)
            if match.group(1) == package_name}
    if known_modules:
        refs.update(match.group(1)
                    for match in _STR_BARE_MODULE_REF_RE.finditer(text)
                    if match.group(1) in known_modules)
    return refs
def _reference_prune_dirs(pkg_dir: Path) -> set[str]:
    return set(scan_exclude_dirs(pkg_dir)) - TEST_ARTIFACT_DIRS
def _iter_reference_sources(pkg_dir: Path) -> Iterator[tuple[Path, str]]:
    skip = _reference_prune_dirs(pkg_dir)
    for dirpath, dirs, files in os.walk(pkg_dir):
        dirs[:] = [d for d in dirs if not is_pruned_scan_dir(d, skip)]
        for name in files:
            if not is_scan_py_name(name):
                continue
            try:
                source = read_source_interpreter_encoding(
                    os.path.join(dirpath, name))
            except (OSError, UnicodeError, LookupError, SyntaxError) as exc:
                logger.debug("[SelfCheck] 引用扫描跳过不可读文件 %s: %s",
                             name, exc)
                continue
            yield Path(dirpath) / name, source
def _add_module_ref(refs: set[str], mod: str, package_name: str) -> None:
    if package_name and mod.startswith(package_name + "."):
        refs.add(mod[len(package_name) + 1:].split(".")[0])
    elif mod and mod != package_name:
        refs.add(mod.split(".")[0])
def _import_name_items(names: str) -> list[str]:
    uncommented = "\n".join(
        line.split("#", 1)[0] for line in names.splitlines())
    body = uncommented.replace("(", " ").replace(")", " ")
    items = (re.split(r"\s+as\s+", item.strip(), maxsplit=1)[0].strip()
             for item in body.split(","))
    return [item for item in items if item]
def _collect_import_refs(
    text: str, refs: set[str], package_name: str, *,
    relative_parent_parts: tuple[str, ...] = (),
) -> None:
    logical_text = re.sub(r"\\(?:\r\n|\n|\r)", "", text)
    for match in _IMPORT_LINE_RE.finditer(logical_text):
        src, names, plain = match.groups()
        if src:
            level = len(src) - len(src.lstrip("."))
            module = src.lstrip(".")
            if level:
                ancestor_depth = level - 1
                if ancestor_depth > len(relative_parent_parts):
                    continue
                base_parts = relative_parent_parts[
                    :len(relative_parent_parts) - ancestor_depth]
                qualified = (*base_parts, *module.split(".")) if module else base_parts
                if qualified:
                    refs.add(qualified[0])
                else:
                    refs.update(_import_name_items(names))
                continue
            _add_module_ref(refs, module, package_name)
            if not module or src == package_name:
                refs.update(_import_name_items(names))
        elif plain:
            for item in _import_name_items(plain):
                _add_module_ref(refs, item, package_name)
def _referenced_root_modules(
    pkg_dir: Path,
    package_name: str | None = None,
    known_modules: frozenset[str] | None = None,
) -> set[str]:
    package = package_name or Path(pkg_dir).name
    refs: set[str] = set()
    for source_path, text in _iter_reference_sources(pkg_dir):
        parent_parts = source_path.relative_to(pkg_dir).parent.parts
        _collect_import_refs(
            text, refs, package, relative_parent_parts=parent_parts)
        refs.update(_string_module_refs(text, package, known_modules))
    return refs
class HealthStatus:
    CORE_MODULES: tuple[str, ...] = ()
    def __init__(self, package_dir: str | os.PathLike | None = None,
                 package_name: str | None = None,
                 core_modules: Iterable[str] | None = None) -> None:
        self._findings: list[dict[str, Any]] = []
        self._package_dir = (_PACKAGE_DIR if package_dir is None
                             else Path(package_dir))
        self._package_name = (package_name or _PACKAGE_NAME
                              if package_dir is None
                              else package_name or self._package_dir.name)
        if core_modules is None and package_dir is not None:
            _facades, core_modules = _discover_entry_modules(
                self._package_dir, self._package_name)
        self._core_modules = (
            (core_modules,) if isinstance(core_modules, str)
            else tuple(core_modules) if core_modules is not None else None
        )
    def check(self) -> dict[str, Any]:
        self._findings = []
        checks = _run_sub_checks(
            (
                ("import_chain", self._check_import_chain),
                ("pycache", self._check_pycache),
            ),
            degrade_status="critical", payload_key="error",
            log_label="HealthStatus")
        critical_count = sum(1 for c in checks.values() if c.get("status") == "critical")
        regressed_count = sum(1 for c in checks.values() if c.get("status") == "regressed")
        if critical_count > 0:
            overall = "critical"
        elif regressed_count > 0:
            overall = "regressed"
        else:
            overall = "healthy"
        return {
            "status": overall,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "checks": checks,
            "findings": self._findings,
        }
    def _check_import_chain(self) -> dict[str, Any]:
        modules = (self.CORE_MODULES if self._core_modules is None
                   else self._core_modules)
        with _package_search_path(
                self._package_dir if self._core_modules is not None else None):
            results = {}
            for mod in modules:
                try:
                    importlib.import_module(mod)
                except (Exception, SystemExit) as exc:  # noqa: BLE001
                    _swallow('_check_import_chain', exc)
                    results[mod] = False
                else:
                    results[mod] = True
        self._findings.extend(
            {"type": "import_missing", "severity": "critical",
             "module": mod}
            for mod, ok in results.items() if not ok)
        return {
            "status": "healthy" if all(results.values()) else "critical",
            "modules": results}
    def _check_pycache(self) -> dict[str, Any]:
        pycache = self._package_dir / "__pycache__"
        py_count = len(list(self._package_dir.glob("*.py")))
        pyc_files = list(pycache.glob("*.pyc")) if pycache.exists() else []
        pyc_count = len(pyc_files)
        ratio = pyc_count / max(py_count, 1)
        findings: list[str] = []
        findings += self._pycache_ratio_findings(py_count, pyc_files, ratio)
        findings += self._pycache_partial_findings()
        findings += self._analysis_dir_findings()
        findings += self._sibling_backup_findings()
        findings += self._orphan_root_module_findings()
        return {
            "status": "regressed" if findings else "healthy",
            "py_files": py_count,
            "pyc_files": pyc_count,
            "ratio": round(ratio, 2),
            "findings": findings,
        }
    def _pycache_ratio_findings(self, py_count: int, pyc_files: list,
                                ratio: float) -> list[str]:
        orphans = sorted(
            p.name for p in pyc_files
            if not (self._package_dir / f"{p.name.split('.')[0]}.py").is_file())
        if not (orphans or ratio > 3):
            return []
        self._findings.append({
            "type": "pycache_ratio",
            "severity": "medium",
            "py_files": py_count,
            "pyc_files": len(pyc_files),
            "ratio": round(ratio, 2),
            "orphans": orphans[:10],
        })
        return ["pycache_ratio"]
    def _iter_pycache_dirs(self) -> Iterator[Path]:
        skip = scan_exclude_dirs(self._package_dir)
        for dirpath, dirs, _files in os.walk(self._package_dir):
            dirs[:] = [d for d in dirs if d == "__pycache__"
                       or not is_pruned_scan_dir(d, skip)]
            path = Path(dirpath)
            if path.name == "__pycache__":
                yield path
                dirs[:] = []
    def _pycache_partial_findings(self) -> list[str]:
        try:
            partial = sorted(
                p.name for d in self._iter_pycache_dirs()
                for p in d.glob("*.pyc.*") if p.is_file())
        except OSError as exc:
            _swallow('_pycache_partial_findings', exc)
            return []
        if not partial:
            return []
        self._findings.append({
            "type": "pycache_partial_write",
            "severity": "medium",
            "count": len(partial),
            "samples": partial[:5],
        })
        return ["pycache_partial_write"]
    def _analysis_dir_findings(self) -> list[str]:
        analysis_dir = self._package_dir / ".analysis"
        if not analysis_dir.exists():
            return []
        self._findings.append({
            "type": "unregistered_analysis_dir",
            "severity": "medium",
            "path": os.fspath(analysis_dir),
        })
        return ["unregistered_analysis_dir"]
    def _sibling_backup_findings(self) -> list[str]:
        if not (self._package_dir / "SKILL.md").is_file():
            return []
        try:
            siblings = sorted(
                p.name for p in self._package_dir.parent.iterdir()
                if p.is_dir() and is_backup_snapshot_dir(p.name))
        except OSError as exc:
            _swallow('_sibling_backup_findings', exc)
            return []
        if not siblings:
            return []
        self._findings.append({
            "type": "sibling_backup_skill",
            "severity": "medium",
            "count": len(siblings),
            "samples": siblings[:5],
        })
        return ["sibling_backup_skill"]
    def _orphan_root_module_findings(self) -> list[str]:
        root_modules = {p.stem for p in self._package_dir.glob("*.py")} - {
            "__init__", "__main__"}
        if not root_modules:
            return []
        orphans = sorted(
            root_modules - _referenced_root_modules(
                self._package_dir, package_name=self._package_name,
                known_modules=frozenset(root_modules)))
        if not orphans:
            return []
        self._findings.append({
            "type": "orphan_root_module",
            "severity": "medium",
            "count": len(orphans),
            "samples": orphans[:5],
            "hint": "根级模块无任何 import/字符串引用；拆分或迁移的"
                    "中间片段应删除，不要留在包根",
        })
        return ["orphan_root_module"]
_FACADE_MODULES, _CORE_MODULES = _discover_entry_modules()
HealthStatus.CORE_MODULES = _CORE_MODULES
def _norm_case_path(path: str) -> str:
    return os.path.normcase(os.path.abspath(path))
def _paths_differ(path_a: str, path_b: str) -> bool:
    if not isinstance(path_a, str) or not isinstance(path_b, str):
        return False
    return (
        _norm_case_path(path_a) != _norm_case_path(path_b)
        and os.path.normcase(os.path.realpath(path_a)) != os.path.normcase(os.path.realpath(path_b))
    )
def _path_has_segment(path: str, expected: str) -> bool:
    parts = [os.path.normcase(p) for p in path.replace("\\", "/").split("/")
             if p]
    expected_parts = [os.path.normcase(p)
                      for p in expected.replace("\\", "/").split("/") if p]
    if not expected_parts:
        return False
    width = len(expected_parts)
    return any(parts[i:i + width] == expected_parts
               for i in range(len(parts) - width + 1))
def list_shadow_packages() -> list[dict[str, str]]:
    shadows = []
    try:
        _cwd = os.getcwd()
    except OSError as exc:
        logger.warning(
            "[SelfCheck] 当前工作目录不可解析，空 sys.path 条目按不可模拟跳过: %s", exc)
        _cwd = None
    for name, mod in list(sys.modules.items()):
        abs_mf = _shadow_probe_path(name, mod)
        if abs_mf is None:
            continue
        first_hit = _first_hit_candidate(name, _cwd)
        if first_hit is not None and _paths_differ(first_hit, abs_mf):
            shadows.append({
                "name": name,
                "loaded_from": abs_mf,
                "also_exists_at": first_hit,
            })
    return sorted(shadows, key=lambda item: item.get("name", ""))
def _shadow_probe_path(name: object, mod: object) -> str | None:
    if not isinstance(name, str) or not name:
        return None
    if name == "__main__":
        return None
    mf = getattr(mod, "__file__", None)
    if not isinstance(mf, str) or not mf:
        return None
    if not os.path.normcase(mf).endswith(".py"):
        return None
    return os.path.abspath(mf)
def _candidate_paths(name: str, base: str) -> Iterator[str]:
    alt = os.path.join(base, *name.split("."))
    yield os.path.join(alt, "__init__.py")
    yield alt + ".py"
def _first_hit_candidate(name: str, cwd: str | None) -> str | None:
    for p in sys.path:
        if not isinstance(p, str):
            continue
        base = p or cwd
        if base is None or not os.path.isdir(base):
            continue
        for alt_candidate in _candidate_paths(name, base):
            if os.path.isfile(alt_candidate):
                return alt_candidate
    return None
def _exec_module_with_family_rollback(pkg_name: str, spec, correct_mod) -> None:
    prefix = pkg_name + "."
    parent_name, _, child_attr = pkg_name.rpartition(".")
    parent_mod = sys.modules.get(parent_name) if parent_name else None
    missing_attr = object()
    parent_binding = (getattr(parent_mod, child_attr, missing_attr)
                      if parent_mod is not None else missing_attr)
    saved = {name: mod for name, mod in sys.modules.items()
             if name == pkg_name or name.startswith(prefix)}
    for name in saved:
        sys.modules.pop(name, None)
    sys.modules[pkg_name] = correct_mod
    try:
        spec.loader.exec_module(correct_mod)
        if parent_mod is not None:
            setattr(parent_mod, child_attr, correct_mod)
    except BaseException:
        for name in tuple(sys.modules):
            if name == pkg_name or name.startswith(prefix):
                sys.modules.pop(name, None)
        sys.modules.update(saved)
        if parent_mod is not None:
            if parent_binding is missing_attr:
                try:
                    delattr(parent_mod, child_attr)
                except AttributeError as _rollback_exc:
                    _swallow('_exec_module_with_family_rollback:delattr',
                             _rollback_exc)
            else:
                setattr(parent_mod, child_attr, parent_binding)
        raise
def _fix_shadowed_module(pkg_name: str, resolved: str) -> None:
    try:
        is_pkg = os.path.basename(resolved) == "__init__.py"
        spec = importlib.util.spec_from_file_location(
            pkg_name, resolved,
            submodule_search_locations=(
                [os.path.dirname(resolved)] if is_pkg else None),
        )
        if spec is None or spec.loader is None:
            logger.warning("[path_guard] 无法为 %s 构建加载规格: %s", pkg_name, resolved)
            return
        correct_mod = importlib.util.module_from_spec(spec)
        _exec_module_with_family_rollback(pkg_name, spec, correct_mod)
        logger.warning("[path_guard] 已重载 %s → %s", pkg_name, resolved)
    except (Exception, SystemExit) as e:
        logger.warning("[path_guard] 重载 %s 失败，保留原模块: %s", pkg_name, e)
def _restore_sys_path(p, path_added):
    if path_added:
        try:
            sys.path.remove(p)
        except ValueError:
            logger.debug("已被移除:%s", p)
_FALSE_FLAG_TOKENS = frozenset({"", "0", "false", "no", "off", "none", "null"})
def _flag_enabled(value: Any, *, default: bool) -> bool:
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() not in _FALSE_FLAG_TOKENS
    if isinstance(value, (int, float)):
        return value != 0
    return bool(value)
def _is_path_arg(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())
def _guard_package_origin(pkg_name: str, resolved: str,
                          expected_parent_dir: str, auto_fix: bool) -> bool:
    if not os.path.isfile(resolved):
        logger.warning("[path_guard] Package file not found: %s", resolved)
        return False
    if not _path_has_segment(resolved, expected_parent_dir):
        logger.critical(
            "[path_guard] Shadow package detected: file=%s, expected_parent=%s not in path",
            resolved, expected_parent_dir)
        return False
    if pkg_name not in sys.modules:
        return True
    existing = sys.modules[pkg_name]
    existing_file = getattr(existing, "__file__", None)
    origin_mismatch = (
        not isinstance(existing_file, str) or not existing_file
        or _paths_differ(existing_file, resolved))
    if not origin_mismatch:
        return True
    logger.warning(
        "[path_guard] sys.modules[%r] points to %r (expected %s)",
        pkg_name, existing_file, resolved)
    if not auto_fix:
        return False
    _fix_shadowed_module(pkg_name, resolved)
    current = getattr(sys.modules.get(pkg_name), "__file__", None)
    return (isinstance(current, str) and bool(current)
            and not _paths_differ(current, resolved))
def guard_package(package_file: str, expected_parent_dir: str, auto_fix: bool = True) -> bool:
    if not (_is_path_arg(package_file) and _is_path_arg(expected_parent_dir)):
        logger.warning(
            "[path_guard] 非 str/空路径入参，按来源不合法拒绝: file=%r, expected_parent=%r",
            package_file, expected_parent_dir)
        return False
    resolved = os.path.abspath(package_file)
    pkg_name = os.path.basename(os.path.dirname(resolved))
    return _guard_package_origin(
        pkg_name, resolved, expected_parent_dir,
        _flag_enabled(auto_fix, default=True))
def _qualified_subpackage_name(parent_file: str, parent_dir: str,
                               subpackage_name: str) -> str:
    for name, loaded in list(sys.modules.items()):
        loaded_file = getattr(loaded, "__file__", None)
        if (isinstance(name, str) and name and isinstance(loaded_file, str)
                and loaded_file and not _paths_differ(loaded_file, parent_file)):
            return f"{name}.{subpackage_name}"
    path = Path(parent_dir)
    parts = [path.name]
    ancestor = path.parent
    while (ancestor / "__init__.py").is_file():
        parts.append(ancestor.name)
        ancestor = ancestor.parent
    return ".".join((*reversed(parts), subpackage_name))
def guard_subpackage(parent_file: str, subpackage_name: str, expected_system: str) -> bool:
    if not (_is_path_arg(parent_file) and _is_path_arg(subpackage_name)
            and _is_path_arg(expected_system)):
        logger.warning(
            "[path_guard] 非 str/空路径入参，按来源不合法拒绝: parent=%r, sub=%r, expected=%r",
            parent_file, subpackage_name, expected_system)
        return False
    if not subpackage_name.isidentifier():
        logger.warning(
            "[path_guard] 子包名不是单一合法标识符，拒绝越界解析: %r",
            subpackage_name)
        return False
    parent_dir = os.path.dirname(os.path.abspath(parent_file))
    sub_dir = os.path.join(parent_dir, subpackage_name)
    if not os.path.isdir(sub_dir):
        logger.warning("[path_guard] Subpackage directory not found: %s", sub_dir)
        return False
    dotted_name = _qualified_subpackage_name(
        os.path.abspath(parent_file), parent_dir, subpackage_name)
    init_path = os.path.join(sub_dir, "__init__.py")
    if os.path.exists(init_path):
        return _guard_package_origin(
            dotted_name, os.path.abspath(init_path), expected_system, False)
    resolved = os.path.abspath(sub_dir)
    if not _path_has_segment(resolved, expected_system):
        logger.warning(
            "[path_guard] Shadow subpackage detected: dir=%s, expected_parent=%s not in path",
            resolved, expected_system
        )
        return False
    if dotted_name not in sys.modules:
        return True
    loaded = sys.modules[dotted_name]
    try:
        search_paths = list(getattr(loaded, "__path__", ()))
    except Exception as exc:  # noqa: BLE001
        _swallow("guard_subpackage:namespace_path", exc)
        search_paths = []
    for candidate in search_paths:
        try:
            candidate_path = os.fspath(candidate)
        except TypeError:
            continue
        if (isinstance(candidate_path, str) and candidate_path
                and not _paths_differ(candidate_path, resolved)):
            return True
    logger.warning(
        "[path_guard] Loaded namespace subpackage has wrong search path: "
        "name=%s, expected=%s, actual=%r",
        dotted_name, resolved, search_paths,
    )
    return False
def dedup_path_insert(path: str, index: int = 0) -> bool:
    if not _is_path_arg(path):
        logger.warning("dedup_path_insert: 非 str/空白路径入参，忽略插入: %r", path)
        return False
    if not isinstance(index, int) or isinstance(index, bool):
        logger.warning("dedup_path_insert: 非 int 插入位置，回退 0: %r", index)
        index = 0
    resolved = os.path.abspath(path)
    normalized = _norm_case_path(path)
    for existing in sys.path:
        try:
            existing_normalized = _norm_case_path(existing)
        except (OSError, ValueError, TypeError) as e:
            logger.warning("[Utils] sys.path entry 规范化失败，跳过: %r (%s)", existing, e)
            continue
        if existing_normalized == normalized:
            logger.debug("dedup_path_insert: path already exists, skipping: %s", path)
            return False
    sys.path.insert(index, resolved)
    logger.debug("dedup_path_insert: inserted path at index %d: %s", index, resolved)
    return True
def _pip_available() -> bool:
    try:
        return shutil.which("pip") is not None or shutil.which("pip3") is not None
    except Exception as _e:
        _swallow('_pip_available', _e)
        return False
def get_platform_info() -> dict[str, str]:
    return {
        "os": sys.platform,
        "python": f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
        "pip_available": str(_pip_available() or spec_exists("pip")),
    }
def check_dependencies(required_packages: list[str]) -> dict[str, bool]:
    if not isinstance(required_packages, (list, tuple, set, frozenset)):
        logger.warning(
            "check_dependencies: 非 iterable 入参，按空清单处理: %r",
            required_packages)
        return {}
    result: dict[str, bool] = {}
    for pkg in required_packages:
        if not isinstance(pkg, str):
            logger.warning(
                "check_dependencies: 非 str 包名元素，跳过: %r", pkg)
            continue
        result[pkg] = module_available(pkg)
    return result
_PACKAGE_SEARCH_PATH_LOCK = threading.RLock()
@contextmanager
def _package_search_path(package_dir: str | os.PathLike | None):
    if package_dir is None:
        yield
        return
    with _PACKAGE_SEARCH_PATH_LOCK:
        parent = os.fspath(Path(package_dir).resolve().parent)
        path_added = dedup_path_insert(parent)
        try:
            yield
        finally:
            _restore_sys_path(parent, path_added)
def _probe_facades(facade_modules=None,
                   package_name: str | None = None,
                   package_dir: str | os.PathLike | None = None
                   ) -> dict[str, tuple[bool, str]]:
    package = package_name or _PACKAGE_NAME
    modules = _module_names(facade_modules, package)
    status: dict[str, tuple[bool, str]] = {}
    with _package_search_path(package_dir):
        for name in modules:
            dotted = f"{package}.{name}"
            import_name = package if name == "__init__" else dotted
            try:
                importlib.import_module(import_name)  # lazy-by-design
                status[dotted] = (True, "")
            except (Exception, SystemExit) as exc:
                _swallow('_probe_facades', exc)
                status[dotted] = (False, f"{type(exc).__name__}: {exc}")
    return status
def _audit_facade_manifest(skill_dir: str | None = None,
                           facade_modules=None,
                           package_name: str | None = None) -> dict:
    if skill_dir is None:
        skill_dir = os.fspath(_PACKAGE_DIR)
    modules = _module_names(
        facade_modules, package_name or _PACKAGE_NAME, deduplicate=False)
    missing_files = []
    duplicates = []
    seen: set[str] = set()
    for name in modules:
        if name in seen and name not in duplicates:
            duplicates.append(name)
        seen.add(name)
        module_present = _module_present(Path(skill_dir), name)
        if not module_present and name not in missing_files:
            missing_files.append(name)
    return {
        "listed": len(modules),
        "missing_files": missing_files,
        "duplicates": duplicates,
    }
@dataclass(frozen=True)
class _SelfCheckTarget:
    skill_root: Path
    package_dir: Path
    package_name: str
    label: str
    facade_modules: Any
    external: bool
    is_package: bool
def _resolve_self_check_target(skill_dir: str | os.PathLike | None,
                               skill_name: str | None,
                               facade_modules) -> _SelfCheckTarget:
    if skill_dir is None:
        return _SelfCheckTarget(
            _PACKAGE_DIR, _PACKAGE_DIR, _PACKAGE_NAME,
            skill_name or _PACKAGE_DIR.name,
            _FACADE_MODULES if facade_modules is None else facade_modules,
            False, True)
    raw_dir = os.fspath(skill_dir)
    if (not isinstance(raw_dir, str) or not raw_dir.strip()
            or not os.path.isdir(raw_dir)):
        raise ValueError(f"技能目录不存在或参数非法: {skill_dir!r}")
    skill_root = Path(raw_dir).resolve()
    layout = detect_layout(raw_dir)
    package_dir = Path(layout.package_root or raw_dir).resolve()
    package_name = layout.package_name or package_dir.name
    modules = facade_modules
    if modules is None:
        modules = (_discover_entry_modules(package_dir, package_name)[0]
                   if layout.is_package else ())
    return _SelfCheckTarget(
        skill_root, package_dir, package_name, skill_name or package_name,
        modules, True, layout.is_package)
def quick_self_check(skip_facades: bool = False,
                     skill_name: str | None = None,
                     facade_modules=None,
                     dependencies=None,
                     skill_dir: str | os.PathLike | None = None) -> dict:
    target = _resolve_self_check_target(
        skill_dir, skill_name, facade_modules)
    skip_facades = _flag_enabled(skip_facades, default=False)
    report: dict = {
        "skill": target.label,
        "skill_dir": os.fspath(target.skill_root),
        "checked_at": time.strftime("%Y-%m-%d %H:%M:%S"),
    }
    report["python_version"] = ".".join(str(x) for x in sys.version_info[:3])
    report["python_required"] = ">=" + ".".join(str(x) for x in MIN_PYTHON)
    report["python_ok"] = sys.version_info >= MIN_PYTHON
    facades_failed = _collect_facade_status(
        report, skip_facades, facade_modules,
        target if target.external else None)
    report["facades_failed"] = facades_failed
    if target.external:
        manifest = _audit_facade_manifest(
            os.fspath(target.package_dir), target.facade_modules,
            target.package_name)
    else:
        manifest = (_audit_facade_manifest() if facade_modules is None
                    else _audit_facade_manifest(
                        facade_modules=facade_modules,
                        package_name=target.package_name))
    report["facades_manifest"] = manifest
    dependency_input = (
        RUNTIME_DEPS if dependencies is None and not target.external
        else () if dependencies is None else dependencies)
    deps = check_dependencies(dependency_input)
    report["dependencies"] = deps
    report["dependencies_missing"] = [k for k, v in deps.items() if not v]
    report["environment"] = get_platform_info()
    shadow = list_shadow_packages()
    report["shadow_packages"] = shadow
    report["shadow_count"] = len(shadow)
    if not target.external:
        report["package_origin_ok"] = _check_package_origin()
    elif target.is_package:
        report["package_origin_ok"] = _check_package_origin(
            target.package_dir, target.package_name)
    else:
        report["package_origin_ok"] = None
    _finalize_health_summary(report, facades_failed, shadow, manifest, skip_facades)
    return report
def _collect_facade_status(report: dict, skip_facades: bool,
                           facade_modules,
                           target: _SelfCheckTarget | None = None) -> list[str]:
    if skip_facades:
        return []
    if target is not None:
        facades = _probe_facades(
            target.facade_modules, target.package_name, target.package_dir)
    else:
        facades = (_probe_facades() if facade_modules is None
                   else _probe_facades(facade_modules))
    report["facades"] = {
        name: {"ok": ok, "error": err} for name, (ok, err) in facades.items()
    }
    return [name for name, (ok, _err) in facades.items() if not ok]
def _unloaded_package_origin(package_dir: Path, package_name: str) -> str | None:
    with _package_search_path(package_dir):
        try:
            spec = importlib.util.find_spec(package_name)
        except Exception as exc:
            _swallow('_unloaded_package_origin', exc)
            return None
    return getattr(spec, "origin", None)
def _namespace_search_path_matches(search_paths: Any, package_dir: Path) -> bool:
    try:
        candidates = list(search_paths) if search_paths is not None else []
    except Exception as exc:  # noqa: BLE001
        _swallow("_namespace_search_path_matches", exc)
        return False
    expected = os.fspath(package_dir)
    for candidate in candidates:
        try:
            candidate_path = os.fspath(candidate)
        except TypeError:
            continue
        if (isinstance(candidate_path, str) and candidate_path
                and not _paths_differ(candidate_path, expected)):
            return True
    return False
def _check_namespace_package_origin(package_dir: Path, package_name: str) -> bool:
    if package_name in sys.modules:
        loaded = sys.modules[package_name]
        search_paths = (None if getattr(loaded, "__file__", None)
                        else getattr(loaded, "__path__", None))
    else:
        with _package_search_path(package_dir):
            try:
                spec = importlib.util.find_spec(package_name)
            except Exception as exc:  # noqa: BLE001
                _swallow("_check_namespace_package_origin", exc)
                spec = None
        search_paths = (
            getattr(spec, "submodule_search_locations", None)
            if spec is not None and getattr(spec, "origin", None) is None
            else None)
    origin_ok = _namespace_search_path_matches(search_paths, package_dir)
    if not origin_ok:
        logger.warning(
            "[SelfCheck] 命名空间包来源对账失败: sys.modules[%s].__path__ 或 "
            "find_spec 搜索路径不包含磁盘目录 %s", package_name, package_dir)
    return origin_ok
def _check_package_origin(package_dir: str | os.PathLike | None = None,
                          package_name: str | None = None) -> bool:
    root = _PACKAGE_DIR if package_dir is None else Path(package_dir)
    package = _PACKAGE_NAME if package_name is None else package_name
    pkg_file = os.fspath(root / "__init__.py")
    if package_dir is not None and not os.path.isfile(pkg_file):
        return _check_namespace_package_origin(root, package)
    origin_ok = _guard_package_origin(
        package, os.path.abspath(pkg_file), root.parent.name, False)
    if package in sys.modules:
        loaded_file = getattr(sys.modules.get(package), "__file__", None)
    else:
        loaded_file = _unloaded_package_origin(root, package)
    if not isinstance(loaded_file, str) or _paths_differ(loaded_file, pkg_file):
        origin_ok = False
        logger.warning(
            "[SelfCheck] 包来源对账失败: sys.modules[%s].__file__=%r, 磁盘=%s",
            package, loaded_file, pkg_file)
    return origin_ok
def _health_ok(report: dict, facades_failed: list[str],
               shadow: list[dict], manifest: dict) -> bool:
    return bool(report["python_ok"] and not facades_failed
                and not manifest["missing_files"]
                and not manifest.get("duplicates")
                and not report.get("dependencies_missing")
                and not shadow and report["package_origin_ok"] is not False)
def _facade_summary_part(report: dict, facades_failed: list[str],
                         skip_facades: bool) -> str:
    if skip_facades:
        return "facades=skipped"
    probed = len(report.get("facades", {}))
    return f"facades={probed - len(facades_failed)}/{probed} ok"
def _manifest_summary_part(manifest: dict) -> str:
    issues = [f"{key.removesuffix('_files')}:{','.join(manifest[key])}"
              for key in ("missing_files", "duplicates") if manifest.get(key)]
    return "manifest=" + (",".join(issues) if issues else "ok")
def _origin_summary_part(report: dict) -> str:
    origin = report["package_origin_ok"]
    return "n/a" if origin is None else "ok" if origin else "FAIL"
def _finalize_health_summary(report: dict, facades_failed: list[str],
                             shadow: list[dict], manifest: dict,
                             skip_facades: bool) -> None:
    report["ok"] = _health_ok(report, facades_failed, shadow, manifest)
    facades_part = _facade_summary_part(report, facades_failed, skip_facades)
    manifest_part = _manifest_summary_part(manifest)
    parts = [
        f"python={report['python_version']}({'ok' if report['python_ok'] else 'FAIL'})",
        facades_part,
        manifest_part,
        f"deps_missing={report['dependencies_missing'] or '无'}",
        f"shadow={len(shadow)}",
        f"origin={_origin_summary_part(report)}",
    ]
    report["summary"] = ("自健康检查通过: " if report["ok"] else "自健康检查失败: ") + ", ".join(parts)
    if not report["ok"]:
        logger.warning("[SelfCheck] %s", report["summary"])
    else:
        logger.info("[SelfCheck] %s", report["summary"])
