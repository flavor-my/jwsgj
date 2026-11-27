from __future__ import annotations

import ast
import logging
import os
import re
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field, replace
from typing import Any

from jwsgj.diag_shared_ast_nodes import ast_name
from jwsgj.diag_shared_ast_views import shared_walk
from jwsgj.diag_shared_source_core import byte_col_to_char_col
from jwsgj.diag_testing_scan_ast import (
    _BUILTINS_MODULE_NAMES,
    _CMD_OWNER_MODULES,
    _CTYPES_FFI_ATTRS,
    _DESER_LOAD_ATTRS,
    _EVAL_EXEC_NAMES,
    _HARDCODED_CREDENTIAL_PATTERNS,
    _YAML_LOAD_FUNCS,
    SHELL_CALL_ATTRS,
    YAML_LOAD_FAMILY,
    ImportBinds,
    ScopeIndex,
    _call_name_is_shadowed,
    _invalid_ast_entries,
    _invalid_ast_result,
    _line_join_has_taint,
    _matches_taint_source,
    _path_join_tainted,
    _scan_text,
    entry_source_lines,
    has_safe_loader,
    has_shell_true_kw,
    line_suppressed_at,
)
from jwsgj.diag_testing_source import entry_nodes, resolve_file_cache
from jwsgj.diag_types_defs import TestMethodResult
from jwsgj.runtime_scope import is_test_file_path
from jwsgj.skill_profile import SkillProfileError, resolve_skill_profile

__all__ = ["run_sca"]
_log = logging.getLogger(__name__)
_log.addHandler(logging.NullHandler())
_log.info("diag_testing_scan_sca 已加载：%d 项导出", len(__all__))
_VERSION_OP_RE = re.compile(r'(===|==|>=|<=|~=|!=|>|<)')
_DEFAULT_REQUIREMENTS_SOURCE = 'requirements.txt'
_DEPENDENCY_NAME_SEP_RE = re.compile(r'[-_.]+')
def _dependency_key(name: str) -> str:
    return _DEPENDENCY_NAME_SEP_RE.sub('-', name).lower()
@dataclass
class _RequirementsScan:
    declared_deps: list[str]
    unpinned_deps: list[str]
    dep_versions: dict[str, set[str]]
    dep_first_line: dict[str, int]
    dep_source: dict[str, str] = field(default_factory=dict)
    manifest_issues: list[dict] = field(default_factory=list)
@dataclass(frozen=True)
class _RequirementLine:
    dep_name: str
    line: str
    unpinned: bool
    eq_vers: set[str]
    conditional: bool
def _record_dependency_manifest_issue(
        scan: _RequirementsScan, source: str, line: int,
        message: str) -> None:
    scan.manifest_issues.append({
        "file": source, "line": line, "dependency": "dependency_manifest",
        "severity": "high", "message": message,
    })
def _sca_self_kernel(skill_dir: str) -> frozenset[str]:
    try:
        return resolve_skill_profile(skill_dir).sca_self_kernel
    except (SkillProfileError, OSError, ValueError) as _swallowed_exc:
        _log.debug("_sca_self_kernel: 技能画像解析降级: %s",
                   _swallowed_exc, exc_info=True)
        return frozenset()
def _register_requirement(parsed: _RequirementLine, lineno: int,
                         scan: _RequirementsScan,
                         source: str = _DEFAULT_REQUIREMENTS_SOURCE) -> None:
    scan.declared_deps.append(parsed.dep_name)
    _key = _dependency_key(parsed.dep_name)
    scan.dep_first_line.setdefault(_key, lineno)
    scan.dep_source.setdefault(_key, source)
    if parsed.unpinned:
        scan.unpinned_deps.append(parsed.line)
    if parsed.eq_vers and not parsed.conditional:
        scan.dep_versions[_key].update(parsed.eq_vers)
_REQUIREMENT_INCLUDE_RE = re.compile(
    r'^(?:(?:-r|--requirement)(?:[ \t]*=[ \t]*|[ \t]+)(.+?)'
    r'|-r(\S.*?))[ \t]*$',
    re.IGNORECASE)
def _requirement_include(raw_line: str) -> str | None:
    line = re.sub(r'(^|\s)#.*', '', raw_line).strip()
    match = _REQUIREMENT_INCLUDE_RE.fullmatch(line)
    if match is None:
        return None
    target = (match.group(1) or match.group(2)).strip()
    if (len(target) >= 2 and target[0] == target[-1]
            and target[0] in ('"', "'")):
        target = target[1:-1].strip()
    return target or None
def _parse_requirements(req_file: str) -> _RequirementsScan:
    scan = _RequirementsScan([], [], defaultdict(set), {})
    _parse_requirements_into(req_file, scan, set())
    return scan
def _parse_requirements_into(req_file: str, scan: _RequirementsScan,
                             visited: set[str]) -> None:
    normalized = os.path.normcase(os.path.realpath(req_file))
    if normalized in visited or not os.path.isfile(req_file):
        return
    visited.add(normalized)
    try:
        with open(req_file, encoding='utf-8') as f:
            content = f.read().removeprefix('\ufeff')
            for lineno, raw_line in enumerate(content.splitlines(), 1):
                include = _requirement_include(raw_line)
                if include is not None:
                    include_path = (include if os.path.isabs(include) else
                                    os.path.join(os.path.dirname(req_file), include))
                    if not os.path.isfile(include_path):
                        _record_dependency_manifest_issue(
                            scan, os.path.basename(req_file), lineno,
                            f"依赖清单包含文件不存在: {include}")
                        continue
                    _parse_requirements_into(include_path, scan, visited)
                    continue
                parsed = _parse_requirement_line(raw_line)
                if parsed is not None:
                    _register_requirement(
                        parsed, lineno, scan,
                        os.path.basename(req_file) or _DEFAULT_REQUIREMENTS_SOURCE)
    except (OSError, UnicodeDecodeError) as e:
        _log.debug("_parse_requirements: requirements read error: %s",
                   e, exc_info=True)
        _record_dependency_manifest_issue(
            scan, os.path.basename(req_file), 0,
            f"依赖清单读取失败: {type(e).__name__}")
def _load_toml_module():
    try:
        import tomllib  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    except ImportError:
        try:
            import tomli as tomllib  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
        except ImportError:
            return None
    return tomllib
def _read_manifest(
        path: str, scan: _RequirementsScan | None = None) -> str:
    try:
        with open(path, encoding='utf-8') as fh:
            return fh.read().removeprefix('\ufeff')
    except (OSError, UnicodeDecodeError) as e:
        _log.debug("_read_manifest: manifest read error: %s", e, exc_info=True)
        if scan is not None:
            _record_dependency_manifest_issue(
                scan, os.path.basename(path), 0,
                f"依赖清单读取失败: {type(e).__name__}")
        return ""
def _manifest_line(text: str, dep_name: str) -> int:
    pattern = re.compile(
        rf'(^|[\s"\']){"".join(re.escape(ch) for ch in dep_name)}(?![\w.-])',
        re.IGNORECASE)
    for lineno, line in enumerate(text.splitlines(), 1):
        if pattern.search(line):
            return lineno
    return 0
def _add_requirement_text(scan: _RequirementsScan, spec: str, source: str,
                          line_text: str, *, conditional: bool = False) -> None:
    parsed = _parse_requirement_line(spec)
    if parsed is None:
        return
    lineno = _manifest_line(line_text, parsed.dep_name)
    _register_requirement(
        replace(parsed, conditional=parsed.conditional or conditional),
        lineno, scan, source)
def _poetry_pin_versions(version: str) -> set[str]:
    if version.startswith("=="):
        return {version[2:].strip()}
    if version[:1].isdigit() and "*" not in version:
        return {version}
    return set()
def _add_poetry_dep(scan: _RequirementsScan, name: str, spec, source: str,
                    line_text: str) -> None:
    direct_reference = (isinstance(spec, dict) and any(
        spec.get(key) for key in ("path", "git", "url", "file")))
    version = spec.get("version", "") if isinstance(spec, dict) else (
        spec if isinstance(spec, str) else "")
    version = str(version or "").strip()
    if version == "*":
        version = ""
    eq_vers = _poetry_pin_versions(version)
    conditional = isinstance(spec, dict) and bool(spec.get("markers"))
    _register_requirement(
        _RequirementLine(name, f"{name}{version}",
                         not version and not direct_reference,
                         eq_vers, conditional),
        _manifest_line(line_text, name), scan, source)
def _dependency_spec_strings(value) -> tuple[str, ...]:
    if not isinstance(value, (list, tuple)):
        return ()
    return tuple(spec for spec in value if isinstance(spec, str))
def _parse_pyproject_requirements(scan: _RequirementsScan, path: str) -> None:
    toml = _load_toml_module()
    text = _read_manifest(path, scan)
    if not text:
        return
    if toml is None:
        _record_dependency_manifest_issue(
            scan, "pyproject.toml", 0, "缺少 TOML 解析器，无法读取依赖清单")
        return
    try:
        data = toml.loads(text)
    except (ValueError, RecursionError) as e:
        _record_dependency_manifest_issue(
            scan, "pyproject.toml", 0,
            f"依赖清单解析失败: {type(e).__name__}")
        return
    project = data.get("project") if isinstance(data, dict) else None
    if isinstance(project, dict):
        for spec in _dependency_spec_strings(project.get("dependencies")):
            _add_requirement_text(scan, spec, "pyproject.toml", text)
        extras = project.get("optional-dependencies")
        if isinstance(extras, dict):
            for group in extras.values():
                for spec in _dependency_spec_strings(group):
                    _add_requirement_text(
                        scan, spec, "pyproject.toml", text)
    dependency_groups = data.get("dependency-groups")
    if isinstance(dependency_groups, dict):
        for group in dependency_groups.values():
            for spec in _dependency_spec_strings(group):
                _add_requirement_text(
                    scan, spec, "pyproject.toml", text)
    tool = data.get("tool") if isinstance(data, dict) else None
    poetry = tool.get("poetry") if isinstance(tool, dict) else None
    if not isinstance(poetry, dict):
        return
    tables = [poetry.get("dependencies") or {}]
    groups = poetry.get("group")
    for group in (groups.values() if isinstance(groups, dict) else ()):
        if isinstance(group, dict):
            tables.append(group.get("dependencies") or {})
    for table in tables:
        if not isinstance(table, dict):
            continue
        for name, spec in table.items():
            if str(name).lower() != "python":
                _add_poetry_dep(scan, str(name), spec,
                                "pyproject.toml", text)
def _parse_setup_cfg_requirements(scan: _RequirementsScan, path: str) -> None:
    import configparser  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    text = _read_manifest(path, scan)
    if not text:
        return
    parser = configparser.ConfigParser(interpolation=None, strict=False)
    try:
        parser.read_string(text)
    except (configparser.Error, ValueError) as e:
        _record_dependency_manifest_issue(
            scan, "setup.cfg", 0,
            f"依赖清单解析失败: {type(e).__name__}")
        return
    blocks = [parser.get("options", "install_requires", fallback="")]
    if parser.has_section("options.extras_require"):
        blocks.extend(value for _key, value in
                      parser.items("options.extras_require"))
    for block in blocks:
        for spec in (block or "").splitlines():
            if spec.strip() and not spec.strip().startswith("#"):
                _add_requirement_text(
                    scan, spec, "setup.cfg", text)
def _parse_pipfile_requirements(scan: _RequirementsScan, path: str) -> None:
    toml = _load_toml_module()
    text = _read_manifest(path, scan)
    if not text:
        return
    if toml is None:
        _record_dependency_manifest_issue(
            scan, "Pipfile", 0, "缺少 TOML 解析器，无法读取依赖清单")
        return
    try:
        data = toml.loads(text)
    except (ValueError, RecursionError) as e:
        _record_dependency_manifest_issue(
            scan, "Pipfile", 0,
            f"依赖清单解析失败: {type(e).__name__}")
        return
    if not isinstance(data, dict):
        return
    for section in ("packages", "dev-packages"):
        table = data.get(section)
        if isinstance(table, dict):
            for name, spec in table.items():
                _add_poetry_dep(scan, str(name), spec, "Pipfile", text)
def _declared_requirements(skill_dir: str) -> _RequirementsScan:
    scan = _parse_requirements(
        os.path.join(skill_dir, _DEFAULT_REQUIREMENTS_SOURCE))
    for fname, parser in (
            ("pyproject.toml", _parse_pyproject_requirements),
            ("setup.cfg", _parse_setup_cfg_requirements),
            ("Pipfile", _parse_pipfile_requirements)):
        path = os.path.join(skill_dir, fname)
        if os.path.isfile(path):
            parser(scan, path)
    unique_deps: list[str] = []
    seen_deps: set[str] = set()
    for dep in scan.declared_deps:
        key = _dependency_key(dep)
        if key not in seen_deps:
            seen_deps.add(key)
            unique_deps.append(dep)
    scan.declared_deps[:] = unique_deps
    unique_unpinned: list[str] = []
    seen_unpinned: set[str] = set()
    for line in scan.unpinned_deps:
        parsed = _parse_requirement_line(line)
        key = _dependency_key(parsed.dep_name) if parsed is not None else line
        if key not in seen_unpinned:
            seen_unpinned.add(key)
            unique_unpinned.append(line)
    scan.unpinned_deps[:] = unique_unpinned
    return scan
def _parse_requirement_line(raw_line: str) -> _RequirementLine | None:
    line = re.sub(r'(^|\s)#.*', '', raw_line).strip()
    if not line or line.startswith('-'):
        return None
    base = line.split(';', 1)[0].strip()
    _at_parts = base.split('@', 1)
    _is_direct_ref = len(_at_parts) > 1
    base = _at_parts[0].strip()
    base = base.replace('(', ' ').replace(')', ' ').strip()
    dep_name = _VERSION_OP_RE.split(base)[0].strip()
    dep_name = dep_name.split('[')[0].strip()
    if (not dep_name or '://' in dep_name or '+' in dep_name
            or ':' in dep_name or '/' in dep_name or '\\' in dep_name):
        return None
    unpinned = (not _VERSION_OP_RE.search(base)
                and not _is_direct_ref)
    eq_vers = _parse_eq_versions(base)
    return _RequirementLine(dep_name=dep_name, line=line, unpinned=unpinned,
                            eq_vers=eq_vers, conditional=';' in line)
def _parse_eq_versions(base: str) -> set:
    eq_vers: set = set()
    _spec_split = _VERSION_OP_RE.split(base, maxsplit=1)
    if len(_spec_split) == 3:
        for _con in (_spec_split[1] + _spec_split[2]).split(','):
            _con_m = re.match(
                r'^(===|==|>=|<=|~=|!=|>|<)\s*([^\s,]+)',
                _con.strip())
            if (_con_m and _con_m.group(1) in ('==', '===')
                    and '*' not in _con_m.group(2)):
                eq_vers.add(_con_m.group(2))
    return eq_vers
_SCA_FINDINGS_LIMIT = 50
def run_sca(skill_dir: str, **kwargs) -> TestMethodResult:  # jwsgj:suppress shell
    start = time.perf_counter()
    result = TestMethodResult(method_name="软件成分分析", method_id="sca")
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "软件成分分析", "sca", "扫描", start)
    invalid_entries = _invalid_ast_entries(cache)
    if invalid_entries:
        return _invalid_ast_result(result, invalid_entries, start)
    req = _declared_requirements(skill_dir)
    is_self_scan = _is_self_scan(skill_dir)
    self_kernel = _sca_self_kernel(skill_dir) if is_self_scan else frozenset()
    dependencies, vulnerabilities, entries = _execute_sca_scans(
        cache, is_self_scan, self_kernel)
    vulnerabilities[:0] = req.manifest_issues
    _sca_collect_version_conflicts(
        req.dep_versions, req.dep_first_line, vulnerabilities,
        req.dep_source)
    skill_name = os.path.basename(os.path.abspath(skill_dir))
    local_modules = _local_top_level_modules(entries, dependencies)
    third_party = _third_party_deps(dependencies, skill_name, local_modules)
    undeclared_deps = (set() if req.manifest_issues else
                       _sca_collect_undeclared_imports(
                           entries, third_party, req.declared_deps,
                           vulnerabilities))
    _metrics = _dependency_metrics(
        dependencies, req.declared_deps, req.unpinned_deps, third_party)
    _metrics["undeclared_imports"] = len(undeclared_deps)
    _metrics["dependency_manifest_errors"] = len(req.manifest_issues)
    if req.manifest_issues:
        _metrics["undeclared_imports_suppressed"] = True
    result.metrics = {**_metrics, **_vuln_metrics(vulnerabilities)}
    result.findings = vulnerabilities[:_SCA_FINDINGS_LIMIT]
    high_count = result.metrics["high_severity"]
    result.status, result.score = _sca_grade(high_count, len(vulnerabilities))
    result.summary = (
        f"扫描 {len(dependencies)} 个依赖, "
        f"{len(vulnerabilities)} 个风险项 ({high_count} 高危)")
    truncated = len(vulnerabilities) - len(result.findings)
    if truncated > 0:
        result.metrics["findings_truncated"] = truncated
        result.summary += f"，findings 仅保留前 {_SCA_FINDINGS_LIMIT} 条"
    result.finish(start)
    return result
def _is_self_scan(skill_dir: str) -> bool:
    self_root = os.path.dirname(os.path.abspath(__file__))
    return (os.path.realpath(os.path.abspath(skill_dir))
            == os.path.realpath(self_root))
def _execute_sca_scans(cache, is_self_scan: bool,
                       self_kernel: frozenset[str]) -> tuple[dict, list, list]:
    dependencies: dict[str, list[str]] = defaultdict(list)
    vulnerabilities: list = []
    entries = [entry for entry in cache.valid_entries
               if _is_sca_target(entry, self_kernel)]
    indexes = {id(entry): ScopeIndex(entry.tree) for entry in entries}
    _sca_scan_entries(entries, is_self_scan, dependencies, vulnerabilities,
                      indexes)
    sca_scan_weak_hash(entries, vulnerabilities, indexes)
    sca_scan_tempfile_xml(entries, vulnerabilities, indexes)
    return dependencies, vulnerabilities, entries
def _is_sca_target(entry, self_kernel: frozenset[str]) -> bool:
    rel_path = getattr(entry, 'rel_path', '') or ''
    if is_test_file_path(rel_path):
        return False
    return os.path.basename(rel_path.replace('\\', '/')) not in self_kernel
def _sca_scan_entries(entries, is_self_scan: bool, dependencies: dict,
                      vulnerabilities: list,
                      indexes: dict[int, ScopeIndex]) -> None:
    for entry in entries:
        source_lines = entry_source_lines(entry)
        index = scope_index_for(entry, indexes)
        sca_scan_ast(entry.tree, entry.rel_path, source_lines, dependencies,
                     vulnerabilities, index)
        scan_text = _scan_text(entry.source, mask_strings=is_self_scan)
        sca_scan_regex(scan_text, RegexScanContext(
            source_lines=source_lines,
            rel_path=entry.rel_path,
            vulnerabilities=vulnerabilities,
            has_taint_source=_matches_taint_source(scan_text),
            scope_by_line=scope_line_index(entry.tree),
            tree=entry.tree))
def _sca_collect_version_conflicts(dep_versions: dict, dep_first_line: dict,
                                   vulnerabilities: list,
                                   dep_source: dict | None = None) -> None:
    for dep, versions in dep_versions.items():
        if len(versions) > 1:
            vulnerabilities.append({
                "file": (dep_source or {}).get(
                    dep, _DEFAULT_REQUIREMENTS_SOURCE),
                "line": dep_first_line.get(dep, 0),
                "dependency": "version_conflict", "severity": "high",
                "message": f"依赖 {dep} 有多个版本声明: {sorted(versions)}"})
_PACKAGE_IMPORT_ALIASES: dict[str, str] = {
    'pyyaml': 'yaml',
    'z3-solver': 'z3',
    'pillow': 'PIL',
    'beautifulsoup4': 'bs4',
    'python-dateutil': 'dateutil',
    'scikit-learn': 'sklearn',
    'opencv-python': 'cv2',
    'opencv-python-headless': 'cv2',
    'python-docx': 'docx',
    'python-pptx': 'pptx',
    'python-multipart': 'multipart',
    'msgpack-python': 'msgpack',
    'pyserial': 'serial',
    'pyzmq': 'zmq',
    'ruamel.yaml': 'ruamel',
    'google-api-python-client': 'googleapiclient',
    'grpcio': 'grpc',
}
# 单分发包提供多个顶层模块：只按一个包名做别名，会把同包内的兄弟模块
# 判成「未声明的第三方依赖」（pywin32 就提供 pythoncom/win32com/win32gui/
# win32ui/pywintypes 一整套）。这里按分发名登记全部顶层模块。
_MULTI_MODULE_DISTRIBUTIONS: dict[str, tuple[str, ...]] = {
    'pywin32': ('pythoncom', 'pywintypes', 'win32com', 'win32api',
                'win32con', 'win32event', 'win32file', 'win32gui',
                'win32process', 'win32ui'),
}
def _declared_module_names(declared_deps: list) -> set[str]:
    names: set[str] = set()
    declared_keys: set[str] = set()
    for dep in declared_deps:
        key = _dependency_key(dep)
        declared_keys.add(key)
        lower = dep.lower()
        names.update((lower, lower.partition('.')[0], key,
                      key.replace('-', '_')))
    for package, module in _PACKAGE_IMPORT_ALIASES.items():
        if _dependency_key(package) in declared_keys:
            names.add(module.lower())
    for package, modules in _MULTI_MODULE_DISTRIBUTIONS.items():
        if _dependency_key(package) in declared_keys:
            names.update(module.lower() for module in modules)
    return names
def _local_top_level_modules(entries: list,
                             imported_tops=()) -> set[str]:
    tops = {str(name) for name in imported_tops if name}
    modules: set[str] = set()
    for entry in entries:
        rel = (getattr(entry, 'rel_path', '') or '').replace('\\', '/')
        rel = rel.strip('/')
        if not rel.endswith('.py'):
            continue
        parts = rel[:-3].split('/')
        if not parts:
            continue
        # 模块名（文件干）也要算本地模块：双模式技能会把 ``scripts/`` 直接挂到
        # sys.path，此时 ``import _shared`` / ``from cad_bridge import ...``
        # 引用的是**文件干**而不是顶层目录名。只按 parts[0] 判定会把项目自身的
        # 每个模块都误报成「未声明的第三方依赖」。
        stem = parts[-1]
        if stem != '__init__' and stem in tops:
            modules.add(stem)
        candidates = set(parts[:2]) if parts[0] == 'src' else {parts[0]}
        modules.update(candidate for candidate in candidates
                       if candidate != '__init__' and candidate in tops)
    return modules
_STDLIB_MODULES = frozenset(sys.stdlib_module_names)
def _third_party_deps(dependencies: dict, skill_name: str,
                      local_modules=None) -> dict[str, list[str]]:
    stdlib_modules = _STDLIB_MODULES
    local = set(local_modules or ())
    own_keys = {_dependency_key(skill_name)} if skill_name else set()
    return {dep: files for dep, files in dependencies.items()
            if dep not in stdlib_modules
            and _dependency_key(dep) not in own_keys and dep not in local}
def _import_dep_lines(node: ast.AST) -> list[tuple[str, int]]:
    if isinstance(node, ast.Import):
        return [
            (alias.name.split('.')[0],
             getattr(alias, 'lineno', node.lineno) or node.lineno)
            for alias in node.names
        ]
    if (isinstance(node, ast.ImportFrom) and node.module
            and not node.level):
        return [(node.module.split('.')[0], node.lineno)]
    return []
def _sca_collect_undeclared_imports(entries, third_party: dict,
                                    declared_deps: list,
                                    vulnerabilities: list) -> set[str]:
    declared = _declared_module_names(declared_deps)
    pending = {dep for dep in third_party if dep.lower() not in declared}
    reported: set[str] = set()
    if not pending:
        return reported
    for entry in entries:
        tree = getattr(entry, 'tree', None)
        if tree is None:
            continue
        rel_path = getattr(entry, 'rel_path', '') or ''
        source_lines = entry_source_lines(entry)
        for node in shared_walk(tree):
            for dep, line in _import_dep_lines(node):
                if dep not in pending:
                    continue
                if line_suppressed_at(line, source_lines,
                                      _import_suppression_kind(dep)):
                    continue
                pending.discard(dep)
                reported.add(dep)
                vulnerabilities.append(_vuln(
                    rel_path, line, "undeclared_import", "medium",
                    f"第三方依赖 {dep} 未在依赖清单（requirements/pyproject）中声明"))
                if not pending:
                    return reported
    return reported
def _dependency_metrics(dependencies: dict, declared_deps: list,
                        unpinned_deps: list,
                        third_party: dict) -> dict:
    return {
        "total_dependencies": len(dependencies),
        "third_party_count": len(third_party),
        "stdlib_count": sum(1 for dep in dependencies
                            if dep in _STDLIB_MODULES),
        "declared_requirements": len(declared_deps),
        "unpinned_deps": len(unpinned_deps),
    }
def _vuln_metrics(vulnerabilities: list) -> dict:
    _sev = Counter(v["severity"] for v in vulnerabilities)
    _dep = Counter(v.get("dependency", "unknown") for v in vulnerabilities)
    return {
        "vulnerability_count": len(vulnerabilities),
        "high_severity": _sev.get("high", 0),
        "medium_severity": _sev.get("medium", 0),
        "low_severity": _sev.get("low", 0),
        "weak_hash_usage": _dep.get("weak_hash", 0),
        "insecure_tempfile": _dep.get("insecure_tempfile", 0),
        "insecure_xml": _dep.get("insecure_xml", 0),
        "version_conflicts": _dep.get("version_conflict", 0),
        "vulnerability_categories": dict(_dep),
    }
def _sca_grade(high_count: int, vuln_count: int) -> tuple[str, int]:
    if high_count == 0 and vuln_count <= 3:
        return "pass", (90 if vuln_count else 100)
    if high_count <= 2:
        return "warn", 60
    return "warn", 20
_RISK_CATALOG: dict[str, tuple[str, str]] = {
    "pickle": ("high", "pickle 反序列化可导致任意代码执行"),
    "marshal": ("high", "marshal.loads 可执行任意代码"),
    "shelve": ("low", "shelve 基于 pickle，存在反序列化风险"),
    "yaml.load": ("high", "yaml.load 未指定 Loader 可导致任意对象构造"),
    "ssl._create_unverified_context": ("high", "SSL 证书验证被禁用"),
    "os.system": ("medium", "命令执行调用，需确保输入安全"),
    "subprocess.shell": ("high", "subprocess shell=True 可导致命令注入"),
    "ctypes": ("high", "ctypes FFI 调用可绕过 Python 安全机制"),
    "eval": ("high", "eval() 调用可执行任意代码"),  # jwsgj:suppress eval
    "exec": ("high", "exec() 调用可执行任意代码"),  # jwsgj:suppress exec
    "ssrf": ("medium", "疑似 SSRF: URL 包含动态拼接"),
    "weak_hash": ("medium", "弱哈希算法不应用于安全场景"),
    "insecure_tempfile": ("medium", "不安全临时文件操作"),
    "insecure_xml": ("low", "xml.etree.ElementTree 未防 XXE，建议使用 defusedxml"),
}
_IMPORT_RISK_NAMES = frozenset({'pickle', 'marshal', 'shelve'})
_SQL_PATTERNS = [
    re.compile(r'f["\']\s*(?:SELECT|INSERT|UPDATE|DELETE|DROP)\s+.*(?:WHERE|VALUES|SET)\s*.*\{[^}]+\}.*["\']', re.IGNORECASE),
    re.compile(r'["\'](?:SELECT|INSERT|UPDATE|DELETE)\b[^"\']*["\']\s*\+', re.IGNORECASE),
    re.compile(r'["\'](?:SELECT|INSERT|UPDATE|DELETE)\b[^"\']*["\']\s*%', re.IGNORECASE),
]
_LOG_LEVEL_TOKENS = frozenset({
    'debug', 'info', 'warning', 'warn', 'error', 'exception', 'critical',
    'fatal', 'log', 'trace',
})
_LOG_NAME_TOKENS = frozenset({'log', 'logger', 'logging'})
_PRINT_CALLABLES = frozenset({'print', 'pprint', 'pp', 'cprint'})
_CALL_NAME_RE = re.compile(r'(?<![\w.])([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)\s*\(')
_LOG_METHOD_CALL_RE = re.compile(
    r'\.\s*(?:' + '|'.join(sorted(_LOG_LEVEL_TOKENS)) + r')\s*\(')
def _call_name_tokens(name: str) -> list[str]:
    return [tok.lower() for tok in re.split(r'[._]', name) if tok]
def _is_log_statement_line(line: str) -> bool:
    if _LOG_METHOD_CALL_RE.search(line):
        return True
    for match in _CALL_NAME_RE.finditer(line):
        tokens = _call_name_tokens(match.group(1))
        if not tokens:
            continue
        if len(tokens) == 1 and tokens[0] in _PRINT_CALLABLES:
            return True
        if len(tokens) == 1 and tokens[0] in _LOG_NAME_TOKENS:
            return True
        if (tokens[-1] in _LOG_LEVEL_TOKENS
                and any(tok in _LOG_NAME_TOKENS for tok in tokens[:-1])):
            return True
    return False
_CMD_INJECTION_PATTERNS = [
    re.compile(r'os\.popen\s*\(\s*f["\']', re.IGNORECASE),
    re.compile(r'os\.exec(?:le|lpe|ve|vpe)\s*\(\s*(?:[^()+]|\([^()]*\))*\+', re.IGNORECASE),  # jwsgj:suppress exec
]
_HTTP_URL_METHODS = frozenset({
    'get', 'post', 'put', 'delete', 'head', 'patch', 'options',
})
_SSRF_CALLS = {
    'urllib.request': frozenset({'urlopen'}),
    'requests': _HTTP_URL_METHODS,
    'httpx': _HTTP_URL_METHODS,
}
_XXE_PATTERNS = [
    re.compile(r'xml\.etree\.ElementTree\.parse\s*\(', re.IGNORECASE),
    re.compile(r'xml\.dom\.minidom\.parse\s*\(', re.IGNORECASE),
    re.compile(r'xml\.sax\.parse\s*\(', re.IGNORECASE),
]
_INSECURE_DESERIAL_PATTERNS = [
    re.compile(r'json\.loads\s*\(.*request', re.IGNORECASE),
    re.compile(r'configparser\.ConfigParser\(\).*read\s*\(.*\+', re.IGNORECASE),
]
_DEBUG_PATTERNS = [
    re.compile(r'(?:app|application|flask|django)\.(?:run|debug)\s*\(.*debug\s*=\s*True', re.IGNORECASE),
    re.compile(r'(?<![\w.])DEBUG\s*=\s*True', re.IGNORECASE),
    re.compile(r'FLASK_DEBUG\s*=\s*["\']?1', re.IGNORECASE),
]
_HARDCODED_ADDR_PATTERNS = [
    re.compile(r'https?://(?:\d{1,3}\.){3}\d{1,3}'),
    re.compile(r'(?:\d{1,3}\.){3}\d{1,3}:\d{2,5}'),
]
_PATH_TRAVERSAL_PATTERNS = [
    re.compile(r'open\s*\(\s*(?:[^()+]|\([^()]*\))*\+\s*.*\)', re.IGNORECASE),
]
@dataclass(frozen=True)
class _CallScanContext:
    rel_path: str
    source_lines: list
    vulnerabilities: list
    binds: ImportBinds
    index: ScopeIndex
def sca_scan_ast(tree: ast.AST, rel_path, source_lines, dependencies,
                 vulnerabilities, index: ScopeIndex) -> None:
    for node in shared_walk(tree):
        if isinstance(node, ast.Import):
            _scan_import_node(node, rel_path, source_lines,
                              dependencies, vulnerabilities)
        elif isinstance(node, ast.ImportFrom) and node.module and not node.level:
            _record_import_risk(node, node.module, rel_path, source_lines,
                                dependencies, vulnerabilities)
        if isinstance(node, ast.Call):
            _sca_check_call(node, _CallScanContext(
                rel_path=rel_path, source_lines=source_lines,
                vulnerabilities=vulnerabilities,
                binds=index.binds_for_call(node), index=index))
def _scan_import_node(node, rel_path, source_lines, dependencies,
                      vulnerabilities) -> None:
    for alias in node.names:
        _record_import_risk(node, alias.name, rel_path, source_lines,
                            dependencies, vulnerabilities)
def _record_import_risk(node, dotted: str, rel_path, source_lines,
                       dependencies, vulnerabilities) -> None:
    dep = dotted.split('.')[0]
    dependencies.setdefault(dep, []).append(rel_path)
    if dep not in _IMPORT_RISK_NAMES:
        return
    if line_suppressed_at(node.lineno, source_lines,
                          _import_suppression_kind(dep)):
        return
    sev, msg = _RISK_CATALOG[dep]
    vulnerabilities.append(_vuln(rel_path, node.lineno, dep, sev, msg))
_IMPORT_SUPPRESSION_KINDS = {
    "pickle": "import_pickle",
    "marshal": "import_marshal",
    "shelve": "import_shelve",
}
def _import_suppression_kind(name: str) -> str:
    return _IMPORT_SUPPRESSION_KINDS.get(name, name)
def _vuln(rel_path: str, line: int, dependency: str,
          severity: str, message: str) -> dict:
    return {"file": rel_path, "line": line, "dependency": dependency,
            "severity": severity, "message": message}
def _emit_risk(ctx, node: ast.AST, name: str,
                message: str | None = None) -> None:
    severity, default_message = _RISK_CATALOG[name]
    if line_suppressed_at(node.lineno, ctx.source_lines, name):
        return
    ctx.vulnerabilities.append(_vuln(
        ctx.rel_path, node.lineno, name, severity,
        message or default_message))
def _attr_owner_in(node: ast.Call, owner_names: set) -> bool:
    return (isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in owner_names)
def _literal_kw_is(call_node: ast.Call, name: str, value: bool) -> bool:
    for kw in call_node.keywords:
        if kw.arg != name or not isinstance(kw.value, ast.Constant):
            continue
        return bool(kw.value.value) is value
    return False
def _attr_os_system_risk(node, func_name, ctx: _CallScanContext) -> None:
    if func_name == "system" and _attr_owner_in(node, ctx.binds.os_names):
        _emit_risk(ctx, node, "os.system")
def _attr_subprocess_shell_risk(node, func_name,
                                ctx: _CallScanContext) -> None:
    if (func_name in SHELL_CALL_ATTRS
            and _attr_owner_in(node, ctx.binds.sp_names)
            and has_shell_true_kw(node)):
        _emit_risk(ctx, node, "subprocess.shell")
def _attr_ctypes_ffi_risk(node, func_name, ctx: _CallScanContext) -> None:
    if (func_name in _CTYPES_FFI_ATTRS
            and _attr_owner_in(node, ctx.binds.ctypes_names)):
        _emit_risk(ctx, node, "ctypes")
def _attr_ssl_unverified_risk(node, func_name, ctx: _CallScanContext) -> None:
    if (func_name == "_create_unverified_context"
            and _attr_owner_in(node, ctx.binds.ssl_names)):
        _emit_risk(ctx, node, "ssl._create_unverified_context")
def _check_bound_name_call_risks(node, func_name,
                                 ctx: _CallScanContext) -> None:
    _bind = ctx.binds.from_binds.get(func_name)
    if _bind is None:
        return
    _mod, _sym = _bind
    if _mod in _CMD_OWNER_MODULES:
        _check_bound_cmd_risks(_mod, _sym, node, ctx)
    elif _mod == 'ctypes':
        _check_bound_ffi_risk(_sym, node, ctx)
    elif _ssrf_module_match(_mod) is not None:
        _check_bound_ssrf_risk(_mod, _sym, node, ctx)
    elif _mod == 'ssl':
        _check_bound_ssl_risk(_sym, node, ctx)
    elif _mod == 'yaml':
        _check_yaml_load_risk(_sym, node, ctx)
def _check_bound_cmd_risks(_mod: str, _sym: str, node,
                           ctx: _CallScanContext) -> None:
    if _mod == 'os' and _sym == 'system':
        _emit_risk(ctx, node, "os.system")
    elif (_mod == 'subprocess' and _sym in SHELL_CALL_ATTRS
            and has_shell_true_kw(node)):
        _emit_risk(ctx, node, "subprocess.shell")
def _check_bound_ffi_risk(_sym: str, node, ctx: _CallScanContext) -> None:
    if _sym in _CTYPES_FFI_ATTRS:
        _emit_risk(ctx, node, "ctypes")
def _check_bound_ssl_risk(_sym: str, node, ctx: _CallScanContext) -> None:
    if _sym == "_create_unverified_context":
        _emit_risk(ctx, node, "ssl._create_unverified_context")
def _ssrf_url_arg(node: ast.Call) -> ast.AST | None:
    return node.args[0] if node.args else next(
        (kw.value for kw in node.keywords if kw.arg == 'url'), None)
def _is_static_url_concat(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return True
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and _is_static_url_concat(node.left)
            and _is_static_url_concat(node.right))
def _is_static_format_value(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, ast.Starred):
        return _is_static_format_value(node.value)
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return all(_is_static_format_value(item) for item in node.elts)
    if isinstance(node, ast.Dict):
        return all(
            (key is None or _is_static_format_value(key))
            and _is_static_format_value(value)
            for key, value in zip(node.keys, node.values))
    return False
def _is_static_url_fstring(node: ast.JoinedStr) -> bool:
    for part in node.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            continue
        if (isinstance(part, ast.FormattedValue)
                and _is_static_format_value(part.value)
                and (part.format_spec is None
                     or _is_static_url_fstring(part.format_spec))):
            continue
        return False
    return True
def _ssrf_url_is_dynamic(node: ast.Call) -> bool:
    url = _ssrf_url_arg(node)
    if isinstance(url, ast.JoinedStr):
        return not _is_static_url_fstring(url)
    if isinstance(url, ast.BinOp):
        if isinstance(url.op, ast.Add):
            return not _is_static_url_concat(url)
        if isinstance(url.op, ast.Mod):
            return not (_is_static_url_concat(url.left)
                        and _is_static_format_value(url.right))
    if (isinstance(url, ast.Call)
            and isinstance(url.func, ast.Attribute)
            and url.func.attr == 'format'):
        return not (_is_static_url_concat(url.func.value)
                    and all(_is_static_format_value(arg) for arg in url.args)
                    and all(_is_static_format_value(kw.value)
                            for kw in url.keywords))
    return False
def _ssrf_module_match(module: str) -> str | None:
    for known in _SSRF_CALLS:
        if module == known or module.startswith(f"{known}."):
            return known
    return None
def _check_bound_ssrf_risk(_mod: str, _sym: str, node,
                           ctx: _CallScanContext) -> None:
    risk_module = _ssrf_module_match(_mod)
    if (risk_module is not None and _sym in _SSRF_CALLS[risk_module]
            and _ssrf_url_is_dynamic(node)):
        _emit_risk(ctx, node, "ssrf")
def _ssrf_owner_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        owner = _ssrf_owner_name(node.value)
        return f"{owner}.{node.attr}" if owner else ""
    return ""
def _attr_ssrf_owner_matches(node: ast.Call, owner: str, module: str,
                             ctx: _CallScanContext) -> bool:
    if (owner == module
            or owner in ctx.index.module_aliases_for_call(node, module)):
        return True
    root, *suffix = owner.split('.')
    binding = ctx.binds.from_binds.get(root)
    if binding is not None:
        resolved = '.'.join((binding[0], binding[1], *suffix))
        if _ssrf_module_match(resolved) == module:
            return True
    parts = module.split('.')
    for cut in range(1, len(parts) + 1):
        prefix = '.'.join(parts[:cut])
        if root not in ctx.index.module_aliases_for_call(node, prefix):
            continue
        resolved = '.'.join([prefix, *suffix])
        if _ssrf_module_match(resolved) == module:
            return True
    return False
def _attr_ssrf_risk(node: ast.Call, func_name: str,
                    ctx: _CallScanContext) -> None:
    if not isinstance(node.func, ast.Attribute):
        return
    owner = _ssrf_owner_name(node.func.value)
    if not owner or not _ssrf_url_is_dynamic(node):
        return
    if ctx.index._name_is_shadowed(
            node, owner.split('.', 1)[0], False):
        return
    for module, symbols in _SSRF_CALLS.items():
        if func_name not in symbols:
            continue
        if _attr_ssrf_owner_matches(node, owner, module, ctx):
            _emit_risk(ctx, node, "ssrf")
            return
def _check_yaml_load_risk(_sym: str, node, ctx: _CallScanContext) -> None:
    if _sym not in YAML_LOAD_FAMILY:
        return
    if _sym in _YAML_LOAD_FUNCS and has_safe_loader(
            node, ctx.binds, ctx.index):
        return
    _emit_risk(ctx, node, "yaml.load")
def _check_module_deser_risk(node, func_name: str, ctx: _CallScanContext,
                             module: str, module_names: set[str]) -> None:
    if (func_name in _DESER_LOAD_ATTRS
            and _attr_owner_in(node, module_names)):
        _emit_risk(ctx, node, module)
def _check_bound_deser_risk(node, func_name: str,
                            ctx: _CallScanContext) -> None:
    if not isinstance(node.func, ast.Name):
        return
    binding = ctx.binds.from_binds.get(func_name)
    if binding is None:
        return
    module, symbol = binding
    if module in ("pickle", "marshal") and symbol in _DESER_LOAD_ATTRS:
        _emit_risk(ctx, node, module)
def _check_yaml_call_risk(node, func_name, ctx: _CallScanContext) -> None:
    if not _attr_owner_in(node, ctx.binds.yaml_names):
        return
    _check_yaml_load_risk(func_name, node, ctx)
def _eval_exec_source_name(node, func_name: str,
                           ctx: _CallScanContext) -> str | None:
    func = node.func
    if isinstance(func, ast.Attribute):
        if (func.attr in _EVAL_EXEC_NAMES
                and isinstance(func.value, ast.Name)
                and func.value.id in ctx.binds.builtins_names
                and not ctx.index.name_is_shadowed(node, func.value.id)):
            return func.attr
        return None
    if not isinstance(func, ast.Name):
        return None
    binding = ctx.binds.from_binds.get(func_name)
    if binding is None:
        if func_name not in _EVAL_EXEC_NAMES:
            return None
        return None if ctx.index.name_is_shadowed(node, func_name) else func_name
    module, symbol = binding
    if module in _BUILTINS_MODULE_NAMES and symbol in _EVAL_EXEC_NAMES:
        return symbol
    return None
def _check_eval_exec_risk(node, func_name: str,
                          ctx: _CallScanContext) -> None:
    source_name = _eval_exec_source_name(node, func_name, ctx)
    if source_name is not None:
        _emit_risk(ctx, node, source_name)
def _sca_path_join_risk(node: ast.Call, ctx: _CallScanContext) -> None:
    scope = (ctx.index._call_class_scope.get(id(node))
             or ctx.index.scope_of_call(node) or ctx.index._tree)
    if not _path_join_tainted(node, scope, ctx):
        return
    if line_suppressed_at(node.lineno, ctx.source_lines, 'path_traversal'):
        return
    ctx.vulnerabilities.append(_vuln(
        ctx.rel_path, node.lineno, 'path_traversal', 'low',
        '疑似路径穿越: 字符串拼接构建路径'))
def _sca_check_call(node, ctx: _CallScanContext) -> None:
    if _call_name_is_shadowed(node, ctx.index):
        return
    func_name = ast_name(node.func)
    if isinstance(node.func, ast.Attribute):
        _attr_os_system_risk(node, func_name, ctx)
        _attr_subprocess_shell_risk(node, func_name, ctx)
        _attr_ctypes_ffi_risk(node, func_name, ctx)
        _attr_ssl_unverified_risk(node, func_name, ctx)
        _attr_ssrf_risk(node, func_name, ctx)
    _check_eval_exec_risk(node, func_name, ctx)
    if isinstance(node.func, ast.Name):
        _check_bound_name_call_risks(node, func_name, ctx)
    _check_module_deser_risk(
        node, func_name, ctx, "pickle", ctx.binds.pickle_names)
    _check_module_deser_risk(
        node, func_name, ctx, "marshal", ctx.binds.marshal_names)
    _check_bound_deser_risk(node, func_name, ctx)
    _check_yaml_call_risk(node, func_name, ctx)
    _sca_path_join_risk(node, ctx)
_SCA_REGEX_RULES = [
    (_SQL_PATTERNS, "sql_injection", "high", "疑似 SQL 注入: {match}...", "sql"),
    (_PATH_TRAVERSAL_PATTERNS, "path_traversal", "medium", "疑似路径穿越: 字符串拼接构建路径", None),
    (_HARDCODED_CREDENTIAL_PATTERNS, "hardcoded_credential", "high", "疑似硬编码凭据: {match}...", None),
    (_CMD_INJECTION_PATTERNS, "command_injection", "high", "疑似命令注入: {match}...", "cmd"),
    (_XXE_PATTERNS, "xxe", "high", "XML 解析可能存在 XXE 风险", None),
    (_INSECURE_DESERIAL_PATTERNS, "insecure_deserialization", "high", "不安全反序列化: {match}...", None),
    (_DEBUG_PATTERNS, "debug_mode", "medium", "Debug 模式开启: {match}...", None),
    (_HARDCODED_ADDR_PATTERNS, "hardcoded_address", "low", "硬编码网络地址: {match}...", None),
]
_LINE_LEVEL_RULES = frozenset({'hardcoded_address'})
def _iter_rule_matches(scan_source: str):
    for patterns, dep, severity, msg_tmpl, scan_type in _SCA_REGEX_RULES:
        for pattern in patterns:
            for match in pattern.finditer(scan_source):
                yield dep, severity, msg_tmpl, scan_type, match
@dataclass(frozen=True)
class RegexScanContext:
    source_lines: list
    rel_path: str
    vulnerabilities: list
    has_taint_source: bool
    scope_by_line: dict
    tree: ast.AST | None = None
def _sca_rule_message(dep: str, msg_tmpl: str, match) -> str:
    text = match.group()
    if dep == 'hardcoded_credential':
        secret = match.group(1) if match.lastindex else ''
        if secret:
            text = text.replace(secret, '<已脱敏>')
    return msg_tmpl.format(match=text[:50])
def sca_scan_regex(scan_source: str, ctx: RegexScanContext) -> None:
    _stripped_lines = scan_source.split('\n')
    reported: set[tuple[str, int]] = set()
    for dep, severity, msg_tmpl, scan_type, match in _iter_rule_matches(
            scan_source):
        sev = severity
        line_ctx = _regex_match_line_context(
            scan_source, ctx.source_lines, _stripped_lines, match,
            allow_log=dep == 'hardcoded_credential', dep=dep,
            tree=ctx.tree)
        if line_ctx is None:
            continue
        line_num, line_text = line_ctx
        if dep in _LINE_LEVEL_RULES:
            key = (dep, line_num)
            if key in reported:
                continue
            reported.add(key)
        if line_suppressed_at(line_num, ctx.source_lines, dep):
            continue
        if scan_type == "sql" and _sql_match_exempt(match):
            continue
        if dep == "path_traversal":
            skip, sev = _path_traversal_verdict(
                ctx.has_taint_source, ctx.scope_by_line, line_num,
                line_text, severity)
            if skip:
                continue
        msg = _sca_rule_message(dep, msg_tmpl, match)
        ctx.vulnerabilities.append(
            _vuln(ctx.rel_path, line_num, dep, sev, msg))
_REGEX_EXECUTION_CALL_ATTRS = {
    'sql_injection': frozenset({
        'execute', 'executemany', 'executeMany', 'query',
        'fetchone', 'fetchall', 'fetchmany',
    }),
    'path_traversal': frozenset({'open'}),
    'command_injection': frozenset({
        'popen', 'execle', 'execlpe', 'execve', 'execvpe',
    }),
    'insecure_deserialization': frozenset({'loads', 'read'}),
    'xxe': frozenset({'parse'}),
    'debug_mode': frozenset({'run', 'debug'}),
}
def _scan_offset_position(source: str, offset: int) -> tuple[int, int]:
    line_start = source.rfind('\n', 0, offset) + 1
    return source.count('\n', 0, offset) + 1, offset - line_start
def _call_char_span(node: ast.Call, source_lines: list) -> tuple | None:
    start_line = getattr(node, 'lineno', None)
    end_line = getattr(node, 'end_lineno', None)
    if start_line is None or end_line is None:
        return None
    start_col = node.col_offset
    end_col = node.end_col_offset
    if 0 < start_line <= len(source_lines):
        start_col = byte_col_to_char_col(
            source_lines[start_line - 1], start_col)
    if 0 < end_line <= len(source_lines):
        end_col = byte_col_to_char_col(source_lines[end_line - 1], end_col)
    return (start_line, start_col), (end_line, end_col)
def _match_intersects_execution_call(
        tree: ast.AST | None, scan_source: str, source_lines: list,
        match, dep: str) -> bool:
    execution_attrs = _REGEX_EXECUTION_CALL_ATTRS.get(dep, ())
    if tree is None or not execution_attrs:
        return False
    match_start = _scan_offset_position(scan_source, match.start())
    match_end = _scan_offset_position(scan_source, match.end())
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or ast_name(node.func) not in execution_attrs:
            continue
        span = _call_char_span(node, source_lines)
        if span is None:
            continue
        start, end = span
        if start < match_end and match_start < end:
            return True
    return False
def _regex_match_line_context(scan_source, source_lines, stripped_lines,
                               match, *, allow_log: bool = False,
                               dep: str = '', tree: ast.AST | None = None,
                               ) -> tuple[int, str] | None:
    line_num = scan_source[:match.start()].count('\n') + 1
    if line_num > len(source_lines):
        return None
    line_text = source_lines[line_num - 1]
    if line_text.lstrip().startswith('#'):
        return None
    if not allow_log and _is_log_statement_line(stripped_lines[line_num - 1]):
        if tree is None:
            try:
                tree = ast.parse(scan_source)
            except (SyntaxError, ValueError):
                tree = None
        if not _match_intersects_execution_call(
                tree, scan_source, source_lines, match, dep):
            return None
    return line_num, line_text
def _sql_match_exempt(match) -> bool:
    interp_parts = re.findall(r'\{([^}]+)\}', match.group())
    if not interp_parts:
        return False
    return all(_interp_is_literal(part) for part in interp_parts)
def _interp_is_literal(part: str) -> bool:
    text = part.split('!', 1)[0].split(':', 1)[0].strip()
    if not text:
        return False
    try:
        parsed = ast.parse(text, mode='eval').body
    except (SyntaxError, ValueError):  # jwsgj:silent-ok 非合法表达式即谓词否定结果
        return False
    return isinstance(parsed, ast.Constant)
def _path_traversal_verdict(has_taint_source: bool, scope_by_line,
                             line_num: int, line_text: str,
                             severity: str) -> tuple[bool, str]:
    if not has_taint_source:
        return True, severity
    if scope_by_line is not None:
        _fn = scope_by_line.get(line_num)
        if _fn is not None and not _line_join_has_taint(_fn, line_num):
            return True, severity
    return False, severity
@dataclass(frozen=True)
class _EntryScanContext:
    entry: object
    lines: list
    vulnerabilities: list
    @property
    def rel_path(self) -> str:
        return getattr(self.entry, 'rel_path', '') or ''
    @property
    def source_lines(self) -> list:
        return self.lines
def _iter_entry_scan_contexts(entries, vulnerabilities):
    for entry in entries:
        if entry.tree is None:
            continue
        yield entry, _EntryScanContext(
            entry=entry, lines=entry_source_lines(entry),
            vulnerabilities=vulnerabilities)
_WEAK_HASH_FUNCS = frozenset({'md5', 'sha1', 'md4'})
_WEAK_HASH_SYMBOLS = (*sorted(_WEAK_HASH_FUNCS), 'new')
_NON_SECURITY_CONTEXT = frozenset({
    'fingerprint', 'cache', 'id', 'checksum', 'ast', 'index',
})
_WEAK_HASH_SECURITY_KW = (
    'password', 'passwd', 'pwd', 'salt', 'sign', 'auth', 'cert', 'token',
    'secret', 'encrypt', 'decrypt', 'hmac', 'credential', 'api_key', 'apikey',
)
def _check_weak_hash_call(node, ctx: _EntryScanContext,
                          hashlib_names, hash_binds, scope_by_line):
    _sym = _weak_hash_sym(node, hashlib_names, hash_binds)
    if _sym is None or _weak_hash_exempt(node, ctx.lines, scope_by_line):
        return
    _emit_risk(ctx, node, "weak_hash",
               f"弱哈希算法 {_sym}() 不应用于安全场景")
def _weak_hash_sym(node, hashlib_names, hash_binds):
    func = node.func
    if (isinstance(func, ast.Attribute)
            and func.attr in _WEAK_HASH_FUNCS
            and isinstance(func.value, ast.Name)
            and func.value.id in hashlib_names):
        return func.attr
    if (isinstance(func, ast.Name)
            and hash_binds.get(func.id) in _WEAK_HASH_FUNCS):
        return hash_binds[func.id]
    if _is_hashlib_new_call(func, hashlib_names, hash_binds):
        return _hashlib_new_weak_alg(node)
    return None
def _is_hashlib_new_call(func, hashlib_names, hash_binds) -> bool:
    if (isinstance(func, ast.Attribute) and func.attr == 'new'
            and isinstance(func.value, ast.Name)
            and func.value.id in hashlib_names):
        return True
    return isinstance(func, ast.Name) and hash_binds.get(func.id) == 'new'
def _hashlib_new_weak_alg(node) -> str | None:
    arg = node.args[0] if node.args else next(
        (kw.value for kw in node.keywords if kw.arg in ('name', None)), None)
    if not (isinstance(arg, ast.Constant) and isinstance(arg.value, str)):
        return None
    alg = arg.value.lower()
    return alg if alg in _WEAK_HASH_FUNCS else None
def _in_non_security_context(line: str) -> bool:
    lower = line.lower()
    if any(kw in lower for kw in _WEAK_HASH_SECURITY_KW):
        return False
    tokens = frozenset(re.findall(r'[a-z0-9]+', lower))
    return bool(_NON_SECURITY_CONTEXT.intersection(tokens))
def _weak_hash_context_text(line: str, scope_by_line, lineno: int) -> str:
    func_node = scope_by_line.get(lineno) if scope_by_line else None
    _name = getattr(func_node, 'name', '') if func_node is not None else ''
    return f"{line} {_name}" if _name else line
def _weak_hash_exempt(node, lines, scope_by_line) -> bool:
    if _literal_kw_is(node, 'usedforsecurity', False):
        return True
    if line_suppressed_at(node.lineno, lines, "weak_hash"):
        return True
    line = lines[node.lineno - 1] if 1 <= node.lineno <= len(lines) else ""
    return _in_non_security_context(
        _weak_hash_context_text(line, scope_by_line, node.lineno))
def scope_index_for(entry, indexes: dict[int, ScopeIndex]) -> ScopeIndex:
    index = indexes.get(id(entry))
    return index if index is not None else ScopeIndex(entry.tree)
def scope_line_index(tree) -> dict[int, ast.AST]:
    index: dict[int, ast.AST] = {}
    for node in shared_walk(tree):
        lineno = getattr(node, 'lineno', None)
        if lineno is not None:
            index.setdefault(lineno, tree)
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        end = getattr(node, 'end_lineno', None) or node.lineno
        for lineno in range(node.lineno, end + 1):
            index[lineno] = node
    return index
def sca_scan_weak_hash(entries: Any, vulnerabilities,
                       indexes: dict[int, ScopeIndex]) -> None:
    for entry, ctx in _iter_entry_scan_contexts(entries, vulnerabilities):
        _index = scope_index_for(entry, indexes)
        _scope_by_line = scope_line_index(entry.tree)
        for node in entry_nodes(entry):
            if not isinstance(node, ast.Call):
                continue
            if _call_name_is_shadowed(node, _index):
                continue
            _check_weak_hash_call(
                node, ctx,
                _index.module_aliases_for_call(node, 'hashlib'),
                _index.bound_symbols_for_call(
                    node, 'hashlib', _WEAK_HASH_SYMBOLS),
                _scope_by_line)
_INSECURE_TEMPFILE_CALLS = ('mktemp', 'NamedTemporaryFile')
def _check_insecure_tempfile_call(node, ctx: _EntryScanContext,
                                  tf_names, tf_bind_syms) -> None:
    _sym, _from_tempfile = _tempfile_call_source(node, tf_names, tf_bind_syms)
    if not _from_tempfile or _sym not in _INSECURE_TEMPFILE_CALLS:
        return
    if _sym == 'mktemp':
        _emit_risk(ctx, node, "insecure_tempfile",
                   "不安全临时文件操作: mktemp()")
    elif _literal_kw_is(node, 'delete', False):
        _emit_risk(ctx, node, "insecure_tempfile",
                   "不安全临时文件操作: NamedTemporaryFile() delete=False")
def _tempfile_call_source(node, tf_names, tf_bind_syms) -> tuple[str, bool]:
    func_name = ''
    if isinstance(node.func, ast.Name):
        func_name = node.func.id
    elif isinstance(node.func, ast.Attribute):
        func_name = node.func.attr
    _bind_sym = (tf_bind_syms.get(func_name)
                 if isinstance(node.func, ast.Name) else None)
    _sym = _bind_sym or func_name
    _from_tempfile = (
        (isinstance(node.func, ast.Name) and _bind_sym is not None)
        or (isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id in tf_names))
    return _sym, _from_tempfile
def _check_xml_plain_import(node, ctx: _EntryScanContext) -> None:
    if any(a.name == 'xml.etree' or a.name.startswith('xml.etree.')
           for a in node.names):
        _emit_risk(ctx, node, "insecure_xml")
def _check_xml_from_import(node, ctx: _EntryScanContext) -> None:
    from_xml_etree = (node.module == 'xml'
                      and any(a.name == 'etree' for a in node.names))
    if (node.module and not node.level
            and (from_xml_etree or node.module == 'xml.etree'
                 or node.module.startswith('xml.etree.'))):
        _emit_risk(ctx, node, "insecure_xml")
def sca_scan_tempfile_xml(entries: Any, vulnerabilities,
                          indexes: dict[int, ScopeIndex]) -> None:
    for entry, ctx in _iter_entry_scan_contexts(entries, vulnerabilities):
        _index = scope_index_for(entry, indexes)
        for node in entry_nodes(entry):
            if isinstance(node, ast.Call):
                if not _call_name_is_shadowed(node, _index):
                    _check_insecure_tempfile_call(
                        node, ctx,
                        _index.module_aliases_for_call(node, 'tempfile'),
                        _index.bound_symbols_for_call(
                            node, 'tempfile', _INSECURE_TEMPFILE_CALLS))
            elif isinstance(node, ast.Import):
                _check_xml_plain_import(node, ctx)
            elif isinstance(node, ast.ImportFrom):
                _check_xml_from_import(node, ctx)
