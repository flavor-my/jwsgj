from __future__ import annotations

import ast
import asyncio
import builtins
import concurrent.futures
import contextlib
import errno
import functools
import importlib
import importlib.util
import inspect
import io
import os
import sys
import threading
import time
import tokenize
import traceback
import types as _types_mod
from dataclasses import (
    dataclass,
    field,
)
from typing import (
    Any,
    ClassVar,
)
from unittest.mock import (
    DEFAULT,
    MagicMock,
)

from jwsgj.diag_self_check import available_memory_bytes
from jwsgj.diag_shared_source_core import parse_cached, read_source
from jwsgj.diag_types_normalize import normalize_execute_timeout
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import is_path_within_skill
from jwsgj.runtime_scope import (
    prune_scan_dirnames,
    prune_walk_dirs,
    py_stem,
    safe_relpath,
    scan_prune_dirs,
)

logger = get_module_logger(__name__, __file__)
SIM_MODULE_FILE: str = __file__
__all__ = [
    'ApiResponse',
    'ExecutionResult',
    'SandboxExecutor',
    'SimEntryPoint',
    'infer_module_identity',
    'safe_compile',
    'safe_exec',
]
_EXEC_ALLOWED_BUILTINS = {
    "abs", "aiter", "all", "anext", "any", "ascii", "bin",
    "bool", "bytearray", "bytes", "callable",
    "chr", "classmethod", "complex", "delattr", "dict", "dir", "divmod",
    "enumerate", "filter", "float", "format", "frozenset",
    "getattr", "globals", "hasattr", "hash", "hex", "id",
    "int", "isinstance", "issubclass", "iter", "len", "list",
    "locals", "map", "max", "memoryview", "min", "next", "object", "oct",
    "ord", "pow", "print", "property", "range", "repr",
    "reversed", "round", "set", "setattr", "slice", "sorted",
    "staticmethod", "str", "sum", "super", "tuple", "type", "vars",
    "zip", "Exception", "BaseException", "TypeError",
    "ValueError", "RuntimeError", "AttributeError", "KeyError",
    "IndexError", "ImportError", "ModuleNotFoundError", "OSError",
    "StopIteration", "NotImplementedError", "NameError",
    "ZeroDivisionError", "FileNotFoundError", "RecursionError",
    "AssertionError", "SystemExit", "KeyboardInterrupt",
    "exit", "quit",
    "__build_class__",
}
_REAL_IMPORT = builtins.__import__
def _build_exec_builtins() -> dict:
    table = builtins.__dict__
    allowed = {name: table[name]
               for name in _EXEC_ALLOWED_BUILTINS if name in table}
    allowed.update({
        name: value for name, value in table.items()
        if isinstance(value, type) and issubclass(value, BaseException)
    })
    for _name in ("NotImplemented", "Ellipsis"):
        if _name in table:
            allowed[_name] = table[_name]
    return allowed
_EXEC_RESTRICTED_BUILTINS: dict = _build_exec_builtins()
_SAFE_MODULES = frozenset({
    "sys", "os", "io", "re", "json", "math", "time", "datetime",
    "collections", "itertools", "functools", "typing", "abc",
    "ast", "traceback", "warnings", "logging", "copy", "enum",
    "dataclasses", "pathlib", "textwrap", "hashlib", "base64",
    "struct", "random", "string", "threading", "queue",
    "unittest", "inspect", "importlib", "pkgutil", "contextlib",
    "concurrent", "concurrent.futures",
    "asyncio",
    "unicodedata",
    "types", "weakref", "operator", "keyword", "copyreg", "reprlib",
    "gc", "errno",
})
# 默认可加载的「已安装第三方包」黑名单：这些包能直接触达系统副作用
# （子进程、原生句柄、网络监听、COM 自动化），即使已安装也不放进沙箱。
# 判断依据是「包的能力」而非「包名可识别性」：宁可少放行，不可多放行。
_DENY_THIRD_PARTY_MODULES = frozenset({
    "subprocess", "multiprocessing", "ctypes", "socket", "socketserver",
    "shutil", "pty", "tty", "fcntl", "mmap", "resource", "signal",
    "pythoncom", "pywintypes", "win32com", "win32api", "win32con",
    "win32gui", "win32process", "win32event", "win32file", "win32ui",
})
_DEFAULT_ENTRY_TIMEOUT = 30.0
_SANDBOX_SETUP_TIMEOUT = 60.0
_DEFAULT_MEM_GUARD_MB = 1536
_DEFAULT_ENTRY_FILE = ""
_MAX_IMPORT_ROOT_DEPTH = 2
_MODULES_MISSING = object()
_RUNTIME_PROTECTED_MODULES = frozenset({"builtins"})
def _resolve_relative_name(name, globals, level: int) -> str:
    pkg = None
    if isinstance(globals, dict):
        pkg = globals.get("__package__")
        if pkg is None:
            pkg = globals.get("__name__")
            if (isinstance(pkg, str) and pkg
                    and "__path__" not in globals):
                pkg = pkg.rsplit(".", 1)[0]
    if not isinstance(pkg, str) or not pkg:
        raise ImportError(
            f"[SE-20] 相对导入缺少包上下文: name={name!r} level={level}")
    bits = pkg.rsplit(".", level - 1)
    if len(bits) < level:
        raise ImportError(
            f"[SE-20] 相对导入越出顶层包: package={pkg!r} level={level}")
    return bits[0] + ("." + name if name else "")
def _return_sys_modules_hit(name, mod, fromlist):
    if fromlist:
        if _is_safe_module(name) or _is_engine_module(name):
            return _safe_module_delegate(name, None, None, fromlist, 0)
        _ensure_fromlist_submodules(mod, fromlist)
        return mod
    top = name.split(".")[0]
    top_mod = sys.modules.get(top, _MODULES_MISSING)
    if top_mod is _MODULES_MISSING or top_mod is None:
        raise ImportError(
            f"[SE-20] 顶层包 {top!r} 不在 sys.modules（模块注册表非法状态）: {name!r}")
    return top_mod
def _mock_external_submodule(name: str, fromlist):
    top, _sep, rest = name.partition(".")
    if not rest:
        return None
    top_mod = sys.modules.get(top, _MODULES_MISSING)
    if top_mod is _MODULES_MISSING:
        return None
    if not isinstance(top_mod, (ApiResponse, MagicMock)):
        return None
    if not fromlist:
        return top_mod
    node = top_mod
    for seg in rest.split("."):
        node = getattr(node, seg)
    return node
def _safe_module_delegate(name, globals, locals, fromlist, level):
    try:
        return _REAL_IMPORT(name, globals, locals, fromlist, level)
    except Exception as e:
        raise ImportError(
            f"[SE-20] 安全模块 {name!r} 加载失败: {e}") from e
def _import_intra_package_module(name, fromlist):
    try:
        mod = importlib.import_module(name)
    except Exception as e:
        raise ImportError(
            f"[SE-20] 包内模块 {name!r} 加载失败: {e}") from e
    if fromlist:
        _ensure_fromlist_submodules(mod, fromlist)
        return mod
    return sys.modules.get(name.split(".")[0], mod)
def _sandbox_import(name, globals=None, locals=None, fromlist=(), level=0):
    if level > 0:
        resolved = _resolve_relative_name(name, globals, level)
        return _sandbox_import(resolved, globals, locals, fromlist, level=0)
    if level == 0:
        mod = sys.modules.get(name, _MODULES_MISSING)
        if mod is not _MODULES_MISSING and mod is not None:
            return _return_sys_modules_hit(name, mod, fromlist)
        if _is_safe_module(name):
            return _safe_module_delegate(name, globals, locals, fromlist, level)
        if _is_engine_module(name):
            return _safe_module_delegate(name, globals, locals, fromlist, level)
        if _is_installed_third_party(name):
            return _safe_module_delegate(name, globals, locals, fromlist, level)
        if _is_intra_package_module(name):
            return _import_intra_package_module(name, fromlist)
        _sub_mock = _mock_external_submodule(name, fromlist)
        if _sub_mock is not None:
            return _sub_mock
    raise ImportError(f"[SE-20] 沙箱禁止加载未注册模块: {name!r}")
def _should_preload_submodule(mod, mod_name: str, item) -> bool:
    if not isinstance(item, str) or item == "*":
        return False
    if getattr(mod, item, None) is not None:
        return False
    return _is_intra_package_module(mod_name + "." + item)
def _ensure_fromlist_submodules(mod, fromlist):
    if not fromlist or mod is None:
        return
    mod_name = getattr(mod, "__name__", "")
    if not _is_intra_package_module(mod_name):
        return
    for item in fromlist:
        if not _should_preload_submodule(mod, mod_name, item):
            continue
        sub = mod_name + "." + item
        try:
            importlib.import_module(sub)
        except Exception as e:
            raise ImportError(
                f"[SE-20] 包内模块 {sub!r} 加载失败: {e}") from e
_ACTIVE_PROJECT_ROOTS: tuple[str, ...] = ()
_PROJECT_ROOTS_LOCK = threading.RLock()
_ENGINE_PACKAGE_ROOT = os.path.dirname(os.path.abspath(__file__))
_ENGINE_PACKAGE_NAME = __package__ or "jwsgj"
def _normalized_abspath(path) -> str:
    try:
        return os.path.normcase(os.path.normpath(os.path.abspath(
            os.fsdecode(path))))
    except (TypeError, ValueError, OSError) as _e:
        logger.debug("路径规范化不可用: %r (%s)", path, _e)
        return ""
@functools.lru_cache(maxsize=64)
def _normalized_root_forms(project_root: str) -> tuple[str, ...]:
    if not project_root:
        return ()
    forms: list[str] = []
    for candidate in (project_root, os.path.realpath(project_root)):
        norm = _normalized_abspath(candidate)
        if norm and norm not in forms:
            forms.append(norm)
    return tuple(forms)
@functools.lru_cache(maxsize=16)
def _trusted_root_forms(roots: tuple[str, ...]) -> tuple[str, ...]:
    forms: list[str] = []
    for root in roots:
        for norm in _normalized_root_forms(root):
            if norm not in forms:
                forms.append(norm)
    return tuple(forms)
def _path_within_roots(path, roots) -> bool:
    norm = _normalized_abspath(path)
    if not norm:
        return False
    for root in roots:
        if norm == root or norm.startswith(root.rstrip(os.sep) + os.sep):
            return True
    return False
def _is_engine_module(mod_name: str) -> bool:
    if not isinstance(mod_name, str) or not mod_name:
        return False
    if not (mod_name == _ENGINE_PACKAGE_NAME
            or mod_name.startswith(_ENGINE_PACKAGE_NAME + ".")):
        return False
    mod = sys.modules.get(mod_name)
    mod_file = getattr(mod, "__file__", None)
    if isinstance(mod_file, str) and mod_file:
        return _path_within_roots(
            mod_file, _normalized_root_forms(_ENGINE_PACKAGE_ROOT))
    return True
def _clear_project_module_caches() -> None:
    _root_entries.cache_clear()
    _intra_package_module_cached.cache_clear()
def _set_active_project_roots(roots) -> tuple[str, ...]:
    global _ACTIVE_PROJECT_ROOTS
    with _PROJECT_ROOTS_LOCK:
        previous = _ACTIVE_PROJECT_ROOTS
        roots = tuple(roots)
        if roots != previous:
            _clear_project_module_caches()
            _ACTIVE_PROJECT_ROOTS = roots
    return previous
def _restore_active_project_roots(previous: tuple[str, ...]) -> None:
    global _ACTIVE_PROJECT_ROOTS
    with _PROJECT_ROOTS_LOCK:
        if previous != _ACTIVE_PROJECT_ROOTS:
            _clear_project_module_caches()
            _ACTIVE_PROJECT_ROOTS = previous
def _project_roots() -> tuple[str, ...]:
    roots = _ACTIVE_PROJECT_ROOTS
    if roots:
        return roots
    try:
        return (os.getcwd(),)
    except OSError as exc:
        log_swallowed(__name__, exc, context="_project_roots:OSError")
        return ()
@functools.lru_cache(maxsize=256)
def _root_entries(root: str) -> frozenset[str]:
    try:
        return frozenset(
            name.removesuffix(".py") for name in os.listdir(root))
    except OSError as _e:
        log_swallowed(__name__, _e, context="_root_entries:OSError")
        return frozenset()
def _module_file_in_dir(base_dir: str, parts: list[str]) -> bool:
    if not parts or parts[0] not in _root_entries(base_dir):
        return False
    target = os.path.join(base_dir, *parts)
    return (os.path.isfile(target + ".py")
            or os.path.isdir(target))
def _is_own_package_module(mod_name: str) -> bool:
    if not isinstance(mod_name, str) or not mod_name:
        return False
    if _is_engine_module(mod_name):
        return True
    mod = sys.modules.get(mod_name)
    mod_file = getattr(mod, "__file__", None)
    if (isinstance(mod_file, str) and mod_file
            and _path_within_roots(
                mod_file, _trusted_root_forms(_project_roots()))):
        return True
    return _is_intra_package_module(mod_name)
def _is_safe_module(name: str) -> bool:
    return isinstance(name, str) and name.split(".", maxsplit=1)[0] in _SAFE_MODULES
@functools.lru_cache(maxsize=4096)
def _is_installed_third_party(name: str) -> bool:
    """已安装且无系统副作用的第三方包（沙箱放行）。

    历史缺陷：``_SAFE_MODULES`` 只含标准库，``numpy`` / ``PIL`` 这类纯计算
    包也被判为「未注册模块」，导致**任何依赖第三方依赖的技能**在沙箱里
    入口全跳过、整体降级——技能本身没有缺陷，是白名单过窄。

    放行边界：只放行「能 import 到、且不在系统副作用黑名单」的顶层包。
    危险调用（``subprocess`` / ``os.system`` / ``ctypes`` 等）另由
    ``diag_se_injection`` 的高风险调用静态检查拦截，不依赖本白名单。
    """
    if not isinstance(name, str) or not name:
        return False
    top = name.split(".", maxsplit=1)[0]
    if not top or top.startswith("_") or top in _SAFE_MODULES:
        return False
    if top in _DENY_THIRD_PARTY_MODULES:
        return False
    try:
        return importlib.util.find_spec(top) is not None
    except (ImportError, AttributeError, ValueError):
        return False
@functools.lru_cache(maxsize=8192)
def _intra_package_module_cached(name: str, roots: tuple[str, ...]) -> bool:
    parts = [part for part in name.split(".") if part]
    if not parts:
        return False
    for root in roots:
        if _module_file_in_dir(root, parts):
            return True
        root_base = os.path.basename(os.path.normpath(root))
        if parts[0] == root_base and _module_file_in_dir(
                os.path.dirname(os.path.normpath(root)), parts):
            return True
    return False
def _is_intra_package_module(name: str) -> bool:
    if not isinstance(name, str) or not name:
        return False
    return _intra_package_module_cached(name, _project_roots())
def _call_target_name(node) -> str | None:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None
def _warn_danger_nodes(tree: ast.Module, filepath: str) -> None:
    dangerous_attrs = {"__subclasses__", "__mro__", "__bases__"}
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            func_name = _call_target_name(node)
            if func_name in ("system", "popen"):
                logger.warning(
                    "[SE-20] Simulated target contains high-risk call %s in %s:L%s",
                    func_name, filepath,
                    getattr(node, "lineno", "?"),
                )
        if isinstance(node, ast.Attribute) and node.attr in dangerous_attrs:
            logger.warning(
                "[SE-20] Simulated target contains sandbox-escape vector %s in %s:L%s",
                node.attr, filepath,
                getattr(node, "lineno", "?"),
            )
def safe_compile(source: str, filepath: str):
    try:
        tree = parse_cached(source, filepath)
    except (SyntaxError, ValueError, RecursionError) as e:
        logger.debug("suppressed %s: %s", type(e).__name__, e)
        raise SyntaxError(f"Syntax error in {filepath}: {e}") from e
    _warn_danger_nodes(tree, filepath)
    try:
        return compile(tree, filepath, "exec")
    except Exception as e:  # noqa: BLE001
        logger.warning("[Simulate] compile() failed for %s: %s", filepath, e)
        return None
def _make_sandbox_open(orig_open):
    def _sandbox_open(file, mode="r", *args, **kwargs):
        if not (isinstance(mode, str)
                and any(c in mode for c in ("w", "a", "+", "x"))):
            return orig_open(file, mode, *args, **kwargs)
        operation = next((c for c in "rwax" if c in mode), "")
        binary = "b" in mode
        content = b"" if binary else ""
        if (operation == "x"
                and isinstance(file, (str, bytes, os.PathLike))
                and os.path.lexists(file)):
            raise FileExistsError(
                errno.EEXIST, os.strerror(errno.EEXIST), file)
        if ("+" in mode and operation in ("r", "a")
                and isinstance(file, (str, bytes, os.PathLike))):
            try:
                with orig_open(file, "rb" if binary else "r",
                               *args, **kwargs) as source:
                    content = source.read()
            except FileNotFoundError:
                if operation != "a":
                    raise
                parent = os.path.dirname(os.path.abspath(file))
                if not os.path.isdir(parent):
                    raise
        stream = io.BytesIO(content) if binary else io.StringIO(content)
        if operation == "a":
            stream.seek(0, io.SEEK_END)
        return stream
    return _sandbox_open
def safe_exec(code, exec_globals: dict, filepath: str,
             _exit_state: dict[str, bool] | None = None,
             ) -> tuple[str | None, str | None]:
    _restricted_builtins = dict(_EXEC_RESTRICTED_BUILTINS)
    _restricted_builtins["__import__"] = _sandbox_import
    _real_open = builtins.open
    _restricted_builtins["open"] = _make_sandbox_open(_real_open)
    exec_globals["__builtins__"] = _restricted_builtins
    with _SANDBOX_PATCH_LOCK:
        _BYTECODE_PATCH_LEASE.acquire()
    try:
        exec(code, exec_globals)  # noqa: S102
    except SystemExit as e:
        logger.warning("[SE-20] Simulation triggered SystemExit: %s", filepath, exc_info=True)
        label = _system_exit_label(e)
        if label is not None:
            return label, traceback.format_exc()
        if _exit_state is not None:
            _exit_state["clean_system_exit"] = True
        return None, None
    except BaseException as e:
        logger.warning("[SE-20] Simulation exception %s: %s", filepath, e, exc_info=True)
        return str(e) or type(e).__name__, traceback.format_exc()
    finally:
        with _SANDBOX_PATCH_LOCK:
            _BYTECODE_PATCH_LEASE.release()
    return None, None
_API_DEFAULT_MISS = object()
class ApiResponse(MagicMock):
    _API_DEFAULTS: ClassVar[dict] = {
        "success": True,
        "code": 0,
        "msg": "ok",
        "page_token": "",
        "next_page_token": "",
        "records": [],
        "items": [],
    }
    def __call__(self, *_args, **_kwargs):
        if self._mock_return_value is not DEFAULT:
            return self._mock_return_value
        return ApiResponse()
    def __bool__(self) -> bool:
        return True
    def __len__(self) -> int:
        return 0
    def __str__(self) -> str:
        return "ApiResponse()"
    def _api_default(self, key):
        if not isinstance(key, str) or key not in self._API_DEFAULTS:
            return _API_DEFAULT_MISS
        val = self._API_DEFAULTS[key]
        return list(val) if isinstance(val, list) else val
    def __getitem__(self, key):
        val = self._api_default(key)
        if val is not _API_DEFAULT_MISS:
            return val
        if isinstance(key, int):
            raise IndexError(key)
        return ApiResponse()
    __repr__ = __str__
    def __iter__(self):
        return iter([])
    def _get_child_mock(self, **kw):
        name = kw.get("name") or kw.get("_new_name") or ""
        if name == "__iter__":
            return lambda *_args, **_kwargs: iter([])
        if name == "__getitem__":
            def _getitem(*keys):
                _keys = keys[1:] if keys and isinstance(keys[0], ApiResponse) else keys
                if len(_keys) == 1:
                    return ApiResponse.__getitem__(self, _keys[0])
                return ApiResponse()
            return _getitem
        default = self._api_default(name)
        if default is not _API_DEFAULT_MISS:
            return default
        return ApiResponse(**kw)
    def get(self, key, default=None) -> Any:
        val = self._api_default(key)
        if val is not _API_DEFAULT_MISS:
            return val
        if isinstance(key, str) and ('/' in key or key.startswith('http')):
            return ApiResponse()
        return default
@dataclass
class SimEntryPoint:
    name: str
    filepath: str
    line: int
    kind: str
    args: tuple = ()
    skip_reason: str = ""
    exit_on_return: bool = False
@dataclass
class ExecutionResult:
    entry: SimEntryPoint
    success: bool = False
    duration_sec: float = 0.0
    timed_out: bool = False
    error: str | None = None
    traceback: str | None = None
    sim_errors: list[str] = field(default_factory=list)
def _relative_module_parts(filepath: str, project_root: str) -> list[str]:
    _parts = py_stem(safe_relpath(filepath, project_root)).split("/")
    if _parts and (_parts[0] == ".." or ":" in _parts[0]):
        return [py_stem(os.path.basename(filepath))]
    if _parts and not _parts[-1]:
        _parts = _parts[:-1]
    return _parts
def _subtree_py_counts(root: str) -> dict[str, int]:
    direct: dict[str, int] = {}
    children: dict[str, list[str]] = {}
    order: list[str] = []
    for cur, dirs, files in os.walk(root):
        prune_walk_dirs(dirs, root_dir=root)
        dirs.sort()
        direct[cur] = sum(1 for name in files if name.lower().endswith(".py"))
        children[cur] = [os.path.join(cur, name) for name in dirs]
        order.append(cur)
    for cur in reversed(order):
        for child in children[cur]:
            direct[cur] += direct.get(child, 0)
    return direct
def _source_import_root(source_dir: str, project_root: str) -> str:
    package_dir = None
    current = source_dir
    boundary = os.path.normcase(os.path.realpath(project_root))
    while is_path_within_skill(current, project_root):
        if os.path.isfile(os.path.join(current, "__init__.py")):
            package_dir = current
        if os.path.normcase(os.path.realpath(current)) == boundary:
            break
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return os.path.dirname(package_dir) if package_dir else source_dir
def _project_import_roots(project_root: str) -> tuple[str, ...]:
    proj = os.path.abspath(project_root)
    roots = [proj]
    candidates: list[tuple[int, int, str, str]] = []
    subtree_counts = _subtree_py_counts(proj)
    for cur, dirs, files in os.walk(proj):
        rel = os.path.relpath(cur, proj)
        depth = 0 if rel == "." else len(rel.split(os.sep))
        if depth > _MAX_IMPORT_ROOT_DEPTH:
            dirs[:] = []
            continue
        prune_walk_dirs(dirs, root_dir=proj)
        dirs.sort()
        if cur != proj and subtree_counts.get(cur, 0) > 0:
            import_root = _source_import_root(cur, proj)
            root_rel = os.path.relpath(import_root, proj)
            root_depth = (0 if root_rel == "."
                          else len(root_rel.split(os.sep)))
            candidates.append((-subtree_counts.get(cur, 0), root_depth,
                               os.path.normcase(import_root), import_root))
    roots.extend(candidate[3] for candidate in sorted(candidates))
    parent = os.path.dirname(proj)
    if parent and parent != proj:
        roots.append(parent)
    return tuple(dict.fromkeys(roots))
def _project_trust_roots(project_root: str, import_roots) -> tuple[str, ...]:
    parent = os.path.normcase(os.path.dirname(os.path.abspath(project_root)))
    return tuple(root for root in import_roots
                 if os.path.normcase(os.path.abspath(root)) != parent)
class _SysPathEntry(str):
    pass
def _push_sys_path(roots) -> list[str]:
    inserted: list[str] = []
    for root in reversed(tuple(roots)):
        entry = _SysPathEntry(root)
        sys.path.insert(0, entry)
        inserted.append(entry)
    return inserted
def _pop_sys_path(inserted) -> None:
    for root in reversed(inserted):
        if isinstance(root, _SysPathEntry):
            for index, current in enumerate(sys.path):
                if current is root:
                    del sys.path[index]
                    break
            else:
                logger.debug("被调代码已移除路径项: %s", root)
            continue
        try:
            sys.path.remove(root)
        except ValueError:
            logger.debug("被调代码已移除路径项: %s", root)
def _entry_directory(entry_file: str) -> str:
    return os.path.dirname(os.path.abspath(entry_file)) if entry_file else ""
def _import_scope_roots(project_root: str, import_roots,
                        entry_file: str = _DEFAULT_ENTRY_FILE) -> list[str]:
    roots = list(import_roots) if import_roots else list(
        _project_import_roots(project_root))
    entry_dir = _entry_directory(entry_file)
    if (entry_dir and entry_dir not in roots
            and is_path_within_skill(entry_dir, project_root)):
        roots.insert(0, entry_dir)
    return roots
_SANDBOX_EXECUTION_LOCK = threading.RLock()
_SANDBOX_EXECUTION_STATE = threading.local()
@contextlib.contextmanager
def _execution_scope(project_root: str, import_roots=None,
                     entry_file=_DEFAULT_ENTRY_FILE):
    with _SANDBOX_EXECUTION_LOCK:
        previous_active = getattr(
            _SANDBOX_EXECUTION_STATE, "active", False)
        _SANDBOX_EXECUTION_STATE.active = True
        patches_acquired = False
        try:
            _acquire_process_patches()
            patches_acquired = True
            roots = _import_scope_roots(project_root, import_roots, entry_file)
            inserted = _push_sys_path(roots)
            previous: tuple[str, ...] | None = None
            try:
                previous = _set_active_project_roots(
                    _project_trust_roots(project_root, roots))
                previous_modules = frozenset(sys.modules)
                try:
                    yield
                finally:
                    _purge_new_project_modules(previous_modules)
            finally:
                try:
                    if previous is not None:
                        _restore_active_project_roots(previous)
                finally:
                    _pop_sys_path(inserted)
        finally:
            try:
                if patches_acquired:
                    _release_process_patches()
            finally:
                _SANDBOX_EXECUTION_STATE.active = previous_active
@contextlib.contextmanager
def _sandbox_argv(entry_file: str):
    previous = sys.argv
    prog = entry_file or (previous[0] if previous else "")
    sys.argv = [prog]
    try:
        yield
    finally:
        sys.argv = previous
def _top_package_dir(filepath: str, project_root: str) -> str | None:
    proj = os.path.realpath(os.path.abspath(project_root))
    cur = os.path.dirname(os.path.realpath(os.path.abspath(filepath)))
    found = None
    while (cur and os.path.normcase(cur) != os.path.normcase(proj)
           and is_path_within_skill(cur, proj)):
        if os.path.isfile(os.path.join(cur, "__init__.py")):
            found = cur
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    return found
def _skill_prefix_shadowed(skill_name: str, project_root: str) -> bool:
    proj = os.path.realpath(os.path.abspath(project_root))
    for entry in sys.path:
        try:
            base = os.path.realpath(entry or os.getcwd())
        except (OSError, ValueError) as exc:
            log_swallowed(__name__, exc, context="_skill_prefix_shadowed:OSError,ValueError")
            continue
        if is_path_within_skill(base, proj):
            continue
        candidate_dir = os.path.realpath(os.path.join(base, skill_name))
        if candidate_dir == proj:
            continue
        if (os.path.isfile(os.path.join(base, skill_name + ".py"))
                or os.path.isfile(os.path.join(candidate_dir, "__init__.py"))):
            return True
    return False
def infer_module_identity(filepath: str, project_root: str) -> tuple[str, str]:
    proj = os.path.abspath(project_root)
    parts = _relative_module_parts(filepath, project_root)
    is_pkg_init = bool(parts) and parts[-1] == "__init__"
    if is_pkg_init:
        parts = parts[:-1]
    skill_name = os.path.basename(os.path.normpath(proj))
    if os.path.isfile(os.path.join(proj, "__init__.py")):
        full_parts = [skill_name] + parts
    else:
        top = _top_package_dir(filepath, proj)
        if top is not None and _skill_prefix_shadowed(skill_name, proj):
            rel_top = os.path.relpath(top, proj)
            prefix = [] if rel_top == "." else rel_top.replace("\\", "/").split("/")
            full_parts = prefix + _relative_module_parts(filepath, top)
        else:
            full_parts = [skill_name] + parts
    if not full_parts:
        full_parts = [skill_name]
    while full_parts and not full_parts[0].isidentifier():
        full_parts.pop(0)
    if not full_parts:
        return "", ""
    if is_pkg_init or not parts:
        name = ".".join(full_parts)
        return name, name
    if len(full_parts) == 1:
        return "", full_parts[0]
    return ".".join(full_parts[:-1]), ".".join(full_parts)
_SANDBOX_PATCH_LOCK = threading.RLock()
_SANDBOX_MOD_LOCK = threading.RLock()
_SANDBOX_MOD_ENTRIES: dict[str, list] = {}
def _restore_sys_module(mod_name: str, original) -> None:
    if original is _MODULES_MISSING:
        sys.modules.pop(mod_name, None)
    else:
        sys.modules[mod_name] = original
def _purge_new_project_modules(previous_names: frozenset[str]) -> None:
    trusted_roots = _trusted_root_forms(_project_roots())
    for mod_name in tuple(sys.modules):
        if (not isinstance(mod_name, str) or mod_name in previous_names
                or _is_engine_module(mod_name)):
            continue
        top = mod_name.split(".", 1)[0]
        if top in _SAFE_MODULES or top in _RUNTIME_PROTECTED_MODULES:
            continue
        mod_file = getattr(sys.modules.get(mod_name), "__file__", None)
        if isinstance(mod_file, str) and mod_file:
            in_project = _path_within_roots(mod_file, trusted_roots)
        else:
            in_project = _is_intra_package_module(mod_name)
        if in_project:
            sys.modules.pop(mod_name, None)
@contextlib.contextmanager
def _sim_module_registration(module):
    module_name = module.__name__
    register = bool(module_name) and not _is_engine_module(module_name)
    previous = (sys.modules.get(module_name, _MODULES_MISSING)
                if register else _MODULES_MISSING)
    if register:
        sys.modules[module_name] = module
    try:
        yield
    finally:
        if register:
            _restore_sys_module(module_name, previous)
def _make_cf_wait_patch(orig_wait):
    def _sandbox_patched_wait(fs, timeout=None,
                              return_when=concurrent.futures.ALL_COMPLETED):
        effective = min(999 if timeout is None else timeout, 2)
        return orig_wait(fs, timeout=effective, return_when=return_when)
    return _sandbox_patched_wait
def _get_builtins_open():
    if isinstance(__builtins__, dict):
        return __builtins__["open"]
    return __builtins__.open
def _set_builtins_open(func) -> None:
    if isinstance(__builtins__, dict):
        __builtins__["open"] = func
    else:
        builtins.open = func
def _sandbox_closed_error(action: str) -> RuntimeError:
    return RuntimeError(
        f"sandbox closed (timed out): {action} — "
        "execute must not run in a degraded sandbox")
class _PatchLease:
    __slots__ = ("_factory", "_read", "_write", "original", "patch", "refs")
    def __init__(self, read, write, factory) -> None:
        self.refs = 0
        self.original = None
        self.patch = None
        self._read = read
        self._write = write
        self._factory = factory
    def acquire(self) -> None:
        if self.refs == 0:
            self.original = self._read()
            self.patch = self._factory(self.original)
            self._write(self.patch)
        self.refs += 1
    def release(self) -> None:
        if self.refs <= 0:
            return
        self.refs -= 1
        if self.refs:
            return
        if self._read() is self.patch:
            self._write(self.original)
        self.patch = None
        self.original = None
_OPEN_PATCH_LEASE = _PatchLease(
    _get_builtins_open, _set_builtins_open, _make_sandbox_open)
_IO_OPEN_PATCH_LEASE = _PatchLease(
    lambda: io.open, lambda func: setattr(io, "open", func),
    _make_sandbox_open)
_CF_PATCH_LEASE = _PatchLease(
    lambda: concurrent.futures.wait,
    lambda func: setattr(concurrent.futures, "wait", func),
    _make_cf_wait_patch)
_BYTECODE_PATCH_LEASE = _PatchLease(
    lambda: sys.dont_write_bytecode,
    lambda value: setattr(sys, "dont_write_bytecode", value),
    lambda _original: True,
)
_PROCESS_PATCH_LEASES = (
    _OPEN_PATCH_LEASE,
    _IO_OPEN_PATCH_LEASE,
    _CF_PATCH_LEASE,
)
def _acquire_process_patches() -> None:
    with _SANDBOX_PATCH_LOCK:
        acquired: list[_PatchLease] = []
        try:
            for lease in _PROCESS_PATCH_LEASES:
                lease.acquire()
                acquired.append(lease)
        except BaseException:
            for lease in reversed(acquired):
                try:
                    lease.release()
                except Exception as cleanup_error:  # noqa: BLE001
                    logger.warning(
                        "沙箱补丁申请失败后的回滚异常: %s", cleanup_error)
            raise
def _release_process_patches() -> None:
    with _SANDBOX_PATCH_LOCK:
        for lease in _PROCESS_PATCH_LEASES:
            lease.release()
def _iter_absolute_import_names(tree: ast.AST):
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            yield from (alias.name for alias in node.names)
        elif (isinstance(node, ast.ImportFrom) and node.level == 0
              and node.module):
            yield node.module
def _project_import_top_levels(project_root: str) -> tuple[str, ...]:
    imported: set[str] = set()
    _skip = scan_prune_dirs(project_root)
    for dirpath, dirnames, filenames in os.walk(project_root):
        prune_scan_dirnames(dirnames, _skip)
        for filename in filenames:
            if not filename.lower().endswith(".py"):
                continue
            filepath = os.path.join(dirpath, filename)
            try:
                _scan_src = read_source(filepath)
                if _scan_src is None:
                    logger.debug("[Simulate] 依赖预扫描跳过不可读 %s", filepath)
                    continue
                tree = parse_cached(_scan_src, filepath)
            except (OSError, SyntaxError, UnicodeDecodeError, ValueError,
                    RecursionError, MemoryError) as exc:
                logger.debug("[Simulate] 依赖预扫描跳过 %s: %s", filepath, exc)
                continue
            imported.update(
                name.split(".", 1)[0]
                for name in _iter_absolute_import_names(tree))
    return tuple(sorted(imported))
def _system_exit_label(exc: SystemExit) -> str | None:
    code = exc.code
    if code is None or (isinstance(code, int) and code == 0):
        return None
    return f"SystemExit({code})"
def _invoke_callable(func, *args, **kwargs):
    value = func(*args, **kwargs)
    if not inspect.isawaitable(value):
        return value
    async def await_value():
        return await value
    return asyncio.run(await_value())
class SandboxExecutor:
    DEFAULT_TIMEOUT = _DEFAULT_ENTRY_TIMEOUT
    SAFE_MODULES = _SAFE_MODULES
    def __init__(self, project_root: str) -> None:
        try:
            raw_root = os.fsdecode(os.fspath(project_root))
        except (TypeError, ValueError) as exc:
            raise ValueError(f"无效的项目根目录: {project_root!r}") from exc
        if not raw_root.strip():
            raise ValueError(f"无效的项目根目录: {project_root!r}")
        root = os.path.abspath(raw_root)
        if not os.path.isdir(root):
            raise ValueError(f"无效的项目根目录: {project_root!r}")
        self.project_root = root
        self._import_roots = _project_import_roots(self.project_root)
        self._trusted_roots = _project_trust_roots(
            self.project_root, self._import_roots)
        self._injected_modules: set = set()
        self._sandbox_active = False
        self._sandbox_lock = threading.RLock()
        self._closed = False
        self._inserted_roots: list[str] = []
        self._previous_roots: tuple[str, ...] = ()
        self._previous_module_names: frozenset[str] = frozenset()
        self._entry_roots_previous: tuple[str, ...] | None = None
        self._external_top_levels: tuple[str, ...] | None = None
        self._module_stems: frozenset | None = None
    @property
    def closed(self) -> bool:
        return self._closed
    def execute(self, entry: SimEntryPoint, timeout: float | None = None) -> ExecutionResult:
        if getattr(_SANDBOX_EXECUTION_STATE, "active", False):
            result = ExecutionResult(entry=entry)
            result.error = "nested sandbox execution rejected"
            return result
        timeout = normalize_execute_timeout(timeout, self.DEFAULT_TIMEOUT)
        result = ExecutionResult(entry=entry)
        if entry.skip_reason:
            _mark_entry_skipped(
                result, f"[SIM-SKIP] {entry.skip_reason}",
                f"{getattr(entry, 'name', '<unknown>')}: skipped "
                f"({entry.skip_reason})")
            return result
        if timeout <= 0:
            return self._timeout_result(result, timeout)
        if self.closed:
            result.error = str(_sandbox_closed_error("entry rejected"))
            return result
        exec_result = {"done": False, "error": None, "tb": None}
        entry_started = threading.Event()
        thread = threading.Thread(
            target=self._run_entry,
            args=(entry, exec_result, entry_started), daemon=True)
        try:
            thread.start()
        except BaseException as e:  # noqa: BLE001 — 线程创建失败同样需回滚
            log_swallowed(__name__, e, context='execute:BaseException')
            self._rollback_sandbox(setup_error=e)
            result.error = f"{type(e).__name__}: {e}"
            result.traceback = traceback.format_exc()
            return result
        if (not entry_started.wait(_SANDBOX_SETUP_TIMEOUT)
                and not entry_started.is_set()):
            return self._timeout_result(result, timeout)
        entry_t0 = time.time()
        thread.join(timeout=timeout)
        result.duration_sec = round(time.time() - entry_t0, 2)
        if thread.is_alive():
            return self._timeout_result(result, timeout)
        result.success = exec_result["done"] and not exec_result["error"]
        if exec_result["error"]:
            result.error = exec_result["error"]
            result.traceback = exec_result["tb"]
        return result
    def _rollback_sandbox(self, setup_error: BaseException) -> None:
        try:
            self._exit_sandbox()
        except Exception as cleanup_error:  # noqa: BLE001 — 回滚不得掩盖 setup 错误
            logger.warning("沙箱 setup 失败后回滚异常（已上报原始错误 %s）: %s",
                           type(setup_error).__name__, cleanup_error)
    def _run_entry(self, entry: SimEntryPoint, exec_result: dict,
                   entry_started: threading.Event | None = None) -> None:
        with _SANDBOX_EXECUTION_LOCK:
            previous_active = getattr(
                _SANDBOX_EXECUTION_STATE, "active", False)
            _SANDBOX_EXECUTION_STATE.active = True
            try:
                try:
                    self._enter_sandbox()
                    with self._sandbox_lock:
                        if self.closed:
                            raise _sandbox_closed_error(
                                "entry rejected after setup")
                        if entry_started is not None:
                            entry_started.set()
                    self._exec_entry(entry)
                    exec_result["done"] = True
                except BaseException as e:  # noqa: BLE001
                    logger.debug("suppressed %s: %s", type(e).__name__, e)
                    exec_result["error"] = f"{type(e).__name__}: {e}"
                    exec_result["tb"] = (
                        getattr(e, "exec_tb", None) or traceback.format_exc())
                finally:
                    if entry_started is not None:
                        entry_started.set()
                    try:
                        self._exit_sandbox()
                    except BaseException as e:  # noqa: BLE001
                        logger.debug(
                            "suppressed sandbox cleanup %s: %s",
                            type(e).__name__, e)
                        cleanup_error = f"{type(e).__name__}: {e}"
                        previous_error = exec_result.get("error")
                        exec_result["error"] = (
                            f"{previous_error}; sandbox cleanup: {cleanup_error}"
                            if previous_error else cleanup_error)
                        cleanup_tb = traceback.format_exc()
                        previous_tb = exec_result.get("tb")
                        exec_result["tb"] = (
                            f"{previous_tb}\nSandbox cleanup:\n{cleanup_tb}"
                            if previous_tb else cleanup_tb)
            finally:
                _SANDBOX_EXECUTION_STATE.active = previous_active
    def _timeout_result(self, result: ExecutionResult,
                        timeout: float) -> ExecutionResult:
        result.timed_out = True
        result.error = f"超时（{timeout:g}s）"
        # Setup can hold _sandbox_lock; timeout signalling must not wait for it.
        self._closed = True
        return result
    def _enter_sandbox(self):
        with self._sandbox_lock:
            self._enter_sandbox_locked()
    def _enter_sandbox_locked(self):
        if self._sandbox_active:
            return
        if self._closed:
            raise _sandbox_closed_error("entry rejected")
        self._sandbox_active = True
        self._previous_roots = _set_active_project_roots(self._trusted_roots)
        self._mock_loaded_modules()
        self._prefill_project_externals()
        self._previous_module_names = frozenset(sys.modules)
        _acquire_process_patches()
    def _loaded_project_module_conflict(self, mod_name: str) -> bool:
        mod_file = getattr(sys.modules.get(mod_name), "__file__", None)
        if not isinstance(mod_file, str) or not mod_file:
            return False
        if _path_within_roots(
                mod_file, _trusted_root_forms(self._trusted_roots)):
            return True
        return _is_intra_package_module(mod_name)
    def _mock_loaded_modules(self) -> None:
        for mod_name in list(sys.modules.keys()):
            top = mod_name.split(".")[0]
            if top in self.SAFE_MODULES or top in _RUNTIME_PROTECTED_MODULES:
                continue
            if _is_engine_module(mod_name):
                continue
            if self._loaded_project_module_conflict(mod_name):
                self._evict_loaded_module(mod_name)
                self._injected_modules.add(mod_name)
                continue
            if _is_own_package_module(mod_name) or top.startswith("_"):
                continue
            if sys.modules.get(mod_name, _MODULES_MISSING) is _MODULES_MISSING:
                continue
            self._install_module_mock(mod_name)
            self._injected_modules.add(mod_name)
    def _project_module_stems(self) -> frozenset:
        if self._module_stems is None:
            stems = set()
            for _dirpath, _dirnames, _filenames in os.walk(self.project_root):
                prune_walk_dirs(_dirnames, root_dir=self.project_root)
                stems.update(
                    py_stem(name) for name in _filenames
                    if name.lower().endswith(".py"))
            self._module_stems = frozenset(stems)
        return self._module_stems
    def _prefill_project_externals(self) -> None:
        if self._external_top_levels is None:
            self._external_top_levels = _project_import_top_levels(
                self.project_root)
        for name in self._external_top_levels:
            if (name in self.SAFE_MODULES or name in sys.modules
                    or name in _RUNTIME_PROTECTED_MODULES
                    or _is_own_package_module(name)
                    or _is_engine_module(name)
                    or name in self._project_module_stems()):
                continue
            self._install_module_mock(name)
            self._injected_modules.add(name)
    def _exit_sandbox(self):
        with self._sandbox_lock:
            self._exit_sandbox_locked()
    def _exit_sandbox_locked(self):
        if not self._sandbox_active:
            return
        try:
            _purge_new_project_modules(self._previous_module_names)
        finally:
            try:
                self._restore_module_mocks()
            finally:
                try:
                    _release_process_patches()
                finally:
                    self._sandbox_active = False
                    self._previous_module_names = frozenset()
                    _restore_active_project_roots(self._previous_roots)
    def _restore_module_mocks(self) -> None:
        for mod_name in list(self._injected_modules):
            self._release_module_mock(mod_name)
        self._injected_modules.clear()
    def _make_safe_mock(self, mod_name: str) -> MagicMock:
        existing = sys.modules.get(mod_name)
        if isinstance(existing, (ApiResponse, MagicMock)):
            return existing
        return ApiResponse()
    def _install_module_mock(self, mod_name: str) -> None:
        with _SANDBOX_MOD_LOCK:
            entry = _SANDBOX_MOD_ENTRIES.get(mod_name)
            if entry is not None:
                entry[1] += 1
                return
            original = sys.modules.get(mod_name, _MODULES_MISSING)
            sys.modules[mod_name] = self._make_safe_mock(mod_name)
            _SANDBOX_MOD_ENTRIES[mod_name] = [original, 1]
    @staticmethod
    def _evict_loaded_module(mod_name: str) -> None:
        with _SANDBOX_MOD_LOCK:
            entry = _SANDBOX_MOD_ENTRIES.get(mod_name)
            if entry is not None:
                entry[1] += 1
                return
            original = sys.modules.get(mod_name, _MODULES_MISSING)
            sys.modules.pop(mod_name, None)
            _SANDBOX_MOD_ENTRIES[mod_name] = [original, 1]
    @staticmethod
    def _release_module_mock(mod_name: str) -> None:
        with _SANDBOX_MOD_LOCK:
            entry = _SANDBOX_MOD_ENTRIES.get(mod_name)
            if entry is None or entry[1] <= 0:
                return
            entry[1] -= 1
            if entry[1] > 0:
                return
            original = entry[0]
            del _SANDBOX_MOD_ENTRIES[mod_name]
            _restore_sys_module(mod_name, original)
    def _acquire_path(self, entry_file: str = _DEFAULT_ENTRY_FILE) -> None:
        with self._sandbox_lock:
            if self._closed:
                raise _sandbox_closed_error("path acquisition rejected")
            roots = _import_scope_roots(
                self.project_root, self._import_roots, entry_file)
            self._inserted_roots = _push_sys_path(roots)
            entry_dir = _entry_directory(entry_file)
            _entry_trusted = (
                entry_dir and is_path_within_skill(
                    entry_dir, self.project_root))
            self._entry_roots_previous = _set_active_project_roots(
                (entry_dir,) + tuple(self._trusted_roots)
                if _entry_trusted else self._trusted_roots)
    def _release_path(self) -> None:
        with self._sandbox_lock:
            _pop_sys_path(self._inserted_roots)
            self._inserted_roots = []
            if self._entry_roots_previous is not None:
                _restore_active_project_roots(self._entry_roots_previous)
                self._entry_roots_previous = None
    def _exec_entry(self, entry: SimEntryPoint):
        try:
            self._acquire_path(entry.filepath)
            with _sandbox_argv(entry.filepath):
                filepath = entry.filepath
                with tokenize.open(filepath) as f:
                    source = f.read()
                code = safe_compile(source, filepath)
                if code is None:
                    logger.warning(
                        "[Simulate] safe_compile returned None for %s, "
                        "recording failure", filepath)
                    raise RuntimeError(
                        f"{filepath}: compile unavailable (non-syntax failure)")
                _package, _module_name = infer_module_identity(
                    filepath, self.project_root)
                _sim_module = _types_mod.ModuleType(_module_name)
                exec_globals = _sim_module.__dict__
                exec_globals.update({
                    "__name__": _module_name,
                    "__file__": filepath,
                    "__spec__": None,
                    "__package__": _package,
                })
                with _sim_module_registration(_sim_module):
                    exit_state: dict[str, bool] = {}
                    _exec_err, _exec_tb = safe_exec(
                        code, exec_globals, filepath, _exit_state=exit_state)
                    if _exec_err:
                        exc = RuntimeError(_exec_err)
                        exc.exec_tb = _exec_tb
                        raise exc
                    if exit_state.get("clean_system_exit"):
                        return
                    self._call_entry_function(exec_globals, entry)
        finally:
            self._release_path()
    def _call_entry_function(self, exec_globals: dict, entry: SimEntryPoint) -> None:
        if entry.name not in exec_globals:
            raise RuntimeError(f"{entry.name}: not found in module globals")
        func = exec_globals[entry.name]
        if not callable(func):
            raise TypeError(f"{entry.name}: entry value not callable")
        try:
            returned = _invoke_callable(func, *entry.args)
            if getattr(entry, "exit_on_return", False):
                raise SystemExit(returned)
        except SystemExit as _exit:
            if _system_exit_label(_exit) is not None:
                raise
            logger.debug("_call_entry_function: suppressed SystemExit(0)", exc_info=True)
def _sim_mem_guard_min_bytes() -> int:
    try:
        _mb = int(os.environ.get(
            "JWSGJ_SIM_MEM_GUARD_MB", str(_DEFAULT_MEM_GUARD_MB)))
    except (TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_sim_mem_guard_min_bytes:TypeError,ValueError')
        _mb = _DEFAULT_MEM_GUARD_MB
    if _mb <= 0:
        return 0
    return _mb * 1024 * 1024
def _mem_guard_tripped(mem_guard):
    if mem_guard <= 0:
        return False, None
    avail = available_memory_bytes()
    if avail is None or avail >= mem_guard:
        return False, None
    return True, avail
def _trip_mem_guard(mem_guard: int) -> bool:
    tripped, _avail = _mem_guard_tripped(mem_guard)
    if not tripped:
        return False
    logger.warning(
        "[Simulate] 系统可用内存 %.2fGB 低于护栏阈值 %.2fGB，"
        "中止余下沙箱入口（degraded，可追溯）",
        _avail / 2**30, mem_guard / 2**30)
    return True
def _mark_entry_skipped(result,
                        error: str, sim_error: str) -> None:
    result.success = False
    result.error = error
    result.sim_errors.append(sim_error)
