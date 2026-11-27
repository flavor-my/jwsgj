from __future__ import annotations

__all__ = [
    'build_creation_script_assets',
    'collect_scripts_info',
    'declares_cli_flag',
    'detect_cli_json_flag',
    'enhance_script_agent_friendly',
    'generate_agent_cli_script',
    'generate_agent_cli_template',
    'generate_agent_friendly_module_template',
    'generate_agent_friendly_script',
    'generate_agent_module_script',
    'generate_agent_module_template',
    'generate_cli_interface',
    'generate_cli_template',
    'generate_optimized_example_script',
    'generate_optimized_script_for_skill',
    'generate_script_call_examples',
    'generate_script_usage_guide',
    'generate_scripts_for_skill',
    'generate_scripts_readme',
    'has_main_entry_guard',
    'parse_script_source',
    'parse_tree_for_enhance',
    'persist_generated_script',
    'read_script_text',
    'sanitize_cli_identifier',
    'strip_bom_prefix',
    'write_init_module',
]
import ast
import builtins
import io
import json
import keyword
import os
import re
import shlex
import tokenize
from collections.abc import Sequence
from pathlib import Path
from string import Template as _Template
from typing import Any

from jwsgj.build_text_frontmatter import DEFAULT_SKILL_VERSION
from jwsgj.build_text_scoring import (
    md_escape_cell,
    normalize_keywords,
)
from jwsgj.diag_guard_io import (
    atomic_write_text,
    fs_path_text,
    normalize_out_path,
)
from jwsgj.diag_shared_ast_bindings import binding_names_of, import_bound_names
from jwsgj.diag_shared_ast_nodes import (
    ast_name,
    iter_module_scope_nodes,
    module_level_binding_names,
)
from jwsgj.diag_shared_source_core import (
    SOURCE_READ_PARSE_ERRORS,
    parse_py_source,
    read_py_source_with_error,
)
from jwsgj.diag_split_gate import get_entry_guard
from jwsgj.diag_types_normalize import (
    escape_dq_inline,
    escape_dq_text,
    text_or_empty,
)
from jwsgj.diag_types_vocab import EntryDecision
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import normalize_text, py_stem
from jwsgj.skill_profile import is_scan_py_name

logger = get_module_logger(__name__, __file__)
_DEFAULT_OUTPUT_LIMIT = 100
_CONTROL_CHARS_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
def _strip_control_chars(value: Any) -> str:
    return _CONTROL_CHARS_RE.sub("", normalize_text(value))
def read_script_text(path: str | Path, *, lenient: bool = False) -> str:
    path_text = fs_path_text(path)
    if not path_text:
        raise ValueError(f"脚本路径为空或类型非法: {path!r}")
    text, error = read_py_source_with_error(path_text)
    if text is not None:
        return text
    if lenient:
        try:
            return Path(path_text).read_bytes().decode(
                "utf-8", errors="replace").removeprefix(_BOM_PREFIX)
        except OSError as fallback_exc:
            log_swallowed(
                __name__, fallback_exc,
                context=f'read_script_text:{type(fallback_exc).__name__}')
    raise error if error is not None else OSError(f"无法读取脚本: {path}")
def parse_script_source(path: str | Path) -> tuple[str, str, ast.Module]:
    text = read_script_text(path)
    tree, error = parse_py_source(text)
    if tree is None:
        raise error if error is not None else SyntaxError(f"无法解析脚本: {path}")
    doc = (ast.get_docstring(tree) or "").strip()
    purpose_line = doc.split("\n", maxsplit=1)[0].strip()
    return purpose_line, text, tree
_LITERAL_NODE_TYPES = (
    ast.Constant, ast.List, ast.Tuple, ast.Set, ast.Dict, ast.UnaryOp)
def _literal_node_value(node: ast.AST | None, default=None):
    if node is None or not isinstance(node, _LITERAL_NODE_TYPES):
        return default
    try:
        return ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_literal_node_value:Literal')
        return default
def _script_option_specs(tree: ast.AST) -> list[dict[str, Any]]:
    specs: list[dict[str, Any]] = []
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "add_argument"):
            continue
        flags = [
            arg.value for arg in node.args
            if isinstance(arg, ast.Constant)
            and isinstance(arg.value, str)
            and arg.value.startswith("-")
        ]
        if not flags:
            continue
        keywords = {kw.arg: kw.value for kw in node.keywords if kw.arg}
        specs.append({
            "flags": flags,
            "action": (
                _literal_node_value(keywords.get("action"), "")
                or ast_name(keywords.get("action"))
            ),
            "choices": _literal_node_value(keywords.get("choices"), None),
            "default": _literal_node_value(keywords.get("default"), None),
            "required": _literal_node_value(keywords.get("required"), False),
        })
    return specs
_JSON_FLAG_NAMES = ("--output-json", "--json")
_DRY_RUN_FLAG_NAMES = ("--dry-run", "--dry_run")
_ENABLING_ARGPARSE_ACTIONS = frozenset({"store_true", "BooleanOptionalAction"})
def _option_value_from_specs(
    specs: list[dict[str, Any]], name: str
) -> str | None:
    for spec in specs:
        if name not in spec["flags"]:
            continue
        choices = spec.get("choices")
        if isinstance(choices, (list, tuple)) and len(choices) == 1:
            return str(choices[0])
        default = spec.get("default")
        if isinstance(default, str) and default.strip():
            return default.strip()
        if (spec.get("required")
                and isinstance(choices, (list, tuple)) and choices):
            return str(choices[0])
    return None
def _declared_boolean_flag(
    specs: list[dict[str, Any]], names: tuple[str, ...]
) -> str:
    for name in names:
        for spec in specs:
            if (name in spec["flags"]
                    and spec.get("action") in _ENABLING_ARGPARSE_ACTIONS):
                return name
    return ""
def _script_command_prefix(fname: Any) -> str:
    return f"python {shlex.quote(f'scripts/{fname}')}"
def _script_usage_line(fname: str, specs: list[dict[str, Any]]) -> str:
    parts = [_script_command_prefix(fname)]
    action = _option_value_from_specs(specs, "--action")
    if action:
        parts.extend(["--action", shlex.quote(action)])
    json_flag = _declared_boolean_flag(specs, _JSON_FLAG_NAMES)
    if json_flag:
        parts.append(json_flag)
    return " ".join(parts)
def _script_example_line(
    specs: list[dict[str, Any]], usage: str
) -> str:
    dry_run = _declared_boolean_flag(specs, _DRY_RUN_FLAG_NAMES)
    return f"{usage} {dry_run}" if dry_run else usage
def _script_flag_labels(specs: list[dict[str, Any]]) -> str:
    flags: list[str] = []
    for spec in specs:
        for flag in spec["flags"]:
            if flag not in flags:
                flags.append(flag)
    return ", ".join(f"`{flag}`" for flag in flags) if flags else "未声明"
def _script_entries(scripts_info: list[dict] | None) -> list[dict]:
    return [
        item for item in (scripts_info or [])
        if isinstance(item, dict) and item.get("name")
    ]
_UNNAMED_SKILL = "未命名技能"
_SCRIPT_TABLE_HEADER = (
    "| 脚本 | 用途 | 已声明标志 | 调用方式 |",
    "|------|------|-----------|---------|",
)
def detect_cli_json_flag(content: str) -> str:
    if not isinstance(content, str):
        logger.debug("detect_cli_json_flag 内容非 str（%s），按未声明处理",
                     type(content).__name__)
        return ""
    tree, error = parse_py_source(content)
    if tree is None:
        logger.debug("detect_cli_json_flag 语法不可解析，按未声明处理: %s", error)
        return ""
    specs = _script_option_specs(tree)
    return _declared_boolean_flag(specs, _JSON_FLAG_NAMES)
def declares_cli_flag(
    content: str, flag: str, *, enabling: bool = False,
) -> bool:
    if not isinstance(content, str):
        logger.debug("declares_cli_flag 内容非 str（%s），按未声明处理",
                     type(content).__name__)
        return False
    if not isinstance(flag, str) or not flag.startswith("-"):
        return False
    tree, error = parse_py_source(content)
    if tree is None:
        logger.debug("declares_cli_flag 语法不可解析，按未声明处理: %s", error)
        return False
    specs = _script_option_specs(tree)
    if enabling:
        return bool(_declared_boolean_flag(specs, (flag,)))
    return any(flag in spec["flags"] for spec in specs)
def _script_usage_text(script: dict) -> str:
    return str(
        script.get("usage") or _script_command_prefix(script.get("name")))
def _script_rows(scripts_info: list[dict] | None) -> list[str]:
    rows = []
    for script in _script_entries(scripts_info):
        name = script['name']
        usage = _script_usage_text(script)
        rows.append(
            f"| `{md_escape_cell(name)}` "
            f"| {md_escape_cell(str(script.get('purpose') or ''))} "
            f"| {md_escape_cell(str(script.get('flags') or '未声明'))} "
            f"| `{md_escape_cell(usage)}` |"
        )
    return rows
def _collect_scripts_info(scripts_dir: str, py_files: list) -> list[dict]:
    scripts_info = []
    for fname in py_files:
        purpose = "核心操作"
        usage = _script_command_prefix(fname)
        example = usage
        flags = "未声明"
        specs: list[dict[str, Any]] = []
        try:
            first, _source_text, tree = parse_script_source(
                os.path.join(scripts_dir, fname))
            if first:
                purpose = first
            specs = _script_option_specs(tree)
            usage = _script_usage_line(fname, specs)
            example = _script_example_line(specs, usage)
            flags = _script_flag_labels(specs)
        except SOURCE_READ_PARSE_ERRORS as e:
            logger.warning(
                "[build_script_generation] 读取脚本描述失败,用默认: %s", e)
        scripts_info.append({
            "name": fname,
            "purpose": purpose,
            "usage": usage,
            "example": example,
            "flags": flags,
            "json_flag": bool(_declared_boolean_flag(specs, _JSON_FLAG_NAMES)),
            "has_dry": bool(_declared_boolean_flag(
                specs, _DRY_RUN_FLAG_NAMES)),
        })
    return scripts_info
def _script_detail_lines(script: dict, heading: str,
                         code_name: bool) -> list[str]:
    name = script["name"]
    purpose = str(script.get("purpose") or "")
    usage = _script_usage_text(script)
    example = str(script.get("example") or "")
    safe_name = md_escape_cell(name)
    title = (f"{heading} `{safe_name}`" if code_name
             else f"{heading} {safe_name}")
    lines = [
        title,
        f"**用途**: {purpose}",
        "",
        "**调用方式**:",
        "```bash",
        usage,
        "```",
    ]
    if example and example != usage:
        lines.extend(["**示例**:", "```bash", example, "```"])
    lines.extend([
        f"**Agent 调用时机**: 当需要通过 CLI 执行 {purpose} 时调用此脚本",
        "",
    ])
    return lines
def generate_script_call_examples(scripts_info: list[dict]) -> str:
    entries = _script_entries(scripts_info)
    lines = [
        "## 脚本调用指引", "", "### 脚本概览", "",
        *_SCRIPT_TABLE_HEADER,
        *_script_rows(entries),
        "",
    ]
    for script in entries:
        lines.extend(_script_detail_lines(script, "###", True))
    lines.extend([
        "**脚本调用原则**：",
        "- 仅使用本表列出的实际声明标志；未声明标志不得假定可用",
        "- 脚本失败时检查退出码、标准错误及其真实结构化输出契约",
        "",
    ])
    return "\n".join(lines)
def generate_scripts_readme(
    skill_name: str, scripts_info: list[dict],
) -> str:
    skill_name = normalize_text(skill_name) or _UNNAMED_SKILL
    lines = [
        f"# {skill_name} Scripts",
        "",
        *_SCRIPT_TABLE_HEADER,
        *_script_rows(scripts_info),
        "",
        "## 注意事项",
        "- 上表只列出从源码 `add_argument` 实际扫描到的标志，未声明标志不得假定可用",
        "- 参数取值与行为以各脚本源码或 `--help` 输出为准",
        "",
    ]
    return "\n".join(lines)
def _is_public_script(scripts_dir: str, name: str) -> bool:
    if name.startswith("_") or not is_scan_py_name(name):
        return False
    return os.path.isfile(os.path.join(scripts_dir, name))
def _public_script_filenames(scripts_dir: str) -> list[str]:
    if not os.path.isdir(scripts_dir):
        return []
    try:
        names = os.listdir(scripts_dir)
    except OSError as exc:
        logger.warning(
            "[build_script_generation] 列举脚本目录失败，返回空清单: %s: %s",
            scripts_dir, exc)
        return []
    return sorted(
        name for name in names if _is_public_script(scripts_dir, name))
def collect_scripts_info(target_dir: str) -> list[dict]:
    root_text = fs_path_text(target_dir)
    if not root_text:
        return []
    scripts_dir = os.path.join(root_text, "scripts")
    return _collect_scripts_info(
        scripts_dir, _public_script_filenames(scripts_dir))
def generate_script_usage_guide(
    skill_name: str, scripts_info: list[dict[str, Any]] | None = None,
) -> str:
    skill_name = normalize_text(skill_name) or _UNNAMED_SKILL
    entries = _script_entries(scripts_info)
    lines = [
        f"# {skill_name} — 脚本调用指引",
        "",
        f"本技能提供 {len(entries)} 个 Agent 友好脚本，以下是完整调用方式。",
        "",
    ]
    if entries:
        lines.extend([
            "## 脚本概览", "", *_SCRIPT_TABLE_HEADER,
            *_script_rows(entries), "",
        ])
    lines.extend([
        "## Agent 脚本使用原则",
        "",
        "- 仅使用上表列出的实际声明标志；未声明标志不得假定可用",
        "- 参数取值与行为以各脚本源码或 `--help` 输出为准",
        "- 脚本失败时检查退出码、标准错误及其真实结构化输出契约",
        "",
    ])
    for script in entries:
        lines.extend(_script_detail_lines(script, "##", False))
    lines.append("---")
    return "\n".join(lines)
_DEFAULT_MODULE_NAME = "script"
def generate_agent_friendly_script(
    module_name: str = _DEFAULT_MODULE_NAME,
    purpose: str = "",
    skill_keywords: list[str] | str | None = None,
    functions: list[dict] | dict | None = None,
) -> str:
    safe_purpose = escape_dq_inline(_strip_control_chars(purpose))
    safe_module_name = escape_dq_inline(
        _strip_control_chars(module_name or _DEFAULT_MODULE_NAME))
    skill_keywords = _normalize_keyword_list(skill_keywords)
    if isinstance(functions, dict):
        functions = [functions]
    lines = _agent_script_header_lines(safe_purpose, safe_module_name,
                                       skill_keywords, functions)
    lines.extend(_agent_script_body_lines(safe_purpose))
    return "\n".join(lines)
def _normalize_keyword_list(value: object) -> list[str] | None:
    if value is None:
        return None
    if isinstance(value, str):
        return [value]
    if isinstance(value, (set, frozenset)):
        return sorted(value, key=str)
    if isinstance(value, (list, tuple)):
        return list(value)
    logger.debug(
        "generate_agent_friendly_script: skill_keywords 非字符串容器（%s），"
        "按未提供处理", type(value).__name__)
    return None
def _doc_keyword_lines(skill_keywords: list[str] | None) -> list[str]:
    if not skill_keywords:
        return []
    kws: list[str] = []
    for k in skill_keywords:
        if k is None:
            continue
        keyword_text = _strip_control_chars(k).strip()
        if keyword_text:
            kws.append(escape_dq_text(keyword_text))
    if not kws:
        return []
    return [f"Skill keywords: {', '.join(kws)}", ""]
def _doc_function_line(fn: object) -> str:
    if not isinstance(fn, dict):
        return ""
    fname = _strip_control_chars(fn.get("name") or "").strip()
    if not fname:
        return ""
    fdesc = _strip_control_chars(
        fn.get("description") or fn.get("desc") or "").strip()
    fname_s = escape_dq_text(fname)
    fdesc_s = escape_dq_text(fdesc)
    return f"- {fname_s}: {fdesc_s}" if fdesc_s else f"- {fname_s}"
def _doc_function_lines(functions: list[dict] | None) -> list[str]:
    if not functions:
        return []
    fn_lines = [
        line for fn in functions if (line := _doc_function_line(fn))
    ]
    return ["Functions:", *fn_lines, ""] if fn_lines else []
def _agent_script_header_lines(safe_purpose: str, safe_module_name: str,
                                skill_keywords: list[str] | None,
                                functions: list[dict] | None) -> list[str]:
    lines: list[str] = ['"""', f"{safe_purpose or safe_module_name + ' 脚本'}", ""]
    lines.extend(_doc_keyword_lines(skill_keywords))
    lines.extend(_doc_function_lines(functions))
    command_name = safe_module_name.replace(" ", "_")
    lines.append("Agent 使用示例:")
    lines.append(f'  python {command_name} --action run --input "..." --json')
    lines.append(f"  python {command_name} --dry-run")
    lines.append('"""')
    return lines
_STDOUT_ENCODING_GUARD_LINES = (
    "# 输出编码契约：stdout/stderr 统一 UTF-8，消除通道编码对 locale",
    "# 的依赖（GBK 通道遇不可编码载荷会让成功路径在输出环节崩溃，",
    "# 违反 B4/B6 标准）；reconfigure 仅对可重配的标准流生效，测试桩",
    "# 替换的非标准流对象跳过",
    "for _stream in (sys.stdout, sys.stderr):",
    '    if hasattr(_stream, "reconfigure"):',
    '        _stream.reconfigure(encoding="utf-8")',
)
def _stdout_encoding_guard_lines(indent: str = "    ") -> list[str]:
    return [indent + line for line in _STDOUT_ENCODING_GUARD_LINES]
_STDOUT_ENCODING_GUARD_BLOCK = "\n".join(_stdout_encoding_guard_lines())
def _agent_script_body_lines(safe_purpose: str) -> list[str]:
    return [
        "",
        "import argparse",
        "import json",
        "import sys",
        "from pathlib import Path",
        "",
        "__all__ = ['main', 'run_action']",
        "",
        "",
        "def run_action(input_data: str, force: bool = False) -> dict:",
        '    """执行核心操作。force=True 时跳过幂等性检查。"""',
        '    return {"status": "ok", "data": input_data}',
        "",
        "",
        "def main():",
        *_stdout_encoding_guard_lines(),
        '    parser = argparse.ArgumentParser(description="' + safe_purpose + '")',
        '    parser.add_argument("--action", default="run", help="操作名称（当前仅支持 run）")',
        '    parser.add_argument("--input", default="", help="输入数据")',
        '    parser.add_argument("--json", action="store_true", help="JSON 输出")',
        '    parser.add_argument("--dry-run", action="store_true", help="预览模式，不执行实际操作")',
        '    parser.add_argument("--quiet", action="store_true", help="静默模式")',
        '    parser.add_argument("--force", action="store_true", help="跳过幂等性检查")',
        "    args = parser.parse_args()",
        "",
        "    try:",
        "        if args.action != \"run\":",
        "            print(json.dumps({\"status\": \"error\", \"error_code\": \"E002\",",
        "                              \"message\": f\"未知操作: {args.action}\",",
        "                              \"suggestion\": \"当前脚本仅支持 run\"},",
        "                             ensure_ascii=False))",
        "            sys.exit(1)",
        "        if args.dry_run:",
        "            print(json.dumps({\"status\": \"dry_run\", \"action\": args.action,",
        "                              \"input\": args.input},",
        "                             ensure_ascii=False))",
        "            return",
        "        result = run_action(args.input, force=args.force)",
        "        if args.json:",
        "            print(json.dumps(result, ensure_ascii=False, indent=2))",
        "        elif not args.quiet:",
        "            print(result)",
        "    except Exception as e:",
        '        error = {"status": "error", "error_code": "E001", "message": str(e), "suggestion": "检查输入参数"}',
        "        print(json.dumps(error, ensure_ascii=False))",
        "        sys.exit(1)",
        "",
        "",
        'if __name__ == "__main__":',
        "    main()",
        "",
    ]
_CODING_DECL_RE = re.compile(r"^#.*?coding[:=][ \t]*[-\w.]+", re.IGNORECASE)
def _single_line_label(value: Any) -> str:
    return " ".join(_strip_control_chars(value).split())
_BOM_PREFIX = "\ufeff"
_LINE_BREAK_RE = re.compile(r"\r\n|\r|\n")
_LONE_CR_RE = re.compile(r"\r(?!\n)")
def _tokenize_stream(content: str) -> io.StringIO:
    return io.StringIO(_LONE_CR_RE.sub("\n", content))
_DOC_QUOTES = ('"""', "'''")
_DOC_PREFIX_CHARS = frozenset("rRuU")
def _detect_eol(content: str) -> str:
    match = _LINE_BREAK_RE.search(content)
    return match.group(0) if match is not None else "\n"
def _count_line_breaks(content: str, end: int | None = None) -> int:
    return len(_LINE_BREAK_RE.findall(
        content if end is None else content[:end]))
def strip_bom_prefix(content: str) -> str:
    if content.startswith(_BOM_PREFIX):
        return content[len(_BOM_PREFIX):]
    return content
def _leading_header_end(lines: list[str]) -> int:
    insert_at = 0
    for ln in lines:
        s = ln.strip()
        if not s or s.startswith("#!") or _CODING_DECL_RE.match(s):
            insert_at += 1
        else:
            break
    return insert_at
def _leading_statement_start(lines: list[str]) -> int:
    idx = 0
    for ln in lines:
        if not ln.strip() or ln.strip().startswith("#"):
            idx += 1
        else:
            break
    return idx
def _doc_open(head: str) -> tuple[int, str] | None:
    candidates = [(0, head)]
    if head[:1] in _DOC_PREFIX_CHARS:
        candidates.append((1, head[1:]))
    for offset, body in candidates:
        for quote in _DOC_QUOTES:
            if body.startswith(quote):
                return offset, quote
    return None
def _leading_module_doc_span(content: str) -> tuple[int, int] | None:
    lines = content.splitlines()
    idx = _leading_statement_start(lines)
    if idx >= len(lines):
        return None
    head = lines[idx].strip()
    opened = _doc_open(head)
    if opened is None:
        return None
    offset, quote = opened
    if quote in head[offset + len(quote):]:
        return idx + 1, idx + 1
    for end in range(idx + 1, len(lines)):
        if quote in lines[end]:
            return idx + 1, end + 1
    return idx + 1, len(lines)
def _text_main_nodes(content: str) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
    lines = content.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    tokens = []
    try:
        tokens.extend(tokenize.generate_tokens(_tokenize_stream(content).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as e:
        logger.debug("语法错误源码 tokenize 提前终止，复用已读取 token: %s", e)
    nodes: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
    for index, token in enumerate(tokens):
        if token.type != tokenize.NAME or token.string != "def":
            continue
        start_token = token
        if token.start[1] != 0:
            previous = tokens[index - 1] if index else None
            if (previous is None or previous.type != tokenize.NAME
                    or previous.string != "async" or previous.start[1] != 0
                    or previous.start[0] != token.start[0]):
                continue
            start_token = previous
        following = tokens[index + 1] if index + 1 < len(tokens) else None
        if (following is None or following.type != tokenize.NAME
                or following.string != "main"):
            continue
        depth = 0
        colon = None
        for candidate in tokens[index + 2:]:
            if candidate.type == tokenize.OP:
                if candidate.string in ("(", "[", "{"):
                    depth += 1
                elif candidate.string in (")", "]", "}"):
                    depth = max(0, depth - 1)
                elif candidate.string == ":" and depth == 0:
                    colon = candidate
                    break
            elif candidate.type in (tokenize.NEWLINE, tokenize.INDENT,
                                    tokenize.DEDENT, tokenize.ENDMARKER):
                break
        if colon is None:
            continue
        start = offsets[start_token.start[0] - 1] + start_token.start[1]
        end = offsets[colon.end[0] - 1] + colon.end[1]
        header_tree, _swallowed_exc = parse_py_source(
            content[start:end] + " pass\n")
        if header_tree is None:
            log_swallowed(
                __name__, _swallowed_exc,
                context=f'_text_main_nodes:{type(_swallowed_exc).__name__}')
            continue
        if (len(header_tree.body) == 1
                and isinstance(header_tree.body[0],
                               (ast.FunctionDef, ast.AsyncFunctionDef))):
            nodes.append(header_tree.body[0])
    return nodes
def _main_entry_invocable(tree: ast.Module | None, content: str) -> bool:
    if tree is not None:
        return _main_entry_invocable_ast(tree)
    nodes = _text_main_nodes(content)
    return bool(nodes) and _main_fn_zero_arg_invocable(nodes[-1])
def _main_rebound_after(tree: ast.Module, main_def: ast.AST) -> bool:
    index = next(
        (i for i, statement in enumerate(tree.body) if statement is main_def),
        len(tree.body),
    )
    trailing = tree.body[index + 1:]
    if not trailing:
        return False
    trailing_tree = ast.Module(body=trailing, type_ignores=[])
    if ("main" in module_level_binding_names(trailing_tree)
            or "main" in import_bound_names(trailing)):
        return True
    return any(
        isinstance(node, ast.Delete)
        and any("main" in binding_names_of(target) for target in node.targets)
        for node in iter_module_scope_nodes(trailing_tree, descend_classes=False)
    )
def _main_entry_invocable_ast(tree: ast.Module) -> bool:
    main_node = next(
        (node for node in reversed(tree.body)
         if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
         and node.name == "main"),
        None,
    )
    return (main_node is not None
            and not _main_rebound_after(tree, main_node)
            and _main_fn_zero_arg_invocable(main_node))
def _main_fn_zero_arg_invocable(node) -> bool:
    if isinstance(node, ast.AsyncFunctionDef):
        return False
    a = node.args
    pos = list(a.posonlyargs) + list(a.args)
    if len(pos) > len(a.defaults):
        return False
    if any(d is None for d in a.kw_defaults):
        return False
    return not _own_body_is_generator(node)
def _own_body_is_generator(node: ast.FunctionDef) -> bool:
    stack = list(node.body)
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.Yield, ast.YieldFrom)):
            return True
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(current))
    return False
_EXEC_SCOPE_BOUNDARY_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _iter_module_exec_nodes(tree: ast.AST):
    stack = list(ast.iter_child_nodes(tree))
    while stack:
        node = stack.pop()
        if isinstance(node, _EXEC_SCOPE_BOUNDARY_NODES):
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def _module_main_entry_spans(tree: ast.Module) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    for node in _iter_module_exec_nodes(tree):
        if isinstance(node, ast.If) and _is_main_guard_test(node.test):
            spans.append((node.lineno, node.end_lineno))
    return spans
_MAIN_NAME_LITERAL = "__name__"
_MAIN_ENTRY_LITERAL = "__main__"
def _is_main_entry_literal(node: ast.expr) -> bool:
    return isinstance(node, ast.Constant) and node.value == _MAIN_ENTRY_LITERAL
def _is_main_name_node(node: ast.expr) -> bool:
    return isinstance(node, ast.Name) and node.id == _MAIN_NAME_LITERAL
def _is_main_literal_collection(node: ast.expr) -> bool:
    if not isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return False
    return any(_is_main_entry_literal(item) for item in node.elts)
def _is_main_guard_test(t: ast.expr) -> bool:
    if isinstance(t, ast.BoolOp):
        return any(_is_main_guard_test(value) for value in t.values)
    if not isinstance(t, ast.Compare) or len(t.ops) != 1:
        return False
    left, op, right = t.left, t.ops[0], t.comparators[0]
    if isinstance(op, ast.Eq):
        return ((_is_main_name_node(left) and _is_main_entry_literal(right))
                or (_is_main_entry_literal(left) and _is_main_name_node(right)))
    if isinstance(op, ast.In):
        return (_is_main_name_node(left)
                and _is_main_literal_collection(right))
    return False
_MAIN_ENTRY_CONDITION_RE = r"(?P<condition>.*?)"
_MAIN_ENTRY_CALL_RE = (
    r"(?:main[ \t]*\([^()]*\)"
    r"|sys[ \t]*\.[ \t]*exit[ \t]*\([ \t]*"
    r"main[ \t]*\([^()]*\)[ \t]*\)"
    r"|raise[ \t]+SystemExit[ \t]*\([ \t]*"
    r"main[ \t]*\([^()]*\)[ \t]*\)"
    r"|asyncio[ \t]*\.[ \t]*run[ \t]*\([ \t]*"
    r"main[ \t]*\([^()]*\)[ \t]*\))"
)
_MAIN_GUARD_ENTRY_RE = re.compile(
    r"(?P<header>if[ \t]+" + _MAIN_ENTRY_CONDITION_RE + r"[ \t]*:)"
    r"(?P<post>[ \t]*(?:#[^\r\n]*)?)"
    r"(?:\r\n|\r|\n)?"
    r"(?P<between>(?:[ \t]*(?:#[^\r\n]*)?(?:\r\n|\r|\n))*)"
    r"[ \t]*(?P<call>" + _MAIN_ENTRY_CALL_RE + r")"
    r"(?P<trail>[ \t]*(?:#[^\r\n]*)?)"
    r"(?:\r\n|\r|\n|$)",
    re.DOTALL,
)
def _is_main_guard_condition_text(condition: str) -> bool:
    probe, error = parse_py_source(f"if {condition}:\n    pass\n")
    if probe is None:
        logger.debug("入口 guard 条件不可解析，按非入口处理: %s", error)
        return False
    return (len(probe.body) == 1 and isinstance(probe.body[0], ast.If)
            and _is_main_guard_test(probe.body[0].test))
def _main_guard_if_offsets(content: str) -> set[int]:
    lines = content.splitlines(keepends=True)
    line_offsets = [0]
    for line in lines:
        line_offsets.append(line_offsets[-1] + len(line))
    offsets: set[int] = set()
    try:
        for token in tokenize.generate_tokens(_tokenize_stream(content).readline):
            if token.type == tokenize.NAME and token.string == "if":
                row, column = token.start
                offsets.add(line_offsets[row - 1] + column)
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        logger.debug("入口 guard token 扫描提前终止，复用已读取 token: %s", exc)
    return offsets
def _find_entry_guard_targets(
    content: str,
    tree: ast.Module | None,
    doc_line_offset: int,
) -> list[re.Match[str]]:
    if_offsets = _main_guard_if_offsets(content)
    candidates = [
        match for match in _MAIN_GUARD_ENTRY_RE.finditer(content)
        if match.start("header") in if_offsets
        and _is_main_guard_condition_text(match.group("condition"))
    ]
    if tree is None:
        return candidates
    spans = _module_main_entry_spans(tree)
    if not spans:
        return []
    targets: list[re.Match[str]] = []
    for match in candidates:
        match_line = (
            _count_line_breaks(content, match.start()) + 1 - doc_line_offset)
        if any(lo <= match_line <= hi for lo, hi in spans):
            targets.append(match)
    return targets
def parse_tree_for_enhance(content: str) -> ast.Module | None:
    tree, error = parse_py_source(content)
    if tree is None:
        logger.debug("语法解析失败，模块 docstring 走文本近似判定: %s", error)
    return tree
def _inject_module_doc(content: str, skill_name: str,
                       tree: ast.Module | None) -> tuple[str, int]:
    has_module_doc = (ast.get_docstring(tree) is not None
                      if tree is not None
                      else _leading_module_doc_span(content) is not None)
    if has_module_doc:
        return content, 0
    purpose = escape_dq_text(_single_line_label(
        f"{skill_name} 脚本" if skill_name else "脚本"))
    eol = _detect_eol(content)
    doc_block = f'"""{purpose} — Agent 友好化增强"""{eol}{eol}'
    lines = content.splitlines(keepends=True)
    insert_at = _leading_header_end(lines)
    new_content = ("".join(lines[:insert_at]) + doc_block
                   + "".join(lines[insert_at:]))
    return (new_content,
            _count_line_breaks(new_content) - _count_line_breaks(content))
_IGNORED_GUARD_TOKENS = frozenset({
    tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
    tokenize.DEDENT, tokenize.ENCODING, tokenize.ENDMARKER,
})
def _if_header_tokens(tokens: list[tokenize.TokenInfo],
                      start: int) -> list[tokenize.TokenInfo]:
    depth = 0
    header: list[tokenize.TokenInfo] = []
    for token in tokens[start:]:
        if token.type in (tokenize.NEWLINE, tokenize.INDENT,
                          tokenize.DEDENT, tokenize.ENDMARKER):
            return []
        if token.type == tokenize.OP:
            if token.string in "([{":
                depth += 1
            elif token.string in ")]}":
                depth -= 1
            elif token.string == ":" and depth == 0:
                return header
        header.append(token)
    return []
def _is_main_guard_token_header(header: list[tokenize.TokenInfo]) -> bool:
    return _is_main_guard_condition_text(tokenize.untokenize(header))
def _text_has_main_entry_guard(content: str) -> bool:
    tokens: list[tokenize.TokenInfo] = []
    try:
        for token in tokenize.generate_tokens(_tokenize_stream(content).readline):
            if token.type not in _IGNORED_GUARD_TOKENS:
                tokens.append(token)
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc, context='_text_has_main_entry_guard:TokenError')
    for index, token in enumerate(tokens):
        if token.type != tokenize.NAME or token.string != "if":
            continue
        header = _if_header_tokens(tokens, index + 1)
        if header and _is_main_guard_token_header(header):
            return True
    return False
def has_main_entry_guard(content: str, tree: ast.Module | None) -> bool:
    if tree is not None:
        return bool(_module_main_entry_spans(tree))
    return _text_has_main_entry_guard(content)
def _inject_main_entry(content: str, tree: ast.Module | None) -> tuple[str, int]:
    if (has_main_entry_guard(content, tree)
            or not _main_entry_invocable(tree, content)):
        return content, -1
    eol = _detect_eol(content)
    content = (content.rstrip("\r\n") + eol * 3
               + f'if __name__ == "__main__":{eol}'
               + f'    raise SystemExit(main()){eol}')
    return content, content.rindex('if __name__ == "__main__":')
def _line_start_before(content: str, pos: int) -> int:
    line_start = 0
    for match in _LINE_BREAK_RE.finditer(content, 0, pos):
        line_start = match.end()
    return line_start
def _wrap_main_entry(content: str, target: re.Match[str], eol: str) -> str:
    line_start = _line_start_before(content, target.start())
    indent = content[line_start:target.start()]
    if indent.strip():
        return content
    body = indent + "    "
    call_text = target.group("call") + target.group("trail").rstrip()
    call_lines = call_text.splitlines() or [call_text]
    header = (target.group("header") + target.group("post")).rstrip()
    guard_lines = [
        body + "try:",
        *(body + "    " + line for line in call_lines),
        body + "except Exception as e:  # 异常隔离：顶层包装转结构化错误",
        body + '    print(__import__("json").dumps(',
        body + '        {"status": "error", "error_code": "E999", "message": str(e),',
        body + '         "suggestion": "检查输入参数和环境"}, ensure_ascii=False))',
        body + "    raise SystemExit(1)",
        "",
    ]
    wrapped = header + eol + target.group("between") + eol.join(guard_lines)
    return content[:target.start()] + wrapped + content[target.end():]
def _inject_exception_guard(content: str, tree: ast.Module | None,
                            doc_line_offset: int,
                            injected_entry_at: int) -> str:
    eol = _detect_eol(content)
    targets = ([_MAIN_GUARD_ENTRY_RE.search(content, injected_entry_at)]
               if injected_entry_at >= 0
               else _find_entry_guard_targets(content, tree, doc_line_offset))
    for target in reversed([t for t in targets if t is not None]):
        content = _wrap_main_entry(content, target, eol)
    return content
def enhance_script_agent_friendly(content: str, skill_name: str = "") -> str:
    if not content or not content.strip():
        return content
    body = strip_bom_prefix(content)
    tree = parse_tree_for_enhance(body)
    body, doc_line_offset = _inject_module_doc(body, skill_name, tree)
    body, injected_entry_at = _inject_main_entry(body, tree)
    return _inject_exception_guard(body, tree, doc_line_offset,
                                   injected_entry_at)
def generate_agent_friendly_module_template(
    module_name: str, description: str = "",
) -> str:
    safe_desc = escape_dq_text(_strip_control_chars(description or module_name))
    return f'"""\n{safe_desc}\n"""\n\n__all__ = []\n'
_CLI_TYPE_WHITELIST = frozenset({
    "str", "int", "float",
})
_ARGPARSE_RESERVED_OPT_NAMES = frozenset({"help"})
def sanitize_cli_identifier(raw: str) -> str:
    s = str(raw or "").strip()
    if not s:
        return "cli_func"
    return _finalize_identifier(
        s if s.isidentifier() else "_".join(_split_identifier_parts(s)))
def _split_identifier_parts(s: str) -> list[str]:
    parts: list[str] = []
    part: list[str] = []
    for ch in s:
        if ("_" + ch).isidentifier():
            part.append(ch)
        elif part:
            parts.append("".join(part))
            part = []
    if part:
        parts.append("".join(part))
    return parts
def _finalize_identifier(cleaned: str) -> str:
    if not cleaned:
        return "cli_func"
    if not cleaned.isidentifier():
        cleaned = f"_{cleaned}"
    return f"{cleaned}_" if keyword.iskeyword(cleaned) else cleaned
def _unique_arg_name(safe_name: str, used_names: set[str]) -> str:
    if safe_name not in used_names:
        return safe_name
    n = 2
    while f"{safe_name}_{n}" in used_names:
        n += 1
    return f"{safe_name}_{n}"
def _resolve_arg_type(raw_type: str) -> str:
    if raw_type in _CLI_TYPE_WHITELIST:
        return raw_type
    if raw_type:
        logger.debug(
            "generate_cli_interface 非白名单 type=%r 回退 str", raw_type)
    return "str"
def _cli_option_spec(unique_name: str) -> str:
    if unique_name in _ARGPARSE_RESERVED_OPT_NAMES:
        logger.debug(
            "generate_cli_interface 参数名 %r 与 argparse 内建 --help 冲突，"
            "改用 --%s-arg 并以 dest 保留原名", unique_name, unique_name)
        return f'"--{unique_name}-arg", dest="{unique_name}", '
    return f'"--{unique_name}", '
def _cli_argument_line(p: Any, used_names: set[str]) -> str | None:
    raw_name = p.get("name") if isinstance(p, dict) else None
    if not raw_name:
        logger.debug("generate_cli_interface 跳过缺少 name 的参数: %r", p)
        return None
    safe_name = sanitize_cli_identifier(raw_name)
    unique_name = _unique_arg_name(safe_name, used_names)
    if unique_name != safe_name:
        logger.debug(
            "generate_cli_interface 参数 %r 净化后撞名，唯一化为 %r",
            raw_name, unique_name)
    used_names.add(unique_name)
    safe_help = escape_dq_inline(_strip_control_chars(p.get("help")))
    arg_type = _resolve_arg_type(str(p.get("type") or "str").strip())
    return (f'    parser.add_argument({_cli_option_spec(unique_name)}'
            f'type={arg_type}, help="{safe_help}")')
def generate_cli_interface(
    function_name: str, params: list[dict[str, str]],
) -> str:
    fn = sanitize_cli_identifier(function_name)
    safe_desc = escape_dq_inline(_strip_control_chars(function_name))
    lines = ["import argparse", "", f"def {fn}_cli():"]
    lines.append(f'    parser = argparse.ArgumentParser(description="{safe_desc}")')
    used_names: set[str] = set()
    for p in (params or []):
        arg_line = _cli_argument_line(p, used_names)
        if arg_line is not None:
            lines.append(arg_line)
    lines.append("    args = parser.parse_args()")
    lines.append(f"    return {fn}(**vars(args))")
    return "\n".join(lines)
def _sanitize_template_name(name: Any) -> str:
    cleaned = re.sub(r'["\'`\\\x00-\x1f\x7f{}]', "", text_or_empty(name)).strip()
    return cleaned or "module"
def _sanitize_docstring_text(text: Any) -> str:
    return re.sub(r'"{3,}', lambda m: '\\"' * len(m.group(0)),
                  _strip_control_chars(text).replace("\\", "\\\\"))
_BUILTIN_NAMES: frozenset[str] = frozenset(dir(builtins))
_MODULE_TEMPLATE_RUNTIME_NAMES: frozenset[str] = frozenset({
    "os", "Any", "__all__", "__version__", "__doc__", "__name__",
    "__file__", "__package__", "__loader__", "__spec__", "__builtins__",
    "__annotations__", "__cached__",
})
_MODULE_TEMPLATE_RESERVED: frozenset[str] = (
    _BUILTIN_NAMES | _MODULE_TEMPLATE_RUNTIME_NAMES)
def _normalize_exports(
        exports: list[str] | tuple[str, ...] | set[str] | str | None) -> list[str]:
    if isinstance(exports, str):
        exports = [exports]
    elif isinstance(exports, (set, frozenset)):
        exports = sorted(exports, key=repr)
    elif not isinstance(exports, (list, tuple)):
        exports = []
    named = [e for e in exports if isinstance(e, str)
             and e.isidentifier() and not keyword.iskeyword(e)]
    if len(named) != len(exports):
        logger.debug("generate_agent_module_template: 跳过非标识符/关键字 exports 元素 %d 个",
                   len(exports) - len(named))
    reserved = [e for e in named if e in _MODULE_TEMPLATE_RESERVED]
    if reserved:
        logger.warning(
            "generate_agent_module_template: 丢弃 exports 条目 %r（与模板模块作用域名冲突，"
            "生成同名 def 会遮蔽该全局）", reserved)
    clean = [e for e in named if e not in _MODULE_TEMPLATE_RESERVED]
    deduped = list(dict.fromkeys(clean))
    if len(deduped) != len(clean):
        logger.debug("generate_agent_module_template: 跳过重复 exports 条目 %d 个",
                   len(clean) - len(deduped))
    return deduped
def _render_exports_block(clean_exports: list[str]) -> str:
    if not clean_exports:
        return ""
    exports_list = "\n".join(f'    "{e}",' for e in clean_exports)
    return f"\n\n__all__ = [\n{exports_list}\n]"
def _render_export_definitions(clean_exports: list[str]) -> str:
    blocks = []
    for name in dict.fromkeys(clean_exports):
        if name == "run":
            continue
        blocks.append(f'''

def {name}(*args: Any, **kwargs: Any) -> dict[str, Any]:
    """自定义导出占位：调用方须在使用前实现真实业务契约。"""
    return {{"ok": False, "data": None,
            "error": "{name} 尚未实现",
            "fix": "实现该导出函数并补充参数、返回值与测试契约"}}
''')
    return "".join(blocks)
def generate_agent_cli_template(module_name: str, description: str) -> str:
    module_name = _sanitize_template_name(module_name)
    description = _sanitize_docstring_text(description)
    guard_block = "\n".join(_stdout_encoding_guard_lines())
    return f'''#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""{module_name} - {description}

Agent 友好 CLI 脚本入口模板（无状态、强校验、结构化响应、异常隔离）。

I/O 规格:
    输入:  --input  输入文件/目录路径（可选）
    输出:  --output 输出文件路径（可选，缺省打印 JSON 到 stdout）

Usage:
    python {module_name}.py --input <path> --output <path>
    python {module_name}.py --help
    python {module_name}.py --version
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from typing import Any

VERSION = "0.1.0"


def main() -> int:
    """主入口：非交互式，结构化 JSON 输出，异常含修复建议。"""
{guard_block}
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--input", help="输入文件/目录路径")
    parser.add_argument("--output", help="输出文件路径（缺省打印到 stdout）")
    parser.add_argument("--max-items", type=int, default={_DEFAULT_OUTPUT_LIMIT},
                        help="输出条数上限（输出边界控制）")
    parser.add_argument("--version", action="version", version=f"%(prog)s {{VERSION}}")
    args = parser.parse_args()

    try:
        # 强校验：入口处提前失败（不满足直接 raise，杜绝静默降级）
        if args.input and not os.path.exists(args.input):
            raise FileNotFoundError(f"输入路径不存在: {{args.input}}")

        if args.max_items is not None and args.max_items < 1:
            raise ValueError("--max-items 必须 >= 1")

        # 核心逻辑（示例：透传统计）。truncated 基于完整清单长度
        # 判定（条目数恰等于上限时未发生截断，不得误报），先判定后截取
        entries: list[Any] = []
        if args.input:
            if os.path.isdir(args.input):
                entries = sorted(os.listdir(args.input))
            else:
                entries = [os.path.basename(args.input)]
        truncated = len(entries) > args.max_items
        items = entries[: args.max_items]

        result = {{"ok": True, "data": {{"module": "{module_name}", "items": items,
                                 "truncated": truncated}},
                 "fix": ""}}

        # 原子写入：同目录唯一临时文件 + os.replace，避免并发调用
        # 共用固定 .tmp 路径导致一方把另一方的临时文件移走。
        if args.output:
            output_path = os.path.abspath(args.output)
            tmp_path = None
            try:
                with tempfile.NamedTemporaryFile(
                    mode="w", encoding="utf-8", prefix=".tmp-", suffix=".tmp",
                    dir=os.path.dirname(output_path), delete=False,
                ) as fh:
                    tmp_path = fh.name
                    json.dump(result, fh, ensure_ascii=False, indent=2)
                os.replace(tmp_path, output_path)
            finally:
                if tmp_path is not None and os.path.exists(tmp_path):
                    os.unlink(tmp_path)
            print(json.dumps({{"ok": True, "data": {{"written": args.output}},
                             "fix": ""}},
                             ensure_ascii=False))
        else:
            print(json.dumps(result, ensure_ascii=False))
        return 0

    except Exception as exc:  # 异常隔离：顶层包装转结构化错误
        print(json.dumps({{"ok": False, "error": str(exc)[:200],
                         "fix": "查看 --help 确认参数用法，或检查输入数据格式"}},
                         ensure_ascii=False))
        return 1


if __name__ == "__main__":
    sys.exit(main())
'''
def generate_agent_module_template(
        module_name: str, description: str,
        exports: list[str] | tuple[str, ...] | set[str] | str | None = None,
) -> str:
    module_name = _sanitize_template_name(module_name)
    description = _sanitize_docstring_text(description)
    clean_exports = _normalize_exports(exports)
    exports_block = _render_exports_block(clean_exports)
    export_definitions = _render_export_definitions(clean_exports)
    return f'''# -*- coding: utf-8 -*-
"""{module_name} - {description}

Agent 友好模块模板（遵循脚本六原则：无状态、强校验、结构化响应、
异常隔离、幂等、可观测）。

I/O 规格:
    run(input_path, output_path) -> {{"ok": bool, "data": ...,
                                      "error": str, "fix": str}}
"""

from __future__ import annotations

import os
from typing import Any{exports_block}{export_definitions}

def run(input_path: str = "", output_path: str = "") -> dict[str, Any]:
    """便捷运行入口：无状态、强校验、结构化响应、异常隔离。"""
    try:
        if input_path and not os.path.exists(input_path):
            raise ValueError(f"输入路径不存在: {{input_path}}")

        data: dict[str, Any] = {{"module": "{module_name}", "input": input_path}}
        # 可观测性：关键步骤进度输出
        print(f"[{module_name}] run: input={{input_path!r}}")

        if output_path:
            os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True)
            with open(output_path, "w", encoding="utf-8") as fh:
                fh.write(repr(data))
        return {{"ok": True, "data": data, "error": "", "fix": ""}}
    except Exception as exc:
        return {{"ok": False, "data": None, "error": str(exc)[:200],
                "fix": "检查输入路径与参数格式"}}
'''
_CLI_SKELETON_GLOBAL_NAMES: frozenset[str] = frozenset(
    {'argparse', 'inspect', 'json', 'logging', 'sys', '_log', 'main', '__name__'})
_CLI_RESERVED_DEF_NAMES: frozenset[str] = (
    _BUILTIN_NAMES | _CLI_SKELETON_GLOBAL_NAMES)
_CLI_ACTION_RESERVED_PARAM_NAMES: frozenset[str] = frozenset(
    {'_log', 'Exception', 'str'})
_MODULE_PUBLIC_FUNCS: tuple[str, ...] = ('execute', 'validate_input', 'get_status')
_PROBE_FMT = "def _sig_probe({param}): pass"
def _probe_single_param(param: str) -> ast.arguments | None:
    tree, _e = parse_py_source(_PROBE_FMT.format(param=param))
    if tree is None:
        log_swallowed(__name__, _e,
                      context=f'_probe_single_param:{type(_e).__name__}')
        return None
    if len(tree.body) != 1 or not isinstance(tree.body[0], ast.FunctionDef):
        return None
    _args = tree.body[0].args
    if len(_args.args) != 1:
        return None
    return _args
def _param_sig_text_rejects(param: object) -> bool:
    if not isinstance(param, str) or not param or '\n' in param or '\r' in param:
        return True
    return param.endswith(',') or param != param.rstrip()
def _param_sig_has_comment_marker(param: str) -> bool:
    try:
        probe_src = _PROBE_FMT.format(param=param)
        for _tok in tokenize.generate_tokens(io.StringIO(probe_src).readline):
            if _tok.type == tokenize.COMMENT:
                return True
    except (tokenize.TokenError, IndentationError, SyntaxError,
            ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_param_sig_has_comment_marker:{type(_e).__name__}')
        return True
    return False
def _is_valid_param_sig(param: object) -> bool:
    if _param_sig_text_rejects(param):
        return False
    _args = _probe_single_param(param)
    if _args is None:
        return False
    if (_args.posonlyargs or _args.vararg or _args.kwonlyargs
            or _args.kwarg):
        return False
    if _param_sig_has_comment_marker(param):
        return False
    if _args.args[0].arg in _CLI_ACTION_RESERVED_PARAM_NAMES:
        logger.warning(
            "generate_agent_cli_script: 丢弃参数名 %r（会遮蔽生成动作体的运行期依赖）",
            _args.args[0].arg)
        return False
    return True
def _dedup_param_entries(params: list[str]) -> list[str]:
    seen: set[str] = set()
    deduped: list[str] = []
    for param in params:
        param_args = _probe_single_param(param)
        name = param_args.args[0].arg if param_args is not None else ""
        if name and name in seen:
            logger.warning(
                "generate_agent_cli_script: 丢弃重复参数名条目 %r（与先前条目参数名 %r 重名）",
                param, name)
            continue
        if name:
            seen.add(name)
        deduped.append(param)
    return deduped
def _action_def_name(name: str) -> str:
    return f'{name}_action' if name in _CLI_RESERVED_DEF_NAMES else name
def _is_valid_def_name(name: object, used_names: set[str],
                       used_defs: set[str]) -> bool:
    if not isinstance(name, str) or not name.isidentifier() or keyword.iskeyword(name):
        return False
    return name not in used_names and _action_def_name(name) not in used_defs
def _unique_fallback_name(idx: int, used_names: set[str],
                          used_defs: set[str]) -> str:
    fallback = f'func_{idx}'
    while fallback in used_names or fallback in used_defs:
        idx += 1
        fallback = f'func_{idx}'
    return fallback
def _normalize_func_entries(funcs: list[dict]) -> list[dict]:
    normalized = []
    used_names: set[str] = set()
    used_defs: set[str] = set()
    for idx, raw_func in enumerate(funcs):
        func = dict(raw_func)
        name = func.get('name', 'main')
        func['name'] = name
        if not _is_valid_def_name(name, used_names, used_defs):
            fallback = _unique_fallback_name(idx, used_names, used_defs)
            logger.warning(
                "generate_agent_cli_script: 函数名 %r 非法或重复（非法名/关键字/"
                "重名/产物作用域名重命名后撞名），回退 %s",
                name, fallback)
            func['name'] = fallback
        used_names.add(func['name'])
        used_defs.add(_action_def_name(func['name']))
        normalized.append(func)
    return normalized
def _build_param_str(func: dict) -> str:
    params_raw = normalize_keywords(func.get('params'))
    params = []
    for param in params_raw:
        if _is_valid_param_sig(param):
            params.append(param)
        else:
            logger.warning(
                "generate_agent_cli_script: 丢弃非法参数条目 %r（非「参数名[: 注解][= 默认值]」形态）",
                param)
    params = _dedup_param_entries(params)
    if not params:
        return "input_str: str = ''"
    parts: list[str] = []
    for index, param in enumerate(params):
        param_args = _probe_single_param(param)
        if param_args.defaults:
            parts.append(param)
            continue
        if param_args.args[0].arg == "force":
            parts.append(f"{param}=False")
            continue
        parts.append(param if index == 0 else f"{param}=None")
    return ", ".join(parts)
def _cli_head_lines(purpose: str, skill_name: str) -> list[str]:
    return [
        '#!/usr/bin/env python3',
        (f'"""{escape_dq_text(purpose or f"{skill_name} CLI 工具")}\n\nAgent Usage:\n'
         '    本脚本专为 AI Agent 调用设计。\n'
         '    始终使用 --json 获取结构化输出。\n'
         '    使用 --dry-run 预览操作。\n'
         '    使用 --yes 跳过确认提示。\n'
         '    """'),
        '',
        'from __future__ import annotations',
        '',
        'import argparse, inspect, json, logging, sys',
        '',
        '_log = logging.getLogger(__name__)',
        '',
    ]
def _cli_function_def_lines(func: dict) -> list[str]:
    fname = func['name']
    fdesc = _strip_control_chars(func.get('desc'))
    param_str = _build_param_str(func)
    gen_name = _action_def_name(fname)
    return [
        '',
        f'def {gen_name}({param_str}):',
        f'    """{escape_dq_text(fdesc)}"""',
        '    try:',
        f'        _log.info("执行 {fname}")',
        '        return {"status": "ok", "data": None}',
        '    except Exception as e:',
        f'        _log.error("{fname} 失败: %s", e)',
        '        return {"status": "error", "error": str(e)}',
        '',
    ]
def _cli_main_lines(default_action: str, purpose: str, script_name: str,
                    funcs: list[dict]) -> list[str]:
    lines = [
        '',
        'def main():',
        '    """CLI 入口 -- Agent 友好设计 (CLI七原则)。"""',
        *_stdout_encoding_guard_lines(),
        '    parser = argparse.ArgumentParser(',
        f'        description="{escape_dq_inline(purpose or script_name)}",',
        '        formatter_class=argparse.RawDescriptionHelpFormatter,',
        '    )',
        f'    parser.add_argument("--action", "-a", default="{default_action}", help="操作名称")',
        '    parser.add_argument("--input", "-i", default=None, help="输入参数")',
        '    parser.add_argument("--json", "-j", action="store_true", help="JSON 输出")',
        '    parser.add_argument("--yes", "-y", action="store_true", help="跳过确认")',
        '    parser.add_argument("--dry-run", "-n", action="store_true", help="预览模式")',
        '    parser.add_argument("--quiet", "-q", action="store_true", help="静默模式")',
        f'    parser.add_argument("--limit", "-l", type=int, default={_DEFAULT_OUTPUT_LIMIT}, help="限制输出量")',
        '    parser.add_argument("--force", "-f", action="store_true", help="跳过幂等性检查")',
        '',
        '    args = parser.parse_args()',
        '    if args.quiet:',
        '        logging.basicConfig(level=logging.WARNING)',
        '    else:',
        '        logging.basicConfig(level=logging.INFO)',
        '',
        '    action_map = {',
    ]
    for func in funcs:
        fname = func['name']
        lines.append(f'        "{fname}": {_action_def_name(fname)},')
    lines.extend([
        '    }',
        '',
        '    handler = action_map.get(args.action)',
        '    if not handler:',
        '        if args.json:',
        '            print(json.dumps({"status": "error", "error_code": "E_UNKNOWN_ACTION",',
        '                              "message": f"未知操作: {args.action}",',
        '                              "available_actions": list(action_map),',
        '                              "suggestion": "使用 --help 查看可用操作"},',
        '                             ensure_ascii=False))',
        '        else:',
        '            print(f"错误: 未知操作 {args.action}, 可用: {list(action_map.keys())}", file=sys.stderr)',
        '        return 1',
        '',
        '    if args.dry_run:',
        '        print(json.dumps({"status": "dry_run", "action": args.action}))',
        '        return 0',
        '',
        '    # 按签名分派：省略 --input 时保留动作默认值；无默认值形参沿用空串。',
        '    _parameters = inspect.signature(handler).parameters',
        '    _params = tuple(_parameters)',
        '    _input_params = [name for name in _params if name != "force"]',
        '    _call_kwargs = {}',
        '    if _input_params:',
        '        _input_name = _input_params[0]',
        '        if args.input is not None:',
        '            _call_kwargs[_input_name] = args.input',
        '        elif _parameters[_input_name].default is inspect.Parameter.empty:',
        '            _call_kwargs[_input_name] = ""',
        '    if "force" in _params:',
        '        _call_kwargs["force"] = args.force',
        '    result = handler(**_call_kwargs)',
        '    # --limit 落实输出边界：list 型 data 按上限截断',
        '    data = result.get("data")',
        '    if isinstance(data, list) and args.limit > 0:',
        '        data = data[: args.limit]',
        '        result["data"] = data',
        '    if args.json:',
        '        print(json.dumps(result, ensure_ascii=False, indent=2))',
        '    elif not args.quiet:',
        '        print(data if data is not None else result.get("status", "done"))',
        '    return 0 if result.get("status") == "ok" else 1',
        '',
        '',
        'if __name__ == "__main__":',
        '    sys.exit(main())',
        '',
    ])
    return lines
def _normalize_cli_functions(functions: object, purpose: str) -> list[dict]:
    if isinstance(functions, dict):
        functions = [functions]
    funcs = ([f for f in functions if isinstance(f, dict)]
             if isinstance(functions, (list, tuple)) else [])
    if funcs:
        return _normalize_func_entries(funcs)
    if functions:
        logger.warning(
            "generate_agent_cli_script: functions 非 dict 条目或不可迭代形态，回退默认 main")
    return _normalize_func_entries(
        [{'name': 'main', 'desc': purpose or '核心功能', 'params': []}])
def generate_agent_cli_script(script_name: str, purpose: str, skill_name: str = '',
                              functions: list[dict[str, Any]] | None = None) -> str:
    script_name = _strip_control_chars(script_name)
    purpose = _strip_control_chars(purpose)
    skill_name = _strip_control_chars(skill_name)
    funcs = _normalize_cli_functions(functions, purpose)
    default_action = funcs[0]['name']
    lines = _cli_head_lines(purpose, skill_name)
    for func in funcs:
        lines.extend(_cli_function_def_lines(func))
    lines.extend(_cli_main_lines(default_action, purpose, script_name, funcs))
    return '\n'.join(lines)
def _module_script_lines(name_base: str, purpose: str,
                         exports: list[str]) -> list[str]:
    return [
        (f'"""{escape_dq_text(purpose)}\n\n'
         '本模块专为 AI Agent 调用设计。\n'
         '所有公开函数:\n'
         '  - 接受类型化参数，有明确默认值\n'
         '  - 返回结构化 dict: {"status": "ok|error", "data": ..., "error": None|{...}}\n'
         '  - 优雅处理错误，包含可操作的错误信息\n'
         '  - 无状态，幂等（在可能的情况下）\n'
         '"""'),
        '',
        'import logging',
        'from typing import Any, Dict, List, Optional',
        '',
        '_log = logging.getLogger(__name__)',
        '',
        '',
        'def execute(input_data: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:',
        '    """执行核心操作。',
        '',
        '    Args:',
        '        input_data: 输入参数字典',
        '',
        '    Returns:',
        '        {"status": "ok|error", "data": ..., "error": None|{...}}',
        '    """',
        '    try:',
        '        result = _do_execute(input_data or {})',
        '        return {"status": "ok", "data": result, "error": None}',
        '    except ValueError as e:',
        '        _log.warning("参数错误: %s", e)',
        '        return {"status": "error", "data": None, "error": {"message": str(e), "type": "ValidationError"}}',
        '    except Exception as e:',
        '        _log.error("未预期错误: %s", e, exc_info=True)',
        '        return {"status": "error", "data": None, "error": {"message": str(e), "type": type(e).__name__}}',
        '',
        '',
        'def _do_execute(params: Dict[str, Any]) -> Any:',
        '    """内部实现。在此实现业务逻辑。"""',
        '    raise NotImplementedError("_do_execute() 需要实现")',
        '',
        '',
        'def validate_input(params: Dict[str, Any], required: List[str]) -> Optional[str]:',
        '    """校验输入参数。返回错误消息字符串（校验失败时），None（校验通过时）。"""',
        '    if params is None:',
        '        return "输入参数不能为 None"',
        '    for field in required:',
        '        if field not in params:',
        '            return f"缺少必填字段: {field}"',
        '        if params[field] is None:',
        '            return f"字段 {field} 不能为 None"',
        '    return None',
        '',
        '',
        'def get_status() -> Dict[str, Any]:',
        '    """返回模块状态信息。"""',
        f'    return {{"name": "{escape_dq_inline(name_base)}", "version": "{DEFAULT_SKILL_VERSION}", "ok": True}}',
        '',
        '',
        f'__all__ = {exports}',
        '',
    ]
def _valid_module_exports(exports: list[str] | None) -> list[str]:
    valid: list[str] = []
    for exp in exports or []:
        if isinstance(exp, str) and exp in _MODULE_PUBLIC_FUNCS:
            if exp in valid:
                logger.debug(
                    "generate_agent_module_script: 跳过重复 exports 条目 %r", exp)
            else:
                valid.append(exp)
            continue
        logger.warning(
            "generate_agent_module_script: 丢弃 exports 条目 %r"
            "（模板未定义该公开函数，登记 __all__ 会令 import * 崩断）", exp)
    return valid or ['execute', 'get_status']
def generate_agent_module_script(
        module_name: str, purpose: str,
        exports: list[str] | tuple[str, ...] | set[str] | str | None = None,
) -> str:
    _exports = _valid_module_exports(normalize_keywords(exports))
    return "\n".join(_module_script_lines(
        py_stem(_strip_control_chars(module_name)),
        _strip_control_chars(purpose), _exports))
def generate_optimized_script_for_skill(
    skill_dir: str, script_name: str, purpose: str,
    skill_keywords: list[str] | None = None,
    functions: list[dict] | None = None,
) -> str:
    root_text = fs_path_text(skill_dir)
    if not root_text:
        raise ValueError(
            f"generate_optimized_script_for_skill: skill_dir 为空或类型非法: "
            f"{skill_dir!r}")
    script_text = fs_path_text(script_name)
    script_name = Path(script_text).name if script_text else ""
    if script_name in ("", ".", ".."):
        raise ValueError(
            f"script_name 含路径成分且无文件名，无法锚定 scripts/ 写盘: {script_name!r}")
    path = Path(root_text) / "scripts" / script_name
    content_str = generate_agent_friendly_script(
        module_name=script_name, purpose=purpose,
        skill_keywords=skill_keywords, functions=functions,
    )
    return persist_generated_script(
        path, content_str, script_name=script_name, gate=True)
def persist_generated_script(path: str | Path, content: str, *,
                             script_name: str, gate: bool) -> str:
    if not isinstance(content, str):
        raise TypeError(
            f"persist_generated_script: content 须为 str，得到 {type(content).__name__}")
    target = Path(path)
    if gate and not _guard_generated_code(str(target), content):
        raise ValueError(
            f"生成脚本未通过五重门禁，已阻断写盘: {target}；"
            f"请修复阻断项后重试（详见日志 [代码生成守卫]）"
        )
    target.parent.mkdir(parents=True, exist_ok=True)
    atomic_write_text(
        str(target), content, tag="script-generation", newline="\n")
    logger.info("[脚本生成] %s 已写盘%s: %s", script_name,
                "（经五重门禁）" if gate else "", target)
    return str(target)
def _guard_generated_code(filepath: str, code: str) -> bool:
    try:
        result = get_entry_guard().before_write(code, filepath)
    except Exception as e:
        logger.warning(
            "[代码生成守卫] %s 守卫不可用，已阻断写盘: %s", filepath, e, exc_info=True,
        )
        return False
    # ok 只表示无阻断错误；SPLIT_REQUIRED 同样不是写盘许可。
    if not result.ok or result.decision is EntryDecision.SPLIT_REQUIRED:
        logger.warning(
            "[代码生成守卫] %s 未通过门禁（decision=%s，阻断 %d 项），"
            "已阻断写盘: %s",
            filepath, result.decision.value, len(result.errors),
            "; ".join(result.errors[:5]),
        )
        return False
    if result.warnings:
        logger.info(
            "[代码生成守卫] %s 通过但有 %d 项警告", filepath, len(result.warnings),
        )
    return True
def generate_scripts_for_skill(skill_dir: str, skill_name: str, purpose: str = '',
                               functions: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    if not isinstance(skill_dir, (str, os.PathLike)):
        raise TypeError(
            f"generate_scripts_for_skill: skill_dir 须为 str/PathLike，"
            f"得到 {type(skill_dir).__name__}")
    if not str(skill_dir).strip():
        raise ValueError("generate_scripts_for_skill: skill_dir 不能为空")
    skill_name = normalize_text(skill_name)
    purpose = normalize_text(purpose)
    scripts_dir = os.path.join(skill_dir, 'scripts')
    os.makedirs(scripts_dir, exist_ok=True)
    funcs = functions or [{'name': 'execute_task', 'desc': purpose or f'执行 {skill_name} 核心操作', 'params': ['input_param: str']}]
    cli_content = generate_agent_cli_script('main.py', purpose, skill_name, funcs)
    cli_path = persist_generated_script(
        os.path.join(scripts_dir, 'main.py'), cli_content,
        script_name='main.py', gate=True)
    module_content = generate_agent_module_script(skill_name, purpose)
    module_path = persist_generated_script(
        os.path.join(scripts_dir, '__init__.py'), module_content,
        script_name='__init__.py', gate=True)
    written = (cli_path, module_path)
    return {'cli_script': cli_path, 'module_script': module_path,
            'scripts_generated': sum(1 for path in written if path)}
def generate_cli_template(display_name: str,
                          keywords: list[str] | None = None) -> str:
    params: list[dict[str, str]] = [
        {"name": name, "type": "str", "help": f"关键词：{name}"}
        for name in normalize_keywords(keywords)
        if not any(ch.isspace() for ch in name)
    ]
    return generate_cli_interface(display_name, params)
def build_creation_script_assets(
    skill_dir: str, skill_name: str, optimized_description: str,
    optimized_keywords: list[str],
) -> dict[str, Any]:
    skill_name = normalize_text(skill_name)
    optimized_description = normalize_text(optimized_description)
    safe_name = skill_name.replace("-", "_")
    cli_template = generate_agent_friendly_script(
        safe_name, optimized_description[:100])
    module_template = generate_agent_friendly_module_template(
        safe_name, optimized_description[:100])
    script_result = _write_creation_entry_script(
        skill_dir, skill_name, optimized_description, optimized_keywords)
    return {
        "cli_template": cli_template,
        "module_template": module_template,
        "script_result": script_result,
    }
def _write_creation_entry_script(
    skill_dir: str, skill_name: str, optimized_description: str,
    optimized_keywords: list[str],
) -> str | None:
    optimized_description = normalize_text(optimized_description)
    skill_dir_norm = normalize_out_path(skill_dir)
    if skill_dir_norm is None:
        if skill_dir:
            logger.warning("[SkillCreation] skill_dir 非法: %r，跳过脚本写盘",
                           skill_dir)
        return None
    return generate_optimized_script_for_skill(
        skill_dir=skill_dir_norm,
        script_name="main.py",
        purpose=optimized_description[:200],
        skill_keywords=optimized_keywords,
        functions=[{
            "name": "execute_task",
            "description": f"执行 {skill_name} 的核心操作",
            "params": ["input_param: str"],
        }],
    )
_INIT_PY_TEMPLATE = '''"""
$name - v$version
"""

__version__ = "$version"


# --- Code quality baseline (auto-injected by skill scaffolding, do not delete) ---


# Idempotency constraint: prevent re-entry
_executed_actions = set()


def _once(action_id: str):
    """Ensure an action executes only once (idempotent guard)."""
    if action_id in _executed_actions:
        return False
    _executed_actions.add(action_id)
    return True


# Standardized output constraint

def _ok(data=None):
    """Return standard success response."""
    return {"status": "ok", "data": data}


def _err(message: str, code: str = "UNKNOWN"):
    """Return standard error response."""
    return {"status": "error", "error": {"message": message, "code": code}}


def _result(data=None, error=None):
    """Return standard result response."""
    if error is not None:
        return _err(str(error), "RUNTIME")
    return _ok(data)
'''
def write_init_module(target_dir: str, name: str) -> str:
    root_text = fs_path_text(target_dir)
    if not root_text:
        raise ValueError(
            f"write_init_module: target_dir 为空或类型非法: {target_dir!r}")
    safe_name = _sanitize_docstring_text(_single_line_label(name))
    init_py = _Template(_INIT_PY_TEMPLATE).substitute(
        name=safe_name,
        version=DEFAULT_SKILL_VERSION,
    )
    init_path = os.path.join(root_text, "__init__.py")
    atomic_write_text(
        init_path, init_py, tag="script-generation", newline="\n")
    return init_path
def _gen_opt_b1_header(display_name: str) -> str:
    _display = _sanitize_docstring_text(normalize_text(display_name))
    return f'''"""{_display} — 核心执行脚本 (v1.0.0)

本脚本符合以下 8 项代码质量优化标准：
B1: 完整类型注解
B2: Google 风格 docstring + Example
B3: 黑盒封装，无交互输入
B4: 结构化错误处理
B5: argparse CLI 接口
B6: 结构化日志
B7: 幂等性保护
B8: 依赖自检

使用方式:
    python scripts/main.py --action run --input "test" --output-json
    python scripts/main.py --action run --input "test" --dry-run
    python scripts/main.py --help
"""

import argparse
import errno
import hashlib
import importlib.util
import json
import logging
import os
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any, Dict, Optional, Tuple

if os.name == "nt":
    import msvcrt
else:
    import fcntl
'''
def _gen_opt_b8_dependency_check() -> str:
    return '''# B8: 依赖自检
def _check_dependencies() -> bool:
    """检查运行环境是否满足依赖要求。

    Returns:
        bool: 所有依赖是否满足

    Example:
        >>> _check_dependencies()
        True
    """
    required = []  # 在此添加必需的第三方包
    missing = []
    for pkg in required:
        if importlib.util.find_spec(pkg.replace("-", "_")) is None:
            missing.append(pkg)
    if missing:
        print(json.dumps({"error": "missing_dependencies", "packages": missing,
                          "suggestion": f"pip install {' '.join(missing)}"},
                         ensure_ascii=False))
        return False
    return True
'''
def _gen_opt_b6_logging() -> str:
    return '''# B6: 结构化日志


def setup_logging(log_file: Optional[str] = None) -> logging.Logger:
    """配置 JSON Lines 结构化日志。

    Args:
        log_file: 日志文件路径（None 表示 stderr，避免污染 stdout 业务结果）

    Returns:
        logging.Logger: 配置好的日志器
    """
    logger = logging.getLogger(__name__)
    logger.setLevel(logging.INFO)
    for _h in list(logger.handlers):
        if isinstance(_h, logging.FileHandler):
            _h.close()
    logger.handlers.clear()

    class JsonlFormatter(logging.Formatter):
        def format(self, record):
            entry = {
                "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(record.created)),
                "level": record.levelname,
                "operation": getattr(record, "operation", record.msg),
                "status": getattr(record, "status", "info"),
                "duration_ms": getattr(record, "duration_ms", 0),
                "message": record.getMessage(),
            }
            return json.dumps(entry, ensure_ascii=False)

    if log_file is None:
        handler = logging.StreamHandler(sys.stderr)
    else:
        handler = logging.FileHandler(log_file, mode="a", encoding="utf-8")
    handler.setFormatter(JsonlFormatter())
    logger.addHandler(handler)
    return logger
'''
def _gen_opt_b7_idempotency() -> str:
    return '''# B7: 幂等性保护（检查与标记分离：检查只读不写，操作成功后
# 显式标记完成，防止"检查即标记"让失败操作在重试时被误跳过）
def _lock_windows_handle(lock_handle) -> None:
    """Windows 下对句柄首字节加独占锁（自旋等待；锁冲突以外的错误上抛）。"""
    lock_handle.seek(0, os.SEEK_END)
    if lock_handle.tell() == 0:
        lock_handle.write(b"\\0")
        lock_handle.flush()
    lock_handle.seek(0)
    while True:
        try:
            msvcrt.locking(lock_handle.fileno(), msvcrt.LK_NBLCK, 1)
            return
        except OSError as exc:
            if exc.errno not in (errno.EACCES, errno.EAGAIN, errno.EDEADLK):
                raise
            time.sleep(0.05)


def _acquire_idem_state_lock(state_file: str):
    """获取跨线程/跨进程状态锁；进程退出时由操作系统自动释放。"""
    state_path = Path(state_file)
    state_path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = state_path.with_name(state_path.name + ".lock")
    lock_handle = lock_path.open("a+b")
    try:
        if os.name == "nt":
            _lock_windows_handle(lock_handle)
        else:
            fcntl.flock(lock_handle.fileno(), fcntl.LOCK_EX)
        return lock_handle
    except Exception:
        lock_handle.close()
        raise


def _release_idem_state_lock(lock_handle) -> None:
    try:
        lock_handle.seek(0)
        if os.name == "nt":
            msvcrt.locking(lock_handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            fcntl.flock(lock_handle.fileno(), fcntl.LOCK_UN)
    finally:
        lock_handle.close()


def _load_idem_state(state_file: str) -> dict:
    """读取幂等状态；内容损坏按空态处理，读取 OSError 必须向上抛出。"""
    state_path = Path(state_file)
    if state_path.exists():
        try:
            state = json.loads(state_path.read_text(encoding="utf-8"))
        except (ValueError, RecursionError, MemoryError):
            # 仅内容损坏按空状态处理（JSONDecodeError 是 ValueError 子类）。
            # 读取 OSError 不在此吞掉：把权限/占用失败当成空状态会把已完成
            # 操作误判为首次执行；应交给 main 转 IDEMPOTENCY_STATE_ERROR。
            state = None
        # 形态守卫：合法 JSON 但非 dict（如被人工编辑为列表/字符串）
        # 同属状态不可用，兑现本函数 dict 返回契约
        if isinstance(state, dict):
            # 子形态守卫：completed 必须是 list。人工编辑成标量/字典时
            # `operation_id in completed` 会退化为子串匹配（"op1" in
            # "op10" 假跳过）或 TypeError，mark_completed 的 append 会
            # AttributeError；归一为空表，check/mark 共用同一契约
            if not isinstance(state.get("completed"), list):
                state["completed"] = []
            return state
    return {"completed": []}


def _check_idempotency_unlocked(
        state_file: str, operation_id: str, force: bool = False,
) -> Tuple[bool, str]:
    if force:
        return True, "强制执行"
    state = _load_idem_state(state_file)
    if operation_id in state.get("completed", []):
        return False, f"操作 {operation_id} 已完成，跳过"
    return True, "首次执行"


def check_idempotency(state_file: str, operation_id: str, force: bool = False) -> Tuple[bool, str]:
    """检查操作是否已执行（只读检查，不写状态文件）。

    Args:
        state_file: 状态文件路径
        operation_id: 操作唯一标识
        force: 是否强制执行

    Returns:
        Tuple[bool, str]: (是否应执行, 原因)

    Example:
        >>> should_run, reason = check_idempotency("state.json", "op_001")
        >>> print(should_run)
        True
    """
    if force:
        return True, "强制执行"
    lock_handle = _acquire_idem_state_lock(state_file)
    try:
        return _check_idempotency_unlocked(state_file, operation_id)
    finally:
        _release_idem_state_lock(lock_handle)


def _mark_completed_unlocked(state_file: str, operation_id: str) -> None:
    """操作成功执行后标记为已完成（写入状态文件）。

    与 check_idempotency 分离：检查阶段不写状态，仅操作成功后
    由调用方显式标记，确保失败操作可重试。
    """
    state = _load_idem_state(state_file)
    completed = state.setdefault("completed", [])
    if operation_id not in completed:
        completed.append(operation_id)
    state_path = Path(state_file)
    state_path.parent.mkdir(parents=True, exist_ok=True)
    temp_path = state_path.with_name(
        f"{state_path.name}.tmp.{os.getpid()}.{threading.get_ident()}")
    try:
        temp_path.write_text(
            json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
        os.replace(temp_path, state_path)
    finally:
        if temp_path.exists():
            temp_path.unlink(missing_ok=True)


def mark_completed(state_file: str, operation_id: str) -> None:
    """操作成功执行后标记为已完成（写入状态文件）。

    与 check_idempotency 分离：检查阶段不写状态，仅操作成功后
    由调用方显式标记，确保失败操作可重试。
    """
    lock_handle = _acquire_idem_state_lock(state_file)
    try:
        _mark_completed_unlocked(state_file, operation_id)
    finally:
        _release_idem_state_lock(lock_handle)
'''
def _gen_opt_b2_core_action(display_name: str) -> str:
    _display = _sanitize_docstring_text(normalize_text(display_name))
    return f'''# B1+B2: 核心函数（完整类型注解 + Google 风格 docstring）
def run_core_action(input_data: str, options: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """执行 {_display} 的核心操作。

    Args:
        input_data: 输入数据
        options: 可选配置参数

    Returns:
        Dict[str, Any]: 操作结果，含 status、output、duration_ms

    Raises:
        ValueError: 输入数据无效时抛出

    Example:
        >>> result = run_core_action("test_input", {{"verbose": True}})
        >>> print(result["status"])
        success
    """
    start = time.time()
    options = options or {{}}

    if not input_data:
        raise ValueError("input_data 不能为空")

    output = f"已处理: {{input_data}}"

    duration_ms = (time.time() - start) * 1000
    return {{
        "status": "success",
        "output": output,
        "duration_ms": round(duration_ms, 2),
    }}
'''
def _gen_opt_b4_error_handling() -> str:
    return '''# B4: 结构化错误处理
def safe_execute(func, *args, **kwargs) -> Dict[str, Any]:
    """安全执行函数，异常转为结构化错误。

    Args:
        func: 要执行的函数
        *args: 位置参数
        **kwargs: 关键字参数

    Returns:
        Dict[str, Any]: 执行结果或错误信息
    """
    try:
        return func(*args, **kwargs)
    except ValueError as e:
        return {"status": "error", "error_code": "VALUE_ERROR", "message": str(e)}
    except TypeError as e:
        return {"status": "error", "error_code": "TYPE_ERROR", "message": str(e)}
    except OSError as e:
        return {"status": "error", "error_code": "IO_ERROR", "message": str(e)}
    except Exception as e:  # noqa: BLE001 -- pipeline guard
        return {"status": "error", "error_code": "UNKNOWN_ERROR", "message": str(e)}
'''
def _gen_opt_b5_cli(display_name: str) -> str:
    _desc_literal = json.dumps(f"{display_name} — 核心执行脚本", ensure_ascii=False)
    return f'''# B5: CLI 接口
def build_parser() -> argparse.ArgumentParser:
    """构建标准化命令行参数解析器。

    Returns:
        argparse.ArgumentParser: 配置好的解析器
    """
    parser = argparse.ArgumentParser(
        description={_desc_literal},
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python scripts/main.py --action run --input "test" --output-json
  python scripts/main.py --action run --input "test" --dry-run
  python scripts/main.py --action status
        """
    )
    parser.add_argument("--action", choices=["run", "status", "check"],
                        default="run", help="操作类型")
    parser.add_argument("--input", type=str, help="输入数据")
    parser.add_argument("--output-json", action="store_true",
                        help="以 JSON 格式输出结果")
    parser.add_argument("--dry-run", action="store_true",
                        help="预览模式，不执行实际操作")
    parser.add_argument("--verbose", action="store_true",
                        help="详细输出")
    parser.add_argument("--force", action="store_true",
                        help="强制执行（跳过幂等性检查）")
    return parser
'''
def _gen_opt_b3_main_entry(display_name: str, keyword_sample: Sequence[str]) -> str:
    _display_literal = json.dumps(display_name, ensure_ascii=False)
    _keywords_literal = json.dumps(
        normalize_keywords(keyword_sample)[:5], ensure_ascii=False)
    return f'''# B3: 黑盒封装主入口
def _run_with_idempotency(args) -> Dict[str, Any]:
    """B7: 幂等保护下执行核心操作并返回结构化结果。

    状态属于运行态产物，不得写进被调用方（任何项目）的源码目录：优先
    SCRIPT_STATE_DIR，否则落系统临时目录下按脚本绝对路径分区，既不
    污染工程树，也不随 CWD 漂移。
    """
    _state_dir = os.environ.get("SCRIPT_STATE_DIR") or os.path.join(
        tempfile.gettempdir(), "agent-script-state")
    _state_file = os.path.join(
        _state_dir,
        hashlib.sha256(
            str(Path(__file__).resolve()).encode("utf-8")).hexdigest()[:16]
        + ".state.json")
    # 非空输入沿用历史幂等键；缺失/空输入用 JSON 区分 None、空串与 default。
    op_id = (f"{{args.action}}_{{args.input}}" if args.input else
             json.dumps([args.action, args.input], ensure_ascii=False,
                        separators=(",", ":")))
    try:
        # 检查、业务执行和成功标记是同一事务；只锁写文件仍会让两个
        # 调用同时通过检查并重复产生副作用。
        _lock_handle = _acquire_idem_state_lock(_state_file)
        try:
            should_run, reason = _check_idempotency_unlocked(
                _state_file, op_id, force=args.force
            )
            if not should_run:
                return {{"status": "skipped", "reason": reason}}
            # B4: 安全执行
            result = safe_execute(run_core_action, args.input or "",
                                  {{"verbose": args.verbose}})
            # B7: 仅执行成功才标记完成（失败可重试，不写状态）
            if result.get("status") == "success":
                _mark_completed_unlocked(_state_file, op_id)
            return result
        finally:
            _release_idem_state_lock(_lock_handle)
    except OSError as exc:
        # 状态读写也属于主业务链；失败必须进入同一结构化错误契约。
        return {{"status": "error",
                "error_code": "IDEMPOTENCY_STATE_ERROR",
                "message": str(exc)[:200],
                "suggestion": "检查 SCRIPT_STATE_DIR 的目录类型与写权限"}}


def main() -> int:
    """主入口函数（黑盒封装，无交互输入）。

    Returns:
        int: 退出码（0=成功, 1=失败）
    """
{_STDOUT_ENCODING_GUARD_BLOCK}

    if not _check_dependencies():
        return 1

    parser = build_parser()
    args = parser.parse_args()

    logger = setup_logging()
    logger.info("script_start", extra={{"operation": args.action, "status": "starting"}})

    if args.dry_run:
        print(json.dumps({{"status": "dry_run", "action": args.action,
                          "message": "预览模式，未执行实际操作"}},
                         ensure_ascii=False, indent=2))
        return 0

    if args.action == "status":
        result = {{"status": "ok", "skill": {_display_literal},
                  "keywords": {_keywords_literal}}}
    elif args.action == "check":
        result = {{"status": "ok", "dependencies": "all_ok",
                  "python_version": f"{{sys.version_info.major}}.{{sys.version_info.minor}}"}}
    else:
        # B7: 幂等保护下的执行/标记事务在独立函数中完成，主入口只做分派。
        result = _run_with_idempotency(args)

    if args.output_json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        print(json.dumps(result, ensure_ascii=False))

    logger.info("script_end", extra={{"operation": args.action,
                "status": result.get("status", "unknown")}})
    return 0 if result.get("status") in ("success", "ok", "skipped", "dry_run") else 1

if __name__ == "__main__":
    sys.exit(main())'''
def generate_optimized_example_script(
        target_dir: str,
        display_name: str,
        keywords: Sequence[str] | None = None) -> str:
    root_text = fs_path_text(target_dir)
    if not root_text:
        raise ValueError(
            "generate_optimized_example_script: target_dir 为空或类型非法: "
            f"{target_dir!r}")
    scripts_dir = os.path.join(root_text, "scripts")
    os.makedirs(scripts_dir, exist_ok=True)
    script_path = os.path.join(scripts_dir, "main.py")
    display_name = normalize_text(display_name)
    keyword_sample = normalize_keywords(keywords)
    sections = [
        _gen_opt_b1_header(display_name),
        _gen_opt_b8_dependency_check(),
        _gen_opt_b6_logging(),
        _gen_opt_b7_idempotency(),
        _gen_opt_b2_core_action(display_name),
        _gen_opt_b4_error_handling(),
        _gen_opt_b5_cli(display_name),
        _gen_opt_b3_main_entry(display_name, keyword_sample),
    ]
    script_content = '\n\n'.join(sections)
    return persist_generated_script(
        script_path, script_content, script_name="main.py", gate=True)
