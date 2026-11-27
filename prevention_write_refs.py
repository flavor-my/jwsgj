from __future__ import annotations  # noqa: I001
import logging
from jwsgj.prevention_refs_main import (
    CHANNEL_SUFFIX,
    CodeRef,
    anchor_module,
    build_keyed_registry,
    make_code_ref,
    register_code_refs,
    series_names,
    series_rule_ids,
)
__all__ = [
    'GUARDS_CODE_REFS',
    'GUARDS_CODE_REFS_VERSION',
    'WRITE_CODE_REFS',
    'WRITE_CODE_REFS_VERSION',
]
_log = logging.getLogger(__name__)
_log.info("prevention_write_refs 编写时与守卫域预防库已加载: %d 项导出", len(__all__))
WRITE_CODE_REFS_VERSION = '1.1.6'
_WRITE_CHANNEL = anchor_module('prevention_write_checks') + CHANNEL_SUFFIX
_WRITE_REFS: list[CodeRef] = [
    make_code_ref(
        'robust', 'WM-01', '管道键名契约断裂：调用方访问返回字典中不存在的键', 'P1',
        'def run_stage1(data):\n'
            '    return {"report": {"findings": [{"rule_id": "D1"}], "count": 1}}\n'
            '\n'
            '\n'
            'def run_stage2(stage1_result):\n'
            '    # BUG: findings 嵌在 report 层下，顶层 .get 恒取默认空\n'
            '    findings = stage1_result.get("findings", [])\n'
            '    return {"processed": len(findings)}\n'
            '\n'
            '\n'
            'def main(data):\n'
            '    return run_stage2(run_stage1(data))\n',
        'def run_stage1(data):\n'
            '    return {"report": {"findings": [{"rule_id": "D1"}], "count": 1}}\n'
            '\n'
            '\n'
            'def run_stage2(stage1_result):\n'
            '    # 契约对齐：嵌套层级与上游字面量逐一核对\n'
            '    findings = stage1_result["report"]["findings"]\n'
            '    return {"processed": len(findings)}\n'
            '\n'
            '\n'
            'def main(data):\n'
            '    return run_stage2(run_stage1(data))\n',
        '多阶段管道/编排器中最高频的静默 BUG：上游返回嵌套字典'
            '（{"report": {"findings": []}}），下游按旧契约在顶层 .get'
            '("findings")——不报错、恒空、功能静默失效；编排器变体是'
            '循环内 stage 结果不回写 context，下游读共享层恒空。写跨函数'
            '消费代码时，调用方键路径必须与上游 return 字面量（含嵌套'
            '层级）逐一核对；编排循环内必须回写结果到共享上下文。',
        _WRITE_CHANNEL,
    ),
    make_code_ref(
        'pytrap', 'DC-05', '数据类缺少 @dataclass 装饰器（注解字段不生成构造器）', 'P1',
        'class ScanResult:\n'
            '    file: str\n'
            '    findings: list\n'
            '    duration: float = 0.0\n'
            '\n'
            '\n'
            'def main():\n'
            '    return ScanResult("a.py", [])  # TypeError: 缺 __init__\n',
        'from dataclasses import dataclass\n'
            '\n'
            '\n'
            '@dataclass\n'
            'class ScanResult:\n'
            '    file: str\n'
            '    findings: list\n'
            '    duration: float = 0.0\n'
            '\n'
            '\n'
            'def main():\n'
            '    return ScanResult("a.py", [])\n',
        '类定义了类型注解字段但未加 @dataclass——注解只是元数据，'
            '不生成 __init__，实例化 ScanResult(...) 直接 TypeError。'
            'AI 手写数据类时高频遗漏装饰器行；反之 Enum/TypedDict/'
            'Protocol/pydantic BaseModel 应显式继承基类，不用 dataclass。',
        _WRITE_CHANNEL,
    ),
    make_code_ref(
        'fileops', 'NL-01', 'open 读写 newline 不匹配：\\r\\n 被二次转成 \\r\\r\\n', 'P1',
        'def fix_file(path):\n'
            '    with open(path, "r", encoding="utf-8", newline="") as f:\n'
            '        src = f.read()\n'
            '    fixed = src.replace("old", "new")\n'
            '    # BUG: 原有 \\r\\n 被写侧再转一次 → \\r\\r\\n 整文件破坏\n'
            '    with open(path, "w", encoding="utf-8", newline="\\r\\n") as f:\n'
            '        f.write(fixed)\n',
        'def fix_file(path):\n'
            "    # 读写统一 newline=''：原样保留，零转换\n"
            '    with open(path, "r", encoding="utf-8", newline="") as f:\n'
            '        src = f.read()\n'
            '    fixed = src.replace("old", "new")\n'
            '    with open(path, "w", encoding="utf-8", newline="") as f:\n'
            '        f.write(fixed)\n',
        "读侧 newline='' 保留原文件 \\r\\n，写侧 newline='\\r\\n' 会对"
            '内容中每个 \\n 再做一次转换——CRLF 文件被写成 \\r\\r\\n，'
            '换行全坏、py_compile 报超出行数 SyntaxError。读写两侧'
            "newline 必须同语义（统一 '' 或都不传）。",
        _WRITE_CHANNEL,
    ),
    make_code_ref(
        'robust', 'EF-01', 'Optional 函数 None 分支被无判空属性访问击穿', 'P1',
        'class ReportFormatter:\n'
            '    def render(self, items):\n'
            '        return "\\n".join(str(i) for i in items)\n'
            '\n'
            '\n'
            'def get_formatter(fmt):\n'
            '    if fmt == "text":\n'
            '        return ReportFormatter()\n'
            '    return None  # 空壳降级\n'
            '\n'
            '\n'
            'def build_report(fmt, items):\n'
            '    formatter = get_formatter(fmt)\n'
            '    return formatter.render(items)  # None 时 AttributeError\n',
        'class NullFormatter:\n'
            '    def render(self, items):\n'
            '        return ""\n'
            '\n'
            '\n'
            'class ReportFormatter:\n'
            '    def render(self, items):\n'
            '        return "\\n".join(str(i) for i in items)\n'
            '\n'
            '\n'
            'def get_formatter(fmt):\n'
            '    if fmt == "text":\n'
            '        return ReportFormatter()\n'
            '    return NullFormatter()  # 空对象而非 None\n'
            '\n'
            '\n'
            'def build_report(fmt, items):\n'
            '    formatter = get_formatter(fmt)\n'
            '    return formatter.render(items)\n',
        '可选依赖 fallback / 工厂函数返回 None 而非有效结果对象时，'
            '调用方直接 .attr 消费——降级分支必然 AttributeError。'
            '修复双通道：源头返回空对象（Null Object）；或调用方强制'
            'if result is None 分支。注意 except AttributeError 宽泛兜底'
            '会掩盖断裂，不算修复。',
        _WRITE_CHANNEL,
    ),
    make_code_ref(
        'robust', 'SF-01', '子进程超时静默回退进程内全量执行（内存爆满 P0 模式）', 'P0',
        'import subprocess\n'
            '\n'
            '\n'
            'def run_tests(cmd):\n'
            '    try:\n'
            '        out = subprocess.run(cmd, capture_output=True,\n'
            '                              timeout=90)  # 远小于真实耗时\n'
            '        return out.stdout.decode()\n'
            '    except subprocess.TimeoutExpired:\n'
            '        # 静默降级：无日志无 metrics\n'
            '        return _run_all_in_process(cmd)  # 全量 exec 进本进程\n',
        'import logging\n'
            'import subprocess\n'
            '\n'
            '\n'
            '_log = logging.getLogger(__name__)\n'
            '\n'
            '\n'
            'def run_tests(cmd, timeout_s):\n'
            '    # 超时预算由目标项目配置或调用方显式注入\n'
            '    if timeout_s <= 0:\n'
            '        raise ValueError("timeout_s 必须为正数")\n'
            '    try:\n'
            '        out = subprocess.run(cmd, capture_output=True,\n'
            '                              timeout=timeout_s)\n'
            '        status = "passed" if out.returncode == 0 else "failed"\n'
            '        return {"status": status, "output": out.stdout.decode(),\n'
            '                "reason": None if status == "passed" else "test_failure"}\n'
            '    except subprocess.TimeoutExpired:\n'
            '        # 显式降级：日志 + metrics 透传原因，不静默\n'
            '        _log.warning("pytest timeout=%ss, degraded", timeout_s)\n'
            '        return {"status": "error", "output": "",\n'
            '                "reason": "subprocess_timeout"}\n',
        '「子进程超时阈值 << 真实耗时 → 必然超时 → except 静默降级为'
            '进程内全量执行」是 P0 内存爆满缺陷模式：全量测试模块被 '
            'exec 进诊断进程，叠加 AST 缓存与注册表只增不减，RSS 直接'
            '爆满。四要点：超时阈值与目标项目真实耗时匹配，并由项目配置'
            '或调用方显式注入；降级产出明确降级结果（而非回退执行）；'
            '日志+metrics 透传降级原因；无 pytest 进程内分支加 RSS 熔断。'
            '子进程返回码必须映射 passed/failed，不得把“未超时”等同于测试通过。',
        (f"{anchor_module('prevention_write_refs')}"
         ' (纯编写前注入：需运行时超时观测，无静态检测器)'),
        self_verifiable=False,
    ),
    make_code_ref(
        'cvmethod', 'DK-01', '去重键缺行号维度：同规则多行 finding 被合并吞掉', 'P1',
        'def dedup_findings(findings):\n'
            '    seen = set()\n'
            '    kept = []\n'
            '    for f in findings:\n'
            '        key = f["rule_id"]  # BUG: 同规则不同行被合并\n'
            '        if key in seen:\n'
            '            continue\n'
            '        seen.add(key)\n'
            '        kept.append(f)\n'
            '    return kept\n',
        'def dedup_findings(findings):\n'
            '    seen = set()\n'
            '    kept = []\n'
            '    for f in findings:\n'
            '        # 兼容位置字段别名，仅 None 回退，保留合法行号/列号 0\n'
            '        line = f.get("line")\n'
            '        if line is None:\n'
            '            line = f.get("lineno")\n'
            '        file_path = f.get("file")\n'
            '        if file_path is None:\n'
            '            file_path = f.get("filepath")\n'
            '        column = f.get("col_offset")\n'
            '        if column is None:\n'
            '            column = f.get("column")\n'
            '        key = (f["rule_id"], line, file_path, column)\n'
            '        if key in seen:\n'
            '            continue\n'
            '        seen.add(key)\n'
            '        kept.append(f)\n'
            '    return kept\n',
        '对 finding 列表去重时键只取 rule_id——同一规则在多行/多文件'
            '的真实发现被合并成 1 条，任意项目的交叉验证与诊断结果都会'
            '静默缩水。去重键必须包含能区分「同一问题实例」的全部维度：'
            'rule_id + line + file + column（兼容 lineno/filepath/col_offset/column 别名）；'
            '别名只在原值为 None 时回退，不能用 or 把合法行号或列号 0 吞掉。',
        (f"{anchor_module('prevention_write_refs')}"
         ' (纯编写前注入：需 finding 语义，无静态检测器)'),
        self_verifiable=False,
    ),
]
WRITE_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    _WRITE_REFS, "WRITE_CODE_REFS")
register_code_refs(WRITE_CODE_REFS, 'prevention_write_refs')
_log.info(
    "prevention_write_refs:write 编写时预防库已注册完成：%d 条规则（%s），版本 %s",
    len(WRITE_CODE_REFS),
    ", ".join(
        f"{s}={len(series_rule_ids(WRITE_CODE_REFS, s))}"
        for s in sorted(series_names(WRITE_CODE_REFS)))
    or "空",
    WRITE_CODE_REFS_VERSION,
)
GUARDS_CODE_REFS_VERSION = "1.0.9"
_SERIES_GUARDQUALITY = "guardquality"
_SERIES_GUARD = "guard"
_SERIES_DQUALITY = "dquality"
_R_GQ = f"{anchor_module('diag_guard_source')} (guard_syntax/guard_docstring + 读源底座: G3/G8)"
_R_GQA = (f"{anchor_module('diag_guard_quality')} "
          "(guard_ast/guard_funcbody/guard_mro/guard_slots: G2/G6/G10/G11); "
          f"{anchor_module('diag_guard_source')} (guard_fstring: G7)")
_R_GS13 = f"{anchor_module('build_safe_orchestration')} (guard_default_deny: G13)"
_R_GS16 = f"{anchor_module('build_safe_write')} (guard_path_sanitize: G16)"
_R_GS17 = f"{anchor_module('diag_guard_source')} (guard_size_limit: G17)"
_R_GS26 = f"{anchor_module('build_safe_write')} (guard_safe_delete: G26)"
_R_GSL = (f"{anchor_module('build_safe_orchestration')} "
          "(guard_throttle/guard_idempotency/guard_diag_trail/guard_intent_confirm: "
          "G15/G18/G19/G22)")
_R_GS21 = f"{anchor_module('build_safe_write')} (guard_post_verify: G21)"
_R_GQ_DICTRET = f"{anchor_module('diag_guard_quality')} (guard_dictret: G9)"
_R_GQ_STATE = (f"{anchor_module('diag_guard_quality')} "
               "(guard_concurrent_state/guard_recursion_depth: G25/G27)")
_R_GIO_CONTENT = f"{anchor_module('diag_guard_source')} (guard_content_diag: G14)"
_R_GSR_SIDEFX = (f"{anchor_module('build_import_time_guard')} "
                 "(guard_import_side_effect/guard_atexit_register: G28/G29)")
_R_CQ = (f"{anchor_module('diag_traps_coding')}.check_CQ02 "
         "(CQ-02 / DetectorRegistry); "
         f"{anchor_module('diag_detectors_registry')}"
         ".preflight_diagnostic_check (Gate5)")
_GUARDQUALITY_REFS: list[CodeRef] = [
make_code_ref(
    _SERIES_GUARDQUALITY, 'G6', '函数体完整性（修改后函数意外丢失/pass 残留）', 'P1',
    '# 反例：修复中 process 函数被误删（未声明删除），run_all 残留 pass\n'
    'def helper(x):\n'
    '    return x * 2\n'
    '\n'
    'def run_all(items):\n'
    '    # process 函数整体丢失（修改前后函数清单对比检出意外丢失）\n'
    '    pass\n'
    '    return [helper(i) for i in items]\n',
    '# 正例：修改保持函数定义完整，无 pass 残留，嵌套层级不变\n'
    'def process(data):\n'
    '    cleaned = [x.strip() for x in data if x]\n'
    '    return cleaned\n'
    '\n'
    'def helper(x):\n'
    '    return x * 2\n'
    '\n'
    'def run_all(items):\n'
    '    processed = process(items)\n'
    '    return [helper(i) for i in processed]\n',
    'pass 占位修复若未恢复，AST 函数数量对比会检出「函数意外丢失」；'
    '同名函数被嵌套（缩进破坏）会形成遮蔽。修改后必须核对函数清单与层级。',
    _R_GQA,
),
make_code_ref(
    _SERIES_GUARDQUALITY, 'G7', 'f-string 空花括号与变量引用丢失', 'P1',
    '# 反例：f-string 插值段连同变量名被整体误删，插值静默丢失\n'
    'def render(user, count):\n'
    '    msg = f"Hello , you have items"  # {user} 与 {count} 丢失\n'
    '    return msg\n',
    '# 正例：f-string 花括号内变量完整\n'
    'def render(user, count):\n'
    '    msg = f"Hello {user}, you have {count} items"\n'
    '    return msg\n',
    '插值段连同变量名被误删后输出静默残缺，无异常无告警；修改前后 '
    'f-string 变量计数减少指示变量名被误删（guard_fstring 对比通道）。'
    '真空花括号 f"{}" 本身即 SyntaxError，无法作为语法合法代码静默'
    '存在，guard_fstring 仅在 parse 失败时以文本扫描定位该病因。'
    'AI 批量改码后必须逐个核对插值变量。',
    _R_GQA,
),
make_code_ref(
    _SERIES_GUARDQUALITY, 'G8', 'docstring 三引号边界破坏', 'P1',
    '# 反例：docstring 被挤到函数体中间，开始三引号前是普通代码行（孤立开始符）\n'
    'def load(path):\n'
    '    total = 0\n'
    '    """\n'
    '    加载配置文件，\n'
    '    返回解析后的 dict 对象。\n'
    '    """\n'
    '    return _parse(path)\n',
    '# 正例：docstring 三引号严格成对（单行写法闭合同行，避免孤立结束符）\n'
    'def load(path):\n'
    '    """加载配置文件，返回路径与内容长度的 dict 对象。"""\n'
    '    with open(path, encoding="utf-8") as f:\n'
    '        return {"path": path, "size": len(f.read())}\n',
    '三引号不闭合会把后续代码吞进字符串（语法错或静默改变语义）；pass 替换'
    'docstring 开头、孤立开始/结束符是批量改码的高发破坏模式，写盘前必须'
    '统计三引号配对。',
    _R_GQ,
),
make_code_ref(
    _SERIES_GUARDQUALITY, 'G9', '字典返回完整性（计算了变量却返回空字典）', 'P2',
    '# 反例：函数计算了 result 却 return {}，调用方拿到空结果\n'
    'def summarize(rows):\n'
    '    total = sum(r["value"] for r in rows)\n'
    '    count = len(rows)\n'
    '    result = {"total": total, "count": count}\n'
    '    return {}  # 忘记返回 result\n',
    '# 正例：计算结果完整放入返回字典\n'
    'def summarize(rows):\n'
    '    total = sum(r["value"] for r in rows)\n'
    '    count = len(rows)\n'
    '    return {"total": total, "count": count}\n',
    'AI 重构时常保留计算语句却把 return 改成 {}；空字典是合法返回值，'
    '不报错但功能全失。重构后必须对比修改前后 return 字典的键集合。',
    _R_GQ_DICTRET,
),
make_code_ref(
    _SERIES_GUARDQUALITY, 'G10', 'MRO 链（重复基类 / Mixin 未调 super().__init__）', 'P2',
    '# 反例：Mixin 定义 __init__ 却不调用 super().__init__()，\n'
    '# 阻断协作式多重继承链，后续基类初始化被吞\n'
    'class BaseService:\n'
    '    def __init__(self):\n'
    '        self.base_ready = True\n'
    '\n'
    'class LoggerMixin:\n'
    '    def __init__(self):\n'
    '        self.log = []  # 缺 super().__init__()，MRO 链断裂\n'
    '\n'
    'class Service(LoggerMixin, BaseService):\n'
    '    def __init__(self, name):\n'
    '        super().__init__()  # BaseService.__init__ 被 Mixin 截断\n'
    '        self.name = name\n',
    '# 正例：Mixin 遵循协作式多重继承，__init__ 首行调用 super().__init__()\n'
    'class BaseService:\n'
    '    def __init__(self):\n'
    '        self.base_ready = True\n'
    '\n'
    'class LoggerMixin:\n'
    '    def __init__(self):\n'
    '        super().__init__()\n'
    '        self.log = []\n'
    '\n'
    'class Service(LoggerMixin, BaseService):\n'
    '    def __init__(self, name):\n'
    '        super().__init__()\n'
    '        self.name = name\n',
    'Mixin 不调 super().__init__() 会截断 MRO 协作链，组合类中位于其后'
    '的基类初始化被静默跳过；重复基类则直接 TypeError（无法创建 MRO）。',
    _R_GQA,
),
make_code_ref(
    _SERIES_GUARDQUALITY, 'G11', '__slots__ 声明完整性', 'P2',
    '# 反例：声明了 __slots__ 但 __init__ 设置了未声明的属性\n'
    'class Point:\n'
    '    __slots__ = ("x",)\n'
    '\n'
    '    def __init__(self, x, y):\n'
    '        self.x = x\n'
    '        self.y = y  # y 未在 __slots__ 中声明，AttributeError\n',
    '# 正例：__slots__ 覆盖 __init__ 设置的全部属性\n'
    'class Point:\n'
    '    __slots__ = ("x", "y")\n'
    '\n'
    '    def __init__(self, x, y):\n'
    '        self.x = x\n'
    '        self.y = y\n',
    '__slots__ 生成的类没有 __dict__，未声明的属性赋值直接 AttributeError；'
    '空 __slots__ = () 同样要求 __init__ 不设任何实例属性。',
    _R_GQA,
),
]
_GUARD_REFS: list[CodeRef] = [
make_code_ref(
    _SERIES_GUARD, 'G13', '默认拒绝（路径/命令黑白名单）', 'P0',
    '# 反例：操作任意路径、拼接黑名单命令，绕过白名单校验\n'
    'import os\n'
    '\n'
    'def hard_reset(target):\n'
    '    os.system(f"rm -rf {target}")  # 黑名单命令\n'
    '    with open("/etc/hosts", "w") as f:  # 黑名单路径\n'  # jwsgj:suppress SS-02
    '        f.write("")\n',
    '# 正例：目标项目显式提供授权根，真实路径按目录边界校验\n'
    'import os\n'
    '\n'
    'def _within(root, path):\n'
    '    try:\n'
    '        return os.path.commonpath((root, path)) == root\n'
    '    except ValueError:  # 跨盘符路径不属于同一授权根\n'
    '        return False\n'
    '\n'
    'def _assert_safe(path, safe_roots):\n'
    '    candidate = os.path.normcase(os.path.realpath(path))\n'
    '    roots = tuple(os.path.normcase(os.path.realpath(root))\n'
    '                  for root in safe_roots)\n'
    '    if not roots:\n'
    '        raise PermissionError("目标项目未声明任何授权根")\n'
    '    if not any(_within(root, candidate) for root in roots):\n'
    '        raise PermissionError(f"路径不在白名单内: {path}")\n'
    '    return candidate\n'
    '\n'
    'def clean_output(target, safe_roots):\n'
    '    checked = _assert_safe(target, safe_roots)\n'
    '    return {"target": checked, "allowed": True}\n',
    '默认拒绝原则：不在白名单内的路径/命令一律拒绝。授权根必须由目标项目'
    '或调用方显式提供，不能使用工具预设目录名代替项目授权。路径先做 realpath '
    '与 normcase 归一化，再按目录边界判断是否位于白名单根内；仅出现同名目录段'
    '或字符串前缀不构成授权，防止相似目录名、上跳与符号链接绕过。',
    _R_GS13,
),
make_code_ref(
    _SERIES_GUARD, 'G14', '危险模式扫描（写盘前内容检查）', 'P0',
    '# 反例：写入前未扫描危险模式，eval/提权/敏感信息直接落盘\n'
    'def run_plugin(code, cfg):\n'
    '    result = eval(code)  # 动态执行任意代码\n'
    '    password = cfg["password"]  # 明文敏感信息\n'
    '    import os\n'
    '    os.system("sudo chmod 777 /data")  # 提权 + 危险权限\n'
    '    return result\n',
    '# 正例：动态能力用受限通道，敏感字段脱敏，权限操作走白名单\n'
    'import ast\n'
    'import operator\n'
    '\n'
    'ALLOWED_NODES = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Constant,\n'
    '                 ast.Load, ast.Add, ast.Sub, ast.Mult, ast.Div,\n'
    '                 ast.FloorDiv, ast.Mod, ast.UAdd, ast.USub)\n'
    'BIN_OPS = {ast.Add: operator.add, ast.Sub: operator.sub,\n'
    '           ast.Mult: operator.mul, ast.Div: operator.truediv,\n'
    '           ast.FloorDiv: operator.floordiv, ast.Mod: operator.mod}\n'
    'UNARY_OPS = {ast.UAdd: operator.pos, ast.USub: operator.neg}\n'
    '\n'
    'def _eval_node(node):\n'
    '    if isinstance(node, ast.Expression):\n'
    '        return _eval_node(node.body)\n'
    '    if isinstance(node, ast.Constant):\n'
    '        if type(node.value) not in (int, float):\n'
    '            raise ValueError("只允许数值常量")\n'
    '        return node.value\n'
    '    if isinstance(node, ast.BinOp):\n'
    '        return BIN_OPS[type(node.op)](_eval_node(node.left),\n'
    '                                       _eval_node(node.right))\n'
    '    if isinstance(node, ast.UnaryOp):\n'
    '        return UNARY_OPS[type(node.op)](_eval_node(node.operand))\n'
    '    raise ValueError(f"不允许的表达式节点: {type(node).__name__}")\n'
    '\n'
    'def run_plugin(expr, cfg):\n'
    '    if len(expr) > 256:\n'
    '        raise ValueError("表达式超过长度限制")\n'
    '    tree = ast.parse(expr, mode="eval")\n'
    '    for node in ast.walk(tree):\n'
    '        if not isinstance(node, ALLOWED_NODES):\n'
    '            raise ValueError(f"不允许的表达式节点: {type(node).__name__}")\n'
    '    value = _eval_node(tree)\n'
    '    has_token = bool(cfg.get("token"))\n'
    '    return {"value": value, "token_present": has_token}\n',
    '写盘前内容级扫描拦截五类危险模式：危险系统调用（eval/exec/os.system）、'
    '文件系统破坏（rm -rf/rmtree）、网络下载执行（curl|sh）、权限提升'
    '（sudo/chmod 777）、敏感信息明文（password=/api_key=）。受限表达式只接受数值运算，'
    '限制输入长度且不支持幂运算，防止动态求值自身成为资源耗尽入口。',
    _R_GIO_CONTENT,
),
make_code_ref(
    _SERIES_GUARD, 'G15', '操作熔断（次数/删除/超时/频率上限）', 'P1',
    '# 反例：循环内无计数无间隔，刷屏式连续触发文件操作直至失控\n'
    'import os\n'
    '\n'
    'def sync_all(files):\n'
    '    for f in files:\n'
    '        os.replace(f + ".tmp", f)  # 连续数百次无熔断无间隔\n',
    '# 正例：项目注入计数、间隔与超时预算，超限即熔断\n'
    'import os\n'
    'import time\n'
    '\n'
    'def _check_deadline(started, max_task_seconds, delay=0.0):\n'
    '    if time.monotonic() - started + delay > max_task_seconds:\n'
    '        raise TimeoutError(f"任务超过 {max_task_seconds}s，已熔断")\n'
    '\n'
    'def sync_all(files, max_ops, min_interval, max_task_seconds):\n'
    '    if min(max_ops, max_task_seconds) <= 0 or min_interval < 0:\n'
    '        raise ValueError("熔断预算必须为正数，间隔不得为负")\n'
    '    started = time.monotonic()\n'
    '    done = 0\n'
    '    for f in files:\n'
    '        _check_deadline(started, max_task_seconds)\n'
    '        if done >= max_ops:\n'
    '            raise RuntimeError(f"操作次数达上限 {max_ops}，任务熔断")\n'
    '        _check_deadline(started, max_task_seconds, delay=min_interval)\n'
    '        time.sleep(min_interval)\n'
    '        _check_deadline(started, max_task_seconds)\n'
    '        os.replace(f + ".tmp", f)\n'
    '        done += 1\n'
    '    _check_deadline(started, max_task_seconds)\n'
    '    return done\n',
    '批量任务必须带操作次数、频率与总耗时熔断，具体预算由目标项目的操作'
    '风险、资源容量和合规要求决定，不能将固定次数或固定秒数强加给所有项目。'
    '计划等待必须计入截止时间，等待后、副作用前再次检查，避免超时后仍写盘。'
    '无熔断的循环在异常输入下会指数放大破坏面（如递归目录全删）。',
    _R_GSL,
),
make_code_ref(
    _SERIES_GUARD, 'G16', '路径净化（.. 越权/符号链接逃逸/工作区外）', 'P0',
    '# 反例：拼接用户输入不净化，.. 越权 + 符号链接逃逸出工作区\n'
    'import os\n'
    '\n'
    'def read_report(name):\n'
    '    path = os.path.join("reports", name)  # name="../../etc/passwd"\n'  # jwsgj:suppress SS-02,供应链安全-敏感路径
    '    with open(path, encoding="utf-8") as f:\n'
    '        return f.read()\n',
    '# 正例：调用方传入项目授权根，realpath 归一并按目录边界校验\n'
    'import os\n'
    '\n'
    'def read_report(workspace, name):\n'
    '    if not workspace:\n'
    '        raise ValueError("必须显式提供项目授权根")\n'
    '    workspace = os.path.normcase(os.path.realpath(workspace))\n'
    '    if ".." in str(name).replace("\\\\", "/").split("/"):\n'
    '        raise ValueError("路径包含 .. 越权段")\n'
    '    reports_root = os.path.normcase(os.path.realpath(\n'
    '        os.path.join(workspace, "reports")))\n'
    '    path = os.path.normcase(os.path.realpath(os.path.join(reports_root, name)))\n'
    '    try:\n'
    '        within_workspace = os.path.commonpath((workspace, path)) == workspace\n'
    '        within_reports = os.path.commonpath((reports_root, path)) == reports_root\n'
    '    except ValueError:  # 跨盘符路径按越界处理\n'
    '        within_workspace = False\n'
    '        within_reports = False\n'
    '    if not (within_workspace and within_reports):\n'
    '        raise PermissionError(f"路径逃逸出 reports 授权目录: {path}")\n'
    '    with open(path, encoding="utf-8") as f:\n'
    '        return f.read()\n',
    '.. 路径段可跳出受限目录；符号链接可指向工作区外（realpath 解析后才'
    '判等）。授权根应由目标项目配置或调用方显式提供，缺失时拒绝而不是回退'
    'cwd，也不绑定某个环境变量名。所有面向外部的路径必须净化并校验落在'
    '授权根内；read_report 还必须落在 reports 子目录，因为绝对路径会覆盖 '
    'os.path.join 的前缀，只检查 workspace 会放行工作区内其他敏感文件。',
    _R_GS16,
),
make_code_ref(
    _SERIES_GUARD, 'G17', '文件大小限制（写入前体积校验）', 'P1',
    '# 反例：把全部结果拼成单个巨型文件写盘，无体积检查\n'
    'def dump_everything(records):\n'
    '    lines = [f"{r}" for r in records]  # 可能数十万行\n'
    '    with open("all_output.py", "w", encoding="utf-8") as f:\n'
    '        f.write("\\n".join(lines))  # 单文件超 5000 逻辑行/10MB\n',
    '# 正例：写盘前按行数/UTF-8 字节数分片，并校验文件数与总量\n'
    'def dump_everything(records, chunk_name="all_output", *, max_lines,\n'
    '                    max_bytes, max_files, max_total_bytes):\n'
    '    budgets = (max_lines, max_bytes, max_files, max_total_bytes)\n'
    '    if any(value <= 0 for value in budgets):\n'
    '        raise ValueError("体积预算必须由项目提供且全部为正数")\n'
    '    lines = [f"{r}" for r in records]\n'
    '    if any("\\n" in line or "\\r" in line for line in lines):\n'
    '        raise ValueError("单条记录不得包含换行符，否则无法保证行数预算")\n'
    '    sizes = [len(line.encode("utf-8")) for line in lines]\n'
    '    parts = []\n'
    '    part_sizes = []\n'
    '    part = []\n'
    '    part_bytes = 0\n'
    '    for line, size in zip(lines, sizes):\n'
    '        if size > max_bytes:\n'
    '            raise ValueError(f"单条记录超过项目预算 {max_bytes} 字节")\n'
    '        if part and (len(part) >= max_lines\n'
    '                     or part_bytes + 1 + size > max_bytes):\n'
    '            parts.append(part)\n'
    '            part_sizes.append(part_bytes)\n'
    '            part = []\n'
    '            part_bytes = 0\n'
    '        if part:\n'
    '            part_bytes += 1  # 仅实际存在的 join 分隔符计一个字节\n'
    '        part.append(line)\n'
    '        part_bytes += size\n'
    '    if part:\n'
    '        parts.append(part)\n'
    '        part_sizes.append(part_bytes)\n'
    '    if sum(part_sizes) > max_total_bytes:\n'
    '        raise ValueError(f"任务总输出超过项目预算 {max_total_bytes} 字节")\n'
    '    if len(parts) > max_files:\n'
    '        raise ValueError(f"任务输出超过项目预算 {max_files} 个文件")\n'
    '    written = []\n'
    '    for idx, part in enumerate(parts, 1):\n'
    '        name = f"{chunk_name}_{idx}.txt" if len(parts) > 1 else f"{chunk_name}.txt"\n'
    '        with open(name, "w", encoding="utf-8", newline="") as f:\n'
    '            f.write("\\n".join(part))\n'
    '        written.append(name)\n'
    '    return written\n',
    '单文件、文件数与任务总量预算必须由目标项目按存储容量、部署限制和'
    '业务负载显式提供，不能将固定 MB、行数或文件数作为所有项目的通用上限。'
    '分片必须同时按 UTF-8 编码后的真实字节数与行数计算，换行符只在实际'
    '写入时计数；每条记录限定为一个物理行，含换行的记录直接拒绝，防止'
    '记录内换行绕过行数预算；任一条目或任务总量超限即拒绝。',
    _R_GS17,
),
make_code_ref(
    _SERIES_GUARD, 'G18', '诊断追踪（危险操作可追溯）', 'P2',
    '# 反例：执行删除/修改但不留任何上下文，事后无法追溯\n'
    'import os\n'
    '\n'
    'def cleanup():\n'
    '    os.remove("cache.bin")  # 无目标记录、无 before 快照、无审计日志\n',
    '# 正例：操作前后生成内容哈希快照，验证消失后写审计结果\n'
    'import hashlib\n'
    'import logging\n'
    'import os\n'
    '\n'
    'log = logging.getLogger(__name__)\n'
    '\n'
    'def _snapshot(path):\n'
    '    if not os.path.exists(path):\n'
    '        return {"exists": False}\n'
    '    with open(path, "rb") as handle:\n'
    '        payload = handle.read()\n'
    '    return {"exists": True, "size": len(payload),\n'
    '            "sha256": hashlib.sha256(payload).hexdigest()}\n'
    '\n'
    'def cleanup(target, safe_delete):\n'
    '    # 删除能力由目标项目注入，本示例不绑定具体工具实现\n'
    '    before = _snapshot(target)\n'
    '    log.info("cleanup target=%s before=%s", target, before)\n'
    '    if not before["exists"]:\n'
    '        after = _snapshot(target)\n'
    '        result = {"target_path": target, "affected_files": [],\n'
    '                  "before": before, "after": after, "removed": False}\n'
    '        log.info("cleanup skipped target=%s reason=not_found", target)\n'
    '        return result\n'
    '    if not safe_delete(target):\n'
    '        raise RuntimeError("安全删除失败，不得报告成功")\n'
    '    after = _snapshot(target)\n'
    '    if after["exists"]:\n'
    '        raise RuntimeError("删除后目标仍存在，不得报告成功")\n'
    '    result = {"target_path": target, "affected_files": [target],\n'
    '              "before": before, "after": after, "removed": True}\n'
    '    log.info("cleanup done target=%s removed=%s", target, result["removed"])\n'
    '    return result\n',
    '删除/修改/重构等危险操作必须留下 target_path、affected_files 与'
    'before/after 快照，才能在事后复盘点检「谁改了什么、改前什么样」。'
    '缺快照的操作一旦出错无从回滚定位。实际删除函数由目标项目显式注入，'
    '示例只约定其成功返回真值、失败返回假值，不依赖特定工具包。',
    _R_GSL,
),
make_code_ref(
    _SERIES_GUARD, 'G19', '操作意图确认（范围/预期结果/目标歧义）', 'P2',
    '# 反例：模糊目标直接执行，无法评估影响范围\n'
    'import shutil\n'
    '\n'
    'def tidy(pattern):\n'
    '    shutil.rmtree(pattern)  # 通配符/歧义目标，范围未界定\n',
    '# 正例：先界定范围、声明预期结果与理由，确认后再执行\n'
    'import os\n'
    '\n'
    'def tidy(target, expected_outcome, reason):\n'
    '    if "*" in target or "?" in target:\n'
    '        raise ValueError(f"目标含通配符，歧义拒绝: {target}")\n'
    '    if not os.path.isdir(target):\n'
    '        raise NotADirectoryError(target)\n'
    '    plan = {"target": target, "expected_outcome": expected_outcome,\n'
    '            "reason": reason, "scope": [os.path.join(target, f)\n'
    '            for f in os.listdir(target)]}\n'
    '    return plan  # 确认 plan 后再委托安全删除通道执行\n',
    '执行前必须可回答三个问题：影响哪些文件（范围）、成功长什么样（预期'
    '结果）、为什么要做（理由）。目标含通配符或类型不匹配（目录当文件删）'
    '是 AI 误操作的高频形态。',
    _R_GSL,
),
make_code_ref(
    _SERIES_GUARD, 'G21', '操作后结果校验（防执行幻觉）', 'P1',
    '# 反例：写完不校验，声称成功但实际写入失败/内容未变\n'
    'def apply_fix(path, new_content):\n'
    '    with open(path, "w", encoding="utf-8") as f:\n'
    '        f.write(new_content)\n'
    '    return "done"  # 无校验：文件可能没变、预期片段可能缺失\n',
    '# 正例：读回全文必须与预期一致，再核对变化与预期片段\n'
    'import os\n'
    '\n'
    'def apply_fix(path, new_content, expected_marker):\n'
    '    before = None\n'
    '    if os.path.exists(path):\n'
    '        with open(path, encoding="utf-8", newline="") as f:\n'
    '            before = f.read()\n'
    '    with open(path, "w", encoding="utf-8", newline="") as f:\n'
    '        f.write(new_content)\n'
    '    with open(path, encoding="utf-8", newline="") as f:\n'
    '        after = f.read()\n'
    '    if after != new_content:\n'
    '        raise RuntimeError("读回内容与预期写入不一致，不得报告成功")\n'
    '    if after == before:\n'
    '        raise RuntimeError("写入前后内容一致，不得报告已修改")\n'
    '    if expected_marker not in after:\n'
    '        raise RuntimeError(f"写入后缺少预期内容: {expected_marker}")\n'
    '    return {"path": path, "size": len(after),\n'
    '            "changed": True, "verified": True}\n',
    'Agent 幻觉执行的高发形态：声称已修改但文件内容与修改前完全一致、'
    '声称已删除但文件仍存在。操作后必须读回校验（内容已变 + 包含预期'
    '片段 + 目标状态正确），且读回全文必须与预期写入一致；读写统一 newline=""，'
    '禁止换行二次转换，否则不能报告成功。',
    _R_GS21,
),
make_code_ref(
    _SERIES_GUARD, 'G22', '幂等性（重复操作/幂等标记/删除不存在目标）', 'P2',
    '# 反例：重复执行无检测，重复删除不存在的目标\n'
    'import os\n'
    '\n'
    'def remove_cache(path):\n'
    '    os.remove(path)  # 目标可能已删除（幻觉重复执行），直接 FileNotFoundError\n',
    '# 正例：先探测存在性，已删除视为成功（幂等语义）\n'
    'import os\n'
    '\n'
    'def remove_cache(path):\n'
    '    if not os.path.exists(path):\n'
    '        return {"path": path, "status": "already_gone"}\n'
    '    return {"path": path, "status": "ready",\n'
    '            "size": os.path.getsize(path)}  # 确认后委托安全删除通道\n',
    '重复操作（同目标短时间内多次操作）指示执行循环失控或幻觉重放；删除'
    '已不存在的目标是典型幻觉信号。操作应设计为幂等：重复执行结果一致，'
    '目标不存在时安静返回成功。',
    _R_GSL,
),
make_code_ref(
    _SERIES_GUARD, 'G25', '并发状态（模块级可变全局无锁修改）', 'P2',
    '# 反例：模块级全局缓存在回调/多线程路径上无锁修改\n'
    '_GLOBAL_CACHES = set()\n'
    '\n'
    'def register(key):\n'
    '    _GLOBAL_CACHES.add(key)  # 多线程并发 add 竞态，可能丢注册\n'
    '\n'
    'def dispatch(event):\n'
    '    for k in list(_GLOBAL_CACHES):  # 迭代中并发 add 触发 RuntimeError\n'
    '        handle(k, event)\n'
    '\n'
    'def handle(k, event):\n'
    '    return k, event\n',
    '# 正例：锁内读当前快照 → 局部容器合并 → 一次性整体替换全局，\n'
    '# 迭代方消费不可变快照；既免迭代竞态又保证注册累积语义\n'
    'import threading\n'
    '\n'
    '_LOCK = threading.Lock()\n'
    '_GLOBAL_CACHES = frozenset()\n'
    '\n'
    'def register(key):\n'
    '    global _GLOBAL_CACHES\n'
    '    with _LOCK:\n'
    '        merged = set(_GLOBAL_CACHES)  # 锁内读当前快照\n'
    '        merged.add(key)  # 局部容器内完成修改\n'
    '        _GLOBAL_CACHES = frozenset(merged)  # 一次性整体替换\n'
    '        return _GLOBAL_CACHES\n'
    '\n'
    'def dispatch(event):\n'
    '    snapshot = _GLOBAL_CACHES  # 取不可变快照，无竞态\n'
    '    for k in snapshot:\n'
    '        handle(k, event)\n'
    '\n'
    'def handle(k, event):\n'
    '    return k, event\n',
    '模块级 set/dict/list 在多线程（含 pytest-xdist、守护线程回调）下的'
    '原地修改是竞态源头，迭代中修改直接 RuntimeError。优先局部容器改完'
    '一次性赋值（或 frozenset 不可变快照）；确需原地修改时用 Lock 包住'
    '读写两端。',
    _R_GQ_STATE,
),
make_code_ref(
    _SERIES_GUARD, 'G26', '安全删除（非安全路径禁删）', 'P0',
    '# 反例：直接删除源码/配置等非安全路径文件\n'
    'import os\n'
    '\n'
    'def drop_module(mod_name):\n'
    '    os.remove(f"{mod_name}.py")  # 源码 .py 直接删除，不可恢复\n',
    '# 正例：目标项目显式提供授权根、临时目录与可删除形态\n'
    'import os\n'
    '\n'
    'def _within(root, path):\n'
    '    try:\n'
    '        return os.path.commonpath((root, path)) == root\n'
    '    except ValueError:\n'
    '        return False\n'
    '\n'
    'def drop_artifact(path, workspace, temp_roots, cache_names, safe_suffixes):\n'
    '    if not workspace:\n'
    '        raise ValueError("必须显式提供项目授权根")\n'
    '    workspace = os.path.normcase(os.path.realpath(workspace))\n'
    '    candidate = os.path.normcase(os.path.realpath(path))\n'
    '    roots = tuple(os.path.normcase(os.path.realpath(root))\n'
    '                  for root in temp_roots)\n'
    '    in_temp = any(_within(root, candidate) for root in roots)\n'
    '    within_workspace = _within(workspace, candidate)\n'
    '    relative_parts = (set(os.path.relpath(candidate, workspace).split(os.sep))\n'
    '                      if within_workspace else set())\n'
    '    in_cache = bool(set(cache_names) & relative_parts)\n'
    '    safe_shape = in_temp or in_cache or candidate.endswith(tuple(safe_suffixes))\n'
    '    if not within_workspace or not safe_shape:\n'
    '        raise PermissionError(f"非安全路径拒绝删除: {path}")\n'
    '    if os.path.isdir(candidate):\n'
    '        raise IsADirectoryError(f"目录删除须逐项校验: {candidate}")\n'
    '    return {"path": candidate, "checked": True,\n'
    '            "size": os.path.getsize(candidate)}  # 校验后委托安全删除\n',
    '删除是不可逆操作：目标必须位于目标项目显式声明的授权根内，且符合项目'
    '提供的临时目录、缓存目录名或安全后缀策略。不能预设 Temp、__pycache__'
    '或固定环境变量适用于所有项目；相似目录名子串与授权根外绝对路径均不'
    '授权。源码 .py 的删除必须走有导入者校验与版本控制的流程。',
    _R_GS26,
),
make_code_ref(
    _SERIES_GUARD, 'G27', '递归深度（无保护的递归）', 'P2',
    '# 反例：无深度上限也无 RecursionError 捕获，畸形输入直接栈溢出\n'
    'def walk_tree(node):\n'
    '    results = [node["name"]]\n'
    '    for child in node.get("children", []):\n'
    '        results.extend(walk_tree(child))  # 环状数据 = 无限递归\n'
    '    return results\n',
    '# 正例：显式 max_depth 参数，超限转迭代或截断\n'
    'def walk_tree(node, max_depth=100):\n'
    '    results = [node["name"]]\n'
    '    if max_depth <= 0:\n'
    '        raise ValueError("递归深度超限，数据可能含环")\n'
    '    for child in node.get("children", []):\n'
    '        results.extend(walk_tree(child, max_depth - 1))\n'
    '    return results\n',
    '环状引用数据会让无保护递归瞬间打爆调用栈（RecursionError 崩溃进程）；'
    '递归函数必须带 max_depth 参数或捕获 RecursionError 兜底，深层结构'
    '改用显式栈迭代。',
    _R_GQ_STATE,
),
make_code_ref(
    _SERIES_GUARD, 'G28', 'import 副作用（__init__.py 模块级 I/O）', 'P1',
    '# 反例：__init__.py 顶层做 I/O，任何 import 都触发目录创建\n'
    'import os\n'
    '\n'
    'os.makedirs("runtime/cache", exist_ok=True)  # 模块级副作用\n'
    '\n'
    'from .core import Engine  # noqa: E402\n',
    '# 正例：I/O 移入函数延迟执行，import 零副作用\n'
    'import os\n'
    '\n'
    'from .core import Engine\n'
    '\n'
    'def ensure_cache():\n'
    '    os.makedirs("runtime/cache", exist_ok=True)\n'
    '    return "runtime/cache"\n'
    '\n'
    'def build_engine():\n'
    '    # 构造延迟到调用点，导入期只做名字绑定\n'
    '    return Engine()\n',
    '__init__.py 模块级的 open/makedirs/remove 等调用在「任何一次 import」'
    '时执行（包括文档收集、类型检查、打包扫描），污染只读环境并放大故障面。'
    'I/O 一律延迟到显式函数调用。',
    _R_GSR_SIDEFX,
),
make_code_ref(
    _SERIES_GUARD, 'G29', 'atexit 注册（无防重入标志）', 'P3',
    '# 反例：每次调用都注册，重复导入/多次调用导致清理函数堆积执行多次\n'
    'import atexit\n'
    '\n'
    'def setup():\n'
    '    atexit.register(flush_cache)  # 无防重入，重复注册\n'
    '\n'
    'def flush_cache():\n'
    '    pass\n',
    '# 正例：同一模块实例内用锁包裹检查与注册，重复/并发调用只注册一次\n'
    'import atexit\n'
    'import threading\n'
    '\n'
    '_REGISTER_LOCK = threading.Lock()\n'
    '_REGISTERED = False\n'
    '\n'
    'def setup():\n'
    '    global _REGISTERED\n'
    '    with _REGISTER_LOCK:\n'
    '        if not _REGISTERED:\n'
    '            atexit.register(flush_cache)\n'
    '            _REGISTERED = True\n'
    '\n'
    'def flush_cache():\n'
    '    """落盘待写缓冲；无缓冲时也返回可校对的统计。"""\n'
    '    return {"written": 0, "flushed": True}\n',
    'atexit.register 无防重入保护时，同一模块实例内 setup 被重复或并发调用'
    '会让清理函数重复执行（重复写盘/重复删除）。用锁包住状态检查与注册'
    '才构成完整的防重入临界区；独立重复导入须由应用统一注册所有者。',
    _R_GSR_SIDEFX,
),
]
_DQUALITY_REFS: list[CodeRef] = [
make_code_ref(
    _SERIES_DQUALITY, 'CQ-02', '业务逻辑代码使用 assert', 'P1',
    '# 反例：业务代码用 assert 做校验，python -O 下整段被剥离\n'
    'def transfer(account, amount):\n'
    '    assert amount > 0, "转账金额必须为正数且不允许为零或负数，请检查入参"  # -O 下静默失效\n'
    '    assert account.balance >= amount, "账户余额不足以完成本次转账，请先充值后再试"\n'
    '    account.balance -= amount\n'
    '    return account.balance\n',
    '# 正例：业务校验用显式 if/raise，任何运行模式下都生效\n'
    'def transfer(account, amount):\n'
    '    if amount <= 0:\n'
    '        raise ValueError(f"转账金额必须为正数: {amount}")\n'
    '    if account.balance < amount:\n'
    '        raise ValueError(f"余额不足: {account.balance} < {amount}")\n'
    '    account.balance -= amount\n'
    '    return account.balance\n',
    'assert 语句在 python -O / -OO 优化模式下被整体剥离，业务校验静默'
    '失效（资金/权限类校验尤其致命）。assert 仅限测试代码使用，业务逻辑'
    '一律显式 if + raise。',
    _R_CQ,
),
]
GUARDS_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    [*_GUARDQUALITY_REFS, *_GUARD_REFS, *_DQUALITY_REFS],
    "GUARDS_CODE_REFS",
)
register_code_refs(GUARDS_CODE_REFS, "prevention_write_refs:guards")
_log.info(
    "prevention_write_refs:guards 守卫域预防库已注册完成：%d 条规则（%s），版本 %s",
    len(GUARDS_CODE_REFS),
    ", ".join(
        f"{s}={len(series_rule_ids(GUARDS_CODE_REFS, s))}"
        for s in sorted(series_names(GUARDS_CODE_REFS)))
    or "空",
    GUARDS_CODE_REFS_VERSION,
)
