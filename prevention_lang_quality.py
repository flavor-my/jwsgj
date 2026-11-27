from __future__ import annotations  # noqa: I001
import logging
from jwsgj.prevention_refs_main import (
    DETECTOR_REF_ARTIFACT,
    DETECTOR_REF_QUALITY,
    DETECTOR_REF_RECOVERED,
    DETECTOR_REF_SECURITY,
    DETECTOR_REF_STRING_JSON,
    CodeRef,
    anchor_module,
    make_code_ref,
)
__all__ = [
    'BUG_REFS',
    'FILEOPS_REFS',
    'IMPORTEXTRA_REFS',
    'PYTRAP_REFS',
    'SERIES_BUG',
    'SERIES_FILEOPS',
    'SERIES_IMPORTEXTRA',
    'SERIES_PYTRAP',
    'SERIES_TESTQUALITY',
    'TESTQUALITY_REFS',
]
_log = logging.getLogger(__name__)
_log.info("prevention_lang_quality 已加载: %d 项导出", len(__all__))
SERIES_TESTQUALITY = "testquality"
SERIES_FILEOPS = "fileops"
SERIES_IMPORTEXTRA = "importextra"
SERIES_PYTRAP = "pytrap"
SERIES_BUG = "bug"
_R_TESTING_STUBS = (f"{anchor_module('diag_testing_static')} "
                    "(DetectorRegistry: TT01-TT03/SK01-SK02 编写时 preflight_diagnostic_check)")
_R_QB = (f"{anchor_module('diag_traps_coding')} (AS06) + "
         f"{anchor_module('diag_rules_expr_forms')} (RB17) "
         "(DetectorRegistry: 编写时 preflight_diagnostic_check)")
_R_AT01 = f"{anchor_module('diag_traps_payload')}.check_AT01 (目录级通道，直调自证)"
_R_SEC_GATE = (f"{anchor_module('diag_gate_io_control')} "
               "(DetectorRegistry: RB-03/RB-11 承接，资源泄漏)")
_R_RG = f"{anchor_module('diag_se_stdlib')} (DetectorRegistry: RG-02)"
_R_JSON = (f"{anchor_module('diag_traps_guard')} "
           "(DetectorRegistry: JS03 编写时 preflight_diagnostic_check)")
_R_IMP_HYG = (f"{anchor_module('diag_wiring_imports')} "
              "(DetectorRegistry: IM01/IM02/IM04 编写时 preflight_diagnostic_check)")
_R_PY01 = (f"{anchor_module('diag_rules_py_syntax')}.check_PY01 "
           "(PY01 属 REGISTRY_SKIP_IDS，源码树直调；注册表同点由 EX-07/TP-05 承接)")
_R_PY_SYNTAX = (f"{anchor_module('diag_rules_py_syntax')} (DetectorRegistry: PY03/PY05/PY07) + "
                f"{anchor_module('diag_pattern_rules')} (DetectorRegistry: MP01/MP03) + "
                f"{anchor_module('diag_rules_text_damage')} (DetectorRegistry: PY09/PY10) 编写时 preflight_diagnostic_check")
TESTQUALITY_REFS: list[CodeRef] = [
    make_code_ref(SERIES_TESTQUALITY, 'TT-01', '空壳测试函数', 'P1',
          'def test_empty():\n    pass\n',
          'def test_add():\n    assert 1 + 1 == 2\n',
          'test_ 函数体仅 pass/...，测试"通过"是假象，覆盖率为零；'
          'AI 生成测试时的高频凑数模式，必须写真实断言',
          _R_TESTING_STUBS),
    make_code_ref(SERIES_TESTQUALITY, 'TT-03', '测试函数缺少断言', 'P2',
          'def test_print_only():\n'
          '    result = 1 + 1\n'
          '    print("done", result)\n',
          'def test_value():\n'
          '    result = 1 + 1\n'
          '    assert result == 2\n',
          '只执行不断言的测试永远绿，缺陷照样漏过；'
          '每个测试至少一条 assert 校验可观察结果',
          _R_TESTING_STUBS),
    make_code_ref(SERIES_TESTQUALITY, 'SK-01', '空函数体仅 pass', 'P1',
          'def placeholder():\n    pass\n',
          'def compute(x):\n    return x * 2\n',
          '非测试代码的空函数是未完成的桩，调用方拿到 None 还以为'
          '逻辑已实现；要么实现要么显式 raise NotImplementedError',
          _R_TESTING_STUBS),
    make_code_ref(SERIES_TESTQUALITY, 'SK-02', '桩函数仅返回 None', 'P1',
          'def stub():\n    return None\n',
          'def compute(x):\n    return x + 1\n',
          'return None 桩让调用方静默拿到空值，错误沿数据流扩散；'
          '占位实现必须显式声明未完成',
          _R_TESTING_STUBS),
    make_code_ref(SERIES_TESTQUALITY, 'AS-06', 'assert 承载业务逻辑', 'P1',
          'def process(items):\n'
          '    assert items.sort()\n'
          '    return items\n',
          'def process(items):\n'
          '    items.sort()\n'
          '    return items\n',
          'assert 在 -O 优化模式下被整体剔除，依赖它的副作用/校验'
          '随之消失；业务逻辑与校验用 if+raise',
          _R_QB),
]
FILEOPS_REFS: list[CodeRef] = [
    make_code_ref(SERIES_FILEOPS, 'AT-01', 'open 覆盖写源码/文档', 'P2',
          'with open("core_module.py", "w") as f:\n    f.write("print(1)")\n',
          'from pathlib import Path\n\n\n'
          'def render_report(out_dir, text):\n'
          '    out_path = Path(out_dir) / "report_out.txt"\n'
          '    out_path.parent.mkdir(parents=True, exist_ok=True)\n'
          '    out_path.write_text(text, encoding="utf-8")\n',
          '覆盖写模式直指调用方未明确授权替换的 .py/.md 等现有文件，'
          '一次写坏整个文件且无备份；写入前必须确认目标路径与覆盖授权，'
          '生成内容落到调用方选择的位置。需要保留原文件时先备份，并以'
          '同目录临时文件配合 os.replace 原子替换；普通临时产物可使用'
          '应用约定的临时目录',
          _R_AT01),
    make_code_ref(SERIES_FILEOPS, 'AT-02', 'os.rename 跨文件系统移动', 'P2',
          'import os\n\nos.rename("/tmp/a.txt", "/data/b.txt")\n',
          'import shutil\n\nshutil.move("incoming/a.txt", "archive/b.txt")\n',
          'os.rename 跨文件系统（跨盘/跨挂载点）时抛 OSError 且非原子；'
          '跨盘移动用 shutil.move',
          DETECTOR_REF_ARTIFACT),
    make_code_ref(SERIES_FILEOPS, 'RB-03', 'open 未用 with 管理', 'P1',
          'def read(path):\n'
          '    f = open(path)\n'
          '    return f.read()\n',
          'def read(path):\n'
          '    with open(path, encoding="utf-8") as f:\n'
          '        return f.read()\n',
          '无 with 时异常路径必泄漏句柄（Windows 上文件被锁无法删改）；'
          '文件生命周期一律交给上下文管理器',
          _R_SEC_GATE),
    make_code_ref(SERIES_FILEOPS, 'RB-11', '文件句柄未显式关闭', 'P1',
          'def dump(path, text):\n'
          '    f = open(path, "w")\n'
          '    f.write(text)\n'
          '    return len(text)\n',
          'def dump(path, text):\n'
          '    with open(path, "w", encoding="utf-8") as f:\n'
          '        f.write(text)\n'
          '    return len(text)\n',
          '写后不关闭则缓冲可能未刷盘，进程存活期间句柄泄漏累积；'
          'with 语句保证异常路径也关闭',
          _R_SEC_GATE),
    make_code_ref(SERIES_FILEOPS, 'FS-02', '嵌套目录写入前未建目录', 'P2',
          'with open("out/nested/report.txt", "w") as f:\n    f.write("x")\n',
          'import os\n\n'
          'os.makedirs("out/nested", exist_ok=True)\n'
          'with open("out/nested/report.txt", "w", encoding="utf-8") as f:\n'
          '    f.write("x")\n',
          '父目录不存在时 open 写模式直接 FileNotFoundError；'
          '写入前先 os.makedirs(..., exist_ok=True)',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_FILEOPS, 'GF-02', 'docstring 后悬挂字符串', 'P1',
          'def f():\n'
          '    """doc"""\n'
          '    "hanging fragment"\n'
          '    return 1\n',
          'def f():\n'
          '    """doc"""\n'
          '    return 1\n',
          'docstring 闭合引号被截断后剩余文本掉出为孤立字符串表达式，'
          '文档边界失真（AI 编辑 docstring 的典型残留）；'
          '合并回 docstring 或删除',
          DETECTOR_REF_ARTIFACT),
    make_code_ref(SERIES_FILEOPS, 'RG-02', '循环体内重复 re.compile', 'P2',
          'import re\n\n'
          'def parse(items):\n'
          '    out = []\n'
          '    for item in items:\n'
          '        out.append(re.compile(r"\\d+").match(item))\n'
          '    return out\n',
          'import re\n\n'
          '_PATTERN = re.compile(r"\\d+")\n'
          '\n'
          'def parse(items):\n'
          '    out = []\n'
          '    for item in items:\n'
          '        out.append(_PATTERN.match(item))\n'
          '    return out\n',
          '循环内每次迭代都重新编译正则（无缓存收益时开销 O(n) 放大）；'
          '编译结果提升为模块级常量复用',
          _R_RG),
    make_code_ref(SERIES_FILEOPS, 'UC-01', '导入未使用', 'P2',
          'import os\nimport sys\n\n'
          'def main():\n'
          '    return sys.argv\n',
          'import sys\n\n'
          'def main():\n'
          '    return sys.argv\n',
          '无用导入增加命名空间污染与启动开销，还掩盖真实依赖关系；'
          '重构后的残留导入应随手清理',
          DETECTOR_REF_QUALITY),
    make_code_ref(SERIES_FILEOPS, 'TH-01', '线程启动后悬空', 'P2',
          'import threading\n\n'
          'def worker():\n'
          '    return sum(range(10))\n'
          '\n'
          't = threading.Thread(target=worker)\n'
          't.start()\n',
          'import threading\n\n'
          'def worker():\n'
          '    return sum(range(10))\n'
          '\n'
          't = threading.Thread(target=worker)\n'
          't.start()\n'
          't.join()\n',
          '非 daemon 线程不 join 会阻断进程退出；daemon 线程则会在解释器'
          '退出时被突然终止并丢失未完成任务；关键任务使用非 daemon 并'
          '在关键路径 join 等其完成，join(timeout) 不能替代终止/完成确认',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_FILEOPS, 'JS-03', 'json.loads 解析可能为空的输入', 'P2',
          'import json\n\n'
          'def load(text=""):\n'
          '    return json.loads(text)\n',
          'import json\n\n'
          'def load(text=""):\n'
          '    if text is None:\n'
          '        return {}\n'
          '    if not isinstance(text, (str, bytes, bytearray)):\n'
          '        raise TypeError("JSON input must be str, bytes or bytearray")\n'
          '    if not text:\n'
          '        return {}\n'
          '    return json.loads(text)\n',
          '空串直接进 json.loads 抛 JSONDecodeError，None 则抛 TypeError；'
          '分别处理 None 与空输入，并保留 json.loads 支持的 str/bytes/bytearray 类型，其他非法类型显式拒绝',
          _R_JSON),
]
IMPORTEXTRA_REFS: list[CodeRef] = [
    make_code_ref(SERIES_IMPORTEXTRA, 'IM-01', '引用未导入的标准库模块', 'P0',
          'def where():\n    return f"cwd={os.getcwd()}"\n',
          'import os\n\n\ndef where():\n    return f"cwd={os.getcwd()}"\n',
          '用了 os/json 等标准库名却无对应 import，运行时 NameError；'
          'AI 删导入/搬代码时的高频断裂',
          _R_IMP_HYG),
    make_code_ref(SERIES_IMPORTEXTRA, 'IM-02', '循环体内 import', 'P1',
          'import json\n\n'
          'def load_all(files):\n'
          '    out = []\n'
          '    for path in files:\n'
          '        import json\n'
          '        out.append(json.load(open(path)))\n'
          '    return out\n',
          'import json\n\n'
          'def load_all(files):\n'
          '    out = []\n'
          '    for path in files:\n'
          '        with open(path, encoding="utf-8") as f:\n'
          '            out.append(json.load(f))\n'
          '    return out\n',
          '循环体内 import 每次迭代都执行模块查找，且常用来掩盖'
          '循环依赖问题；导入提升到模块顶部',
          _R_IMP_HYG),
    make_code_ref(SERIES_IMPORTEXTRA, 'IM-04', 'docstring 内含 import 语句', 'P0',
          '"""Module doc.\n'
          '\n'
          'import os\n'
          'import sys\n'
          '"""\n'
          '\n'
          'def f():\n'
          '    return 1\n',
          '"""Module doc."""\n'
          '\n'
          'import os\n'
          '\n'
          'def f():\n'
          '    return os.name\n',
          '代码被误放进三引号后，import 与后续逻辑整体失效'
          '（看似存在实则不执行）；AI 改 docstring 时的经典事故',
          _R_IMP_HYG),
    make_code_ref(SERIES_IMPORTEXTRA, 'IA-01', '下划线顶层模块导入绕过包边界', 'P2',
          'from _core import helper\n\nhelper()\n',
          'from pkg.core import helper\n\nhelper()\n',
          'from _core import helper 是顶层绝对导入，不是相对导入；它把包内依赖错误绑定到全局下划线模块，安装或移动后即 ImportError；包内应使用 from pkg.core import ... 或 from .core import ...',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_IMPORTEXTRA, 'IA-02', 'import 别名与使用不一致', 'P1',
          'import os as _os\n\nprint(os.getcwd())\n',
          'import os\n\nprint(os.getcwd())\n',
          'import X as _X 后仍用裸 X，运行时 NameError；'
          '别名一旦引入，全文使用必须一致',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_IMPORTEXTRA, 'AW-04', '单行函数体与 def 同行', 'P2',
          'def double(x): return x * 2\n',
          'def double(x):\n    return x * 2\n',
          '单行函数在 AST 插入语句（body[0] 与 def 同行）时定位错乱，'
          '自动化改码的高危形态；写成常规多行形式',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_IMPORTEXTRA, 'AW-05', '下划线模块 import *', 'P0',
          'from _internal import *\n\nvalue = _helper()\n',
          'from pkg._internal import _helper\n\nvalue = _helper()\n',
          'from _x import * 不导入下划线前缀名称，调用这些名称会在运行时才'
          '暴露 NameError；确需消费模块内私有名的受信任包内代码应显式列出'
          '导入名单，跨包公开消费则应使用正式公开 API',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_IMPORTEXTRA, 'RB-17', 'globals() 动态改命名空间', 'P2',
          'def setup():\n    globals()["debug_flag"] = True\n',
          '_debug_flag = False\n\n'
          'def setup():\n'
          '    global _debug_flag\n'
          '    _debug_flag = True\n',
          'globals()[...] = 绕过静态分析，重命名重构时必然漏改；'
          '用 global 声明或显式容器管理状态',
          _R_QB),
]
PYTRAP_REFS: list[CodeRef] = [
    make_code_ref(SERIES_PYTRAP, 'PY-01', 'except 绑定名前后不一致', 'P0',
          'import json\n\n'
          'def load():\n'
          '    try:\n'
          '        data = json.loads("bad")\n'
          '    except ValueError as e:\n'
          '        print("bad json", _e)\n'
          '        data = {}\n'
          '    return data\n',
          'import json\n\n'
          'def load():\n'
          '    try:\n'
          '        data = json.loads("{}")\n'
          '    except ValueError as e:\n'
          '        print("bad json", e)\n'
          '        data = {}\n'
          '    return data\n',
          '绑定为 e 却使用 _e（或反之）在运行时抛 NameError，'
          '把可恢复异常变成崩溃；绑定名与使用名必须一致',
          _R_PY01),
    make_code_ref(SERIES_PYTRAP, 'PY-03', 'global 重复声明', 'P0',
          'count = 0\n\n'
          'def bump():\n'
          '    global count\n'
          '    print(count)\n'
          '    global count\n'
          '    count += 1\n',
          '_count = 0\n\n'
          'def bump():\n'
          '    global _count\n'
          '    _count += 1\n',
          '同一函数内重复 global 声明且两次声明之间存在对该名字的使用'
          '（CPython 实测 SyntaxError: used prior to global declaration）；'
          '相邻重复（无中间使用）合法但属编辑残留；每个名字只声明一次',
          _R_PY_SYNTAX),
    make_code_ref(SERIES_PYTRAP, 'PY-05', '同名类重复定义', 'P0',
          'class Parser:\n'
          '    def run(self):\n'
          '        return 1\n'
          '\n'
          '\n'
          'class Parser:\n'
          '    def run(self):\n'
          '        return 2\n',
          'class Parser:\n'
          '    def run(self):\n'
          '        return 1\n'
          '\n'
          '\n'
          'class ParserV2:\n'
          '    def run(self):\n'
          '        return 2\n',
          '后一个同名类静默覆盖前一个，调用方拿到的是"最后版本"，'
          '语义漂移无任何告警；同名类必须改名区分（模块级同名函数重复'
          '由 DC-03 专职检测，本规则不重复报告防同点双报）',
          _R_PY_SYNTAX),
    make_code_ref(SERIES_PYTRAP, 'PY-07', 'spec_from_file_location 传目录', 'P0',
          'import importlib.util\n\n'
          'spec = importlib.util.spec_from_file_location("m", "./src/")\n',
          'import importlib.util\n\n'
          'spec = importlib.util.spec_from_file_location("m", "./src/mod.py")\n',
          '传目录路径时 spec 为 None，随后 module_from_spec 直接'
          'AttributeError 崩溃；必须传具体 .py 文件路径',
          _R_PY_SYNTAX),
    make_code_ref(SERIES_PYTRAP, 'FM-01', '% 格式化占位符数量不匹配', 'P0',
          'name = "x"\nmsg = "hello %s and %s" % name\n',
          'name = "x"\nother = "y"\nmsg = "hello %s and %s" % (name, other)\n',
          '单个值对多个占位符抛 TypeError: not enough arguments；'
          '多值必须显式组元组',
          DETECTOR_REF_STRING_JSON),
    make_code_ref(SERIES_PYTRAP, 'FM-02', 'f-string 引用未定义变量', 'P1',
          'def greet(user):\n'
          '    return f"hello {usr}"\n',
          'def greet(user):\n'
          '    return f"hello {user}"\n',
          'f-string 中的名字在模块内无任何赋值时，渲染瞬间 NameError；'
          '拼写漂移（usr/user）是 AI 改名时的典型残留',
          DETECTOR_REF_STRING_JSON),
    make_code_ref(SERIES_PYTRAP, 'FM-03', 'format 占位符与参数不匹配', 'P1',
          'msg = "{a} and {b}".format(a=1)\n',
          'msg = "{a} and {b}".format(a=1, b=2)\n',
          '占位符 {b} 无对应关键字参数时 KeyError；'
          '自动编号 {} 与显式编号 {0} 缺位置参数时 IndexError；'
          '占位符与实参必须一一配对（*args 展开按未知放行）',
          DETECTOR_REF_STRING_JSON),
    make_code_ref(SERIES_PYTRAP, 'CF-01', 'os.environ 直接索引', 'P1',
          'import os\n\nhome = os.environ["HOME"]\n',
          'import os\n\nhome = os.environ.get("HOME", "")\n',
          '环境变量缺失时 os.environ[...] 直接 KeyError 崩溃；'
          '用 .get(key, default) 提供降级值',
          DETECTOR_REF_ARTIFACT),
    make_code_ref(SERIES_PYTRAP, 'CQ-03', '字典重复键静默覆盖', 'P1',
          'config = {"host": "a", "host": "b", "port": 80}\n',
          'config = {"host": "b", "port": 80}\n',
          'Python 允许重复键字面量且后值静默覆盖前值，无任何告警；'
          '去重必须保留最后值才能维持运行语义（1 与 True 亦视为同键）',
          DETECTOR_REF_QUALITY),
    make_code_ref(SERIES_PYTRAP, 'CQ-06', 'dict.get 默认 True 使缺键静默开启', 'P2',
          'def check(cfg):\n'
          '    if cfg.get("enabled", True):\n'
          '        return "on"\n'
          '    return "off"\n',
          'def check(cfg):\n'
          '    if cfg.get("enabled") is True:\n'
          '        return "on"\n'
          '    return "off"\n',
          'if cfg.get(key, True) 并非整体恒真，但键缺失会默认进入开启分支，'
          '且 "false" 等真值非 bool 数据也会开启；用 is True 明确布尔契约，'
          '三态配置则先单独处理 None',
          DETECTOR_REF_QUALITY),
    make_code_ref(SERIES_PYTRAP, 'CQ-07', '多赋值链共享可变引用', 'P2',
          'a = b = []\nb.append(1)\n',
          'def build():\n'
          '    a = []\n'
          '    b = []\n'
          '    b.append(1)\n'
          '    return a, b\n',
          'a = b = [] 让两个名字指向同一列表，改一个另一个跟着变；'
          '可变对象必须分别创建',
          DETECTOR_REF_QUALITY),
    make_code_ref(SERIES_PYTRAP, 'MM-01', '类属性可变默认被实例共享', 'P1',
          'class Registry:\n'
          '    items = []\n'
          '\n'
          '    def add(self, item):\n'
          '        self.items.append(item)\n'
          '        return len(self.items)\n',
          'class Registry:\n'
          '    def __init__(self):\n'
          '        self.items = []\n'
          '\n'
          '    def add(self, item):\n'
          '        self.items.append(item)\n'
          '        return len(self.items)\n',
          '类属性 list/dict 被全部实例共享，A 实例的 append 会出现在'
          'B 实例里（内存意外积累）；实例状态放 __init__',
          DETECTOR_REF_QUALITY),
    make_code_ref(SERIES_PYTRAP, 'NT-01', 'None 用 == 比较', 'P2',
          'value = None\n\nif value == None:\n    print("none")\n',
          'value = None\n\nif value is None:\n    print("none")\n',
          'None 是单例，== 可被自定义 __eq__ 重载产生意外结果；'
          '单例身份判断一律用 is / is not',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_PYTRAP, 'CL-01', 'staticmethod 内引用 self', 'P1',
          'class Box:\n'
          '    @staticmethod\n'
          '    def size(n):\n'
          '        return self._n\n',
          'class Box:\n'
          '    @staticmethod\n'
          '    def size(n):\n'
          '        return n\n',
          '静态方法无实例绑定，运行时 self 未定义直接 NameError；'
          '要么去掉 @staticmethod 要么改用常规方法',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_PYTRAP, 'NM-02', 'Decimal 与 float 混用运算', 'P2',
          'from decimal import Decimal\n\ntotal = Decimal("1.50") + 0.75\n',
          'from decimal import Decimal\n\ntotal = Decimal("1.50") + Decimal("0.75")\n',
          'Decimal + float 直接 TypeError（不允许隐式转换）；'
          '金额计算两侧都必须是 Decimal',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_PYTRAP, 'DC-01', '终止语句后的不可达代码', 'P3',
          'def f(x):\n'
          '    return x + 1\n'
          '    print("dead")\n',
          'def f(x):\n'
          '    print("computing")\n'
          '    return x + 1\n',
          'return/raise/break/continue 之后的语句永不执行，'
          '多为编辑残留；死代码误导维护者以为有副作用',
          DETECTOR_REF_QUALITY),
]
_GATE3_BUG_ANCHOR = anchor_module("diag_detector_assembly")
def _bug_ref(rule_id: str, module: str, detector: str) -> str:
    return (f"{_GATE3_BUG_ANCHOR} (Gate3 {rule_id}) + "
            f"{anchor_module(module)}.{detector}")
BUG_REFS: list[CodeRef] = [
    make_code_ref(SERIES_BUG, 'B36', '字面量解包数量错配', 'ERROR',
          """x, y = (1, 2, 3)""",
          """x, y, z = (1, 2, 3)""",
          '赋值两侧同为固定长度字面量时元素数不等，一执行必抛 ValueError（too many values to unpack），无需任何运行时信息即可判定。',
          _bug_ref('B36', 'diag_gate_expr',
                   'detect_b36_unpack_literal_mismatch')),
    make_code_ref(SERIES_BUG, 'B37', '惰性迭代器直接下标', 'ERROR',
          """first = map(str, [1, 2])[0]""",
          """first = list(map(str, [1, 2]))[0]""",
          'map/filter/zip 等返回的迭代器无 __getitem__，直接下标即 TypeError（py2 返回 list 的直觉残留）；须先经 list()/tuple() 物化。',
          _bug_ref('B37', 'diag_gate_loop',
                   'detect_b37_lazy_iterator_subscript')),
    make_code_ref(SERIES_BUG, 'B38', 'dict 视图对象直接下标', 'ERROR',
          """vals = {'a': 1}.values()[0]""",
          """vals = list({'a': 1}.values())[0]""",
          'py3 的 keys()/values()/items() 返回视图对象而非 list，不支持下标/切片，直接下标即 TypeError。',
          _bug_ref('B38', 'diag_gate_expr_flow',
                   'detect_b38_dict_view_subscript')),
    make_code_ref(SERIES_BUG, 'B39', 'len() 消费惰性迭代器', 'ERROR',
          """n = len(zip([1], [2]))""",
          """n = len(list(zip([1], [2])))""",
          'zip/map/filter/生成器表达式均无 __len__，len() 一执行即 TypeError；须先物化为序列再取长度。',
          _bug_ref('B39', 'diag_gate_loop',
                   'detect_b39_len_of_lazy_iterator')),
    make_code_ref(SERIES_BUG, 'B40', 'raise 非异常对象', 'ERROR',
          """raise 'boom'""",
          """raise ValueError('boom')""",
          'raise 的对象必须派生自 BaseException：raise 字面量一执行即 TypeError（exceptions must derive from BaseException）。',
          _bug_ref('B40', 'diag_gate_io_control',
                   'detect_b40_raise_non_exception')),
    make_code_ref(SERIES_BUG, 'B41', '__repr__/__str__ 内格式化裸 self', 'ERROR',
          """class Point:
    def __init__(self, x):
        self.x = x

    def __repr__(self):
        return f'Point({self})'
""",
          """class Point:
    def __init__(self, x):
        self.x = x

    def __repr__(self):
        return f'Point({self.x})'
""",
          "__repr__ 体内格式化裸 self 会重入 __repr__ 自身：f'{self}' 经 str(self) 转调 self.__repr__，无限递归至 RecursionError。",
          _bug_ref('B41', 'diag_gate_class_protocol',
                   'detect_b41_repr_str_self_recursion')),
    make_code_ref(SERIES_BUG, 'B42', '无效正则字面量', 'ERROR',
          """import re

pattern = re.compile('([')
""",
          """import re

pattern = re.compile('([a-z]+)')
""",
          're.compile 首参为 str 常量时合法性可静态试算，编译失败即运行时同位置必抛 re.error。',
          _bug_ref('B42', 'diag_gate_expr',
                   'detect_b42_invalid_regex_literal')),
    make_code_ref(SERIES_BUG, 'B43', '显式关键字与 **dict 字面量键重复', 'ERROR',
          """result = dict(**{'a': 1}, a=2)""",
          """result = dict(**{'a': 1}, b=2)""",
          '显式关键字实参与 **dict 字面量键重复时，调用点一执行即 TypeError（got multiple values for keyword argument）。',
          _bug_ref('B43', 'diag_gate_expr',
                   'detect_b43_duplicate_keyword_arg')),
    make_code_ref(SERIES_BUG, 'B44', '数字构造字面量必失败', 'ERROR',
          """value = int('3.14')""",
          """value = int(float('3.14'))""",
          'int/float/complex 的 str 常量实参解析合法性可静态试算，失败即运行时同位置必抛 ValueError/TypeError。',
          _bug_ref('B44', 'diag_gate_expr',
                   'detect_b44_literal_number_parse_invalid')),
    make_code_ref(SERIES_BUG, 'B45', '字面量容器下标越界', 'ERROR',
          """char = 'abc'[5]""",
          """char = 'abc'[2]""",
          '字面量容器长度静态可知，整型常量下标超出 [-len, len) 区间即必抛 IndexError。',
          _bug_ref('B45', 'diag_gate_expr',
                   'detect_b45_literal_subscript_out_of_range')),
    make_code_ref(SERIES_BUG, 'B46', 'except 子句类型非法', 'ERROR',
          """try:
    raise ValueError('boom')
except [ValueError]:
    value = 0
""",
          """try:
    value = 1
except ValueError:
    value = 0
""",
          'except 后的类型必须是异常类或其元组：异常发生时解释器求值该子句，列字典型态与字面量类型即抛 TypeError（catching classes that do not inherit from BaseException）。',
          _bug_ref('B46', 'diag_gate_io_control',
                   'detect_b46_except_invalid_handler_type')),
    make_code_ref(SERIES_BUG, 'B47', '实例方法零参数漏 self', 'ERROR',
          """class Counter:
    def bump():
        return 1
""",
          """class Counter:
    def bump(self):
        return 1
""",
          '类体内无装饰器且零位置参数的 def，实例调用时解释器自动传入 self，即 TypeError（takes 0 positional arguments but 1 was given）。',
          _bug_ref('B47', 'diag_gate_class_protocol',
                   'detect_b47_method_missing_self')),
    make_code_ref(SERIES_BUG, 'B48', 'property 存取器签名错', 'ERROR',
          """class Box:
    @property
    def size(self, extra):
        return extra
""",
          """class Box:
    @property
    def size(self):
        return 1
""",
          'property 协议签名固定（fget(self)/fset(self, value)/fdel(self)），参数数不符时解释器按固定参数调用即 TypeError。',
          _bug_ref('B48', 'diag_gate_class_protocol',
                   'detect_b48_property_bad_signature')),
    make_code_ref(SERIES_BUG, 'B49', '无参数 staticmethod 内零参 super()', 'ERROR',
          """class Base:
    @staticmethod
    def build():
        return 'base'


class Child(Base):
    @staticmethod
    def build():
        return super().build()
""",
          """class Base:
    @staticmethod
    def build():
        return 'base'


class Child(Base):
    @staticmethod
    def build():
        return Base.build()
""",
          '零参 super() 依赖编译器注入的 __class__ 单元与第一位置参数作绑定对象，无参 staticmethod 内调用即 RuntimeError（super(): no arguments）。',
          _bug_ref('B49', 'diag_gate_class_protocol',
                   'detect_b49_super_in_staticmethod')),
    make_code_ref(SERIES_BUG, 'B50', 'match 重复 case 字面量模式', 'ERROR',
          """def route(kind):
    match kind:
        case 1:
            return 'one'
        case 1:
            return 'uno'
    return 'unknown'
""",
          """def route(kind):
    match kind:
        case 1:
            return 'one'
        case 2:
            return 'two'
    return 'unknown'
""",
          'match 自上而下首个匹配即命中：无 guard 的重复字面量模式使后一分支永不可达（增改分支时的高频残留）。',
          _bug_ref('B50', 'diag_gate_expr',
                   'detect_b50_duplicate_case_pattern')),
    make_code_ref(SERIES_BUG, 'B51', 'seq[len(seq)] 下标必越界', 'ERROR',
          """def last_item(items):
    return items[len(items)]
""",
          """def last_item(items):
    return items[-1] if items else None
""",
          '合法下标上界为 len(seq)-1，以 len(seq) 本身作下标必抛 IndexError（取末元素漏写 -1 的典型笔误）。',
          _bug_ref('B51', 'diag_gate_expr',
                   'detect_b51_index_of_len_oob')),
    make_code_ref(SERIES_BUG, 'B52', '模块级就地函数结果被消费', 'ERROR',
          """import random

shuffled = random.shuffle([1, 2])
""",
          """import random

items = [1, 2]
random.shuffle(items)
shuffled = items
""",
          'random.shuffle 等模块级就地函数返回 None，结果被赋值/返回时消费方拿到的恒为 None，后续使用即 TypeError（与 B21 就地方法同族）。',
          _bug_ref('B52', 'diag_gate_expr_flow',
                   'detect_b52_inplace_module_func_result')),
    make_code_ref(SERIES_BUG, 'B53', '子类重写 __init__ 未调父类初始化', 'WARN',
          """class Base:
    def __init__(self):
        self.ready = True


class Child(Base):
    def __init__(self):
        self.flag = 1
""",
          """class Base:
    def __init__(self):
        self.ready = True


class Child(Base):
    def __init__(self):
        super().__init__()
        self.flag = 1
""",
          '子类重写 __init__ 后不调用父类初始化，父类建立的属性/状态静默缺失，后续访问即 AttributeError 或行为漂移（WARN 级：存在有意完全接管场景）。',
          _bug_ref('B53', 'diag_gate_class_protocol',
                   'detect_b53_missing_super_init')),
    make_code_ref(SERIES_BUG, 'B54', 'async 函数内 time.sleep', 'WARN',
          """import asyncio
import time


async def fetch():
    time.sleep(1)
    return await asyncio.sleep(0)
""",
          """import asyncio


async def fetch():
    return await asyncio.sleep(1)
""",
          'time.sleep 是同步阻塞调用，在 async def 内直接调用会冻结事件循环上全部协程，异步并发语义静默退化为串行。',
          _bug_ref('B54', 'diag_gate_class_protocol',
                   'detect_b54_blocking_sleep_in_async')),
    make_code_ref(SERIES_BUG, 'B55', 'asyncio.create_task 结果丢弃', 'WARN',
          """import asyncio


async def work():
    return 1


async def run():
    asyncio.create_task(work())
""",
          """import asyncio


async def work():
    return 1


async def run():
    task = asyncio.create_task(work())
    await task
""",
          '事件循环对 task 仅持弱引用：create_task 返回值作独立语句丢弃时，任务可能在完成前被 GC 回收静默取消（RUF006 同口径）。',
          _bug_ref('B55', 'diag_gate_class_protocol',
                   'detect_b55_create_task_dropped')),
    make_code_ref(SERIES_BUG, 'B56', 'NaN 等值比较', 'WARN',
          """import math


def is_missing(value):
    return value == math.nan
""",
          """import math


def is_missing(value):
    return isinstance(value, float) and math.isnan(value)
""",
          'IEEE 754 语义下 NaN 与任何值（含自身）相等比较恒为 False，用 ==/!= 作守卫即守卫失效；判定须用 math.isnan。',
          _bug_ref('B56', 'diag_gate_expr',
                   'detect_b56_nan_equality')),
    make_code_ref(SERIES_BUG, 'B57', '条件位海象绑定字面量', 'WARN',
          """def check(value):
    if total := 5:
        return total
    return 0
""",
          """def check(value):
    if total := value + 5:
        return total
    return 0
""",
          'if/while 条件为海象绑定常量时真值即常量真值：if x := 5 恒真（else 永不可达），多为漏写比较表达式的笔误。',
          _bug_ref('B57', 'diag_gate_expr',
                   'detect_b57_walrus_literal_condition')),
    make_code_ref(SERIES_BUG, 'B58', '裸 raise 在 except 上下文外', 'ERROR',
          """def fail():
    raise
""",
          """def fail():
    raise RuntimeError('failed')
""",
          '裸 raise 仅在 except 子句内（有活跃异常被处理）合法，上下文外执行必抛 RuntimeError（No active exception to re-raise）。',
          _bug_ref('B58', 'diag_gate_io_control',
                   'detect_b58_bare_raise_outside_except')),
    make_code_ref(SERIES_BUG, 'B59', '__init__ 含 yield/yield from 或声明为 async', 'ERROR',
          """class Bag:
    def __init__(self):
        self.items = []
        yield self.items
""",
          """class Bag:
    def __init__(self):
        self.items = []
""",
          '__init__ 出现 yield/yield from 会成为生成器函数，声明为 async def 则成为协程函数；两者实例化时都会向解释器返回非 None 对象，触发 __init__() should return None 的 TypeError。',
          _bug_ref('B59', 'diag_gate_class_protocol',
                   'detect_b59_dunder_yield_in_init')),
    make_code_ref(SERIES_BUG, 'B60', 'dunder 协议方法返回字面量违反契约', 'ERROR',
          """class Flag:
    def __bool__(self):
        return 'yes'
""",
          """class Flag:
    def __bool__(self):
        return True
""",
          '协议消费点（bool()/len()/str() 等）校验返回类型：__bool__ 返回非 bool、__len__ 返回非 int/负值一执行即 TypeError/ValueError。',
          _bug_ref('B60', 'diag_gate_class_protocol',
                   'detect_b60_dunder_return_type_violation')),
    make_code_ref(SERIES_BUG, 'B61', 'isinstance/issubclass 第二参数非法', 'ERROR',
          """ok = isinstance(1, [int])""",
          """ok = isinstance(1, (int, float))""",
          'isinstance 第二参数必须是类型、类型元组或联合类型：列字典型态与字面量一执行即 TypeError（arg 2 must be a type, a tuple of types, or a union）。',
          _bug_ref('B61', 'diag_gate_expr',
                   'detect_b61_isinstance_invalid_type_arg')),
    make_code_ref(SERIES_BUG, 'B62', 'del 删除名后再次引用', 'ERROR',
          """def cleanup(payload):
    del payload
    return len(payload)
""",
          """def cleanup(payload):
    size = len(payload)
    del payload
    return size
""",
          '作用域内 del 执行后绑定即移除，其后无重绑定的引用必抛 NameError（模块/类层）或 UnboundLocalError（函数层）。',
          _bug_ref('B62', 'diag_gate_scope_bind',
                   'detect_b62_del_then_reference')),
    make_code_ref(SERIES_BUG, 'B63', 'max/min 对空字面量序列求值且无 default', 'ERROR',
          """best = max([])""",
          """best = max([], default=0)""",
          'max([])/min(()) 等空字面量单参数调用必抛 ValueError（arg is an empty sequence），须显式给 default 或改用多参数形态。',
          _bug_ref('B63', 'diag_gate_expr',
                   'detect_b63_min_max_empty_literal')),
    make_code_ref(SERIES_BUG, 'B64', '正则匹配结果赋值后未判空解引用', 'WARN',
          """import re


def find_group(text):
    matched = re.search('a', text)
    return matched.group()
""",
          """import re


def find_group(text):
    matched = re.search('a', text)
    if matched:
        return matched.group()
    return ''
""",
          're.search/match 无匹配返回 None：赋值后在无判空屏障的直线段内解引用（.group() 等）必抛 AttributeError，与 B34 链式形态互补。',
          _bug_ref('B64', 'diag_gate_expr_flow',
                   'detect_b64_regex_assigned_unchecked_deref')),
    make_code_ref(SERIES_BUG, 'B65', '函数/方法引用未调用直接作条件', 'WARN',
          """def has_items(items):
    if len:
        return True
    return False
""",
          """def has_items(items):
    if len(items):
        return True
    return False
""",
          '函数/方法对象恒真：把可调用引用当调用结果作条件，else 分支成死代码，多为漏写调用括号与参数的笔误（WARN 级语义缺陷）。',
          _bug_ref('B65', 'diag_gate_expr_flow',
                   'detect_b65_callable_ref_truthy')),
    make_code_ref(SERIES_BUG, 'B66', 'next() 参数非法', 'ERROR',
          """first = next([1, 2])""",
          """first = next(iter([1, 2]))""",
          'next 的第一参数必须是迭代器：直接传序列字面量必抛 TypeError（object is not an iterator），空迭代器无 default 必抛 StopIteration。',
          _bug_ref('B66', 'diag_gate_loop',
                   'detect_b66_next_invalid_iterator')),
    make_code_ref(SERIES_BUG, 'B67', 'input() 返回值直接数值运算', 'ERROR',
          """total = input() - 1""",
          """total = int(input()) - 1""",
          'input() 恒返回 str：直接参与数值运算必抛 TypeError，须先显式转换（+/* 与 str 组合属合法拼接/重复形态不报）。',
          _bug_ref('B67', 'diag_gate_expr',
                   'detect_b67_input_arithmetic')),
    make_code_ref(SERIES_BUG, 'B68', 'while True 循环体无任何退出路径', 'ERROR',
          """def render(items):
    while True:
        pass
""",
          """def render(items):
    while items:
        items.pop()
""",
          '循环体（含嵌套块、不含嵌套函数体）无 break/return/raise/yield/await 且无任何函数调用时，必无退出通道亦无间接退出可能，循环永不终止——AI 生成残留占位的典型形态。',
          _bug_ref('B68', 'diag_gate_loop',
                   'detect_b68_while_true_no_exit')),
    make_code_ref(SERIES_BUG, 'B69', '字面量容器/字符串 .index() 查找必失败', 'ERROR',
          """pos = 'abc'.index('z')""",
          """pos = 'abc'.index('b')""",
          '字面量容器与字符串的元素/子串静态可知：.index() 查找不存在的值必抛 ValueError，属可静态试算的确定性失败。',
          _bug_ref('B69', 'diag_gate_expr_flow',
                   'detect_b69_literal_index_missing')),
    make_code_ref(SERIES_BUG, 'B70', '不可变对象元素赋值', 'ERROR',
          """text = 'abc'
text[0] = 'A'
""",
          """text = 'Abc'""",
          'str/bytes/tuple 为不可变对象：元素赋值一执行即 TypeError（object does not support item assignment），须构造新对象替代。',
          _bug_ref('B70', 'diag_gate_expr_flow',
                   'detect_b70_immutable_item_assign')),
    make_code_ref(SERIES_BUG, 'B71', '不可变容器调用不存在的修改方法', 'ERROR',
          """text = 'abc'
text.append('d')
""",
          """text = 'abc' + 'd'""",
          '不可变类型无就地修改 API：对 str/tuple 调用 append/extend 等修改方法必抛 AttributeError，须用拼接/重建方式表达。',
          _bug_ref('B71', 'diag_gate_expr_flow',
                   'detect_b71_immutable_forbidden_method')),
    make_code_ref(SERIES_BUG, 'B72', '调试器断点残留', 'WARN',
          """def compute(value):
    breakpoint()
    return value + 1
""",
          """def compute(value):
    return value + 1
""",
          'breakpoint()/pdb.set_trace() 残留会进入交互调试阻塞生产执行路径（无 TTY 环境表现更隐蔽），交付前必须清除。',
          _bug_ref('B72', 'diag_gate_expr_flow',
                   'detect_b72_debugger_residue')),
]
