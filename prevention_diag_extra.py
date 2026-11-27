"""prevention_diag_extra — 诊断规则代码引用·补充域与 DIAG4 后补批.
本模块承载 DIAG 库 11 系列中的其余五个补充域（49 条），以及第二张登记表
DIAG4_CODE_REFS（13 条，版本 1.1.4），合计 62 条；清单与注册表的
一致性由建键/注册期校验兜底（build_keyed_registry 重复规则号即 ValueError，
register_code_refs 校验键与引用），本模块无专用清单解析测试。rule_id 与诊断 findings 严格一致；
importextra/bug/dstruct/dquality/security 带连字符，DIAG4 的 pytrap/arch_extra/
robust 等系列沿用原规则编号形态（DB-05、MP-03 等，同样带连字符）。
  7. importextra  2 条 — 导入完整性，diag_wiring_import_scan(GF16/GF18)，
                 项目目录扫描级，静态单文件不可自证：GF-16 GF-18
  8. bug          5 条 — 运行时缺陷：RB-01 RB-04（注册表别名通道，适配自
                 Gate3 B01/B03 同语义实现）、EX-04 UH-01 AW-03
  9. dstruct      5 条 — 结构域，目录/清单/SQL 级不可自证：SL-06 导出面、
                 MS-02 PI-01 PY-04 XT01（合并自保护/包结构/影子包/SQL 字段）
 10. dquality     1 条 — 质量域，体积预警，体积级不可自证：SZ-02
 11. security    36 条 — 安全域：PT-01 路径穿越 AI-02 MCP 工具投毒；
                 SE 族按实现模块分派：SE-05 SE-06 SE-07 SE-08 SE-09 SE-10
                 SE-11 SE-12 SE-13 SE-14 SE-15 SE-16 SE-17 SE-18 SE-19
                 SE-20 SE-23 SE-24 SE-25 SE-26 SE-27 SE-28 SE-29 SE-30
                 SE-31 SE-32 SE-33 SE-34 SE-35 SE-36 SE-37 SE-38 SE-39
                 SE-40；锚点分别指向 diag_se_injection（SE-05/06/08/20/
                 35/37）、diag_se_stdlib（注册表 SE-07/09/11-17/19/23/
                 25/26/29-31/33/34 + A5 通道 SE-18/24）、diag_se_data（SE-10/28/36）、
                 diag_traps_blocking（SE-27）、diag_security_diagnoser
                 （场景级 SE-38/39/40）；SE-32 与 SE-05 同语义，
                 无独立检测器，仅编写前注入。
severity 是检测器口径的投影：每条 severity 与对应检测器在 bad_example 上的实际
severity 逐条一致（tests 直接比对 finding severity，漂移即失败）。
自证机制（防示例本身成为幻觉源）：self_verifiable=True 的条目由诊断通道做
静态核验——主系列由 DetectorRegistry/Gate3 承接，后补批经 diag_detector_assembly
的直调通道（RD_PREVENTION_CHECKS）与 A5 detect_all 分派；
diag_detectors_registry 的存活探针按注册表 ID 抽样执行 bad_example，命中本规则
或声明别名即视为存活。good_example 不得报中目标规则，bad_example 由对应检测器
真实报出。补充域以下 12 条标记 False（DIAG4 批的 AS-09 同为 False，按体积级
单列在下方批次说明），只做注入文本引导、不做示例自证：
- 声明级/项目目录级/目录级/体积级：GF-16、GF-18、SL-06、SZ-02
- 合并计划级/包结构级/SQL schema 级：MS-02、PI-01、PY-04、XT01
- 场景级（A5 静态通道，判定依赖跨文件/框架上下文）：SE-38、SE-39、SE-40
- 同语义重复规则（SE-05 承接，无独立检测器）：SE-32
DIAG4 后补批：DIAG4_CODE_REFS 13 条（版本 1.1.4），与本段 49 条规则号不重叠，
导入时以 'prevention_diag_extra:diag4' 为源标签幂等并入主库
CODE_REFS。DIAG4 是后补批次，条数与版本独立演进；不要与主表合并，否则任一批次
刷新都会带动另一批次的版本号与清单变更。
接线：模块加载尾部把 DIAG_SUPPLEMENT_CODE_REFS 与 DIAG4_CODE_REFS 幂等合并进
主库 CODE_REFS（本模块 → prevention_refs_main 单向）。11 系列联合视图
DIAG_CODE_REFS 由 jwsgj/__init__.py 在装配期按「core + supplement」顺序合并；
两个数据模块之间不互相导入。主库消费者（attach_code_refs /
enrich_entry_result / inject_code_refs_to_prompt / preflight_diagnostic_check）
通过 CODE_REFS 自动获得全部条目。
区块结构：importextra/bug/dstruct/dquality/security 五个补充域分节承载 49 条，
DIAG4 后补批单独成节承载 13 条。
"""
from __future__ import annotations

import logging

from jwsgj.prevention_refs_main import (
    CodeRef,
    anchor_module,
    build_keyed_registry,
    make_code_ref,
    register_code_refs,
)

__all__ = [
    'DIAG4_CODE_REFS',
    'DIAG4_CODE_REFS_VERSION',
    'DIAG_SUPPLEMENT_CODE_REFS',
    'SERIES_ARCH_EXTRA',
    'SERIES_BUG',
    'SERIES_DQUALITY',
    'SERIES_DSTRUCT',
    'SERIES_IMPORTEXTRA',
    'SERIES_PYTRAP',
    'SERIES_ROBUST',
    'SERIES_SECURITY',
]
_log = logging.getLogger(__name__)
_log.info("prevention_diag_extra 补充域诊断规则代码引用预防库已加载: %d 项导出", len(__all__))
SERIES_IMPORTEXTRA = "importextra"
SERIES_BUG = "bug"
SERIES_DSTRUCT = "dstruct"
SERIES_DQUALITY = "dquality"
SERIES_SECURITY = "security"
SERIES_ARCH_EXTRA = "arch_extra"
SERIES_PYTRAP = "pytrap"
SERIES_ROBUST = "robust"
_R_IMPORT_SAFETY = (
    f"{anchor_module('diag_wiring_import_scan')} "
    "(DetectorRegistry: GF16/GF18，项目目录扫描级)"
)
_R_REGISTRY_ALIAS = (
    f"{anchor_module('diag_detector_assembly')} "
    "(DetectorRegistry: RB01/RB04 注册表别名通道，"
    "适配自 diag_gate_class.detect_b01_mutable_default / "
    "diag_gate_io_control.detect_b03_bare_except)"
)
_R_SIZE_GUARD = (f"{anchor_module('diag_gate_arch')} (DetectorRegistry: SZ02，体积预警级；"
                 f"注册装配见 {anchor_module('diag_detector_assembly')})")
_R_RUNTIME_HAZ = (
    f"{anchor_module('diag_se_injection')} (DetectorRegistry: PT01 路径穿越) + "
    f"{anchor_module('diag_rules_runtime')} (DetectorRegistry: UH01)"
)
_R_SE_INJECTION = (
    f"{anchor_module('diag_se_injection')} "
    "(DetectorRegistry + A5 detect_all: SE05/SE06/SE08/SE20/SE35/SE37)"
)
_R_SE_STDLIB = (
    f"{anchor_module('diag_se_stdlib')} "
    "(DetectorRegistry + A5 detect_all: SE07/SE09/SE11-SE17/SE19/"
    "SE23/SE25/SE26/SE29/SE30/SE31/SE33/SE34)"
)
_R_SE_STDLIB_A5 = (
    f"{anchor_module('diag_se_stdlib')} "
    "(A5 detect_all: SE18/SE24；未注册 DetectorRegistry)"
)
_R_SE_DATA = (
    f"{anchor_module('diag_se_data')} "
    "(DetectorRegistry + A5 detect_all: SE10/SE28/SE36)"
)
_R_SE_TRAPS = (
    f"{anchor_module('diag_traps_blocking')} "
    "(A5 detect_all: SE27；未注册 DetectorRegistry)"
)
_R_SE_SCENARIO = (
    f"{anchor_module('diag_security_diagnoser')} "
    "(A5 detect_all 场景级: SE38/SE39/SE40)"
)
_R_SE_DUPLICATE = (
    f"{anchor_module('diag_se_injection')} "
    "(SE05 同语义承接；SE32 无独立检测器，仅编写前注入)"
)
_R_MS = f"{anchor_module('diag_merge_safety')} (DetectorRegistry: MS01/MS02)"
_R_PY_SYNTAX = (f"{anchor_module('diag_rules_py_syntax')} (DetectorRegistry: PY02/PY04) + "
                f"{anchor_module('diag_pattern_rules')} (DetectorRegistry: MP01) + "
                f"{anchor_module('diag_rules_text_damage')} (DetectorRegistry: PY09/PY10)")
_R_RC = f"{anchor_module('diag_structure_rules')} (DetectorRegistry: PI01)"
_R_XT = f"{anchor_module('diag_verify_contract')} (DetectorRegistry: XT01)"
_R_EXC_FLOW = (f"{anchor_module('diag_wiring_exc_flow')} "
               "(DetectorRegistry: EX04/EX06/EX07/EH04/EH05 编写时 preflight_diagnostic_check)")
_R_SPLIT = (f"{anchor_module('diag_wiring_symbol_scan')} "
            "(DetectorRegistry: SL-06 编写时 preflight_diagnostic_check)")
_R_TRAPS_CODING = (f"{anchor_module('diag_traps_coding')} "
                   "(DetectorRegistry: AW03/AI02 编写时 preflight_diagnostic_check)")
_IMPORTEXTRA_REFS: list[CodeRef] = [
    make_code_ref(SERIES_IMPORTEXTRA, 'GF-16', '裸包内导入（绕过包边界）', 'ERROR',
          '# 反例（项目目录级）：包内模块绕过包名直接裸导入兄弟模块\n'
          '# 包结构 pkg/{__init__.py, core.py, utils.py}，core.py 中：\n'
          'import utils  # 裸导入：脱离包上下文，安装后 ImportError\n',
          '# 正例：包内相对导入或带包前缀的绝对导入\n'
          'from . import utils\n'
          '# 或\n'
          'from pkg import utils\n',
          '裸包内导入（import 兄弟模块不带包前缀）在源码目录内侥幸可跑，'
          '一旦安装/换 cwd 即 ImportError；包内一律使用相对导入或带包名的'
          '绝对导入。项目目录扫描级规则，编写前注入约束预防，事后由 GF-16 扫描兜底。',
          _R_IMPORT_SAFETY, self_verifiable=False),
    make_code_ref(SERIES_IMPORTEXTRA, 'GF-18', '导入深度误算（超约定层级）', 'WARN',
          '# 反例（项目目录级）：深挖内部实现层\n'
          'from pkg.core.internal._impl import helper\n',
          '# 正例：消费包公开导出的稳定 API\n'
          'from pkg import helper\n'
          '# 或消费包声明的稳定入口\n'
          'from pkg.api import helper\n',
          '导入越过包的公开 API 直插内部实现层（下划线模块/超约定层级），'
          '内部重构时消费方静默断裂；只导入包在 __init__/api 中公开声明的符号。'
          '项目目录扫描级规则，编写前注入约束预防。',
          _R_IMPORT_SAFETY, self_verifiable=False),
]
_BUG_REFS: list[CodeRef] = [
    make_code_ref(SERIES_BUG, 'RB-01', '可变默认参数（注册表别名）', 'P1',
          'def append_item(item, items=[]):\n'
          '    # 反例：默认列表在调用间共享，状态跨调用累积\n'
          '    items.append(item)\n'
          '    return items\n',
          'def append_item(item, items=None):\n'
          '    # 正例：None 哨兵 + 函数体内构造\n'
          '    if items is None:\n'
          '        items = []\n'
          '    items.append(item)\n'
          '    return items\n',
          '可变默认参数（list/dict/set）在函数定义时求值一次，所有调用共享'
          '同一对象，导致状态跨调用意外累积；这是注册表 RB-01 通道'
          '（与主库 B01 同语义），两条 rule_id 均可命中本示例。',
          _R_REGISTRY_ALIAS),
    make_code_ref(SERIES_BUG, 'RB-04', '裸 except 吞掉一切（注册表别名）', 'P2',
          'def parse_value(text):\n'
          '    try:\n'
          '        return int(text)\n'
          '    except:  # 反例：裸 except 连 KeyboardInterrupt/SystemExit 一并吞掉\n'
          '        return None\n',
          'def parse_value(text):\n'
          '    try:\n'
          '        return int(text)\n'
          '    except (TypeError, ValueError):\n'
          '        # 正例：精确捕获预期异常类型\n'
          '        return None\n',
          '裸 except: 会捕获包括 SystemExit/KeyboardInterrupt 在内的一切异常，'
          '掩盖真实故障并阻断进程控制信号；这是注册表 RB-04 通道'
          '（与主库 B03 同语义），精确捕获预期异常类型。',
          _R_REGISTRY_ALIAS),
    make_code_ref(SERIES_BUG, 'EX-04', '重复 except 类型（后分支永不执行）', 'P2',
          'def parse(text):\n'
          '    try:\n'
          '        return int(text)\n'
          '    except ValueError:\n'
          '        return None\n'
          '    except ValueError:  # 反例：重复捕获，此分支永不执行\n'
          '        return 0\n',
          'def parse(text):\n'
          '    try:\n'
          '        return int(text)\n'
          '    except (ValueError, TypeError):  # 正例：同类异常合并为一个分支\n'
          '        return None\n',
          '同一 try 的多个 except 捕获相同异常类型时，后面的分支永远不会执行'
          '（Ruff B014 / Pylint W0705），掩盖真实错误分支并误导阅读者；'
          '重复类型合并进同一 except 元组。',
          _R_EXC_FLOW),
    make_code_ref(SERIES_BUG, 'UH-01', 'list/dict/set 作 dict key 或 set 元素', 'P0',
          'def build_index():\n'
          '    # 反例：list 不可哈希，作为 dict key 运行时报 TypeError\n'
          '    lookup = {["a", "b"]: 1}\n'
          '    return lookup\n',
          'def build_index():\n'
          '    # 正例：可哈希的 tuple 作 key\n'
          '    lookup = {("a", "b"): 1}\n'
          '    return lookup\n',
          'list/dict/set 不可哈希，用作 dict 的 key 或 set 的元素时，'
          '运行期直接抛 TypeError: unhashable type；需用可哈希的'
          'tuple()/frozenset() 替代。',
          _R_RUNTIME_HAZ),
    make_code_ref(SERIES_BUG, 'AW-03', 'AST 节点误用 node.parent 属性', 'P0',
          'import ast\n'
          '\n'
          'def find_parent(node):\n'
          '    # 反例：标准 ast 节点没有 parent 属性，运行期 AttributeError\n'
          '    return node.parent\n',
          'import ast\n'
          '\n'
          'class ParentMap(ast.NodeVisitor):\n'
          '    """正例：NodeVisitor 维护 parent 映射并提供查询。"""\n'
          '    def __init__(self):\n'
          '        self._parents = {}\n'
          '\n'
          '    def generic_visit(self, node):\n'
          '        for child in ast.iter_child_nodes(node):\n'
          '            self._parents[id(child)] = node\n'
          '        super().generic_visit(node)\n'
          '\n'
          '    def parent_of(self, node):\n'
          '        return self._parents.get(id(node))\n'
          '\n'
          'def find_parent(node, root):\n'
          '    parents = ParentMap()\n'
          '    parents.visit(root)\n'
          '    return parents.parent_of(node)\n',
          'Python 标准 ast 节点没有 parent 属性，node.parent 运行期抛 '
          'AttributeError，hasattr(node, "parent") 恒 False 使依赖它的分支'
          '静默退化；应通过 NodeVisitor.generic_visit 维护 parent 映射并提供查询入口，'
          '或用 asttokens 等带父指针的库。',
          _R_TRAPS_CODING),
]
_DSTRUCT_REFS: list[CodeRef] = [
    make_code_ref(SERIES_DSTRUCT, 'SL-06', '声明的包根公共入口导出缺失', 'WARN',
          '# 反例（目录级）：项目声明包根为公共入口，pkg/__init__.py 却未兑现\n'
          '# pkg/core.py 的 public_func 属该入口承诺的公共符号，但 __all__ 漏列\n'
          'from pkg.core import public_func\n',
          '# 正例：包根是公共入口时，显式导出该入口承诺的公共符号\n'
          '# pkg/__init__.py\n'
          'from pkg.core import public_func\n'
          '\n'
          '__all__ = ["public_func"]\n',
          '项目把包根声明为公共入口时，__init__.py 必须兑现该入口承诺的导出面；'
          '公共子模块同样可以成为稳定API，不要求所有项目把全部公共符号聚合到包根。'
          '关键是公共入口声明与实现一致，避免消费方依赖未承诺的内部深路径。',
          _R_SPLIT, self_verifiable=False),
    make_code_ref(
        SERIES_DSTRUCT, "MS-02", "合并操作自保护缺失", "P0",
        '# 合并方案：输出 merge_target.py 却同时列入删除清单\n'
        'plan = {"merge": ["a.py", "b.py"], "output": "merge_target.py",\n'
        '        "delete": ["a.py", "b.py", "merge_target.py"]}\n',
        '# 合并产物不得出现在删除列表；源与输出不得同名；源必须真实存在\n'
        'plan = {"merge": ["a.py", "b.py"], "output": "merge_target.py",\n'
        '        "delete": ["a.py", "b.py"]}\n',
        "合并产物出现在删除清单会导致产物创建后立即被删；合并源与输出同名形成"
        "自引用循环；路径比较须 abspath 归一化防分隔符差异静默失效（合并计划"
        "级检测，仅注入引导）。",
        _R_MS,
        self_verifiable=False,
    ),
    make_code_ref(
        SERIES_DSTRUCT, "PI-01", "普通包与命名空间包形态混用", "P2",
        '# 反例：项目使用普通包相对导入约定，目标目录却漏建 __init__.py\n',
        '# 正例：普通包同步创建 __init__.py；若明确采用PEP 420命名空间包，\n'
        '# 则保持无 __init__.py，并确保各分布部分遵循同一命名空间约定\n',
        "缺少 __init__.py 不必然断裂：PEP 420命名空间包是合法形态。真正风险是"
        "项目未明确选择普通包或命名空间包，导致相对导入、打包与路径解析预期不一致；"
        "按项目声明的包形态保持一致，不把jwsgj自身布局强加给目标项目。",
        _R_RC,
        self_verifiable=False,
    ),
    make_code_ref(
        SERIES_DSTRUCT, "PY-04", "本地模块与预期依赖同名形成影子导入", "P0",
        '# 项目根存在 local_utils.py，同时代码预期导入已安装的 local_utils\n'
        'import local_utils  # 实际导入对象取决于项目结构与 sys.path 顺序\n',
        '# 依据目标项目依赖清单与导入解析结果消除同名歧义\n'
        'from my_project.local_io import load  # 使用项目内唯一的明确模块路径\n',
        "任何本地模块都可能与当前项目声明的第三方包、标准库或兄弟包同名；"
        "是否构成影子导入必须依据目标项目的依赖清单、包结构与导入解析结果判定，"
        "不能把某个固定模块名视为所有项目的冲突。确属冲突时，应在项目内建立"
        "唯一且明确的模块路径，并同步更新消费方（项目目录级检测，仅注入引导）。",
        _R_PY_SYNTAX,
        self_verifiable=False,
    ),
    make_code_ref(
        SERIES_DSTRUCT, "XT01", "表结构与 SQL 字段不匹配", "P2",
        '# schema: users(id, name)\n'
        'conn.query("SELECT id, name, email FROM users")  # email 不存在\n',
        '# SQL 字段与 schema 逐一对齐\n'
        'conn.query("SELECT id, name FROM users")\n',
        "SQL 语句引用了表结构中不存在的字段/类型不匹配，运行时才报错；写 SQL"
        "前对照 schema 定义逐字段核对（按文件路径自读源码检测，仅注入引导）。",
        _R_XT,
        self_verifiable=False,
    ),
]
_DQUALITY_REFS: list[CodeRef] = [
    make_code_ref(SERIES_DQUALITY, 'SZ-02', '文件/函数体积偏高预警', 'WARN',
          '# 反例（体积级）：单函数行数逼近硬上限 300（预警线 240）\n'
          'def do_everything(request):\n'
          '    ...  # 校验/业务/持久化/日志混合 280 逻辑行\n',
          '# 正例：按职责拆分为小于预警线的多个函数\n'
          'def validate_request(request):\n'
          '    ...\n'
          '\n'
          'def apply_business_logic(request):\n'
          '    ...\n',
          '文件与函数的体积预算应以目标项目声明为准；未声明时才采用检测器'
          '默认阈值，达到当前预算的 80% 即进入预警。编写时应优先简化逻辑、'
          '消除重复并按职责内聚函数；是否迁移或拆分由项目结构与净收益决定，'
          '不把某一组固定行数或治理方式强加给所有项目。体积级规则，'
          '编写前注入约束预防。',
          _R_SIZE_GUARD, self_verifiable=False),
]
_SE_RULE_REFS: list[CodeRef] = [
make_code_ref(
    SERIES_SECURITY, "SE-05", "f-string 拼接 SQL 语句", "P0",
    'def get_user(cursor, user_id):\n'
    '    return cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")\n',
    'def get_user(cursor, user_id):\n'
    '    return cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))\n',
    "f-string 把用户输入直接拼进 SQL 语句，攻击者注入引号即可改写查询语义（SQL 注入）。"
    "参数化查询（占位符 + 参数元组）让驱动负责转义，注入面被彻底消除。",
    _R_SE_INJECTION,
),
make_code_ref(
    SERIES_SECURITY, "SE-06", "os.path.join 拼接外部输入路径", "P0",
    'import os\n'
    '\n'
    'def build_path(base_dir, user_input):\n'
    '    return os.path.join(base_dir, user_input)\n',
    'import os\n'
    '\n'
    'def build_path(base_dir, user_input):\n'
    '    safe_name = os.path.basename(user_input)\n'
    '    if safe_name in ("", ".", ".."):\n'
    '        raise ValueError(f"invalid name: {user_input!r}")\n'
    '    return os.path.join(base_dir, safe_name)\n',
    "外部输入直接拼进路径时，'../..' 或绝对路径可逃出预期目录（路径穿越）。"  # jwsgj:suppress SS-02 — 缺陷说明文本，非执行面
    "basename 剥掉目录成分后仍会保留 '.'/'..' 自身（basename('..') == '..'，"
    "join(base, '..') 仍上跳一级），必须显式拒绝后才能在 join 中把结果"
    "钉死在 base_dir 内。",
    _R_SE_INJECTION,
),
make_code_ref(
    SERIES_SECURITY, "SE-13", "webbrowser.open 未校验 URL", "P2",
    'import webbrowser\n'
    '\n'
    'def open_doc(url):\n'
    '    webbrowser.open(url)\n',
    'import webbrowser\n'
    'from urllib.parse import urlsplit\n'
    '\n'
    'def open_doc(url):\n'
    '    # 拒绝不可信输入的改写与选项形态，只打开明确的HTTP(S)绝对URL\n'
    '    if url != url.strip() or url.startswith("-"):\n'
    '        raise ValueError("unsafe URL")\n'
    '    parsed = urlsplit(url)\n'
    '    if parsed.scheme not in {"http", "https"} or not parsed.netloc:\n'
    '        raise ValueError("unsupported URL")\n'
    '    webbrowser.open(url)\n',
    "前导横杠会被部分浏览器解析为命令行选项，前导空白还可能绕过单纯的字符剥离。"
    "先拒绝选项形态、首尾空白与非HTTP(S)/无主机URL，再交给浏览器；合法URL不会因末端防御被改写。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-20", "动态执行用户输入的代码", "P0",
    'def calc(data):\n'
    '    return eval(data)\n',
    'import ast\n'
    '\n'
    'def calc(data):\n'
    '    return ast.literal_eval(data)\n',
    "eval/exec 会执行任意 Python 代码，用户输入即 RCE（远程代码执行）入口。"
    "ast.literal_eval 只解析字面量（数字/字符串/元组/列表/字典），永不执行代码。",
    _R_SE_INJECTION,
),
make_code_ref(
    SERIES_SECURITY, "SE-32", "SQL 查询直接 f-string/format 拼接", "P0",
    'def find_orders(cursor, status):\n'
    '    sql = f"SELECT * FROM orders WHERE status = {status}"\n'
    '    return cursor.execute(sql)\n',
    'def find_orders(cursor, status):\n'
    '    return cursor.execute(\n'
    '        "SELECT * FROM orders WHERE status = ?", (status,))\n',
    "拼接 SQL 与参数化查询的差别在于：前者把输入当代码解释，后者把输入当数据传递。占位符 + 参数元组让数据库驱动安全转义，注入语义不可能成立。",
    _R_SE_DUPLICATE, self_verifiable=False,
),
make_code_ref(
    SERIES_SECURITY, "SE-35", "str.format 变量模板注入", "P1",
    'def render(template, user_input):\n'
    '    return template.format(user_input)\n',
    'def render(template, user_input):\n'
    '    allowed = ("Hello {0}",)\n'
    '    if template not in allowed:\n'
    '        raise ValueError("unsupported template")\n'
    '    return "Hello {0}".format(user_input)\n',
    "模板来自变量时，攻击者可控模板内容（如 {0.__init__.__globals__}）实现属性穿越读取。"
    "动态模板必须先通过代码内白名单的完整匹配，再只允许变量填充值位，模板面与数据面严格分离。",
    _R_SE_INJECTION,
),
make_code_ref(
    SERIES_SECURITY, "SE-37", "高级 SQL 注入（间接拼接/bypass 向量）", "P0",
    'def search(cursor, keyword):\n'
    '    query = f"SHOW COLUMNS FROM items LIKE \'%{keyword}%\'"\n'
    '    return cursor.execute(query)\n',
    'def search(cursor, keyword):\n'
    '    return cursor.execute(\n'
    '        "SHOW COLUMNS FROM items LIKE ?", ("%" + keyword + "%",))\n',
    "f-string 先赋值给变量再传入 execute 的间接拼接，与直接拼接同罪——输入仍被当 SQL 代码解释。"
    "通配符拼在参数值里而非 SQL 文本里，keyword 只能作为数据匹配，无法改变查询结构；保留 SHOW COLUMNS 元数据查询语义，不以行查询替代。",
    _R_SE_INJECTION,
),
make_code_ref(
    SERIES_SECURITY, "SE-12", "shutil.unpack_archive 未校验 ZIP 成员路径", "P0",
    'import shutil\n'
    '\n'
    'def extract(archive_path, dest_dir):\n'
    '    shutil.unpack_archive(archive_path, dest_dir)\n',
    'import ntpath\n'
    'import zipfile\n'
    '\n'
    'def extract(archive_path, dest_dir):\n'
    '    with zipfile.ZipFile(archive_path) as zf:\n'
    '        for name in zf.namelist():\n'
    '            parts = name.replace("\\\\", "/").split("/")\n'
    '            if (ntpath.isabs(name) or ntpath.splitdrive(name)[0]\n'
    '                    or ".." in parts):\n'
    '                raise ValueError(f"unsafe member: {name}")\n'
    '        zf.extractall(dest_dir)\n',
    "Zip Slip：恶意归档内的绝对路径（C:\\...）或 ../.. 成员会解压到目标目录之外，覆盖任意文件。"  # jwsgj:suppress SS-02 — 缺陷说明文本，非执行面
    "解压前逐成员校验路径（ntpath 同时覆盖 Windows 盘符/UNC 与反斜杠形态的任意位置上跳段），把解压范围钉死在目标目录内。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-25", "隐蔽渠道不安全反序列化", "P0",
    'import io\n'
    'import pickle as p\n'
    '\n'
    'def load_state(blob):\n'
    '    return p.Unpickler(io.BytesIO(blob)).load()\n',
    'import json\n'
    '\n'
    'def load_state(blob_text):\n'
    '    return json.loads(blob_text)\n',
    "pickle.Unpickler 直接实例化同样可执行任意代码；模块或函数别名会绕过"
    "只做全名匹配的安全审查。load/loads 由 SE-04 承接，本条覆盖隐蔽的 "
    "Unpickler 实例化，避免同一调用双报。JSON 等数据格式只描述结构，"
    "不携带行为，反序列化面不再可达 RCE。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-26", "tarfile.extractall 未校验路径", "P1",
    'import tarfile\n'
    '\n'
    'def untar(path, dest):\n'
    '    tarfile.open(path).extractall(dest)\n',
    'import ntpath\n'
    'import tarfile\n'
    '\n'
    'def untar(path, dest):\n'
    '    with tarfile.open(path) as tf:\n'
    '        for member in tf.getmembers():\n'
    '            parts = member.name.replace("\\\\", "/").split("/")\n'
    '            if member.issym() or member.islnk():\n'
    '                raise ValueError(f"unsafe link: {member.name}")\n'
    '            if (ntpath.isabs(member.name)\n'
    '                    or ntpath.splitdrive(member.name)[0]\n'
    '                    or ".." in parts):\n'
    '                raise ValueError(f"unsafe member: {member.name}")\n'
    '        for member in tf.getmembers():\n'
    '            tf.extract(member, dest)\n',
    "tar 成员名可含绝对路径或 ../，extractall 会原样落盘造成路径穿越覆盖。"  # jwsgj:suppress SS-02 — 缺陷说明文本，非执行面
    "先逐成员完成全量校验再统一解压（ntpath 覆盖盘符/UNC/反斜杠上跳），并拒绝 "
    "symlink/hardlink，既防止 linkname 绕过成员名校验，也避免后续非法成员出现时已部分落盘；"
    "Python 3.12+ 也可用 filter=\"data\"。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-17", "pkgutil.get_data 资源参数未校验", "P1",
    'import pkgutil\n'
    '\n'
    'def read_resource(package, resource_name):\n'
    '    return pkgutil.get_data(package, resource_name)\n',
    'import ntpath\n'
    'import importlib.resources as res\n'
    '\n'
    'def read_resource(package, resource_name):\n'
    '    parts = resource_name.replace("\\\\", "/").split("/")\n'
    '    if (not resource_name or ntpath.isabs(resource_name)\n'
    '            or ntpath.splitdrive(resource_name)[0]\n'
    '            or ".." in parts):\n'
    '        raise ValueError("invalid resource name")\n'
    '    return res.files(package).joinpath(resource_name).read_bytes()\n',
    "resource 参数来自外部时，'../../secrets' 形态可读取包目录外任意文件（路径穿越读取）。"  # jwsgj:suppress SS-02 — 缺陷说明文本，非执行面
    "拒绝绝对路径、盘符与任意位置的上跳段后再取资源，读取范围被限制在包内。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-10", "hashlib.md5 弱哈希用于安全场景", "P1",
    'import hashlib\n'
    '\n'
    'def make_sig(salted):\n'
    '    m = hashlib.md5(salted)\n'
    '    return m.digest()\n',
    'import hashlib\n'
    '\n'
    'def make_sig(salted):\n'
    '    m = hashlib.sha256(salted)\n'
    '    return m.digest()\n',
    "MD5/SHA1 已被证明可构造碰撞，签名/校验场景下攻击者可伪造通过验证。"
    "SHA-256 无已知实际碰撞；确需 MD5 做非安全指纹时应显式声明 usedforsecurity=False。",
    _R_SE_DATA,
),
make_code_ref(
    SERIES_SECURITY, "SE-11", "random 模块生成安全令牌", "P1",
    'import random\n'
    '\n'
    'def make_token():\n'
    '    return "".join(random.choice("abcdef0123456789") for _ in range(32))\n',
    'import secrets\n'
    '\n'
    'def make_token():\n'
    '    return secrets.token_hex(16)\n',
    "random 是可预测的伪随机（种子可推断），令牌/密钥被猜出即账号失守。secrets 基于操作系统密码学随机源，不可预测，专为此场景设计。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-31", "cryptography 弃用加密 API（ARC4/DES/ECB）", "P2",
    'from cryptography.hazmat.primitives.ciphers import Cipher, algorithms\n'
    '\n'
    'def make_cipher(key):\n'
    '    return Cipher(algorithms.ARC4(key), None)\n',
    'from cryptography.hazmat.primitives.ciphers.aead import AESGCM\n'
    '\n'
    'def make_cipher(key):\n'
    '    return AESGCM(key)\n',
    "ARC4/Blowfish/DES 是已被攻破的弱算法，ECB 模式相同明文产生相同密文（模式泄露明文结构）。"
    "AES-GCM 认证加密同时提供机密性与完整性，是当前对称加密默认选择。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-14", "XML 解析未限制嵌套深度", "P1",
    'import xml.etree.ElementTree as ET\n'
    '\n'
    'def parse_doc(xml_file):\n'
    '    return ET.parse(xml_file)\n',
    'from defusedxml.ElementTree import parse\n'
    '\n'
    'def parse_doc(xml_file):\n'
    '    return parse(xml_file, forbid_dtd=True)\n',
    "Expat 解析深度嵌套 DTD 内容模型时会耗尽 C 栈（CVE-2026-4224），"
    "一个恶意 XML 即可打崩进程。defusedxml 没有通用元素深度上限，且默认 "
    "forbid_dtd=False；必须显式 forbid_dtd=True 在内容模型解析前拒绝 DTD，"
    "同时保留实体与外部引用防护，不能只替换导入路径。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-19", "XML 解析未禁用外部实体（XXE）", "P0",
    'import xml.etree.ElementTree as ET\n'
    '\n'
    'def parse_feed(xml_text):\n'
    '    return ET.fromstring(xml_text)\n',
    'from defusedxml.ElementTree import fromstring\n'
    '\n'
    'def parse_feed(xml_text):\n'
    '    return fromstring(xml_text)\n',
    "XXE：外部实体可读本地文件（file:///etc/passwd）、探测内网（SSRF），数据以错误信息/回显外泄。"  # jwsgj:suppress SS-02,供应链安全-敏感路径 — 缺陷说明文本，非路径访问
    "defusedxml 默认禁用 DTD 与外部实体，XXE 向量整体失效。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-16", "BaseCookie.js_output 未转义 script 标签", "P1",
    'from http.cookies import SimpleCookie\n'
    '\n'
    'def cookie_script():\n'
    '    cookie = SimpleCookie()\n'
    '    cookie["sid"] = "abc123"\n'
    '    return cookie.js_output()\n',
    'from http.cookies import SimpleCookie\n'
    '\n'
    'def cookie_header():\n'
    '    cookie = SimpleCookie()\n'
    '    cookie["sid"] = "abc123"\n'
    '    return cookie.output()\n',
    "js_output 生成的 <script> 片段未转义 </script> 序列，Cookie 值含该序列时可注入任意脚本（XSS）。"
    "改用 output() 生成 Set-Cookie 响应头，不再产出可被注入的 <script> 片段，闭合向量被消除。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-23", "HTTP 请求禁用 SSL 证书验证", "P1",
    'import requests\n'
    '\n'
    'def fetch(url):\n'
    '    return requests.get(url, verify=False, timeout=30)\n',
    'import requests\n'
    '\n'
    'def fetch(url):\n'
    '    headers = {"User-Agent": "myapp/1.0"}\n'
    '    return requests.get(\n'
    '        url, headers=headers, verify=True, timeout=30)\n',
    "verify=False 关闭证书校验后，中间人可冒充目标站点截获/篡改全部流量（MITM）。"
    "保持证书验证开启（默认行为），自签场景应把 CA 证书装入 trust store 而非关闭验证。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-27", "网络请求未设置超时", "P2",
    'import requests\n'
    '\n'
    'def fetch(url):\n'
    '    return requests.get(url)\n',
    'import requests\n'
    '\n'
    'def fetch(url):\n'
    '    headers = {"User-Agent": "myapp/1.0"}\n'
    '    return requests.get(url, headers=headers, timeout=30)\n',
    "无超时的请求会被恶意/故障服务器无限挂起，连接池耗尽即整服务不可用（DoS）。"
    "显式 timeout 把最坏等待钉在有限值，配合重试策略实现快速失败。",
    _R_SE_TRAPS,
),
make_code_ref(
    SERIES_SECURITY, "SE-29", "requests 请求未设置 User-Agent", "P3",
    'import requests\n'
    '\n'
    'def fetch(url):\n'
    '    return requests.get(url, timeout=30)\n',
    'import requests\n'
    '\n'
    'def fetch(url):\n'
    '    headers = {"User-Agent": "myapp/1.0"}\n'
    '    return requests.get(url, headers=headers, timeout=30)\n',
    "requests 默认 UA 特征明显，常被 WAF 拦截或识别为爬虫导致请求被静默降级。显式设置 UA 表明合法身份，避免被默认策略误伤。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-33", "http 明文传输敏感数据", "P1",
    'API_URL = "http://api.example.com/v1/data"\n',
    'API_URL = "https://api.example.com/v1/data"\n',
    "http 明文链路上凭据/令牌可被链路任意节点嗅探（咖啡店 WiFi 即可抓包）。"
    "https 的 TLS 加密层使嗅探只能看到密文，传输机密性由协议保证。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-34", "telnetlib 传输明文凭据", "P0",
    'import telnetlib\n'
    '\n'
    'def connect(host, user, password):\n'
    '    tn = telnetlib.Telnet(host)\n',
    'import paramiko\n'
    '\n'
    'def connect(host, user, key_file):\n'
    '    client = paramiko.SSHClient()\n'
    '    client.load_system_host_keys()\n'
    '    client.connect(host, username=user, key_filename=key_file)\n'
    '    return client\n',
    "telnet 全程明文且 telnetlib 已在 Python 3.13 移除，凭据在链路上裸奔。"
    "SSH（paramiko）提供加密信道 + 密钥认证，凭据不再暴露于链路。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-28", "print 输出敏感信息", "P2",
    'def audit(api_key):\n'
    '    print(api_key)\n',
    'def audit(api_key):\n'
    '    print("api_key: ********")\n',
    "stdout 通常被日志收集器/终端历史记录持久化，明文凭据一旦打印即进入多方存储。"
    "输出脱敏掩码（固定星号）而非真实值，审计语义保留、泄露面消除。",
    _R_SE_DATA,
),
make_code_ref(
    SERIES_SECURITY, "SE-36", "日志输出敏感信息", "P1",
    'import logging\n'
    '\n'
    'def on_login(auth_token):\n'
    '    logging.info(f"login ok token={auth_token}")\n',
    'import logging\n'
    '\n'
    'def on_login(user_id):\n'
    '    logging.info("login ok user=%s", user_id)\n',
    "令牌/密钥进日志后随日志管线扩散（聚合/备份/第三方日志服务），撤换成本远高于打印前过滤。"
    "日志只记非敏感标识（user_id），敏感字段在源头就不进入日志语句。",
    _R_SE_DATA,
),
make_code_ref(
    SERIES_SECURITY, "SE-30", "正则表达式 ReDoS 风险", "P1",
    'import re\n'
    '\n'
    'def match_tag(text):\n'
    '    pattern = re.compile(r"^(a+)+$")\n'
    '    return pattern.match(text) is not None\n',
    'import re\n'
    '\n'
    'def match_tag(text):\n'
    '    pattern = re.compile(r"^a+$")\n'
    '    return pattern.match(text) is not None\n',
    "嵌套量词 (a+)+ 使回溯路径指数爆炸，30 余字符的非匹配输入即可让线程卡死分钟级（灾难性回溯）。"
    "展平量词层级（单一 +）或使用占有量词/原子组，回溯路径线性化，不再可被恶意输入放大。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-07", "yaml.load 未指定 Loader", "P0",
    'import yaml\n'
    '\n'
    'def load_config(data):\n'
    '    return yaml.load(data)\n',
    'import yaml\n'
    '\n'
    'def load_config(data):\n'
    '    return yaml.safe_load(data)\n',
    "PyYAML 6 的 yaml.load 必须显式传 Loader，省略 Loader 会直接 TypeError；"
    "旧版默认 Loader 或显式 UnsafeLoader 可构造任意 Python 对象，恶意 YAML 可导致任意代码执行。"
    "safe_load 只解析基础类型，同时消除现代版本的签名错误与旧版本的不安全对象构造面。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-08", "subprocess 使用 shell=True", "P0",
    'import subprocess\n'
    '\n'
    'def run_cmd(cmd):\n'
    '    return subprocess.run(cmd, shell=True, timeout=30)\n',
    'import subprocess\n'
    '\n'
    'def run_cmd(cmd):\n'
    '    allowed = (["git", "status"], ["git", "diff"])\n'
    '    if cmd not in allowed:\n'
    '        raise ValueError("unsupported command")\n'
    '    return subprocess.run(cmd, shell=False, timeout=30)\n',
    "shell=True 时命令经 shell 解释，输入中的分号/反引号/$(...)都会被展开（命令注入）。"
    "参数列表形态不经 shell，每个参数只是数据；完整命令数组必须通过代码内白名单，不能只校验可执行文件名。",
    _R_SE_INJECTION,
),
make_code_ref(
    SERIES_SECURITY, "SE-09", "tempfile.mktemp 竞态条件", "P0",
    'import tempfile\n'
    '\n'
    'def tmp_path():\n'
    '    return tempfile.mktemp()\n',
    'import tempfile\n'
    '\n'
    'def tmp_file():\n'
    '    """返回持有原子创建 fd 的临时文件，调用方负责关闭与清理。"""\n'
    '    return tempfile.NamedTemporaryFile(mode="w+b", delete=False)\n',
    "mktemp 只生成名字不创建文件，检查与使用之间的时间窗可被抢占（symlink 攻击覆写任意文件）。"
    "原子创建并持有已打开文件对象，避免先关闭 fd 再只返回路径所产生的替换窗口；"
    "调用方按最小权限使用，关闭后按需清理临时文件。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-15", "base64.b64decode 未使用 validate", "P1",
    'import base64\n'
    '\n'
    'def decode_payload(token):\n'
    '    return base64.b64decode(token)\n',
    'import base64\n'
    '\n'
    'def decode_payload(token):\n'
    '    return base64.b64decode(token, validate=True)\n',
    "默认模式遇非法字符静默截断，'aGVsbG8!!!' 与 'aGVsbG8' 解码相同，下游基于解码结果的校验可被尾部垃圾绕过。"
    "validate=True 遇非 Base64 字符直接抛错，输入校验绕过向量被关闭。",
    _R_SE_STDLIB,
),
make_code_ref(
    SERIES_SECURITY, "SE-18", "assert 用于输入验证", "P1",
    'def process_order(order):\n'
    '    assert order.amount > 0, "invalid amount"\n'
    '    return charge(order)\n',
    'def process_order(order):\n'
    '    if order.amount <= 0:\n'
    '        raise ValueError("invalid amount")\n'
    '    return charge(order)\n',
    "python -O 优化模式下 assert 被整体移除，生产环境的输入校验静默失效。"
    "显式 if + raise 的校验不受优化模式影响，任何运行形态下都生效。",
    _R_SE_STDLIB_A5,
),
make_code_ref(
    SERIES_SECURITY, "SE-24", "os.chmod 设置过度宽松权限", "P1",
    'import os\n'
    '\n'
    'def unlock(path):\n'
    '    os.chmod(path, 0o777)\n',
    'import os\n'
    '\n'
    'def lock_down(path):\n'
    '    os.chmod(path, 0o600)\n',
    "0o777 使任意用户可读写执行，提权与篡改面完全暴露。最小权限原则：属主读写（0o600）即可满足，"
    "需要执行时按角色收窄到 0o700/0o750。",
    _R_SE_STDLIB_A5,
),
make_code_ref(
    SERIES_SECURITY, "SE-38", "跨文件污点传播", "P1",
    '# 反例：污点源到危险汇聚点无任何净化/白名单拦截\n'
    'def handle(req):\n'
    '    path = req.args.get("p")            # 污点源\n'
    '    return FileServer().serve(path)     # 汇聚点：读任意文件\n',
    '# 正例：污点源进入汇聚点前经过显式净化/白名单\n'
    'import os\n'
    'def handle(req):\n'
    '    path = os.path.basename(req.args.get("p", ""))\n'
    '    if not ALLOWED_NAMES.issuperset({path}):\n'
    '        raise ValueError("not allowed")\n'
    '    return FileServer().serve(path)\n',
    "单点看无害的代码，污点经函数边界/模块边界传播后在远端汇聚点爆发；需要跨文件污点追踪（源→传播→汇聚点）才能判定。"
    "编写时应确保每个外部输入在到达文件/命令/SQL/反序列化汇聚点前有显式净化或白名单校验。",
    _R_SE_SCENARIO, self_verifiable=False,
),
make_code_ref(
    SERIES_SECURITY, "SE-39", "框架上下文感知安全风险", "P2",
    '# 反例：脱离框架防护直接处理原始请求\n'
    'def raw_view(environ):\n'
    '    cmd = environ.get("CMD")\n'
    '    return os.popen(cmd).read()\n',
    '# 正例：经框架中间件（认证/CSRF/输入清洗）后再处理\n'
    '@app.route("/run", methods=["POST"])\n'
    '@login_required\n'
    'def run_view():\n'
    '    task = TaskSchema.model_validate(request.get_json())\n'
    '    return run_task(task.name)\n',
    "绕过框架中间件（认证/CSRF/Schema 校验）直接处理原始输入，会把框架层面已解决的攻击面重新打开；需结合框架路由/中间件上下文判定。"
    "编写视图时应经框架入口（路由+中间件+Schema 校验）而非直接处理原始 environ/输入。",
    _R_SE_SCENARIO, self_verifiable=False,
),
make_code_ref(
    SERIES_SECURITY, "SE-40", "符号执行漏洞验证", "P2",
    '# 反例：路径条件恒可达，漏洞可被真实触发\n'
    'def transfer(amount, balance):\n'
    '    if amount <= balance:   # 只校验上界，未拒绝负数\n'
    '        balance -= amount\n'
    '    return balance   # transfer(-100, 0) 余额变 100\n',
    '# 正例：路径条件覆盖全部攻击输入域\n'
    'def transfer(amount, balance):\n'
    '    if (isinstance(amount, bool) or not isinstance(amount, int)\n'
    '            or amount <= 0 or amount > balance):\n'
    '        raise ValueError("invalid amount")\n'
    '    return balance - amount\n',
    "符号执行沿路径求解可达性：表面有校验但条件域留洞（如未拒绝负数）时，攻击输入可真实走到危险状态。"
    "编写校验条件时应自问『什么输入能让这个条件失效』，把类型、符号、边界全部钉死；"
    "bool 是 int 子类，必须单独拒绝，避免 True/False 作为金额参与算术。",
    _R_SE_SCENARIO, self_verifiable=False,
),
]
_SECURITY_REFS: list[CodeRef] = [
    make_code_ref(SERIES_SECURITY, 'PT-01', 'os.path.join 拼接不可信输入无路径校验', 'P1',
          'import os\n'
          '\n'
          'def save_attachment():\n'
          '    user_name = input("enter name: ")\n'
          '    # 反例：不可信输入直接拼入路径，无校验（OWASP A01）\n'
          '    return os.path.join(user_name, "report.txt")\n',
          'import os\n'
          '\n'
          'def save_attachment(user_name):\n'
          '    # 正例：规范化后校验真实路径仍位于白名单目录内\n'
          '    base_dir = os.path.realpath("attachments")\n'
          '    path = os.path.realpath(\n'
          '        os.path.join(base_dir, user_name, "report.txt"))\n'
          '    if os.path.commonpath((base_dir, path)) != base_dir:\n'
          '        raise ValueError("非法路径片段")\n'
          '    return path\n',
          'os.path.join 拼接源自 input()/request.*/socket/urlopen 等不可信来源'
          '的变量且无校验时，构成路径穿越面（OWASP A01:2021）；'
          '必须用 os.path.realpath() 规范化，再以 os.path.commonpath() '
          '验证结果仍位于白名单目录内，统一拦截绝对路径、上跳与跨盘输入。',
          _R_RUNTIME_HAZ),
    make_code_ref(SERIES_SECURITY, 'AI-02', 'MCP 工具调用未验证声明与行为一致性', 'P0',
          'def invoke_tool(name):\n'
          '    # 反例：直接调用 MCP 工具，未验证声明与实际行为一致\n'
          '    return mcp_client.call_tool(name)\n',
          '_TRUSTED_TOOLS = {"search", "calc"}\n'
          '\n'
          'def invoke_tool(name):\n'
          '    # 正例：白名单校验通过后才调用，MCP 服务器沙箱隔离\n'
          '    if name not in _TRUSTED_TOOLS:\n'
          '        raise ValueError("未知工具")\n'
          '    return run_trusted(name)\n',
          'MCP 工具声明与实现可能不一致（投毒面），直接 mcp_call_tool/'
          'tool_call 且不校验工具身份时，外部注入的工具可窃取上下文或'
          '执行任意操作；调用前校验工具白名单，MCP 服务器沙箱隔离。',
          _R_TRAPS_CODING),
    *_SE_RULE_REFS,
]
_GF_DETECT_ALL = (f"{anchor_module('diag_symbol_integrity')} "
                  '(detect_all 编排，B1 file 维度)')
_REG_CHANNEL = (f"{anchor_module('diag_detectors_registry')}.DetectorRegistry "
                '(Gate5 注册表 + B1 注册表通道：DB05/DG01/MP03/DC03/MM03 的'
                '绑定表随规则实现寄宿 diag_rules_expr_forms / diag_pattern_rules / '
                'diag_gate_scope_bind / diag_gate_io_control / diag_gate_class_protocol，'
                '经 diag_detector_assembly._register_rule_bindings 按具名目录批量注册；'
                'AS09/SZ02 随架构门禁规则域 diag_gate_arch 的 rule_bindings 目录注册)')
def _diag4_ref(rule_id: str) -> str:
    return (f"{_GF_DETECT_ALL} check_{rule_id.replace('-', '')}；"
            "编写时直调通道 RD_PREVENTION_CHECKS")
def _registry_ref(rule_id: str) -> str:
    return f"{_REG_CHANNEL} check_{rule_id.replace('-', '')}"
DIAG4_CODE_REFS_VERSION = '1.1.4'
_DIAG4_ENTRIES: list[CodeRef] = [
    make_code_ref(
        SERIES_IMPORTEXTRA, 'RD-26',
        '合并残留：符号既导入又本地定义（含自导入/双重导入）', 'P1',
        (
            'import json\n'
            '\n'
            '\n'
            'def json():\n'
            '    return None\n'
        ),
        (
            'import json\n'
            '\n'
            '\n'
            'def parse(text):\n'
            '    # 合并/迁移收尾自查：模块级导入与模块级定义不得同名共存\n'
            '    return json.loads(text)\n'
        ),
        (
            'AI 执行模块合并/函数迁移/内聚重组时，最典型残留是「from x import f '
            '与 def f() 并存」或「同符号从两条路径导入」——Python 不报错，'
            '运行时按后者覆盖前者，来源歧义直接改变行为。合并收尾必须自查：'
            '模块级导入名 × 模块级定义名求交集，交集非空即删冗余一侧。'
        ),
        _diag4_ref('RD-26'),
    ),
    make_code_ref(
        SERIES_ARCH_EXTRA, 'RD-27',
        'Feature envy：方法集中访问外来对象数据多于自身', 'P2',
        (
            'class Report:\n'
            '    def render(self, invoice):\n'
            '        total = invoice.total + invoice.tax - invoice.discount\n'
            '        return f"{invoice.title}: {total}"\n'
        ),
        (
            'class Report:\n'
            '    def render(self, invoice):\n'
            '        # 数据与行为同置：计算归 Invoice，展示归 Report\n'
            '        return f"{invoice.title}: {invoice.net_total()}"\n'
            '\n'
            '\n'
            'class Invoice:\n'
            '    def net_total(self):\n'
            '        return self.total + self.tax - self.discount\n'
        ),
        (
            '方法对外部对象属性访问显著多于 self（≥3 次且超过 self 两倍）时，'
            '数据与行为分离——改字段/加字段都要跨类同步改，是 AI 生成「工具类'
            '剥数据」的典型反模式。方向：Move Method，把方法主体移到它所'
            '依恋的类（数据所在类），原处留一行委托。'
        ),
        _diag4_ref('RD-27'),
    ),
    make_code_ref(
        SERIES_SECURITY, 'RD-28',
        'SQL 注入：execute() 参数为 f-string/format/% 拼接', 'P0',
        (
            'def get_user(conn, user_id):\n'
            '    return conn.execute(\n'
            '        f"SELECT * FROM users WHERE id={user_id}"\n'
            '    ).fetchone()\n'
        ),
        (
            'def get_user(conn, user_id):\n'
            '    # 参数化查询：占位符由驱动转义，与 SQL 文本分离\n'
            '    return conn.execute(\n'
            '        "SELECT * FROM users WHERE id=?", (user_id,)\n'
            '    ).fetchone()\n'
        ),
        (
            'execute/executemany/raw/text/executescript 的首参为 f-string/'
            'format/%/+ 拼接时即 SQL 注入（OWASP A03:2021，最高频漏洞）：'
            '拼接值一旦含引号或注释符即可改写查询语义。铁律：SQL 文本恒为'
            '常量字符串，用户值恒走占位符元组（?/%s）——无例外。'
        ),
        _diag4_ref('RD-28'),
    ),
    make_code_ref(
        SERIES_ROBUST, 'RD-29',
        '数据库连接泄漏：connect 后未用 with/finally close', 'P1',
        (
            'import sqlite3\n'
            '\n'
            '\n'
            'def query(db_path):\n'
            '    conn = sqlite3.connect(db_path)\n'
            '    return conn.execute("SELECT * FROM t").fetchall()\n'
        ),
        (
            'import sqlite3\n'
            '\n'
            '\n'
            'def query(db_path):\n'
            '    conn = sqlite3.connect(db_path)\n'
            '    try:\n'
            '        return conn.execute("SELECT * FROM t").fetchall()\n'
            '    finally:\n'
            '        conn.close()\n'
        ),
        (
            'connect/create_engine/sessionmaker 创建的连接若无 with 包裹或'
            'try-finally close，异常路径连接永不释放，累积耗尽连接池/文件'
            '句柄。注意 Python 陷阱：with sqlite3.connect() 管理的是事务'
            '而非连接关闭——标准可靠写法是 try/finally 显式 close（或'
            'contextlib.closing 包裹）。'
        ),
        _diag4_ref('RD-29'),
    ),
    make_code_ref(
        SERIES_ROBUST, 'RD-30',
        '事务未关闭：写操作后缺少 commit/rollback', 'P1',
        (
            'def add_user(conn, name):\n'
            '    conn.execute(\n'
            '        "INSERT INTO users (name) VALUES (?)", (name,)\n'
            '    )\n'
        ),
        (
            'def add_user(conn, name):\n'
            '    try:\n'
            '        conn.execute(\n'
            '            "INSERT INTO users (name) VALUES (?)", (name,)\n'
            '        )\n'
            '        conn.commit()\n'
            '    except Exception:\n'
            '        # 回滚后原样抛出；非数据库异常也不能留下悬挂事务\n'
            '        conn.rollback()\n'
            '        raise\n'
        ),
        (
            '函数内 execute 写操作（INSERT/UPDATE/DELETE/CREATE/DROP/'
            'ALTER/REPLACE）而无 commit/rollback 时，事务悬挂：连接关闭时'
            '写操作被静默回滚——代码看似执行成功、数据从未落库，是「跑完'
            '没报错但结果丢了」的典型静默 BUG。写操作后必须显式 commit'
            '（异常路径 rollback）。'
        ),
        _diag4_ref('RD-30'),
    ),
    make_code_ref(
        SERIES_SECURITY, 'RD-31',
        '硬编码数据库凭证：连接字符串/参数含明文密码', 'P0',
        (
            'import psycopg2\n'
            '\n'
            '\n'
            'def connect_db():\n'
            '    return psycopg2.connect(\n'
            '        "postgresql://admin:Sup3rS3cret@db.example.com/prod"\n'
            '    )\n'
        ),
        (
            'import os\n'
            'import psycopg2\n'
            '\n'
            '\n'
            'def connect_db():\n'
            '    # 凭证只走环境变量/密钥管理，代码库零明文\n'
            '    user = os.environ.get("DB_USER")\n'
            '    password = os.environ.get("DB_PASSWORD")\n'
            '    if not user or not password:\n'
            '        raise RuntimeError("DB_USER/DB_PASSWORD must be configured")\n'
            '    return psycopg2.connect(\n'
            '        host="db.example.com", dbname="prod",\n'
            '        user=user, password=password,\n'
            '    )\n'
        ),
        (
            '连接字符串（postgres/mysql/redis://<user>:<pwd>@<host>）或 connect'
            '(password=...) 中的明文密码属 OWASP A07:2021/CWE-798：git '
            '历史/日志/异常堆栈都会泄出。AI 生成演示代码时尤爱编造真实'
            '形态密码串——凭证恒走 os.environ / .env（入 .gitignore）/ '
            'Secrets Manager，占位符模板（${DB_PASSWORD}）不算硬编码；必填变量'
            '缺失时明确 fail-fast，不能用空密码默认值静默降级。'
        ),
        _diag4_ref('RD-31'),
    ),
    make_code_ref(
        SERIES_SECURITY, 'RD-32',
        'ORM raw()/extra() 使用未净化输入', 'P1',
        (
            'def find_user(name):\n'
            '    return User.objects.raw(\n'
            '        f"SELECT * FROM app_user WHERE name=\'{name}\'"\n'
            '    )\n'
        ),
        (
            'def find_user(name):\n'
            '    # ORM raw 参数化：SQL 常量 + 参数列表分离\n'
            '    return User.objects.raw(\n'
            '        "SELECT * FROM app_user WHERE name=%s", [name]\n'
            '    )\n'
        ),
        (
            'raw()/extra()/from_statement()/exec_driver_sql() 是 ORM 留的'
            '逃生舱，AI 常把 f-string/变量直接塞进去——绕过了 ORM 的自动'
            '转义，注入面与裸 SQL 完全相同。raw 的参数化形态是「SQL 常量 + '
            'params 列表」两参；变量/拼接/ format 形态一律按注入处理。'
        ),
        _diag4_ref('RD-32'),
    ),
    make_code_ref(
        SERIES_PYTRAP, 'DB-05',
        'SQLite PRAGMA 不支持 ? 占位符——执行即 OperationalError', 'P0',
        (
            'def set_timeout(conn, ms):\n'
            '    conn.execute("PRAGMA busy_timeout=?", (ms,))\n'
        ),
        (
            'def set_timeout(conn, ms):\n'
            '    # PRAGMA 语句不支持占位符：整条语句字符串内联值\n'
            '    conn.execute(f"PRAGMA busy_timeout={int(ms)}")\n'
        ),
        (
            'AI 高频幻觉：以为 execute 的 ? 占位符对一切 SQL 生效——'
            'SQLite 的 PRAGMA 语句不支持参数绑定，conn.execute('
            '"PRAGMA busy_timeout=?", (ms,)) 在 prepare 阶段即抛 '
            'sqlite3.OperationalError: near "?": syntax error，'
            '不是静默忽略。PRAGMA 值必须内联进语句字符串（int() '
            '钳制防注入），这是「把不支持绑定的语句当参数化 API」的'
            '典型形态。'
        ),
        _registry_ref('DB-05'),
    ),
    make_code_ref(
        SERIES_PYTRAP, 'MP-03',
        '__getattr__ 内 self.attr 访问触发递归自调用', 'P1',
        (
            'class Config:\n'
            '    def __getattr__(self, name):\n'
            '        return self.defaults[name]\n'
        ),
        (
            'class Config:\n'
            '    def __init__(self, values):\n'
            '        # 内部表放实例 __dict__，__getattr__ 只读它\n'
            '        self._values = dict(values)\n'
            '\n'
            '    def __getattr__(self, name):\n'
            '        try:\n'
            '            return self.__dict__["_values"][name]\n'
            '        except KeyError:\n'
            '            # 未命中必须抛 AttributeError，返回 None 会让 hasattr 恒真\n'
            '            raise AttributeError(name) from None\n'
        ),
        (
            '__getattr__ 只在属性「未找到」时被调用——方法体内访问 '
            'self.defaults 时若 defaults 本身也不存在，会再次触发 '
            '__getattr__，无限递归直至 RecursionError。方法体内只允许'
            'self.__dict__/self.__class__ 等豁免访问，其余一律走 '
            'object.__getattribute__ 或 __dict__。'
        ),
        _registry_ref('MP-03'),
    ),
    make_code_ref(
        SERIES_DQUALITY, 'AS-09', '文件行数超过项目预算：治理收益评估', 'P2',
        (
            '# 示意（真实命中需 >4000 行文件）：\n'
            '# 单文件持续追加函数而不拆分，模块行数无预算上限，\n'
            '# 直到任何定位/审阅/合并冲突成本都随行数线性恶化。\n'
            'def part_3970():\n'
            '    pass\n'
        ),
        (
            '# 编写前预算：遵循目标项目声明；未声明时采用检测器默认值，\n'
            '# 接近预算时先简化逻辑、消除重复并评估代码迁移净收益，\n'
            '# 不预设拆分文件；治理方式由当前项目结构与风险决定。\n'
            'def normalize_items(items):\n'
            '    return [str(item).strip() for item in items if str(item).strip()]\n'
        ),
        (
            '文件行数是定位成本、审阅成本、合并冲突面的共同放大器。'
            '检测器默认以 4000 行作为评估信号，但这不是所有项目统一的硬上限；'
            '目标项目已有体积预算时遵循项目声明。接近预算后应比较简化逻辑、'
            '消除重复、收敛依赖与代码迁移的风险和净收益，不预设拆分文件。'
            '默认信号需要真实 4000+ 行文件才会命中，故本条仅编写前文本注入。'
        ),
        _registry_ref('AS-09'),
        self_verifiable=False,
    ),
    make_code_ref(
        SERIES_ROBUST, 'DG-01',
        'd.get(k, []).append(v) 原地修改可能被丢弃', 'P1',
        (
            'def collect(groups, key, val):\n'
            '    groups.get(key, []).append(val)\n'
        ),
        (
            'def collect(groups, key, val):\n'
            '    # setdefault 取的是字典内真实引用，修改会写回\n'
            '    groups.setdefault(key, []).append(val)\n'
        ),
        (
            'd.get(k, []) 返回的默认值是**临时新建对象**——键缺失时对它'
            'append 的结果不会写回字典，该分支静默丢数据；键存在时返回'
            '字典内的真实引用，修改有效。这是 AI 高频真实缺陷：写法自然、'
            '不报错、测试漏键分支就通过。正确形态：'
            'd.setdefault(k, []).append(v)（取字典内真实引用）或 '
            'if k not in d: d[k] = [] 显式初始化。'
        ),
        _registry_ref('DG-01'),
    ),
    make_code_ref(
        SERIES_PYTRAP, 'DC-03',
        '同名顶级函数重复定义——前者被静默覆盖', 'P0',
        (
            'def build_report(rows):\n'
            '    return {"rows": rows}\n'
            '\n'
            '\n'
            'def build_report(rows, title):\n'
            '    return {"rows": rows, "title": title}\n'
        ),
        (
            '_UNSET = object()\n'
            '\n'
            '\n'
            'def build_report(rows, title=_UNSET):\n'
            '    # 哨兵区分未传 title 与显式空值，保持两种旧调用返回结构\n'
            '    report = {"rows": rows}\n'
            '    if title is not _UNSET:\n'
            '        report["title"] = title\n'
            '    return report\n'
        ),
        (
            'Python 对同名顶级函数不报错：后定义静默覆盖前定义——'
            'AI 在长文件尾部追加函数时尤易与既有同名函数相撞，旧实现的'
            '行为无声丢失，调用方拿到的是另一份实现。合并/追加代码时'
            '先按名查重；重复定义要么合并（用哨兵兼容参数与返回结构），'
            '要么改名，有意重载须注释说明。'
        ),
        _registry_ref('DC-03'),
    ),
    make_code_ref(
        SERIES_PYTRAP, 'MM-03',
        '__del__ 参与循环引用时回收时机不可控', 'P2',
        (
            'class Node:\n'
            '    def __init__(self, parent=None):\n'
            '        self.parent = parent\n'
            '        self.children = []\n'
            '\n'
            '    def __del__(self):\n'
            '        self.cleanup()\n'
        ),
        (
            'import weakref\n'
            '\n'
            '\n'
            'class Node:\n'
            '    def __init__(self, parent=None):\n'
            '        # 回指用弱引用打破循环；清理走显式 close()\n'
            '        self._parent = weakref.ref(parent) if parent is not None else None\n'
            '        self.children = []\n'
            '\n'
            '    def cleanup(self):\n'
            '        self.children.clear()\n'
            '\n'
            '    def close(self):\n'
            '        self.cleanup()\n'
        ),
        (
            '定义 __del__ 的对象参与循环引用时（parent↔children 互指是'
            '最常见形态），回收从引用计数即时释放降级为等待 GC 代际'
            '扫描——PEP 442（3.4+）起 GC 可回收该类对象，但时机不可控'
            '且批量滞留，长驻进程内存随行增长；__del__ 在 GC 期间'
            '执行，解释器关闭阶段模块全局可能已清理，方法体内引用'
            '全局资源即 AttributeError。'
            '替代：回指边用 weakref.ref；清理职责用显式 close()/上下文'
            '管理器（__enter__/__exit__）承载，不依赖 __del__。'
        ),
        _registry_ref('MM-03'),
    ),
]
DIAG_SUPPLEMENT_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    [
        *_IMPORTEXTRA_REFS,
        *_BUG_REFS,
        *_DSTRUCT_REFS,
        *_DQUALITY_REFS,
        *_SECURITY_REFS,
    ],
    "DIAG_SUPPLEMENT_CODE_REFS",
)
DIAG4_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    _DIAG4_ENTRIES, "DIAG4_CODE_REFS",
)
register_code_refs(DIAG_SUPPLEMENT_CODE_REFS,
                   "prevention_diag_extra")
register_code_refs(DIAG4_CODE_REFS,
                   "prevention_diag_extra:diag4")
