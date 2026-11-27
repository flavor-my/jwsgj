from __future__ import annotations

import logging

from jwsgj.prevention_refs_main import (
    DETECTOR_REF_GATE3_ARCH,
    CodeRef,
    anchor_module,
    build_keyed_registry,
    make_code_ref,
    register_code_refs,
)

__all__ = [
    'DIAG_CORE_CODE_REFS',
    'GOV_CODE_REFS',
    'SERIES_ARCH_EXTRA',
    'SERIES_DEPRECATED',
    'SERIES_HALLUC',
    'SERIES_IO',
    'SERIES_ROBUST',
    'SERIES_TRAP',
]
_log = logging.getLogger(__name__)
_log.info("prevention_diag_refs 主域诊断规则代码引用预防库已加载: %d 项导出", len(__all__))
SERIES_TRAP = "trap"
SERIES_IO = "io"
SERIES_HALLUC = "halluc"
SERIES_DEPRECATED = "deprecated"
SERIES_ROBUST = "robust"
SERIES_ARCH_EXTRA = "arch_extra"
def _registry_channel(ids: str) -> str:
    return f' (DetectorRegistry: {ids} 编写时 preflight_diagnostic_check)'
_R_TRAP = (anchor_module('diag_traps_binding') + ' + ' + anchor_module('diag_traps_guard') + ' + ' + anchor_module('diag_traps_blocking') + _registry_channel('LK02/CN01/HC02/RT01/RT02/RL03/TP05/TP07/TP11/TP23/TP25/CL03/FS01'))
_R_TRAP_NUMERIC = anchor_module('diag_rules_expr_forms') + _registry_channel('TP17/TP19')
_R_IO_SAFE = (anchor_module('diag_traps_blocking') + ' (IO01 源码树通道)'
              + ' + ' + anchor_module('diag_gate_io_control')
              + ' (IO05 源码树通道)' + _registry_channel('IO03'))
_R_EXC_FLOW = anchor_module('diag_wiring_exc_flow') + _registry_channel('EX04/EX06/EX07/EH04/EH05')
_R_EXC_SILENCE = anchor_module('diag_wiring_exc') + _registry_channel('RF01')
_R_IMP_HYG = anchor_module('diag_wiring_imports') + _registry_channel('IM05')
_R_EX08 = anchor_module('diag_rules_runtime') + _registry_channel('EX08')
_R_TO = anchor_module('diag_traps_blocking') + _registry_channel('TO02')
_R_HALLUC = (anchor_module('diag_symbol_surface') + ' (H01/H02/H09 符号解析族+grounding域契约) + ' + anchor_module('hallucination_norms') + ' (H03-H08 规则族: 逻辑矛盾/实质缺失/外部断言 + 统一编排)')
_R_DEPRECATED = anchor_module('diag_rules_api_risk') + _registry_channel('DP05/DP10/DP11/DP12/DP32/DP33/DP39/DP45/DP47')
_R_DEPRECATED_NAMES = anchor_module('diag_rules_api_risk') + _registry_channel('DP04/DP07/DP08/DP09/DP49')
_R_ROBUST = anchor_module('diag_rules_expr_forms') + _registry_channel('BZ01/DF03/IC01/TY02')
_R_ROBUST_PKGFS = anchor_module('diag_rules_runtime') + _registry_channel('DG02/EP02/NS01')
_R_TRAPS_PAYLOAD = (anchor_module('diag_traps_payload')
                   + ' (EN01 源码树通道)' + _registry_channel('EN03/SP01'))
_R_SPLIT = anchor_module('diag_wiring_imports') + _registry_channel('SL01')
_TRAP_REFS: list[CodeRef] = [
    make_code_ref(SERIES_TRAP, 'LK-02', '多锁获取无统一顺序（死锁）', 'P1',
          "import threading\n"
          "\n"
          "lock_a = threading.Lock()\n"
          "lock_b = threading.Lock()\n"
          "\n"
          "\n"
          "def update_first_second():\n"
          "    with lock_a:\n"
          "        with lock_b:\n"
          "            return 'a-then-b'\n"
          "\n"
          "\n"
          "def update_second_first():\n"
          "    with lock_b:\n"
          "        with lock_a:\n"
          "            return 'b-then-a'",
          "import threading\n"
          "\n"
          "lock_a = threading.Lock()\n"
          "lock_b = threading.Lock()\n"
          "\n"
          "\n"
          "def update_first_second():\n"
          "    # 全部路径按固定顺序 lock_a -> lock_b 获取\n"
          "    with lock_a, lock_b:\n"
          "        return 'a-then-b'\n"
          "\n"
          "\n"
          "def update_second_first():\n"
          "    with lock_a, lock_b:\n"
          "        return 'same-order'",
          '两个线程各自持有一把锁并等待对方时形成循环等待；全部路径按固定顺序获取可破坏循环等待条件',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'CN-01', 'threading.local 用于线程池', 'P1',
          "import threading\n"
          "from concurrent.futures import ThreadPoolExecutor\n"
          "\n"
          "ctx = threading.local()\n"
          "\n"
          "\n"
          "def handle(request_id):\n"
          "    # worker 线程复用, ctx 中的请求级数据跨任务残留\n"
          "    ctx.request_id = request_id\n"
          "    return ctx.request_id\n"
          "\n"
          "\n"
          "def run_all(ids):\n"
          "    with ThreadPoolExecutor(max_workers=4) as pool:\n"
          "        return list(pool.map(handle, ids))",
          "from concurrent.futures import ThreadPoolExecutor\n"
          "\n"
          "\n"
          "def handle(request_id):\n"
          "    # 任务级状态经参数传入, 结果经返回值传出\n"
          "    return request_id\n"
          "\n"
          "\n"
          "def run_all(ids):\n"
          "    with ThreadPoolExecutor(max_workers=4) as pool:\n"
          "        return list(pool.map(handle, ids))",
          '线程池 worker 复用线程，threading.local 数据与线程绑定而非任务绑定，跨任务残留且对提交方不可见',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'HC-02', 'requests 请求参数 bool 未序列化', 'P1',
          "import requests\n"
          "\n"
          "\n"
          "def fetch(flag):\n"
          "    return requests.get(\n"
          "        'https://api.example.com/items',\n"
          "        params={'active': True},\n"
          "        timeout=30,\n"
          "    )",
          "import requests\n"
          "\n"
          "\n"
          "def fetch(flag):\n"
          "    return requests.get(\n"
          "        'https://api.example.com/items',\n"
          "        params={'active': str(flag).lower()},\n"
          "        timeout=30,\n"
          "    )",
          "Python bool 序列化为 'True'/'False'，多数 Web API 仅识别 'true'/'false'，参数被静默忽略",
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'RT-02', '查询结果直接调用 dict 视图方法', 'P2',
          "def summarize(cursor):\n"
          "    return list(cursor.fetchone().values())",
          "def summarize(cursor):\n"
          "    row = cursor.fetchone()\n"
          "    # fetchone 返回 tuple/Row, 按位置或配套访问器取值;\n"
          "    # 无行时返回 None, 直接 list(row) 抛 TypeError\n"
          "    if row is None:\n"
          "        return []\n"
          "    return list(row)",
          'execute/fetchone/fetchall 返回 list[tuple] 或 Row 对象，直接 .values()/.keys() 触发 AttributeError；无结果行时 fetchone 返回 None，链式取值同为崩溃点，须显式判空',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'SP-01', 'subprocess text=True 缺 encoding', 'P1',
          "import subprocess\n"
          "\n"
          "\n"
          "def run_tool(cmd):\n"
          "    proc = subprocess.run(cmd, capture_output=True, text=True)\n"
          "    return proc.stdout",
          "import subprocess\n"
          "\n"
          "\n"
          "def run_tool(cmd):\n"
          "    proc = subprocess.run(\n"
          "        cmd, capture_output=True, text=True, encoding='utf-8',\n"
          "        timeout=30,\n"
          "    )\n"
          "    return proc.stdout",
          "text=True 走系统本地代码页（Windows 为 GBK），UTF-8 输出即 UnicodeDecodeError，结果整体丢失",
          _R_TRAPS_PAYLOAD),
    make_code_ref(SERIES_TRAP, 'RL-03', '同文件多处 __version__ 不一致', 'P1',
          "__version__ = '1.2.0'\n"
          "\n"
          "\n"
          "def get_version():\n"
          "    return __version__\n"
          "\n"
          "\n"
          "__version__ = '1.2.1'",
          "__version__ = '1.2.1'\n"
          "\n"
          "\n"
          "def get_version():\n"
          "    return __version__",
          '多处声明值漂移后导入方按访问顺序拿到不同版本号，兼容性判断随机失效；版本号只保留一处 SSOT',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'TP-05', 'except 块引用未定义名称', 'P1',
          "def load(path):\n"
          "    try:\n"
          "        with open(path, encoding='utf-8') as f:\n"
          "            return f.read()\n"
          "    except OSError:\n"
          "        # _log 从未定义/导入, 异常路径首次触发即 NameError\n"
          "        _log.warning('load failed: %s', path)\n"
          "        return ''",
          "import logging\n"
          "\n"
          "_log = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def load(path):\n"
          "    try:\n"
          "        with open(path, encoding='utf-8') as f:\n"
          "            return f.read()\n"
          "    except OSError:\n"
          "        _log.warning('load failed: %s', path)\n"
          "        return ''",
          '异常处理块引用从未定义/导入的名称（如 _log），该路径首次触发即 NameError，掩盖原始异常',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'TP-07', '模块级可变全局被原地修改', 'P1',
          "RESULTS = []\n"
          "\n"
          "\n"
          "def record(item):\n"
          "    RESULTS.append(item)\n"
          "    return len(RESULTS)",
          "def build_results(items):\n"
          "    # 函数内局部构建返回, 不共享模块级可变状态\n"
          "    results = []\n"
          "    for item in items:\n"
          "        results.append(item)\n"
          "    return results",
          '模块级 list/dict/set 是进程内共享状态，原地修改对所有导入方立即可见，多入口并发产生竞态与状态残留',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'TP-11', '链式 replace 返回值未接收', 'P1',
          "def normalize(text):\n"
          "    text.replace(', ', ',')\n"
          "    text.replace('; ', ';')\n"
          "    return text",
          "def normalize(text):\n"
          "    text = text.replace(', ', ',')\n"
          "    text = text.replace('; ', ';')\n"
          "    return text",
          'str 不可变，replace 返回新对象；裸调用语句 s.replace(a, b) 的替换全部静默丢失',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'TP-17', '指标硬编码 0.0 占位', 'P2',
          "def evaluate(predictions):\n"
          "    if not predictions:\n"
          "        # 未计算路径以 0.0 作为最终结果返回\n"
          "        score = 0.0\n"
          "        return score\n"
          "    return sum(predictions) / len(predictions)",
          "def evaluate(predictions):\n"
          "    if not predictions:\n"
          "        # 未计算用 None, 消费侧显式区分「没算」与「算了得 0 分」\n"
          "        return None\n"
          "    return sum(predictions) / len(predictions)",
          '指标未计算时以 0.0 占位落盘，下游无法区分「没算」与「算了得 0 分」，掩盖计算链断裂',
          _R_TRAP_NUMERIC),
    make_code_ref(SERIES_TRAP, 'TP-19', '关键参数硬编码 0', 'P2',
          "def run_tool(cmd):\n"
          "    return run_command(cmd, timeout=0)",
          "def run_tool(cmd):\n"
          "    # timeout=0 会立即超时; 显式传业务语义值\n"
          "    return run_command(cmd, timeout=30)",
          'threshold=0 使判断恒真/恒假、timeout=0 立即超时、limit=0 空结果，静默改变业务语义',
          _R_TRAP_NUMERIC),
    make_code_ref(SERIES_TRAP, 'TP-23', '缓存只写无失效操作', 'P3',
          "_cache = {}\n"
          "\n"
          "\n"
          "def get_value(key, compute):\n"
          "    if key not in _cache:\n"
          "        _cache[key] = compute(key)\n"
          "    return _cache[key]",
          "_cache = {}\n"
          "\n"
          "\n"
          "def get_value(key, compute):\n"
          "    if key not in _cache:\n"
          "        _cache[key] = compute(key)\n"
          "    return _cache[key]\n"
          "\n"
          "\n"
          "def reset_cache():\n"
          "    # 提供失效入口, 关键写路径调用防止数据陈旧\n"
          "    _cache.clear()",
          '模块级缓存只写不清，长生命周期进程内存单调增长且数据陈旧；须提供 clear/TTL/容量上限',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'TP-25', '多版本函数参数签名不一致', 'P1',
          "def parse_v1(text):\n"
          "    return text.strip()\n"
          "\n"
          "\n"
          "def parse_v2(text, strict):\n"
          "    return text.strip() if strict else text",
          "def parse_v1(text, strict=True):\n"
          "    # 签名对齐且保留 v1 默认 strip 行为, 调用方显式传 False 可关闭\n"
          "    return text.strip() if strict else text\n"
          "\n"
          "\n"
          "def parse_v2(text, strict=True):\n"
          "    return text.strip() if strict else text",
          '同名多版本实现（_v1/_v2）参数不同步，按版本路由的调用方拿到静默错误输出；统一参数名和默认值时必须保持既有无参调用行为',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'CL-03', 'dir() 用于存在性检测', 'P3',
          "def has_helper():\n"
          "    return 'helper' in dir()",
          "def has_helper(obj):\n"
          "    # 属性用 hasattr, 全局名用 'x' in globals()\n"
          "    return hasattr(obj, 'helper')",
          'dir() 返回名字列表而非对象，函数内调用只列当前局部名（模块级名字不在其中）；hasattr/globals() 才是正确工具',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'RT-01', '函数返回深嵌套 dict 字面量', 'P3',
          "def build_report(status, items):\n"
          "    return {\n"
          "        'status': status,\n"
          "        'summary': {\n"
          "            'count': len(items),\n"
          "            'detail': {\n"
          "                'first': items[0] if items else None,\n"
          "                'last': items[-1] if items else None,\n"
          "            },\n"
          "        },\n"
          "    }",
          "from dataclasses import dataclass\n"
          "\n"
          "\n"
          "@dataclass\n"
          "class ReportDetail:\n"
          "    first: object | None = None\n"
          "    last: object | None = None\n"
          "\n"
          "\n"
          "@dataclass\n"
          "class ReportSummary:\n"
          "    count: int = 0\n"
          "    detail: ReportDetail | None = None\n"
          "\n"
          "\n"
          "@dataclass\n"
          "class Report:\n"
          "    status: str = ''\n"
          "    summary: ReportSummary | None = None\n"
          "\n"
          "\n"
          "def build_report(status, items):\n"
          "    # 结构契约显式化, 键名漂移在类型检查期暴露\n"
          "    return Report(\n"
          "        status=status,\n"
          "        summary=ReportSummary(\n"
          "            count=len(items),\n"
          "            detail=ReportDetail(\n"
          "                first=items[0] if items else None,\n"
          "                last=items[-1] if items else None,\n"
          "            ),\n"
          "        ),\n"
          "    )",
          '≥3 层嵌套 dict 返回值缺少结构契约，消费方层层 .get() 取值，键名漂移静默返回 None',
          _R_TRAP),
    make_code_ref(SERIES_TRAP, 'FS-01', 'os.getenv 缺默认值', 'P2',
          "import os\n"
          "\n"
          "\n"
          "def get_home():\n"
          "    return os.getenv('APP_HOME')",
          "import os\n"
          "\n"
          "\n"
          "def get_home(default_home):\n"
          "    # 默认根由当前项目注入, 关键变量缺失也可改为显式报错\n"
          "    return os.getenv('APP_HOME', default_home)",
          '环境变量缺失时 getenv 返回 None，直接参与路径拼接抛 TypeError 或生成 "None/xxx" 假路径',
          _R_TRAP),
]
_IO_REFS: list[CodeRef] = [
    make_code_ref(SERIES_IO, 'IO-01', 'requests 调用缺 timeout', 'P1',
          "import requests\n"
          "\n"
          "\n"
          "def fetch(url):\n"
          "    return requests.get(url)",
          "import requests\n"
          "\n"
          "\n"
          "def fetch(url):\n"
          "    return requests.get(url, timeout=30)",
          '未设置 timeout 的网络请求可能永久阻塞调用线程，拖垮整个服务',
          _R_IO_SAFE),
    make_code_ref(SERIES_IO, 'IO-05', 'open() 缺 encoding 参数', 'P1',
          "def read_text(path):\n"
          "    with open(path) as f:\n"
          "        return f.read()",
          "def read_text(path):\n"
          "    with open(path, encoding='utf-8') as f:\n"
          "        return f.read()",
          "不指定 encoding 时用系统本地代码页（Windows 为 GBK），跨平台读写非 ASCII 内容即乱码或 UnicodeDecodeError",
          _R_IO_SAFE),
    make_code_ref(SERIES_IO, 'EX-06', 'except 块引用未绑定异常名', 'P0',
          "def parse(text):\n"
          "    try:\n"
          "        return int(text)\n"
          "    except Exception:\n"
          "        # e 从未被 as e 绑定, 此引用即 NameError\n"
          "        return e",
          "import logging\n"
          "\n"
          "_log = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def parse(text):\n"
          "    try:\n"
          "        return int(text)\n"
          "    except ValueError as exc:\n"
          "        _log.warning('parse failed: %s', exc)\n"
          "        return 0",
          'except Exception: 未用 as e 绑定，块内引用 e 即 NameError，异常路径二次崩溃',
          _R_EXC_FLOW),
    make_code_ref(SERIES_IO, 'EX-07', '异常绑定名与引用名不一致', 'P0',
          "def parse(text):\n"
          "    try:\n"
          "        return int(text)\n"
          "    except Exception as e:\n"
          "        # 绑定名是 e, 引用名却是 _e\n"
          "        return _e",
          "def parse(text):\n"
          "    try:\n"
          "        return int(text)\n"
          "    except ValueError as err:\n"
          "        raise ValueError(f'invalid integer: {text!r}') from err",
          'as e 绑定后引用 _e/err 等不一致变量名，运行时 NameError 掩盖原始异常',
          _R_EXC_FLOW),
    make_code_ref(SERIES_IO, 'EX-08', '重复 except 处理块', 'P2',
          "def convert(value):\n"
          "    try:\n"
          "        return int(value)\n"
          "    except ValueError:\n"
          "        return 0\n"
          "    except TypeError:\n"
          "        return 0",
          "def convert(value):\n"
          "    try:\n"
          "        return int(value)\n"
          "    except (ValueError, TypeError):\n"
          "        # 不同类型, 相同处理逻辑合并为一个 except 子句\n"
          "        return 0",
          '不同异常类型、处理逻辑完全相同的分支应合并为 except (T1, T2):，重复分支是漂移起点',
          _R_EX08),
    make_code_ref(SERIES_IO, 'EH-04', 'raise 新异常未显式链接原始异常', 'P1',
          "def load(path):\n"
          "    try:\n"
          "        with open(path, encoding='utf-8') as f:\n"
          "            return f.read()\n"
          "    except OSError:\n"
          "        raise RuntimeError('load failed')",
          "def load(path):\n"
          "    try:\n"
          "        with open(path, encoding='utf-8') as f:\n"
          "            return f.read()\n"
          "    except OSError as exc:\n"
          "        # from exc 保留原始异常链与堆栈, 根因可追溯\n"
          "        raise RuntimeError('load failed') from exc",
          '异常处理中直接 raise 新异常会自动设置隐式 __context__ 并保留原堆栈，但显示为“处理过程中发生另一异常”，主动转换与次生故障不易区分；raise ... from exc 显式设置 __cause__，明确转换关系并保留原始堆栈',
          _R_EXC_FLOW),
    make_code_ref(SERIES_IO, 'EH-05', '捕获的异常对象未使用', 'P2',
          "def parse(text):\n"
          "    try:\n"
          "        return int(text)\n"
          "    except ValueError as e:\n"
          "        return 0",
          "import logging\n"
          "\n"
          "log = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def parse(text):\n"
          "    try:\n"
          "        return int(text)\n"
          "    except ValueError as e:\n"
          "        # 捕获的异常对象至少被记录或向上传播\n"
          "        log.warning('parse failed: %s', e)\n"
          "        return 0",
          'as e 后 e 从未被读取，异常上下文被静默丢弃；至少记录日志或向上传播',
          _R_EXC_FLOW),
    make_code_ref(SERIES_IO, 'SL-01', '空串 in str() 恒真条件', 'P0',
          "def is_blank(text):\n"
          "    return '' in str(text)",
          "def is_blank(text):\n"
          "    # 空串是任意字符串的子串, 恒真; 用显式语义判断\n"
          "    return not str(text).strip()",
          "空字符串是任意字符串的子串，'' in s 恒为 True，条件判断失去分支意义",
          _R_SPLIT),
    make_code_ref(SERIES_IO, 'RF-01', 'except 块仅 pass 无注释', 'P1',
          "def load(path):\n"
          "    try:\n"
          "        with open(path, encoding='utf-8') as f:\n"
          "            return f.read()\n"
          "    except Exception:\n"
          "        pass",
          "import logging\n"
          "\n"
          "logger = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def load(path):\n"
          "    try:\n"
          "        with open(path, encoding='utf-8') as f:\n"
          "            return f.read()\n"
          "    except OSError:\n"
          "        # 有意忽略须留注释说明理由, 否则必须记录或传播\n"
          "        logger.warning('optional file missing: %s', path)\n"
          "        return ''",
          '无注释的 except: pass 是无声吞错，故障被推迟到难以定位的位置；有意忽略必须写明理由',
          _R_EXC_SILENCE),
    make_code_ref(SERIES_IO, 'TO-02', 'subprocess 缺 timeout', 'P1',
          "import subprocess\n"
          "\n"
          "\n"
          "def run_tool(cmd):\n"
          "    proc = subprocess.run(cmd, capture_output=True)\n"
          "    return proc.returncode",
          "import subprocess\n"
          "\n"
          "\n"
          "def run_tool(cmd):\n"
          "    # 无 timeout 的子进程可能永久阻塞调用线程\n"
          "    proc = subprocess.run(cmd, capture_output=True, timeout=30)\n"
          "    return proc.returncode",
          '无 timeout 的子进程可能永久挂起，调用线程永久阻塞',
          _R_TO),
    make_code_ref(SERIES_IO, 'IM-05', '使用 logging 未导入', 'P0',
          "def setup():\n"
          "    # logger 从未导入/定义, 运行时 NameError\n"
          "    logger.info('ready')",
          "import logging\n"
          "\n"
          "log = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def setup():\n"
          "    log.info('ready')",
          "引用 logging/logger 等符号但未 import logging，运行时 NameError（示例为 name 'logger' is not defined）",
          _R_IMP_HYG),
    make_code_ref(SERIES_IO, 'IO-03', 'httpx/aiohttp 调用未设置 timeout', 'P2',
          'import httpx\n'
          '\n'
          'def fetch(url):\n'
          '    # 反例：未设置 timeout，网络异常时可能永久阻塞\n'
          '    return httpx.get(url)\n',
          'import httpx\n'
          '\n'
          'def fetch(url):\n'
          '    # 正例：显式设置 timeout，避免永久阻塞\n'
          '    return httpx.get(url, timeout=30.0)\n',
          'httpx/aiohttp 的 get/post/put/delete/patch 若不传 timeout，'
          '超时行为取决于库默认值（httpx 5s；aiohttp 会话默认 300s 总超时），'
          '默认值与业务耗时不符时请求被过早截断或长时间阻塞；生产代码一律显式'
          'timeout（requests 同规则见 IO-01 通道）。',
          _R_IO_SAFE),
    make_code_ref(SERIES_IO, 'EN-01', 'open() 文本模式未指定 encoding', 'P2',
          'def read_text(path):\n'
          '    # 反例：依赖平台默认编码（Windows cp936/gbk），跨平台炸\n'
          '    with open(path, "r") as f:\n'
          '        return f.read()\n',
          'def read_text(path):\n'
          '    # 正例：显式 encoding；二进制模式（"rb"/"wb"）可省略\n'
          '    with open(path, "r", encoding="utf-8") as f:\n'
          '        return f.read()\n',
          'open() 文本模式未指定 encoding 时使用平台默认编码'
          '（Windows: cp936/gbk，Linux: UTF-8），同一份 UTF-8 文件在 Windows 上'
          '读取即抛 UnicodeDecodeError；AI 生成代码默认写 encoding="utf-8"'
          '（PEP 597 方向）。',
          _R_TRAPS_PAYLOAD),
    make_code_ref(SERIES_IO, 'EN-03', '非 UTF-8 家族编码声明 + 非 ASCII 字符', 'P3',
          '# -*- coding: gbk -*-\n'
          '"""中文说明文档字符串"""\n',
          '# -*- coding: utf-8 -*-\n'
          '"""中文说明文档字符串"""\n',
          'Python 3 源码默认 UTF-8（PEP 3120），声明 gbk/cp936 等非 UTF-8 家族'
          '编码且含非 ASCII 字符时，不同工具链按声明/按默认解码结果不一致，'
          '产生乱码风险；直接省略声明或声明 UTF-8 家族编码。',
          _R_TRAPS_PAYLOAD),
]
_HALLUC_REFS: list[CodeRef] = [
    make_code_ref(SERIES_HALLUC, 'H01', '幻觉 API 调用', 'P0',
          "def fetch_rows(cursor):\n"
          "    # _fetch_all_rows 是凭空脑补的 API, 作用域中不存在\n"
          "    return _fetch_all_rows(cursor)",
          "def fetch_rows(cursor):\n"
          "    # 只调用当前作用域或导入链中真实存在的函数\n"
          "    return cursor.fetchall()",
          '凭空脑补的函数/对象名不在当前作用域、导入链或内置中，运行时 NameError；每个调用都须确认真实存在',
          _R_HALLUC),
    make_code_ref(SERIES_HALLUC, 'H02', '幻觉导入（* 导入下划线名）', 'P0',
          "from os import *\n"
          "\n"
          "\n"
          "def get_environ_type():\n"
          "    # _Environ 真实存在于 os, 但不在 os.__all__, import * 不导入\n"
          "    return _Environ",
          "from os import _Environ\n"
          "\n"
          "\n"
          "def get_environ_type():\n"
          "    # 下划线名必须显式导入\n"
          "    return _Environ",
          'import * 绑定面以源模块 __all__ 为准，未入 __all__ 的下划线名不被导入，凭星号导入使用此类 _name 即 NameError，须显式导入（os._exit 已入 os.__all__ 会被星号导入绑定，故载体用未入 __all__ 的 os._Environ）',
          _R_HALLUC),
    make_code_ref(SERIES_HALLUC, 'H03', '宽泛捕获吞掉幻觉异常', 'P0',
          "# _read_json 是凭空脑补的 API；except Exception: pass 把 NameError 一并吞掉\n"
          "def load_config(path):\n"
          "    try:\n"
          "        return _read_json(path)\n"
          "    except Exception:\n"
          "        pass",
          "import json\n"
          "\n"
          "\n"
          "def load_config(path):\n"
          "    with open(path, encoding='utf-8') as f:\n"
          "        return json.load(f)",
          'except Exception: pass 会静默吞掉幻觉导致的 NameError/ImportError，使幻觉缺陷不可见；须精确捕获并记录',
          _R_HALLUC),
    make_code_ref(SERIES_HALLUC, 'H04', '注释/签名与实现矛盾', 'P3',
          "def normalize(value):\n"
          "    # 注释声称返回 list, 实际却返回 dict -- 语义自相矛盾\n"
          "    \"\"\"返回归一化后的键列表\"\"\"\n"
          "    return {k: v for k, v in value.items()}",
          "def normalize(value):\n"
          "    \"\"\"返回归一化后的键值映射\"\"\"\n"
          "    return {k: v for k, v in value.items()}",
          '注释、签名、常量与实现语义不一致是上下文矛盾，误导后续维护与 AI 仿写',
          _R_HALLUC, self_verifiable=False),
    make_code_ref(SERIES_HALLUC, 'H05', 'AI Slop（仅 docstring/pass 无实现）', 'P2',
          "def compute_score(items):\n"
          "    \"\"\"计算综合得分。\"\"\"",
          "def compute_score(items):\n"
          "    \"\"\"计算综合得分。\"\"\"\n"
          "    if not items:\n"
          "        return 0.0\n"
          "    return sum(item.score for item in items) / len(items)",
          '仅有 docstring 或仅含 pass 的函数是灌水代码，制造「看似完成」的假象；接口占位必须实现或显式声明',
          _R_HALLUC),
    make_code_ref(SERIES_HALLUC, 'H06', '测试幻觉（无断言伪测试）', 'P1',
          "def add(a, b):\n"
          "    return a + b\n"
          "\n"
          "\n"
          "def test_add():\n"
          "    \"\"\"验证加法正确(无断言的测试永远通过)。\"\"\"",
          "def add(a, b):\n"
          "    return a + b\n"
          "\n"
          "\n"
          "def test_add():\n"
          "    \"\"\"验证加法正确。\"\"\"\n"
          "    assert add(1, 2) == 3\n"
          "    assert add(-1, 1) == 0",
          '无断言的测试函数永远通过，制造虚假覆盖率；每个测试必须有验证被测行为的有意义断言',
          _R_HALLUC),
    make_code_ref(SERIES_HALLUC, 'H07', '记忆/总结幻觉', 'P0',
          "# 错误做法: 凭印象写总结 -- 「本模块共五百行, 四十二个函数, 全部完成」\n"
          "# 声明未与代码实际状态核对, 行数/函数数与 AST 统计偏差超 20%\n"
          "def build():\n"
          "    return []",
          "# 正确做法: 先统计后声明 -- 用 AST/行数统计工具核对再写结论, \n"
          "# 声明中的量化指标(行数/函数数/测试数)与实际状态一致\n"
          "def build():\n"
          "    return []",
          '声称的行数/函数数/完成度与代码实际状态不符（偏差超 20%）即记忆幻觉；量化声明必须先统计后落笔',
          _R_HALLUC, self_verifiable=False),
    make_code_ref(SERIES_HALLUC, 'H08', '沙箱反射（exec 上下文反射）', 'P0',
          "def run_generated(code_text, obj):\n"
          "    # exec 上下文中调用危险反射 = 沙箱逃逸风险\n"
          "    exec(code_text)\n"
          "    return getattr(obj, 'secret')",
          "def run_task(task, obj):\n"
          "    # 不用 exec 执行动态代码; 反射经白名单校验\n"
          "    allowed = {'name', 'value'}\n"
          "    key = task.key\n"
          "    if key not in allowed:\n"
          "        raise KeyError(key)\n"
          "    return getattr(obj, key)",
          'exec/eval 动态代码执行上下文中调用 getattr/setattr/globals 等构成沙箱逃逸风险；反射须经白名单校验',
          _R_HALLUC),
]
_DEPRECATED_REFS: list[CodeRef] = [
    make_code_ref(SERIES_DEPRECATED, 'DP-05', 'datetime.utcnow() 已弃用', 'P2',
          "from datetime import datetime\n"
          "\n"
          "\n"
          "def now_iso():\n"
          "    return datetime.utcnow().isoformat()",
          "from datetime import datetime, timezone\n"
          "\n"
          "\n"
          "def now_iso():\n"
          "    # 时区感知版本, 3.12+ 推荐\n"
          "    return datetime.now(timezone.utc).isoformat()",
          'utcnow() 返回 naive datetime 且 3.12 起弃用；时区感知写法 now(timezone.utc) 才是正确姿势',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-07', 'typing.Union[X, Y] 旧语法', 'P2',
          "from typing import Union\n"
          "\n"
          "\n"
          "def merge(a: Union[int, str], b: Union[int, str]):\n"
          "    return str(a) + str(b)",
          "def merge(a: int | str, b: int | str):\n"
          "    # PEP 604 语法(Python 3.10+), 无需导入 typing.Union\n"
          "    return str(a) + str(b)",
          'PEP 604（Python 3.10+）支持 X | Y 语法，Union 下标写法已过时',
          _R_DEPRECATED_NAMES),
    make_code_ref(SERIES_DEPRECATED, 'DP-08', 'collections 旧别名导入', 'P3',
          "from collections import Mapping\n"
          "\n"
          "\n"
          "def size(data: Mapping):\n"
          "    return len(data)",
          "from collections.abc import Mapping\n"
          "\n"
          "\n"
          "def size(data: Mapping):\n"
          "    return len(data)",
          'Mapping/Sequence 等 ABC 应从 collections.abc 导入，collections 下的别名已弃用并在新版本移除',
          _R_DEPRECATED_NAMES),
    make_code_ref(SERIES_DEPRECATED, 'DP-09', 'threading 驼峰旧命名', 'P3',
          "import threading\n"
          "\n"
          "\n"
          "def current():\n"
          "    return threading.currentThread().name",
          "import threading\n"
          "\n"
          "\n"
          "def current():\n"
          "    return threading.current_thread().name",
          'currentThread/activeCount/notifyAll 等驼峰命名已弃用，3.10+ 统一蛇形命名',
          _R_DEPRECATED_NAMES),
    make_code_ref(SERIES_DEPRECATED, 'DP-10', 'inspect.getargspec() 已移除', 'P2',
          "import inspect\n"
          "\n"
          "\n"
          "def params(fn):\n"
          "    return inspect.getargspec(fn)",
          "import inspect\n"
          "\n"
          "\n"
          "def params(fn):\n"
          "    # getargspec 已在 3.11 移除\n"
          "    return inspect.getfullargspec(fn)",
          'inspect.getargspec() 在 Python 3.11 已移除，调用即 AttributeError；改用 getfullargspec/signature',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-12', 'contextlib.nested() 已移除', 'P2',
          "from contextlib import nested\n"
          "\n"
          "\n"
          "def read_two(a, b):\n"
          "    with nested(open(a), open(b)) as (fa, fb):\n"
          "        return fa.read(), fb.read()",
          "def read_two(a, b):\n"
          "    # 多资源用嵌套 with 或 ExitStack, 且 open 须被 with 直接管理\n"
          "    with open(a, encoding='utf-8') as fa, open(b, encoding='utf-8') as fb:\n"
          "        return fa.read(), fb.read()",
          'contextlib.nested() 已移除且本就有异常安全问题；改用 ExitStack 或嵌套 with',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-32', 'logging.warn() 弃用别名', 'P3',
          "import logging\n"
          "\n"
          "log = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def check(value):\n"
          "    log.warn('value invalid: %s', value)",
          "import logging\n"
          "\n"
          "log = logging.getLogger(__name__)\n"
          "\n"
          "\n"
          "def check(value):\n"
          "    # warn 是 warning 的弃用别名\n"
          "    log.warning('value invalid: %s', value)",
          "warn() 是 warning() 的弃用别名，新版本将移除；日志统一用 warning()",
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-45', '@asyncio.coroutine 已移除', 'P2',
          "import asyncio\n"
          "\n"
          "\n"
          "@asyncio.coroutine\n"
          "def fetch(url):\n"
          "    return url",
          "async def fetch(url):\n"
          "    return url",
          '@asyncio.coroutine 旧式生成器协程装饰器 3.8 起弃用、3.11 已移除（使用即 AttributeError）；一律用 async def + await',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-47', 'asyncio loop 参数已弃用', 'P3',
          "import asyncio\n"
          "\n"
          "\n"
          "async def work(delay, loop):\n"
          "    # loop 参数 3.8 起弃用、3.10 已移除, 传入即 TypeError\n"
          "    await asyncio.sleep(delay, loop=loop)",
          "import asyncio\n"
          "\n"
          "\n"
          "async def work(delay):\n"
          "    # 协程内直接使用运行中事件循环; 外部入口用 asyncio.run()\n"
          "    await asyncio.sleep(delay)",
          'asyncio.sleep/wait/gather 等 API 的 loop 参数在 3.8 弃用、3.10 已移除，传入即 TypeError；协程内直接使用运行中事件循环，外部入口用 asyncio.run()',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-49', 'StringIO 旧导入路径', 'P3',
          "from StringIO import StringIO\n"
          "\n"
          "\n"
          "def build(text):\n"
          "    return StringIO(text)",
          "from io import StringIO\n"
          "\n"
          "\n"
          "def build(text):\n"
          "    return StringIO(text)",
          'StringIO/cStringIO 是 Python 2 路径，统一从 io 导入（字节流用 BytesIO）',
          _R_DEPRECATED_NAMES),
    make_code_ref(SERIES_DEPRECATED, 'DP-11', '__getattr__ 内含危险动态执行', 'P3',
          'import builtins\n'
          '\n'
          'class LazyLoader:\n'
          '    def __getattr__(self, name):\n'
          '        # 反例：__getattr__ 中执行动态代码，属性访问即可触发注入\n'
          '        return builtins.eval(f"self._load_{name}()")\n',
          'class LazyLoader:\n'
          '    def __init__(self, backend):\n'
          '        # _backend 经 __init__ 直写入实例 __dict__，后续属性\n'
          '        # 读取在 __dict__ 命中，不再落入 __getattr__ 自递归\n'
          '        self._backend = backend\n'
          '\n'
          '    def __getattr__(self, name):\n'
          '        # 正例：属性访问只做查找/惰性加载，不执行动态代码；\n'
          '        # backend 用 object.__getattribute__ 直取（不二次落入\n'
          '        # __getattr__），杜绝代理属性的自递归风险（MP-03 同款建议）\n'
          '        if name.startswith("_load_"):\n'
          '            raise AttributeError(name)\n'
          '        backend = object.__getattribute__(self, "_backend")\n'
          '        return getattr(backend, name)\n',
          '__getattr__ 在属性正常查找失败时触发（每次访问未定义属性都会落入这里），若其中调用 eval/exec/compile/'
          '__import__，攻击者构造的属性名即可转化为任意代码执行；'
          '动态导入应改用 importlib.import_module。',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-33', 'warn_explicit 位置参数超过 6 个', 'P3',
          'import warnings\n'
          '\n'
          'def legacy_warn(message, category, filename, lineno, module,\n'
          '                registry, module_globals=None):\n'
          '    # 反例：可选参数按位置传满 7 个，各位置含义只能靠记忆\n'
          '    warnings.warn_explicit(\n'
          '        message, category, filename, lineno, module, registry,\n'
          '        module_globals,\n'
          '    )\n',
          'import warnings\n'
          '\n'
          'def modern_warn(message, category, filename, lineno, module,\n'
          '                registry):\n'
          '    # 正例：必填 4 个位置参数，可选参数一律关键字传入\n'
          '    warnings.warn_explicit(\n'
          '        message, category, filename, lineno,\n'
          '        module=module, registry=registry,\n'
          '    )\n',
          'warnings.warn_explicit() 的可选参数（module/registry/'
          'module_globals/source）应使用关键字形式传入；按位置传满 7 个参数'
          '虽然仍可运行，但调用点无法分辨各位置含义，版本新增参数时极易'
          '把新值填进旧位置（3.12 新增 source 参数即为近期实例）。',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED, 'DP-39', 'csv.Sniffer.sniff 位置参数超限', 'P3',
          'import csv\n'
          '\n'
          'def detect_dialect(sample):\n'
          '    sniffer = csv.Sniffer()\n'
          '    # 反例：sniff 只接受 sample/delimiters 两个位置参数，\n'
          '    # 第三个位置参数直接 TypeError\n'
          '    return sniffer.sniff(sample, ",;", "\\r\\n")\n',
          'import csv\n'
          '\n'
          'def detect_dialect(sample):\n'
          '    sniffer = csv.Sniffer()\n'
          '    # 正例：定界符用关键字传入，参数语义与签名一一对应\n'
          '    return sniffer.sniff(sample, delimiters=",;")\n',
          'csv.Sniffer.sniff() 的签名是 sniff(sample, delimiters=None)，'
          '只接受两个位置参数；多传第三个位置参数不是弃用而是直接 '
          'TypeError（takes from 2 to 3 positional arguments）。'
          '定界符用关键字传入，避免把参数个数当成可扩展面。',
          _R_DEPRECATED),
    make_code_ref(
        SERIES_DEPRECATED, "DP-04", "Python 3.9 弃用 typing 别名", "P3",
        'from typing import List\n'
        '\n'
        'def get_names(rows) -> List[str]:\n'
        '    """取名字列表。"""\n'
        '    return [r["name"] for r in rows]\n',
        'def get_names(rows) -> list[str]:\n'
        '    """取名字列表。"""\n'
        '    return [r["name"] for r in rows]\n',
        "typing.List/Dict/Set/FrozenSet/Tuple 等别名自 Python 3.9 起弃用（PEP 585）；它们仍可使用且目前未计划移除，新代码优先使用内建泛型 list[str]/dict[str, int]，不要按虚构期限做破坏性迁移。",
        _R_DEPRECATED_NAMES,
    ),
]
_ROBUST_REFS: list[CodeRef] = [
    make_code_ref(SERIES_ROBUST, 'BZ-01', '== True/False 布尔陷阱', 'P2',
          "def is_ready(flag):\n"
          "    if flag == True:\n"
          "        return 'ready'\n"
          "    return 'pending'",
          "def is_ready(flag):\n"
          "    if flag:\n"
          "        return 'ready'\n"
          "    return 'pending'",
          '== 可被 __eq__ 重载，且 truthy 非 bool 值与 True 的 == 结果有歧义；直接用 if x / if not x',
          _R_ROBUST),
    make_code_ref(SERIES_ROBUST, 'DG-02', 'dict.update 同键隐式覆盖', 'P2',
          "def apply(cfg):\n"
          "    base = {'name': 'app', 'level': 2}\n"
          "    base.update({'name': 'core'})\n"
          "    # 'name' 键被隐式覆盖, 前一值静默丢失\n"
          "    base.update({'name': 'worker'})\n"
          "    return base",
          "def apply(cfg):\n"
          "    base = {'name': 'app', 'level': 2}\n"
          "    # 覆盖是有意的状态流转: 显式赋值并只改目标键, 其余键原值保留\n"
          "    base['name'] = 'worker'\n"
          "    return base",
          'update 覆盖已有键时前一值静默丢失；状态流转用显式赋值并注释意图',
          _R_ROBUST_PKGFS),
    make_code_ref(SERIES_ROBUST, 'IC-01', '相邻字符串隐式拼接', 'P2',
          "def build():\n"
          "    return ['alpha' 'beta', 'gamma']",
          "def build():\n"
          "    # 相邻字符串隐式拼接是丢逗号 BUG 的温床, 显式写全\n"
          "    return ['alpha', 'beta', 'gamma']",
          "同一逻辑行内相邻字符串字面量自动拼接，'a' 'b' 掩盖丢逗号类 BUG，列表/元组中危害最大",
          _R_ROBUST),
    make_code_ref(SERIES_ROBUST, 'NS-01', '可空返回值链式访问', 'P2',
          "def get_city(profile):\n"
          "    return profile.get('address').get('city')",
          "def get_city(profile):\n"
          "    address = profile.get('address')\n"
          "    if address is None:\n"
          "        return ''\n"
          "    return address.get('city', '')",
          '.get()/re.search() 等无结果时返回 None，直接链式 .attr/[key] 即 AttributeError/TypeError；'
          'str.find() 则返回 -1（不是 None），须显式判断 -1',
          _R_ROBUST_PKGFS),
    make_code_ref(SERIES_ROBUST, 'EP-02', '__init__.py 业务逻辑过多', 'P2',
          "VALUE = 1\n"
          "_state = 2\n"
          "count = 3\n"
          "name = 'x'\n"
          "flag = True\n"
          "items = []\n"
          "ready = False\n"
          "total = 0\n"
          "label = 'y'\n"
          "mode = 'z'\n"
          "extra = 11\n"
          "more = 12",
          "\"\"\"包初始化: 仅保留导入与再导出, 业务逻辑移至子模块。\"\"\"\n"
          "from .core import VALUE, run\n"
          "\n"
          "__all__ = ['VALUE', 'run']",
          '__init__.py 顶层语句过多（>10）拖慢导入且易产生导入副作用；仅保留导入/再导出/dunder 声明',
          _R_ROBUST_PKGFS),
    make_code_ref(SERIES_ROBUST, 'TY-02', 'Optional[X] | None 双重可选', 'P2',
          "from typing import Optional\n"
          "\n"
          "\n"
          "def find(key: Optional[str] | None):\n"
          "    return key",
          "def find(key: str | None):\n"
          "    # Optional[X] 本身已含 None, 二者取一\n"
          "    return key",
          'Optional[X] 本身已含 None，再叠加 | None 是冗余注解，误导读者以为有第三种状态',
          _R_ROBUST),
    make_code_ref(SERIES_ROBUST, 'DF-03', 'set 与非集合字面量运算', 'P2',
          "def can_read():\n"
          "    # 想判断 'read' 是否在集合中, 误用 & 与字符串字面量运算\n"
          "    # set 字面量与非集合字面量直接位运算, 运行时 TypeError\n"
          "    return {'read', 'write'} & 'read'",
          "def can_read():\n"
          "    # 成员判定改用 in; 集合运算则操作数统一为 set 字面量\n"
          "    return 'read' in {'read', 'write'}",
          'set 字面量与 list/str 字面量直接 &/|/^/- 运行时 TypeError；操作数须统一为 set(...)；成员判定用 in',
          _R_ROBUST),
]
_ARCH_EXTRA_REFS: list[CodeRef] = [
    make_code_ref(SERIES_ARCH_EXTRA, 'D06', '动态导入固定模块', 'WARN',
          "import importlib\n"
          "\n"
          "\n"
          "def load_json():\n"
          "    # 固定模块用动态导入, 绕过静态可分析性\n"
          "    return importlib.import_module('json')",
          "import json\n"
          "\n"
          "\n"
          "def load_json():\n"
          "    return json",
          'importlib.import_module()/__import__() 加载固定模块绕过静态分析与 IDE 补全；仅插件/延迟加载等场景合法',
          DETECTOR_REF_GATE3_ARCH),
    make_code_ref(SERIES_ARCH_EXTRA, 'D07', '空函数体无文档', 'WARN',
          "def validate(token):\n"
          "    pass",
          "def validate(token):\n"
          "    \"\"\"接口占位: 校验令牌合法性, 子类/后续实现。\"\"\"\n"
          "    raise NotImplementedError('validate pending')",
          '仅含 pass 的函数若无 docstring 即疑似未完成实现；接口占位必须文档声明或显式 NotImplementedError',
          DETECTOR_REF_GATE3_ARCH),
    make_code_ref(SERIES_ARCH_EXTRA, 'D18', '桩函数硬编码返回', 'WARN',
          "def compute_total(items):\n"
          "    return 0",
          "def compute_total(items):\n"
          "    return sum(item.total for item in items)",
          '仅返回硬编码值（0/None/空容器）的桩函数制造「看似实现」的假象；要么实现要么显式占位声明',
          DETECTOR_REF_GATE3_ARCH),
    make_code_ref(SERIES_ARCH_EXTRA, 'D21', '__version__ 重复定义', 'WARN',
          "__version__ = '1.0.0'\n"
          "\n"
          "\n"
          "def get_version():\n"
          "    return __version__\n"
          "\n"
          "\n"
          "__version__ = '1.0.1'",
          "__version__ = '1.0.1'\n"
          "\n"
          "\n"
          "def get_version():\n"
          "    return __version__",
          '同一文件多处 __version__/元数据定义易失同步，保留一处 SSOT',
          DETECTOR_REF_GATE3_ARCH),
    make_code_ref(SERIES_ARCH_EXTRA, 'D25', '代码中全角标点', 'WARN',
          "def report(name):\n"
          "    # 全角 ｌ 在词法分析时经 NFKC 归一化为半角 l, 与 label\n"
          "    # 是同一个变量; 源码视觉不同、grep 搜不到, 极难排查\n"
          "    ｌabel = 'name'\n"
          "    return ｌabel",
          "def report(name):\n"
          "    # 标识符一律半角; 字符串内的中文全角标点是合法输出内容\n"
          "    label = '名称: ' + name\n"
          "    return label",
          '代码位置的全角字符（如全角标识符经 NFKC 归一化后语法合法但视觉难辨）导致难以排查的语法/比较错误；字符串/注释内的全角中文标点是合法内容不报，标识符一律使用半角',
          DETECTOR_REF_GATE3_ARCH),
]
DIAG_CORE_GROUPS: tuple[tuple[str, list[CodeRef]], ...] = (
    (SERIES_TRAP, _TRAP_REFS),
    (SERIES_IO, _IO_REFS),
    (SERIES_HALLUC, _HALLUC_REFS),
    (SERIES_DEPRECATED, _DEPRECATED_REFS),
    (SERIES_ROBUST, _ROBUST_REFS),
    (SERIES_ARCH_EXTRA, _ARCH_EXTRA_REFS),
)
DIAG_CORE_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    [ref for _series, refs in DIAG_CORE_GROUPS for ref in refs],
    "DIAG_CORE_CODE_REFS",
)
register_code_refs(DIAG_CORE_CODE_REFS, "prevention_diag_refs")
_GOV_REF_DEFAULTS = {
    "series": "governance",
    "severity": "ERROR",
}
GOV_CODE_REFS: dict[str, CodeRef] = build_keyed_registry([
    CodeRef(
        rule_id='GOV-01', name='禁止以拆分为治理手段',
        bad_example=(
            "def handle_order(order):\n"
            "    # 文件超过 1200 行，直接拆成 order_core.py 与 order_utils.py\n"
            "    return _apply(order)"
        ),
        good_example=(
            "def handle_order(order):\n"
            "    # 不新增模块边界：同模块内提取私有实现并消除重复\n"
            "    return _apply_rules(order)\n"
            "\n"
            "\n"
            "def _apply_rules(order):\n"
            "    return order.total"
        ),
        rationale='拆分只转移复杂度，不降低复杂度；治理须落在简化逻辑/消除重复/'
                  '收敛依赖/迁移代码/提取同模块私有实现',
        detector_ref=(anchor_module('ai_review_governance_review') + ' (治理手段合规性维度) + ' + anchor_module('build_refactor_policy') + ' (R-15 no_split_as_governance)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-02', name='合并须附四要素论证',
        bad_example=(
            "MERGE_DECISION = {\n"
            "    'action': 'merge',\n"
            "    'reason': '两个文件长得很像',\n"
            "}"
        ),
        good_example=(
            "MERGE_DECISION = {\n"
            "    'action': 'merge',\n"
            "    'pros': ['消除同一规则的两份实现'],\n"
            "    'cons': ['单文件评审面积增大'],\n"
            "    'net_benefit': 'positive',\n"
            "    'risk': '需补跨模块回归用例',\n"
            "}"
        ),
        rationale='合并必须证明净收益为正并记录风险，否则只是把两处耦合叠成一处',
        detector_ref=(anchor_module('ai_review_governance_review') + ' (合并论证校验) + ' + anchor_module('build_refactor_gate') + ' (merge_decisions 指标)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-03', name='禁止跨模块内部符号导入',
        bad_example=(
            "from shop.orders.internal import _recalculate_total\n"
            "\n"
            "\n"
            "def total(order):\n"
            "    return _recalculate_total(order)"
        ),
        good_example=(
            "# 目标包入口 __all__ 已登记 recalculate_total\n"
            "from shop.orders import recalculate_total\n"
            "\n"
            "\n"
            "def total(order):\n"
            "    return recalculate_total(order)"
        ),
        rationale='跨模块只允许包对外导出的公共 API；内部符号随实现变更即破坏调用方',
        detector_ref=(anchor_module('diag_module_topology') + ' (GOV-B02 internal_symbol_import)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-04', name='禁止深层路径导入',
        bad_example=(
            "from shop.orders.pricing.rules import apply_discount\n"
            "\n"
            "\n"
            "def checkout(order):\n"
            "    return apply_discount(order)"
        ),
        good_example=(
            "# 统一出入口：包 __init__.py 白名单导出 apply_discount\n"
            "from shop.orders import apply_discount\n"
            "\n"
            "\n"
            "def checkout(order):\n"
            "    return apply_discount(order)"
        ),
        rationale='深层路径导入把内部目录结构固化成外部契约，公共 API 无法收敛与演进',
        detector_ref=(anchor_module('diag_module_topology') + ' (GOV-B01/B03/B04)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-05', name='迁移须降耦而非原样搬移',
        bad_example=(
            "from legacy.state import CURRENT_CART\n"
            "\n"
            "\n"
            "def total():\n"
            "    # 整段复制到新模块，仍直读旧模块全局状态\n"
            "    return sum(item.price for item in CURRENT_CART)"
        ),
        good_example=(
            "def total(cart):\n"
            "    # 迁移时断开对旧模块全局状态的依赖，改为显式入参\n"
            "    return sum(item.price for item in cart)"
        ),
        rationale='原样搬移只是换文件位置，耦合随代码一起迁移；迁移必须同时切断旧依赖',
        detector_ref=(anchor_module('ai_review_governance_review') + ' (迁移降耦判定)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-06', name='公共 API 变更须显式声明',
        bad_example=(
            "# 未声明新增 refund_order，API surface 静默膨胀\n"
            "__all__ = ['create_order', 'cancel_order', 'refund_order']"
        ),
        good_example=(
            "# 公共 API 变更声明：新增 refund_order，过门禁时显式登记\n"
            "__all__ = ['create_order', 'cancel_order', 'refund_order']\n"
            "\n"
            "result = check_acceptance(\n"
            "    skill_dir, baseline, declared_api_additions=['refund_order'])\n"
            "assert result['passed'], result['failed_metrics']"
        ),
        rationale='导出符号是外部契约，新增/删除必须显式声明并评估 API surface 影响',
        detector_ref=(anchor_module('build_refactor_gate') + ' (public_api 指标)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-07', name='治理收尾须过六项基线验收',
        bad_example=(
            "# 合并完成即结项，未对比基线、未跑测试\n"
            "merge_modules('a.py', 'b.py')"
        ),
        good_example=(
            "result = check_acceptance(\n"
            "    skill_dir, baseline, test_status='passed', rollback_id='rb-1')\n"
            "assert result['passed'], result['failed_metrics']"
        ),
        rationale='治理是否收敛只能由基线差集裁决：环/非法导入/API/复杂度/测试/合并留痕',
        detector_ref=(anchor_module('build_refactor_gate') + ' (check_acceptance 六项指标)'),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-08', name='回归未获验证结论不得视为通过',
        bad_example=(
            "def gate(result):\n"
            "    if result.get('status') != 'failed':\n"
            "        return 'applied'   # status=error（回归没跑起来）也走这里\n"
        ),
        good_example=(
            "VERIFIED = frozenset({'passed'})\n"
            "\n"
            "\n"
            "def gate(result):\n"
            "    if result.get('status') in VERIFIED:\n"
            "        return 'applied'\n"
            "    return 'failed'   # 按字节回滚原文件\n"
        ),
        rationale='定向回归 status 域含 skipped/error：skipped 已覆盖“无套件可跑”，'
                  'error 专指“执行异常/未获结论”，与 failed 同属未验证；只排除 failed '
                  '会让写盘门禁在回归崩溃时静默放行，缺陷随修复一起落盘',
        detector_ref=(anchor_module('ai_review_governance') + ' (写盘门禁判据) + ' + anchor_module('fix_safety_gate._post_write_regression')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-09', name='删除通道回归异常同样按未验证收口',
        bad_example=(
            "def apply(plan, regression):\n"
            "    if regression['status'] == 'failed':\n"
            "        return 'rejected'\n"
            "    return delete_target(plan)   # error/skipped 直接删\n"
        ),
        good_example=(
            "VERIFIED = frozenset({'passed'})\n"
            "\n"
            "\n"
            "def apply(plan, regression):\n"
            "    if regression.get('status') not in VERIFIED:\n"
            "        restore(plan)\n"
            "        return 'rejected'\n"
            "    return delete_target(plan)\n"
        ),
        rationale='删除通道与写盘通道共用同一回归语义；passed 是唯一已验证状态，'
                  'failed/error/skipped/缺失或未知状态都必须恢复原文件，否则会在'
                  '“回归未获通过结论”时产出不可逆删除，且事后无从取证',
        detector_ref=(anchor_module('ai_review_governance') + ' (删除通道判据) + ' + anchor_module('fix_safety_gate.apply_verified_write')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-10', name='未知键不得落兜底桶并报生效',
        bad_example=(
            "def approve(item):\n"
            "    bucket = BUCKETS.get(item['kind'], 'misc')   # 无人读取的兜底桶\n"
            "    write(bucket, item)\n"
            "    log.info('调整建议已采纳生效')\n"
        ),
        good_example=(
            "def approve(item):\n"
            "    if item['kind'] not in BUCKETS:\n"
            "        return reject('kind 不在生效域内：兜底桶无消费端')\n"
            "    write(BUCKETS[item['kind']], item)\n"
            "    log.info('调整建议已采纳生效')\n"
        ),
        rationale='兜底桶没有任何计算消费端，写入即等于丢失；同时日志宣告“已生效”，'
                  '把静默丢弃伪装成成功销项，脏数据永远不再被看见',
        detector_ref=(anchor_module('ai_review_governance') + ' (销项真实性判据) + ' + anchor_module('ai_review_governance._invalid_adjustment_reason')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-11', name='空操作不得报为已应用',
        bad_example=(
            "def apply(entry):\n"
            "    mark(entry)          # 日志里根本没有该条目 → 什么都没标记\n"
            "    return 'applied'     # 上游据此销项，问题被永久掩埋\n"
        ),
        good_example=(
            "def apply(entry):\n"
            "    res = mark(entry)\n"
            "    if not res.get('file_marked'):\n"
            "        return 'already_absent'   # 不写记忆操作、不联动销项\n"
            "    return 'applied'\n"
        ),
        rationale='“没找到待应用条目”与“已应用”是两种事实；混同会让消费端把'
                  '未处理的问题当作已处理，且不再进入重试队列',
        detector_ref=(anchor_module('ai_review_governance') + ' (生效证据判据) + ' + anchor_module('ai_review_item_plan._enhancement_effective_status')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-12', name='相对路径必须锚定技能根',
        bad_example=(
            "import os\n"
            "\n"
            "\n"
            "def resolve(plan):\n"
            "    return plan['file']          # 按进程 cwd 解析 → 删错目标\n"
            "\n"
            "\n"
            "def remove(plan):\n"
            "    os.remove(resolve(plan))\n"
        ),
        good_example=(
            "import os\n"
            "\n"
            "\n"
            "def resolve_target(skill_dir, plan):\n"
            "    # 唯一锚点: 技能根 realpath + 计划字段; 符号链接越界同样拒绝\n"
            "    root = os.path.realpath(skill_dir)\n"
            "    path = os.path.realpath(os.path.join(root, plan['file']))\n"
            "    return path if path.startswith(root + os.sep) else None\n"
            "\n"
            "\n"
            "def remove(skill_dir, plan):\n"
            "    path = resolve_target(skill_dir, plan)   # 两条通道共用同一函数\n"
            "    if path is None:\n"
            "        return False\n"
            "    os.remove(path)\n"
            "    return True\n"
        ),
        rationale='同一计划字段在两条通道被两种方式解析（cwd vs 技能根）'
                  '必然分叉；锚点须收敛到单一 SSOT 函数，并用 realpath 同时'
                  '阻断 .. 与符号链接逃逸，下游重新校验存在性',
        detector_ref=(anchor_module('ai_review_governance') + ' (路径锚点判据) + ' + anchor_module('cleanup_residue._plan_target_path')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-13', name='豁免判定须作用在注释段',
        bad_example=(
            "def exempt(line_text):\n"
            "    return 'nosec' in line_text.lower()   # 字符串里的 nosec 也算豁免\n"
        ),
        good_example=(
            "from jwsgj.diag_shared_source_core import scan_line_quote_state\n"
            "\n"
            "\n"
            "def exempt(line_text):\n"
            "    # 先定位字符串外的第一个 '#'; -1 表示整行无注释段\n"
            "    cut, _state = scan_line_quote_state(line_text)\n"
            "    if cut < 0:\n"
            "        return False\n"
            "    return 'nosec' in line_text[cut:].lower()\n"
        ),
        rationale='整行子串会把字符串/文档串里的关键字当成显式豁免，'
                  '安全规则被数据静默关闭；判定必先定位注释段，再判关键字',
        detector_ref=(anchor_module('ai_review_governance') + ' (豁免判据) + ' + anchor_module('diag_solidify_rules') + ' (CS-99 regex 规则) + ' + anchor_module('diag_shared_source_core.scan_line_quote_state')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-14', name='顶层符号类型变更须升级风险等级',
        bad_example=(
            "def changed(orig, fixed):\n"
            "    return set(orig) ^ set(fixed)   # 只比名字：class A → def A 视为未变更\n"
        ),
        good_example=(
            "def changed(orig, fixed):\n"
            "    old = {name: kind for name, (kind, _sig) in orig.items()}\n"
            "    new = {name: kind for name, (kind, _sig) in fixed.items()}\n"
            "    return {n for n in set(old) | set(new) if old.get(n) != new.get(n)}\n"
        ),
        rationale='同名符号从 class 变 def（或反向）是调用契约级破坏，'
                  '只比名字集合会稳定降级为 CAUTION，足以被自动流程放行',
        detector_ref=(anchor_module('ai_review_governance') + ' (风险分级判据) + ' + anchor_module('fix_safety_boundary._top_level_symbols_changed')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-15', name='动态 __all__ 须保留历史并集',
        bad_example=(
            "__all__ = ['a']\n"
            "__all__ = ['b']\n"
            "__all__ = build_all()   # 只取最后一次字面量 → a/b 全判丢失\n"
        ),
        good_example=(
            "import ast\n"
            "from jwsgj.diag_shared_ast_surface import collect_module_exports_ordered\n"
            "\n"
            "source = (\n"
            "    \"__all__ = ['a']\\n\"\n"
            "    \"__all__ += ['b']\\n\"\n"
            "    \"__all__ += list(build_all())\\n\"\n"
            ")\n"
            "names, exact = collect_module_exports_ordered(ast.parse(source))\n"
            "assert names == ['a', 'b'] and not exact\n"
            "# 动态部分未知，但增量写法保留了可证明的历史导出并集\n"
        ),
        rationale='动态覆盖赋值会丢失此前已经声明的导出；应增量合并历史列表。'
                  '分析端在 exact=False 时只能采用收集器返回的已知并集，'
                  '不得把未知动态部分当成空集或把历史项判成丢失',
        detector_ref=(anchor_module('ai_review_governance') + ' (导出契约判据) + ' + anchor_module('diag_shared_ast_surface.collect_module_exports_state')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-16', name='同语义定位须单一 SSOT',
        bad_example=(
            "def run_regression(skill_dir, fp):\n"
            "    return locate_targeted_tests(skill_dir, fp)    # bridge 优先\n"
            "\n"
            "\n"
            "def verify_l4(skill_dir, fp):\n"
            "    return filename_matched_tests(skill_dir, fp)   # 只按文件名\n"
        ),
        good_example=(
            "def verify_l4(skill_dir, fp):\n"
            "    tests, mode = locate_targeted_tests(skill_dir, fp)\n"
            "    return tests, mode\n"
        ),
        rationale='“该跑哪些测试”写两份实现时，覆盖映射/bridge 只在其中一条生效，'
                  '另一条稳定漏跑且不报错，验证层与实际回归口径分叉',
        detector_ref=(anchor_module('ai_review_governance') + ' (验证覆盖判据) + ' + anchor_module('fix_safety_verify._verify_l4_test_layer')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-17', name='增量命中须指向新增行',
        bad_example=(
            "def new_hit_lines(base_lines, cur_lines):\n"
            "    return min(cur_lines)   # 基线已有第 1 行 → 报的仍是旧命中\n"
        ),
        good_example=(
            "def new_hit_lines(base_lines, cur_lines):\n"
            "    fresh = sorted(set(cur_lines) - set(base_lines))\n"
            "    return fresh[0] if fresh else None\n"
        ),
        rationale='增量报告的行号用于人工定位新增风险；复用基线旧行号'
                  '会把评审引到“本来就没改”的代码，等价于证据失真',
        detector_ref=(anchor_module('ai_review_governance') + ' (证据定位判据) + ' + anchor_module('fix_safety_verify._new_redline_hits')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-18', name='新增计数须用多重集差',
        bad_example=(
            "def new_secrets(orig, fixed):\n"
            "    return set(fixed) - set(orig)   # 同值复制到第二处 → 空集漏检\n"
        ),
        good_example=(
            "from collections import Counter\n"
            "\n"
            "\n"
            "def new_secrets(orig, fixed):\n"
            "    added = Counter(fixed) - Counter(orig)\n"
            "    return [v for v, n in added.items() for _ in range(n)]\n"
        ),
        rationale='“新增几处”是重数语义；集合差只回答“出现过哪些值”，'
                  '同值复制与同模式多处新增都会被吞掉，且计数文案恒报 1',
        detector_ref=(anchor_module('ai_review_governance') + ' (计数口径判据) + ' + anchor_module('fix_safety_gate.detect_new_hardcoded_secrets')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-19', name='非契约返回须 fail-closed',
        bad_example=(
            "def normalize(result):\n"
            "    if not isinstance(result, tuple):\n"
            "        return bool(result), {}   # dict/非空串 → True\n"
        ),
        good_example=(
            "def normalize(result):\n"
            "    if isinstance(result, bool):\n"
            "        return result, {}\n"
            "    if (not isinstance(result, tuple) or len(result) != 2\n"
            "            or not isinstance(result[0], bool)):\n"
            "        return False, {'error': '返回形态异常，按验证失败收口'}\n"
            "    passed, details = result\n"
            "    if isinstance(details, dict):\n"
            "        return passed, details\n"
            "    if details is None:\n"
            "        return passed, {}\n"
            "    return passed, {'error': str(details)}\n"
        ),
        rationale='门禁归一层的宽松 bool() 会把“没给出结论”的对象抬成通过；'
                  '与同模块其它归一器口径相反即静默漏洞，脏返回等价于验证通过',
        detector_ref=(anchor_module('ai_review_governance') + ' (门禁归一判据) + ' + anchor_module('diag_guard_io._normalize_verify_fn_result')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-20', name='清理队列脏数据须确定性收口',
        bad_example=(
            "def locate(plan):\n"
            "    if not plan.get('file'):\n"
            "        return None   # 脏计划留在队列里，永远 pending\n"
        ),
        good_example=(
            "import os\n"
            "\n"
            "\n"
            "def locate(skill_dir, plan):\n"
            "    path = resolve_target(skill_dir, plan)   # GOV-12 的唯一锚点\n"
            "    if path is None:\n"
            "        return consume(plan, status='invalid')   # 脏数据确定性收口\n"
            "    if not os.path.isfile(path):\n"
            "        return consume(plan, status='already_absent')\n"
            "    return path\n"
            "\n"
            "\n"
            "def consume(plan, *, status):\n"
            "    plan['status'] = status   # 终态写回: 队列按 status 出队, 不再 pending\n"
            "    return None\n"
        ),
        rationale='队列只应容纳“可执行且未完成”的项；脏数据与已失效目标'
                  '不显式收口就会永久阻塞审核队列，零遗留门禁永不通过',
        detector_ref=(anchor_module('ai_review_governance') + ' (队列收口判据) + ' + anchor_module('cleanup_residue._locate_cleanup_target')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-21', name='行数统计须统一尾换行口径',
        bad_example=(
            "def count_lines(source):\n"
            "    return len(source.split('\\n'))   # 尾换行文件多算 1 行\n"
        ),
        good_example=(
            "from jwsgj.diag_shared_source_core import count_lines\n"
            "\n"
            "line_count = count_lines(source)\n"
            "# 尾换行口径只由 SSOT 维护，调用方不重新实现\n"
        ),
        rationale='split 在尾换行文件上多出空元素，硬限/告警线整体错位一格；'
                  '行数一律走 SSOT count_lines()，不得各写一份口径',
        detector_ref=(anchor_module('ai_review_governance') + ' (行数口径判据) + ' + anchor_module('diag_solidify_rules') + ' (CS-100 regex 规则) + ' + anchor_module('diag_shared_source_core.count_lines')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-22', name='命名空间×属性表须整族派生',
        bad_example=(
            "BUILTIN_NAMESPACES = frozenset({'builtins', '__builtins__'})\n"
            "EXEC_ATTRS = frozenset({'eval', 'exec'})\n"
            "CALL_RULE_TABLE = {\n"
            "    'builtins.eval': 'WRITE-BLOCK-01',\n"
            "    'builtins.exec': 'WRITE-BLOCK-02',\n"
            "}\n"
        ),
        good_example=(
            "BUILTIN_NAMESPACES = frozenset({'builtins', '__builtins__'})\n"
            "EXEC_ATTRS = frozenset({'eval', 'exec'})\n"
            "EXEC_RULE_IDS = {'eval': 'WRITE-BLOCK-01', 'exec': 'WRITE-BLOCK-02'}\n"
            "CALL_RULE_TABLE = {\n"
            "    f'{namespace}.{attr}': EXEC_RULE_IDS[attr]\n"
            "    for namespace in BUILTIN_NAMESPACES\n"
            "    for attr in EXEC_ATTRS\n"
            "}\n"
        ),
        rationale='命名空间集合与属性名集合两份事实表都已存在时，点号键表只手抄'
                  '了其中一个命名空间，新增命名空间（如 __builtins__）会整族漏判'
                  '，写盘红线与规则路由静默失效',
        detector_ref=(anchor_module('diag_solidify_rules') + ' (CS-101 ast 规则) + ' + anchor_module('diag_guard_injection_scan._CALL_RULE_TABLE')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-23', name='17 位紧凑时间戳须走 SSOT',
        bad_example=(
            "import time\n"
            "\n"
            "def report_timestamp(now):\n"
            "    return (time.strftime('%Y%m%d%H%M%S', time.localtime(now))\n"
            "            + f'{int(now * 1000) % 1000:03d}')\n"
        ),
        good_example=(
            "import time\n"
            "from jwsgj.diag_types_normalize import format_compact_ts\n"
            "\n"
            "def report_timestamp(now):\n"
            "    return format_compact_ts(int(now * 1000))\n"
        ),
        rationale='17 位紧凑时间戳已在 diag_types_normalize 定型，本地重拼 '
                  'strftime + 毫秒补零会与 SSOT 各自演进（时区/取整/长度口径分叉）',
        detector_ref=(anchor_module('diag_solidify_rules') + ' (CS-102 ast 规则) + ' + anchor_module('diag_types_normalize.format_compact_ts')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-24', name='文件缺失不得写入异常留痕',
        bad_example=(
            "def read_cached(path):\n"
            "    try:\n"
            "        return path.read_text(encoding='utf-8')\n"
            "    except FileNotFoundError as exc:\n"
            "        log_swallowed(__name__, exc, context='cache')\n"
            "        return None\n"
        ),
        good_example=(
            "def read_cached(path):\n"
            "    if not path.is_file():\n"
            "        return None\n"
            "    try:\n"
            "        return path.read_text(encoding='utf-8')\n"
            "    except FileNotFoundError:\n"
            "        return None\n"
        ),
        rationale='首次写入前文件本就不存在，将 FileNotFoundError 写入 '
                  'swallowed_exception 会向 WARNING+traceback 通道注入伪异常，'
                  '污染日志驱动的退化检测',
        detector_ref=(anchor_module('diag_solidify_rules') + ' (CS-103 ast 规则) + ' + anchor_module('log_config.log_swallowed')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-25', name='派生规则 ID 元组不得手抄',
        bad_example=(
            "DELETE_RULE_IDS = {\n"
            "    'os.remove': 'WRITE-WARN-01',\n"
            "    'os.rmdir': 'WRITE-WARN-02',\n"
            "    'os.unlink': 'WRITE-WARN-01',\n"
            "    'shutil.rmtree': 'WRITE-WARN-02',\n"
            "}\n"
            "SAME_ROOT_RULE_IDS = {'C4': ('WRITE-WARN-01', 'WRITE-WARN-02')}\n"
        ),
        good_example=(
            "DELETE_RULE_IDS = {\n"
            "    'os.remove': 'WRITE-WARN-01',\n"
            "    'os.rmdir': 'WRITE-WARN-02',\n"
            "    'os.unlink': 'WRITE-WARN-01',\n"
            "    'shutil.rmtree': 'WRITE-WARN-02',\n"
            "}\n"
            "DELETE_WRITE_RULE_IDS = tuple(dict.fromkeys(DELETE_RULE_IDS.values()))\n"
            "SAME_ROOT_RULE_IDS = {'C4': DELETE_WRITE_RULE_IDS}\n"
        ),
        rationale='同一张规则 ID 表的取值需要去重派生时，另一处再手抄同一组 '
                  'ID，新增或改名一个受管调用就会与派生值漂移',
        detector_ref=(anchor_module('diag_solidify_rules') + ' (CS-104 ast 规则) + ' + anchor_module('diag_guard_injection_scan.CIE_WRITE_SAME_ROOT_RULE_IDS')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-26', name='同源数据只保留一条投影',
        bad_example=(
            "def load_summary(skill_dir):\n"
            "    return _project_review_fields(_review_view(skill_dir))\n"
            "\n"
            "def load_context(skill_dir):\n"
            "    view = _review_view(skill_dir)\n"
            "    return {'overall_score': view.get('overall_score')}\n"
        ),
        good_example=(
            "def load_summary(skill_dir):\n"
            "    return _project_review_fields(_review_view(skill_dir))\n"
            "\n"
            "def load_context(skill_dir):\n"
            "    return _project_review_fields(_review_view(skill_dir))\n"
        ),
        rationale='同一个私有数据源，一处走统一投影函数、一处手拼常量键字典；'
                  '空数据时手拼分支产出全 None 的伪证据，被下游当真值写进溯源',
        detector_ref=(anchor_module('diag_solidify_rules') + ' (CS-105 ast 规则) + ' + anchor_module('xv_intermediate_store._project_review_fields')),
        **_GOV_REF_DEFAULTS,
    ),
    CodeRef(
        rule_id='GOV-27', name='同名私有副本的空信封口径须统一',
        bad_example=(
            "def _locate_sub_results(payload):\n"
            "    subs = payload.get('sub_results')\n"
            "    if not subs:\n"
            "        return None\n"
            "    return subs\n"
        ),
        good_example=(
            "from jwsgj.xv_intermediate_store import locate_sub_results\n"
            "\n"
            "subs = locate_sub_results(payload)\n"
        ),
        rationale='本模块 _helper 与兄弟模块公开 helper 同名同形参，但空信封口径'
                  '一个是 None、一个是 {}；消费方走哪份实现就两种结果，取不到'
                  '数据时要么抛 AttributeError、要么静默当成「无发现」',
        detector_ref=(anchor_module('diag_solidify_rules') + ' (CS-106 ast 规则) + ' + anchor_module('xv_intermediate_store.locate_sub_results')),
        **_GOV_REF_DEFAULTS,
    ),
], "GOV_CODE_REFS")
register_code_refs(GOV_CODE_REFS, "prevention_diag_refs")
