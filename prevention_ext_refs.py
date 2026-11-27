from __future__ import annotations  # noqa: I001
import logging
import jwsgj.prevention_lang_quality as _lang_quality
from jwsgj.prevention_refs_main import (
    DETECTOR_REF_ARTIFACT,
    DETECTOR_REF_RECOVERED,
    DETECTOR_REF_SECURITY,
    CodeRef,
    anchor_module,
    build_keyed_registry,
    make_code_ref,
    register_code_refs,
)
_BUG_REFS = _lang_quality.BUG_REFS
_FILEOPS_REFS = _lang_quality.FILEOPS_REFS
_IMPORTEXTRA_REFS = _lang_quality.IMPORTEXTRA_REFS
_PYTRAP_REFS = _lang_quality.PYTRAP_REFS
_SERIES_BUG = _lang_quality.SERIES_BUG
_SERIES_FILEOPS = _lang_quality.SERIES_FILEOPS
_SERIES_IMPORTEXTRA = _lang_quality.SERIES_IMPORTEXTRA
_SERIES_PYTRAP = _lang_quality.SERIES_PYTRAP
_SERIES_TESTQUALITY = _lang_quality.SERIES_TESTQUALITY
_TESTQUALITY_REFS = _lang_quality.TESTQUALITY_REFS
__all__ = [
    'AICODER_CODE_REFS',
    'AICODER_CODE_REFS_VERSION',
    'ASYNCIO_REFS',
    'EXT_CODE_REFS',
    'EXT_CODE_REFS_VERSION',
    'PERF_REFS',
    'ROBUST_EXTRA_REFS',
    'SECURITY_REFS',
    'SERIES_ASYNCIO',
    'SERIES_DEPRECATED_EXT',
    'SERIES_DPERF',
    'SERIES_DQUALITY',
    'SERIES_DSEC',
    'SERIES_DTRAP',
    'SERIES_PERF',
    'SERIES_ROBUST_EXTRA',
    'SERIES_SECURITY',
]
_log = logging.getLogger(__name__)
_log.info("prevention_ext_refs 已加载: %d 项导出", len(__all__))
EXT_CODE_REFS_VERSION = "1.5.13"
SERIES_SECURITY = "security"
SERIES_ASYNCIO = "asyncio"
SERIES_PERF = "perf"
SERIES_ROBUST_EXTRA = "robust_extra"
SERIES_DEPRECATED_EXT = "deprecated_ext"
SERIES_DSEC = "dsec"
SERIES_DQUALITY = "dquality"
SERIES_DPERF = "dperf"
SERIES_DTRAP = "dtrap"
_SERIES_CVMETHOD = "cvmethod"
_R_DB = (anchor_module('diag_guard_sql_connection') + ' (DetectorRegistry: DB06 编写时 preflight_diagnostic_check)')
_R_IO_SAFE = (anchor_module('diag_gate_io_control') + ' (DetectorRegistry: IO04 编写时 preflight_diagnostic_check)')
_R_SEC_IN = (anchor_module('diag_traps_payload') + ' (DetectorRegistry: IN01 编写时 preflight_diagnostic_check)')
_R_ASYNC_ITER = (anchor_module('diag_traps_async') + ' (DetectorRegistry: AY01/AY03/AY05-AY07/IT01 编写时 preflight_diagnostic_check) + ' + anchor_module('diag_traps_blocking') + ' (DetectorRegistry: AY02 编写时 preflight_diagnostic_check)')
_R_RDB = (anchor_module('diag_traps_async') + ' (DetectorRegistry: RD04/RD14/RD17 编写时 preflight_diagnostic_check)')
_R_TO = (anchor_module('diag_traps_blocking') + ' (DetectorRegistry: TO01/TO03 编写时 preflight_diagnostic_check)')
_R_STR_PAT = (anchor_module('diag_wiring_imports') + ' (DetectorRegistry: PX02/PX05 编写时 preflight_diagnostic_check)')
_R_DEPRECATED = (anchor_module('diag_rules_api_risk') + ' (DetectorRegistry: DP01-DP13/DP24/DP32-DP34/DP36-DP53 编写时 preflight_diagnostic_check)')
_R_AS07 = (anchor_module('diag_traps_coding') + ' (DetectorRegistry: AS07)')
_R_QC = (anchor_module('diag_traps_coding') + ' (DetectorRegistry: CQ05)')
_R_IT01 = (anchor_module('diag_traps_async') + ' (DetectorRegistry: IT01)')
_R_PY_SYNTAX_RULES = (anchor_module('diag_rules_py_syntax') + ' (DetectorRegistry: PY02/PY04) + ' + anchor_module('diag_pattern_rules') + ' (DetectorRegistry: MP01) + ' + anchor_module('diag_rules_text_damage') + ' (DetectorRegistry: PY09/PY10)')
_R_MS = (anchor_module('diag_merge_safety') + ' (DetectorRegistry: MS01/MS02；MS01 仅覆盖代码 token 全角标点，字符串内属预防引导)')
_R_TT02 = (anchor_module('diag_testing_static') + ' (DetectorRegistry: TT02)')
_R_RG04 = (anchor_module('diag_se_stdlib') + ' (DetectorRegistry: RG-02/RG-04)')
_R_TO04 = (anchor_module('diag_traps_blocking') + ' (DetectorRegistry: TO04)')
_R_PL = (anchor_module('diag_pattern_rules') + ' (DetectorRegistry: PL-01~PL-04 注册表适配)')
_R_SEC = (anchor_module('diag_traps_coding') + ' (AI03/IA03) + ' + anchor_module('diag_wiring_exc') + ' (SN03/SN05) (DetectorRegistry)')
_R_SE = (anchor_module('diag_se_stdlib') + ' (DetectorRegistry: SE-04)')
_R_SE_STATIC = (
    anchor_module('diag_se_injection') + ' (SE-02 command_injection) + ' + anchor_module('diag_se_data') + ' (SE-03 hardcoded_secret) + ' + anchor_module('diag_security_diagnoser') + ' (SE-38 增强扫描通道 check_SE38) (detect_all SE/SL 静态清单通道，未接线注册表 run_file_detectors)'
)
_R_IF = (anchor_module('diag_se_data') + ' (DetectorRegistry: IF-01 覆盖敏感变量→可观测 sink 的隐式流；本条常数时间比较属预防引导，无对应静态检测器)')
_R_SPLIT = (anchor_module('diag_wiring_imports') + ' (DetectorRegistry: SL01/SL05)')
_R_XR = (anchor_module('diag_wiring_symbol_scan') + ' (DetectorRegistry: XR01)')
SECURITY_REFS: list[CodeRef] = [
    make_code_ref(SERIES_SECURITY, 'CF-02', '硬编码密钥/Token', 'P0',
          'API_KEY = "sk-1234567890abcdef1234567890abcdef"\n',
          'import os\n\nAPI_KEY = os.environ.get("MY_API_KEY", "")\n',
          '密钥硬编码进源码即永久泄漏（git 历史/日志/异常栈都会带出），'
          '一律经环境变量或密钥管理器注入',
          DETECTOR_REF_ARTIFACT),
    make_code_ref(SERIES_SECURITY, 'SN-01', '守护/修复类调用吞错', 'P0',
          'def run_pipeline():\n'
          '    try:\n'
          '        pre_delivery_check()\n'
          '    except Exception:\n'
          '        pass\n'
          '\n'
          'def pre_delivery_check():\n'
          '    return True\n',
          'def run_pipeline():\n'
          '    try:\n'
          '        pre_delivery_check()\n'
          '    except Exception as e:\n'
          '        raise RuntimeError(f"pre-delivery check failed: {e}") from e\n'
          '\n'
          'def pre_delivery_check():\n'
          '    return True\n',
          '交付前检查/自愈等守护调用被静默吞错后流程"绿灯放行"，'
          '防线形同虚设，必须向上抛出或记录后显式降级',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_SECURITY, 'SN-02', '状态管理函数吞错', 'P1',
          'def sync():\n'
          '    try:\n'
          '        mark_tools_used("diag")\n'
          '    except Exception:\n'
          '        pass\n',
          'def mark_tools_used(name):\n'
          '    """记录工具使用。"""\n'
          '    return name\n'
          '\n'
          'def sync():\n'
          '    try:\n'
          '        mark_tools_used("diag")\n'
          '    except Exception as e:\n'
          '        raise RuntimeError(f"state sync failed: {e}") from e\n',
          '状态落盘/计数类调用失败被吞后，后续依赖该状态的决策全部'
          '基于过期数据，错误沿调用链放大',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_SECURITY, 'SN-04', '空 except 块吞掉一切', 'P0',
          'def parse(text):\n'
          '    try:\n'
          '        return int(text)\n'
          '    except:\n'
          '        pass\n'
          '    return 0\n',
          'def parse(text):\n'
          '    try:\n'
          '        return int(text)\n'
          '    except ValueError:\n'
          '        return 0\n',
          '裸 except 连 KeyboardInterrupt/SystemExit 一并吞掉，且无任何'
          '痕迹，排障时如同盲区；至少要收窄异常类型并留痕',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_SECURITY, 'CV-01', 'chmod 权限过于宽松', 'P1',
          'import os\n\nos.chmod("config.json", 0o777)\n',
          'import os\n\nos.chmod("config.json", 0o600)\n',
          '0o777 允许任意用户读写执行，含凭据的文件等于裸奔；'
          '按最小权限给 0o600/0o644',
          DETECTOR_REF_SECURITY),
    make_code_ref(SERIES_SECURITY, 'DB-06', 'sqlite 连接未关闭', 'P1',
          'import sqlite3\n\n'
          'def query_rows():\n'
          '    conn = sqlite3.connect("app.db")\n'
          '    return conn.execute("SELECT 1").fetchall()\n',
          'import sqlite3\n\n'
          'def query_rows():\n'
          '    conn = sqlite3.connect("app.db")\n'
          '    try:\n'
          '        return conn.execute("SELECT 1").fetchall()\n'
          '    finally:\n'
          '        conn.close()\n',
          '连接不关闭导致文件锁悬挂（Windows 上文件被占用无法删除），'
          '异常路径泄漏更快；sqlite3 连接的 with 只管事务提交/回滚并不'
          '关闭连接，须 try/finally 显式 close',
          _R_DB),
    make_code_ref(SERIES_SECURITY, 'IO-04', 'FTP 被动模式 SSRF', 'P1',
          'from ftplib import FTP, ftpcp\n\n'
          'src = FTP("untrusted.example")\n'
          'dst = FTP("internal.example")\n'
          'ftpcp(src, "payload.bin", dst)\n',
          'import requests\n\n'
          'resp = requests.get(\n'
          '    "https://example.com/file",\n'
          '    headers={"User-Agent": "example-client/1.0"},\n'
          '    timeout=10,\n'
          ')\n',
          'ftplib.ftpcp() 直接把 PASV 响应中的地址当回连目标'
          '（CVE-2026-8328，3.10.21/3.11.16/3.12.14 等修复版本起）：不可信 FTP '
          '服务器可把回连指向任意内网地址/端口，构成 SSRF 跳板；优先改用 '
          'HTTPS，或升级修复版本并只连可信 FTP 服务器',
          _R_IO_SAFE),
    make_code_ref(SERIES_SECURITY, 'IN-01', 'open 缺 encoding 参数', 'P1',
          'def read(path):\n    with open(path) as f:\n        return f.read()\n',
          'def read(path):\n'
          '    with open(path, encoding="utf-8") as f:\n'
          '        return f.read()\n',
          '文本模式缺 encoding 时依赖平台区域设置（Windows 中文环境常为 GBK），'
          '跨平台读 UTF-8 文件可能直接 UnicodeDecodeError',
          _R_SEC_IN),
    make_code_ref(SERIES_SECURITY, 'CC-01', '常量条件分支', 'P2',
          'if True:\n    print("always runs")\n',
          'def check(flag):\n'
          '    if flag:\n'
          '        print("maybe")\n',
          'if True/if False 多为调试残留或条件变量被误替换，'
          '分支语义失真且 else 分支永不执行，掩盖真实逻辑',
          DETECTOR_REF_SECURITY),
]
ASYNCIO_REFS: list[CodeRef] = [
    make_code_ref(SERIES_ASYNCIO, 'AY-01', 'create_task 后不保存引用', 'P1',
          'import asyncio\n\n'
          'async def worker():\n'
          '    await asyncio.sleep(0.1)\n'
          '\n'
          'async def main():\n'
          '    asyncio.create_task(worker())\n'
          '    await asyncio.sleep(0.2)\n',
          'import asyncio\n\n'
          'async def worker():\n'
          '    await asyncio.sleep(0.1)\n'
          '\n'
          'async def main():\n'
          '    task = asyncio.create_task(worker())\n'
          '    task.add_done_callback(_log_task_exception)\n'
          '    await task\n'
          '\n'
          'def _log_task_exception(t):\n'
          '    if not t.cancelled() and t.exception():\n'
          '        print(t.exception())\n',
          '无引用的 Task 可能被垃圾回收中途取消，异常也无从观察'
          '（"fire-and-forget"静默失败）；保存引用并挂 done_callback',
          _R_ASYNC_ITER),
    make_code_ref(SERIES_ASYNCIO, 'AY-02', 'async 函数内同步阻塞调用', 'P1',
          'import asyncio\nimport time\n\n'
          'async def worker():\n'
          '    time.sleep(1)\n'
          '    return "done"\n',
          'import asyncio\n\n'
          'async def worker():\n'
          '    await asyncio.sleep(1)\n'
          '    return "done"\n',
          '事件循环被同步阻塞后所有并发任务集体卡死，吞吐退化为串行；'
          '改用 await 等价物或 to_thread/run_in_executor',
          _R_ASYNC_ITER),
    make_code_ref(SERIES_ASYNCIO, 'AY-03', 'gather 未处理异常', 'P1',
          'import asyncio\n\n'
          'async def main():\n'
          '    results = await asyncio.gather(task_a(), task_b())\n'
          '    return results\n'
          '\n'
          'async def task_a():\n'
          '    return 1\n'
          '\n'
          'async def task_b():\n'
          '    return 2\n',
          'import asyncio\n\n'
          'async def main():\n'
          '    results = await asyncio.gather(task_a(), task_b(), return_exceptions=True)\n'
          '    values = []\n'
          '    errors = []\n'
          '    for result in results:\n'
          '        if isinstance(result, (Exception, asyncio.CancelledError)):\n'
          '            errors.append(str(result) or type(result).__name__)\n'
          '        else:\n'
          '            values.append(result)\n'
          '    return {"values": values, "errors": errors}\n'
          '\n'
          'async def task_a():\n'
          '    return 1\n'
          '\n'
          'async def task_b():\n'
          '    return 2\n',
          'gather 默认一处抛异常即整体抛出，其余任务结果全部丢弃；'
          'return_exceptions=True 才能拿到完整结果自行分流；CancelledError 继承 '
          'BaseException 而非 Exception，分流时须显式包含，空消息用类型名留痕',
          _R_ASYNC_ITER),
    make_code_ref(SERIES_ASYNCIO, 'AY-05', '运行循环内再调 asyncio.run', 'P1',
          'import asyncio\n\n'
          'async def main():\n'
          '    return asyncio.run(asyncio.sleep(0, result=1))\n',
          'import asyncio\n\n'
          'async def main():\n'
          '    return await asyncio.sleep(0, result=1)\n',
          'asyncio.run 在已有事件循环的上下文中调用直接 RuntimeError 崩溃；'
          'async 上下文内一律用 await',
          _R_ASYNC_ITER),
    make_code_ref(SERIES_ASYNCIO, 'AY-06', 'submit 后丢弃 Future', 'P1',
          'from concurrent.futures import ThreadPoolExecutor\n\n'
          'def heavy_work():\n'
          '    return sum(range(100))\n'
          '\n'
          'executor = ThreadPoolExecutor()\n'
          'executor.submit(heavy_work)\n',
          'from concurrent.futures import ThreadPoolExecutor\n\n'
          'def heavy_work():\n'
          '    return sum(range(100))\n'
          '\n'
          'with ThreadPoolExecutor() as executor:\n'
          '    future = executor.submit(heavy_work)\n'
          '    print(future.result())\n',
          '不持有 Future 时工作线程的异常被静默吞噬，失败无从得知；'
          '保存 Future 并消费 result()/exception()',
          _R_ASYNC_ITER),
    make_code_ref(SERIES_ASYNCIO, 'AY-07', '事件循环策略硬编码', 'P1',
          'import asyncio\n\n'
          'asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())\n',
          'import asyncio\n\n'
          'async def main():\n'
          '    return await asyncio.sleep(0, result=1)\n'
          '\n'
          '# 不设置全局策略：asyncio.run() 使用运行环境的默认策略\n'
          'asyncio.run(main())\n',
          '硬编码平台专属策略在跨平台运行时直接失效；不设置全局策略，'
          '交给 asyncio.run() 使用运行环境的默认策略，'
          '避免把单一平台的行为写死',
          _R_ASYNC_ITER),
]
PERF_REFS: list[CodeRef] = [
    make_code_ref(SERIES_PERF, 'RD-04', '循环内重建常量容器', 'P3',
          'def build(rows):\n'
          '    out = []\n'
          '    for row in rows:\n'
          '        table = [1, 2, 3, 4, 5]\n'
          '        out.append(table[0] + len(row))\n'
          '    return out\n',
          'TABLE = [1, 2, 3, 4, 5]\n'
          '\n'
          'def build(rows):\n'
          '    out = []\n'
          '    for row in rows:\n'
          '        out.append(TABLE[0] + len(row))\n'
          '    return out\n',
          '循环体内对全常量字面量容器反复赋值，每次迭代重建同一对象'
          '浪费 CPU/内存；提升到循环外复用',
          _R_RDB),
    make_code_ref(SERIES_PERF, 'RD-14', '循环内网络/IO 调用', 'P2',
          'import requests\n\n'
          'def fetch(urls):\n'
          '    out = []\n'
          '    for url in urls:\n'
          '        resp = requests.get(url, timeout=5)\n'
          '        out.append(resp.status_code)\n'
          '    return out\n',
          'import requests\n\n'
          'def fetch(urls):\n'
          '    with requests.Session() as session:\n'
          '        out = []\n'
          '        for url in urls:\n'
          '            resp = session.get(url, timeout=5)\n'
          '            out.append(resp.status_code)\n'
          '        return out\n',
          '循环内逐个发起网络请求是 O(n) 次往返，延迟线性放大；'
          '复用连接（Session）或改并发批量',
          _R_RDB),
    make_code_ref(SERIES_PERF, 'RD-17', '嵌套函数定义超过三层', 'P2',
          'def outer(a):\n'
          '    def mid(b):\n'
          '        def inner(c):\n'
          '            def core(d):\n'
          '                return a + b + c + d\n'
          '            return core\n'
          '        return inner\n'
          '    return mid\n',
          'def outer(a, b, c, d):\n'
          '    # 拍平为模块级单层函数: 闭包链改为显式参数,\n'
          '    # 调用方同步由 outer(1)(2)(3)(4) 改为 outer(1, 2, 3, 4)\n'
          '    return a + b + c + d\n',
          '深层闭包链让变量来源难以追踪、调试栈不可读；'
          '超过三层的嵌套应提取为模块级函数',
          _R_RDB),
    make_code_ref(SERIES_PERF, 'TO-01', 'requests 调用未设 timeout', 'P1',
          'import requests\n\nresp = requests.get("https://example.com")\n',
          'import requests\n\n'
          'resp = requests.get(\n'
          '    "https://example.com",\n'
          '    headers={"User-Agent": "example-client/1.0"},\n'
          '    timeout=10,\n'
          ')\n',
          '无 timeout 的请求在网络抖动时无限挂起，整条流水线被拖死；'
          '每次请求必须显式设置超时',
          _R_TO),
    make_code_ref(SERIES_PERF, 'TO-03', 'time.sleep 休眠超过 60 秒', 'P2',
          'import time\n\ntime.sleep(120)\n',
          'import threading\n\n'
          'stop_event = threading.Event()\n'
          'stop_event.wait(120)\n',
          '超长同步休眠会阻塞当前线程且无法被其他线程直接中断；'
          '保持原等待时长并改用 Event.wait，stop_event.set() 可立即唤醒等待方',
          _R_TO),
]
ROBUST_EXTRA_REFS: list[CodeRef] = [
    make_code_ref(SERIES_ROBUST_EXTRA, 'LE-03', 'suppress(Exception) 捕获过宽', 'P2',
          'from contextlib import suppress\n\n'
          'def risky():\n'
          '    raise ValueError("x")\n'
          '\n'
          'with suppress(Exception):\n'
          '    risky()\n',
          'from contextlib import suppress\n\n'
          'def risky():\n'
          '    raise ValueError("x")\n'
          '\n'
          'with suppress(ValueError):\n'
          '    risky()\n',
          'suppress(Exception) 静默吞掉一切异常（含编程错误），'
          '问题被隐藏而非处理；收窄到预期异常类型',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_ROBUST_EXTRA, 'LE-04', 'filterwarnings 无过滤条件', 'P2',
          'import warnings\n\nwarnings.filterwarnings("ignore")\n',
          'import warnings\n\nwarnings.filterwarnings("default", category=DeprecationWarning)\n',
          '无过滤器的全局 ignore 会把 DeprecationWarning 等线索全部屏蔽；'
          '需要保留弃用告警时应对该 category 使用 default（或 error），'
          '不能用 ignore 继续屏蔽目标告警',
          DETECTOR_REF_RECOVERED),
    make_code_ref(SERIES_ROBUST_EXTRA, 'PX-02', '字符串模板混合缩进', 'P2',
          'tpl = "head {x}\\n    spaced\\n\\ttabbed"\n',
          'tpl = "head {x}\\n    spaced\\n    aligned"\n',
          '多行模板混用 tab/空格缩进后，凭肉眼推断做替换必错；'
          '统一缩进风格并用 repr() 确认精确内容',
          _R_STR_PAT),
    make_code_ref(SERIES_ROBUST_EXTRA, 'PX-05', 'redirect_stdout 未按上下文管理', 'P1',
          'from contextlib import redirect_stdout\n'
          'import io\n\n'
          'redirect_stdout(io.StringIO()).__enter__()\n'
          'print("lost output")\n',
          'from contextlib import redirect_stdout\n'
          'import io\n\n'
          'buf = io.StringIO()\n'
          'with redirect_stdout(buf):\n'
          '    print("captured")\n'
          'print(buf.getvalue())\n',
          '手动 __enter__ 而不配对 __exit__：stdout 被永久改写到缓冲区，'
          '此后所有输出丢失且进程内无法恢复（裸调用则相反，重定向从未'
          '生效、捕获恒为空）；一律用 with 限定作用域，或直接 file= 写出',
          _R_STR_PAT),
]
_DEPRECATED_EXT_REFS: list[CodeRef] = [
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-01', 'distutils 已移除(3.12)', 'P1',
          'import distutils.core\n\nsetup = distutils.core.setup\n',
          'from setuptools import setup\n'
          '\n'
          'setup(name="pkg", version="1.0")\n',
          'distutils 在 Python 3.12 被整体移除，导入即 ModuleNotFoundError；'
          '构建统一走 setuptools',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-02', 'ast.Num 等 3.14 移除节点', 'P1',
          'from ast import Num\n\nnode = Num(1)\n',
          'from ast import Constant\n\nnode = Constant(1)\n',
          'ast.Num/Str/Bytes/NameConstant 在 3.8 弃用、3.14 移除；'
          '新代码一律使用 ast.Constant',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-03', 'multiprocessing 未显式指定 start_method', 'P2',
          'import multiprocessing\n\n'
          'def worker():\n'
          '    return 1\n'
          '\n'
          'proc = multiprocessing.Process(target=worker)\n'
          'proc.start()\n',
          'import multiprocessing\n\n'
          'def worker():\n'
          '    return 1\n'
          '\n'
          'if __name__ == "__main__":\n'
          '    ctx = multiprocessing.get_context("spawn")\n'
          '    proc = ctx.Process(target=worker)\n'
          '    proc.start()\n'
          '    proc.join()\n',
          '默认 start_method 随平台漂移（Windows spawn / Linux fork），'
          'fork 下线程锁状态可能死锁；显式 get_context 固定语义',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-06', '项目基线允许时统一 PEP 604 可选类型注解', 'P2',
          '# 项目最低版本为 Python 3.10，团队约定统一使用 PEP 604。\n'
          'from typing import Optional\n\n'
          'def find(key: str) -> Optional[int]:\n'
          '    return len(key) if key else None\n',
          '# 同一 Python 3.10+ 项目按约定使用内置联合类型。\n'
          'def find(key: str) -> int | None:\n'
          '    return len(key) if key else None\n',
          '本条只适用于已选择 PEP 604 且最低版本为 Python 3.10 的项目：'
          'X | None 的运行时联合类型契约自 3.10 起提供。typing.Optional '
          '并未弃用；支持 3.9 及更早版本的项目应保留 Optional，或采用经'
          '项目工具链验证的延迟注解策略，不得为新语法抬高运行时要求',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-13', 'inspect.formatargspec 已移除(3.11)', 'P2',
          'import inspect\n\nsig = inspect.formatargspec(inspect.getfullargspec(len))\n',
          'import inspect\n\nsig = str(inspect.signature(len))\n',
          'formatargspec 在 3.5 弃用、3.11 移除，调用直接 AttributeError；'
          '用 str(inspect.signature(...))',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-24', 'platform.popen 已移除', 'P2',
          'import platform\n\nhandle = platform.popen("python --version")\n',
          'import subprocess\n'
          'import sys\n'
          '\n'
          'result = subprocess.run(\n'
          '    [sys.executable, "--version"],\n'
          '    capture_output=True, timeout=30, check=True,\n'
          ')\n',
          'platform.popen 是 os.popen 的转发壳，Python 3.8 起标准库已无'
          '此函数（3.8-3.12 各版模块文档均无记载、3.12 运行时实证），'
          '无编码控制且资源管理弱；统一改用 subprocess',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-34', '__import__ 动态导入', 'P3',
          'mod = __import__("os.path")\n',
          'import importlib\n\nmod = importlib.import_module("os")\n',
          '__import__ 语义晦涩（默认返回顶层包）且绕过静态导入检查，'
          '重构工具全部失明；改用 importlib.import_module。替换时须保持'
          '原绑定语义：原调用依赖顶层包就显式导入顶层包；目标若为子模块，'
          '应重新明确消费契约，不得借 API 替换静默改变 mod 指向',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-36', 'assertDictContainsSubset 已移除', 'P2',
          'import unittest\n\n'
          'class Case(unittest.TestCase):\n'
          '    def test_subset(self):\n'
          '        self.assertDictContainsSubset({"a": 1}, {"a": 1, "b": 2})\n',
          'import unittest\n\n'
          'class Case(unittest.TestCase):\n'
          '    def test_subset(self):\n'
          '        self.assertEqual({"a": 1}, {k: v for k, v in {"a": 1, "b": 2}.items() if k in {"a": 1}})\n',
          'assertDictContainsSubset 在 Python 3.2 弃用、3.12 移除；'
          '用字典推导 + assertEqual 表达子集断言',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-37', 'assert_ 旧方法已移除(3.12)', 'P3',
          'import unittest\n\n'
          'class Case(unittest.TestCase):\n'
          '    def test_ok(self):\n'
          '        self.assert_(True)\n',
          'import unittest\n\n'
          'class Case(unittest.TestCase):\n'
          '    def test_ok(self):\n'
          '        self.assertTrue(True)\n',
          'assert_ 是历史别名，3.12 已移除，调用直接 AttributeError；'
          '断言用 assertTrue/assertFalse',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-38', 'ElementTree.getchildren 已移除', 'P2',
          'import xml.etree.ElementTree as ET\n\n'
          'root = ET.fromstring("<a><b/></a>")\n'
          'children = root.getchildren()\n',
          'import xml.etree.ElementTree as ET\n\n'
          'root = ET.Element("a")\n'
          'ET.SubElement(root, "b")\n'
          'children = list(root)\n',
          'getchildren 在 3.2 弃用、3.9 移除；子节点遍历用 list(elem)'
          ' 或 elem.iter()',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-40', 'base64.encodestring 已弃用', 'P2',
          'import base64\n\nraw = base64.encodestring(b"data")\n',
          'import base64\n\nraw = base64.encodebytes(b"data")\n',
          'encodestring/decodestring 已弃用多年且 3.9 起移除；'
          '用 encodebytes/decodebytes',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-41', 'imaplib keyfile/certfile 已移除(3.12)', 'P3',
          'import imaplib\n\n'
          'mail = imaplib.IMAP4_SSL("host", keyfile="k.pem", certfile="c.pem")\n',
          'import imaplib\nimport ssl\n\n'
          'ctx = ssl.create_default_context()\n'
          'ctx.load_cert_chain(certfile="c.pem", keyfile="k.pem")\n'
          'mail = imaplib.IMAP4_SSL("host", ssl_context=ctx)\n',
          'keyfile/certfile 分离传参 3.6 弃用、3.12 已移除（传参即'
          ' TypeError）；构建 SSLContext 并加载原客户端证书链，再经'
          ' ssl_context 参数传入',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-42', 'smtplib keyfile/certfile 已移除(3.12)', 'P3',
          'import smtplib\n\n'
          'smtp = smtplib.SMTP_SSL("host", keyfile="k.pem", certfile="c.pem")\n',
          'import smtplib\nimport ssl\n\n'
          'ctx = ssl.create_default_context()\n'
          'ctx.load_cert_chain(certfile="c.pem", keyfile="k.pem")\n'
          'smtp = smtplib.SMTP_SSL("host", context=ctx)\n',
          '同 imaplib：keyfile/certfile 3.6 弃用、3.12 已移除，改经'
          ' context 传已加载原客户端证书链的 SSLContext',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-43', 'ssl.wrap_socket 已移除(3.12)', 'P2',
          'import ssl\nimport socket\n\n'
          's = ssl.wrap_socket(socket.socket())\n',
          'import ssl\nimport socket\n\n'
          'ctx = ssl.create_default_context()\n'
          's = ctx.wrap_socket(socket.socket(), server_hostname="example.com")\n',
          'wrap_socket 无法配置证书校验与协议版本，3.7 弃用、3.12 已'
          '移除；创建默认 SSLContext 再 wrap，客户端必须传 server_hostname 以完成主机名校验',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-44', 'ssl.match_hostname 已移除', 'P2',
          'import ssl\n\nmatch = ssl.match_hostname(None, "host")\n',
          'import ssl\n\nctx = ssl.create_default_context()\n',
          'match_hostname 在 3.7 弃用、3.12 移除（OpenSSL 内建'
          '主机名校验取代，gh-94199）；证书校验交给 SSLContext 默认行为',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-46', '旧式 @asyncio.coroutine 已弃用', 'P2',
          'import asyncio\n\n'
          '@asyncio.coroutine\n'
          'def old():\n'
          '    x = yield from asyncio.sleep(0)\n'
          '    return x\n',
          'import asyncio\n\n'
          'async def modern():\n'
          '    return await asyncio.sleep(0)\n',
          '@asyncio.coroutine + yield from 是 3.4 时代写法，'
          '3.8 弃用、3.11 移除；统一 async def + await',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-48', 'typing.re 已弃用', 'P2',
          'from typing.re import Pattern\n\npat = Pattern\n',
          'import re\n\n'
          'def is_pattern(value):\n'
          '    """判定正则模式对象。"""\n'
          '    return isinstance(value, re.Pattern)\n',
          'typing.re 命名空间 3.8 弃用、3.13 移除；正则类型直接用'
          ' re.Pattern/re.Match',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-50', 'from urllib import X（Py2 路径）', 'P1',
          'from urllib import urlencode\n\nqs = urlencode({"a": 1})\n',
          'from urllib.parse import urlencode\n\nqs = urlencode({"a": 1})\n',
          'Python 3 中 urllib 按用途拆分为 parse/request/error 子模块，'
          '顶层导入直接 ImportError；AI 依 Py2 记忆生成时的高频幻觉',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-51', 'from email import Message（旧式）', 'P2',
          'from email import Message\n\nmsg = Message.Message()\n',
          'from email.message import EmailMessage\n\nmsg = EmailMessage()\n',
          'email.Message 是 Py2 兼容层，新 API 为'
          ' email.message.EmailMessage；旧式导入已不可用',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-52', 'HTTPConnection strict 参数已移除', 'P3',
          'import http.client\n\n'
          'conn = http.client.HTTPConnection("host", 80, strict=True)\n',
          'import http.client\n\n'
          'conn = http.client.HTTPConnection("host", 80)\n',
          'strict 参数 3.2 弃用、3.4 移除；传入即 TypeError'
          '（关键字不匹配）',
          _R_DEPRECATED),
    make_code_ref(SERIES_DEPRECATED_EXT, 'DP-53', 'SafeConfigParser 已移除', 'P2',
          'from configparser import SafeConfigParser\n\n'
          'parser = SafeConfigParser()\n',
          'from configparser import ConfigParser\n\n'
          'parser = ConfigParser()\n',
          'SafeConfigParser 在 3.2 弃用（行为与 ConfigParser 合并）、'
          '3.12 移除；直接用 ConfigParser',
          _R_DEPRECATED),
]
_DQUALITY_REFS: list[CodeRef] = [
make_code_ref(
    SERIES_DQUALITY, "AS-07", "assert 用于数据验证", "P3",
    'def transfer(account, amount):\n'
    '    """转账。"""\n'
    '    assert amount > 0, "amount must be positive"\n'
    '    return account.withdraw(amount)\n',
    'def transfer(account, amount):\n'
    '    """转账。"""\n'
    '    if amount <= 0:\n'
    '        raise ValueError(f"amount must be positive, got {amount}")\n'
    '    return account.withdraw(amount)\n',
    "assert 在 python -O 下被整体剔除，生产环境的入参校验形同虚设；数据"
    "验证必须用显式 if + raise（测试文件外禁用 assert 断言业务约束）。",
    _R_AS07,
),
make_code_ref(
    SERIES_DQUALITY, "CQ-05", "非测试代码裸 assert（生产风险）", "P2",
    'def parse_config(raw):\n'
    '    """解析配置。"""\n'
    '    assert raw\n'
    '    return dict(raw)\n',
    'def parse_config(raw):\n'
    '    """解析配置。"""\n'
    '    if not raw:\n'
    '        raise ValueError("raw config must not be empty")\n'
    '    return dict(raw)\n',
    "生产代码中的裸 assert（无长 msg）在优化模式下被剔除且失败信息不可读；"
    "与 CQ-02 分工：业务断言用 if+raise，仅测试文件保留 assert。",
    _R_QC,
),
make_code_ref(
    SERIES_DQUALITY, "IT-01", "迭代中删除被迭代容器", "P1",
    'def clean(items):\n'
    '    """清理无效项。"""\n'
    '    for item in items:\n'
    '        if item.bad:\n'
    '            del items\n',
    'def clean(items):\n'
    '    """清理无效项（迭代副本）。"""\n'
    '    for item in list(items):\n'
    '        if item.bad:\n'
    '            items.remove(item)\n',
    "for 循环内 del 被迭代容器名只解绑名字：迭代器仍持原对象引用，循环"
    "零跳项走完而清理静默失效（容器从未被改动，循环后引用该名即 "
    "NameError）；del 容器元素或对迭代源原地变异（remove/pop/clear 等）"
    "才会破坏迭代器协议、产生漏迭代/随机跳项；应迭代副本后修改原容器。",
    _R_IT01,
),
make_code_ref(
    SERIES_DQUALITY, "MP-01", "自定义 metaclass 使用", "P2",
    'REGISTRY = {}\n'
    '\n'
    'class RegistryMeta(type):\n'
    '    """注册元类。"""\n'
    '    def __new__(mcs, name, bases, ns):\n'
    '        cls = super().__new__(mcs, name, bases, ns)\n'
    '        REGISTRY[name] = cls\n'
    '        return cls\n'
    '\n'
    'class Plugin(metaclass=RegistryMeta):\n'
    '    """插件基类。"""\n',
    '_REGISTRY = {}\n'
    '\n'
    'def register(cls):\n'
    '    """显式注册装饰器。"""\n'
    '    _REGISTRY[cls.__name__] = cls\n'
    '    return cls\n'
    '\n'
    '@register\n'
    'class Plugin:\n'
    '    """插件基类。"""\n',
    "自定义 metaclass 是隐式魔法：导入即触发注册、调试困难、多数场景可用"
    "显式装饰器/类属性替代（标准库 ABCMeta/EnumMeta 豁免）。",
    _R_PY_SYNTAX_RULES,
),
make_code_ref(
    SERIES_DQUALITY, "MS-01", "代码 token 全角标点（Unicode 安全）", "P2",
    'def render(x, y):\n'
    '    """x."""\n'
    '    # 想输出半角逗号分隔却误敲全角——字符串文本内为数据级漂移；\n'
    '    # token 位置（如 def f(x，y):）的全角标点则直接 SyntaxError\n'
    '    result = f"{x}\uff0c{y}"\n'
    '    return result\n',
    'def render(x, y):\n'
    '    """x."""\n'
    '    # 代码 token 用半角；普通文案按项目语言与数据契约使用 Unicode\n'
    '    result = f"{x}, {y}"\n'
    '    return result\n',
    "代码 token（变量名/运算符/括号/逗号）中的全角标点（，：（））会导致 "
    "SyntaxError 或隐蔽的名称不匹配（tokenize 精确区分上下文）；普通字符串、"
    "注释与 docstring 可按项目语言和数据契约使用 Unicode。字符串若作为机器"
    "文法输入，则另按目标文法选择标点。",
    _R_MS,
    self_verifiable=False,
),
make_code_ref(
    SERIES_DQUALITY, "PY-02", "docstring 宣称但未真实定义的符号", "P0",
    '"""Usage:\n'
    '\n'
    '    rules = load_all_rules()\n'
    '"""\n'
    '\n'
    '\n'
    'def get_rule(rule_id):\n'
    '    """x."""\n'
    '    for r in rules:\n'
    '        if r == rule_id:\n'
    '            return r\n'
    '    return None\n',
    'RULES = []\n'
    '\n'
    '\n'
    'def get_rule(rule_id):\n'
    '    """x."""\n'
    '    for r in RULES:\n'
    '        if r == rule_id:\n'
    '            return r\n'
    '    return None\n',
    "docstring 示例里的绑定名被可执行代码引用而真实代码从未绑定，运行期必"
    " NameError——AI 生成代码的高频幻觉形态（文档与实现脱节）；示例中的"
    "名字必须在可执行代码中真实绑定。",
    _R_PY_SYNTAX_RULES,
),
make_code_ref(
    SERIES_DQUALITY, "PY-09", "ASCII 文法字符串误用全角括号", "P1",
    '# 该字符串随后交给 compile()，必须遵循 Python 文法标点\n'
    'EXPRESSION = "（ready）"\n',
    '# 机器文法与普通文案分开维护\n'
    'EXPRESSION = "(ready)"\n'
    'LABEL = "（就绪）请检查配置"\n',
    "普通字符串中的全角括号和其他 Unicode 文本完全合法，不应一概替换；只有"
    "字符串会作为 Python/SQL/DSL 等机器文法的输入，且目标文法要求 ASCII "
    "标点时，全角括号才会造成 SyntaxError 或解析失败。应区分普通文案与机器"
    "文法，并以后者的实际语法契约为准。",
    (anchor_module('diag_rules_text_damage')
     + " (DetectorRegistry: PY09 覆盖代码 token；"
     "本条仅引导交给 ASCII 文法解析器的字符串，普通 Unicode 文案不属于命中面)"),
    self_verifiable=False,
),
make_code_ref(
    SERIES_DQUALITY, "PY-10", "双反斜杠转义误用", "P3",
    'PATH = "C:\\\\new\\\\table"\n',
    'PATH = r"C:\\new\\table"\n',
    '字符串中密集手写 \\\\n / \\\\t 等双反斜杠序列是转义层级混乱的信号'
    '（想要字面反斜杠的路径/正则应改用原始字符串；想要换行/制表符'
    "则应写单反斜杠转义 \\n / \\t 而非双反斜杠叠加）；Windows 路径与正则应使用原始字符串 r''。",
    _R_PY_SYNTAX_RULES,
),
make_code_ref(
    SERIES_DQUALITY, "TT-02", "测试模块级可变全局状态", "P2",
    'CACHE = {}\n'
    '\n'
    'def test_first():\n'
    '    CACHE["k"] = 1\n'
    '    assert CACHE["k"] == 1\n'
    '\n'
    'def test_second():\n'
    '    assert "k" not in CACHE  # 依赖执行顺序，模块级状态串扰\n',
    'import pytest\n'
    '\n'
    '@pytest.fixture\n'
    'def cache():\n'
    '    return {}\n'
    '\n'
    'def test_first(cache):\n'
    '    cache["k"] = 1\n'
    '    assert cache["k"] == 1\n'
    '\n'
    'def test_second(cache):\n'
    '    assert "k" not in cache  # fixture 每测试独立实例\n',
    "test 文件模块级可变对象（list/dict/set）在测试间共享状态，测试结果"
    "依赖执行顺序；可变状态应放进 fixture 或函数局部。",
    _R_TT02,
),
]
_DPERF_REFS: list[CodeRef] = [
make_code_ref(
    SERIES_DPERF, "RG-04", "贪婪 .* 意外匹配过多", "P3",
    'import re\n'
    '\n'
    'def extract_tag(text):\n'
    '    """提取首对标签。"""\n'
    '    return re.search(r"<.*>", text, re.DOTALL).group(0)\n',
    'import re\n'
    '\n'
    'def extract_tag(text):\n'
    '    """提取首对标签（非贪婪，保留跨行匹配）。"""\n'
    '    match = re.search(r"<.*?>", text, re.DOTALL)\n'
    '    return match.group(0) if match else ""\n',
    "贪婪 .* 叠加 re.DOTALL/re.S 跨行标志会跨过中间结束符与换行，"
    "一直吞到源文本最后一个 '>'，跨行成对结构提取结果远超预期；"
    "跨行提取应用非贪婪 .*?（单行无跨行标志的场景一般不构成问题）。",
    _R_RG04,
),
make_code_ref(
    SERIES_DPERF, "TO-04", "同步原语操作未设超时", "P2",
    'import threading\n'
    '\n'
    '_lock = threading.Lock()\n'
    '\n'
    'def update(data):\n'
    '    """更新共享数据。"""\n'
    '    _lock.acquire()\n'
    '    try:\n'
    '        return process(data)\n'
    '    finally:\n'
    '        _lock.release()\n',
    'import threading\n'
    '\n'
    '_lock = threading.Lock()\n'
    '\n'
    'def process(data):\n'
    '    """处理数据。"""\n'
    '    return data\n'
    '\n'
    'def update(data):\n'
    '    """更新共享数据（带超时）。"""\n'
    '    if not _lock.acquire(timeout=5):\n'
    '        raise TimeoutError("update: lock busy")\n'
    '    try:\n'
    '        return process(data)\n'
    '    finally:\n'
    '        _lock.release()\n',
    "Lock.acquire/Event.wait/Queue.get 不设 timeout 时，持锁方异常卡死会"
    "让等待线程永久阻塞（等待线程连同 daemon 线程一起冻结，进程无法推进）；同步原语操作必须带超时。",
    _R_TO04,
),
make_code_ref(
    SERIES_DPERF, "PL-04", "N+1 查询模式", "P2",
    'def load_user_prefs(users, conn):\n'
    '    """取每个用户的偏好。"""\n'
    '    result = {}\n'
    '    for user in users:\n'
    '        rows = conn.query("SELECT * FROM prefs WHERE user_id=?", user.id)\n'
    '        result[user.id] = rows\n'
    '    return result\n',
    'def _in_clause(count):\n'
    '    """构造 count 个占位符。"""\n'
    '    return ",".join(["?"] * count)\n'
    '\n'
    'def load_user_prefs(users, conn):\n'
    '    """批量取用户偏好。"""\n'
    '    ids = [u.id for u in users]\n'
    '    if not ids:\n'
    '        return {}\n'
    '    sql = "SELECT * FROM prefs WHERE user_id IN (%s)" % _in_clause(len(ids))\n'
    '    rows = conn.query(sql, ids)\n'
    '    grouped = {user_id: [] for user_id in ids}\n'
    '    for row in rows:\n'
    '        grouped.setdefault(row["user_id"], []).append(row)\n'
    '    return grouped\n',
    "循环内逐条查询（N+1）使数据库往返放大 N 倍；应改为 IN 批量查询后"
    "内存分组，并先为全部 id 初始化空列表以保留无记录用户。占位符数量必须与 ids 长度一致（写死单个 ? 会把整个列表当成"
    "一个绑定值，驱动层直接报错或只匹配首项），动态拼接的只能是常量占位符。",
    _R_PL,
),
]
_DSEC_REFS: list[CodeRef] = [
make_code_ref(
    SERIES_DSEC, "AI-03", "AI 代码硬编码密钥", "P0",
    'API_KEY = "sk-proj-4tGx9mQzL2vNb7YhRdKe"\n'
    '\n'
    'def call_llm(prompt):\n'
    '    """调用模型。"""\n'
    '    return client.post(API_KEY, prompt)\n',
    'import os\n'
    '\n'
    'def call_llm(prompt):\n'
    '    """调用模型（密钥走环境变量）。"""\n'
    '    api_key = os.environ.get("LLM_API_KEY", "")\n'
    '    return client.post(api_key, prompt)\n',
    "AI 生成代码常把示例密钥直接写进源码（sk-xxx/AKID 等），入库即泄露；"
    "密钥必须经环境变量/Secret Manager 注入，禁止任何字面量密钥。",
    _R_SEC,
),
make_code_ref(
    SERIES_DSEC, "IA-03", "空壳函数（签名存在但无实现）", "P2",
    'def detect_all(code, detectors):\n'
    '    pass\n',
    'def detect_all(code, detectors):\n'
    '    """全量检测。"""\n'
    '    findings = []\n'
    '    for detector in detectors:\n'
    '        findings.extend(detector(code))\n'
    '    return findings\n',
    "函数体为空/仅 pass/仅返回空值是接口空壳——签名存在但永远不做功，"
    "调用方以为检测已跑实则全绿（空壳实现回归教训）；接口实现必须"
    "有实质逻辑。",
    _R_SEC,
),
make_code_ref(
    SERIES_DSEC, "SE-04", "不安全反序列化 pickle.loads", "P1",
    'import pickle\n'
    '\n'
    'def load_state(path):\n'
    '    """加载状态。"""\n'
    '    with open(path, "rb") as fh:\n'
    '        return pickle.load(fh)\n',
    'import json\n'
    '\n'
    'def load_state(path):\n'
    '    """加载状态（JSON 安全反序列化）。"""\n'
    '    with open(path, "r", encoding="utf-8") as fh:\n'
    '        return json.load(fh)\n',
    "pickle.load/loads 反序列化不可信数据可执行任意代码（RCE）；持久化"
    "交换应使用 JSON 等数据格式，pickle 仅限可信内部快照。",
    _R_SE,
),
make_code_ref(
    SERIES_DSEC, "SE-02", "命令注入 os.system/os.popen", "P0",
    'import os\n'
    '\n'
    'def deploy(path):\n'
    '    """部署（拼接命令恒经 shell 解释）。"""\n'
    '    os.system("tar czf backup.tar.gz " + path)\n',
    'import subprocess\n'
    '\n'
    'def deploy(path):\n'
    '    """部署（参数化列表，不经 shell 解释）。"""\n'
    '    subprocess.run(["tar", "czf", "backup.tar.gz", path], check=True, timeout=30)\n',
    "os.system/os.popen 恒经 shell 解释，拼接外部输入即命令注入（CWE-78）；"
    "应改用 subprocess 参数化列表（默认 shell=False），命令名与参数"
    "分离，从源头消除注入面。",
    _R_SE_STATIC,
    self_verifiable=False,
),
make_code_ref(
    SERIES_DSEC, "SE-03", "硬编码密钥/密码/Token", "P1",
    'def connect(service):\n'
    '    """连接服务（字面量密钥）。"""\n'
    '    password = "P@ssw0rd-2026"\n'
    '    return login(service, password)\n',
    'import os\n'
    '\n'
    'def login(service, password):\n'
    '    """登录服务。"""\n'
    '    return bool(service and password)\n'
    '\n'
    'def connect(service):\n'
    '    """连接服务（凭据走环境变量）。"""\n'
    '    password = os.environ.get("SERVICE_PASSWORD", "")\n'
    '    return login(service, password)\n',
    "敏感名（password/api_key/token 等）被赋字符串字面量即硬编码凭据，"
    "入库即泄露（CWE-798）；凭据必须经环境变量/Secret Manager 注入，"
    "与 AI-03 检测锚点互补（AI03 检 AI 代码形态，SE-03 检全域形态）。",
    _R_SE_STATIC,
    self_verifiable=False,
),
make_code_ref(
    SERIES_DSEC, "SN-03", "关键操作沉默吞错", "P2",
    'import os\n'
    '\n'
    'def save_report(path, data):\n'
    '    """保存报告。"""\n'
    '    try:\n'
    '        write_report(path, data)\n'
    '    except OSError:\n'
    '        pass\n',
    'import logging\n'
    '\n'
    'def write_report(path, data):\n'
    '    """写报告。"""\n'
    '    return len(data)\n'
    '\n'
    'def save_report(path, data):\n'
    '    """保存报告（失败记日志不吞错）。"""\n'
    '    try:\n'
    '        write_report(path, data)\n'
    '    except OSError as exc:\n'
    '        logging.getLogger(__name__).warning(\n'
    '            "save_report failed: %s (%s)", path, exc)\n'
    '        raise\n',
    "关键操作（删除/写盘/提交）的异常被 except: pass 静默吞掉，失败无从"
    "追溯、状态与真实世界脱节；至少记 warning 级日志并保留上下文。",
    _R_SEC,
),
make_code_ref(
    SERIES_DSEC, "SN-05", "debug 级日志吞错", "P2",
    'import logging\n'
    '\n'
    '_LOG = logging.getLogger(__name__)\n'
    '\n'
    'def save_result(data, path):\n'
    '    """保存结果。"""\n'
    '    try:\n'
    '        write_json(path, data)\n'
    '    except Exception as exc:\n'
    '        _LOG.debug("save failed: %s", exc)\n',
    'import logging\n'
    '\n'
    'def write_json(path, data):\n'
    '    """写 JSON。"""\n'
    '    return len(data)\n'
    '\n'
    '_LOG = logging.getLogger(__name__)\n'
    '\n'
    'def save_result(data, path):\n'
    '    """保存结果（失败显式告警并上抛）。"""\n'
    '    try:\n'
    '        write_json(path, data)\n'
    '    except OSError:\n'
    '        _LOG.warning("save_result failed: %s", path, exc_info=True)\n'
    '        raise\n',
    "except 块仅有 debug 日志而无任何恢复逻辑等于沉默吞错（debug 默认不"
    "输出）；异常应 warning 以上并做实质处理或显式上抛。",
    _R_SEC,
),
make_code_ref(
    SERIES_DSEC, "IF-01", "隐式流侧信道泄露", "P2",
    'def check_password(real, guess):\n'
    '    """校验口令（隐式流泄露长度信息）。"""\n'
    '    if len(real) != len(guess):\n'
    '        return False\n'
    '    for a, b in zip(real, guess):\n'
    '        if a != b:\n'
    '            return False\n'
    '    return True\n',
    'import hmac\n'
    '\n'
    'def check_password(real, guess):\n'
    '    """校验口令（UTF-8 字节常数时间比较）。"""\n'
    '    real_bytes = real.encode("utf-8")\n'
    '    guess_bytes = guess.encode("utf-8")\n'
    '    return hmac.compare_digest(real_bytes, guess_bytes)\n',
    "敏感数据的比较/分支模式（长度分支、逐位提前返回）会经隐式控制流泄露"
    "秘密属性（长度/前缀），构成侧信道；敏感比较必须用常数时间 API"
    "（hmac.compare_digest）；str 须先 UTF-8 编码，直接传非 ASCII str 会 TypeError。",
    _R_IF,
    self_verifiable=False,
),
make_code_ref(
    SERIES_DSEC, "PL-02", "assert 用作安全检查", "P1",
    'def authorize(user, action):\n'
    '    """鉴权。"""\n'
    '    assert user.has_permission(action)\n'
    '    return perform(action)\n',
    'def perform(action):\n'
    '    """执行动作。"""\n'
    '    return action\n'
    '\n'
    'def authorize(user, action):\n'
    '    """鉴权（显式拒绝）。"""\n'
    '    if not user.has_permission(action):\n'
    '        raise PermissionError(f"{user} cannot {action}")\n'
    '    return perform(action)\n',
    "安全检查写在 assert 里时，生产 -O 模式直接剔除全部鉴权逻辑；权限"
    "校验必须用 if + 显式异常，禁止 assert。",
    _R_PL,
),
make_code_ref(
    SERIES_DSEC, "PL-03", "global 声明非纯常量", "P2",
    'counter = 0\n'
    '\n'
    'def hit():\n'
    '    """计数。"""\n'
    '    global counter\n'
    '    counter += 1\n'
    '    return counter\n',
    'class Counter:\n'
    '    """显式计数器（无隐式全局可变状态）。"""\n'
    '    def __init__(self):\n'
    '        self.value = 0\n'
    '\n'
    '    def hit(self):\n'
    '        self.value += 1\n'
    '        return self.value\n',
    "函数内 global 声明修改模块级变量造成隐式跨函数耦合，并发下竞态且"
    "测试无法隔离（pytest 全局状态污染教训）；可变状态应封装为实例/显式"
    "传参。",
    _R_PL,
),
]
_DTRAP_REFS: list[CodeRef] = [
make_code_ref(
    SERIES_DTRAP, "PL-01", "闭包晚绑定陷阱", "P2",
    'def make_handlers():\n'
    '    """构造一批回调。"""\n'
    '    handlers = []\n'
    '    for i in range(3):\n'
    '        handlers.append(lambda: i)\n'
    '    return handlers\n',
    'def make_handlers():\n'
    '    """构造一批回调（默认参数捕获当前值）。"""\n'
    '    handlers = []\n'
    '    for i in range(3):\n'
    '        handlers.append(lambda i=i: i)\n'
    '    return handlers\n',
    "循环内 lambda/闭包捕获的是变量引用而非快照，循环结束后全部读到同一"
    "终值（晚绑定）；需用默认参数 i=i 或 functools.partial 固化当前值。",
    _R_PL,
),
make_code_ref(
    SERIES_DTRAP, "SL-05", "拆分残留导入（符号不存在）", "P0",
    '# 单体拆分后：from old_mod import helper_func\n'
    '# 但 helper_func 已迁移到 new_mod，old_mod 中不存在\n'
    'from old_mod import helper_func\n',
    '# 拆分后同步更新导入，指向符号真实所在模块\n'
    'from new_mod import helper_func\n'
    '\n'
    'value = helper_func("x")\n',
    "from X import Y 但 Y 不在 X 中（单体拆分后函数迁移、导入未更新），"
    "导入即 ImportError，代码完全无法运行（P0）；拆分迁移后必须逐条核对"
    "导入符号真实存在（跨模块级检测，仅注入引导）。",
    _R_SPLIT,
    self_verifiable=False,
),
make_code_ref(
    SERIES_DTRAP, "XR01", "跨模块符号引用幻觉", "P1",
    'from collections import definitely_missing_symbol  # 不存在的符号\n',
    'from collections import defaultdict  # 已核实存在的符号\n'
    '\n'
    'counts = defaultdict(int)\n',
    "from X import Y / X.Y() 引用的符号在目标模块中不存在，是 AI 代码"
    "幻觉最高频的断裂形态（凭记忆拼 API 名）；写码前必须 preflight_api_check"
    "或 importlib 核实符号真实存在（跨模块级检测，仅注入引导）。",
    _R_XR,
    self_verifiable=False,
),
]
_EXT_SERIES_REF_GROUPS: tuple[tuple[str, list[CodeRef]], ...] = (
    (SERIES_SECURITY, SECURITY_REFS),
    (SERIES_ASYNCIO, ASYNCIO_REFS),
    (_SERIES_PYTRAP, _PYTRAP_REFS),
    (_SERIES_BUG, _BUG_REFS),
    (_SERIES_TESTQUALITY, _TESTQUALITY_REFS),
    (_SERIES_FILEOPS, _FILEOPS_REFS),
    (_SERIES_IMPORTEXTRA, _IMPORTEXTRA_REFS),
    (SERIES_PERF, PERF_REFS),
    (SERIES_ROBUST_EXTRA, ROBUST_EXTRA_REFS),
    (SERIES_DEPRECATED_EXT, _DEPRECATED_EXT_REFS),
    (SERIES_DSEC, _DSEC_REFS),
    (SERIES_DQUALITY, _DQUALITY_REFS),
    (SERIES_DPERF, _DPERF_REFS),
    (SERIES_DTRAP, _DTRAP_REFS),
)
def _flatten_series_ref_groups(
        groups: tuple[tuple[str, list[CodeRef]], ...]) -> list[CodeRef]:
    refs: list[CodeRef] = []
    for series, group in groups:
        for ref in group:
            if ref.series != series:
                raise ValueError(
                    f"系列分组错配: {ref.rule_id} 的 series={ref.series!r}，"
                    f"却挂在 {series!r} 分组下")
            refs.append(ref)
    return refs
def _validate_series_labels(
        entries: list[CodeRef], allowed: frozenset[str],
        registry_name: str) -> None:
    drift = sorted(
        (ref.rule_id, ref.series) for ref in entries
        if ref.series not in allowed)
    if drift:
        raise ValueError(
            f"{registry_name} 系列标签漂移: {drift[:5]}；允许集合 "
            f"{sorted(allowed)}；include_series 按标签精确匹配，"
            "漂移条目会在注入时静默丢失")
EXT_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    _flatten_series_ref_groups(_EXT_SERIES_REF_GROUPS),
    "EXT_CODE_REFS",
)
register_code_refs(EXT_CODE_REFS, "prevention_ext_refs")
AICODER_CODE_REFS_VERSION = '1.1.4'
_GATE_TRAPS = (anchor_module('diag_traps_async') + ' / ' + anchor_module('diag_traps_blocking') + ' / ' + anchor_module('diag_traps_coding') + ' / ' + anchor_module('diag_traps_binding') + ' / ' + anchor_module('diag_traps_guard') + ' (Gate5 注册表 + B1 逐文件管线)')
_HOST_RECOVERED_EXPR = (anchor_module('diag_rules_expr_forms') + ' (Gate5 注册表 + B1 逐文件管线)')
_HOST_RECOVERED_GUARD = (anchor_module('diag_rules_numeric_guard') + ' (Gate5 注册表 + B1 逐文件管线)')
_HOST_RECOVERED_RUNTIME_OBJECTS = (
    anchor_module('diag_runtime_objects') + ' (Gate5 注册表 + B1 逐文件管线)')
_GATE_XV = (anchor_module('xv_rule_checks') + ' / ' + anchor_module('diag_types_vocab.CV_RULES') + ' (CV 交叉验证)')
_AICODER_ENTRIES: list[CodeRef] = [
    make_code_ref(
        SERIES_ASYNCIO, 'LK-03', '锁临界区内执行耗时阻塞调用', 'P1',
        (
            'import threading\n'
            'import requests\n'
            '\n'
            '_lock = threading.Lock()\n'
            '_cache = {}\n'
            '\n'
            'def refresh(key):\n'
            '    with _lock:\n'
            '        r = requests.get(key)\n'
            '        _cache[key] = r.json()\n'
        ),
        (
            'import threading\n'
            'import requests\n'
            '\n'
            '_lock = threading.Lock()\n'
            '_cache = {}\n'
            '_versions = {}\n'
            '\n'
            'def refresh(key):\n'
            '    # 在锁内登记本次刷新世代，耗时 IO 全部移出临界区\n'
            '    with _lock:\n'
            '        version = _versions.get(key, 0) + 1\n'
            '        _versions[key] = version\n'
            '    r = requests.get(\n'
            '        key,\n'
            '        headers={"User-Agent": "example-client/1.0"},\n'
            '        timeout=(3.05, 30),\n'
            '    )\n'
            '    payload = r.json()\n'
            '    # 仅最新世代可写回；失效或后续刷新都会使旧响应作废\n'
            '    with _lock:\n'
            '        if _versions.get(key) == version:\n'
            '            _cache[key] = payload\n'
            '\n'
            'def invalidate(key):\n'
            '    with _lock:\n'
            '        _versions[key] = _versions.get(key, 0) + 1\n'
            '        _cache.pop(key, None)\n'
        ),
        (
            '阻塞调用持锁等待期间其余线程全部停在锁上，并发度塌缩为'
            '串行，一次网络抖动放大为全局停顿（缓存刷新/心跳场景高发）。'
            '锁内只做内存操作，耗时 IO 移出临界区；同时使用逐键版本号'
            '阻止在途旧响应覆盖已失效或更新的结果。'
        ),
        _GATE_TRAPS + ' check_LK03',
    ),
    make_code_ref(
        _SERIES_PYTRAP, 'FL-01', '非精确浮点字面量参与 ==/!= 比较', 'P2',
        (
            'def is_target(value):\n'
            '    return value == 0.1 or value != 0.3\n'
        ),
        (
            'import math\n'
            '\n'
            'def is_target(value):\n'
            '    # 非精确浮点用容差比较；!= 对应 not isclose，不能反转语义。\n'
            '    return (math.isclose(value, 0.1, rel_tol=1e-9)\n'
            '            or not math.isclose(value, 0.3, rel_tol=1e-9))\n'
        ),
        (
            '0.1/0.3 等十进制值在二进制浮点中是无限循环小数的近似表示，'
            '== 比较的是舍入后的位模式而非数学相等——条件会意外命中或'
            '永不命中（0.1 + 0.2 == 0.3 为 False）。用 math.isclose 容差'
            '比较；金额场景用 decimal.Decimal。'
        ),
        _HOST_RECOVERED_EXPR + ' check_FL01',
    ),
    make_code_ref(
        _SERIES_PYTRAP, 'TY-03', '字符串与非 str 操作数直接拼接', 'P1',
        (
            'def label(user_id, items):\n'
            '    return f"user-{user_id} count: " + len(items)\n'
        ),
        (
            'def label(user_id, items):\n'
            '    # f-string 自动调用 __format__，非 str 操作数安全转换；\n'
            '    # 拼接符 + 场景须显式 str(value)\n'
            '    return f"user-{user_id} count: {len(items)}"\n'
        ),
        (
            '+ 不做隐式类型转换，str 与 int/float/bool 相加直接抛 TypeError。'
            'str + 变量名形态（如 "user-" + user_id）静态不可判定，拼接前'
            '统一显式转换或改用 f-string，从源头消灭运行时崩溃。'
        ),
        _HOST_RECOVERED_EXPR + ' check_TY03',
    ),
    make_code_ref(
        SERIES_ROBUST_EXTRA, 'TP-26', '重试循环内网络调用无退避间隔', 'P2',
        (
            'import requests\n'
            '\n'
            'def fetch_retry(url):\n'
            '    for _ in range(3):\n'
            '        try:\n'
            '            return requests.get(url)\n'
            '        except requests.RequestException:\n'
            '            continue\n'
            '    return None\n'
        ),
        (
            'import random\n'
            'import time\n'
            '\n'
            'import requests\n'
            '\n'
            'def fetch_retry(url):\n'
            '    # 会话在循环外创建，复用连接并明确请求头。\n'
            '    with requests.Session() as session:\n'
            '        session.headers.update({"User-Agent": "example-client/1.0"})\n'
            '        for attempt in range(3):\n'
            '            try:\n'
            '                return session.get(url, timeout=(3.05, 30))\n'
            '            except requests.RequestException:\n'
            '                if attempt == 2:\n'
            '                    break\n'
            '                # 指数退避 + 抖动：随机化打散同时重试的流量峰值\n'
            '                backoff = min(2 ** attempt, 8)\n'
            '                time.sleep(backoff + random.uniform(0, backoff * 0.5))\n'
            '    return None\n'
        ),
        (
            '对端过载或熔断时立即重试会放大流量（重试风暴）——3 次重试'
            '瞬间打满下游剩余容量，还拖垮自身线程池。except 分支必须带'
            '退避等待（指数退避 + jitter），并配 max_retries 上限。'
        ),
        _GATE_TRAPS + ' check_TP26',
    ),
    make_code_ref(
        SERIES_ROBUST_EXTRA, 'JS-01', 'json 结果未做形状防御直接按 dict 使用', 'P1',
        (
            'import json\n'
            '\n'
            'def load_row(line):\n'
            '    row = json.loads(line)\n'
            '    return row.get("name", "")\n'
        ),
        (
            'import json\n'
            '\n'
            'def load_row(line, bad_counter=None):\n'
            '    try:\n'
            '        row = json.loads(line)\n'
            '    except ValueError:\n'
            '        if bad_counter is not None:\n'
            '            bad_counter[0] += 1\n'
            '        return None\n'
            '    # 形状校验：非 dict 记坏行逐条跳过，禁止整体中断\n'
            '    if not isinstance(row, dict):\n'
            '        if bad_counter is not None:\n'
            '            bad_counter[0] += 1\n'
            '        return None\n'
            '    return row.get("name", "")\n'
        ),
        (
            'json.loads 对任意合法 JSON（标量/数组）都成功返回，返回形态由'
            '输入决定而非由调用方假设决定——loads("123") 合法返回 int，随后的'
            '.get()/["key"] 抛 AttributeError 击穿整条加载链；异常若发生在'
            '落盘前，损坏行永不挤出，陷入永久失效循环（历史审计最重要缺陷'
            '模式）。解析后先 isinstance 形状校验，非 dict 逐条隔离。'
        ),
        _GATE_TRAPS + ' check_JS01',
    ),
    make_code_ref(
        _SERIES_PYTRAP, 'BI-01', 'isinstance 数值判定后参与算术未排除 bool', 'P2',
        (
            'def count_valid(values):\n'
            '    n = 0\n'
            '    for v in values:\n'
            '        if isinstance(v, (int, float)):\n'
            '            n += v if v > 0 else 1\n'
            '    return n\n'
        ),
        (
            'def count_valid(values):\n'
            '    n = 0\n'
            '    for v in values:\n'
            '        # bool 是 int 子类，参与统计前必须显式排除\n'
            '        if isinstance(v, (int, float)) and not isinstance(v, bool):\n'
            '            n += v if v > 0 else 1\n'
            '    return n\n'
        ),
        (
            'bool 是 int 子类（isinstance(True, int) 为真），True/False 混入'
            '后统计/覆盖率/置信度被悄悄污染：本例 True 按 1 累加，False 也'
            '会走 else 分支加 1，两个布尔值都会被误计为有效样本（历史案例：'
            '覆盖率统计把布尔成功标记算成 1 次有效样本）。参与算术前必须 '
            'isinstance(x, bool) 排除。'
        ),
        _HOST_RECOVERED_GUARD + ' check_BI01',
    ),
    make_code_ref(
        SERIES_ASYNCIO, 'TP-27', 'with 线程池内依赖超时参数控制整体时长', 'P2',
        (
            'from concurrent.futures import ThreadPoolExecutor, as_completed\n'
            '\n'
            'def run_all(jobs):\n'
            '    with ThreadPoolExecutor(max_workers=4) as ex:\n'
            '        futs = [ex.submit(j) for j in jobs]\n'
            '        for f in as_completed(futs, timeout=30):\n'
            '            f.result()\n'
        ),
        (
            'from concurrent.futures import ThreadPoolExecutor, as_completed\n'
            '\n'
            'def run_all(jobs):\n'
            '    ex = ThreadPoolExecutor(max_workers=4)\n'
            '    try:\n'
            '        futs = [ex.submit(j) for j in jobs]\n'
            '        for f in as_completed(futs, timeout=30):\n'
            '            f.result()\n'
            '    finally:\n'
            '        # 不等挂死线程：超时后取消未启动任务并立即释放主流程\n'
            '        ex.shutdown(wait=False, cancel_futures=True)\n'
        ),
        (
            'with ThreadPoolExecutor 块退出时执行 shutdown(wait=True)，仍会'
            '无限等待挂死线程——as_completed(timeout=)/result(timeout=) 只让'
            '等待方抛 TimeoutError，线程本身不会被终止，超时后主流程照样卡死'
            '在 with 出口（历史审计教训：with 池超时形同虚设）。改手动生命'
            '周期：finally 中 shutdown(wait=False, cancel_futures=True)。'
        ),
        _GATE_TRAPS + ' check_TP27',
    ),
    make_code_ref(
        _SERIES_PYTRAP, 'NM-01', 'float 判定通过后 int()/round() 无 isfinite 防御', 'P2',
        (
            'def clamp_fp(x):\n'
            '    if isinstance(x, float):\n'
            '        return int(x)   # inf/nan 通过 isinstance 后崩溃\n'
            '    return int(x)\n'
        ),
        (
            'import math\n'
            '\n'
            'def clamp_fp(x, bad_counter=None):\n'
            '    # 仅浮点路径需要有限性检查；其他输入保持原 int() 转换契约\n'
            '    if isinstance(x, float) and not math.isfinite(x):\n'
            '        if bad_counter is not None:\n'
            '            bad_counter[0] += 1\n'
            '        return None\n'
            '    return int(x)\n'
        ),
        (
            'inf/nan 均通过 isinstance(x, float)，int(inf) 抛 OverflowError、'
            'int(nan) 抛 ValueError——发生在循环内时会中断整批合法条目加载'
            '（历史案例：钳制非法数值时未防 inf，整批合法条目被连带丢弃）。类型'
            '检查后必须加 math.isfinite，非有限值逐条跳过并计数。'
        ),
        _HOST_RECOVERED_GUARD + ' check_NM01',
    ),
    make_code_ref(
        _SERIES_PYTRAP, 'DT-01', 'naive 与 aware datetime 相减', 'P2',
        (
            'from datetime import datetime, timezone\n'
            '\n'
            '_started = datetime.now(timezone.utc)\n'
            '\n'
            'def elapsed():\n'
            '    return (datetime.now() - _started).days\n'
        ),
        (
            'from datetime import datetime, timezone\n'
            '\n'
            '_started = datetime.now(timezone.utc)\n'
            '\n'
            'def elapsed():\n'
            '    # 口径统一：全 aware 相减\n'
            '    return (datetime.now(timezone.utc) - _started).days\n'
        ),
        (
            'naive（无时区）与 aware（带时区）datetime 相减/比较抛 TypeError: '
            "can't subtract offset-naive and offset-aware datetimes——同模块"
            '混用 datetime.now() 与 datetime.now(timezone.utc)/astimezone() '
            '结果是 AI 高频缺陷。统一时区口径后再运算，跨口径用 astimezone '
            '归一。'
        ),
        _HOST_RECOVERED_RUNTIME_OBJECTS + ' check_DT01',
    ),
    make_code_ref(
        SERIES_ASYNCIO, 'AB-01', '协程函数内同步阻塞调用', 'P1',
        (
            'import requests\n'
            '\n'
            'async def fetch(url):\n'
            '    return await requests.get(url)   # await 伪异步幻觉\n'
        ),
        (
            'import httpx\n'
            '\n'
            'async def fetch(url):\n'
            '    async with httpx.AsyncClient(timeout=30) as client:\n'
            '        return await client.get(url, timeout=30)\n'
        ),
        (
            '协程内同步阻塞调用期间整个事件循环被卡死，其余协程全部停摆，'
            '并发度塌缩为串行。await 一个同步阻塞调用并不会使其变异步'
            '（AI 幻觉高发形态：await requests.get(url) 直接 TypeError 或'
            '假异步）。time.sleep→asyncio.sleep；requests/urlopen→'
            'httpx.AsyncClient/aiohttp；无法改造的同步 IO 用 '
            'asyncio.to_thread()/run_in_executor 包裹。'
        ),
        _GATE_TRAPS + ' check_AB01',
    ),
    make_code_ref(
        _SERIES_CVMETHOD, 'CV-32', '配置键/常量变更未同步消费方（配置漂移）', 'P2',
        (
            'import json\n'
            '\n'
            'def timeout_of(cfg):\n'
            '    # 配置键已改名 request_timeout，读取处漏改，\n'
            '    # 静默回退默认值——超时策略无声失效\n'
            '    return cfg.get("http_timeout", 30)\n'
        ),
        (
            'import warnings\n'
            '\n'
            'def timeout_of(cfg):\n'
            '    # 新键优先；旧键兼容期内仍生效并告警，避免静默漂移\n'
            '    if "request_timeout" in cfg:\n'
            '        return cfg["request_timeout"]\n'
            '    if "http_timeout" in cfg:\n'
            '        warnings.warn(\n'
            '            "配置键 http_timeout 已更名为 request_timeout，"\n'
            '            "下一版本移除",\n'
            '            DeprecationWarning,\n'
            '            stacklevel=2,\n'
            '        )\n'
            '        return cfg["http_timeout"]\n'
            '    return 30\n'
        ),
        (
            '配置键/常量重命名或改值后，任一读取处/样例/文档漏改即产生'
            '配置漂移：get() 静默回退默认值，行为差异无报错无日志，只能'
            '靠 CV 配置漂移交叉确认（文档一致性 + AST 交叉）事后发现。'
            '变更时全库检索旧键名并同步全部消费方。'
        ),
        _GATE_XV + ' 规则32/51（配置漂移交叉确认）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SERIES_CVMETHOD, 'CV-44', '修改公开函数签名破坏既有调用方', 'P1',
        (
            'def build_report(items, strict, title):\n'
            '    return {"title": title, "rows": list(items)}\n'
        ),
        (
            'def build_report(items, title="", *, strict=False):\n'
            '    # 新参数带默认值，既有调用 build_report(items, title)\n'
            '    # 零破坏；语义变更用关键字参数隔离，不重排位置参数\n'
            '    rows = list(items)\n'
            '    if strict and not rows:\n'
            '        raise ValueError("items must not be empty")\n'
            '    return {"title": title, "rows": rows}\n'
        ),
        (
            '直接增删/重排公开函数的位置参数，所有既有调用方立即 '
            'TypeError（调用面断裂）。新参数一律带默认值；语义变更用'
            'keyword-only 参数隔离；删除旧参数先走一个版本的'
            ' DeprecationWarning 兼容期。CV 规则44（历史 + 回归/兼容'
            '交叉）只能事后发现，兼容设计在编写时完成。'
        ),
        _GATE_XV + ' 规则44（API 向后兼容交叉确认）',
        self_verifiable=False,
    ),
    make_code_ref(
        SERIES_ASYNCIO, 'GM-01', '私有全局可变状态跨函数写无锁', 'P2',
        (
            '_cache = {}\n'
            '\n'
            'def put(k, v):\n'
            '    _cache[k] = v        # 多线程并发写无保护\n'
            '    return len(_cache)\n'
        ),
        (
            'import threading\n'
            '\n'
            '_cache = {}\n'
            '_cache_lock = threading.Lock()\n'
            '\n'
            'def put(k, v):\n'
            '    with _cache_lock:\n'
            '        _cache[k] = v\n'
            '        return len(_cache)\n'
            '\n'
            'def drop(k):\n'
            '    with _cache_lock:\n'
            '        _cache.pop(k, None)\n'
        ),
        (
            '模块级 dict/list/set 被多个函数写入时即为共享可变状态：多线程'
            '并发写触发 RuntimeError（dict changed size during iteration）或'
            '脏读。TP-07 静态检测覆盖公开全局的存量面，下划线私有形态'
            '（如 _cache）有合法缓存用途、静态不可判定，靠编写前预防：跨'
            '函数写的全局容器一律配锁（threading.Lock）或改线程本地/队列。'
        ),
        (anchor_module('diag_traps_guard')
         + ' check_TP07（公开全局存量面）+ prevention-only '
         '方法前移（跨线程判定不可静态化，无逐文件静态检测器）'),
        self_verifiable=False,
    ),
]
_AICODER_ALLOWED_SERIES = frozenset({
    SERIES_ASYNCIO, _SERIES_PYTRAP, SERIES_ROBUST_EXTRA, _SERIES_CVMETHOD,
})
_validate_series_labels(
    _AICODER_ENTRIES, _AICODER_ALLOWED_SERIES, "AICODER_CODE_REFS")
AICODER_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    _AICODER_ENTRIES, "AICODER_CODE_REFS")
register_code_refs(AICODER_CODE_REFS, 'prevention_ext_refs:aicoder')
