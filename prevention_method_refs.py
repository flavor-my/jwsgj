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
    'METH_CODE_REFS',
    'METH_CODE_REFS_VERSION',
]
_log = logging.getLogger(__name__)
_SER_GUARDFIX = 'guardfix'
_SER_ROBUSTFIX = 'robustfix'
_SER_SECFIX = 'secfix'
_SER_RUFFFIX = 'rufffix'
_SER_NORMTEXT = 'normtext'
_SER_CVMETHOD = 'cvmethod'
_SER_DIAGMETHOD = 'diagmethod'
_SER_NETFIX = 'netfix'
METH_CODE_REFS_VERSION = '1.3.2'
_METH_ANCHORED = [
    make_code_ref(
        _SER_ROBUSTFIX, 'RD-05', 'subprocess 调用无超时', 'P1',
        'import subprocess\n\ndef run(cmd):\n    return subprocess.run(cmd).stdout\n',
        'import logging\n'
        'import subprocess\n'
        '\n'
        '_log = logging.getLogger(__name__)\n'
        '\n'
        'def run(cmd):\n'
        '    try:\n'
        '        return subprocess.run(\n'
        '            cmd, capture_output=True, timeout=60\n'
        '        ).stdout\n'
        '    except subprocess.TimeoutExpired:\n'
        '        _log.warning("命令超时（60s），返回空输出: %s", cmd)\n'
        '        return b""\n',
        'subprocess.run/call/check_output 无 timeout 参数时，命令挂起即'
        '永久阻塞调用线程；必须显式设 timeout 并处理 TimeoutExpired',
        anchor_module('diag_traps_blocking') + ' (DetectorRegistry: TO-02 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'SC-01', '命令调用未设超时（SEC 域）', 'P1',
        'import subprocess\n\ndef ping(host):\n    subprocess.call(["ping", "-c", "1", host])\n',
        'import logging\n'
        'import subprocess\n'
        '\n'
        '_log = logging.getLogger(__name__)\n'
        '\n'
        'def ping(host):\n'
        '    try:\n'
        '        return subprocess.call(\n'
        '            ["ping", "-c", "1", host], timeout=10\n'
        '        )\n'
        '    except subprocess.TimeoutExpired:\n'
        '        _log.warning("ping 超时（10s），返回失败码: %s", host)\n'
        '        return -1\n',
        '与 RD-05 同根因：外部命令是天然不可信的阻塞源，无超时等于把'
        '进程生命周期交给外部环境',
        anchor_module('diag_traps_blocking') + ' (DetectorRegistry: TO-02 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_ROBUSTFIX, 'RD-08', 'try/except 嵌套超两层', 'P2',
        'def f():\n    try:\n        try:\n            try:\n                risky()\n            except TypeError:\n                pass\n        except ValueError:\n            pass\n    except KeyError:\n        pass\n',
        'def f():\n    try:\n        return risky()\n    except (TypeError, ValueError, KeyError):\n        return None\n',
        '嵌套 try/except 使异常流向不可读、finally 语义交叉；提取内层'
        '为子函数或合并异常处理，保持单层职责',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: RD-08 互补；嵌套层数无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_ROBUSTFIX, 'RD-15', 'except Exception 过于宽泛', 'P1',
        'def f():\n    try:\n        return int(data)\n    except Exception:\n        return 0\n',
        'def f():\n    try:\n        return int(data)\n    except (ValueError, TypeError):\n        return 0\n',
        'except Exception 不会吞掉 BaseException 子类（KeyboardInterrupt/'
        'SystemExit 仍会穿透），但会把 AttributeError/NameError 等编程'
        '非预期错误与业务异常一并吞掉、掩盖真实缺陷；只捕获预期异常类型',
        anchor_module('diag_wiring_exc') + ' (DetectorRegistry: RF-01 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_ROBUSTFIX, 'D35-SILENT-FALLBACK', '静默降级缺日志与理由', 'P1',
        'def load():\n    try:\n        return read_config()\n    except Exception:\n        return DEFAULT\n',
        'import logging\n\n_LOG = logging.getLogger(__name__)\nDEFAULT: dict = {}\n\n\ndef load():\n    try:\n        return read_config()\n    except OSError as exc:\n        _LOG.warning("配置读取失败，回退默认值: %s", exc)\n        return DEFAULT\n',
        '回退路径若不留下告警与理由，故障被静默吸收，排障时无迹可循；'
        '降级必须可观测',
        anchor_module('diag_wiring_exc') + ' (DetectorRegistry: RF-01 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_ROBUSTFIX, 'DB-01', 'SQLite 连接异常路径未关闭', 'P1',
        'import sqlite3\n\ndef query(sql):\n    conn = sqlite3.connect("db.sqlite")\n    return conn.execute(sql).fetchall()\n',
        'import sqlite3\n\n\ndef query(sql):\n    conn = sqlite3.connect("db.sqlite")\n    try:\n        return conn.execute(sql).fetchall()\n    finally:\n        conn.close()\n',
        '连接对象在异常路径泄漏后达到连接上限，后续请求全部失败；'
        'sqlite3 的 with 语句只提交/回滚事务、不关闭连接（Python '
        '官方语义，与 diag_guard_sql_statement RD-30 事务口径一致），关闭必须 '
        'finally 显式 close 或 contextlib.closing 包装',
        anchor_module('diag_guard_sql_connection') + ' (DetectorRegistry: DB-06 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'LG-01', '通配符导入', 'P2',
        'from os.path import *\n\n\ndef p(x):\n    return join(x, "f")\n',
        'from os.path import join\n\n\ndef p(x):\n    return join(x, "f")\n',
        'import * 污染命名空间、遮蔽内置名且静态不可分析；显式列出'
        '所用名称（B19/G28 同源）',
        anchor_module('diag_gate_arch') + ' (DetectorRegistry: D49 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'NC-01', 'None 比较用 ==', 'P2',
        'def check(v):\n    if v == None:\n        return True\n    return False\n',
        'def check(v):\n    if v is None:\n        return True\n    return False\n',
        '== 走 __eq__ 运算符重载，自定义对象可能返回非布尔或误判；'
        'None 单例比较必须用 is/is not（PEP 8）',
        anchor_module('diag_rules_expr_forms') + ' (DetectorRegistry: NT-01 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GL-01', '模块级可变全局变量', 'P1',
        'CACHE = {}\n\n\ndef put(k, v):\n    CACHE[k] = v\n',
        'class _Cache:\n    """进程内键值缓存（线程安全由调用方保证）。"""\n\n    def __init__(self):\n        self._data = {}\n\n    def put(self, k, v):\n        self._data[k] = v\n\n\ndef build_cache():\n    # 实例由调用方持有与注入, 不在模块层共享状态\n    return _Cache()\n',
        '模块级可变全局破坏测试隔离且引入并发竞态；用类实例或不可变'
        '结构封装状态',
        anchor_module('diag_traps_guard') + ' (DetectorRegistry: TP-07 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'MDA-01', '可变默认参数', 'P1',
        'def append(item, bucket=[]):\n    bucket.append(item)\n    return bucket\n',
        'def append(item, bucket=None):\n    if bucket is None:\n        bucket = []\n    bucket.append(item)\n    return bucket\n',
        '默认可变对象在函数定义时创建一次，跨调用共享导致状态串扰'
        '（与 B01 同根因，知识库键独立）',
        anchor_module('diag_gate_class') + ' (gate_adapter_bindings: RB-01 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-09', '使用模块但未导入', 'P0',
        'def dump(obj):\n    return json.dumps(obj, default=str)\n',
        'import json\n\n\ndef dump(obj):\n    return json.dumps(obj, default=str)\n',
        '未导入即用在运行时必现 NameError（关键基础模块 os/sys/re/json/'  # jwsgj:suppress 供应链安全-敏感路径 — 基础模块清单文本，非路径访问
        'logging 缺失时崩溃面最大）；写盘前核对 import 完整性',
        anchor_module('diag_wiring_imports') + ' (DetectorRegistry: IM-01 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'CM-01', 'open 未用 with 语句', 'P1',
        'def read(path):\n    fp = open(path, encoding="utf-8")\n    data = fp.read()\n    return data\n',
        'def read(path):\n    with open(path, encoding="utf-8") as fp:\n        return fp.read()\n',
        '不经 with 的文件对象依赖 GC 回收关闭，CPython 外解释器或'
        '异常路径都会泄漏句柄（句柄泄漏与编码缺失是两个独立规则：'
        '示例已带 encoding，本条只论 with/close，编码由 IO-05 单独覆盖）',
        anchor_module('diag_gate_io_control') + ' (DetectorRegistry: RB-03 承接，别名锚定；IO-05 独立覆盖 open 缺 encoding)',
    ),
    make_code_ref(
        _SER_SECFIX, 'B101', '生产代码 assert 做校验', 'P3',
        'def withdraw(amount):\n    assert amount > 0\n    return balance - amount\n',
        'def withdraw(amount):\n    if amount <= 0:\n        raise ValueError("amount must be positive")\n    return balance - amount\n',
        'python -O 会剔除 assert，生产环境校验静默失效；业务校验一律'
        '显式 if-raise（测试文件例外）',
        anchor_module('diag_traps_coding') + ' (DetectorRegistry: AS-07 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'BANDIT-B101', 'bandit B101 同源：assert 校验', 'P3',
        'def process(data):\n    assert data\n    return data.strip()\n',
        'def process(data):\n    if not data:\n        raise ValueError("data required")\n    return data.strip()\n',
        '与 B101 同一条外部规则（bandit B101）的知识键；-O 优化后'
        'assert 全部蒸发，输入校验必须用异常',
        anchor_module('diag_traps_coding') + ' (DetectorRegistry: AS-07 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'SEC-02', 'SQL 拼接注入', 'P0',
        'import sqlite3\n\n\ndef user(uid):\n    conn = sqlite3.connect("app.db")\n    return conn.execute("select * from users where id=" + uid).fetchall()\n',
        'import sqlite3\n\n\ndef user(uid):\n    conn = sqlite3.connect("app.db")\n    try:\n        return conn.execute(\n            "select * from users where id=?", (uid,)\n        ).fetchall()\n    finally:\n        conn.close()\n',
        '字符串拼接 SQL 让任意输入成为可执行语句；一律参数化查询'
        '（占位符 + 参数元组）',
        anchor_module('diag_symbol_integrity') + ' (RD-28 承接，detect_all 编排通道，防 B1 双跑不注册表，非注册表通道无法标准自证，走专项直调锚定)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_SECFIX, 'SEC-03', '硬编码凭据', 'P0',
        'API_KEY = "sk-abcdef1234567890abcdef"\n\n\ndef call():\n    return use(API_KEY)\n',
        'import os\n\n\ndef _required_env(name):\n'
        '    value = os.environ.get(name)\n'
        '    if not value:\n'
        '        raise ValueError(f"{name} must be set and non-empty")\n'
        '    return value\n\n\nAPI_KEY = _required_env("MY_API_KEY")\n'
        '\n\ndef call():\n    return use(API_KEY)\n',
        '明文凭据进源码即永久泄漏（git 历史/日志/异常栈带出）；'
        '经环境变量或密钥管理器注入，缺失/空值显式失败（CF-02 同源补条）',
        anchor_module('diag_traps_payload') + ' (DetectorRegistry: CF-02 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'hardcoded_credential', '硬编码凭据（检测器名键）', 'P0',
        'password = "SuperSecret123"\n\n\ndef auth():\n    return check(password)\n',
        'import os\n\n\ndef _required_env(name):\n'
        '    value = os.environ.get(name)\n'
        '    if not value:\n'
        '        raise ValueError(f"{name} must be set and non-empty")\n'
        '    return value\n\n\npassword = _required_env("APP_PASSWORD")\n'
        '\n\ndef auth():\n    return check(password)\n',
        '以检测器名作为知识键的硬编码凭据条目：明文 password/secret/'
        'API Key 赋值一律改环境变量引用并校验必填，禁止空兜底',
        anchor_module('diag_traps_payload') + ' (DetectorRegistry: CF-02 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'SEC-04', '弱加密算法', 'P1',
        'import hashlib\n\n\ndef digest(text):\n    algo = hashlib.md5(text.encode())\n    return algo.hexdigest()\n',
        'import hashlib\n\n\ndef digest(text):\n    return hashlib.sha256(text.encode()).hexdigest()\n',
        'MD5/SHA1 已被证实可碰撞，用于签名/校验即是漏洞；升级 SHA-256'
        '以上或 AES-GCM（SE-10 同域补条）',
        anchor_module('diag_se_data') + ' (DetectorRegistry: SE-10 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'SEC-05', '安全场景弱随机数', 'P1',
        'import random\n\n\ndef make_token():\n    return str(random.randint(100000, 999999))\n',
        'import secrets\n\n\ndef make_token():\n    return str(secrets.randbelow(900000) + 100000)\n',
        'random 模块可预测，token/口令/nonce 属安全场景必须用 secrets'
        '（CSPRNG）',
        anchor_module('diag_se_stdlib') + ' (DetectorRegistry: SE-11 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_SECFIX, 'SEC-06', '路径拼接无边界校验', 'P1',
        'import os\n\n\ndef read(base):\n    name = input("file name: ")\n    return open(os.path.join(base, name)).read()\n',
        'import os\n\n\ndef read(base, name):\n    if "/" in name or "\\\\" in name or ".." in name:\n        raise ValueError("非法路径片段")\n    base_dir = os.path.realpath(base)\n    path = os.path.realpath(os.path.join(base_dir, name))\n    if os.path.commonpath((base_dir, path)) != base_dir:\n        raise ValueError("path traversal")\n    with open(path, encoding="utf-8") as fp:\n        return fp.read()\n',
        '不可信输入拼路径可携带 ../ 穿越 sandbox（OWASP A01）；'  # jwsgj:suppress SS-02 — 缺陷示例代码文本，非执行面
        '先做分隔符与 .. 片段白名单校验，规范化后与基目录比对边界',
        anchor_module('diag_se_injection') + ' (DetectorRegistry: PT-01 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-F811', '重定义覆盖', 'P0',
        'def load():\n    return 1\n\n\ndef load():\n    return 2\n',
        'def load():\n    return 2\n',
        '后定义静默覆盖前定义，调用方拿到非预期实现；删除冗余定义'
        '或更名（DC-03 承接）',
        anchor_module('diag_gate_io_control') + ' (DetectorRegistry: DC-03 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-B023', '循环变量闭包延迟绑定', 'P2',
        'def build():\n    fns = []\n    for i in range(3):\n        fns.append(lambda: i)\n    return [fn() for fn in fns]\n',
        'def build():\n    fns = []\n    for i in range(3):\n        fns.append(lambda i=i: i)\n    return [fn() for fn in fns]\n',
        '闭包捕获变量名而非值，循环结束后全部读到末值；默认参数'
        '快照绑定（B11 同根因，BUG-018 承接）',
        anchor_module('diag_pattern_rules') + ' (DetectorRegistry: PL-01 承接，BUG-018 别名锚定)',
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-UP006', '废弃泛型注解', 'P3',
        'from typing import List, Dict\n\n\ndef make() -> List[Dict[str, int]]:\n    return [{}]\n',
        'def make() -> list[dict[str, int]]:\n    return [{}]\n',
        'typing.List/Dict 是历史兼容层；Py3.9+ 直接内建泛型'
        '（DP-04 承接）',
        anchor_module('diag_rules_api_risk') + ' (DetectorRegistry: DP-04 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-UP045', '废弃 Optional 注解', 'P2',
        'from typing import Optional\n\n\ndef get(k: Optional[str] = None) -> Optional[int]:\n'
        '    if k is None:\n'
        '        return None\n'
        '    return len(k)\n',
        'def get(k: str | None = None) -> int | None:\n'
        '    if k is None:\n'
        '        return None\n'
        '    return len(k)\n',
        'Optional[X] 是 Union 旧写法；Py3.10+ 用 X | None 更简洁'
        '（DP-06 承接）',
        anchor_module('diag_rules_api_risk') + ' (DetectorRegistry: DP-06 承接，别名锚定)',
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-PLW0211', '静态方法带 self 参数', 'P2',
        'class Parser:\n    @staticmethod\n    def parse(self, text):\n        return text.split()\n',
        'class Parser:\n    @staticmethod\n    def parse(text):\n        return text.split()\n',
        'staticmethod 不隐式绑定实例，第一参数只是普通实参；命名 self '
        '会误导调用方和维护者按实例方法理解，应按实际参数语义命名'
        '（CL-01 上下文敏感，不稳触发，降级注入）',
        anchor_module('diag_runtime_objects') + ' (DetectorRegistry: CL-01 上下文敏感)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'RB-14', '推导式中调用副作用函数', 'P2',
        'def fanout(tasks, sink):\n    return [sink.append(t) for t in tasks]\n',
        'def fanout(tasks, sink):\n'
        '    results = []\n'
        '    for t in tasks:\n'
        '        results.append(sink.append(t))\n'
        '    return results\n',
        '推导式语义是"构造新序列"，混入 append/dispatch 等副作用使'
        '意图模糊且难做惰性改造；副作用用显式 for',
        anchor_module('diag_rules_expr_forms.check_RB14') + ' (Gate5 注册表 RB-14；覆盖 append/print/write 等已知副作用名，自定义副作用函数由编写前文本注入兜底)',
    ),
    make_code_ref(
        _SER_GUARDFIX, 'RC-01', '__del__ 中访问外部资源', 'P2',
        'import sqlite3\n\n\nclass Repo:\n    def __del__(self):\n        conn = sqlite3.connect("db.sqlite")\n        conn.close()\n',
        'import sqlite3\n\n\nclass Repo:\n    def __init__(self, path):\n        self._conn = sqlite3.connect(path)\n\n    def close(self):\n        self._conn.close()\n\n    def __enter__(self):\n        return self\n\n    def __exit__(self, *exc):\n        self.close()\n',
        '__del__ 调用时机不确定且解释器关闭期资源可能已失效；用'
        '上下文管理器或显式 close 管理生命周期',
        anchor_module('diag_rules_expr_forms.check_RC01') + ' (Gate5 注册表 RC-01；诊断侧与编写前双通道)',
    ),
    make_code_ref(
        _SER_ROBUSTFIX, 'WC-01', 'finally 块中 raise 吞异常', 'P2',
        'def cleanup(res):\n    try:\n        return res.use()\n    finally:\n        raise RuntimeError("cleanup failed")\n',
        'def cleanup(res):\n    try:\n        return res.use()\n    finally:\n        res.close()\n',
        'finally 内 raise 会替换并吞掉原异常，故障根因丢失；清理动作'
        '放 finally，错误上报放 except',
        anchor_module('diag_wiring_exc_flow.check_WC01') + ' (Gate5 注册表 WC-01；pylint W0133 同源)',
    ),
]
_METH_METHODS = [
    make_code_ref(
        _SER_CVMETHOD, 'CV-M1', '多源仲裁：修复前双源确认', 'P1',
        '# 修复依据单一工具输出，直接改码\n# ruff 报 F841 -> 直接删变量\n',
        '# 修复前至少两源交叉：\n#   源A lint 报未使用变量\n#   源B grep 调用点确认无字符串/反射引用\n# 两源一致 -> 修复；冲突 -> 标记 uncertain 升级人工\n',
        '交叉验证 63 规则核心条款：单一来源结论置信度不足，双源一致'
        '才可写盘，冲突一律升级人工仲裁',
        anchor_module('xv_confidence_review') + '（CV 多源仲裁规则，编写前方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_CVMETHOD, 'CV-M2', '基线对比：修改前后可对比', 'P1',
        '# 直接重写函数，无基线快照\n# 出错后无法回答"改之前是什么行为"\n',
        '# 修改前先落基线：\n#   baseline = run_current_behavior(args)  # 输出快照\n#   rewrite ...\n#   assert run_current_behavior(args) == baseline  # 等价域内\n',
        '基线对比规则前移：任何重构/修复先固化当前行为快照，改后'
        '在等价域内回放对比，行为差异显式化',
        anchor_module('xv_rule_checks') + '（CV 基线对比规则，编写前方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_CVMETHOD, 'CV-M3', '变异测试：修复必须可被测出', 'P2',
        '# 加了一个 if 分支，测试全绿就交付\n# 实际该分支从未被测试走进\n',
        '# 交付前自问：把新逻辑故意改错（变异），测试会不会红？\n#   不会红 -> 补测试用例覆盖该分支，再交付\n',
        '变异测试规则前移：测试对变更"敏感"才算有效覆盖；故意引入'
        '缺陷验证测试能捕获，防假绿',
        anchor_module('xv_confidence_review') + '（CV 变异测试规则，编写前方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_CVMETHOD, 'CV-M4', '代码漂移：结论有时效', 'P2',
        '# 上午诊断"函数 X 死代码"，下午代码改过\n# 仍按上午结论直接删\n',
        '# 删除前复核新鲜度：\n#   git diff --stat <file>  # 诊断后有无变更\n#   有变更 -> 重跑该文件检测，旧结论作废\n',
        '漂移守卫规则前移：检测结论对"当前源码快照"负责；源码变更'
        '后旧结论降级待复扫，删除类操作前必须复核',
        anchor_module('xv_evidence_crosscheck') + '（CV 证据新鲜度规则，编写前方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_CVMETHOD, 'CV-M5', '误报固化：确认误报须沉淀', 'P2',
        '# 判断某报警是误报，口头带过\n# 下次诊断同一误报再次阻断\n',
        '# 确认误报后同步固化：\n#   diag_zero_backlog_gate.fixate_fp_rules(skill_dir)  # 沉淀误报规则\n#   后续诊断自动降级，不再反复阻断\n',
        '误报固化闭环前移：确认的误报必须由固化入口 fixate_fp_rules 写入'
        '规则库并留门禁留痕（treatment_state 只做单条误报簿记，批量判定归'
        'treatment_feedback），否则同一误报在每次诊断/编写时反复消耗注意力',
        anchor_module('diag_zero_backlog_gate.fixate_fp_rules') + '（CV 误报固化域，编写前方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-1', '等价性自检：重构前后语义等价', 'P1',
        '# 重构循环为推导式后直接交付\n# 忽略了原循环里的 break 短路语义\n',
        '# 重构交付前自检三问：\n#   1) 短路(break/return)语义是否保留？\n#   2) 异常路径行为是否一致？\n#   3) 副作用顺序是否改变？\n# 任一存疑 -> 保留原实现或补等价性测试\n',
        'EquivalenceGuard 前移：重构不是"改写"而是"等价变换"，'
        '短路/异常/副作用顺序三域必须逐一核对',
        anchor_module('diag_regression_guard.EquivalenceGuard') + '（编写时方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-2', '异常传播自检：链路逐层核对', 'P1',
        '# 加了内部 try/except 后直接交付\n# 下游依赖该异常做重试，现在静默失败\n',
        '# 新增异常处理前自检：\n#   grep 调用链下游有无 except 该类型做分支？\n#   有 -> 本层吞掉即破坏其重试/降级逻辑，须 re-raise\n',
        '异常传播静态分析前移：捕获某异常前先查全链路谁在依赖它；'
        '吞异常等于改了下游的控制流',
        anchor_module('diag_exception_detection') + '（编写时方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-3', '行为回归：修复附回归验证', 'P1',
        '# 修完 bug 手动看一眼输出，直接交付\n# 下周老 bug 回归\n',
        '# 修复必须三件套：\n#   1) 复现测试（红）\n#   2) 修复（绿）\n#   3) 该测试进回归套件\n# 缺一即不算修复完成\n',
        '行为回归规则前移：bug 修复的完成定义是"复现测试进回归'
        '套件"，不是"看起来好了"',
        anchor_module('diag_regression_guard') + '（编写时方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-4', '静默降级禁令：可观测性三件套', 'P1',
        'def load(cfg):\n    try:\n        return read_config(cfg)\n    except Exception:\n        return None\n',
        'import logging\n\n_LOG = logging.getLogger(__name__)\n\n\ndef load(cfg):\n    try:\n        return read_config(cfg)\n    except ValueError as exc:\n        _LOG.warning("配置读取失败回退默认: %s", exc)\n        return None\n',
        '六阶段管线高频缺陷：静默 except/裸 pass/吞错返回 None；'
        '降级必须告警日志 + 理由 + 可追溯标记三件套',
        anchor_module('refactor_split_actions') + ' + D35-SILENT-FALLBACK（编写时方法引用）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-5', '导入链自检：改完即 compile+import', 'P0',
        '# 批量改了 3 个模块的 import，跳过验证\n# 消费方 import 即崩\n',
        '# 每个被改模块改完立即：\n#   compile(src, name, "exec")   # 语法层\n#   python -c "import <module>"  # 导入链层\n# 任一失败 -> 立即回滚该文件，禁止批量改完再验\n',
        'pyc 缓存与惰性导入会掩盖断裂链；逐文件 compile+import 双'
        '验证，禁批量攒验',
        anchor_module('diag_dependency_core') + '（编写时方法引用，Gotchas#1/#2 固化）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-6', '序列化自检：禁止 default=str 静默降级', 'P1',
        'import json\n\n\ndef save(state):\n    with open("state.json", "w", encoding="utf-8") as fp:\n        json.dump(state, fp, default=str)\n',
        'import json\n\n\ndef save(state):\n    with open("state.json", "w", encoding="utf-8") as fp:\n        json.dump(state, fp)\n',
        'default=str 会把 set/datetime/自定义对象静默压成字符串，类型与结构失真；'
        '默认让 json.dump 对不支持的对象显式抛 TypeError。确需扩展类型时，由项目'
        '定义能保持数据契约的显式编码器，并补往返测试，不用 str 充当通用序列化',
        anchor_module('treatment_experience') + ' (编写时方法引用：序列化类型契约)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-7', '__future__ 位置自检', 'P0',
        'import ast\nfrom __future__ import annotations\n',
        'from __future__ import annotations\n\nimport ast\n',
        'from __future__ 必须在模块 docstring 与其他 import 之前，'
        '位置错误遍历即 SyntaxError 崩溃；验证用 compile 而非 ast.parse',
        anchor_module('treatment_experience') + ' (Gotchas#1 固化：__future__ 位置，编写时方法引用)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_DIAGMETHOD, 'DM-8', '复杂度预算：写前先算圈复杂度', 'P2',
        '# 边写边堆分支，交付时才发现圈复杂度 25+ 无法维护\n',
        '# 动笔前预算：\n#   分支/循环/except 计数 > 10 -> 先设计卫语句与子函数拆分\n#   参数 > 7 -> 先定 dataclass\n#   嵌套 > 3 -> 先定提前返回结构\n',
        '复杂度评分前移为"写前预算"：圈复杂度/参数数/嵌套深度在'
        '设计期控制，比写完再重构成本低一个量级',
        anchor_module('diag_shared_ast_nodes') + '（编写前方法引用）',
        self_verifiable=False,
    ),
]
_METH_TEXTUAL = [
    make_code_ref(
        _SER_NORMTEXT, 'RD-01', 'raise 新异常未链原始异常', 'P1',
        'def parse(raw):\n    try:\n        return int(raw)\n    except ValueError:\n        raise ValueError("bad input")\n',
        'def parse(raw):\n    try:\n        return int(raw)\n    except ValueError as exc:\n        raise ValueError("bad input") from exc\n',
        '不写 from 时原始异常只作为隐式 __context__ 附在后文，语义弱且'
        '可被上层 from None 抑制；raise ... from exc 显式固定 __cause__ '
        '因果链，日志与上层判断都稳定可读',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: RD-01 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'RD-03', 'float 直接 == 比较', 'P1',
        'import math\n\n\ndef near(a, b):\n    return a == b\n',
        'import math\n\n\ndef near(a, b):\n    return math.isclose(a, b, rel_tol=1e-9)\n',
        '二进制浮点表示误差使 0.1+0.2 != 0.3；等值判断用 math.isclose '
        '并显式给容差',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: RD-03 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'RD-06', 'except 仅 print 不处理', 'P2',
        'def run():\n    try:\n        return step()\n    except OSError as exc:\n        print(exc)\n        return None\n',
        'import logging\n\n_LOG = logging.getLogger(__name__)\n\n\ndef run():\n    try:\n        return step()\n    except OSError:\n        _LOG.exception("step 失败，返回安全值")\n        return None\n',
        'print 不进日志系统、无级别无堆栈；异常处理要么实质修复/重试/'
        '上报，要么 _LOG.exception 带堆栈记录后给出明确返回契约',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: RD-06 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'RD-12', '低效循环与重复计算', 'P2',
        'def scale(items, k):\n    out = []\n    for i in range(len(items)):\n        out.append(items[i] * k)\n    return ", ".join([str(x) for x in out])\n',
        'def scale(items, k):\n    return ", ".join(str(x * k) for x in items)\n',
        'range(len()) 反复下标、循环外重复 len()、列表推导拼字符串都'
        '是可避免的开销与噪音；用生成器/推导式/直接迭代',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: RD-12 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'RD-23', '函数体超 50 行未拆分', 'P2',
        'def process(rows):\n    # 50+ 行混合清洗/校验/计算/落盘\n    cleaned = []\n    for r in rows:\n        if r.get("v"):\n            cleaned.append(r)\n    total = sum(r["v"] for r in cleaned)\n    with open("out.txt", "w", encoding="utf-8") as fp:\n        fp.write(str(total))\n    # ... 更多 50 行\n    return total\n',
        'def _clean(rows):\n    return [r for r in rows if r.get("v")]\n\n\ndef _persist(total):\n    with open("out.txt", "w", encoding="utf-8") as fp:\n        fp.write(str(total))\n\n\ndef process(rows):\n    total = sum(r["v"] for r in _clean(rows))\n    _persist(total)\n    return total\n',
        '超长函数混合多职责导致测试与复用成本陡增；按清洗/计算/IO '
        '职责拆分小函数',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: RD-23 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'DP-22', 'os.popen 的无超时 Shell 调用', 'P1',
        'import os\n\ndef ls(path):\n    return os.popen("ls " + path).read()\n',
        'import subprocess\n\n\ndef ls(path):\n    return subprocess.run(\n        ["ls", path], capture_output=True, text=True,\n        encoding="utf-8", timeout=30,\n    ).stdout\n',
        'os.popen 无超时无错误码，管道语义弱；subprocess.run 提供 '
        'capture_output/timeout/returncode 全套',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: DP-22 互补；检测器 DP 域未覆盖，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'DP-23', 'os.system 的无超时 Shell 调用', 'P1',
        'import os\n\ndef backup(src):\n    os.system("cp -r " + src + " /tmp")\n',
        'import subprocess\n\n\ndef backup(src):\n    return subprocess.run(\n        ["cp", "-r", src, "/tmp"], timeout=60\n    ).returncode\n',
        'os.system 返回值是退出码拼装且必经 shell 拼接注入面；'
        'subprocess.run 列表参数绕开 shell',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: DP-23 互补；检测器 DP 域未覆盖，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'DP-35', 'locale.format 已弃用', 'P2',
        'import locale\n\n\ndef fmt(n):\n    return locale.format("%d", n, grouping=True)\n',
        'import locale\n\n\ndef fmt(n):\n    return locale.format_string("%d", n, grouping=True)\n',
        'locale.format 自 3.7 弃用、3.12 已移除（调用即 AttributeError）；'
        'format_string 才是受维护 API，纯数字展示直接 f-string',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: DP-35 互补；检测器 DP 域未覆盖，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'DP-54', 'socket 全局默认超时的隐式耦合', 'P2',
        'import socket\n\n\ndef init():\n    socket.setdefaulttimeout(30)\n',
        'import socket\n\n\ndef connect(host):\n    conn = socket.create_connection((host, 443), timeout=30)\n    conn.settimeout(30)\n    return conn\n',
        'setdefaulttimeout 是正常 API（无弃用标记），但全局默认超时'
        '影响全进程所有 socket 且对已建连接无效，隐式耦合不可控；'
        '工程上在连接/套接字粒度显式设 timeout',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: DP-54 互补；工程实践建议非弃用 API，检测器 DP 域未覆盖，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'DP-55', '环境变量读取入口不统一', 'P2',
        'import os\n\n\ndef conf(k):\n    return os.environ[k] if k in os.environ else None\n\n\ndef conf2(k):\n    return os.getenv(k)\n',
        'import os\n\n\ndef conf(k, fallback):\n    return os.environ.get(k, fallback)\n',
        'os.environ[k] 缺省抛 KeyError、os.getenv 缺省返回 None，混用使'
        '缺省语义不一致；统一 os.environ.get(key, fallback)，由调用方显式提供默认值（注：'
        'os.getenv 从无第三参数，strict= 等额外实参调用即 TypeError）',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: DP-55 互补；检测器 DP 域未覆盖，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'MC-01', '循环引用 + __del__ 回收时机不可控', 'P2',
        'class Node:\n    def __init__(self):\n        self.peer = None\n\n    def __del__(self):\n        self.peer = None\n\n\ndef pair():\n    a, b = Node(), Node()\n    a.peer = b\n    b.peer = a\n    return a, b\n',
        'import weakref\n\n\nclass Node:\n    def __init__(self):\n        self._peer = None\n\n    def bind(self, peer):\n        self._peer = weakref.ref(peer)\n',
        'PEP 442 起带 __del__ 的循环引用可被 GC 回收、不再滞留 '
        'gc.garbage，但回收时机取决于 GC 触发而非引用计数，资源释放'
        '不确定；互引用改 weakref，清理逻辑用 with/finally',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: MC-01 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'FN-01', '函数参数超过 7 个', 'P2',
        'def render(title, body, author, date, tags, lang, theme, footer, header):\n    return title + body + author + date + str(tags) + lang + theme + footer + header\n',
        'from dataclasses import dataclass\n\n\n@dataclass\nclass RenderSpec:\n    title: str\n    body: str\n    author: str\n    date: str\n    tags: list\n    lang: str\n    theme: str\n    footer: str\n    header: str\n\n\ndef render(spec: RenderSpec) -> str:\n    return (\n        spec.title + spec.body + spec.author + spec.date + str(spec.tags)\n        + spec.lang + spec.theme + spec.footer + spec.header\n    )\n',
        '参数超过 7 个后调用方错误率与维护成本陡增；聚合为 dataclass '
        '参数对象或 Builder',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: FN-01 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'HP-006', '嵌套深度过高', 'P2',
        'def grade(score):\n    if score:\n        if score > 60:\n            if score > 80:\n                if score > 90:\n                    return "A"\n                return "B"\n            return "C"\n        return "D"\n    return "F"\n',
        'def grade(score):\n    if not score:\n        return "F"\n    if score > 90:\n        return "A"\n    if score > 80:\n        return "B"\n    if score > 60:\n        return "C"\n    return "D"\n',
        '深嵌套使分支组合数指数膨胀，测试难以覆盖；卫语句提前返回'
        '压平分支',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: HP-006 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'SB-01', '遮蔽内置名称', 'P2',
        'def summarize(list):\n    return len(list), max(list)\n',
        'def summarize(values):\n    return len(values), max(values)\n',
        '参数/变量命名为 list/dict/type/id/open 等内置名后，同作用域'
        '内置功能即被遮蔽（与 B19 检测同源）',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: SB-01 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'unbounded_recursion', '无界递归', 'P1',
        'def walk(node):\n    return 1 + walk(node.next)\n',
        'def walk(node):\n    count = 0\n    seen = set()\n    while node is not None and id(node) not in seen:\n        seen.add(id(node))\n        count += 1\n        node = node.next\n    return count\n',
        '无终止条件的递归在长链或环输入上触发 RecursionError（默认递归'
        '上限 1000，深度守卫设在 1000 也来不及触发）；改显式迭代并用'
        '已访问集合断环，深度不再受解释器栈限制',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: unbounded_recursion 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'TX-01', '函数返回多种类型', 'P2',
        'def find(key):\n    if key in TABLE:\n        return TABLE[key]\n    if key.startswith("x"):\n        return "not found"\n    return None\n',
        'def find(key):\n    """返回命中值；未命中返回 None。"""\n    return TABLE.get(key)\n',
        '多类型返回迫使调用方逐分支 isinstance 防御；统一返回契约'
        '（同类型 / Optional / 显式 Union 标注）',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: TX-01 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'TY-01', '公开函数缺类型注解', 'P2',
        'def convert(value, rate):\n    return value * rate\n',
        'def convert(value: float, rate: float) -> float:\n    return value * rate\n',
        '公开 API 无注解时调用方只能读实现猜契约；按默认值推断补'
        '参数注解并标注返回值',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: TY-01/missing_annotations 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'missing_docstring', '公开函数缺 docstring', 'P2',
        'import json\n\n\ndef export(rows, fmt):\n    if fmt == "json":\n        return json.dumps(rows, ensure_ascii=False)\n    return "\\n".join(",".join(str(cell) for cell in row) for row in rows)\n',
        'import json\n\n\ndef export(rows, fmt):\n    """导出行数据。\n\n    Args:\n        rows: 待导出行列表。\n        fmt: 目标格式（csv/json）。\n    """\n    if fmt == "json":\n        return json.dumps(rows, ensure_ascii=False)\n    return "\\n".join(",".join(str(cell) for cell in row) for row in rows)\n',
        'docstring 是 API 的第一契约面；骨架至少含参数与返回值摘要',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: missing_docstring 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_NORMTEXT, 'T18-MAGIC-NUMBER', '魔法数字', 'P2',
        'def circle(r):\n    return 3.14159 * r * r\n',
        'PI = 3.14159\n\n\ndef circle(r):\n    return PI * r * r\n',
        '裸数字掩盖业务语义且改点分散；提取为命名常量（安全数字 '
        '0/1/2/-1 豁免，__all__/__version__ 防误改）',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE: T18-MAGIC-NUMBER 互补；无确定性检测器，编写前文本注入)',
        self_verifiable=False,
    ),
]
_METH_TEXTUAL_GFX = [
    make_code_ref(
        _SER_GUARDFIX, 'GF-01', '全角标点混入代码', 'P1',
        'def add(a, b)：\n    return a + b\n',
        'def add(a, b):\n    return a + b\n',
        '全角标点（（）｛｝【】：；，？！及“”‘’全角引号）直接触发'
        'SyntaxError；复制粘贴来自文档/聊天的代码后必须核对标点为半角',
        anchor_module('diag_rules_text_damage._check_fullwidth') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-03', '连续重复语句（编辑残留）', 'P2',
        'def reset():\n    self.count = 0\n    self.count = 0\n    self.count = 0\n    return True\n',
        'def reset():\n    self.count = 0\n    return True\n',
        '连续 3 行以上完全相同语句是批量编辑残留特征；保留一行即可',
        anchor_module('diag_rules_text_damage._check_duplicate_lines') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-06', '孤立 except 块残留', 'P1',
        'def f(x):\n    return x\n    except ValueError:\n        pass\n',
        'def f(x):\n    return x\n',
        'try: 被移除后 except 残留是结构性破坏，编译期即报错；'
        '重构删除 try 时必须整体删除 except 段',
        anchor_module('diag_rules_text_damage._check_orphaned_except') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-08', 'try/except 静默吞错的脆弱导入链', 'P2',
        'try:\n    import json\nexcept Exception:\n    pass\ntry:\n    import yaml\nexcept Exception:\n    pass\n',
        'import json\n\ntry:\n    import yaml\nexcept ImportError as exc:\n    import logging\n\n    logging.getLogger(__name__).warning("yaml 不可用: %s", exc)\n    yaml = None\n',
        '成串的静默吞错导入链使依赖故障不可见；拆分独立导入并对'
        '可选依赖显式降级日志',
        anchor_module('diag_symbol_integrity.check_import_chain_integrity') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-10', '悬挂缩进（块变更后未跟随）', 'P1',
        'def f():\n    if x:\n        return 1\n      return 2\n',
        'def f():\n    if x:\n        return 1\n    return 2\n',
        '块首行调整后内部缩进未跟随即 IndentationError；缩进对齐后'
        '用 compile() 而非 ast.parse 验证',
        anchor_module('diag_rules_text_damage._check_hanging_indent') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-12', '管线产物完整性异常', 'P1',
        '# 产物文件内容：截断的函数片段\ndef broken(:\n    pass\n',
        '# 产物文件内容：完整可编译单元\n'
        'def fixed(value):\n'
        '    return value * 2\n',
        '生成管线中断会留下截断/空文件产物；写盘前后用 compile+import '
        '双向验证产物完整性',
        anchor_module('diag_rules_text_damage._check_artifact_integrity') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-15', '函数体坍缩为空壳', 'P2',
        'def validate(self, payload):\n    pass\n',
        'def validate(self, payload):\n    if not payload:\n        raise ValueError("payload required")\n    return True\n',
        '重构把有意义实现收缩成 pass/... 空壳后调用方静默失去校验；'
        '确属占位须留 TODO 与负责人',
        anchor_module('diag_module_surface._check_stub_collapse') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-17', '枢纽模块使用相对导入', 'P2',
        '# pkg/hub.py（被多层子包引用）\nfrom . import sibling\n',
        '# pkg/hub.py（被多层子包引用）\nfrom pkg import sibling\n',
        '相对导入按模块自身 __package__ 解析，消费方层级不影响；但枢纽'
        '模块一旦被移动、以脚本方式执行或跨包复用即断链，故一律绝对导入',
        anchor_module('diag_wiring_import_scan.detect_hub_modules') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_GUARDFIX, 'GF-19', '传递依赖缺失导入', 'P2',
        'def render(ctx):\n    return helper.transform(ctx)\n',
        'from pkg.helpers import helper\n\n\ndef render(ctx):\n    return helper.transform(ctx)\n',
        '依赖模块的依赖被移走后本文件成为断点；补充显式 import 并'
        '确认来源模块归属',
        anchor_module('diag_wiring_symbol_scan.detect_transitive_missing') + '（编写前文本注入）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-F401', '未使用导入', 'P2',
        'import os\nimport sys\n\n\ndef f():\n    return sys.path\n',
        'import sys\n\n\ndef f():\n    return sys.path\n',
        '未使用导入是死代码且触发导入副作用；移除，或为 re-export '
        '显式声明 __all__',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 F401，知识库 RUFF-F401 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-F541', '无占位 f-string', 'P3',
        'def greet():\n    return f"hello"\n',
        'def greet():\n    return "hello"\n',
        '无 {} 占位的 f 前缀是冗余标记，常为删变量后残留；移除 f 前缀',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 F541，知识库 RUFF-F541 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-F821', '未定义名称', 'P0',
        'def f():\n    return conifg["key"]\n',
        'def f(config):\n    return config["key"]\n',
        '未定义名称运行时必现 NameError（IM-01/GF-09 同域，拼写错'
        '高发）；写盘前过一遍名称解析',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 F821，知识库 RUFF-F821 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-F841', '未使用局部变量', 'P2',
        'def total(items):\n    sum_v = sum(items)\n    return len(items)\n',
        'def total(items):\n    return len(items)\n',
        '赋值后未读取的局部变量是逻辑丢失信号（可能漏 return）；'
        '删除或改 _ 前缀显式忽略',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 F841，知识库 RUFF-F841 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-SIM103', '条件返回可简化', 'P3',
        'def ok(x):\n    if x > 0:\n        return True\n    return False\n',
        'def ok(x):\n    return x > 0\n',
        'if/return True/False 二段式可直接返回布尔表达式，语义等价'
        '且少一半分支',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 SIM103，知识库 RUFF-SIM103 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-C403', '推导式外层冗余 set/list', 'P3',
        'def uniq(items):\n    return set([x for x in items])\n',
        'def uniq(items):\n    return set(items)\n',
        'set()/list() 直接接受可迭代，包一层推导是双重遍历；直接构造（ruff C403 针对列表推导包裹，C401 针对生成器包裹）',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 C403，知识库 RUFF-C403 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-DTZ005', 'datetime.now() 缺时区', 'P2',
        'from datetime import datetime\n\n\ndef now():\n    return datetime.now()\n',
        'from datetime import datetime, timezone\n\n\ndef now():\n    return datetime.now(timezone.utc)\n',
        'naive datetime 在跨时区部署下排序/比较错乱；显式传 tz=timezone.utc '
        '或业务时区',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 DTZ005，知识库 RUFF-DTZ005 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-G004', '日志用 f-string 即时求值', 'P3',
        'import logging\n\n_LOG = logging.getLogger(__name__)\n\n\ndef f(v):\n    _LOG.info(f"value={v}")\n',
        'import logging\n\n_LOG = logging.getLogger(__name__)\n\n\ndef f(v):\n    _LOG.info("value=%s", v)\n',
        'f-string 在日志被过滤时仍求值，热点路径白白开销；用惰性 '
        '% 参数',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 G004（flake8-logging-format），知识库 RUFF-G004 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-UP032', '%-format/str.format 改 f-string', 'P3',
        'def msg(n):\n    return "count=%d" % n\n',
        'def msg(n):\n    return f"count={n}"\n',
        'f-string 可读性与求值效率均优；新代码统一 f-string（日志'
        '惰性 % 场景除外）',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 UP032，知识库 RUFF-UP032 互补）',
        self_verifiable=False,
    ),
    make_code_ref(
        _SER_RUFFFIX, 'RUFF-I001', '导入块未排序', 'P3',
        'import sys\nimport os\n\n\ndef f():\n    return os.sep + sys.prefix\n',
        'import os\nimport sys\n\n\ndef f():\n    return os.sep + sys.prefix\n',
        '导入块按 stdlib→三方→本地分组排序，冲突与依赖一眼可读',
        anchor_module('fix_guide_knowledge') + ' (RULE_FIX_KNOWLEDGE 互补；ruff 外部规则 I001，知识库 RUFF-I001 互补）',
        self_verifiable=False,
    ),
]
_NETWORK_AND_SEC_REFS: list[CodeRef] = [
    make_code_ref(
        _SER_NETFIX, 'NW-01', 'HTTP客户端显式禁用证书校验', 'P1',
        'import requests\n'
        'import httpx\n'
        '\n'
        'def fetch(url):\n'
        '    return requests.get(url, verify=False)\n'
        '\n'
        'async def fetch_async(url):\n'
        '    async with httpx.AsyncClient(verify=False) as client:\n'
        '        return await client.get(url)\n',
        'import requests\n'
        'import httpx\n'
        '\n'
        'def fetch(url):\n'
        '    # 默认校验证书；自签名场景用自定义 CA 而非关闭校验\n'
        '    return requests.get(url, timeout=30)\n'
        '\n'
        'async def fetch_async(url, ca_bundle=None):\n'
        '    # 缺省使用系统信任库；私有 CA 由当前项目显式注入\n'
        '    verify = ca_bundle if ca_bundle is not None else True\n'
        '    async with httpx.AsyncClient(verify=verify) as client:\n'
        '        return await client.get(url, timeout=30.0)\n',
        "verify=False/ssl=False 使连接接受任意证书，中间人可截获或篡改传输数据（凭据/Token/业务数据）。"
        "自签名证书应通过自定义 CA 上下文解决而非关闭校验。aiohttp 场景由 SE-23 扩展的 ssl=False 分支承接。",
        anchor_module('diag_se_stdlib.check_SE23') + ' (Gate5 注册表 SE23)',
    ),
    make_code_ref(
        _SER_NETFIX, 'NW-02', 'urllib urlopen 未设置超时', 'P2',
        'from urllib.request import urlopen\n'
        '\n'
        'def fetch(url):\n'
        '    with urlopen(url) as resp:\n'
        '        return resp.read()\n',
        'from urllib.request import urlopen\n'
        '\n'
        'def fetch(url):\n'
        '    with urlopen(url, timeout=30) as resp:\n'
        '        return resp.read()\n',
        "urlopen 无 timeout 时依赖全局 socket 默认值（可能无限阻塞），恶意/慢速服务端可拖垮调用线程。"
        "检测语义由 check_SE27（A5 通道）承接，不在 Gate5 注册表（与 IO-01/TO-01 防双报豁免一致）。",
        anchor_module('diag_traps_blocking.check_SE27') + ' (A5 detect_all 通道)',
    ),
    make_code_ref(
        _SER_NETFIX, 'NW-03', 'httpx 请求未设置超时', 'P2',
        'import httpx\n'
        '\n'
        'def fetch(url):\n'
        '    return httpx.get(url)\n'
        '\n'
        'def fetch_stream(url):\n'
        '    # timeout=None 显式禁用超时，同样风险\n'
        '    with httpx.stream("GET", url, timeout=None) as resp:\n'
        '        return resp.read()\n',
        'import httpx\n'
        '\n'
        'def fetch(url):\n'
        '    return httpx.get(url, timeout=30)\n'
        '\n'
        'def fetch_stream(url):\n'
        '    # 保留流式 API；分阶段超时：连接 10s / 读 300s\n'
        '    timeout = httpx.Timeout(connect=10.0, read=300.0, write=60.0, pool=10.0)\n'
        '    with httpx.stream("GET", url, timeout=timeout) as resp:\n'
        '        return resp.read()\n',
        "httpx 顶层快捷 API 与 Client/AsyncClient 都有默认超时（当前默认 5s，具体以所用版本配置为准），"
        "显式传 timeout=None 才是完全禁用；依赖默认值可能与业务耗时不匹配，无超时请求可被恶意服务端无限阻塞。"
        "Gate5 由 IO-03 单一权威源实时拦截（NW03 注册但让位防双报）；"
        "本条直调 check_NW03 与 A5 通道保留。",
        anchor_module('diag_traps_blocking.check_NW03') + ' (A5 detect_all / 直调通道；Gate5 由 IO-03 承接)',
    ),
    make_code_ref(
        _SER_NETFIX, 'NW-04', 'aiohttp 会话请求未设置超时', 'P2',
        'import aiohttp\n'
        '\n'
        'async def fetch(url):\n'
        '    async with aiohttp.ClientSession() as session:\n'
        '        async with session.get(url) as resp:\n'
        '            return await resp.read()\n',
        'import aiohttp\n'
        '\n'
        'async def fetch(url):\n'
        '    timeout = aiohttp.ClientTimeout(total=30, connect=10)\n'
        '    async with aiohttp.ClientSession(timeout=timeout) as session:\n'
        '        async with session.get(url) as resp:\n'
        '            return await resp.read()\n',
        "aiohttp per-request 未设 timeout 时回落到 ClientSession 默认 total=300s，"
        "长阻塞占用连接与协程资源。会话级 ClientTimeout 提供统一默认；仅耗时不同的请求"
        "才在请求级覆盖，避免同值双写漂移。"
        "Gate5 注册表 NW04 实时拦截（仅认 ClientSession 构造的接收者，requests.Session 不误报）。",
        anchor_module('diag_traps_blocking.check_NW04') + ' (Gate5 注册表 NW04)',
    ),
    make_code_ref(
        _SER_SECFIX, 'SE-30b', '裸 popen（from os import popen）执行动态构造命令', 'P1',
        'from os import popen\n'
        '\n'
        'def read_log(filename):\n'
        '    # 命令经 shell 解释，filename 可注入 "x; rm -rf /"\n'
        '    return popen("cat /var/log/" + filename).read()\n',
        'import re\n'
        'import subprocess\n'
        '\n'
        'def read_log(filename):\n'
        '    # 数组形态本身即转义；白名单防参数滥用（如 --flag 注入）\n'
        '    if not re.fullmatch(r"[A-Za-z0-9._-]+", filename):\n'
        '        raise ValueError("invalid filename")\n'
        '    return subprocess.run(\n'
        '        ["cat", "/var/log/" + filename],\n'  # jwsgj:suppress 供应链安全-敏感路径 — 缺陷示例代码文本
        '        shell=False, check=True, capture_output=True,\n'
        '        text=True, encoding="utf-8",\n'
        '        timeout=30,\n'
        '    ).stdout\n',
        "裸 popen（from os import popen）无条件经 /bin/sh 解释命令，"
        "动态拼接等价于命令注入（分号/管道/反引号均可利用）；popen 无 shell=False 可关。"
        "唯一安全解是换 subprocess 数组形态（数组参数不经 shell，"
        "无需 shlex.quote——quote 的引号会成为传给命令的字面参数，含空格的合法文件名反被破坏）。"
        "os.popen 模块前缀形态由 SE-02 恒报覆盖（防双报分工），"
        "与 SE-08（subprocess shell=True）互补覆盖执行面。",
        anchor_module('diag_se_injection.check_SE30b') + ' (Gate5 注册表 SE30B)',
    ),
    make_code_ref(
        _SER_SECFIX, 'CV-01b', 'marshal 反序列化不可信数据', 'P1',
        'import marshal\n'
        '\n'
        'def load_cache(blob):\n'
        '    # 不可信字节可致解析失败或解释器未定义行为\n'
        '    return marshal.loads(blob)\n',
        'import json\n'
        '\n'
        'def load_cache(blob):\n'
        '    # 仅适用于 JSON 兼容缓存，不能机械替代全部 marshal 数据\n'
        '    return json.loads(blob)\n',
        "marshal 是 CPython 内部序列化格式，支持标量、容器与代码对象，不与 pickle 共享任意对象构造协议；"
        "loads 本身不执行代码对象，后续 exec/eval 才会执行。但恶意或畸形输入仍可导致解析失败或解释器未定义行为，"
        "代码对象跨版本反序列化也有未定义行为。跨信任边界只应使用 JSON 等无代码对象语义的格式，且 JSON 仅覆盖其类型子集。"
        "与 SE-04/SE-25（pickle 系）互补覆盖反序列化面。",
        anchor_module('diag_se_stdlib.check_CV01b') + ' (Gate5 注册表 CV01B)',
    ),
    make_code_ref(
        _SER_SECFIX, 'B108', '硬编码系统临时目录路径', 'P3',
        'import os\n'
        '\n'
        'def dump_debug(data):\n'
        '    # 可预测路径：符号链接抢占 + 跨平台不可移植\n'
        '    with open("/tmp/debug_dump.json", "w") as fh:\n'
        '        fh.write(data)\n',
        'import tempfile\n'
        '\n'
        'def dump_debug(data):\n'
        '    with tempfile.NamedTemporaryFile(\n'
        '        mode="w", suffix=".json", delete=False,\n'
        '    ) as fh:\n'
        '        fh.write(data)\n'
        '        return fh.name\n',
        "硬编码 /tmp/ 等系统临时路径使文件位置可预测，本地攻击者可抢先创建符号链接指向敏感文件（CWE-377），"
        "且 Windows 下路径不存在。tempfile 家族按平台返回安全随机路径。"
        "与 SE-09（tempfile.mktemp 竞态 API）互补。",
        anchor_module('diag_se_stdlib.check_B108') + ' (Gate5 注册表 B108)',
    ),
    make_code_ref(
        _SER_SECFIX, 'B603', '外部输入构造 subprocess 命令数组', 'P1',
        'import subprocess\n'
        '\n'
        'def ping(host):\n'
        '    # host 来自请求参数时，数组形态只能挡注入不能挡滥用\n'
        '    return subprocess.run(["ping", "-c", "1", host],\n'
        '                          capture_output=True)\n',
        'import re\n'
        'import subprocess\n'
        '\n'
        'def ping(host):\n'
        '    # 格式白名单：仅允许 ASCII 字母/数字/点/连字符/下划线\n'
        '    # （str.isalnum 会放行全部 Unicode 字母，不可作白名单判据）\n'
        '    if not re.fullmatch(r"[A-Za-z0-9._-]+", host):\n'
        '        raise ValueError("invalid host")\n'
        '    return subprocess.run(["ping", "-c", "1", "--", host],\n'
        '                          shell=False, capture_output=True,\n'
        '                          timeout=30, check=True)\n',
        "subprocess 数组形态（shell=False）已阻断 shell 元字符注入，"
        "但外部输入仍可被滥用为参数注入（如 host 位置传入 \"--flag\"）。对外部输入做格式白名单校验 + \"--\" 终结选项解析是完整口径。"
        "跨文件污点语义由 SE-38（场景级）承接，本条仅编写前引导。",
        anchor_module('diag_security_diagnoser') + ' (SE-38 跨文件污点传播，场景级)',
        self_verifiable=False,
    ),
]
METH_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    [*_METH_ANCHORED, *_METH_METHODS, *_METH_TEXTUAL,
     *_METH_TEXTUAL_GFX, *_NETWORK_AND_SEC_REFS],
    "METH_CODE_REFS",
)
register_code_refs(METH_CODE_REFS, "prevention_method_refs")
_log.info(
    "prevention_method_refs 方法级预防库已加载: %d 条 (v%s)",
    len(METH_CODE_REFS), METH_CODE_REFS_VERSION)
