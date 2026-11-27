from __future__ import annotations

__all__ = [
    'BANDIT_FIX_SUGGESTIONS',
    'RUFF_DELEGATION_KNOWLEDGE',
    'RUFF_DELEGATION_SAFE_KEY',
    'RUFF_DELEGATION_UNSAFE_KEY',
    'RULE_FAMILY_GUIDANCE',
    'RULE_FIX_KNOWLEDGE',
    'SE_FIX_KNOWLEDGE',
]
_ASSERT_VALIDATION_GUIDANCE = (
    "生产代码避免用 assert 做输入校验（-O 模式下整条语句被移除）："
    "改用显式 if not cond: raise ValueError(...)；测试代码中的 assert 属"
    "断言语义不在此列（与 CA-01 同内核）")
_SYSTEM_TEMP_DIR_GUIDANCE = (
    "避免硬编码 /tmp、/var/tmp、C:\\Temp 等系统临时目录（可预测路径可被"
    "本地攻击者抢先创建符号链接，且跨平台不可移植）：改用 "
    "tempfile.mkdtemp()/NamedTemporaryFile() 创建，或 tempfile.gettempdir() "
    "动态获取")
_NONE_COMPARISON_GUIDANCE = (
    "==/!= 与 None 比较：替换为 is None / is not None（None 为单例，"
    "== 可被自定义 __eq__ 重载产生意外结果）；AST 级安全替换点为 "
    "Compare 节点的 operands，参考 Ruff E711")
_MUTABLE_DEFAULT_GUIDANCE = (
    "可变默认参数（list/dict/set/{} / set()）：默认值在函数定义期只求值"
    "一次，跨调用共享同一对象会累积状态；改为 None 占位并在函数内部"
    "初始化（None→新建容器）")
_OPEN_WITH_GUIDANCE = (
    "open() 未用 with 语句可能导致资源泄漏：包装为 with open(...) as f: "
    "模式（或 finally 中显式 close()），确保异常路径同样释放句柄")
_CHMOD_MIN_PERMISSION_GUIDANCE = (
    "按最小权限收敛（文件 0o600/0o640、目录 0o700/0o750；"
    "目录必须保留执行/搜索位），取消 group/other 写位；"
    "修复后核对属主与部署账号")
_SENSITIVE_VALUE_MASK_EXAMPLE = (
    "def mask(value): text = str(value); return text[:2] + '****' + "
    "text[-2:] if len(text) > 8 else '****'")
BANDIT_FIX_SUGGESTIONS: dict[str, str] = {
    "B307": "避免使用 eval()，考虑 ast.literal_eval() 或 json.loads() 处理可信数据",
    "B308": "避免使用 mark_safe()，确保输入经过充分转义",
    "B310": "避免直接打开不可信 URL：用 urllib.parse.urlparse 校验 scheme（仅 http/https）与主机白名单，拒绝 file 等危险 scheme 及内网/本地地址；仅改用 requests 不能替代这些校验",
    "B403": "避免使用 pickle 反序列化不可信数据，使用 json 或 msgpack",
    "B404": "评估 subprocess 使用是否必要，确保不拼接用户输入到 shell 命令",
    "B602": "subprocess 首选参数列表+shell=False；仅 POSIX 环境确需 shell=True 时才用 shlex.quote() 逐参转义（Windows cmd.exe 不适用）",
    "B603": "subprocess shell=False 时，验证输入参数",
    "B604": "避免 shell=True，使用参数列表形式",
    "B605": "避免 os.system()，使用 subprocess.run() 并验证输入",
    "B607": "subprocess shell=True 时避免拼接部分路径，改用绝对路径参数列表",
    "B608": "SQL 字符串拼接存在注入风险，改用参数化查询（execute 携带占位符与参数元组）",
    "B321": "避免使用 FTP 协议传输敏感数据，使用 SFTP/SCP",
    "B322": "避免使用 Python 2 的 input()（读取后按源码求值，等价 eval）：改用 sys.stdin.readline() 读取并显式校验/转换，或迁移到 Python 3",
    "B306": "避免使用 mktemp()，使用 tempfile.mkstemp()",
    "B108": _SYSTEM_TEMP_DIR_GUIDANCE,
    "B501": "避免 verify=False 关闭 SSL 证书验证，保留默认验证或指定 CA 证书包",
    "B303": "避免使用 MD5/SHA1，使用 hashlib.sha256() 或 hashlib.sha512()",
    "B304": "避免使用 DES/Blowfish，使用 AES-256 (cryptography 库)",
    "B305": "避免不安全的 cipher 模式（尤其 ECB）：优先 AES-GCM 等 AEAD；必须使用 CBC 时采用随机 IV 并配合 Encrypt-then-MAC 认证，禁止只加密不认证",
    "B311": "安全场景避免使用 random 模块（PRNG 可预测），改用 secrets 或 os.urandom",
    "B324": "使用 hashlib 时指定安全算法 (sha256/sha512)",
    "B301": "避免 pickle.loads() 反序列化不可信数据，改用 json 或白名单 Unpickler",
    "B506": "避免 yaml.load() 缺省 Loader（可执行任意代码），改用 yaml.safe_load()",
    "B106": "避免硬编码密码函数默认参数，凭据经环境变量或密钥管理器注入",
    "B320": "lxml 解析需禁用实体解析（resolve_entities=False, no_network=True）或改用 defusedxml",
    "B317": "SAX/XML 解析需禁用外部实体（external_general/parameter_entities=False）或改用 defusedxml",
    "B703": "Django 模板避免 mark_safe() 处理用户输入，依赖自动转义或改用 format_html",
    "B101": _ASSERT_VALIDATION_GUIDANCE,
    "B103": _CHMOD_MIN_PERMISSION_GUIDANCE,
    "B113": "requests 调用必须设置 timeout 参数，避免对端无响应时请求永久挂起",
}
_DELEGATION_SAFE = "safe_to_delegate"
_DELEGATION_UNSAFE = "do_not_mechanically_fix"
RUFF_DELEGATION_SAFE_KEY = _DELEGATION_SAFE
RUFF_DELEGATION_UNSAFE_KEY = _DELEGATION_UNSAFE
RUFF_DELEGATION_KNOWLEDGE: dict[str, dict[str, str]] = {
    _DELEGATION_SAFE: {
        "UP032": "str.format 调用替换为 f-string；仅委托 Ruff 可安全转换的形态",
        "F541": "无占位 f-string 移除 f 前缀；会产生 docstring 的形态不得机械修复",
        "RUF010": "f-string 内显式 str()/repr()/ascii() 改 !s/!r/!a 转换旗标；含注释的形态不得机械修复",
    },
    _DELEGATION_UNSAFE: {
        "PERF102": "dict.items() 仅使用键或值时改 keys()/values()：本机 Ruff 0.17.5 实测把该修复标为 unsafe，ruff --fix 不会改动（仅 --unsafe-fixes 才执行），非标准映射接收者还会丢键值语义；须人工确认接收者是否为内建 dict",
        "UP031": "printf 风格 % 格式化改 str.format 的官方修复为 unsafe：单元素元组 '%s' % (x,) 与 f-string 语义不同（元组整体 vs 解包），占位符与实参形态需逐条核对；ruff --fix 默认不执行",
        "LOG015": "root logger 调用应改用模块级 logger = logging.getLogger(__name__)；Ruff 不提供自动修复，且本规则不是 G004 的 logging f-string 规则",
        "C401": "set(generator) 改集合推导或 set(iterable) 的官方修复为 unsafe，可能删除注释；须人工保留注释与语义",
        "SIM102": "嵌套 if 合并在非 preview 下为 unsafe；先核对短路、副作用、注释与格式，禁止默认机械 --fix",
        "SIM103": "条件返回简化可能改变非 bool 条件及自定义比较语义，官方修复为 unsafe；须人工确认返回布尔契约",
        "F401": "删除未使用导入可能移除导入副作用或再导出；先区分安全再导出与 unsafe 删除，禁止一键清理",
        "RUF034": "if-else 两个分支表达式相同则直接赋值；Ruff 不提供自动修复，须人工确认分支求值与注释",
        "SIM118": "key in obj.keys() 仅在 obj 已知为 dict 时可安全改为 key in obj；其他 keys() 接收者上为 unsafe",
        "SIM115": "open() 等资源改用 with 管理生命周期；Ruff 不提供自动修复，须人工核对闭包与异常路径",
        "I001": "ruff --fix --select I001 重排导入历史 100% 回滚率：可破坏 __future__ 导入位置与 __all__ 引用，需人工审查",
        "UP045": "Optional[X]→X|None 在无 from __future__ import annotations 的文件上于 Python 3.12 模块加载时求值 TypeError（如 threading.Lock | None），先确认文件已有 __future__ annotations 再改",
        "UP006": "typing.List→list 等内建泛型要求目标 Python≥3.9；仍需兼容旧解释器或存在特殊运行时注解消费时，先确认兼容矩阵再改，不得机械替换",
        "UP037": "移除引号注解同受运行时求值约束，需确认注解不被运行时求值（如 dataclass/pydantic 字段）再改",
        "F811": "ruff 对重复 import 的 F811 修复按 safe 下发：实测 ruff --fix 直接删除重复导入（含 __init__.py 中 from x import y 的显式再导出形态）；def/class 重定义则不给修复。删除会连同后定义处的 docstring 与再导出一起消失，非纯等价转换；与修复器风险元数据 RUFF-F811（reliability=low/auto_safe=False）同口径，禁止一键 --fix",
        "F841": "ruff 对 F841 的修复为 Unsafe 级（官方 Fix safety 明确标注 unsafe）：删除未使用局部变量可能一并移除带副作用的赋值表达式；与修复器风险元数据 RUFF-F841（reliability=low/auto_safe=False）同口径，不得双标",
    },
}
RULE_FAMILY_GUIDANCE: dict[str, str] = {
    'GF': '建议检查代码格式并手动修正相关行',
    'SD': '建议检查文档或代码规范并调整',
    'POL': '建议调整策略配置以符合项目规范',
    'SE': '建议检查安全编码并手动修正',
    'DP': '建议参考 Python 最新 API 进行迁移（弃用项替换为官方推荐替代）',
    'RB': '建议按重构最佳实践进行调整',
    'RD': '建议检查代码质量指标并优化',
    'CQ': '建议检查代码质量并优化',
    'DB': '建议检查数据库连接、事务、查询参数化与资源释放',
    'GL': '建议检查全局变量使用并优化',
    'SC': '建议检查安全编码并手动修正',
    'NW': ('网络调用风险族：NW-01 显式关闭证书校验（verify=False/ssl=False，锚 SE-23）、'
           'NW-02/03/04 分别为 urllib/httpx/aiohttp 缺超时（锚 SE-27）——先补校验与 timeout，'
           '不要用 socket.setdefaulttimeout 改全局默认值'),
    'SJ': '建议检查字符串拼接并优化（循环内 += 改为 append + join）',
    'TX': '建议统一函数返回类型契约',
    'D21': '建议检查跨模块依赖并修正',
    'D9': ('依赖架构治理：循环依赖→拆解环上职责；分层违规→修正依赖方向；'
           '高扇出→按 fan_out_breakdown 的 upward 优先收敛；'
           '高扇入→先确认稳定底座契约再收敛消费方'),
    'HP': '建议按幻觉防控最佳实践处理',
    'SZ': '大文件/超阈值文件建议简化逻辑/消除重复/迁移无关职责（禁止直接拆分文件）',
    'LP': '建议补充活性探针（liveness probe）提升运行时可观测性',
    'AI': 'AI 技能安全建议：检查数据隐私、供应链投毒与反序列化安全',
    'AS': '建议评估模块分层/依赖方向/循环引用是否符合架构约束',
    'CM': '建议检查资源管理（文件/连接句柄）并使用 with 语句',
    'FN': '建议精简函数签名（参数对象/@dataclass 或 **kwargs）',
    'MC': '建议检查内存管理（循环引用/__del__/weakref）',
    'RC': '建议检查资源管理并添加清理逻辑',
    'RL': '建议在异常路径中释放资源（finally/with 语句）',
    'TY': '建议为公开函数参数与返回值补充类型注解',
    'XT': '建议核对 SQL 字段/表名与数据库 schema 及 SKILL.md 表格定义的一致性（列名拼写、表存在性）',
    'XR': '建议用 importlib/dir() 核实跨模块引用符号真实存在（防凭记忆拼写 API 名的幻觉引用）',
    'deep_nesting': '建议将深层嵌套代码提取为独立函数',
    'module_level_call': '建议将模块级调用移至函数内或使用 if __name__ 守卫',
    'todo_marker': '建议处理 TODO 标记或添加跟踪工单号',
    'conditional_import': '建议将条件导入统一为 try/except ImportError 模式',
    'danger_pattern': '建议检查危险模式并采用安全替代方案',
    'priority_recommendation': '建议按优先级排序处理代码问题',
    'SEC': '建议按安全编码规范手动修复（注入/加密/路径穿越等）',
    'RUFF': '建议按 ruff 规则说明修复对应代码问题',
    'BANDIT': '建议按 bandit 安全规则说明修复',
}
RULE_FIX_KNOWLEDGE: dict[str, str] = {
    "D9-HIGH-FANOUT": (
        "高扇出治理（converge_dependency）：①先看 fan_out_breakdown.upward——"
        "向上依赖必须消除（职责下沉到既有基座模块，或改为经包统一出入口消费）；"
        "②同层依赖合并为单一职责入口，消除重复边；③向下依赖属编排职责，"
        "保留但按子域拆分入口函数；④禁止拆分文件或新建模块，禁止保留转发桩"
    ),
    "D9-HIGH-FANIN": (
        "高扇入治理（converge_dependency）：①先确认是否为稳定底座契约"
        "（类型/日志/路径类天然高扇入，登记设计豁免）；②非底座则收敛消费方——"
        "把可上移的公共逻辑提到更底层模块；③禁止用转发桩稀释扇入；"
        "④扇入超过 100 的上帝模块必须给出稳定性评估与变更影响面"
    ),
    "D9-LAYER": (
        "分层违规治理：下层模块不得依赖上层。把被依赖的上层能力下沉到下层基座，"
        "或改为依赖注入（调用方传入）消除静态依赖；D9-LAYER-IMPLICIT 同样按此"
        "处理，禁止用 sys.modules 等动态机制绕过"
    ),
    "DP-01": "Python 3.12 移除 API：distutils→setuptools/_distutils_hack，imp→importlib，asynchat/asyncore/smtpd 已移除",
    "DP-02": "Python 3.14 移除 API：检查是否使用了 3.14 计划移除的 stdlib 模块",
    "DP-03": "multiprocessing：显式指定 start_method 避免平台差异",
    "DP-05": "datetime.utcnow()/utcfromtimestamp() 已弃用：替换为 datetime.now(datetime.timezone.utc) 等时区感知版本",
    "DP-07": "typing.Union[X, Y] 并非正式弃用，但 PEP 604（Python 3.10+）起推荐 X | Y：替换前确认目标解释器版本与注解是否在运行时求值（缺 from __future__ import annotations 时会在定义期求值）",
    "DP-08": "collections.abc：使用 collections.abc.Mapping 等替代 collections.Mapping",
    "DP-09": "threading：将 currentThread() 替换为 current_thread() 等蛇形命名",
    "DP-10": "inspect.getargspec() 已移除（3.11）：替换为 inspect.getfullargspec()",
    "DP-11": "__getattr__：若需完全控制属性访问，应同时定义 __getattribute__",
    "DP-12": "contextlib.nested() 已移除：改用 ExitStack 或嵌套 with 语句",
    "DP-13": "inspect.formatargspec() 已移除（3.11）：替换为 str(inspect.signature(func))",
    "DP-16": "圈复杂度超阈值（高复杂度）：提取独立职责子函数、卫语句提前返回、长 if-elif 链改策略表/match 分派；与 RD-23（长函数拆分）/RD-17（深层嵌套提取）同属复杂度治理，避免继续堆叠分支",
    "DP-22": "os.popen() 未标记弃用；官方推荐 subprocess.Popen/run 以控制编码等选项：subprocess.run([...], shell=False, capture_output=True, text=True) 并显式设 timeout；确需管道/重定向等 shell 特性时才用 shell=True，且拼接参数必须 shlex.quote 转义（否则与 SE-02 Shell 注入规则自相矛盾）",
    "DP-23": "os.system() 未标记弃用，但官方推荐使用 subprocess：改用 subprocess.run(cmd_list, shell=False)",
    "DP-24": "platform.popen() 已从标准库移除（当前标准库不存在）：改用 subprocess 模块",
    "DP-32": "logging.warn() 已弃用：替换为 logging.warning()",
    "DP-33": "warnings.warn_explicit()：检查参数签名是否匹配 Python 3.12+ 版本",
    "DP-35": "locale.format() 已弃用：替换为 locale.format_string()（纯数字展示可直接用 f-string）",
    "DP-36": "assertDictContainsSubset 已移除：用 assertEqual({k: actual[k] for k in expected.keys() & actual.keys()}, expected)，缺键或值不等都会判不通过，且支持不可哈希 value",
    "DP-37": "assert_() 已弃用：使用 assertTrue()",
    "DP-38": "xml.etree.ElementTree.getchildren() 已移除：使用 list(elem) 或 elem.iter()",
    "DP-39": "csv.Sniffer.sniff() 最多接收 sample 与 delimiters 两个参数：删除第三个及后续实参；delimiters 可保留，建议使用 delimiters=... 关键字传参",
    "DP-40": "base64.encodestring()/decodestring() 已弃用：使用 encodebytes()/decodebytes()",
    "DP-41": "imaplib.IMAP4_SSL() 的 keyfile/certfile 参数已弃用：构建 ssl.SSLContext 后经 ssl_context 参数传入",
    "DP-42": "smtplib.SMTP_SSL() 的 keyfile/certfile 参数已弃用：构建 ssl.SSLContext 后经 context 参数传入",
    "DP-43": "ssl.wrap_socket() 已弃用：创建 SSLContext 对象并调用 ctx.wrap_socket(sock)",
    "DP-44": "ssl.match_hostname() 已弃用(3.7)并移除(3.12)：改用 service_identity 库；使用 SSLContext 时必须同时设置 check_hostname=True、verify_mode=ssl.CERT_REQUIRED 并加载可信 CA，hostname_checks_common_name 仅控制 commonName 回退匹配，不能单独替代主机名验证",
    "DP-45": "@asyncio.coroutine 装饰器已弃用并移除（3.11）：改用 async def 定义协程",
    "DP-46": "@asyncio.coroutine + yield from 旧式协程已弃用：重构为 async def + await 语法",
    "DP-47": "asyncio API 的 loop 参数在 Python 3.10+ 已弃用：移除 loop 参数，改用 asyncio.get_running_loop()",
    "DP-48": "typing.re.Pattern/Match 已弃用：直接使用 re.Pattern/re.Match",
    "DP-49": "cStringIO/StringIO 旧导入路径：统一为 from io import StringIO（字节流用 BytesIO）",
    "DP-50": "from urllib import X 为 Python 2 路径：按用途改为 urllib.parse/urllib.request/urllib.error",
    "DP-51": "from email import Message 旧式导入：改为 from email.message import EmailMessage",
    "DP-52": "http.client.HTTPConnection 的 strict 参数已移除：删除该参数",
    "DP-53": "configparser.SafeConfigParser 已移除：替换为 configparser.ConfigParser",
    "DP-54": "socket.setdefaulttimeout() 是正常 API（无弃用标记），但设全局默认超时会影响全进程所有 socket 且对已建连接无效（隐式耦合不可控）：改为在连接/套接字粒度显式传 timeout（socket.create_connection(timeout=…)/conn.settimeout(…)）",
    "DP-55": "环境变量读取入口不统一（os.environ[k] 缺省抛 KeyError、os.getenv 缺省返 None）：统一 os.environ.get(key, default) 显式声明缺省语义；os.getenv 从无第三参数，多传实参即 TypeError",
    "RB-01": _MUTABLE_DEFAULT_GUIDANCE,
    "RB-03": _OPEN_WITH_GUIDANCE,
    "RB-04": "except 块内仅 return None 会吞没异常：应记录/处理异常或向上重新抛出",
    "RB-11": "文件对象未显式关闭：使用 with 语句管理生命周期，或补 close() 调用",
    "RB-14": "列表推导式中不应调用有副作用的函数：改用显式 for 循环确保副作用可见性",
    "RD-01": "raise 新异常未链原始异常：改为 raise NewError(...) from err 保留异常链与堆栈",
    "RD-03": "float 直接 == 比较有精度陷阱：替换为 math.isclose(a, b)",
    "RD-05": "subprocess 调用无超时会永久挂起：添加 timeout=N 参数并处理 TimeoutExpired",
    "RD-06": "except 块中仅 print/log 异常不够：应采取修复/重试/上报等实质措施，或向上重新抛出",
    "RD-08": "超过 2 层 try/except 嵌套应重构：提取子函数/使用上下文管理器/合并异常处理",
    "RD-12": "低效循环（len() 反复调用）/重复计算/不必要列表创建/字符串拼接：使用生成器/缓存/列表推导",
    "RD-15": "except Exception 过于宽泛：捕获具体异常类型（ValueError/TypeError 等）并添加有效处理逻辑",
    "RD-17": "嵌套函数定义达到 3 层（>=3）应提取为模块级函数，降低闭包复杂度",
    "RD-19": "修复函数应在应用修复后验证目标问题已解决",
    "RD-23": "函数体 >50 行应拆分为职责单一的小函数",
    "CM-01": _OPEN_WITH_GUIDANCE,
    "CO-01": "os.remove/os.rmdir 直接删除（不可恢复，路径错误即误删）：删除前校验路径边界与存在性，优先改用可恢复删除（先备份/进回收站）；批量清理先 dry-run 打印目标列表",
    "DB-01": "SQLite 连接在异常路径中未关闭可能导致资源泄漏：在 finally 块中调用 conn.close()；with sqlite3.connect(...) as conn 只管理事务提交/回滚，不会自动关闭连接，需要 with 时组合 contextlib.closing(sqlite3.connect(...)) 与事务管理以确保关闭",
    "FN-01": "函数参数超过 7 个降低可读性：使用参数对象（@dataclass）或 **kwargs/Builder 模式",
    "GL-01": "模块级可变全局变量（list/dict/set）易导致线程安全和测试隔离问题：使用类封装或配置对象",
    "MC-01": "循环引用 + __del__ 可能导致 GC 无法回收：使用 weakref 或移除 __del__，改用上下文管理器",
    "RC-01": "__del__ 中访问外部资源（文件/网络/数据库）不可靠：使用上下文管理器（__enter__/__exit__）替代",
    "RL-01": "except 块中应释放资源（close/release/disconnect）：在 finally 块中统一释放或使用 with 语句",
    "TX-01": "函数返回多种类型（int/str/list/None）违反接口契约：统一返回类型或使用 Union 类型标注",
    "TY-01": "公开函数参数缺类型注解：按默认值推断补注解（None→X | None、str 字面量→str、容器字面量→list/dict），返回值以 -> 标注；except 宽泛语义由 RD-15 承接",
    "BZ-01": "if x == True / x == False 布尔陷阱：仅当 x 已知为 bool 时才简化为 if x / if not x；严格单例判定用 is True / is False。自定义 __eq__ 或 truthy 非 bool 值不得机械改写，否则分支语义可能变化",
    "DG-01": "dict.get(k, 可变默认值).append()/update() 等原地修改作用于键缺失时创建的临时对象，结果不会写回字典：按原默认值类型改用 d.setdefault(k, [])、d.setdefault(k, {}) 或 d.setdefault(k, set()) 后操作，或 if k not in d 时初始化同类型对象；不要用 d.get(k) or 新容器，它会把已有空容器等假值替换成新对象，同样可能丢失修改",
    "EN-01": "open() 未指定 encoding（依赖平台默认编码，Windows cp936 下读 UTF-8 文件即 UnicodeDecodeError）：文本模式统一补 encoding='utf-8'（与 IN-01/IO-05 共享判定内核，修复口径一致）",
    "IN-01": "open() 文本模式缺 encoding（依赖平台默认编码，Windows cp936 读 UTF-8 文件即 UnicodeDecodeError）：补 encoding='utf-8' 或改用 pathlib.Path.read_text(encoding='utf-8')；与 EN-01 同内核同口径（PEP 597）",
    "B09": "循环内字符串拼接（f-string/+= 累积，O(n²)）：改为列表 append + ''.join(parts) 一次性拼接；与 SJ 族指导同口径",
    "IC-01": "相邻字符串字面量隐式拼接（无逗号/加号）：显式合并为一个字符串或补 + 号，避免漏逗号类 BUG 被掩盖",
    "LG-01": "from module import * 通配符导入：改为显式列出所用名称（需人工确认实际用量）",
    "IM-01": "引用未导入的标准库模块（如未 import os 就调 os.path.join，运行时 NameError）：在文件顶部补 import <模块> 或改用已导入模块的等价调用；批量替换/编辑误删 import 行是常见成因",
    "DG-02": "dict.update 同键覆盖（隐式数据丢失）：确认覆盖是否有意——状态流转改显式赋值 cfg['k'] = v 并注释；无意覆盖应删除较早的冗余写入、改用不同键，或按业务规则合并两个值（如列表 extend/数值累加），不要用一次 update 或字典展开掩盖覆盖；仅字面量键重叠才上报（变量合并键不可知不判）",
    "EX-08": "重复 except 处理块（不同异常类型、相同处理体）：合并为 except (Type1, Type2): 共用一个处理块，语义完全等价；若后续需差异化处理再拆分；裸 except 不参与合并（保留兜底语义）",
    "X3": "定时任务提示词含定时暗示词（每天/定时/提醒/循环/每隔等）：改写为一次性纯任务指令（如「查询北京今天的天气并生成报告」），周期性由调度配置表达；提示词中的定时暗示会让执行方再次创建定时任务，递归增殖成无限循环",
    "FS-02": "open() 写模式指向嵌套目录路径但作用域链无 makedirs/mkdir：写入前调用 os.makedirs(os.path.dirname(path), exist_ok=True)（幂等安全，目录已存在不报错）；目录确定已存在时可显式注释说明；当前目录写入与变量路径已由检测器豁免",
    "NS-01": "可空返回值链式访问（.get()/.find()/.search()/.match()/.fullmatch() 结果直接 .attr / [key] 访问）：先判空再访问 v = x.get(k); if v is not None: v.attr，或布尔守护 (x.get(k) or {}).get('sub')；re 结果 m = re.search(p, s) 后 if m: m.group(1)；.get(k, default) 的非 None 默认值只覆盖键缺失，键存在但值为 None 时仍会断链，不能据此豁免；os.environ.get 特例由 NT-02 专职处理",
    "LK-02": "多锁获取顺序不一致（死锁风险）：定义全局锁顺序常量，所有路径按相同顺序获取；或用 with a, b: 固定顺序",
    "LK-03": "锁临界区内耗时阻塞调用（持锁等待 IO）：耗时 IO 移出临界区——锁内取任务/快照，锁外执行 requests/subprocess，再锁内写回；确需同步等待时为调用加超时参数约束临界区时长",
    "FL-01": "非精确浮点字面量 ==/!= 比较（舍入误差致条件意外命中/永不命中）：改用 math.isclose(a, b, rel_tol=1e-9) 容差比较；金额等精确十进制场景改用 decimal.Decimal；0.5/1.0 等 2 的幂分母值精确可表示不报",
    "TY-03": "字符串与非 str 操作数直接拼接（TypeError）：拼接前显式 str(value)，或改用 f-string（自动调用 __format__）；str + 变量名形态静态不可判定，拼接前统一转换",
    "TP-26": "重试循环内网络调用无退避间隔（失败后立即重试形成请求风暴）：except 分支加 time.sleep(退避) 或指数退避（backoff 库 + jitter 抖动）；配 max_retries 上限防无限重试",
    "SP-01": "subprocess text=True 未指定 encoding：显式加 encoding='utf-8'（Windows 默认 GBK 解码非 ASCII 即 UnicodeDecodeError）",
    "TP-07": "模块级可变全局被原地修改（共享状态竞态）：改为函数内局部构建返回；确需共享用 tuple/frozenset + 显式重建或加锁访问器",
    "TP-05": "except 块引用未定义名称（异常路径触发 NameError 掩盖根因）：_log 形态补 import logging 与 _log = logging.getLogger(__name__)，或改用模块已导入的日志对象；其他未定义名补定义/导入后再引用",
    "FS-01": "os.getenv 无默认值参数（环境变量缺失返回 None，拼接抛 TypeError 或生成假路径）：os.getenv('X', default) 提供默认值；关键路径变量缺失应显式 raise 报错而非静默继续",
    "EP-02": "__init__.py 业务逻辑过多（>10 条模块级语句）：移到独立子模块，__init__.py 仅保留导入/dunder 声明/再导出；TYPE_CHECKING 与 __main__ 守卫块不计入",
    "TY-02": "Optional[X] | None 双重可选注解冗余：直接使用 Optional[X] 或 X | None 二选一（Optional[X] 本身已含 None）",
    "DF-03": "set 字面量与非集合字面量直接 &/|/^/- 运算（运行时 TypeError）：操作数统一为 set(...)；成员判定改用 in；双侧均为 set 字面量豁免",
    "WC-01": "finally 块中 raise 会覆盖正在传播的异常：finally 仅执行不抛异常的清理；在对应 except 中记录原错误并用 raise ... from err 链式抛出，成功路径也需要报错时单独保留显式分支；禁止把 finally 中的 raise 机械移动到 except",
    "IO-03": "httpx/aiohttp 请求未设 timeout：显式传 timeout=秒数（或 Timeout 对象），避免对端无响应时请求永久挂起",
    "IO-01": "requests 调用缺 timeout（对端无响应时永久阻塞）：显式传 timeout=30（连接/读取可分别用 (connect, read) 元组）并捕获 requests.Timeout 分支；与 IO-03（httpx/aiohttp）同族语义",
    "PT-01": "os.path.join 拼接用户可控路径存在穿越风险（OWASP A01）：resolve 后用 os.path.commonpath 或 pathlib.Path.relative_to 校验候选路径仍位于基目录；文件名白名单仅允许单个安全名称，禁止把字符串前缀拼接当作边界校验",
    "CV-01": "os.chmod() 权限过宽（0o777/0o666 等 group/other 可写）："
              + _CHMOD_MIN_PERMISSION_GUIDANCE
              + "（与检测器 chmod 语义及 Bandit B103 同口径）",
    "UH-01": "list/dict/set 不可哈希，作 dict 键或 set 元素运行时必然 TypeError：改用 tuple/frozenset 或以 str/哈希值作键",
    "EX-04": "同一 try 的多个 except 捕获重复类型（Ruff B014）：合并为单个 except (A, B) 或删除冗余分支",
    "AI-02": "MCP 协议工具调用面临投毒风险：校验工具名/参数来源白名单，不直接执行未审计的工具配置",
    "AW-03": "标准 ast 节点无 parent 属性：遍历时自行维护 parent 映射或改用 ast.walk 检索，不要访问 node.parent",
    "EN-03": "编码声明与内容不一致（非 UTF-8 家族 cookie 且含非 ASCII 字符）：移除非 UTF-8 声明（Python 3 默认 UTF-8）或统一文件编码",
    "GF-01": "全角标点混入：将代码中的全角标点替换为半角等价物；全角→半角精确映射：，（U+FF0C）→, 、（U+3001）→, ；（U+FF1B）→; ：（U+FF1A）→: （（U+FF08）→( ）（U+FF09）→)",
    "GF-02": "断裂 docstring（docstring 后紧跟第二段悬挂字符串常量）：核对是否为坏编辑残留；将应保留文本合并进前一段 docstring，或删除确认无用途的悬挂表达式，再用 AST 与定向测试复检，不要盲目在文件末尾补引号",
    "GF-03": "连续 3 行以上完全相同语句（疑似文本编辑残留）：先核对控制流、状态推进与副作用；仅确认语句无副作用且重复执行幂等时才删除多余副本，含调用、await/yield、I/O、随机数或迭代器推进时不得直接删除",
    "GF-04": "惰性导入冗余（标记 @lazy 但模块可直接导入）：移除惰性标记改为直接导入",
    "GF-08": "导入链级联断裂（try/except 静默吞错的脆弱链）：拆分为独立 import 或添加显式降级日志",
    "GF-09": "关键导入缺失（代码使用模块但未导入）：在文件头部补充缺失的 import 语句；优先恢复关键基础模块（os/sys/re/json/logging/datetime/sqlite3，缺失即崩溃面最大）",  # jwsgj:suppress 供应链安全-敏感路径 — 基础模块清单文本，非路径访问
    "GF-12": "管道产物完整性异常（语法错误/空文件/格式异常）：重新生成或修复产物格式",
    "GF-14": "重构后 API 覆盖率 <70%：对照接口清单补齐缺失实现",
    "GF-15": "函数体行数坍缩（有意义实现变为空壳）：恢复实现或确认为设计变更",
    "GF-16": "裸包内导入（绕过包层级直接 import）：改为经包 __init__ 的正确导入路径",
    "GF-17": "枢纽模块（被多模块引用）使用相对导入：改为绝对导入，避免消费方层级耦合",
    "GF-06": "孤立 except 块（try: 已被移除的残留）：核实后转换为注释或删除",
    "GF-07": "正则替换副作用：逐条核对真实函数签名与运行语义；sys.path.insert(index, object) 的 index 是必需参数，不得移除 index=0 或位置 0；仅删除经调用链确认无关且可去除的重复 keyword 参数，括号内赋值需人工确认",
    "GF-10": "悬挂缩进（块首行变更后内部缩进未跟随）：按块层级重新对齐并 AST 验证",
    "GF-18": "模块移动后相对导入点数不匹配：按新目录层级重算 from . / from .. 的点数",
    "GF-19": "传递依赖缺失导入：在文件头部补充缺失的 import（需人工确认来源模块）",
    "SL-06": "__init__.py 公共导出缺失：按来源补充 from .module import name（导出符号）或 from . import module（导出子模块）；已声明 __all__ 时同步登记，禁止留下缺少导入对象的 from . import",
    "SZ-02": "文件/函数体积接近阈值：文件级简化逻辑、消除重复并迁移无关职责；函数级提取私有实现，禁止直接拆分文件，防止继续膨胀",
    "BC-01": "断裂调用（需语义理解）：核对被调符号的真实签名后修复",
    "missing_docstring": "docstring 缺失：为函数/类补充 docstring 骨架（含参数与返回值摘要）",
    "unbounded_recursion": "无界递归：优先改为迭代；必须递归时增加明确基例与深度/输入规模守卫，不要通过 sys.setrecursionlimit 提高上限掩盖失控递归",
    "SEC-01": "代码注入风险：改用参数化/安全 API，杜绝拼接执行",
    "SEC-02": "SQL 注入风险：使用参数化查询，禁止字符串拼接 SQL",
    "SEC-03": "硬编码凭据：将明文凭据（sk-/pk-/AKIA/ghp_ 前缀 API Key、password=/secret= 明文赋值）替换为 os.environ.get(\"VAR_NAME\") 引用并在部署环境注入；检测规则配置中的示例 token 与 token 计数变量（total_token/estimated_token 等）为已知误报形态，确认非真实密钥后可加 # noqa: B106 抑制",
    "SEC-04": "弱加密算法：升级到 AES-256/GCM 等现代算法",
    "SEC-05": "弱随机数：安全场景使用 secrets 而非 random",
    "SEC-06": "路径穿越安全：规范化并校验路径边界",
    "SEC-GEN": "通用安全审查建议：按具体发现评估攻击面",
    "B101": _ASSERT_VALIDATION_GUIDANCE,
    "CA-01": _ASSERT_VALIDATION_GUIDANCE,
    "BE-01": "裸/空 except：裸 except 会连 SystemExit/KeyboardInterrupt 一并吞掉，改为捕获具体异常类型（ValueError/TypeError 等）并添加有效处理逻辑（记录/重试/上报，口径同 RD-15）；确需兜底时用 except Exception 且处理体不可为空",
    "SB-01": "遮蔽内置名称：将命名为 list/dict/set/type/id/input/file/filter/map/len/open/str/int/sum/min/max 等内置名的参数、变量或导入重命名为尾下划线安全名（list→list_、dict→dict_、type→type_，与 B19 检测器建议口径一致，尾下划线防风格冲突）或语义化名称（items/mapping/data_type）；ruff F402 导入遮蔽与 E741 模糊变量名同源，替换需全文件词边界一致执行避免半改；同语义规则 RB-02（B19）",
    "NC-01": _NONE_COMPARISON_GUIDANCE,
    "MDA-01": _MUTABLE_DEFAULT_GUIDANCE,
    "PY-11": "重复参数名：同一函数签名内参数名重复（如 def f(a, a) 或 def f(a=1, a=2)），Python 解析即报 SyntaxError，模块不可导入；删除或重命名重复参数，保持签名唯一",
    "PF01": "纯转发层：函数仅原样转发调用且无校验/转换/副作用，或模块仅做重导出；内联调用方直连目标，或补充真实逻辑（校验/转换/缓存）并在文档中说明委托的架构原因",
    "T18-MAGIC-NUMBER": "魔法数字：提取为命名常量（CONST_ 前缀模块级常量约定；安全数字 {0,1,2,-1} 豁免；跳过 __all__/__version__/VERSION/注释行/logging. 行防误改元数据与日志格式）",
    "D21-CMA": "跨模块赋值建议：收敛为显式接口调用",
    "D21-SM": "sys.modules 操作建议：核对模块真实加载路径",
    "D35-SILENT-FALLBACK": "静默降级增强建议：为回退路径补充告警日志与理由",
    "D38-PATH-RESOLVE": "文件路径解析建议：使用 os.path 规范化路径",
    "HP-GEN": "通用启发式模式建议：按具体发现人工评估",
    "HP-003": "模块级可变变量：转为不可变或添加保护",
    "HP-006": "嵌套深度过高：提取内层逻辑为独立函数",
    "AP-C2": "函数级延迟导入（信息级提示）：非循环依赖/启动耗时场景应提升为模块顶部直接导入；确因规避循环依赖或加速冷启动而保留时补充注释说明理由（延迟导入属设计模式而非缺陷，不强制修复）",
    "AP-C8": "死代码 __init__：移除无消费者的初始化残留",
    "AP-C18": "重复默认参数：把多处同值默认参数收敛为共享常量/配置项（模块级 DEFAULT_* 或 Settings），各函数引用同一来源；仅当默认值确属同一配置语义时合并，避免把不同业务含义的同值参数强行耦合",
    "AP-C19": "纯转发层：模块公开函数仅原样转发时，删除包装层让调用方直连目标，或补充真实职责（校验/转换/缓存/默认值收敛）；单函数粒度已由 PF01 覆盖，本条是模块级结构提示",
    "mutable_global": "模块级可变全局变量：改为类封装或不可变结构",
    "RUFF-UP006": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["UP006"],
    "RUFF-UP045": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["UP045"],
    "RUFF-UP037": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["UP037"],
    "RUFF-UP032": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_SAFE]["UP032"],
    "RUFF-UP031": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["UP031"],
    "RUFF-RUF010": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_SAFE]["RUF010"],
    "RUFF-F541": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_SAFE]["F541"],
    "RUFF-F821": "未定义名称：补导入或修正拼写",
    "RUFF-F811": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["F811"],
    "RUFF-F841": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["F841"],
    "RUFF-I001": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["I001"],
    "RUFF-S110": "try-except-pass：为静默吞异常补充日志或注释理由",
    "RUFF-RUF013": "隐式 Optional：显式标注 Optional[X]",
    "RUFF-RUF059": "未使用解包变量：不需要的值改为 _ 或符合 lint.dummy-variable-rgx 的名称；保留解包表达式本身的副作用",
    "RUFF-PLW0211": "静态方法首参误名 self/cls：将首参重命名为语义化名称并保持参数个数与调用签名；确实需要实例/类上下文时才改普通方法或类方法并同步调用方",
    "RUFF-PLE0605": "__all__ 格式：改为字符串列表",
    "RUFF-DTZ005": "datetime.now() 无 tz：补充时区参数",
    "RUFF-DTZ006": "datetime.fromtimestamp() 无 tz：补充 tz=datetime.timezone.utc 等明确时区",
    "RUFF-G004": "logging f-string：改为惰性 % 格式化参数",
    "RUFF-PERF102": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["PERF102"],
    "RUFF-C403": "不必要 list comprehension：set(x for x in items) 改集合推导，或 set(items) 直接构造",
    "RUFF-LOG015": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["LOG015"],
    "RUFF-C401": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["C401"],
    "RUFF-SIM102": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["SIM102"],
    "RUFF-SIM103": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["SIM103"],
    "RUFF-RUF034": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["RUF034"],
    "RUFF-SIM118": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["SIM118"],
    "RUFF-SIM115": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["SIM115"],
    "RUFF-B023": "循环闭包陷阱：绑定循环变量快照后再捕获",
    "RUFF-F401": RUFF_DELEGATION_KNOWLEDGE[_DELEGATION_UNSAFE]["F401"],
    "BANDIT-B101": _ASSERT_VALIDATION_GUIDANCE,
    "SC-01": "subprocess.run/call/check_output 未设 timeout 会永久挂起：为命令调用添加 timeout=N 秒参数（如 subprocess.run(cmd, timeout=60)）并捕获 subprocess.TimeoutExpired 做超时处理",
    "NT-01": _NONE_COMPARISON_GUIDANCE,
    "RG-02": "re.compile() 在循环体内重复调用：每轮迭代都重新编译同一正则，浪费解析与编译开销。修复：把 re.compile(...) 提升到循环外只编译一次并复用（模块级常量或函数级局部变量）；模式需按迭代变量动态构造时，先评估能否改为常量前缀 + re.escape(...) 拼接，避免每轮编译",
    "RG-04": "正则中使用贪婪 .* 可能过度匹配：配合 DOTALL 或内联 (?s) 时 .* 会跨行吞掉过多内容，匹配范围失控。修复：改用非贪婪 .*?，或用字符集显式限定范围（如 [^\\n]*），或收窄 DOTALL 的作用范围（把 (?s) 限定到具体分组）",
    "CV-01b": "marshal 反序列化不可信数据：marshal 与 pickle 同为对象序列化协议，反序列化不可信字节流可构造任意对象导致代码执行。修复：跨信任边界的数据改用 json.loads 等安全序列化格式；确需 marshal 时仅限内部可信字节流并校验来源（哈希/签名），禁止处理网络或用户上传字节",
    "B108": _SYSTEM_TEMP_DIR_GUIDANCE,
}
SE_FIX_KNOWLEDGE: dict[str, str] = {
    "SE-01": (
        "危险函数调用 - eval()/exec()\n根因: eval()/exec()会执行任意Python代码, 攻击者可通过注入恶意字符串实现RCE(远程代码执行)。\n修复策略:\n1. 替换为ast.literal_eval()(仅解析字面量, 不执行代码):\n   ast.literal_eval('[1, 2, 3]')  # 安全, 仅解析列表\n2. 使用json.loads()解析JSON数据(推荐):\n   json.loads(json_string)  # 安全, 仅解析JSON\n3. 使用白名单数学表达式解析器: 只允许数字、运算符与明确函数，禁止直接 sympify/eval 用户输入\n4. 沙箱隔离(最后手段): 使用RestrictedPython限制可用命名空间\n参考: OWASP A03:2021 / CWE-95 / Bandit B307"
    ),
    "SE-02": (
        "Shell注入风险 - subprocess/os.system with shell=True\n根因: shell=True时, 命令字符串通过shell解释执行, 用户输入中的特殊字符(;|&$`)可被注入。\n修复策略:\n1. 使用列表参数+shell=False(首选):\n   subprocess.run(['grep', pattern, filename], shell=False)\n2. POSIX shell=True 的最后手段是用 shlex.join()/quote() 转义每个参数（Windows cmd.exe 不适用；首选仍为列表参数+shell=False）:\n   subprocess.run(shlex.join(['grep', pattern, filename]), shell=True)\n3. 替代os.system(): 使用subprocess.run()并指定shell=False\n4. 白名单校验: 对命令参数使用 if cmd not in ALLOWED_COMMANDS: raise ValueError\n参考: OWASP A03:2021 / CWE-78 / Bandit B605/B607"
    ),
    "SE-03": (
        "硬编码密钥/密码/Token (P1)\n根因: 敏感变量名(api_key/password/secret/token等)被赋予字符串字面量, 凭据随源码入库, 任何代码访问权即可泄露。\n修复策略:\n1. 环境变量注入(首选): key = os.environ.get('API_KEY')\n2. 密钥管理器: vault/kms/aws-secrets-manager 按需拉取\n3. 配置文件+权限隔离: 配置置于部署环境(chmod 0o600)不入版本库, .gitignore 排除\n4. 示例/调试凭据: 确认非真实密钥后改为占位形态或删除\n参考: OWASP A07:2021 / CWE-798"
    ),
    "SE-04": (
        "反序列化不可信数据 - pickle.loads() (P1)\n"
        "根因: pickle.loads()可执行任意代码, 反序列化不可信数据导致RCE。\n"
        "修复策略:\n"
        "1. 替换pickle为JSON: json.loads(data) (推荐, 跨语言兼容)\n"
        "2. 如必须用pickle, 添加类白名单\n"
        "参考: OWASP A08:2021 / CWE-502 / Bandit B301"
    ),
    "SE-05": (
        "检测f-string/format拼接SQL语句(Bandit B608/Semgrep).\n根因: f-string/format拼接SQL使输入直接嵌入SQL语句, 导致SQL注入。\n修复策略:\n1. 参数化查询(首选): cursor.execute('SELECT ... WHERE id = %s', (uid,))\n   sqlite3用?占位符, PostgreSQL用%s, SQLAlchemy用:text+命名参数\n2. ORM查询集: User.objects.filter(name=user_input)\n3. 白名单表名/列名: if table not in ALLOWED_TABLES: raise ValueError\n4. psycopg2.sql标识符转义(最后手段)\n参考: OWASP A03:2021 / CWE-89 / Bandit B608"
    ),
    "SE-06": (
        "检测os.path.join拼接外部输入(OWASP A01/CWE-22).\n根因: os.path.join拼接用户输入可构造../路径穿越, 访问预期外的文件。\n修复策略:\n1. 路径规范化+commonpath边界校验(首选):\n   base = os.path.realpath(base_dir)\n   safe_path = os.path.realpath(os.path.join(base, user_input))\n   if os.path.commonpath((base, safe_path)) != base: raise ValueError\n2. 使用Path.resolve()+relative_to()校验:\n   base = pathlib.Path(base_dir).resolve()\n   safe_path = pathlib.Path(base, user_input).resolve()\n   try: safe_path.relative_to(base)\n   except ValueError: raise ValueError('path escapes base')\n3. 白名单文件名: if filename not in ALLOWED_FILES: raise ValueError\n4. 拒绝..和绝对路径: if '..' in user_input or os.path.isabs(user_input): raise ValueError\n参考: OWASP A01:2021 / CWE-22（路径穿越无对应 Bandit 检查项，勿引临时文件类规则）"
    ),
    "SE-07": (
        "检测yaml.load()未指定Loader参数(Bandit B506).\n根因: yaml.load()不指定Loader时默认使用FullLoader(PyYAML 5.1+)或unsafe Loader, 可执行任意代码。\n修复策略:\n1. 使用yaml.safe_load()(首选): yaml.safe_load(data)  # 等价于 Loader=SafeLoader\n2. 显式指定SafeLoader: yaml.load(data, Loader=yaml.SafeLoader)\n3. 使用CSafeLoader(性能更优): from yaml import CSafeLoader\n4. 替换为JSON: json.loads(data) (无代码执行风险)\n参考: CWE-502 / Bandit B506 / PyYAML Security"
    ),
    "SE-08": (
        "检测subprocess调用使用shell=True(Bandit B602/B603).\n根因: shell=True使命令通过shell解释执行, 注入特殊字符(;|&$`)可执行任意命令。\n修复策略:\n1. 使用列表参数+shell=False(首选): subprocess.run(['cmd', 'arg1'], shell=False)\n2. 使用shlex.split()解析命令字符串: subprocess.run(shlex.split(cmd), shell=False)\n3. 如 POSIX 环境必须用 shell=True, 用 shlex.quote() 转义每个参数（Windows cmd.exe 不适用，必须优先列表参数+shell=False）\n4. 使用subprocess.run()替代os.system()/os.popen()\n参考: OWASP A03:2021 / CWE-78 / Bandit B602/B603"
    ),
    "SE-09": (
        "检测tempfile.mktemp()不安全使用(Bandit B306).\n根因: tempfile.mktemp()仅生成文件名不创建文件, 存在TOCTOU竞态(返回的文件名被攻击者抢先创建)。\n修复策略:\n1. 使用tempfile.mkstemp()(首选): fd, path = tempfile.mkstemp()\n2. 使用NamedTemporaryFile(推荐):\n   with tempfile.NamedTemporaryFile(delete=False) as f: f.write(data)\n3. 使用TemporaryDirectory: with tempfile.TemporaryDirectory() as tmpdir: ...\n参考: CWE-377 / Bandit B306"
    ),
    "SE-10": (
        "使用了hashlib.md5()弱哈希算法 (P1)\n根因: MD5存在已知碰撞攻击, 不适用于安全场景(密码存储/签名/完整性校验)。\n修复策略:\n1. 密码存储: 使用bcrypt/passlib/argon2-cffi: pwd_context.hash(password)\n2. 安全哈希(推荐): hashlib.sha256()或hashlib.sha512()\n3. HMAC签名: hmac.new(key, msg, hashlib.sha256).digest()\n4. 文件完整性: hashlib.sha256()替代md5sum\n5. 如需兼容MD5(遗留系统): hashlib.md5(data, usedforsecurity=False)\n参考: OWASP A02:2021 / CWE-327 / Bandit B324"
    ),
    "SE-11": (
        "使用了random模块生成安全令牌 (P1)\n根因: random模块使用Mersenne Twister PRNG, 状态可预测, 不适用于安全令牌/密码重置/会话ID。\n修复策略:\n1. 使用secrets模块(首选, Python 3.6+):\n   token = secrets.token_urlsafe(32)  # 安全随机URL安全令牌\n   secrets.token_hex(16)  # 安全随机十六进制\n2. 使用os.urandom(): os.urandom(32).hex()\n3. UUID4(如需UUID格式): uuid.uuid4() (基于os.urandom)\n参考: OWASP A02:2021 / CWE-330 / Bandit B311"
    ),
    "SE-12": (
        "shutil.unpack_archive()未校验ZIP绝对路径 (P0)\n根因: ZIP文件中的条目可包含../路径或绝对路径, 解压时写入预期外位置(Zip Slip攻击)。\n修复策略:\n1. 使用zipfile逐条校验(首选):\n   dest_root = os.path.realpath(dest)\n   with zipfile.ZipFile(path) as zf:\n       for member in zf.namelist():\n           resolved = os.path.realpath(os.path.join(dest_root, member))\n           if os.path.commonpath((dest_root, resolved)) != dest_root: raise ValueError\n       zf.extractall(dest_root)\n2. 使用tarfile时设置filter='data': tar.extractall(path, filter='data')\n3. 限制最大解压大小, 防止Zip Bomb\n参考: OWASP A01:2021 / CWE-22 / Snyk Zip Slip"
    ),
    "SE-13": (
        "webbrowser.open()未净化URL (P2)\n根因: webbrowser.open()把URL交给浏览器命令行处理, 以'-'开头的URL会被解析为浏览器选项(如 -d), 构成选项注入向量, 也可被用于开放重定向。\n修复策略:\n1. URL协议白名单: if not url.startswith(('http://', 'https://')): raise ValueError\n2. 使用urllib.parse.urlparse()校验: parsed = urlparse(url); if parsed.scheme not in ('http','https'): raise ValueError('unsupported URL scheme')\n3. 避免直接传递用户输入到webbrowser.open()\n参考: CWE-601 / CWE-88（属参数/选项注入，无对应 Bandit 检查项）"
    ),
    "SE-14": (
        "XML解析未限制嵌套深度 (P1)\n根因: 深度嵌套的XML可导致解析器栈溢出或内存耗尽(Billion Laughs攻击的变体)。\n修复策略:\n1. 使用defusedxml(首选): from defusedxml import ElementTree as ET\n2. 限制XML大小: 检查文件大小后再解析, 超过阈值拒绝\n3. 实体扩展须显式关闭: etree.XMLParser(resolve_entities=False, no_network=True); lxml 无 forbid_entities 参数(传入即 TypeError), 且 SE-19 检测器不认该写法, 仍会报 XXE\n4. 设置超时: 使用signal.alarm()或multiprocessing限制解析时间\n参考: CWE-776 / defusedxml文档（实体开关口径与 SE-19 同源）"
    ),
    "SE-15": (
        "base64.b64decode()未启用validate=True严格校验 (P1)\n根因: base64.b64decode()默认(validate=False)丢弃非Base64字符而非报错, 可用于绕过输入校验(如WAF)。\n修复策略:\n1. 添加validate=True: base64.b64decode(data, validate=True)\n2. 先校验再解码: if not re.match(r'^[A-Za-z0-9+/]*={0,2}$', data): raise ValueError\n3. URL安全Base64同样严格校验: base64.b64decode(data, altchars=b'-_', validate=True)\n参考: CWE-20（严格解码校验无对应 Bandit 检查项）"
    ),
    "SE-16": (
        "BaseCookie.js_output()未转义script标签 (P1)\n根因: BaseCookie.js_output()输出JavaScript document.cookie语句, 未转义可导致XSS。\n修复策略:\n1. 避免使用js_output(), 改用Set-Cookie HTTP头(推荐): response.set_cookie(key, value, httponly=True)\n2. 禁止把 html.escape(cookie.js_output()) 当作修复：HTML 转义不能保证 JavaScript 上下文安全，必须迁移到 Set-Cookie\n3. 设置HttpOnly和Secure属性: response.set_cookie(key, value, httponly=True, secure=True)\n参考: OWASP A03:2021 / CWE-79"
    ),
    "SE-17": (
        "pkgutil.get_data()资源参数未校验 (P1)\n根因: pkgutil.get_data()的resource参数未校验, 路径穿越可读取包外文件。\n修复策略:\n1. 白名单资源名: if resource not in ALLOWED_RESOURCES: raise ValueError\n2. 仅允许单段资源名: p=pathlib.PurePath(resource); if not resource or p.name != resource or p.drive or resource in {'.', '..'}: raise ValueError\n3. 使用importlib.resources(推荐, Python 3.9+): 先按1/2校验，再用 importlib.resources.files(pkg).joinpath(resource)；joinpath 本身不做包边界校验，禁止直接传入外部 resource\n参考: CWE-22 / OWASP A01:2021（importlib.resources.files 属 Python 3.9+ 库 API，无对应 PEP）"
    ),
    "SE-18": (
        "使用assert进行输入验证 (P1)\n根因: assert语句在python -O优化模式下被移除, 输入校验将完全失效。\n修复策略:\n1. 替换为if+raise(首选):\n   if not isinstance(data, str): raise TypeError('data must be str')\n   if len(data) > MAX_LEN: raise ValueError(f'data too long: {len(data)}')\n2. 使用Pydantic模型校验: class InputModel(BaseModel): data: str = Field(max_length=100)\n3. 使用typeguard运行时类型检查: @typechecked def func(data: str) -> ...\n4. 保留assert仅用于调试不变量(开发环境), 生产环境用if+raise\n参考: CWE-617 / Bandit B101"
    ),
    "SE-19": (
        "XML解析未禁用外部实体(XXE) (P0)\n根因: XML解析器默认处理外部实体, 攻击者可通过DTD读取本地文件/SSRF/DoS。\n修复策略:\n1. 使用defusedxml(首选): from defusedxml.ElementTree import parse; parse(xml_file)\n2. 禁用实体解析(lxml):\n   parser = etree.XMLParser(resolve_entities=False, no_network=True)\n3. 禁用DTD(xml.sax): from xml.sax.handler import feature_external_ges; parser.setFeature(feature_external_ges, False)\n4. 禁用外部参数实体: from xml.sax.handler import feature_external_pes; parser.setFeature(feature_external_pes, False)（标准库无 feature_external_general_entities/feature_external_parameter_entities 属性）\n参考: OWASP A05:2021 / CWE-611 / Bandit B317（xml_bad_sax）/ B320（xml_bad_etree）"
    ),
    "SE-20": (
        "动态执行用户输入的代码 (P0)\n根因: exec()/eval()执行用户输入的代码, 导致RCE(compile仅编译,结果流入eval/exec才危险)。\n修复策略:\n1. 完全移除exec/eval, 使用专用解析器(JSON/正则/模板引擎)\n2. 如需动态导入, 用importlib.import_module()+白名单:\n   if module_name not in ALLOWED_MODULES: raise ImportError\n3. 沙箱隔离: 使用RestrictedPython或separate subprocess限制可用操作\n4. 代码签名: 仅执行经过HMAC签名的代码\n参考: OWASP A03:2021 / CWE-94 / CWE-95"
    ),
    "SE-23": (
        "HTTP请求未验证SSL证书 (P1)\n根因: verify=False/ssl=False禁用SSL证书校验, 允许中间人攻击截获通信内容。\n修复策略:\n1. 始终使用verify=True(默认): requests.get(url, verify=True)\n2. 使用CA证书: requests.get(url, verify='/path/to/ca-bundle.pem')\n3. 使用certifi证书包: requests.get(url, verify=certifi.where())\n4. aiohttp: 不传 ssl=False; 自签名场景传 ssl.create_default_context(cafile=...)\n5. 如需自签名证书, 使用自定义CA而非禁用验证\n参考: OWASP A02:2021 / CWE-295 / Bandit B501"
    ),
    "SE-24": (
        "使用os.chmod()设置过于宽松的权限 (P1)\n根因: 设置777/666等世界可写权限, 允许任何用户修改文件。\n修复策略:\n1. " + _CHMOD_MIN_PERMISSION_GUIDANCE + "\n2. 私钥文件: os.chmod(path, 0o600)  # 仅owner可读写\n3. 可执行文件: os.chmod(path, 0o750)  # owner读写执行, 其他仅读执行\n4. 目录: os.chmod(path, 0o750)  # 避免世界可写\n5. 使用stat模块常量: os.chmod(path, stat.S_IRUSR | stat.S_IWUSR)\n参考: CWE-732 / Bandit B103"
    ),
    "SE-25": (
        "使用pickle.load()反序列化不可信数据 (P0)\n根因: pickle.load()可执行任意代码, 反序列化不可信数据导致RCE。\n修复策略:\n1. 替换为JSON(首选): json.loads(data) (无代码执行风险)\n2. 使用json+自定义解码器: json.loads(data, object_hook=custom_decoder)\n3. 如必须用pickle, 实现白名单Unpickler:\n   class SafeUnpickler(pickle.Unpickler):\n       def find_class(self, module, name):\n           if (module, name) not in ALLOWED: raise ValueError\n           return super().find_class(module, name)\n4. 数据签名验证: pickle.load前用hmac验证数据完整性\n参考: OWASP A08:2021 / CWE-502 / Bandit B301"
    ),
    "SE-26": (
        "使用tarfile.extractall()未校验路径 (P1)\n根因: tarfile.extractall()不校验成员路径, ../路径或绝对路径可写入预期外位置。\n修复策略:\n1. 使用filter='data'(Python 3.12+, 首选): tar.extractall(path, filter='data')\n2. 手动校验每个成员(兼容旧版本):\n   dest_root = os.path.realpath(path)\n   for member in tar.getmembers():\n       resolved = os.path.realpath(os.path.join(dest_root, member.name))\n       if os.path.isabs(member.name) or os.path.commonpath((dest_root, resolved)) != dest_root: raise ValueError\n3. 限制符号链接: 检查member.issym()和member.islnk()并拒绝\n4. 限制最大文件大小, 防止解压炸弹\n参考: OWASP A01:2021 / CWE-22 / CVE-2007-4559"  # jwsgj:suppress SS-02 — 修复知识文本，非执行面
    ),
    "SE-27": (
        "使用httplib/urllib未设置超时 (P2)\n根因: 未设置超时的网络请求可被恶意服务器无限阻塞, 导致DoS。\n修复策略:\n1. 使用requests+timeout(推荐): requests.get(url, timeout=(3.05, 30))\n2. urllib.request: urllib.request.urlopen(url, timeout=30)\n3. http.client: http.client.HTTPConnection(host, timeout=30)\n4. 套接字粒度: socket.create_connection((host, port), timeout=30) 或 conn.settimeout(30)；勿用 socket.setdefaulttimeout() 改全进程默认值（对已建连接无效且隐式耦合，见 DP-54）\n参考: CWE-400 / Bandit B113"
    ),
    "SE-28": (
        "使用print输出敏感信息 (P2)\n根因: print()输出敏感信息到stdout, 日志收集器/终端记录/异常堆栈均可泄露。\n修复策略:\n1. 移除敏感信息的print(首选): 删除或注释掉调试输出\n2. 使用logging+脱敏: logger.info('user_id=%s', mask_sensitive(user_id))\n3. 脱敏函数: " + _SENSITIVE_VALUE_MASK_EXAMPLE + "\n4. 调试开关只控制脱敏元数据: if os.getenv('DEBUG') == '1': logger.debug('metadata=%s', mask(metadata))；禁止打印原始敏感值\n参考: OWASP A09:2021 / CWE-532"
    ),
    "SE-29": (
        "使用requests未设置User-Agent (P3)\n根因: 默认User-Agent暴露requests版本, 可被WAF识别拦截或用于指纹攻击。\n修复策略:\n1. 设置自定义UA: headers={'User-Agent': 'MyApp/1.0'}; requests.get(url, headers=headers)\n2. 使用Session统一设置: session = requests.Session(); session.headers['User-Agent'] = 'MyApp/1.0'\n3. 模拟浏览器UA: 'Mozilla/5.0 ...' (爬虫场景)\n参考: CWE-693 / requests文档"
    ),
    "SE-30": (
        "正则表达式ReDoS风险 - 嵌套量词灾难性回溯 (P1)\n"
        "根因: 嵌套量词与量词修饰的分组在回溯时产生指数级路径组合, 恶意输入可触发灾难性回溯致拒绝服务。\n"
        "修复策略:\n"
        "1. 消除嵌套量词: 重写模式, 避免 (a+)+ /(a*)* 等量词嵌套与量词修饰的捕获分组\n"
        "2. 使用原子组 (?>...) 或占有量词 (a++/a*+) 阻断回溯: Python 3.11+ 标准 re 支持, 旧版本需 regex 第三方库\n"
        "3. 对匹配设置输入长度上限与超时: 超长输入直接拒绝, 防灾难性回溯占满 CPU\n"
        "4. 预编译固定模式并限制输入域: 白名单字符集先行校验再进正则\n"
        "参考: CWE-1333 / OWASP ReDoS Prevention"
    ),
    "SE-30b": (
        "裸 popen() 执行动态构造命令 (P1)\n根因: from os import popen 的命令经 shell 解释, 外部输入可注入任意命令(分号/管道/反引号)。\n修复策略:\n1. 改用 subprocess.run(shlex.split(cmd), shell=False, check=True)\n2. POSIX shell 必须拼接时才对每个外部输入 shlex.quote（Windows cmd.exe 不适用；优先列表参数+shell=False）\n参考: CWE-78 / Bandit B605"
    ),
    "SE-31": (
        "使用cryptography库已弃用的危险API (P2)\n根因: 弃用API可能存在已知漏洞或不安全默认值, 新版本可能移除支持。\n修复策略:\n1. 迁移到新API(推荐): 查阅cryptography文档Migration Guide\n2. 使用hazmat前确认必要性: 低层hazmat API需专业知识, 优先用高层API\n3. 升级cryptography库: pip install --upgrade cryptography\n4. 使用Fernet对称加密(推荐): from cryptography.fernet import Fernet\n参考: CWE-477 / cryptography deprecation guide"
    ),
    "SE-32": (
        "SQL查询中直接使用f-string/format拼接 (P0)\n根因: f-string/format拼接SQL使输入直接嵌入SQL语句, 导致SQL注入。\n修复策略:\n1. 参数化查询(首选): cursor.execute('... WHERE id = %s', (uid,))\n2. ORM查询集: User.objects.filter(name=user_input)\n3. SQLAlchemy text()绑定参数: session.execute(text('... :name'), {'name': val})\n4. 白名单标识符: 对表名/列名使用白名单校验\n参考: OWASP A03:2021 / CWE-89 / Bandit B608"
    ),
    "SE-33": (
        "使用http而非https传输敏感数据 (P1)\n根因: HTTP明文传输, 网络中间人可截获/篡改敏感数据(密码/Token/PII)。\n修复策略:\n1. 使用HTTPS(首选): 将http://替换为https://\n2. 强制重定向: HTTP请求自动301重定向到HTTPS\n3. HSTS头: response.headers['Strict-Transport-Security'] = 'max-age=31536000'\n4. 校验URL协议: if not url.startswith('https://'): raise ValueError\n参考: OWASP A02:2021 / CWE-319"
    ),
    "SE-34": (
        "使用telnetlib传输明文凭据 (P0)\n根因: Telnet协议明文传输所有数据包括密码, 可被网络嗅探截获。\n修复策略:\n1. 使用SSH替代(首选): paramiko.SSHClient() / asyncssh.connect()\n2. 使用SFTP替代Telnet文件传输: paramiko.SFTPClient\n3. telnetlib已在Python 3.11标记弃用, 3.13移除, 必须迁移\n4. 如必须用Telnet, 通过VPN/SSH隧道加密传输\n参考: OWASP A02:2021 / CWE-319 / PEP 594"
    ),
    "SE-35": (
        "str.format() 变量注入风险\n根因: str.format()可访问对象的属性和嵌套字段, 用户控制的格式字符串可泄露敏感属性。\n修复策略:\n1. 使用固定格式字符串(首选): 字面量模板 '...{name}...'.format(name=user_input) 而非 template.format(...)（模板可控即注入面）\n2. 固定模板+受限映射: 字面量模板 '{name}'.format_map(SafeDict(data))，模板不得来自用户\n3. 使用string.Template(安全): Template('$name').substitute(name=user_input)\n4. 使用Jinja2模板引擎(复杂场景): 自动转义+沙箱\n参考: CWE-134 / Python format string vulnerability"
    ),
    "SE-36": (
        "日志输出敏感信息 (P1)\n根因: 敏感字段(密码/令牌/个人数据)直接进入日志, 日志收集器/终端记录/异常堆栈均可泄露。\n修复策略:\n1. 移除敏感字段或脱敏输出(首选): logger.info('user=%s', mask(user))\n2. 脱敏函数: " + _SENSITIVE_VALUE_MASK_EXAMPLE + "\n3. logging.Filter 按字段屏蔽敏感键\n4. 长值截断保护: 防完整凭据落盘\n参考: OWASP A09:2021 / CWE-532"
    ),
    "SE-37": (
        "高级SQL注入-多绕过向量 (P0)\n根因: 字面量模板 .format(x)/f-string 拼接SQL、动态拼接标识符(表/列名)、注释终止符(--/*)截断谓词等绕过基本转义的注入形态, 输入直接嵌入SQL语句。\n修复策略:\n1. 参数化查询(首选): cursor.execute('SELECT ... WHERE id = %s', (uid,))\n2. 标识符白名单: 动态表/列名走 if name not in ALLOWED: raise ValueError\n3. 拒绝拼接模板: 字面量模板 .format(x)/f-string 构造SQL一律改参数化\n4. 校验注释符: 输入含 -- 或 /* 时拒绝或转义\n参考: OWASP A03:2021 / CWE-89 / Bandit B608"
    ),
    "SE-38": (
        "跨文件污点传播-输入流入危险汇聚点 (P1)\n根因: 用户输入或外部数据经函数调用链传播到危险汇聚点(exec/eval/SQL执行)未经过净化, 攻击者可构造恶意输入实现代码注入/SQL注入/命令注入。\n修复策略(按优先级):\n1. 汇聚点参数化查询替代字符串拼接(SQL参数化)\n2. 数据入口添加输入净化(白名单过滤/类型校验)\n3. 安全API替代危险函数(subprocess.run([...], shell=False)替代os.system；shlex.quote仅限POSIX shell不得已场景，不能替代执行API)\n4. 输出编码防XSS(html.escape)\n参考: OWASP A03:2021-Injection / CWE-89 / CWE-78 / Bandit B608"
    ),
    "SE-39": (
        "框架上下文感知安全风险 - 检测框架特定安全反模式\n根因: 代码使用了框架特定的不安全API或反模式,如Django的raw()SQL执行、Flask的render_template_string(XSS风险)、FastAPI的未验证重定向,绕过了框架内置的安全防护机制。\n修复策略(按优先级):\n1. 替换为框架推荐的安全API(Django ORM替代raw()/Jinja2自动转义替代render_template_string)\n2. 启用框架安全中间件(Django SecurityMiddleware/Flask-Talisman)\n3. 配置CSP(内容安全策略)头限制脚本来源\n4. 使用框架内置的CSRF保护机制\n代码示例:\n  # Django: 修复前 - User.objects.raw(f\"SELECT * WHERE name='{name}'\")\n  # Django: 修复后 - User.objects.filter(name=name)\n参考标准: OWASP A04:2021-Insecure Design / CWE-1004(框架安全配置) / Bandit B703"
    ),
    "SE-40": (
        "符号执行漏洞验证 - 可达路径中存在安全约束违反\n根因: 通过符号执行验证发现特定输入组合下存在可达的安全约束违反路径,程序缺少输入边界检查或约束验证,在极端输入条件下可能触发未处理的安全漏洞(缓冲区溢出/整数溢出/空指针解引用)。\n修复策略(按优先级):\n1. 在函数入口添加输入边界检查(范围/类型/长度校验)\n2. 添加显式前置校验: if not 0 <= value < MAX_SIZE: raise ValueError(...)（与 SE-18 一致，不使用会被 -O 移除的 assert）\n3. 使用 pydantic 校验模型或 TypeAdapter 做运行时验证（typing.cast 仅约束静态类型，不校验运行时值）\n4. 对关键路径添加不变量检查(invariant check)\n代码示例:\n  # 修复前: def process(data): return buffer[data['offset']]\n  # 修复后: def process(data):\n  #     offset = data['offset']\n  #     if not isinstance(offset, int) or offset < 0 or offset >= len(buffer):\n  #         raise ValueError(f\"Invalid offset: {offset}\")\n  #     return buffer[offset]\n参考标准: SAST-Symbolic Execution / CWE-20(输入验证不当) / CWE-125(越界读取)"
    ),
}
