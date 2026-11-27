from __future__ import annotations

import logging
from collections.abc import Callable, Iterable, Mapping
from typing import Any

from jwsgj.build_refactor_policy import GOVERNANCE_CONSTRAINTS
from jwsgj.cleanup_file_hygiene import get_stub_constraints
from jwsgj.diag_gate_arch import D_ARCH_CONSTRAINTS
from jwsgj.diag_guard_injection_enforce import get_size_guard
from jwsgj.diag_types_normalize import safe_confidence
from jwsgj.diag_types_vocab import (
    DIAGNOSE_TO_P,
    FIELD_SUGGESTED_VALUE,
    HALLUCINATION_NORMS,
    SEVERITY_RANK,
    NormSeverity,
    register_review_provider,
)
from jwsgj.prevention_refs_main import (
    CODE_REFS,
    CodeRef,
    norm_rule_id,
    resolve_code_ref,
)
from jwsgj.retrospective_evolution import collect_diagnostic_defense_signals

__all__ = [
    "BUG_ANTIPATTERN_CONSTRAINTS",
    "OVERENGINEERING_CONSTRAINTS",
    "TASK_PREFERRED_SERIES",
    "attach_code_refs",
    "get_constraints_for_task",
    "get_dynamic_defense_constraints",
    "inject_code_refs_to_prompt",
    "inject_dynamic_defense_to_prompt",
    "inject_full_prevention_prompt",
    "inject_norms_to_prompt",
]
_log = logging.getLogger(__name__)
_log.info("hallucination_prewrite 编写前预防注入域已加载: %d 项导出", len(__all__))
BUG_ANTIPATTERN_CONSTRAINTS: list[dict[str, str]] = [
    {"rule_id": "B01", "name": "禁止可变默认参数", "severity": "ERROR",
     "description": "函数默认参数不得为 list/dict/set 或 list()/dict()/set() 调用，否则跨调用共享可变状态",
     "suggestion": "默认值用 None，函数体内再初始化"},
    {"rule_id": "B02", "name": "禁止资源泄漏", "severity": "ERROR",
     "description": "open() 等资源获取必须使用 with 上下文管理，确保异常路径也释放资源",
     "suggestion": "使用 with open(...) as f:"},
    {"rule_id": "B03", "name": "禁止裸 except", "severity": "WARN",
     "description": "except 必须指定异常类型，裸 except 会捕获 KeyboardInterrupt/SystemExit 等所有异常",
     "suggestion": "明确捕获具体异常，如 except (ValueError, KeyError)"},
    {"rule_id": "B04", "name": "禁止 finally 控制流", "severity": "ERROR",
     "description": "finally 块中禁止 return/break/continue，否则吞掉异常或改变控制流",
     "suggestion": "将 return/break/continue 移出 finally 块"},
    {"rule_id": "B05", "name": "None 比较用 is", "severity": "WARN",
     "description": "与 None 比较必须用 is / is not，而非 == / !=",
     "suggestion": "改为 is None / is not None"},
    {"rule_id": "B06", "name": "禁止未使用变量", "severity": "WARN",
     "description": "变量赋值后必须被读取，未使用变量是冗余或遗漏使用处的信号",
     "suggestion": "移除未使用赋值，或补上遗漏的使用处"},
    {"rule_id": "B07", "name": "禁止循环中修改迭代对象", "severity": "ERROR",
     "description": "for 迭代列表/字典时禁止对其 append/remove/pop/下标赋值，否则跳元素或死循环",
     "suggestion": "迭代副本 for x in list(items) 或先收集再修改"},
    {"rule_id": "B08", "name": "禁止 is 比较字面量", "severity": "WARN",
     "description": "is/is not 用于身份比较，比较字面量/非单例对象（数字/字符串/列表/字典）应用 ==/!=",
     "suggestion": "改用 == / != 比较值"},
    {"rule_id": "B09", "name": "禁止循环内字符串拼接", "severity": "WARN",
     "description": "循环内 s += ... 反复创建新字符串，应收集到列表后 join",
     "suggestion": "收集到 list 后用 ''.join()"},
    {"rule_id": "B10", "name": "禁止 __init__ 返回非 None", "severity": "ERROR",
     "description": "__init__ 方法禁止 return 非 None 值，否则触发 TypeError",
     "suggestion": "__init__ 隐式返回 None，移除 return 值"},
    {"rule_id": "B11", "name": "禁止循环延迟绑定", "severity": "ERROR",
     "description": "循环体/推导式中 lambda 或内嵌函数引用循环变量，闭包共享循环变量最终值",
     "suggestion": "用默认参数绑定当前值（lambda i=i: i）或 functools.partial"},
    {"rule_id": "B12", "name": "禁止可变类属性", "severity": "WARN",
     "description": "类体中 list/dict/set 属性被所有实例共享，应在 __init__ 中初始化为实例属性",
     "suggestion": "在 __init__ 中初始化 self.xxx = []"},
    {"rule_id": "B13", "name": "禁止异常静默吞掉", "severity": "WARN",
     "description": "except 块为空或仅 pass/continue，掩盖真实错误，应记录日志或重新抛出",
     "suggestion": "至少记录日志或 raise 重新抛出"},
    {"rule_id": "B14", "name": "禁止 type() 比较类型", "severity": "WARN",
     "description": "type(x) == Y 精确类型比较会排除子类实例，破坏多态",
     "suggestion": "改用 isinstance(x, SomeType)"},
    {"rule_id": "B15", "name": "禁止字面量除零", "severity": "ERROR",
     "description": "除法/整除/取模的除数为字面量 0，运行时必然抛 ZeroDivisionError",
     "suggestion": "增加除数非零校验，或用 try/except 捕获 ZeroDivisionError"},
    {"rule_id": "B16", "name": "禁止浮点等值比较", "severity": "WARN",
     "description": "用 == / != 比较浮点数，二进制浮点精度误差导致判断不可靠",
     "suggestion": "改用误差范围比较（abs(a - b) < epsilon）或 math.isclose()"},
    {"rule_id": "B17", "name": "禁止迭代器复用", "severity": "WARN",
     "description": "同一迭代器被多次消费（list()/next()/sum() 等），第二次起为空",
     "suggestion": "将迭代器一次性转为 list 再复用，或为每次消费重新创建迭代器"},
    {"rule_id": "B18", "name": "禁止未绑定变量复合赋值", "severity": "ERROR",
     "description": "函数内对未在局部作用域绑定的变量做 += 等复合赋值，运行时必然 UnboundLocalError（若引用外层变量需声明 nonlocal/global）",
     "suggestion": "在函数内先初始化变量，或声明 nonlocal/global 引用外层变量"},
    {"rule_id": "B19", "name": "禁止命名遮蔽内置", "severity": "WARN",
     "description": "参数或变量不得用 list/dict/str/id/type 等内置函数名，遮蔽后调用内置将报 TypeError",
     "suggestion": "内部变量直接改名；公开参数改名前须同步关键字调用方，避免破坏调用契约"},
    {"rule_id": "B20", "name": "禁止布尔冗余", "severity": "WARN",
     "description": "避免 if x == True / if x is True、return True if cond else False 等冗余写法",
     "suggestion": "直接用 truthiness：if x / if not x，或 return bool(cond)"},
    {"rule_id": "B21", "name": "禁止原地方法返回值误用", "severity": "ERROR",
     "description": "list/dict/set 的原地修改方法（sort/append/update/add 等）返回 None，return/yield 其调用结果将得到 None",
     "suggestion": "先调用原地方法再 return 对象本身，或返回期望的值（如 sorted()/副本）"},
    {"rule_id": "B22", "name": "禁止忽略字符串方法返回值", "severity": "WARN",
     "description": "字符串不可变，strip/replace/upper 等方法返回新字符串、不修改原串，作为独立语句丢弃结果则修改无效",
     "suggestion": "将结果赋回变量：s = s.strip()"},
    {"rule_id": "B23", "name": "禁止 get 结果未判空解引用", "severity": "WARN",
     "description": "dict.get(key) 在 key 不存在时返回 None，直接链式解引用（.attr/.method()/[idx]）会抛 AttributeError/TypeError",
     "suggestion": "先判空（if v is not None）或提供非 None 默认值 d.get(key, 默认值)"},
    {"rule_id": "B24", "name": "禁止可变对象共享", "severity": "ERROR",
     "description": "用乘法复制含可变元素的容器（如 [[0]*n]*m、[[]]*n、[{}]*n），list 乘法是浅拷贝，所有副本指向同一对象",
     "suggestion": "改用列表推导式创建独立副本，如 [[0 for _ in range(n)] for _ in range(m)]"},
    {"rule_id": "B25", "name": "禁止异常链丢失", "severity": "WARN",
     "description": "except 块内 raise 新异常未用 from 保留原始异常，导致 traceback 上下文被丢弃",
     "suggestion": "使用 raise NewError(...) from e 保留原始异常链"},
    {"rule_id": "B26", "name": "禁止未指定编码", "severity": "WARN",
     "description": "open() 缺 encoding 参数，Windows 默认 GBK、Linux 默认 UTF-8，跨平台读写结果不一致易乱码",
     "suggestion": "显式指定 encoding=\"utf-8\"（或文件实际编码）"},
    {"rule_id": "B27", "name": "禁止循环变量遮蔽", "severity": "WARN",
     "description": "嵌套循环内层 for 变量与外层同名，内层循环体内无法访问外层变量，易混淆语义",
     "suggestion": "重命名内层循环变量避免遮蔽"},
    {"rule_id": "B28", "name": "禁止返回内部可变状态", "severity": "WARN",
     "description": "方法直接 return self.attr 且 attr 在 __init__ 初始化为 list/dict/set，调用方拿到内部引用可绕过封装修改内部状态",
     "suggestion": "返回副本（self.attr.copy() 或 list(self.attr)），或改为只读视图/不可变类型"},
    {"rule_id": "B29", "name": "禁止 range(len()) 反模式", "severity": "WARN",
     "description": "for i in range(len(x)) 仅用 i 读取 x[i] 时，应直接迭代或 enumerate，避免冗余索引",
     "suggestion": "改为 for item in x，或 for i, item in enumerate(x) 同时需要索引与元素"},
    {"rule_id": "B30", "name": "禁止动态调用作默认参数", "severity": "ERROR",
     "description": "datetime.now()/random.random()/uuid.uuid4() 等每次返回不同值的函数作为默认参数，仅在定义时求值一次，跨调用共享同一冻结值",
     "suggestion": "默认值用 None，函数体内再调用 time/random/uuid 相关函数"},
    {"rule_id": "B31", "name": "禁止 assert 做参数校验", "severity": "WARN",
     "description": "函数内用 assert 校验参数，python -O 优化模式下被剥离、校验失效，应显式 raise ValueError/TypeError",
     "suggestion": "改用 if not isinstance(x, int): raise TypeError(...) 显式抛异常"},
    {"rule_id": "B32", "name": "禁止遍历时删除/更新容器", "severity": "ERROR",
     "description": "for 遍历容器时 del x[...] 或 d.update() 改变容器大小，字典触发 RuntimeError、列表跳元素",
     "suggestion": "先收集待删/待更新项，循环结束后统一处理，或遍历副本 for x in list(items)"},
    {"rule_id": "B33", "name": "禁止空容器判断用 len()", "severity": "WARN",
     "description": "len(x) == 0 / len(x) != 0 对内置容器是冗余写法，应直接用 if not x / if x 的 truthiness",
     "suggestion": "改为 if not x / if x"},
    {"rule_id": "B34", "name": "禁止正则匹配结果未判空解引用", "severity": "WARN",
     "description": "re.search/match/fullmatch(...) 无匹配返回 None，直接 .group()/.groups()/.span() 等链式解引用会抛 AttributeError",
     "suggestion": "先判空再取组: m = re.search(p, s); if m: v = m.group(1)"},
    {"rule_id": "B35", "name": "禁止补丁方式修复", "severity": "ERROR",
     "description": "修复一律定位根因并以根因消除方式修复（SSOT 归口/契约对齐/结构校正）；"
                    "禁止吞异常遮蔽、特判绕过、硬编码短路、只治症状不除根因的补丁式修复（强制行为："
                    "AI 审核执行环节写前补丁预检拦截，审核 verdict 打回）",
     "suggestion": "先归因根因再改代码，fixed_source 须与根因分析可对应；"
                    "吞异常遮蔽改根因修复，特判绕过改契约对齐，硬编码短路改 SSOT 归口"},
    {"rule_id": "B36", "name": "字面量解包数量错配", "severity": "ERROR",
     "description": "x, y = (1, 2, 3) 一执行即 ValueError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B37", "name": "惰性迭代器直接下标", "severity": "ERROR",
     "description": "map(f, xs)[0] 必 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B38", "name": "dict 视图对象直接下标", "severity": "ERROR",
     "description": "d.values()[0] 在 py3 必 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B39", "name": "len() 消费惰性迭代器", "severity": "ERROR",
     "description": "len(zip(a, b)) 必 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B40", "name": "raise 非异常对象", "severity": "ERROR",
     "description": "raise \"msg\"/raise 42/raise NotImplemented 必 TypeError",
     "suggestion": "按异常协议改写（raise 异常实例、except 类型表达式合法），编写后以 Gate3 自查"},
    {"rule_id": "B41", "name": "__repr__/__str__ 内格式化裸 self", "severity": "ERROR",
     "description": "f\"{self}\" 必无限递归",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B42", "name": "无效正则字面量", "severity": "ERROR",
     "description": "re.compile 非法模式一执行即 re.error",
     "suggestion": "修正正则模式（消除未闭合分组/非法量词），含元字符的字面文本先 re.escape，编写后以 Gate3 自查"},
    {"rule_id": "B43", "name": "显式关键字与 **dict 字面量键重复", "severity": "ERROR",
     "description": "f(**{\"a\": 1}, a=2) 必 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B44", "name": "数字构造字面量必失败", "severity": "ERROR",
     "description": "int(\"3.14\")/int(\"\")/float(\"abc\") 必 ValueError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B45", "name": "字面量容器下标越界", "severity": "ERROR",
     "description": "\"abc\"[5]/(1, 2)[5]/[1, 2][-3] 必 IndexError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B46", "name": "except 子句类型非法", "severity": "ERROR",
     "description": "except [ValueError]/except \"X\"/except None 必 TypeError",
     "suggestion": "按异常协议改写（raise 异常实例、except 类型表达式合法），编写后以 Gate3 自查"},
    {"rule_id": "B47", "name": "实例方法零参数漏 self", "severity": "ERROR",
     "description": "类中 def f(): 实例调用必 TypeError",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B48", "name": "property 存取器签名错", "severity": "ERROR",
     "description": "@property def x(self, extra) 调用即 TypeError",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B49", "name": "无参数 staticmethod 内零参 super()", "severity": "ERROR",
     "description": "一执行即 RuntimeError",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B50", "name": "match 重复 case 字面量模式", "severity": "ERROR",
     "description": "后一 case 永不可达",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B51", "name": "seq[len(seq)] 下标必越界", "severity": "ERROR",
     "description": "一执行即 IndexError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B52", "name": "模块级就地函数结果被消费", "severity": "ERROR",
     "description": "x = random.shuffle(lst) 所得恒 None",
     "suggestion": "原地函数（shuffle/sort 等）返回 None：先独立调用再使用原对象，或改用返回新值的 API，编写后以 Gate3 自查"},
    {"rule_id": "B53", "name": "子类重写 __init__ 未调父类初始化", "severity": "WARN",
     "description": "父类初始化逻辑静默丢失",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B54", "name": "async 函数内 time.sleep", "severity": "WARN",
     "description": "阻塞整个事件循环",
     "suggestion": "改用 asyncio 原生等待（await asyncio.sleep/持有任务引用），编写后以 Gate3 自查"},
    {"rule_id": "B55", "name": "asyncio.create_task 结果丢弃", "severity": "WARN",
     "description": "任务弱引用可能被 GC 提前取消",
     "suggestion": "改用 asyncio 原生等待（await asyncio.sleep/持有任务引用），编写后以 Gate3 自查"},
    {"rule_id": "B56", "name": "NaN 等值比较", "severity": "WARN",
     "description": "x == float(\"nan\") 恒假、x != nan 恒真",
     "suggestion": "改用 math.isnan(x) 判定，禁止与 float(\"nan\")/math.nan 做 ==/!=，编写后以 Gate3 自查"},
    {"rule_id": "B57", "name": "条件位海象绑定字面量", "severity": "WARN",
     "description": "if x := 5: 恒真守卫失效",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B58", "name": "裸 raise 在 except 上下文外", "severity": "ERROR",
     "description": "执行即 RuntimeError: No active exception to re-raise",
     "suggestion": "按异常协议改写（raise 异常实例、except 类型表达式合法），编写后以 Gate3 自查"},
    {"rule_id": "B59", "name": "__init__ 含 yield/yield from 或声明为 async", "severity": "ERROR",
     "description": "类实例化必 TypeError",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B60", "name": "dunder 协议方法返回字面量违反契约", "severity": "ERROR",
     "description": "调用即 TypeError/ValueError",
     "suggestion": "按类契约改写（补齐 self/父类初始化/协议方法返回类型），编写后以 Gate3 自查"},
    {"rule_id": "B61", "name": "isinstance/issubclass 第二参数非法", "severity": "ERROR",
     "description": "执行即 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B62", "name": "del 删除名后再次引用", "severity": "ERROR",
     "description": "执行即 NameError/UnboundLocalError",
     "suggestion": "修正名绑定生命周期（删除后不再引用），编写后以 Gate3 自查"},
    {"rule_id": "B63", "name": "max/min 对空字面量序列求值且无 default", "severity": "ERROR",
     "description": "必 ValueError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B64", "name": "正则匹配结果赋值后未判空解引用", "severity": "WARN",
     "description": "无匹配时 AttributeError",
     "suggestion": "先判空再取组（if m: v = m.group(1)），或提供默认值，编写后以 Gate3 自查"},
    {"rule_id": "B65", "name": "函数/方法引用未调用直接作条件", "severity": "WARN",
     "description": "可调用对象恒真，else 分支成死代码",
     "suggestion": "补上调用括号与实参（if len(items):），或显式比较 is not None，编写后以 Gate3 自查"},
    {"rule_id": "B66", "name": "next() 参数非法", "severity": "ERROR",
     "description": "非迭代器必 TypeError / 空迭代器必 StopIteration",
     "suggestion": "第一参数须为迭代器（next(iter(x))），空迭代器场景传默认值 next(it, None)，编写后以 Gate3 自查"},
    {"rule_id": "B67", "name": "input() 返回值直接数值运算", "severity": "ERROR",
     "description": "str 数值运算必 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B68", "name": "while True 循环体无任何退出路径", "severity": "ERROR",
     "description": "必死循环",
     "suggestion": "补齐循环退出路径，编写后以 Gate3 自查"},
    {"rule_id": "B69", "name": "字面量容器/字符串 .index() 查找必失败", "severity": "ERROR",
     "description": "ValueError 试算可定",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B70", "name": "不可变对象元素赋值", "severity": "ERROR",
     "description": "执行即 TypeError",
     "suggestion": "改为运行时可成立的形态（如修正数量/下标/构造参数），编写后以 Gate3 对应检测器自查"},
    {"rule_id": "B71", "name": "不可变容器调用不存在的修改方法", "severity": "ERROR",
     "description": "执行即 AttributeError",
     "suggestion": "不可变类型无 append/extend 等修改方法，改用拼接/构造新对象（\"abc\" + \"d\"），编写后以 Gate3 自查"},
    {"rule_id": "B72", "name": "调试器断点残留", "severity": "WARN",
     "description": "breakpoint()/pdb.set_trace() 进入交互阻塞",
     "suggestion": "移除 breakpoint()/pdb.set_trace()，改用日志或断言，编写后以 Gate3 自查"},
]
OVERENGINEERING_CONSTRAINTS: list[dict[str, str]] = [
    {"rule_id": "O01", "name": "禁止单一实现抽象基类", "severity": "WARN",
     "description": "抽象基类/接口只有一个（或零个）具体子类时，抽象层缺少多态变化，属过度设计",
     "suggestion": "合并到具体类，或确认确有多个子类需求"},
    {"rule_id": "O02", "name": "禁止无分支工厂", "severity": "WARN",
     "description": "工厂方法仅返回单一固定类型、无运行时选择逻辑时，工厂层是多余抽象",
     "suggestion": "直接用构造函数，或补充运行时分支选择"},
    {"rule_id": "O03", "name": "禁止未使用参数", "severity": "WARN",
     "description": "函数定义但从未使用的参数属过度参数化（YAGNI 违反），增加调用负担",
     "suggestion": "移除未使用参数，或以下划线前缀标记有意保留"},
    {"rule_id": "O04", "name": "禁止纯转发包装", "severity": "WARN",
     "description": "函数体仅原样转发调用、无额外逻辑，是多余间接层",
     "suggestion": "直接调用底层函数，或为包装层补充真实逻辑"},
    {"rule_id": "O05", "name": "禁止纯静态方法类", "severity": "WARN",
     "description": "所有方法均为 staticmethod/classmethod 且无实例状态的类，是过度设计，应改为模块级函数",
     "suggestion": "将方法提升为模块层普通函数，或用模块/命名空间组织"},
    {"rule_id": "O06", "name": "禁止单一方法类", "severity": "WARN",
     "description": "仅含一个普通实例方法且无状态、无继承的类，是多余抽象，应改为函数",
     "suggestion": "改为模块级函数"},
    {"rule_id": "O07", "name": "禁止深层继承", "severity": "WARN",
     "description": "继承链深度超过 3 层属过度设计，增加认知负担与脆弱基类问题，多数场景组合优于继承",
     "suggestion": "改用组合（composition）替代继承，或合并中间继承层级"},
    {"rule_id": "O08", "name": "禁止冗余 getter/setter", "severity": "WARN",
     "description": "get_xxx/set_xxx 仅做无校验/无转换/无副作用的属性读写，属过度设计样板代码",
     "suggestion": "移除冗余 getter/setter，调用方直接访问属性；如需封装改用 @property"},
]
_TASK_TYPE_FOCUS: dict[str, tuple[str, ...]] = {
    "default": (),
    "create_skill": ("G", "O"),
    "bugfix": ("B", "V", "R", "LV"),
    "refactor": ("O", "V", "R"),
    "security": ("G7", "V", "R"),
    "test": ("TT", "SK", "S0", "CV", "DM"),
    "data": ("LV", "RD", "AT", "DB", "NW", "SC"),
    "concurrency": ("AY", "LG", "NC", "GL", "MDA", "B"),
    "performance": ("TO", "RUFF", "CV", "RD", "SC"),
    "script": ("RUFF", "DM", "NW", "LG", "NC", "GL", "MDA"),
}
def _split_logic_ref_name(name: str) -> tuple[str, str]:
    head, sep, tail = name.partition("：")
    if sep:
        return head.strip(), tail.strip()
    return name.strip(), ""
_DEFAULT_TASK_TYPE = "default"
_DEFAULT_SKILL_DIR = ""
_SIZE_BUDGET_TASK_MAP: dict[str, str] = {
    "default": "code_write",
    "create_skill": "create",
    "bugfix": "fix",
    "refactor": "refactor",
    "security": "code_write",
    "test": "test_write",
    "data": "code_write",
    "concurrency": "code_write",
    "performance": "code_write",
    "script": "code_write",
}
def _normalize_task_type(task_type: Any) -> str:
    if not isinstance(task_type, str):
        return _DEFAULT_TASK_TYPE
    return task_type.strip().lower() or _DEFAULT_TASK_TYPE
def _task_type_row(table: Mapping[str, Any], task_type: Any) -> Any:
    key = _normalize_task_type(task_type)
    if key in table:
        return table[key]
    return table.get(_DEFAULT_TASK_TYPE)
TASK_PREFERRED_SERIES: dict[str, frozenset[str]] = {
    'default': frozenset({'bug', 'pytrap', 'trap', 'security', 'guardquality', 'netfix', 'logic'}),
    'create_skill': frozenset({'stub', 'norm', 'importextra', 'security', 'guard'}),
    'bugfix': frozenset({'bug', 'pytrap', 'trap', 'robust', 'robust_extra', 'asyncio', 'guardquality', 'logic'}),
    'refactor': frozenset({'arch', 'arch_extra', 'fileops', 'perf', 'overdesign', 'guard', 'logic'}),
    'security': frozenset({'security', 'netfix', 'halluc', 'deprecated', 'deprecated_ext', 'guard'}),
    'test': frozenset({'testquality', 'stub', 'cvmethod', 'diagmethod'}),
    'data': frozenset({'robustfix', 'trap', 'fileops', 'normtext', 'pytrap', 'netfix', 'logic'}),
    'concurrency': frozenset({'asyncio', 'guardfix', 'diagmethod', 'bug'}),
    'performance': frozenset({'perf', 'robustfix', 'rufffix', 'cvmethod'}),
    'script': frozenset({'guardfix', 'diagmethod', 'rufffix', 'normtext', 'netfix'}),
}
def _normalize_severity(value: Any) -> str:
    if not isinstance(value, str) or not value.strip():
        return "WARN"
    return value.strip().upper()
def _constraint_record(
    rule_id: str,
    rule_name: str,
    severity: str,
    description: Any,
    suggestion: str,
    category: str,
    *,
    source: str = "",
) -> dict[str, Any]:
    record = {
        "rule_id": rule_id,
        "rule_name": rule_name,
        "severity": _normalize_severity(severity),
        "description": description,
        "suggestion": suggestion,
        "category": category,
    }
    if source:
        record["source"] = source
    return record
def _governance_constraints() -> list[dict[str, Any]]:
    return [_constraint_record(item["rule_id"], item["name"],
                               item["severity"], item["description"],
                               item["suggestion"], "GOVERNANCE")
            for item in GOVERNANCE_CONSTRAINTS]
def _norm_constraints() -> list[dict[str, Any]]:
    return [_constraint_record(norm.rule_id, norm.name, norm.severity.value,
                               norm.description, norm.violation_consequence,
                               norm.category.value)
            for norm in HALLUCINATION_NORMS]
def _bug_constraint_severity(bug: dict[str, str]) -> str:
    ref = resolve_code_ref(bug["rule_id"])
    severity = getattr(ref, "severity", "") if ref is not None else ""
    return severity or bug["severity"]
def _bug_constraints() -> list[dict[str, Any]]:
    return [_constraint_record(bug["rule_id"], bug["name"],
                               _bug_constraint_severity(bug),
                               bug["description"], bug["suggestion"], "BUG")
            for bug in BUG_ANTIPATTERN_CONSTRAINTS]
def _overdesign_constraints() -> list[dict[str, Any]]:
    return [_constraint_record(od["rule_id"], od["name"], od["severity"],
                               od["description"], od["suggestion"],
                               "OVERDESIGN")
            for od in OVERENGINEERING_CONSTRAINTS]
def _stub_series_constraints() -> list[dict[str, Any]]:
    return [_constraint_record(sc["rule_id"], sc["name"], sc["severity"],
                               sc["description"], sc["suggestion"],
                               sc.get("category", "STUB"))
            for sc in get_stub_constraints()]
def _arch_constraints() -> list[dict[str, Any]]:
    return [_constraint_record(dc["rule_id"], dc["name"],
                               dc.get("severity", "WARN"), dc["description"],
                               dc["suggestion"], "ARCH")
            for dc in D_ARCH_CONSTRAINTS]
_LOGIC_SERIES = "logic"
def _logic_constraints() -> list[dict[str, Any]]:
    constraints: list[dict[str, Any]] = []
    for ref in CODE_REFS.values():
        if ref.series != _LOGIC_SERIES:
            continue
        ref_name, mechanism = _split_logic_ref_name(ref.name)
        constraints.append(_constraint_record(
            ref.rule_id, ref_name, ref.severity, mechanism or ref_name,
            ref.rationale, "LOGIC"))
    return constraints
_BUG_SECTION_TITLE = (
    f"### 三、BUG 反模式（{BUG_ANTIPATTERN_CONSTRAINTS[0]['rule_id']}-"
    f"{BUG_ANTIPATTERN_CONSTRAINTS[-1]['rule_id']}，从源头避免常见 BUG；"
    "B35 为禁止补丁方式修复强制行为）"
)
_OVER_SECTION_TITLE = (
    f"### 四、过度设计（{OVERENGINEERING_CONSTRAINTS[0]['rule_id']}-"
    f"{OVERENGINEERING_CONSTRAINTS[-1]['rule_id']}，避免过度抽象/过度工厂/"
    "纯静态类/单方法类/深层继承/冗余访问器）"
)
_LOGIC_SECTION_TITLE = (
    "### 七、逻辑缺陷预防（LV 系列，AI 高频一执行即错逻辑缺陷，"
    "与编写时 Gate5 检测器同口径）"
)
_STATIC_SERIES: tuple[
    tuple[str, bool, Callable[[], list[dict[str, Any]]]], ...] = (
    (_BUG_SECTION_TITLE, True, _bug_constraints),
    (_OVER_SECTION_TITLE, True, _overdesign_constraints),
    ("### 五、兼容桩/门户预防（S01-S03，重构/迁移后不留兼容桩与门户）",
     True, _stub_series_constraints),
    ("### 六、架构反模式（D 系列，与编写时反模式门禁同口径）",
     True, _arch_constraints),
    (_LOGIC_SECTION_TITLE, False, _logic_constraints),
)
def _static_series() -> list[tuple[str, bool, list[dict[str, Any]]]]:
    return [(title, with_suggestion, build())
            for title, with_suggestion, build in _STATIC_SERIES]
_SENTENCE_END = ("。", "！", "？", ".", "!", "?", "；", ";", "…")
def _ensure_sentence(text: str) -> str:
    body = text.rstrip()
    if not body:
        return ""
    return body if body.endswith(_SENTENCE_END) else f"{body}。"
_SEVERITY_LEVEL_LABELS: dict[str, str] = {
    "ERROR": "阻断",
    "P0": "阻断",
    "BLOCK": "阻断",
    "P1": "严重",
    "INFO": "提示",
}
_BLOCKING_SEVERITIES: frozenset[str] = frozenset({"P0", "ERROR", "BLOCK"})
_DEFAULT_LEVEL_LABEL = "警告"
def _constraint_line(item: dict[str, Any], with_suggestion: bool = True) -> str:
    severity = _normalize_severity(item.get("severity", ""))
    level = _SEVERITY_LEVEL_LABELS.get(severity, _DEFAULT_LEVEL_LABEL)
    line = (f"- [{item['rule_id']}] {item['rule_name']}（{level}）："
            f"{_ensure_sentence(str(item['description']))}")
    suggestion = item.get("suggestion")
    if with_suggestion and suggestion:
        line += _ensure_sentence(str(suggestion))
    return line
def _constraint_priority(item: dict[str, Any],
                        focus_series: Iterable[str] | str | None) -> int:
    rule_id = str(item.get("rule_id", ""))
    if rule_id.startswith("GOV"):
        return 0
    prefixes = ((focus_series,) if isinstance(focus_series, str)
                else tuple(focus_series or ()))
    return 1 if prefixes and rule_id.startswith(prefixes) else 2
def get_constraints_for_task(task_type: str = _DEFAULT_TASK_TYPE,
                             skill_dir: str = _DEFAULT_SKILL_DIR) -> list[dict[str, Any]]:
    task_type = _normalize_task_type(task_type)
    constraints: list[dict[str, Any]] = []
    constraints.extend(_governance_constraints())
    constraints.extend(_norm_constraints())
    for _title, _with_suggestion, items in _static_series():
        constraints.extend(items)
    if skill_dir:
        try:
            constraints.extend(get_dynamic_defense_constraints(skill_dir))
        except Exception as e:  # noqa: BLE001
            _log.warning("get_constraints_for_task: 动态防御约束合并失败（降级静态约束）: %s", e)
    focus = _task_type_row(_TASK_TYPE_FOCUS, task_type)
    constraints.sort(key=lambda item: _constraint_priority(item, focus))
    return constraints
def _precreation_constraint_lessons() -> list[dict[str, Any]]:
    lessons: list[dict[str, Any]] = []
    for item in get_constraints_for_task():
        if item.get("severity") not in _BLOCKING_SEVERITIES:
            continue
        rule_name = item.get("rule_name") or item.get("name") or ""
        rule_id = item.get("rule_id", "")
        description = item.get("description", "")
        lessons.append({
            "description": f"{rule_id}: {rule_name} — {description}",
            FIELD_SUGGESTED_VALUE: item.get("suggestion", ""),
            "source": "hallucination_prewrite",
            "target": "code_generation",
        })
    return lessons
register_review_provider("precreation_constraint_lessons",
                         _precreation_constraint_lessons)
def inject_norms_to_prompt(
    task_type: str = _DEFAULT_TASK_TYPE, skill_dir: str = _DEFAULT_SKILL_DIR,
) -> str:
    task_type = _normalize_task_type(task_type)
    lines: list[str] = []
    _append_section(lines, "## AI 代码编写约束（负面约束优先，违反即阻断）", ())
    _append_governance_section(lines)
    _append_norm_tier(lines, NormSeverity.P0, "### 一、阻断级铁律（P0，违反立即停止）")
    _append_norm_tier(lines, NormSeverity.P1, "### 二、严重级铁律（P1，必须修复）")
    _append_static_series(lines, task_type)
    lines.append("编写时逐条对照上述约束，任何 P0 阻断级或 ERROR 级问题必须在写盘前修复。")
    lines.append("")
    focus = _task_type_row(_TASK_TYPE_FOCUS, task_type)
    if focus:
        focus_desc = ", ".join(focus)
        lines.append(f"当前任务类型（{task_type}）侧重点："
                     f"优先关注 {focus_desc} 系列约束。")
        lines.append("")
    if skill_dir:
        try:
            dynamic_section = inject_dynamic_defense_to_prompt(skill_dir)
            if dynamic_section:
                lines.append(dynamic_section)
        except Exception as e:  # noqa: BLE001
            _log.warning("inject_norms_to_prompt: 动态防御段生成失败（降级静态提示词）: %s", e)
    return "\n".join(lines)
def _append_section(lines: list[str], heading: str,
                    bullets: Iterable[str]) -> None:
    lines.append(heading)
    lines.extend(bullets)
    lines.append("")
def _append_governance_section(lines: list[str]) -> None:
    _append_section(
        lines, "### 零、治理硬约束（GOV，优先级最高；违反即改写方案）",
        (f"- [{item['rule_id']}] {item['name']}："
         f"{_ensure_sentence(item['description'])}"
         f"{_ensure_sentence(item['suggestion'])}"
         for item in GOVERNANCE_CONSTRAINTS))
def _append_norm_tier(lines: list[str], severity: NormSeverity, heading: str) -> None:
    norms = [n for n in HALLUCINATION_NORMS if n.severity == severity]
    if norms:
        _append_section(
            lines, heading,
            (f"- [{norm.rule_id}] {norm.name}：{norm.description}"
             for norm in norms))
def _append_static_series(lines: list[str], task_type: str) -> None:
    for title, with_suggestion, items in _static_series():
        _append_section(
            lines, title,
            (_constraint_line(item, with_suggestion) for item in items))
    lines.append(get_size_guard().format_strong_constraint(
        _task_type_row(_SIZE_BUDGET_TASK_MAP, task_type)))
    lines.append("")
def get_dynamic_defense_constraints(skill_dir: str) -> list[dict[str, Any]]:
    signals = collect_diagnostic_defense_signals(skill_dir)
    constraints: list[dict[str, Any]] = []
    constraints.extend(_constraints_from_bug_intercept(signals))
    constraints.extend(_constraints_from_fp_rules(signals))
    constraints.extend(_constraints_from_defense_feedback(signals))
    constraints.extend(_constraints_from_lessons(signals))
    return constraints
def _constraints_from_bug_intercept(signals: dict[str, Any]) -> list[dict[str, Any]]:
    constraints: list[dict[str, Any]] = []
    for item in signals.get("bug_intercept_high_freq") or []:
        if not isinstance(item, dict):
            continue
        cid = str(item.get("check_id") or "").strip()
        if not cid:
            continue
        count = item.get("count") or 0
        constraints.append(_constraint_record(
            rule_id=f"HF-{cid}",
            rule_name=f"高频拦截预警（{cid}）",
            severity="WARN",
            description=(f"历史编写时门禁已 {count} 次拦截 "
                         f"{cid} 类问题，本任务为高频风险点"),
            suggestion=f"编写时优先对照 {cid} 检测器的判定规则自查，写盘前主动规避",
            category="BUG",
            source="bug_intercept",
        ))
    return constraints
_FP_PROMPT_LIMIT = 20
def _constraints_from_fp_rules(signals: dict[str, Any]) -> list[dict[str, Any]]:
    raw_ids = signals.get("fp_rule_ids")
    if not isinstance(raw_ids, (list, tuple, set, frozenset)):
        return []
    _fp_ids = sorted({ident for x in raw_ids
                      if x is not None and (ident := str(x).strip())})
    if not _fp_ids:
        return []
    _shown = _fp_ids[:_FP_PROMPT_LIMIT]
    _omitted = len(_fp_ids) - len(_shown)
    _suffix = (f"（另有 {_omitted} 条已固化误报未展开，同样无需防御）"
               if _omitted else "")
    return [_constraint_record(
        rule_id="FP-KNOWN",
        rule_name="已知误报规则提示",
        severity="INFO",
        description=(f"以下规则已确认为误报固化，无需过度防御："
                     f"{', '.join(_shown)}{_suffix}"),
        suggestion="编写时无需为这些规则的模式做防御性改写；编写时门禁已对其降级",
        category="META",
        source="fp_rules",
    )]
def _constraints_from_defense_feedback(signals: dict[str, Any]) -> list[dict[str, Any]]:
    raw_recs = signals.get("defense_recommendations")
    if not isinstance(raw_recs, list):
        return []
    recs: list[str] = []
    seen: set[str] = set()
    for rec in raw_recs:
        if not isinstance(rec, str):
            continue
        normalized = rec.strip()
        if not normalized or normalized in seen:
            continue
        seen.add(normalized)
        recs.append(normalized)
    constraints: list[dict[str, Any]] = []
    for i, rec in enumerate(recs, 1):
        constraints.append(_constraint_record(
            rule_id=f"DF-{i:02d}",
            rule_name="防御反馈建议",
            severity="WARN",
            description=rec,
            suggestion="按建议在本次编写中规避同类矛盾/回归失败模式",
            category="DEFENSE",
            source="defense_feedback",
        ))
    return constraints
def _norm_lesson_source(source: Any) -> str:
    return source if isinstance(source, str) and source else "unknown"
def _constraints_from_lessons(signals: dict[str, Any]) -> list[dict[str, Any]]:
    constraints: list[dict[str, Any]] = []
    lsn_seq = 0
    for lesson in signals.get("lessons") or []:
        if not isinstance(lesson, dict):
            continue
        desc = lesson.get("description", "")
        if not desc:
            continue
        conf = safe_confidence(lesson.get("confidence", 0), 0.0)
        source = _norm_lesson_source(lesson.get("source"))
        lsn_seq += 1
        constraints.append(_constraint_record(
            rule_id=f"LSN-{lsn_seq:02d}",
            rule_name=f"历史经验（{source}）",
            severity="WARN" if conf >= 0.7 else "INFO",
            description=desc,
            suggestion=lesson.get(FIELD_SUGGESTED_VALUE, ""),
            category="LESSON",
            source="lessons",
        ))
    return constraints
def _render_prompt_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        return _render_prompt_dict(value)
    if isinstance(value, (list, tuple)):
        return _render_prompt_seq(value)
    return str(value)
def _render_prompt_dict(value: dict) -> str:
    parts = [
        f"{k}: {text}" for k, v in value.items()
        if (text := _render_prompt_text(v))
    ]
    return "；".join(parts)
def _render_prompt_seq(value: list | tuple) -> str:
    parts = [_render_prompt_text(v) for v in value]
    return "、".join(part for part in parts if part)
def inject_dynamic_defense_to_prompt(skill_dir: str) -> str:
    constraints = get_dynamic_defense_constraints(skill_dir)
    if not constraints:
        return ""
    lines = [
        "## 动态编写防御（来自本项目诊断闭环的历史信号）",
        "",
        "以下约束由历史 BUG 拦截/误报固化/防御反馈/复盘经验动态生成，",
        "代表本项目真实出现过的问题模式，优先级高于通用规范：",
        "",
    ]
    rendered: list[str] = []
    for c in constraints:
        sev = c.get("severity", "INFO")
        prefix = "【重点】" if sev == "WARN" else ""
        description = _ensure_sentence(
            _render_prompt_text(c.get("description")))
        if not description:
            continue
        suggestion = _render_prompt_text(c.get("suggestion"))
        tail = _ensure_sentence(suggestion) if suggestion else ""
        rendered.append(
            f"- [{c['rule_id']}] {prefix}{c['rule_name']}："
            f"{description}{tail}")
    if not rendered:
        return ""
    lines.extend(rendered)
    lines.append("")
    return "\n".join(lines)
def _as_constraint_list(constraints: Any) -> list:
    if constraints is None:
        return []
    if isinstance(constraints, (str, bytes, bytearray, Mapping)):
        _log.debug("attach_code_refs: 入参 %s 不是约束序列，按空集合处理",
                   type(constraints).__name__)
        return []
    if not isinstance(constraints, Iterable):
        _log.debug("attach_code_refs: 入参 %s 不可迭代，按空集合处理",
                   type(constraints).__name__)
        return []
    return list(constraints)
def attach_code_refs(constraints: list) -> list:
    constraints = _as_constraint_list(constraints)
    enriched: list = []
    for constraint in constraints:
        if not isinstance(constraint, Mapping):
            enriched.append(constraint)
            continue
        rule_id = constraint.get("rule_id", "")
        ref = resolve_code_ref(rule_id)
        if ref is None:
            enriched.append(constraint)
            continue
        item = dict(constraint)
        item["code_refs"] = {
            "bad_example": ref.bad_example,
            "good_example": ref.good_example,
            "rationale": ref.rationale,
            "detector_ref": ref.detector_ref,
        }
        enriched.append(item)
    return enriched
def _severity_override(severity_by_rule: dict[str, str],
                       rule_id: str) -> str | None:
    if not severity_by_rule:
        return None
    return (severity_by_rule.get(rule_id)
            or severity_by_rule.get(norm_rule_id(rule_id)))
def _effective_severity(ref: CodeRef,
                       severity_by_rule: dict[str, str]) -> str:
    return _normalize_severity(
        _severity_override(severity_by_rule, ref.rule_id) or ref.severity)
def _inject_severity_rank(sev: str) -> int:
    key = sev.strip().upper() if isinstance(sev, str) else ""
    return SEVERITY_RANK.get(DIAGNOSE_TO_P.get(key, key), 3)
def _ordered_inject_refs(
        include_series: frozenset[str] | set[str] | None,
        prefer_series: frozenset[str] | set[str] | None,
        task_type: str,
        severity_by_rule: dict[str, str]) -> list[CodeRef]:
    if prefer_series is None:
        prefer_series = _task_type_row(TASK_PREFERRED_SERIES, task_type)
    preferred = set(prefer_series) if prefer_series else set()
    candidates = CODE_REFS.values()
    if include_series is not None:
        wanted = set(include_series)
        candidates = (
            r for r in candidates
            if _normalize_series_label(r.series) in wanted)
    return sorted(
        candidates,
        key=lambda r: (_inject_severity_rank(
            _effective_severity(r, severity_by_rule)),
            0 if _normalize_series_label(r.series) in preferred else 1,
            r.rule_id),
    )
def _render_ref_section(ref: CodeRef, sev_label: str) -> str:
    return (
        f"### 规则 {ref.rule_id} {ref.name} [{sev_label}]\n"
        f"机理: {ref.rationale}\n"
        f"反例（禁止）:\n```python\n{ref.bad_example}\n```\n"
        f"正例（正确写法）:\n```python\n{ref.good_example}\n```"
    )
_SeriesArg = (frozenset[str] | set[str] | list[str] | tuple[str, ...]
              | str | None)
def _normalize_series_label(value: Any) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _series_tokens(values: Iterable[Any]) -> frozenset[str]:
    return frozenset(
        token for value in values if (token := _normalize_series_label(value)))
def _normalize_series_arg(
        series: _SeriesArg,
) -> frozenset[str] | None:
    if isinstance(series, str):
        return _series_tokens((series,))
    if isinstance(series, (set, frozenset, list, tuple)):
        return _series_tokens(series)
    if series is not None:
        _log.warning(
            "inject_code_refs_to_prompt: 系列入参 %s 非契约，按不选任何系列处理",
            type(series).__name__)
        return frozenset()
    return None
_DEFAULT_MAX_REFS = 20
def inject_code_refs_to_prompt(
    task_type: str = _DEFAULT_TASK_TYPE, skill_dir: str = _DEFAULT_SKILL_DIR,
    max_refs: int = _DEFAULT_MAX_REFS,
    include_series: _SeriesArg = None,
    prefer_series: _SeriesArg = None,
) -> str:
    task_type = _normalize_task_type(task_type)
    include_series = _normalize_series_arg(include_series)
    prefer_series = _normalize_series_arg(prefer_series)
    max_refs = _normalize_max_refs(max_refs)
    if max_refs <= 0:
        return ""
    severity_by_rule = _build_severity_map(
        _load_constraints(task_type, skill_dir))
    ordered = _ordered_inject_refs(
        include_series, prefer_series, task_type, severity_by_rule)
    return _render_refs(ordered, max_refs, severity_by_rule)
def _normalize_max_refs(max_refs: Any) -> int:
    if isinstance(max_refs, bool):
        _log.debug(
            "inject_code_refs_to_prompt: max_refs 为 bool（%r），回退默认 %d",
            max_refs, _DEFAULT_MAX_REFS)
        return _DEFAULT_MAX_REFS
    try:
        return int(max_refs)
    except (TypeError, ValueError, OverflowError):
        _log.debug(
            "inject_code_refs_to_prompt: max_refs 非数值（%r），回退默认 %d",
            max_refs, _DEFAULT_MAX_REFS)
        return _DEFAULT_MAX_REFS
def _load_constraints(task_type: str, skill_dir: str) -> list[dict]:
    try:
        return get_constraints_for_task(task_type=task_type, skill_dir=skill_dir)
    except Exception as e:  # noqa: BLE001
        _log.debug("inject_code_refs_to_prompt: 约束加载失败（降级为纯引用库）: %s", e)
        return []
def _build_severity_map(constraints: list[dict]) -> dict[str, str]:
    severity_by_rule: dict[str, str] = {}
    for constraint in constraints:
        if not isinstance(constraint, dict):
            continue
        rule_id = constraint.get("rule_id")
        if not isinstance(rule_id, str) or not rule_id.strip():
            _log.debug(
                "inject_code_refs_to_prompt: 约束 rule_id=%r 非规则号字符串，"
                "跳过严重度映射", rule_id)
            continue
        severity = constraint.get("severity", "WARN")
        if not isinstance(severity, str) or not severity.strip():
            _log.debug(
                "inject_code_refs_to_prompt: 规则 %s 的 severity=%r 非字符串，"
                "回退 WARN", rule_id, severity)
            severity = "WARN"
        key = rule_id.strip()
        severity = _normalize_severity(severity)
        severity_by_rule[key] = severity
        severity_by_rule.setdefault(norm_rule_id(key), severity)
    return severity_by_rule
def _render_refs(ordered: list[CodeRef], max_refs: int,
                 severity_by_rule: dict[str, str]) -> str:
    selected = ordered[:max_refs]
    if not selected:
        return ""
    parts: list[str] = [
        "## 编写前代码引用预防库（正反示例对照，禁止仿写反例）",
    ]
    parts.extend(_render_ref_section(
        ref, _effective_severity(ref, severity_by_rule)) for ref in selected)
    return "\n\n".join(parts) + "\n"
def _append_loaded_section(
    parts: list[str], label: str, loader: Callable[..., str],
    *args: Any, **kwargs: Any,
) -> None:
    try:
        text = loader(*args, **kwargs)
    except Exception as e:  # noqa: BLE001
        _log.debug("inject_full_prevention_prompt: %s降级跳过: %s", label, e)
        return
    if not isinstance(text, str):
        _log.debug(
            "inject_full_prevention_prompt: %s返回 %s 而非文本，降级跳过",
            label, type(text).__name__)
        return
    normalized = text.rstrip()
    if normalized:
        parts.append(normalized)
def inject_full_prevention_prompt(
    task_type: str = _DEFAULT_TASK_TYPE,
    skill_dir: str = _DEFAULT_SKILL_DIR,
    max_refs: int = _DEFAULT_MAX_REFS,
    include_series: _SeriesArg = None,
    prefer_series: _SeriesArg = None,
) -> str:
    task_type = _normalize_task_type(task_type)
    parts: list[str] = []
    _append_loaded_section(parts, "约束段", inject_norms_to_prompt,
                    task_type=task_type, skill_dir=_DEFAULT_SKILL_DIR)
    _append_loaded_section(parts, "引用段", inject_code_refs_to_prompt,
                    task_type=task_type, skill_dir=_DEFAULT_SKILL_DIR,
                    max_refs=max_refs, include_series=include_series,
                    prefer_series=prefer_series)
    if skill_dir:
        _append_loaded_section(parts, "动态防御段", inject_dynamic_defense_to_prompt,
                        skill_dir)
    if not parts:
        return ""
    header = (
        "# 编写前预防注入（约束 + 正反示例 + 动态防御）\n"
        "# 生成代码前逐条对照；标注「禁止」的反例不得仿写。"
    )
    return header + "\n\n" + "\n\n".join(parts) + "\n"
