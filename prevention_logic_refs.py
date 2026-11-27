from __future__ import annotations

import logging
from collections.abc import Callable
from typing import Any

import jwsgj.prevention_arg_checks as _arg_contract_checks
import jwsgj.prevention_container_length as _container_length_checks
import jwsgj.prevention_container_mutation as _container_mutation_checks
import jwsgj.prevention_flow_exit_checks as _exit_propagation_checks
import jwsgj.prevention_flow_loop_checks as _loop_iteration_checks
import jwsgj.prevention_gen_checks as _gen_consume_checks
import jwsgj.prevention_literal_protocol as _literal_protocol_checks
import jwsgj.prevention_literal_truth as _literal_truth_checks
import jwsgj.prevention_scope_checks as _scope_checks
from jwsgj.prevention_refs_main import (
    CHANNEL_SUFFIX,
    CodeRef,
    build_keyed_registry,
    make_code_ref,
    register_code_refs,
)

__all__ = [
    'LOGIC_CODE_REFS',
    'LOGIC_CODE_REFS_VERSION',
    'LOGIC_DIRECT_CHECKS',
    'list_logic_rule_ids',
]
_log = logging.getLogger(__name__)
LOGIC_CODE_REFS_VERSION = '1.14.0'
_LOGIC_RULE_IDS = frozenset(f'LV-{number:02d}' for number in range(1, 62))
_CHECK_MODULES = (
    _literal_truth_checks,
    _literal_protocol_checks,
    _container_mutation_checks,
    _container_length_checks,
    _arg_contract_checks,
    _loop_iteration_checks,
    _exit_propagation_checks,
    _gen_consume_checks,
    _scope_checks,
)
def _collect_direct_checks() -> dict[str, Callable[..., Any]]:
    checks: dict[str, Callable[..., Any]] = {}
    for module in _CHECK_MODULES:
        for name in getattr(module, '__all__', ()):
            if not name.startswith('check_LV'):
                continue
            check = getattr(module, name)
            if not callable(check):
                raise RuntimeError(
                    f'{module.__name__}.{name} 已导出但不是可调用检测器')
            rule_id = f"LV-{name.removeprefix('check_LV')}"
            if rule_id in checks:
                raise RuntimeError(
                    f'直调检测器重复登记：{rule_id} 同时来自 '
                    f'{checks[rule_id].__module__} 与 {module.__name__}')
            checks[rule_id] = check
    return dict(sorted(checks.items()))
LOGIC_DIRECT_CHECKS: dict[str, Callable[..., Any]] = _collect_direct_checks()
def _logic_entry(
    rule_id: str,
    name: str,
    severity: str,
    bad: str,
    good: str,
    rationale: str,
) -> CodeRef:
    try:
        check = LOGIC_DIRECT_CHECKS[rule_id]
    except KeyError:
        raise RuntimeError(
            f'逻辑库条目 {rule_id} 缺少直调检测器登记：'
            'LOGIC_DIRECT_CHECKS 必须与 LOGIC_CODE_REFS 逐条对应'
        ) from None
    return make_code_ref(
        'logic', rule_id, name, severity, bad, good, rationale,
        check.__module__ + CHANNEL_SUFFIX,
    )
LOGIC_CODE_REFS: dict[str, CodeRef] = build_keyed_registry(
    [
        _logic_entry(
            'LV-01', '恒真/恒假比较链：== a or b 中裸字面量脱离比较语境', 'P1',
            (
                'def check_status(status):\n'
                '    if status == 1 or 2:\n'
                '        return "active"\n'
                '    return "inactive"\n'
            ),
            (
                'def check_status(status):\n'
                '    if status in (1, 2):\n'
                '        return "active"\n'
                '    return "inactive"\n'
            ),
            (
                '自然语言「等于 1 或 2」直译成 ``== 1 or 2``——比较运算符'
                '优先级高于 or，裸操作数 2 被静默求值为 truthiness（恒真），'
                '整条链恒真、分支永久走错且无异常。多值成员判断必须用 '
                '``in`` 元组；每个 or/and 操作数都必须是完整布尔表达式。'
            ),
        ),
        _logic_entry(
            'LV-02', '就地方法返回 None 被赋值：x = lst.sort() 后消费即 TypeError', 'P1',
            (
                'def first_item(items):\n'
                '    result = items.sort()\n'
                '    return result[0]\n'
            ),
            (
                'def first_item(items):\n'
                '    return sorted(items)[0]\n'
            ),
            (
                'list/dict/set 的 sort/reverse/append/extend/update 等就地'
                '变更方法全部返回 None——fluent API 思维写 ``x = lst.sort()``'
                '拿到 None，后续下标/算术/迭代消费直接 TypeError。赋值目标'
                '不限单一局部名：链式多目标（``a = b = lst.sort()``）与属性/'
                '下标目标（``self.items = lst.sort()``）同样拿到 None。需要'
                '返回值时用 sorted()/reversed() 等函数式等价物；就地方法直接'
                '调用后消费原对象。'
            ),
        ),
        _logic_entry(
            'LV-03', '循环体内重置累加器：跨轮累积只剩最后一轮', 'P1',
            (
                'def total_score(rows):\n'
                '    for row in rows:\n'
                '        total = 0\n'
                '        total += row["score"]\n'
                '    return total\n'
            ),
            (
                'def total_score(rows):\n'
                '    total = 0\n'
                '    for row in rows:\n'
                '        total += row["score"]\n'
                '    return total\n'
            ),
            (
                '累加器/收集器初始化（``total = 0`` / ``items = []``）被'
                '误置于循环体内——每轮清零/清空，循环结束后只剩最后一轮'
                '数据，静默产出错误结果。累积操作涵盖 ``+=``、``acc = acc + ...``'
                '自引用重绑、``append/extend/add/update`` 与下标赋值。初始化必须'
                '在循环之前；若确需每轮独立统计，消费也应留在循环体内（循环外不读）。'
            ),
        ),
        _logic_entry(
            'LV-04', 'and 链守卫顺序颠倒：None 判断排在属性访问之后', 'P1',
            (
                'def render(obj):\n'
                '    if obj.field is not None and obj is not None:\n'
                '        return obj.field\n'
                '    return ""\n'
            ),
            (
                'def render(obj):\n'
                '    if obj is not None and obj.field is not None:\n'
                '        return obj.field\n'
                '    return ""\n'
            ),
            (
                '复合守卫条件按业务语序书写（``obj.field is not None and '
                'obj is not None``）——obj 为 None 时前段属性访问直接 '
                'AttributeError，排在后面的 None 守卫是死守卫。None 守卫'
                '必须前置（and 链最左），靠短路保护后续访问。'
            ),
        ),
        _logic_entry(
            'LV-05', 'dict.get 缺默认值参与算术/序比较：键缺失返回 None 触发 TypeError', 'P1',
            (
                'def bump(d):\n'
                '    return d.get("count") + 1\n'
            ),
            (
                'def bump(d):\n'
                '    return d.get("count", 0) + 1\n'
            ),
            (
                '``d.get(k)`` 单参调用在键缺失时返回 None——None 参与算术'
                '（+ - * /）或序比较（< >）直接 TypeError。同作用域内已有'
                '提前退出守卫（``if d.get(k) is None: raise/return``）或同'
                '一 and 链前置 None 判断时已排除；外层守卫不跨延迟执行的'
                '函数、lambda 或生成器主体，但可保护定义时求值的默认参数与'
                '生成器首个迭代器。计数场景补 '
                '``get(k, 0)``、文本场景补 ``get(k, "")``；键必须存在时'
                '直接 ``d[k]`` 让 KeyError 响亮失败，优于 None 静默传播。'
            ),
        ),
        _logic_entry(
            'LV-06', 'range(len(x)) 循环内 x[i+1]：最后一轮 IndexError', 'P1',
            (
                'def pair_sum(x):\n'
                '    out = 0\n'
                '    for i in range(len(x)):\n'
                '        out += x[i] + x[i + 1]\n'
                '    return out\n'
            ),
            (
                'def pair_sum(x):\n'
                '    out = 0\n'
                '    for i in range(len(x) - 1):\n'
                '        out += x[i] + x[i + 1]\n'
                '    return out\n'
            ),
            (
                '相邻元素处理（差分/去重/滑窗）写 ``for i in range(len(x)): '
                'x[i+1]``——最后一轮 i+1 = len(x) 越界 IndexError，运行到'
                '末尾才爆发、短样本测试可能漏过。边界用 ``range(len(x)-1)``；'
                '更优解 ``zip(x, x[1:])`` 配对遍历零越界。'
            ),
        ),
        _logic_entry(
            'LV-07', 'while 条件变量循环体内无更新：初始为真即死循环', 'P1',
            (
                'def drain(queue):\n'
                '    out = []\n'
                '    while queue:\n'
                '        out.append(len(queue))\n'
                '    return out\n'
            ),
            (
                'def drain(queue):\n'
                '    out = []\n'
                '    while queue:\n'
                '        out.append(queue.pop())\n'
                '    return out\n'
            ),
            (
                '重试/轮询循环的条件变量（计数/队列/标志）在体内无任何更新'
                '路径——条件恒定，初始为真即永久循环（CPU 空转、无异常）。'
                '写 while 时自检三件事：条件变量在哪更新、是否每轮必然'
                '向终止靠近、有无超时/break 兜底。'
            ),
        ),
        _logic_entry(
            'LV-08', 'os.path.join 后续参数为绝对/异盘符路径：base 前缀被静默丢弃', 'P1',
            (
                'import os\n'
                '\n'
                '\n'
                'def build(base, name):\n'
                '    return os.path.join(base, "/data/" + name)\n'
            ),
            (
                'import os\n'
                '\n'
                '\n'
                'def build(base, name):\n'
                '    return os.path.join(base, "data", name)\n'
            ),
            (
                'os.path.join 的后续参数以 /、\\\\ 或盘符根路径开头时，前面所有'
                '参数被静默丢弃；``C:data`` 这类驱动器相对路径在同盘符时会'
                '接续前缀，只有可静态确证为异盘符时才按重置报告。base 前缀'
                '失效无告警，落盘位置失控（安全、正确性双重缺陷）。'
            ),
        ),
        _logic_entry(
            'LV-09', 'zip 实参长度不等：按最短静默截断丢数据', 'P2',
            (
                'def merge(names, scores):\n'
                '    return [n + str(s)\n'
                '            for n, s in zip(["a", "b", "c"], [90, 85])]\n'
            ),
            (
                'def merge(names, scores):\n'
                '    return [n + str(s)\n'
                '            for n, s in zip(["a", "b", "c"], [90, 85, 77],\n'
                '                             strict=True)]\n'
            ),
            (
                'zip 默认按最短实参截断——表头/数据行、名称/分数等配对'
                '源长度不齐时长列表尾部数据无声丢失。Python 3.10+ 用 '
                'strict=True 让不齐响亮失败（等长契约）；有意截断写 '
                'strict=False 并注释说明。动态列表组 ``zip(*lists, '
                'strict=True)`` 同样适用——解包后按位置实参校验长度，'
                '等长契约不因星号展开失效。'
            ),
        ),
        _logic_entry(
            'LV-10', '生成器表达式二次消费：第二次迭代恒为空', 'P1',
            (
                'def stats(items):\n'
                '    gen = (x for x in items if x > 0)\n'
                '    total = sum(gen)\n'
                '    count = len(list(gen))\n'
                '    return total, count\n'
            ),
            (
                'def stats(items):\n'
                '    vals = [x for x in items if x > 0]\n'
                '    total = sum(vals)\n'
                '    count = len(vals)\n'
                '    return total, count\n'
            ),
            (
                '生成器只能消费一次——``sum(gen)`` 耗尽后 ``list(gen)`` '
                '恒为空，第二段统计静默归零（count 恒 0、聚合丢失）。'
                '同一消费语句处在可重复执行的循环体内时同理：首轮耗尽，后续轮次恒为空；'
                '静态可证零轮或单轮的循环不属于二次消费。'
                '需要多次消费时物化为列表（列表推导式）；或单遍 for 循环'
                '同时累计多个统计量。'
            ),
        ),
        _logic_entry(
            'LV-11', 'range 起止方向与步长推进方向相反：迭代恒空、循环体静默不执行', 'P1',
            (
                'def tail_sum(scores):\n'
                '    total = 0\n'
                '    for i in range(10, 0):\n'
                '        total += scores[i]\n'
                '    return total\n'
            ),
            (
                'def tail_sum(scores):\n'
                '    total = 0\n'
                '    for i in range(9, 0, -1):\n'
                '        total += scores[i]\n'
                '    return total\n'
            ),
            (
                '``range(10, 0)`` 起始值大于终止值且无负步长——区间恒空、'
                '循环体一次都不执行，统计量静默归零/任务静默跳过，无任何'
                '异常信号。显式正步长（``range(10, 0, 1)`` / ``(10, 0, 2)``）'
                '与缺省同语义，同样恒空。对称形态是正向边界配负步长'
                '（``range(0, 10, -1)``）：起始值小于终止值而步长往回走，'
                '同样一次不执行。倒序遍历必须显式 ``range(hi, lo, -1)``，'
                '升序核对边界（``range(lo, hi)``，含头不含尾），步长方向'
                '与边界必须自洽。'
            ),
        ),
        _logic_entry(
            'LV-12', '嵌套函数对外层变量赋值但缺 nonlocal：外层读到的恒为初始值', 'P1',
            (
                'def run_batch(items):\n'
                '    count = 0\n'
                '\n'
                '    def handle(item):\n'
                '        if item is None:\n'
                '            return\n'
                '        count = count + 1\n'
                '\n'
                '    for it in items:\n'
                '        handle(it)\n'
                '    return count\n'
            ),
            (
                'def run_batch(items):\n'
                '    count = 0\n'
                '\n'
                '    def handle(item):\n'
                '        nonlocal count\n'
                '        if item is None:\n'
                '            return\n'
                '        count = count + 1\n'
                '\n'
                '    for it in items:\n'
                '        handle(it)\n'
                '    return count\n'
            ),
            (
                '闭包「读取」外层变量合法，但「赋值」会在嵌套函数内创建新的'
                '局部绑定——``count = count + 1`` 在赋值前读取未绑定局部，'
                '本例首次执行即 UnboundLocalError，根本不会正常 return；'
                '其他仅赋值形态下外层同样看不到内层更新。嵌套函数内改外层'
                '变量必须先声明 ``nonlocal count``，或改用可变容器载体'
                '（list/dict 存计数）。'
            ),
        ),
        _logic_entry(
            'LV-13', '类定义 __eq__ 但未定义 __hash__：实例放入 set/dict 键即 TypeError', 'P2',
            (
                'class Point:\n'
                '    def __init__(self, x, y):\n'
                '        self.x = x\n'
                '        self.y = y\n'
                '\n'
                '    def __eq__(self, other):\n'
                '        return (self.x, self.y) == (other.x, other.y)\n'
            ),
            (
                'class Point:\n'
                '    def __init__(self, x, y):\n'
                '        self.x = x\n'
                '        self.y = y\n'
                '\n'
                '    def __eq__(self, other):\n'
                '        return (self.x, self.y) == (other.x, other.y)\n'
                '\n'
                '    def __hash__(self):\n'
                '        return hash((self.x, self.y))\n'
            ),
            (
                'Python 协议联动：类定义 ``__eq__`` 且自身未定义 ``__hash__`` '
                '时，``__hash__`` 被隐式置为 None——实例不可哈希，放入 set / '
                'dict 键 / lru_cache 时 TypeError: unhashable type，报错点远离'
                '类定义。值对象应同时实现两者（equal 对象须有相同哈希）；确实'
                '不需要哈希时显式写 ``__hash__ = None`` 声明意图。'
            ),
        ),
        _logic_entry(
            'LV-14', 'endswith/startswith 首参传 list 字面量：调用即 TypeError', 'P1',
            (
                'def is_archive(filename):\n'
                '    return filename.endswith([".zip", ".tar.gz", ".7z"])\n'
            ),
            (
                'def is_archive(filename):\n'
                '    return filename.endswith((".zip", ".tar.gz", ".7z"))\n'
            ),
            (
                '``str.endswith/startswith`` 只接受 str 或 tuple，首参传列表'
                '调用必抛 ``TypeError: endswith first arg must be str or a '
                'tuple of str``。多后缀判断改传元组；动态 list 先 '
                '``tuple(exts)`` 转换再传。'
            ),
        ),
        _logic_entry(
            'LV-15', 'os.makedirs 缺 exist_ok 且无守卫：重跑时 FileExistsError', 'P2',
            (
                'import os\n'
                '\n'
                '\n'
                'def ensure_workspace(base):\n'
                '    out = os.path.join(base, "output")\n'
                '    os.makedirs(out)\n'
                '    return out\n'
            ),
            (
                'import os\n'
                '\n'
                '\n'
                'def ensure_workspace(base):\n'
                '    out = os.path.join(base, "output")\n'
                '    os.makedirs(out, exist_ok=True)\n'
                '    return out\n'
            ),
            (
                '``os.makedirs(path)`` 未传可静态证真的 ``exist_ok`` 且无 '
                '``os.path.isdir`` 前置判断、无 try/except 容错；动态 flag 或'
                '假值字面量不算有效守卫——目录已存在'
                '（重跑/恢复场景）时 FileExistsError，破坏幂等性。目录准备'
                '逻辑默认 ``os.makedirs(path, exist_ok=True)``。'
            ),
        ),
        _logic_entry(
            'LV-16', 'strip(".txt") 按字符集剥离而非去后缀：结果静默错误', 'P2',
            (
                'def clean_filename(name):\n'
                '    return name.strip(".txt")\n'
            ),
            (
                'def clean_filename(name):\n'
                '    return name.removesuffix(".txt")\n'
            ),
            (
                'strip/lstrip/rstrip 的实参是「要剥离的字符集合」而非前后缀'
                '字符串——``".txt"`` 被拆成字符 {., t, x} 逐个剥离两端：'
                '``"report.txt".strip(".txt")`` 结果是 "repor"（尾字符 t '
                '恰在集合内被连带剥掉），``"text.txt".strip(".txt")`` 更是'
                '只剩 "e"——两端恰好由集合内字符组成的合法内容被连带剥掉，'
                '静默错误。去后缀用 ``removesuffix``（3.9+），去前缀用 '
                '``removeprefix``。'
            ),
        ),
        _logic_entry(
            'LV-17', '函数体内无条件分支却自调用：无基例、必无限递归', 'P1',
            (
                'def optimize(value):\n'
                '    improved = refine(value)\n'
                '    return optimize(improved)\n'
            ),
            (
                'def optimize(value):\n'
                '    improved = refine(value)\n'
                '    if improved == value:\n'
                '        return improved\n'
                '    return optimize(improved)\n'
            ),
            (
                '函数体内没有任何条件分支（if/for/while/try/条件表达式）却存在'
                '直接自调用——递归路径无条件执行且无终止条件，首次调用即 '
                'RecursionError。递归必须有基例（``if 终止条件: return``）；'
                '或改用 while 循环让终止条件显式可控。'
            ),
        ),
        _logic_entry(
            'LV-18', 'except 块内 raise e 非裸 raise：栈帧冗余、traceback 起点错位', 'P2',
            (
                'import json\n'
                '\n'
                '\n'
                'def safe_load(text):\n'
                '    try:\n'
                '        return json.loads(text)\n'
                '    except json.JSONDecodeError as e:\n'
                '        print("parse failed:", e)\n'
                '        raise e\n'
            ),
            (
                'import json\n'
                '\n'
                '\n'
                'def safe_load(text):\n'
                '    try:\n'
                '        return json.loads(text)\n'
                '    except json.JSONDecodeError as e:\n'
                '        print("parse failed:", e)\n'
                '        raise\n'
            ),
            (
                'except 块内 ``raise e`` 会在当前行追加新栈帧——traceback '
                '起点错位为 raise 行且多一层冗余帧，干扰定位真正的异常源头。'
                '重抛当前异常用裸 ``raise``（完整保留原始栈）；包装成新异常用 '
                '``raise NewError(...) from e`` 保留异常链。'
            ),
        ),
        _logic_entry(
            'LV-19', '可变元素列表乘法复制：[[]] * n 全部位置引用同一对象', 'P1',
            (
                'def make_buckets(n):\n'
                '    buckets = [[]] * n\n'
                '    return buckets\n'
            ),
            (
                'def make_buckets(n):\n'
                '    buckets = [[] for _ in range(n)]\n'
                '    return buckets\n'
            ),
            (
                '序列乘法 ``[[]] * n`` 复制的是**引用**——n 个位置全部指向'
                '同一个可变对象：任一桶 append 全部桶同步混入、矩阵改一行'
                '全变（``[[0] * cols] * rows`` 行共享），数据静默污染无任何'
                '异常。嵌套结构的每一层都必须独立构造（推导式逐位新建），'
                '不可用乘法展开可变元素。'
            ),
        ),
        _logic_entry(
            'LV-20', 'finally 块内 return：吞掉 try 的异常与返回值', 'P1',
            (
                'def load_config(path):\n'
                '    try:\n'
                '        return parse(path)\n'
                '    except ValueError:\n'
                '        return {"defaults": True}\n'
                '    finally:\n'
                '        return {"fallback": True}\n'
            ),
            (
                'import logging\n'
                '\n'
                '_log = logging.getLogger(__name__)\n'
                '\n'
                '\n'
                'def load_config(path):\n'
                '    try:\n'
                '        return parse(path)\n'
                '    except ValueError:\n'
                '        # 降级必须留痕；finally 只做清理，不承载返回值\n'
                '        _log.warning("load_config: 配置解析失败 %s", path)\n'
                '        return {"defaults": True}\n'
                '    finally:\n'
                '        cleanup_cache()\n'
            ),
            (
                'finally 中的 return 会在退出时覆盖既有控制流：try/except 已计算'
                '的返回值被丢弃，未被处理的异常也被吞掉——except 本身仍会'
                '先执行，但最终调用方只拿到 fallback，原返回或异常凭空消失'
                '且无告警。finally 只做清理（关资源/解锁/打点），return '
                '全部放 try/except 分支。'
            ),
        ),
        _logic_entry(
            'LV-21', 'except 宽捕获在前：后续具体异常分支永不可达', 'P2',
            (
                'def read_int(text):\n'
                '    try:\n'
                '        return int(text)\n'
                '    except Exception:\n'
                '        return 0\n'
                '    except ValueError:\n'
                '        return -1\n'
            ),
            (
                'import logging\n'
                '\n'
                '_log = logging.getLogger(__name__)\n'
                '\n'
                '\n'
                'def read_int(text):\n'
                '    try:\n'
                '        return int(text)\n'
                '    except ValueError:\n'
                '        _log.warning("read_int: 非法整数字面量 %r", text)\n'
                '        return -1\n'
                '    except Exception:\n'
                '        _log.exception("read_int: 未预期异常 %r", text)\n'
                '        return 0\n'
            ),
            (
                '异常按 except 声明序匹配——``except Exception`` 在前已覆盖'
                '后续 Exception 子类 handler，这些具体异常分支永不执行（死分支），'
                '其重试/降级/默认值逻辑静默失效。KeyboardInterrupt/SystemExit '
                '等 BaseException 直接子类不在 Exception 覆盖域；只有 '
                '``except BaseException`` 或裸 except 才是全捕获。handler '
                '必须按「具体在前、宽泛殿后」排序，宽捕获只作最后兜底。'
            ),
        ),
        _logic_entry(
            'LV-22', '迭代源容器在循环体内被修改：dict 一执行即崩/list 跳元素或循环不终止', 'P1',
            (
                'def prune_expired(cache):\n'
                '    for key in cache:\n'
                '        if expired(key):\n'
                '            cache.pop(key)\n'
                '    return cache\n'
            ),
            (
                'def prune_expired(cache):\n'
                '    for key in list(cache):\n'
                '        if expired(key):\n'
                '            cache.pop(key)\n'
                '    return cache\n'
            ),
            (
                '``for k in d: d.pop(k)`` 是遍历删键场景的最高频崩溃：'
                'dict/set 迭代中改尺寸直接 ``RuntimeError: dictionary changed '
                'size during iteration``；list 迭代中 remove/pop 使后续轮次'
                '位移跳过元素、过滤静默漏删。反向的 append/extend/add 同样'
                '致命——迭代器持续看到新元素，list 循环永不终止（边遍历边'
                '收集）。修复铁律：迭代副本、修改原件（``for k in list(d)``），'
                '推导式重建，或先写入临时容器、循环结束再统一 extend。'
            ),
        ),
        _logic_entry(
            'LV-23', '% 格式化占位符与实参载体/数量错配：一执行即 TypeError', 'P1',
            (
                'def show(name, version):\n'
                '    return "%s-%s" % (name,)\n'
            ),
            (
                'def show(name, version):\n'
                '    return "%s-%s" % (name, version)\n'
            ),
            (
                '``"%s-%s" % (x,)`` 占位符数与实参数不等时必抛 '
                'TypeError（not enough arguments / not all arguments '
                'converted），消息拼接/日志格式化行一执行即崩——模板与'
                '实参在多次编辑中各自演化时高频出现。f-string、dict/set 等'
                '非元组字面量只算单值；零占位配单值同样报错；列表多占位形态'
                '归 LV-42。具名槽位 ``%(name)s`` 配非映射实参即抛 '
                '``format requires a mapping``；反之 list/dict/bytes-like '
                '载体在零占位符模板下不被消费也不报错（不得误判为未消费实参）。'
                '新代码优先 f-string '
                '（编译期可见），维护 % 形态时逐个核对占位符与实参'
                '一一对应。'
            ),
        ),
        _logic_entry(
            'LV-24',
            'str 字面量含 {变量} 占位（含属性/下标基名）但无 f 前缀：插值静默失活',
            'P1',
            (
                'def report(count):\n'
                '    return "processed {count} items"\n'
            ),
            (
                'def report(count):\n'
                '    return f"processed {count} items"\n'
            ),
            (
                '插值意图写成普通 str 字面量——``"{count}"`` 缺 f 前缀时'
                '花括号是字面文本，运行时文案原样输出占位符，日志/异常'
                '消息/用户提示中的变量值永不出现。静态渲染错误且无任何'
                '异常信号，是文案类缺陷的最高频成因。docstring、f-string '
                '内部段、``.format`` 模板与惰性 keyword 格式化四类合法'
                '语境不在缺陷范围；字符串加法拼接中的字面量按同一口径检查。'
            ),
        ),
        _logic_entry(
            'LV-25', '除数为 len() 且无空守卫：空容器即 ZeroDivisionError', 'P2',
            (
                'def average(scores):\n'
                '    return sum(scores) / len(scores)\n'
            ),
            (
                'def average(scores):\n'
                '    return sum(scores) / len(scores) if scores else 0.0\n'
            ),
            (
                '``sum(x) / len(x)`` 平均值/占比模式中除数是 len()——'
                '空序列使 len() 归 0，除法瞬间 ZeroDivisionError。空'
                '数据集是运行常态而非异常路径，除法前必须有空守卫'
                '（``if items:`` 或条件表达式）。'
            ),
        ),
        _logic_entry(
            'LV-26', 'json.load 传 str / json.loads 传文件对象：接口形态错抛 TypeError/AttributeError', 'P2',
            (
                'import json\n'
                '\n\n'
                'def load_config():\n'
                '    return json.load(\'{"debug": true}\')\n'
            ),
            (
                'import json\n'
                '\n\n'
                'def load_config():\n'
                '    return json.loads(\'{"debug": true}\')\n'
            ),
            (
                '``json.load(fp)`` 消费文件对象、``json.loads(s)`` 消费 '
                'str——口诀：loads 的 s 是 string。按直觉反记时 '
                '``json.load(str字面量/.read()结果)`` 因 str 无 read 抛 '
                '``AttributeError``；``json.loads(open(...))`` 因文件对象非文本'
                '载荷抛 ``TypeError``，解析入口当步崩溃。槽位按签名取：'
                '位置实参优先，其后同名关键字'
                '（``load(fp=..)`` / ``loads(s=..)``）同口径判；变量承载'
                '形态无静态证据不判，常量、f-string、list/tuple/dict/set '
                '字面量与 .read()/open() 调用形态可静态确证。'
            ),
        ),
        _logic_entry(
            'LV-27', 'max/min 单实参为推导式/生成器表达式且无 default：空结果 ValueError', 'P2',
            (
                'def best_score(rows):\n'
                '    return max(r["score"] for r in rows)\n'
            ),
            (
                'def best_score(rows):\n'
                '    return max((r["score"] for r in rows), default=0)\n'
            ),
            (
                '``max(r for r in rows)`` / ``max([r["score"] for r in '
                'rows])`` 单实参推导式或生成器表达式未带 default——源为'
                '空（如 rows 无记录）时即无值可取，过滤推导式还会在全'
                '过滤时空，抛 ``ValueError: max() arg is an empty '
                'sequence``，取极值入口当步崩溃。聚合前补 ``default=``'
                '（生成器实参须加括号）或先判空走独立分支。'
            ),
        ),
        _logic_entry(
            'LV-28', 'Thread 实例 .run() 直调：目标函数同步执行，多线程意图静默失效', 'P2',
            (
                'import threading\n'
                '\n\n'
                'def run_job(work):\n'
                '    worker = threading.Thread(target=work)\n'
                '    worker.run()\n'
            ),
            (
                'import threading\n'
                '\n\n'
                'def run_job(work):\n'
                '    worker = threading.Thread(target=work)\n'
                '    worker.start()\n'
                '    worker.join()  # 启动后必须汇合，避免线程悬空\n'
            ),
            (
                '``Thread.run()`` 是线程体入口（start 在新线程内部调用它）'
                '——外部直调 .run() 等价普通函数同步调用：不创建线程、'
                '不并发、无异常信号，并发设计整体落空且难以察觉。启动'
                '线程必须 ``.start()``；需返回值用 ThreadPoolExecutor。'
            ),
        ),
        _logic_entry(
            'LV-29', '值返回函数存在隐式 None 落穿路径：部分分支缺 return', 'P2',
            (
                'def clamp(value, low, high):\n'
                '    if value < low:\n'
                '        return low\n'
                '    if value > high:\n'
                '        return high\n'
            ),
            (
                'def clamp(value, low, high):\n'
                '    if value < low:\n'
                '        return low\n'
                '    if value > high:\n'
                '        return high\n'
                '    return value\n'
            ),
            (
                '函数部分分支返回值、部分路径无 return 静默落穿返回 '
                'None——调用方拿 None 继续算术/下标/属性访问时当场 '
                'TypeError，且崩溃现场远离成因点。值返回函数所有路径'
                '都应显式 return（mypy --warn-no-return 同口径）：'
                '兜底 ``return value``、有意 None 写 ``return None``、'
                '不应到达用 ``raise ValueError`` 显式失败。'
                '终止信号含跨模块 NoReturn 契约：``from 本地模块 import '
                '失败出口`` 且被导入方标注 ``-> NoReturn``/``Never``（函数体'
                '无同层 return）时，该调用计为终止（``m.die()`` 属性形态'
                '同口径），不把契约明确的 CLI 失败出口误报为落穿。'
            ),
        ),
        _logic_entry(
            'LV-30', 'while True 无 break 出口：循环不可终止，后续语句永不可达', 'P1',
            (
                'def poll_queue(queue):\n'
                '    while True:\n'
                '        item = queue.get()\n'
                '    return item\n'
            ),
            (
                'def poll_queue(queue):\n'
                '    while True:\n'
                '        item = queue.get()\n'
                '        if item is None:\n'
                '            break\n'
                '    return item\n'
            ),
            (
                '``while True`` 体内没有绑定本循环的 ``break``——循环'
                '永不正常结束，其后语句只能经 break 落穿到达，静态确证'
                '永不可达。进入即挂死：CPU 空转、线程永不归还。裸事件'
                '循环（无后续语句的服务常驻形态）不在缺陷范围；嵌套循'
                '环 ``orelse`` 内的 ``break`` 按编译期绑定归属本循环'
                '（for-else 惯用退出），计为真实出口不误报。有后续'
                '语句即「预期可结束」的静态证据，须补终止判定与 break '
                '出口，或直接以状态作循环条件（``while not done:``）。'
            ),
        ),
        _logic_entry(
            'LV-31', '循环体首轮即无条件返回：后续元素永不处理', 'P2',
            (
                'def any_negative(numbers):\n'
                '    for n in numbers:\n'
                '        if n < 0:\n'
                '            return True\n'
                '        return False\n'
            ),
            (
                'def any_negative(numbers):\n'
                '    for n in numbers:\n'
                '        if n < 0:\n'
                '            return True\n'
                '    return False\n'
            ),
            (
                '循环体内存在每轮必达的 return（直系 return 与条件分支'
                '共存，或 if/else 全分支 return）——循环至多执行一轮，'
                '第二个及之后的元素永不处理，遍历意图静默落空且无异常'
                '信号。「没找到」的兜底 return 应放在循环之后与 for '
                '对齐；find-first 惯用形态 ``next((x for x in items '
                'if cond), None)`` 同义且无此风险。'
            ),
        ),
        _logic_entry(
            'LV-32', 'raise Exception 泛化异常：调用方具体异常分支永不可达', 'P2',
            (
                'def load_config(path):\n'
                '    if not path:\n'
                '        raise Exception("config path is empty")\n'
                '    return read_json(path)\n'
            ),
            (
                'def load_config(path):\n'
                '    if not path:\n'
                '        raise ValueError("config path is empty")\n'
                '    return read_json(path)\n'
            ),
            (
                '``raise Exception(...)`` 抛泛化基类——调用方的 '
                '``except ValueError:`` 等具体分支永不匹配，按类型分流'
                '的防御逻辑整体旁路；``BaseException`` 更穿透 '
                '``except Exception:`` 兜底直达进程顶层。异常类型是'
                '调用双方的隐式契约：按成因抛具体子类（值非法 '
                'ValueError / 状态错误 RuntimeError / 领域自定义异常'
                '基类），re-raise 保留原异常用裸 ``raise``。'
            ),
        ),
        _logic_entry(
            'LV-33', 'assert 元组恒真断言失效：元组非空恒真，校验永不触发', 'P1',
            (
                'def check(x):\n'
                '    assert (x == 1, "x must be 1")\n'
                '    return x\n'
            ),
            (
                'def check(x):\n'
                '    assert x == 1, "x must be 1"\n'
                '    return x\n'
            ),
            (
                '``assert (cond, msg)`` 把消息与条件同括进括号——test 成为二元元组，非空元组恒真，断言永不触发、校验分支不可达且无任何报错信号；正确形态是 msg 作为 assert 的第二位置元素（``assert cond, msg``）。``assert (x,)`` 则是 ``assert x`` 末尾多写逗号，单元素元组同样恒真。若意图校验多个值须拆为独立条件（``assert a and b``）。'
            ),
        ),
        _logic_entry(
            'LV-34', 'isinstance/issubclass 多于两个位置实参：必抛 TypeError（多类型须传元组）', 'P1',
            (
                'def f(x):\n'
                '    return isinstance(x, str, int)\n'
            ),
            (
                'def f(x):\n'
                '    return isinstance(x, (str, int))\n'
            ),
            (
                'isinstance/issubclass 只接受恰好两个位置实参（对象 + 类信息），三个及以上在调用时必抛 TypeError: expected 2 arguments——关键字或星号展开不遮蔽已经超出的固定位置实参；星号位于可能补足前两位时保持未知不误报。多类型判断须把类打包为元组第二实参 ``isinstance(x, (str, int))``。'
            ),
        ),
        _logic_entry(
            'LV-35', 'str.format 槽位与实参错配：自动槽位越界 IndexError / 编号模式混用 ValueError', 'P1',
            (
                'def g(x):\n'
                '    return "{} {}".format(x)\n'
            ),
            (
                'def g(x):\n'
                '    return "{} {}".format(x, x)\n'
            ),
            (
                '模板自动槽位 ``{}`` 按位置消耗实参，槽位数多于实参数时首越界槽位必抛 IndexError: Replacement index out of range——消息模板追加槽位忘记同步补实参。另有两种同族必抛形态：``{0} {}`` 自动与显式编号混用抛 ValueError: cannot switch from manual field specification to automatic field numbering（两种编号模式不能共存）；纯编号槽位越界（``{1}`` 仅一个实参）抛同类 IndexError；具名/编号槽位缺实参另归 LV-57（自动槽位缺实参归本规则）。修复：槽位与实参对齐、编号模式统一，或改 f-string（插值就地可见，编译期不可错配）。'
            ),
        ),
        _logic_entry(
            'LV-36',
            'str/bytes.split("") 空分隔符实参：必抛 ValueError（按字符/字节分割用 list(s)）',
            'P1',
            (
                'def h():\n'
                '    return "".split("")\n'
            ),
            (
                'def h(s):\n'
                '    return list(s)\n'
            ),
            (
                '分隔符为空时 str.split/rsplit 与 bytes.split/rsplit 都必抛 '
                'ValueError: empty separator——空分隔符在 shell/awk 里是合法语义，'
                'Python 契约相反。str 接收者配 ``""``、bytes/bytearray 接收者配 '
                '``b""`` 属同一条契约（bytes 接收者配空 ``""`` 抛的是 TypeError：'
                'a bytes-like object is required，不属本规则）；按字符/字节切分用 '
                '``list(s)``，按分隔符用真实分隔符，按正则用 ``re.split``。'
                '仅对接收者可静态确证为 str/bytes/bytearray 的形态判定，'
                '自定义 split 与未知接收者不套用内建契约；unbound 内建形态'
                '还须显式提供接收者。'
            ),
        ),
        _logic_entry(
            'LV-37',
            'dict.fromkeys 默认值缺陷：可变默认值全键共享（P2）/ 关键字实参必抛 TypeError（P1）',
            'P1',
            (
                'def mk(keys):\n'
                '    return dict.fromkeys(keys, value=[])\n'
            ),
            (
                'def mk(keys):\n'
                '    return {k: [] for k in keys}\n'
            ),
            (
                'fromkeys 的默认值按引用挂到每个键上（不复制）——任一键下 append/update 被所有键同时读到，跨键数据串扰且无报错信号；意图「每键独立容器」须用推导式 ``{k: [] for k in keys}``（与 B24 乘法复制同根因家族）。字面量 ``[]``/``{}`` 与构造器 ``list()``/``dict()``/``set()``/``bytearray()`` 同口径：都是「一个新建可变对象」被全键共享。另：fromkeys 是位置专用签名（``dict.fromkeys() takes no keyword arguments``），``dict.fromkeys(keys, value=[])`` 一执行即 TypeError（P1 形态），与共享默认值是两种缺陷。'
            ),
        ),
        _logic_entry(
            'LV-38', 'defaultdict 默认工厂传非 callable 字面量：first argument must be callable TypeError', 'P1',
            (
                'import collections\n'
                'def mk():\n'
                '    return collections.defaultdict([])\n'
            ),
            (
                'import collections\n'
                'def mk():\n'
                '    return collections.defaultdict(list)\n'
            ),
            (
                'defaultdict 默认工厂必须是 callable，容器字面量或标量常量形态（如 ``defaultdict([])`` / ``defaultdict(0)``）在构造时即抛 TypeError: first argument must be callable or None——意图「每键自动空列表」须传 ``list`` 类对象本身（``defaultdict(list)``），混淆了工厂与工厂产物。'
            ),
        ),
        _logic_entry(
            'LV-39', '纯函数结果作独立语句丢弃：sorted/map/filter/reversed/re.sub 排序与变换静默失效', 'P2',
            (
                'def sort_it(items):\n'
                '    sorted(items)\n'
                '    return items\n'
            ),
            (
                'def sort_it(items):\n'
                '    return sorted(items)\n'
            ),
            (
                'sorted/map/filter/reversed/re.sub 是纯函数——返回新值不修改原对象，作为独立语句调用时结果直接丢弃，排序/替换/过滤整体未生效，后续逻辑建立在未生效假设上静默出错；须接收返回值（``items = sorted(items)``），确需就地变更用原地方言 ``items.sort()``（与 B22 str 方法丢弃域互补）。'
            ),
        ),
        _logic_entry(
            'LV-40', 'key 实参传函数调用结果：len(x) 等返回非 callable，首元素比较必 TypeError', 'P1',
            (
                'def pick(items):\n'
                '    return max(items, key=len(items))\n'
            ),
            (
                'def pick(items):\n'
                '    return max(items, key=len)\n'
            ),
            (
                'sorted/max/min/sort 的 key 必须是 callable（每元素调用一次），``key=len(items)`` 传入的是 int 结果，首元素比较时即抛 TypeError: object is not callable——意图是传函数本身 ``key=len``（无实参括号）。'
            ),
        ),
        _logic_entry(
            'LV-41', '% 数字转换符配字符串实参：%d/%f 等配 str 必抛 TypeError（数量错配见 LV-23）', 'P1',
            (
                'def fmt(count):\n'
                '    return "%d" % str(count)\n'
            ),
            (
                'def fmt(count):\n'
                '    return "%s" % count\n'
            ),
            (
                '%d/%i/%f/%g/%x 等数字族转换符要求实参可转数字，str/bytes 实参必抛 TypeError: a real number is required, not str——把用户输入/名称字段直接配进计数/金额占位符；字符串内容用 %s 或 f-string，需要数字时显式 ``int(x)`` 并处理 ValueError（与 LV-23 数量错配同域互补）。'
            ),
        ),
        _logic_entry(
            'LV-42', '% 多占位符配列表实参：列表整体作单值，必抛 not enough arguments TypeError', 'P1',
            (
                'def fmt2(a, b):\n'
                '    return "%s-%s" % [a, b]\n'
            ),
            (
                'def fmt2(a, b):\n'
                '    return "%s-%s" % (a, b)\n'
            ),
            (
                '% 格式化右侧仅元组被展开为多实参，列表作为单个值整体消费——两个及以上占位符配列表必抛 TypeError: not enough arguments for format string；方括号/圆括号笔误，意图多值格式化须用元组，或改 f-string 消除括号歧义。'
            ),
        ),
        _logic_entry(
            'LV-43', 'for 键值解包直接迭代键的 dict：迭代产出键，解包按键形态抛 ValueError/TypeError（漏 .items()）', 'P1',
            (
                'def process():\n'
                '    d = {"a": 1, "b": 2}\n'
                '    out = []\n'
                '    for k, v in d:\n'
                '        out.append(v)\n'
                '    return out\n'
            ),
            (
                'def process():\n'
                '    d = {"a": 1, "b": 2}\n'
                '    out = []\n'
                '    for k, v in d.items():\n'
                '        out.append(v)\n'
                '    return out\n'
            ),
            (
                '直接迭代 dict 只产出键（单个键对象）——漏写 ``.items()``。首个键的实际后果由键形态决定：长度 ≠ 解包元数的 str/bytes 抛 ``ValueError: not enough values to unpack``；int/float/bool/None 等标量键不可迭代，抛 ``TypeError: cannot unpack non-iterable``；长度恰等于元数的 str/bytes 更隐蔽——不报错，而是把键按字符/字节静默拆给各目标名（无异常、值全错）。键值成对遍历用 ``for k, v in d.items():``，仅需键用 ``for k in d:``。键本身为元组的 dict（如 Counter 以二元组为键）解包是合法惯用法，不在此列。'
            ),
        ),
        _logic_entry(
            'LV-44', '异族二元拼接："a" + 1 / [1] + (2,) / str 拼接 int 参数：一执行即 TypeError', 'P1',
            (
                'def tag(count: int):\n'
                '    return "item-" + count\n'
            ),
            (
                'def tag(count: int):\n'
                '    return f"item-{count}"\n'
            ),
            (
                'Python ``+`` 不做跨类型族隐式转换：str+num/序列跨族/str+bytes'
                ' 一执行即 ``TypeError: can only concatenate str`` / '
                '``unsupported operand type(s) for +``。静态确证两通道：字面量'
                '对（``"a" + 1``）与类型注解名（``"item-" + count: int``——'
                '参数注解及有实际值证据的局部绑定可判型；无值注解不创建绑定，'
                '未知运行值不被注解覆盖）。文案拼接用 f-string 或 str() 归族；'
                'dict/set 合并用 ``|``/update（不支持 +）。'
            ),
        ),
        _logic_entry(
            'LV-45', '就地变更方法链式续接：lst.append(a).append(b) 返回 None 续接必 AttributeError', 'P1',
            (
                'def push(queue, item):\n'
                '    queue.append(item).append(item)\n'
            ),
            (
                'def push(queue, item):\n'
                '    queue.append(item)\n'
                '    queue.append(item)\n'
                '    return queue\n'
            ),
            (
                '就地变更方法（sort/append/update/add 家族，SSOT 集合与 LV-02 '
                '同源）原地修改、返回 None——返回值上续接属性访问必 '
                '``AttributeError: NoneType object has no attribute``。fluent '
                '链式思维（JS 数组链风格）不适用 Python 内建容器 mutator；'
                '拆独立语句逐个调用，需要链式结果用 sorted()/reversed() 等'
                '函数式等价物。'
            ),
        ),
        _logic_entry(
            'LV-46', '类方法引用 self 但参数表无 self/cls：实例调用即 TypeError（无位置形参）/ NameError（有位置形参）', 'P1',
            (
                'class Box:\n'
                '    def area():\n'
                '        return self.w * self.h\n'
            ),
            (
                'class Box:\n'
                '    def area(self):\n'
                '        return self.w * self.h\n'
            ),
            (
                'Python 实例方法不经显式首参声明不绑定 self——类体内 '
                '``def area():`` 引用 ``self``。实例调用把实例当额外位置实参'
                '传入：无位置形参时先撞参数个数检查（``TypeError: area() '
                'takes 0 positional arguments but 1 was given``）；有位置形参'
                '时实例被填进首个形参，体内 ``self`` 才以自由名解析失败'
                "（``NameError: name 'self' is not defined``）；按未绑定方式"
                '``Cls.area()`` 调用同样走 NameError。实例方法首参须 self、'
                '类方法首参须 cls（配 @classmethod）；不访问实例态的方法标 '
                '@staticmethod 并移除 self 引用。类体内嵌套函数引用外层 '
                'self 的合法闭包形态不在此列。'
            ),
        ),
        _logic_entry(
            'LV-47', '__init__ 带值 return：实例化即 TypeError should return None', 'P1',
            (
                'class Session:\n'
                '    def __init__(self, user):\n'
                '        self.user = user\n'
                '        return user\n'
            ),
            (
                'class Session:\n'
                '    def __init__(self, user):\n'
                '        self.user = user\n'
            ),
            (
                '``__init__`` 的返回契约恒为 None——带值 return 在实例化完成时'
                '由类型机制抛 ``TypeError: __init__() should return None``。'
                '构造器按「出口必带值」普通函数直觉生成是高频形态；构造失败'
                '用 raise 异常而非返回错误值，裸 return/return None 合法，'
                '``return None if c else None``（两分支同为 None）返回值仍为'
                'None，同属合法。'
            ),
        ),
        _logic_entry(
            'LV-48', 'json.dump/dumps 缺 obj、重复 obj 或 dump/dumps 其他实参形态错配：一执行即 TypeError', 'P2',
            (
                'import json\n'
                '\n\n'
                'def save(obj):\n'
                '    json.dump(obj, "out.json")\n'
            ),
            (
                'import json\n'
                '\n\n'
                'def save(obj, path):\n'
                '    with open(path, "w", encoding="utf-8") as f:\n'
                '        json.dump(obj, f)\n'
            ),
            (
                '``json.dump(obj, fp)`` 序列化直写文件对象（fp 必填）、'
                '``json.dumps(obj)`` 序列化返回 str（仅单位置实参）——dump=落盘、'
                'dumps=到 str（s 同 string 口诀，与 LV-26 对偶）。obj 缺失或'
                '位置/关键字重复传入、dump 缺 fp、dumps 多位置实参、'
                'dump 的 fp 位传 str/bytes/f-string、None、数值或容器字面量'
                '（均无 write）均在调用时即 TypeError/AttributeError；'
                'obj=/fp= 合法关键字形态与文件对象变量不误报。'
            ),
        ),
        _logic_entry(
            'LV-49', 'str/bytes.join 非字符串元素序列：",".join([1, 2]) 必 TypeError', 'P1',
            (
                'def fmt(nums):\n'
                '    return ",".join([1, 2, 3])\n'
            ),
            (
                'def fmt(nums):\n'
                '    return ",".join(str(n) for n in nums)\n'
            ),
            (
                '``sep.join(iterable)`` 要求元素与 sep 同族（str.join 要 str、'
                'bytes.join 要 bytes）——首个异族元素即 ``TypeError: sequence '
                'item 0: expected str instance, int found``。整数字段拼接先转 '
                'str（map(str, nums)/f-string）；``"".join(range(10))`` 同罪'
                '（range 元素恒 int）。join 无隐式转换，与 %s/f-string 的'
                '自动 str() 行为相反。'
            ),
        ),
        _logic_entry(
            'LV-50', '裸内建谓词函数对象作条件：if any: 恒真守卫失效（漏调用括号）', 'P1',
            (
                'def has_any(items):\n'
                '    if any:\n'
                '        return True\n'
                '    return False\n'
            ),
            (
                'def has_any(items):\n'
                '    if any(items):\n'
                '        return True\n'
                '    return False\n'
            ),
            (
                '内建谓词函数对象（any/all/len/isinstance 家族）本身恒真值——'
                '``if any:`` 等价 ``if True:``，分支恒走、while 形态不可终止；'
                '取反形态 ``if not any:`` 恒为 False，分支永不进入；作为 '
                '``and``/``or`` 链操作数时该操作数被短路语义静默丢弃。三类'
                '形态均无任何报错（比 TypeError 更隐蔽），guard 改写时丢'
                '调用括号是成因；仅当前词法作用域可见的绑定点（用户重定义）'
                '才放行，兄弟函数的同名局部绑定不会污染本作用域判定。'
            ),
        ),
        _logic_entry(
            'LV-51', 'open 纯读/纯写模式与操作错配：r 模式 write 即 io.UnsupportedOperation', 'P1',
            (
                'def dump(path, data):\n'
                '    with open(path) as f:\n'
                '        f.write(data)\n'
            ),
            (
                'def dump(path, data):\n'
                '    with open(path, "w", encoding="utf-8") as f:\n'
                '        f.write(data)\n'
            ),
            (
                'open 模式与块内操作集须对齐：纯读（r，含缺省）禁 write/'
                'writelines、纯写（w/a/x）禁 read/readline/readlines——首次'
                '调用即 ``io.UnsupportedOperation: not writable/readable``。'
                '忘传 mode 就写、按「先读后写」直觉误开纯写流是高频形态；'
                '读写双开用 r+（保留原内容）或 w+（清空重写）。'
            ),
        ),
        _logic_entry(
            'LV-52', 'is/is not 比较非单例字面量：x is 200 identity 语义误用恒不可靠', 'P2',
            (
                'def is_ok(status):\n'
                '    return status is 200\n'
            ),
            (
                'def is_ok(status):\n'
                '    return status == 200\n'
            ),
            (
                '``is`` 判 identity（同一对象），值比较必须 ``==``：``x is 200`` '
                '/ ``s is "done"`` 在小整数缓存/字符串驻留/常量折叠下可能'
                '「碰巧成立」，运行时构造的等值对象即判假——实现细节依赖的'
                '潜伏缺陷，跨解释器行为不稳（ruff F632 同源）。is 仅用于单例'
                '判定（is None/is True）与 sentinel 惯用法。'
            ),
        ),
        _logic_entry(
            'LV-53', 'input() 产出 str 与数字字面量比较：有序必 TypeError，等值恒假/恒真', 'P1',
            (
                'def gate():\n'
                '    age = input("age: ")\n'
                '    if age > 18:\n'
                '        return "adult"\n'
                '    return "minor"\n'
            ),
            (
                'def gate():\n'
                '    age = int(input("age: "))\n'
                '    if age > 18:\n'
                '        return "adult"\n'
                '    return "minor"\n'
            ),
            (
                'Python3 ``input()`` 恒返回 str——与数字字面量做有序比较'
                '（``< <= > >=``）必抛 TypeError；做 ``==``/``!=`` 则恒假'
                '/恒真（无异常信号更隐蔽）。交互读数必须先 ``int(...)/'
                'float(...)`` 显式转换（配合 try 容错非法输入）再参与'
                '数值比较。'
            ),
        ),
        _logic_entry(
            'LV-54', 'print() 返回值赋值/海象绑定：恒 None 落绑，下游消费即错', 'P1',
            (
                'def notify(msg):\n'
                '    sent = print(msg)\n'
                '    return sent\n'
            ),
            (
                'def notify(msg):\n'
                '    print(msg)\n'
                '    return True\n'
            ),
            (
                '``print()`` 的副作用契约是「输出到 stdout」，返回契约'
                '固定为 None——``sent = print(msg)`` 从绑定起即 None：'
                '下游对它做拼接/算术即 TypeError 后移，做 ``if sent:``'
                '恒假形成静默守卫失效。保留 print 独立语句；意图产'
                '出值应 return 真实结果而非 print 的返回值。'
            ),
        ),
        _logic_entry(
            'LV-55', '循环/推导式内 lambda 捕获循环变量未固定：迟绑定，全部回调读终值', 'P2',
            (
                'def build_handlers(ids):\n'
                '    return [lambda: handle(i) for i in ids]\n'
            ),
            (
                'def build_handlers(ids):\n'
                '    return [lambda i=i: handle(i) for i in ids]\n'
            ),
            (
                'Python 闭包按名字捕获（late binding），def 时不求值——'
                '循环结束后所有 lambda 读取同一变量的终值：回调表/映射表'
                '全部静默错位且无异常。用默认参数固定当轮值（``lambda '
                'i=i: ...``）、functools.partial 或具名函数工厂；直接作'
                '调用实参的 lambda（key= 当轮消费）不迟绑，不在此域。'
            ),
        ),
        _logic_entry(
            'LV-56', 'async def 函数裸调用结果丢弃：协程永不执行，函数体整体失效', 'P1',
            (
                'async def fetch():\n'
                '    return 1\n'
                '\n'
                'def run():\n'
                '    fetch()\n'
            ),
            (
                'async def fetch():\n'
                '    return 1\n'
                '\n'
                'async def run():\n'
                '    await fetch()\n'
            ),
            (
                'async def 调用语义=造协程对象，帧推进依赖 await/事件循'
                '环接管—— ``fetch()`` 单独成行只创建即丢弃，函数体一次'
                '都不执行，仅产生 RuntimeWarning（多数环境不可见）。异'
                '步上下文 ``await f()``；同步入口 ``asyncio.run(f())``；'
                '并发编排 ``asyncio.create_task(f())``（须持有 task 引用）。'
            ),
        ),
        _logic_entry(
            'LV-57', 'str.format 具名/编号槽位缺对应实参：必 KeyError/IndexError', 'P1',
            (
                'def greet():\n'
                '    return "Hello {name}, uid={uid}".format(name="x")\n'
            ),
            (
                'def greet(uid):\n'
                '    return "Hello {name}, uid={uid}".format(name="x", uid=uid)\n'
            ),
            (
                '具名槽位 ``{uid}`` 无同名关键字实参必抛 ``KeyError: '
                "\'uid\'``；"
                '编号槽位 ``{1}`` 越界位置实参必抛 IndexError（含 format'
                '_spec 嵌套槽位 ``{:{w}}``）。*args 只使编号槽位数量未知，'
                '不能提供具名槽位；**kwargs 只使具名槽位未知，不能提供编号槽位。'
                '模板与实参各自演化（改名'
                '漏单侧）是高频成因；推荐 f-string——插值就地可见，'
                '编译期不可错配。'
            ),
        ),
        _logic_entry(
            'LV-58', 'dict.keys()/values()/items() 视图与 list/tuple 字面量 == / !=：恒假/恒真', 'P2',
            (
                'def has_all():\n'
                '    d = {"a": 1, "b": 2}\n'
                '    return d.keys() == ["a", "b"]\n'
            ),
            (
                'def has_all():\n'
                '    d = {"a": 1, "b": 2}\n'
                '    return list(d.keys()) == ["a", "b"]\n'
            ),
            (
                '``dict.keys()/values()/items()`` 返回视图对象：keys/items 支持'
                '集合语义，values 仅按 identity 判断；三者都不与 list/tuple '
                '逐元素比较，序列字面量比较恒为 False（==）/True（!=），'
                '结果与字典内容完全无关，守卫静默失效且无异常。序列断言先 '
                '``list(d.keys())``；集合语义比较仅 keys/items 可换集合字面量 '
                '``{...}``。'
            ),
        ),
        _logic_entry(
            'LV-59', '生成器函数带值 return：值经 StopIteration.value 被静默吞没', 'P2',
            (
                'def collect(items):\n'
                '    out = []\n'
                '    for x in items:\n'
                '        yield x\n'
                '    return out\n'
            ),
            (
                'def collect(items):\n'
                '    for x in items:\n'
                '        yield x\n'
            ),
            (
                '生成器的产出协议是 yield 序列；``return value`` 不是数'
                '据通道——值装入 ``StopIteration.value``，``for``/``list('
                'gen())`` 等常规消费方整体丢弃（仅 ``yield from`` 委托链'
                '能拿到）。意图传出累计值时改 yield 并入产出序列，或改'
                '非生成器函数收集后真正 return。'
            ),
        ),
        _logic_entry(
            'LV-60', 'open 二进制/文本模式与 write 实参载体错配：首调即 TypeError', 'P1',
            (
                'def save(path):\n'
                '    with open(path, "wb") as f:\n'
                '        f.write("binary payload")\n'
            ),
            (
                'def save(path):\n'
                '    with open(path, "wb") as f:\n'
                '        f.write("binary payload".encode("utf-8"))\n'
            ),
            (
                'write 的实参类型契约与流类型绑死：二进制流只收 bytes'
                '（写入 str 即 ``TypeError: a bytes-like object is '
                'required``）；文本流只收 str（写入 bytes 即 '
                '``TypeError: write() argument must be str, not bytes``'
                '）。b 模式消不掉编码义务——payload 先 ``.encode()``，'
                '文本流反之 ``.decode()``。可确证载体四类：str/bytes '
                '常量、f-string（恒产 str）与 ``str()``/``bytes()``/'
                '``bytearray()`` 构造调用；变量承载形态无静态证据已放行。'
            ),
        ),
        _logic_entry(
            'LV-61', '字面量赋值遮蔽内建名后按内建语义调用：TypeError not callable', 'P1',
            (
                'def first():\n'
                '    list = [10, 20]\n'
                '    return list("ab")\n'
            ),
            (
                'def first():\n'
                '    pair = [10, 20]\n'
                '    return list(["a", "b"])\n'
            ),
            (
                '赋值把内建名遮蔽为不可调用对象——``list(x)`` 读到的'
                '是遮蔽值而非内建构造函数，续接调用即 ``TypeError: '
                "\'list\' object is not callable``"
                '。list/dict/type/id/input/print/next 是直觉命名撞内建'
                '的超高频名；变量改用语义名（items/values/xxx_list），'
                '遮蔽落在条件分支时路径相关同样必崩。'
            ),
        ),
    ],
    "LOGIC_CODE_REFS",
)
def _assert_direct_checks_aligned() -> None:
    direct = set(LOGIC_DIRECT_CHECKS)
    refs = set(LOGIC_CODE_REFS)
    orphan = sorted(direct - refs)
    missing = sorted(refs - direct)
    absent = sorted(_LOGIC_RULE_IDS - (direct | refs))
    unexpected = sorted((direct | refs) - _LOGIC_RULE_IDS)
    problems = []
    if orphan:
        problems.append(f'多余直调={orphan}')
    if missing:
        problems.append(f'缺失直调={missing}')
    if absent:
        problems.append(f'双方缺号={absent}')
    if unexpected:
        problems.append(f'越界编号={unexpected}')
    if problems:
        raise RuntimeError(
            'LOGIC_DIRECT_CHECKS 与 LOGIC_CODE_REFS 不一致：'
            + '；'.join(problems)
        )
_assert_direct_checks_aligned()
register_code_refs(LOGIC_CODE_REFS, 'prevention_logic_refs')
_log.info("prevention_logic_refs 逻辑缺陷专项预防库已注册完成：%d 条规则，版本 %s",
          len(LOGIC_CODE_REFS), LOGIC_CODE_REFS_VERSION)
def list_logic_rule_ids() -> list[str]:
    return sorted(LOGIC_CODE_REFS)
def wiring_declarations() -> dict[str, dict[str, dict[str, Callable[..., Any]]]]:
    return {
        "catalogs": {
            "rule_bindings": {
                rule_id.replace("-", ""): check_fn
                for rule_id, check_fn in LOGIC_DIRECT_CHECKS.items()
            },
        },
    }
