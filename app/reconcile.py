"""多轮筛查累计检出核算（内部使用）。

模型
----
固定调查为首轮：每个调查格的在册人员即首轮受检人员，首轮检出数取自固定调查。
之后两轮各格填报「受检人数」「检出人数」；三对轮次另填「两轮均受检人数」
与「两轮均检出人数」。每个人在三轮中始终属于同一调查格，每轮状态为：

    未受检 / 受检未检出 / 检出

因此每个格内的人可以按 18 种状态组合（首轮无「未受检」）分配人数。
所有计数都是对这些整数分配人数的线性等式。若干计数无法同时成立时，约束整体
不可满足；此时返回最小不可满足的填报项组（冲突格/配对行），不输出全表结果。

可行时用 z3 Optimize 求：
- 每个格「至少检出过一次」的人数的上下界；
- 全表「至少检出过一次」的人数的上下界；
- 每个格达到各自两个端点时的一份状态组合及人数（各由一份满足全部计数的
  整数分配给出；不同格的端点组合不保证能拼成同一份分配），
  以及全表达到上下界时的完整分配。
"""

from __future__ import annotations

import time

from z3 import And, Bool, Context, Int, Optimize, Solver, Sum, sat, unknown, unsat

# 每轮状态码：0 未受检，1 受检未检出，2 检出
STATE_NAMES = {0: "未受检", 1: "受检未检出", 2: "检出"}
STATE_CODES = {0: "U", 1: "T", 2: "D"}

# 首轮为固定调查，在册人员全部受检，故首轮状态不含 0。
PATTERNS: list[tuple[int, int, int]] = [
    (a, b, c) for a in (1, 2) for b in (0, 1, 2) for c in (0, 1, 2)
]

PAIRS = [(1, 2), (1, 3), (2, 3)]

DEFAULT_TIMEOUT_MS = 30000  # 单次求解上限
DEFAULT_TOTAL_TIMEOUT_MS = 120000  # 一次核算所有求解的总预算

# 填报项标签（用于冲突说明）
FIELD_NAMES = {
    "survey": "固定调查（人数/首轮检出）",
    "tested2": "第 2 轮受检人数",
    "detected2": "第 2 轮检出人数",
    "tested3": "第 3 轮受检人数",
    "detected3": "第 3 轮检出人数",
    "both_tested": "两轮均受检人数",
    "both_detected": "两轮均检出人数",
}


class ReconcileUnsolved(Exception):
    """求解器未能给出确定结论（超时等）。"""


def cell_key(cell: dict) -> tuple[str, str]:
    return cell["district"], cell["age_group"]


def _sum_for(ns, pred):
    idx = [i for i, p in enumerate(PATTERNS) if pred(p)]
    return Sum([ns[i] for i in idx])


def _cell_ever_detected(ns):
    return _sum_for(ns, lambda p: 2 in p)


def _build_problem(ctx: Context, cells: list[dict], cell_inputs: dict, pair_inputs: dict):
    """返回 (每格状态变量, 约束组列表)。

    约束组以「填报项」为单位，便于把不可满足性定位到具体格的具体填报项。
    每个约束组为 (类型, 键, 填报项, 约束列表)。

    变量的命名与整数取值本身即保证：每组状态组合的非负人数之和等于该格人数，
    且首轮无「未受检」状态（固定调查在册人员即首轮受检人员）。
    """
    groups: list[tuple[str, object, str, list]] = []
    all_ns = []
    for cell in cells:
        key = cell_key(cell)
        inp = cell_inputs[key]
        ns = [Int(f"n_{len(all_ns)}_{j}", ctx=ctx) for j in range(len(PATTERNS))]
        all_ns.append(ns)
        pop = int(cell["population"])
        groups.append(
            (
                "cell",
                key,
                "survey",
                [n >= 0 for n in ns]
                + [
                    Sum(ns) == pop,
                    _sum_for(ns, lambda p: p[0] == 2) == int(cell["detected"]),
                ],
            )
        )
        groups.append(
            ("cell", key, "tested2", [_sum_for(ns, lambda p: p[1] >= 1) == int(inp["tested2"])])
        )
        groups.append(
            ("cell", key, "detected2", [_sum_for(ns, lambda p: p[1] == 2) == int(inp["detected2"])])
        )
        groups.append(
            ("cell", key, "tested3", [_sum_for(ns, lambda p: p[2] >= 1) == int(inp["tested3"])])
        )
        groups.append(
            ("cell", key, "detected3", [_sum_for(ns, lambda p: p[2] == 2) == int(inp["detected3"])])
        )

    for r1, r2 in PAIRS:
        a, b = r1 - 1, r2 - 1
        inp = pair_inputs[(r1, r2)]
        groups.append(
            (
                "pair",
                (r1, r2),
                "both_tested",
                [
                    Sum(
                        [
                            all_ns[i][j]
                            for i in range(len(cells))
                            for j, p in enumerate(PATTERNS)
                            if p[a] >= 1 and p[b] >= 1
                        ]
                    )
                    == int(inp["both_tested"])
                ],
            )
        )
        groups.append(
            (
                "pair",
                (r1, r2),
                "both_detected",
                [
                    Sum(
                        [
                            all_ns[i][j]
                            for i in range(len(cells))
                            for j, p in enumerate(PATTERNS)
                            if p[a] == 2 and p[b] == 2
                        ]
                    )
                    == int(inp["both_detected"])
                ],
            )
        )
    return all_ns, groups


def _flatten(groups: list) -> list:
    return [c for _, _, _, cons in groups for c in cons]


def _minimal_core(ctx: Context, groups: list, deadline: float) -> list[int]:
    """求最小不可满足的填报项集合（先取跟踪核心，再贪心删除）。"""

    def build(indices) -> Solver:
        s = Solver(ctx=ctx)
        s.set("timeout", _remaining(deadline))
        s.set("unsat_core", True)
        for i in indices:
            s.assert_and_track(And(groups[i][3]), Bool(f"grp_{i}", ctx=ctx))
        return s

    every = list(range(len(groups)))
    solver = build(every)
    status = solver.check()
    if status == unknown:
        raise ReconcileUnsolved("定位冲突超时，未得出确定结果")
    if status != unsat:  # pragma: no cover - 与整体可行性判定一致
        return every
    active = {int(str(b).removeprefix("grp_")) for b in solver.unsat_core()}
    changed = True
    while changed:
        changed = False
        for i in sorted(active):
            trial = active - {i}
            status = build(trial).check()
            if status == unknown:
                raise ReconcileUnsolved("定位冲突超时，未得出确定结果")
            if status == unsat:
                active = trial
                changed = True
                break
    return sorted(active)


def _state_rows(model, ns) -> list[dict]:
    out = []
    for pat, var in zip(PATTERNS, ns):
        count = model.eval(var, model_completion=True).as_long()
        if count:
            out.append(
                {
                    "states": [STATE_NAMES[s] for s in pat],
                    "codes": [STATE_CODES[s] for s in pat],
                    "count": count,
                }
            )
    return out


def _assignment(model, all_ns, cells) -> list[dict]:
    return [
        {
            "district": cells[i]["district"],
            "age_group": cells[i]["age_group"],
            "states": _state_rows(model, all_ns[i]),
        }
        for i in range(len(cells))
    ]


def _as_int(value, what: str) -> int:
    try:
        return value.as_long()
    except AttributeError as exc:  # pragma: no cover - 防御性
        raise ReconcileUnsolved(f"{what} 未能取得整数结果：{value}") from exc


def _remaining(deadline: float) -> int:
    left = int((deadline - time.monotonic()) * 1000)
    if left <= 0:
        raise ReconcileUnsolved("核算超时，未得出确定结果")
    return min(DEFAULT_TIMEOUT_MS, left)


def _optimize(ctx: Context, constraints, expr, maximize: bool,
              deadline: float):
    """求 expr 的上下界，并返回一份达到该界（而非仅满足）的模型。"""
    timeout_ms = _remaining(deadline)
    opt = Optimize(ctx=ctx)
    opt.set("timeout", timeout_ms)
    opt.add(constraints)
    handle = opt.maximize(expr) if maximize else opt.minimize(expr)
    result = opt.check()
    if result != sat:
        raise ReconcileUnsolved(
            "求解超时，未得出确定结果" if str(result) == "unknown" else "约束不可满足"
        )
    value = _as_int(opt.upper(handle) if maximize else opt.lower(handle), "边界")
    model = opt.model()
    # 用模型复核端点值，避免个别版本 Optimize 返回非最优模型。
    if model.eval(expr, model_completion=True).as_long() != value:
        model = _model_at(ctx, constraints, expr, value, deadline)
    return value, model


def _model_at(ctx: Context, constraints, expr, value: int, deadline: float):
    """显式固定 expr == value 重解，保证状态组合确实达到该端点。"""
    s = Solver(ctx=ctx)
    s.set("timeout", _remaining(deadline))
    s.add(constraints)
    s.add(expr == value)
    if s.check() != sat:
        raise ReconcileUnsolved("端点状态组合无法复核")
    return s.model()


def _aggregate_reasons(cells: list[dict], cell_inputs: dict, pair_inputs: dict) -> list[str]:
    """可由合计直接判定的冲突原因（仅作补充说明，判定仍以求解为准）。"""
    tot_pop = sum(int(c["population"]) for c in cells)
    tot_d1 = sum(int(c["detected"]) for c in cells)
    tot_t2 = sum(int(cell_inputs[cell_key(c)]["tested2"]) for c in cells)
    tot_d2 = sum(int(cell_inputs[cell_key(c)]["detected2"]) for c in cells)
    tot_t3 = sum(int(cell_inputs[cell_key(c)]["tested3"]) for c in cells)
    tot_d3 = sum(int(cell_inputs[cell_key(c)]["detected3"]) for c in cells)

    b12 = int(pair_inputs[(1, 2)]["both_tested"])
    b13 = int(pair_inputs[(1, 3)]["both_tested"])
    b23 = int(pair_inputs[(2, 3)]["both_tested"])
    e12 = int(pair_inputs[(1, 2)]["both_detected"])
    e13 = int(pair_inputs[(1, 3)]["both_detected"])
    e23 = int(pair_inputs[(2, 3)]["both_detected"])

    reasons = []
    # 格内结构下界（逐格即可判定）。
    for c in cells:
        key = cell_key(c)
        inp = cell_inputs[key]
        label = f"{c['district']} / {c['age_group']}"
        pop = int(c["population"])
        if int(inp["tested2"]) > pop:
            reasons.append(f"{label}：第 2 轮受检人数 {inp['tested2']} 超过该格人数 {pop}。")
        if int(inp["detected2"]) > int(inp["tested2"]):
            reasons.append(
                f"{label}：第 2 轮检出人数 {inp['detected2']} 超过第 2 轮受检人数 {inp['tested2']}。"
            )
        if int(inp["tested3"]) > pop:
            reasons.append(f"{label}：第 3 轮受检人数 {inp['tested3']} 超过该格人数 {pop}。")
        if int(inp["detected3"]) > int(inp["tested3"]):
            reasons.append(
                f"{label}：第 3 轮检出人数 {inp['detected3']} 超过第 3 轮受检人数 {inp['tested3']}。"
            )

    # 首轮全员受检 → 与首轮配对的「均受检」必等于后一轮受检合计。
    if b12 != tot_t2:
        reasons.append(
            f"首轮为固定调查、在册人员全部受检，第 1、2 轮均受检人数应等于"
            f"第 2 轮受检合计 {tot_t2}，但填写为 {b12}。"
        )
    if b13 != tot_t3:
        reasons.append(
            f"首轮为固定调查、在册人员全部受检，第 1、3 轮均受检人数应等于"
            f"第 3 轮受检合计 {tot_t3}，但填写为 {b13}。"
        )

    def check_pair(name, both, both_cap, detected, detected_cap):
        if both > both_cap:
            reasons.append(f"{name}均受检人数 {both} 超过可容纳上限 {both_cap}。")
        if detected > both:
            reasons.append(f"{name}均检出人数 {detected} 超过该对均受检人数 {both}。")
        if detected > detected_cap:
            reasons.append(
                f"{name}均检出人数 {detected} 超过由两轮检出数推出的上限 {detected_cap}。"
            )
        if detected < 0:
            reasons.append(f"{name}均检出人数不能为负。")

    check_pair("第 1、2 轮", b12, tot_pop, e12, min(tot_d1, tot_d2))
    check_pair("第 1、3 轮", b13, tot_pop, e13, min(tot_d1, tot_d3))
    check_pair("第 2、3 轮", b23, min(tot_t2, tot_t3), e23, min(tot_d2, tot_d3))

    # 每格内的下界：两轮检出集合的并集必在两轮受检集合的并集内，
    # 故 |D2∩D3| ≥ d2 + d3 − |T2∪T3|，而 |T2∪T3| ≤ min(人数, t2+t3)。
    lower_e12 = sum(
        max(0, int(c["detected"]) + int(cell_inputs[cell_key(c)]["detected2"])
            - int(c["population"]))
        for c in cells
    )
    lower_e13 = sum(
        max(0, int(c["detected"]) + int(cell_inputs[cell_key(c)]["detected3"])
            - int(c["population"]))
        for c in cells
    )
    lower_e23 = sum(
        max(
            0,
            int(cell_inputs[cell_key(c)]["detected2"])
            + int(cell_inputs[cell_key(c)]["detected3"])
            - min(
                int(c["population"]),
                int(cell_inputs[cell_key(c)]["tested2"])
                + int(cell_inputs[cell_key(c)]["tested3"]),
            ),
        )
        for c in cells
    )
    lower_b23 = sum(
        max(
            0,
            int(cell_inputs[cell_key(c)]["tested2"])
            + int(cell_inputs[cell_key(c)]["tested3"])
            - int(c["population"]),
        )
        for c in cells
    )
    upper_e23 = sum(
        min(
            int(cell_inputs[cell_key(c)]["detected2"]),
            int(cell_inputs[cell_key(c)]["detected3"]),
        )
        for c in cells
    )
    upper_b23 = sum(
        min(
            int(cell_inputs[cell_key(c)]["tested2"]),
            int(cell_inputs[cell_key(c)]["tested3"]),
        )
        for c in cells
    )
    if e12 < lower_e12:
        reasons.append(f"第 1、2 轮均检出人数 {e12} 低于由各格两轮检出数推出的下界 {lower_e12}。")
    if e13 < lower_e13:
        reasons.append(f"第 1、3 轮均检出人数 {e13} 低于由各格两轮检出数推出的下界 {lower_e13}。")
    if e23 < lower_e23:
        reasons.append(f"第 2、3 轮均检出人数 {e23} 低于由各格两轮检出数推出的下界 {lower_e23}。")
    if b23 < lower_b23:
        reasons.append(f"第 2、3 轮均受检人数 {b23} 低于由各格受检数推出的下界 {lower_b23}。")
    if b23 > upper_b23:
        reasons.append(f"第 2、3 轮均受检人数 {b23} 超过由各格受检数推出的上界 {upper_b23}。")
    if e23 > upper_e23:
        reasons.append(f"第 2、3 轮均检出人数 {e23} 超过由各格检出数推出的上界 {upper_e23}。")
    return reasons


def reconcile(
    cells: list[dict],
    cell_inputs: dict,
    pair_inputs: dict,
    total_timeout_ms: int = DEFAULT_TOTAL_TIMEOUT_MS,
) -> dict:
    """执行整数分配核算。

    cells:      固定调查格 {district, age_group, population, detected}
    cell_inputs: {(district, age_group): {tested2, detected2, tested3, detected3}}
    pair_inputs: {(1,2)|(1,3)|(2,3): {both_tested, both_detected}}
    返回可行时的上下界与端点状态组合；不可行时只返回冲突信息。
    """
    deadline = time.monotonic() + total_timeout_ms / 1000
    ctx = Context()
    all_ns, groups = _build_problem(ctx, cells, cell_inputs, pair_inputs)
    constraints = _flatten(groups)

    base = Solver(ctx=ctx)
    base.set("timeout", _remaining(deadline))
    base.add(constraints)
    status = base.check()
    if status == unsat:
        core = _minimal_core(ctx, groups, deadline)
        core_cells: dict[tuple, dict] = {}
        core_pairs: dict[tuple, dict] = {}
        for i in core:
            kind, key, field, _ = groups[i]
            if kind == "cell":
                cell = next(c for c in cells if cell_key(c) == key)
                inp = cell_inputs[key]
                entry = core_cells.setdefault(
                    key,
                    {
                        "district": cell["district"],
                        "age_group": cell["age_group"],
                        "population": int(cell["population"]),
                        "detected1": int(cell["detected"]),
                        "tested2": int(inp["tested2"]),
                        "detected2": int(inp["detected2"]),
                        "tested3": int(inp["tested3"]),
                        "detected3": int(inp["detected3"]),
                        "fields": [],
                    },
                )
                label = FIELD_NAMES[field]
                if label not in entry["fields"]:
                    entry["fields"].append(label)
            else:
                inp = pair_inputs[key]
                entry = core_pairs.setdefault(
                    key,
                    {
                        "rounds": list(key),
                        "both_tested": int(inp["both_tested"]),
                        "both_detected": int(inp["both_detected"]),
                        "fields": [],
                    },
                )
                label = FIELD_NAMES[field]
                if label not in entry["fields"]:
                    entry["fields"].append(label)
        return {
            "feasible": False,
            "conflict": {
                "message": "所填计数无法同时成立，未生成全表结果。",
                "cells": list(core_cells.values()),
                "pairs": list(core_pairs.values()),
                "reasons": _aggregate_reasons(cells, cell_inputs, pair_inputs),
            },
        }
    if status != sat:  # pragma: no cover - timeout
        raise ReconcileUnsolved("求解超时，未得出确定结果")

    # 全表上下界
    total_expr = Sum([_cell_ever_detected(ns) for ns in all_ns])
    total_min, min_model = _optimize(ctx, constraints, total_expr, False, deadline)
    total_max, max_model = _optimize(ctx, constraints, total_expr, True, deadline)

    cell_rows = []
    for i, cell in enumerate(cells):
        key = cell_key(cell)
        inp = cell_inputs[key]
        expr = _cell_ever_detected(all_ns[i])
        lo, lo_model = _optimize(ctx, constraints, expr, False, deadline)
        hi, hi_model = _optimize(ctx, constraints, expr, True, deadline)
        cell_rows.append(
            {
                "district": cell["district"],
                "age_group": cell["age_group"],
                "population": int(cell["population"]),
                "detected1": int(cell["detected"]),
                "tested2": int(inp["tested2"]),
                "detected2": int(inp["detected2"]),
                "tested3": int(inp["tested3"]),
                "detected3": int(inp["detected3"]),
                "min": lo,
                "max": hi,
                "min_states": _state_rows(lo_model, all_ns[i]),
                "max_states": _state_rows(hi_model, all_ns[i]),
            }
        )

    return {
        "feasible": True,
        "total": {
            "min": total_min,
            "max": total_max,
            "min_assignment": _assignment(min_model, all_ns, cells),
            "max_assignment": _assignment(max_model, all_ns, cells),
        },
        "cells": cell_rows,
        "pairs": [
            {
                "rounds": list(pair),
                "both_tested": int(pair_inputs[pair]["both_tested"]),
                "both_detected": int(pair_inputs[pair]["both_detected"]),
            }
            for pair in PAIRS
        ],
    }
