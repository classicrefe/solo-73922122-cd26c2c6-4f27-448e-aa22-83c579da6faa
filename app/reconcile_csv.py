"""核算 CSV 的模板生成与解析（内部页使用）。

CSV 表头（7 列）：

    分区,年龄组,轮次,受检人数,检出人数,两轮均受检人数,两轮均检出人数

- 格行：填分区、年龄组；轮次为 2 或 3；填该轮受检人数与检出人数；
  两个「两轮均…」列留空。
- 配对行：分区、年龄组留空；轮次为 1-2 / 1-3 / 2-3；受检、检出列留空；
  填该对轮次的均受检人数与均检出人数。

固定调查即首轮，不在 CSV 中重复填报。
"""

from __future__ import annotations

import csv
import io
import re
import unicodedata
from decimal import Decimal, InvalidOperation

HEADER = [
    "分区",
    "年龄组",
    "轮次",
    "受检人数",
    "检出人数",
    "两轮均受检人数",
    "两轮均检出人数",
]

_ALIASES = {
    "district": {"分区", "district", "地区", "区域"},
    "age_group": {"年龄组", "age_group", "agegroup", "age"},
    "round": {"轮次", "round", "rounds", "轮"},
    "tested": {"受检人数", "tested", "tested_count", "受检数"},
    "detected": {"检出人数", "detected", "detected_count", "检出数"},
    "both_tested": {"两轮均受检人数", "both_tested", "both_tested_count"},
    "both_detected": {"两轮均检出人数", "both_detected", "both_detected_count"},
}

PAIR_ORDER = [(1, 2), (1, 3), (2, 3)]
PAIR_LABELS = {(1, 2): "1-2", (1, 3): "1-3", (2, 3): "2-3"}

_CN_DIGITS = {"一": "1", "二": "2", "三": "3", "1": "1", "2": "2", "3": "3"}


class ReconcileCsvError(ValueError):
    """核算 CSV 结构或取值错误（尚未进入可行性核算）。"""


def build_template(cells: list[dict]) -> str:
    """按当前固定调查格生成空白核算模板。"""
    buf = io.StringIO(newline="")
    writer = csv.writer(buf)
    writer.writerow(HEADER)
    for cell in sorted(cells, key=lambda c: (c["district"], c["age_group"])):
        for rnd in (2, 3):
            writer.writerow([cell["district"], cell["age_group"], rnd, "", "", "", ""])
    for pair in PAIR_ORDER:
        writer.writerow(["", "", PAIR_LABELS[pair], "", "", "", ""])
    return "﻿" + buf.getvalue()


def _normalize_round(raw: str) -> tuple[str, int | tuple[int, int]]:
    # NFKC 把全角数字/符号（２、１～２、－）折成半角
    text = unicodedata.normalize("NFKC", str(raw)).strip().lower()
    for ch in ("第", "轮", "round", " ", "\t"):
        text = text.replace(ch, "")
    for ch in ("—", "–", "~", "～", "、", "，", ",", "/", "_"):
        text = text.replace(ch, "-")
    for cn, digit in _CN_DIGITS.items():
        text = text.replace(cn, digit)
    text = re.sub(r"-+", "-", text).strip("-")
    if text in ("2", "3"):
        return "cell", int(text)
    if text in ("1", "01"):
        raise ReconcileCsvError(
            "首轮即固定调查（在册人员全部受检、检出数取自固定调查），无需填报第 1 轮"
        )
    if text in ("1-2", "2-1"):
        return "pair", (1, 2)
    if text in ("1-3", "3-1"):
        return "pair", (1, 3)
    if text in ("2-3", "3-2"):
        return "pair", (2, 3)
    raise ReconcileCsvError(
        f"无法识别轮次 {raw!r}：格行请填 2 或 3，配对行请填 1-2、1-3 或 2-3"
    )


def _int_value(raw: str, lineno: int, column: str) -> int:
    text = unicodedata.normalize("NFKC", str(raw)).strip()
    if text == "":
        raise ReconcileCsvError(f"第 {lineno} 行「{column}」为空")
    try:
        value = Decimal(text)
    except InvalidOperation:
        raise ReconcileCsvError(f"第 {lineno} 行「{column}」不是整数：{text!r}")
    if not value.is_finite() or value != value.to_integral_value():
        raise ReconcileCsvError(f"第 {lineno} 行「{column}」不是整数：{text!r}")
    as_int = int(value)
    if as_int < 0:
        raise ReconcileCsvError(f"第 {lineno} 行「{column}」不能为负：{text!r}")
    return as_int


def parse_reconcile_csv(text: str, cells: list[dict]) -> tuple[dict, dict]:
    """解析并做结构校验，返回 (cell_inputs, pair_inputs)。

    只校验结构、整数与非负；跨填报项是否同时成立交由核算求解判定，
    以便把冲突定位到具体格/配对行。
    """
    reader = csv.reader(io.StringIO(text))
    rows = [r for r in reader if any(str(cell).strip() for cell in r)]
    if not rows:
        raise ReconcileCsvError("CSV 为空")
    header = [str(h).strip().lstrip("﻿").lower() for h in rows[0]]
    col: dict[str, int] = {}
    for field, aliases in _ALIASES.items():
        for idx, name in enumerate(header):
            if name in {a.lower() for a in aliases}:
                col[field] = idx
                break
        if field not in col:
            raise ReconcileCsvError(
                f"缺少必需列：{field}（标准表头：{','.join(HEADER)}）"
            )

    known = {(c["district"], c["age_group"]) for c in cells}
    cell_inputs: dict[tuple[str, str], dict] = {}
    pair_inputs: dict[tuple[int, int], dict] = {}

    for lineno, row in enumerate(rows[1:], start=2):
        def get(field: str) -> str:
            idx = col[field]
            if idx >= len(row):
                raise ReconcileCsvError(f"第 {lineno} 行列数不足")
            return str(row[idx]).strip()

        district, age = get("district"), get("age_group")
        raw_round = get("round")
        if not raw_round:
            raise ReconcileCsvError(f"第 {lineno} 行「轮次」为空")
        kind, round_value = _normalize_round(raw_round)
        tested_raw, detected_raw = get("tested"), get("detected")
        both_tested_raw, both_detected_raw = get("both_tested"), get("both_detected")

        if kind == "cell":
            if not district or not age:
                raise ReconcileCsvError(f"第 {lineno} 行格行缺少分区或年龄组")
            key = (district, age)
            if key not in known:
                raise ReconcileCsvError(
                    f"第 {lineno} 行组合 {district} / {age} 不在固定调查中"
                )
            if both_tested_raw or both_detected_raw:
                raise ReconcileCsvError(
                    f"第 {lineno} 行是格行，两个「两轮均…」列应留空"
                )
            rnd = int(round_value)
            entry = cell_inputs.setdefault(key, {})
            if f"tested{rnd}" in entry:
                raise ReconcileCsvError(
                    f"第 {lineno} 行重复：{district} / {age} 第 {rnd} 轮"
                )
            entry[f"tested{rnd}"] = _int_value(tested_raw, lineno, "受检人数")
            entry[f"detected{rnd}"] = _int_value(detected_raw, lineno, "检出人数")
        else:
            if district or age:
                raise ReconcileCsvError(
                    f"第 {lineno} 行是配对行，分区与年龄组应留空"
                )
            if tested_raw or detected_raw:
                raise ReconcileCsvError(
                    f"第 {lineno} 行是配对行，受检人数与检出人数列应留空"
                )
            key = tuple(round_value)
            if key in pair_inputs:
                raise ReconcileCsvError(
                    f"第 {lineno} 行重复：轮次对 {PAIR_LABELS[key]}"
                )
            pair_inputs[key] = {
                "both_tested": _int_value(both_tested_raw, lineno, "两轮均受检人数"),
                "both_detected": _int_value(both_detected_raw, lineno, "两轮均检出人数"),
            }

    missing = []
    for district, age in sorted(known):
        entry = cell_inputs.get((district, age), {})
        for rnd in (2, 3):
            if f"tested{rnd}" not in entry:
                missing.append(f"{district} / {age} 第 {rnd} 轮")
    for pair in PAIR_ORDER:
        if pair not in pair_inputs:
            missing.append(f"轮次对 {PAIR_LABELS[pair]}")
    if missing:
        raise ReconcileCsvError("缺少填报行：" + "；".join(missing))
    return cell_inputs, pair_inputs
