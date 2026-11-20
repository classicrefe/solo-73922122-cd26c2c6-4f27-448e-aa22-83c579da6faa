"""关键功能自测：以 TestClient 驱动应用，使用独立临时数据库。

运行：python tests/selftest.py
覆盖：导入校验、导入后不可更换、预览、安全/不安全发布、
两窗口各自安全但合并不安全的重核拒绝、公开页不泄露格内检出数、
公开记录落盘持久化、多轮筛查累计检出核算（上下界、端点组合、
冲突定位、核算不影响固定调查与公开记录）、核算结果与穷举一致。
"""

import os
import sqlite3
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

_TMP = tempfile.mkdtemp(prefix="cdc_guard_test_")
os.environ["DB_PATH"] = str(Path(_TMP) / "test.db")  # 须在导入 app 前设置

from fastapi.testclient import TestClient  # noqa: E402

from app.main import app  # noqa: E402

SAMPLE = (
    "分区,年龄组,人数,检出数\n"
    "城东,青年,10,2\n"
    "城东,老年,10,8\n"
    "城西,青年,10,8\n"
    "城西,老年,10,8\n"
)

results = []


def check(name, cond, extra=""):
    results.append(bool(cond))
    print(f"[{'PASS' if cond else 'FAIL'}] {name}")
    if not cond and extra:
        print("       " + extra.replace("\n", "\n       ")[:800])


def run():
    with TestClient(app) as client:
        def import_csv(text):
            return client.post(
                "/api/import",
                files={"file": ("data.csv", text.encode("utf-8"), "text/csv")},
            )

        # ---- 1. 导入校验 ----
        r = import_csv("分区,年龄组,人数,检出数\nA,青,4,1\n")
        check("人数<5 被拒绝", r.status_code == 400, r.text)
        r = import_csv("分区,年龄组,人数,检出数\nA,青,10,11\n")
        check("检出数>人数 被拒绝", r.status_code == 400, r.text)
        r = import_csv("分区,年龄组,人数,检出数\nA,青,10,-1\n")
        check("检出数<0 被拒绝", r.status_code == 400, r.text)
        r = import_csv("分区,年龄组,人数,检出数\nA,青,10,1.5\n")
        check("检出数非整数 被拒绝", r.status_code == 400, r.text)
        r = import_csv("分区,年龄组,人数,检出数\nA,青,10,1\nA,青,10,2\n")
        check("组合重复 被拒绝", r.status_code == 400, r.text)
        many = "分区,年龄组,人数,检出数\n" + "\n".join(
            f"区{i},青,10,1" for i in range(17)
        )
        r = import_csv(many)
        check("超过16格 被拒绝", r.status_code == 400, r.text)
        r = import_csv("分区,年龄组,人数\nA,青,10\n")
        check("缺少检出数列 被拒绝", r.status_code == 400, r.text)

        # ---- 2. 正常导入 + 不可更换 ----
        r = import_csv(SAMPLE)
        check("示例导入成功", r.status_code == 201 and r.json()["imported"] == 4, r.text)
        r = import_csv(SAMPLE)
        check("重复导入被拒绝（导入后不可更换）", r.status_code == 409, r.text)

        # ---- 3. 预览 ----
        r = client.post("/api/preview", json={"districts": ["城东"], "age_groups": ["青年", "老年"]})
        j = r.json()
        check("预览「城东」总数=10 且安全",
              r.status_code == 200 and j["total"] == 10 and j["safe"], r.text)

        # ---- 4. 两窗口各自安全、合并不安全 ----
        r = client.post("/api/preview", json={"districts": ["城东", "城西"], "age_groups": ["老年"]})
        j = r.json()
        check("窗口「老年」单独预览安全（总数=16）",
              r.status_code == 200 and j["total"] == 16 and j["safe"], r.text)

        r = client.post("/api/publish", json={"districts": ["城东"], "age_groups": ["青年", "老年"]})
        check("发布「城东」成功（总数=10）",
              r.status_code == 201 and r.json()["total"] == 10, r.text)

        r = client.post("/api/preview", json={"districts": ["城东", "城西"], "age_groups": ["老年"]})
        j = r.json()
        aff = j.get("affected", [])
        check("合并后预览「老年」不安全", r.status_code == 200 and not j["safe"], r.text)
        check("受影响格为 城东/青年，可行范围[0,4]，不可取≥5",
              len(aff) == 1
              and aff[0]["district"] == "城东" and aff[0]["age_group"] == "青年"
              and aff[0]["min"] == 0 and aff[0]["max"] == 4
              and aff[0]["zero_feasible"] and not aff[0]["ge5_feasible"], r.text)

        r = client.post("/api/publish", json={"districts": ["城东", "城西"], "age_groups": ["老年"]})
        check("确认发布「老年」被按最新公开记录重核拒绝(409)", r.status_code == 409, r.text)
        d = r.json().get("detail", {})
        check("409 响应含受影响格与可行范围",
              isinstance(d, dict) and d.get("affected")
              and d["affected"][0]["max"] == 4, r.text)

        # ---- 5. 与已公开记录合并仍安全的发布可继续 ----
        r = client.post("/api/publish", json={"districts": ["城东", "城西"], "age_groups": ["青年"]})
        check("发布「青年」（与「城东」合并仍安全）成功",
              r.status_code == 201 and r.json()["total"] == 10, r.text)
        r = client.post("/api/publish", json={"districts": ["城东", "城西"], "age_groups": ["老年"]})
        check("「老年」仍被拒绝", r.status_code == 409, r.text)

        # ---- 6. 公开页不泄露格内检出数 ----
        r = client.get("/api/public")
        j = r.json()
        check("公开 API 不含 detected 字段",
              r.status_code == 200 and all("detected" not in c for c in j["cells"]), r.text)
        check("公开 API 含人数与 2 条获准汇总",
              len(j["cells"]) == 4 and all("population" in c for c in j["cells"])
              and len(j["publications"]) == 2, r.text)
        check("公开汇总不含格值字段",
              all(set(p) == {"id", "districts", "age_groups", "total", "created_at"}
                  for p in j["publications"]), r.text)
        r = client.get("/public")
        check("公开页可访问", r.status_code == 200 and "公开" in r.text)
        r = client.get("/")
        check("内部审查台可访问", r.status_code == 200 and "审查台" in r.text)

        # ---- 7. 持久化（直接读库文件，等价于重启后再读） ----
        conn = sqlite3.connect(os.environ["DB_PATH"])
        n_pub = conn.execute("SELECT COUNT(*) FROM publications").fetchone()[0]
        n_cell = conn.execute("SELECT COUNT(*) FROM cells").fetchone()[0]
        conn.close()
        check("公开记录与格值已落盘（重启保留）", n_pub == 2 and n_cell == 4)

        # ---- 8. 其他边界 ----
        r = client.post("/api/preview", json={"districts": ["不存在"], "age_groups": ["青年"]})
        check("未知分区被拒绝", r.status_code == 400, r.text)
        r = client.post("/api/publish", json={"districts": [], "age_groups": ["青年"]})
        check("空选择被拒绝", r.status_code == 400, r.text)
        r = client.post("/api/preview", json={"districts": ["城东"], "age_groups": []})
        check("空年龄组被拒绝", r.status_code == 400, r.text)

        # ---- 9. 保存失败不留半次发布 ----
        import app.database as dbmod
        import app.main as mainmod

        before = len(client.get("/api/public").json()["publications"])

        # 9a. 接口层：插入时发生异常 → 500 且无记录产生
        orig_insert = mainmod.insert_publication
        def _boom(*a, **k):
            raise RuntimeError("模拟保存失败")
        mainmod.insert_publication = _boom
        try:
            r = client.post(
                "/api/publish",
                json={"districts": ["城东", "城西"], "age_groups": ["青年"]},
            )
            check("保存时异常返回 500", r.status_code == 500, r.text)
        finally:
            mainmod.insert_publication = orig_insert
        after = len(client.get("/api/public").json()["publications"])
        check("保存失败未留下半次发布", after == before, f"before={before} after={after}")

        # 9b. 存储层：库不可打开时写入抛错，且库内容不变
        orig_path = dbmod.DB_PATH
        dbmod.DB_PATH = _TMP  # 指向目录：SQLite 无法打开
        try:
            dbmod.insert_publication(["x"], ["y"], 1)
            check("库不可打开时写入抛错", False, "未抛错")
        except Exception:
            check("库不可打开时写入抛错", True)
        finally:
            dbmod.DB_PATH = orig_path
        after = len(client.get("/api/public").json()["publications"])
        check("库写失败后记录数不变", after == before, f"before={before} after={after}")

        # ---- 10. 求解器并发安全（z3 每评估独立 Context） ----
        from concurrent.futures import ThreadPoolExecutor

        from app.solver import evaluate

        cells = dbmod.get_cells()
        pubs = dbmod.get_publications()
        cand = {"districts": ["城东", "城西"], "age_groups": ["老年"], "total": 16}
        with ThreadPoolExecutor(max_workers=8) as ex:
            outs = list(ex.map(lambda _: evaluate(cells, pubs, cand), range(40)))
        check(
            "40 路并发求解结果一致且正确",
            all(
                (not o["safe"])
                and len(o["affected"]) == 1
                and o["affected"][0]["max"] == 4
                for o in outs
            ),
            str(outs[:2]),
        )

        # ---- 11. 多轮筛查累计检出核算（内部页） ----
        run_reconcile_checks(client)


RECONCILE_OK = """分区,年龄组,轮次,受检人数,检出人数,两轮均受检人数,两轮均检出人数
城东,青年,2,4,0,,
城东,青年,3,6,3,,
城东,老年,2,6,5,,
城东,老年,3,9,8,,
城西,青年,2,8,5,,
城西,青年,3,7,5,,
城西,老年,2,6,6,,
城西,老年,3,5,4,,
,,1-2,,,24,15
,,1-3,,,27,15
,,2-3,,,17,10
"""


def run_reconcile_checks(client):
    sample = (Path(__file__).resolve().parent.parent / "sample_reconcile.csv").read_text(
        encoding="utf-8"
    )
    before_state = client.get("/api/admin/state").json()
    before_public = client.get("/api/public").json()

    def upload(text, name="rec.csv"):
        return client.post(
            "/api/reconcile",
            files={"file": (name, text.encode("utf-8"), "text/csv")},
        )

    # 11a. 模板
    r = client.get("/api/reconcile/template")
    lines = [ln for ln in r.text.lstrip("﻿").splitlines() if ln.strip()]
    check("核算模板可下载且含 4 格×2 轮 + 3 配对行",
          r.status_code == 200 and len(lines) == 1 + 8 + 3, r.text[:300])
    check("示例核算 CSV 与页面演示数据一致", sample == RECONCILE_OK,
          "sample_reconcile.csv 与测试内置样例不一致")

    # 11b. 可行核算：上下界与端点组合
    r = upload(sample, "sample_reconcile.csv")
    ok = r.status_code == 200
    j = r.json() if ok else {}
    res = j.get("result", {})
    check("示例核算请求成功且计数可同时成立",
          ok and res.get("feasible") is True, r.text[:500])
    check("全表至少检出一次上下界为 [31, 32]",
          res.get("total", {}).get("min") == 31 and res["total"]["max"] == 32,
          str({k: res["total"][k] for k in ("min", "max")} if res.get("total") else None))
    bounds = {(c["district"], c["age_group"]): (c["min"], c["max"]) for c in res.get("cells", [])}
    check("各格上下界符合穷举结果",
          bounds == {("城东", "青年"): (3, 5), ("城东", "老年"): (8, 10),
                     ("城西", "青年"): (8, 10), ("城西", "老年"): (8, 10)},
          str(bounds))

    def ever(rows):
        return sum(x["count"] for x in rows if "D" in x["codes"])

    check("每格下界/上界端点状态组合人数等于该端点",
          all(ever(c["min_states"]) == c["min"] and ever(c["max_states"]) == c["max"]
              for c in res.get("cells", [])))
    check("全表下界分配的人数等于全表下界",
          sum(ever(cell["states"]) for cell in res["total"]["min_assignment"]) == 31)
    check("全表上界分配的人数等于全表上界",
          sum(ever(cell["states"]) for cell in res["total"]["max_assignment"]) == 32)

    def assignment_ok(assignment):
        # 校验每份分配在各格内确实满足填报计数与三轮状态定义
        by_cell = {(c["district"], c["age_group"]): c for c in res["cells"]}
        for cell in assignment:
            key = (cell["district"], cell["age_group"])
            comp = {"U": 0, "T": 1, "D": 2}
            stats = {1: [0, 0], 2: [0, 0], 3: [0, 0]}
            for row in cell["states"]:
                for rnd, code in enumerate(row["codes"], start=1):
                    state = comp[code]
                    if state in (1, 2):
                        stats[rnd][0] += row["count"]
                    if state == 2:
                        stats[rnd][1] += row["count"]
            c = by_cell[key]
            if stats[2] != [c["tested2"], c["detected2"]]:
                return False
            if stats[3] != [c["tested3"], c["detected3"]]:
                return False
            if stats[1][1] != c["detected1"]:
                return False
            if sum(row["count"] for row in cell["states"]) != c["population"]:
                return False
        return True

    check("全表端点分配满足所有格级计数",
          assignment_ok(res["total"]["min_assignment"])
          and assignment_ok(res["total"]["max_assignment"]))

    # 11c. 冲突：单格检出>受检
    conflict = sample.replace("城东,青年,2,4,0,,", "城东,青年,2,4,9,,")
    r = upload(conflict)
    j = r.json()
    conflict_cells = [(c["district"], c["age_group"]) for c in j["result"]["conflict"]["cells"]]
    check("检出人数>受检人数 判为冲突且不输出全表结果",
          r.status_code == 200 and j["result"]["feasible"] is False
          and "total" not in j["result"], r.text[:400])
    check("冲突定位到具体格 城东/青年",
          ("城东", "青年") in conflict_cells, str(conflict_cells))
    check("冲突说明含可判定原因",
          any("超过第 2 轮受检人数" in x for x in j["result"]["conflict"]["reasons"]),
          str(j["result"]["conflict"]["reasons"]))

    # 11d. 冲突：配对行与各格合计不符
    pair_conflict = sample.replace(",,1-2,,,24,15", ",,1-2,,,23,15")
    r = upload(pair_conflict)
    j = r.json()
    pairs = [tuple(p["rounds"]) for p in j["result"]["conflict"]["pairs"]]
    check("第 1、2 轮均受检人数与第 2 轮受检合计不符 → 冲突定位到配对行",
          r.status_code == 200 and j["result"]["feasible"] is False
          and (1, 2) in pairs, str(pairs))

    # 11e. 结构错误
    r = upload("分区,年龄组,轮次,受检人数,检出人数,两轮均受检人数,两轮均检出人数\n")
    check("空核算 CSV 被拒绝(400)", r.status_code == 400, r.text)
    r = upload(sample.replace("城东,青年,2,4,0,,", "城东,青年,2,4,-1,,"))
    check("负数填报被拒绝(400)", r.status_code == 400, r.text)
    r = upload(sample.replace("城东,青年,2,4,0,,", "城东,青年,2,4.5,0,,"))
    check("非整数填报被拒绝(400)", r.status_code == 400, r.text)
    r = upload(sample.replace("城东,青年,2,4,0,,", "城东,未知,2,4,0,,"))
    check("不在固定调查中的格被拒绝(400)", r.status_code == 400, r.text)
    r = client.post("/api/reconcile", files={"file": ("x.csv", b"\xff\xfe", "text/csv")})
    check("非 UTF-8 文件被拒绝(400)", r.status_code == 400, r.text)

    # 11f. 核算不影响固定调查与公开记录
    after_state = client.get("/api/admin/state").json()
    after_public = client.get("/api/public").json()
    check("核算后固定调查不变",
          after_state["cells"] == before_state["cells"], "cells changed")
    check("核算后公开记录不变",
          after_public["publications"] == before_public["publications"], "publications changed")
    check("核算数据不出现在公开接口",
          "reconcile" not in str(after_public) and "reconciliations" not in str(after_public))
    r = client.get("/public")
    check("公开页不含核算入口/文字",
          r.status_code == 200 and "核算" not in r.text and "/reconcile" not in r.text)
    r = client.get("/reconcile")
    check("内部核算页可访问", r.status_code == 200 and "核算" in r.text)
    r = client.get("/api/reconcile/history")
    j = r.json()
    check("核算记录已落盘（3 次有效上传，含 1 次可行）",
          r.status_code == 200 and len(j["records"]) == 3, str(len(j.get("records", []))))
    check("核算记录区分可行/冲突",
          sum(1 for x in j["records"] if x["feasible"]) == 1,
          str([x["feasible"] for x in j["records"]]))

    # 11g. 与穷举结果逐项对照（小规模，可完全枚举）
    check_reconcile_matches_bruteforce()


def check_reconcile_matches_bruteforce():
    import itertools

    from app.reconcile import PATTERNS, reconcile

    def compositions(total, parts):
        if parts == 1:
            yield (total,)
            return
        for head in range(total + 1):
            for rest in compositions(total - head, parts - 1):
                yield (head,) + rest

    def cell_vectors(comp):
        return (
            sum(n for n, p in zip(comp, PATTERNS) if p[0] == 2),
            sum(n for n, p in zip(comp, PATTERNS) if p[1] >= 1),
            sum(n for n, p in zip(comp, PATTERNS) if p[1] == 2),
            sum(n for n, p in zip(comp, PATTERNS) if p[2] >= 1),
            sum(n for n, p in zip(comp, PATTERNS) if p[2] == 2),
        )

    def brute(cells, inputs, pairs):
        per_cell = [
            [comp for comp in compositions(c["population"], len(PATTERNS))
             if cell_vectors(comp) == (c["detected"], inputs[(c["district"], c["age_group"])]["tested2"],
                                       inputs[(c["district"], c["age_group"])]["detected2"],
                                       inputs[(c["district"], c["age_group"])]["tested3"],
                                       inputs[(c["district"], c["age_group"])]["detected3"])]
            for c in cells
        ]
        sols = []
        for combo in itertools.product(*per_cell):
            good = True
            for (r1, r2), inp in pairs.items():
                a, b = r1 - 1, r2 - 1
                bt = sum(sum(n for n, p in zip(comp, PATTERNS) if p[a] >= 1 and p[b] >= 1)
                         for comp in combo)
                bd = sum(sum(n for n, p in zip(comp, PATTERNS) if p[a] == 2 and p[b] == 2)
                         for comp in combo)
                if (bt, bd) != (inp["both_tested"], inp["both_detected"]):
                    good = False
                    break
            if good:
                sols.append(combo)
        ever = [sum(n for n, p in zip(comp, PATTERNS) if 2 in p) for comp in sols[0]]
        cell_bounds = []
        for i in range(len(cells)):
            vals = [sum(n for n, p in zip(sol[i], PATTERNS) if 2 in p) for sol in sols]
            cell_bounds.append((min(vals), max(vals)))
        totals = [sum(sum(n for n, p in zip(sol[i], PATTERNS) if 2 in p)
                      for i in range(len(cells))) for sol in sols]
        return cell_bounds, (min(totals), max(totals)), len(sols)

    # 由真实逐人状态构造的小规模算例（保证可行）
    cells = [
        {"district": "甲", "age_group": "青", "population": 4, "detected": 1},
        {"district": "乙", "age_group": "青", "population": 4, "detected": 2},
    ]
    inputs = {}
    pair = {(1, 2): [0, 0], (1, 3): [0, 0], (2, 3): [0, 0]}
    people = {
        ("甲", "青"): [(2, 0, 1), (1, 1, 2), (1, 2, 1), (1, 0, 0)],
        ("乙", "青"): [(2, 2, 2), (2, 1, 0), (1, 0, 2), (1, 1, 1)],
    }
    for key, pats in people.items():
        inputs[key] = {
            "tested2": sum(1 for p in pats if p[1] >= 1),
            "detected2": sum(1 for p in pats if p[1] == 2),
            "tested3": sum(1 for p in pats if p[2] >= 1),
            "detected3": sum(1 for p in pats if p[2] == 2),
        }
        for (a, b) in pair:
            pair[(a, b)][0] += sum(1 for p in pats if p[a - 1] >= 1 and p[b - 1] >= 1)
            pair[(a, b)][1] += sum(1 for p in pats if p[a - 1] == 2 and p[b - 1] == 2)
    pairs = {k: {"both_tested": v[0], "both_detected": v[1]} for k, v in pair.items()}

    expected_cells, expected_total, n_sols = brute(cells, inputs, pairs)
    got = reconcile(cells, inputs, pairs)
    got_cells = [(c["min"], c["max"]) for c in got["cells"]]
    check("小规模算例穷举可行",
          n_sols > 0, f"n_sols={n_sols}")
    check("核算各格上下界与穷举完全一致",
          got["feasible"] and got_cells == expected_cells,
          f"brute={expected_cells} z3={got_cells}")
    check("核算全表上下界与穷举完全一致",
          (got["total"]["min"], got["total"]["max"]) == expected_total,
          f"brute={expected_total} z3={(got['total']['min'], got['total']['max'])}")


run()
print(f"\n{sum(results)}/{len(results)} 通过")
sys.exit(0 if all(results) else 1)
