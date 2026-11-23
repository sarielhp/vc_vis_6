#!/usr/bin/env python3
"""Distill minimal unsatisfiable witness subsets (MIN_CORES_UB6.json) for VC-dim(P) <= 6 (|S| = 7).

Uses binary/chunk deletion (ddmin) followed by fixed-point greedy 1-by-1 deletion on optional
masks (preserving structural anchor masks q=127 and w_D when active), streams CNF clauses via
pipe (0 .cnf files on disk), and cross-verifies every minimal witness set in BOTH Cadical195
and Glucose4.
"""
import argparse
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor

sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
UB6_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, UB6_DIR)

from pysat.solvers import Solver

from cegar_engine import (
    build_sgn_tlit,
    bulk_cegar_enclosure,
    find_violated_n1_cuts,
)
from solve_ub6_43_34_25 import (
    build_masks,
    canonical_orbits_25,
    canonical_orbits_34,
    canonical_orbits_43,
)
from solve_ub6_52 import (
    build_masks_52,
    enumerate_h0_orbits,
    enumerate_h1_branches,
)
from solve_ub6_61 import build_masks_61

BIN_H0 = os.path.join(UB6_DIR, "gen_chiro_h0")
BIN_H1 = os.path.join(UB6_DIR, "gen_chiro_h1")
OUT_JSON = os.path.join(HERE, "MIN_CORES_UB6.json")
OUT_MD = os.path.join(HERE, "SUMMARY.md")


def stream_clauses(bin_path, args, solver_name):
    proc = subprocess.Popen(
        [bin_path] + args,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=4 * 1024 * 1024,
    )
    nv, ncl = 0, 0
    s = Solver(name=solver_name)
    batch = []
    try:
        for line in proc.stdout:
            c = line[0]
            if c == "c":
                continue
            if c == "p":
                parts = line.split()
                nv, ncl = int(parts[2]), int(parts[3])
                continue
            batch.append(list(map(int, line.split()[:-1])))
            if len(batch) >= 100000:
                s.append_formula(batch)
                batch.clear()
        if batch:
            s.append_formula(batch)
        proc.wait()
        err = proc.stderr.read().strip()
        if proc.returncode != 0:
            raise RuntimeError(f"{bin_path} failed ({proc.returncode}): {err}")
    except Exception:
        proc.kill()
        proc.wait()
        s.delete()
        raise
    finally:
        if proc.stdout:
            proc.stdout.close()
        if proc.stderr:
            proc.stderr.close()
    return s, nv, ncl


def test_masks(
    bin_path,
    n_d,
    h_sz,
    lr,
    es,
    arg6,
    masks,
    solver_name="cadical195",
    max_iters=150,
    cand_timeout=None,
    conf_budget=None,
):
    t0 = time.time()
    mw = 2 if len(masks) <= 110 else 1
    args = [
        "7",
        str(n_d),
        str(h_sz),
        str(lr),
        es,
        str(arg6),
        "1",
        "0",
        "0",
        "1",
        "1",
        str(mw),
        "-",
    ] + [str(m) for m in masks]

    s, nv, ncl = stream_clauses(bin_path, args, solver_name=solver_name)
    timed_out = False
    with s:
        tot_cuts = 0
        for it in range(1, max_iters + 1):
            if cand_timeout is not None and (time.time() - t0) >= cand_timeout:
                timed_out = True
                return False, time.time() - t0, nv, ncl, it - 1, tot_cuts, timed_out
            if conf_budget is not None:
                s.conf_budget(conf_budget)
                r = s.solve_limited()
                if r is None:
                    timed_out = True
                    return False, time.time() - t0, nv, ncl, it - 1, tot_cuts, timed_out
            else:
                r = s.solve()
            if not r:
                return True, time.time() - t0, nv, ncl, it - 1, tot_cuts, False
            if cand_timeout is not None and (time.time() - t0) >= cand_timeout:
                timed_out = True
                return False, time.time() - t0, nv, ncl, it, tot_cuts, timed_out
            sgn, tlit = build_sgn_tlit(7 + len(masks), set(s.get_model()))
            _, cuts = bulk_cegar_enclosure(7, masks, sgn, tlit, max_rounds=6)
            n1_cuts = find_violated_n1_cuts(7, masks, sgn, tlit, max_cuts=1500)
            all_new = cuts + n1_cuts
            if not all_new:
                return False, time.time() - t0, nv, ncl, it, tot_cuts, False
            s.append_formula(all_new)
            tot_cuts += len(all_new)
    return False, time.time() - t0, nv, ncl, max_iters, tot_cuts, False


def build_all_tasks():
    tasks = []
    # (6, 1): 1 orbit, gap=1 and gap=0
    for arg6 in (1, 0):
        masks = build_masks_61(1)
        tasks.append({
            "task_id": f"61_0_gap{arg6}",
            "chunk": "61",
            "idx": 0,
            "n_d": 6,
            "h_sz": 0,
            "lr": -1,
            "es": "0",
            "bin_path": BIN_H0,
            "arg6": arg6,
            "tier": 1,
            "initial_masks": masks,
            "orbit_budget": 120.0,
            "cand_timeout": 35.0,
            "label": f"(6,1) #00 |H|=0 e=0 gap={arg6}",
        })

    # (5, 2): 11 orbits
    for i, (es, sz) in enumerate(enumerate_h0_orbits()):
        masks = build_masks_52(es, 0, 1)
        tasks.append({
            "task_id": f"52_h0_{i}",
            "chunk": "52",
            "idx": i,
            "n_d": 5,
            "h_sz": 0,
            "lr": -1,
            "es": es,
            "bin_path": BIN_H0,
            "arg6": 1,
            "tier": 1,
            "initial_masks": masks,
            "orbit_budget": 120.0,
            "cand_timeout": 35.0,
            "label": f"(5,2) #{i:02d} |H|=0 e={es} (sz={sz})",
        })
    for j, (eh, ea) in enumerate(enumerate_h1_branches()):
        es = f"{eh}{ea}"
        idx = 3 + j
        masks = build_masks_52(es, 1, 1)
        tasks.append({
            "task_id": f"52_h1_{j}",
            "chunk": "52",
            "idx": idx,
            "n_d": 5,
            "h_sz": 1,
            "lr": 4,
            "es": es,
            "bin_path": BIN_H1,
            "arg6": 0,
            "tier": 1,
            "initial_masks": masks,
            "orbit_budget": 90.0,
            "cand_timeout": 25.0,
            "label": f"(5,2) #{idx:02d} |H|=1 lr=40 e={es}",
        })

    # (2, 5): 4 orbits
    for i, (n_d, h_sz, lr, es) in enumerate(canonical_orbits_25()):
        masks = build_masks(n_d, es, 1)
        budget = 240.0 if i == 0 else 120.0
        ct = 40.0 if i == 0 else 30.0
        tasks.append({
            "task_id": f"25_{i}",
            "chunk": "25",
            "idx": i,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "bin_path": BIN_H1,
            "arg6": 0,
            "tier": 1,
            "initial_masks": masks,
            "orbit_budget": budget,
            "cand_timeout": ct,
            "label": f"(2,5) #{i:02d} |H|={h_sz} lr=01 e={es}",
        })

    # (4, 3): 29 orbits
    for i, (n_d, h_sz, lr, es) in enumerate(canonical_orbits_43()):
        lr_s = "none" if lr < 0 else f"{lr}{(lr + 1) % n_d}"
        masks = build_masks(n_d, es, 1)
        budget = 180.0 if i == 0 else (90.0 if i in (1, 2, 3, 13) else 55.0)
        ct = 35.0 if i in (0, 1, 2) else 25.0
        tasks.append({
            "task_id": f"43_{i}",
            "chunk": "43",
            "idx": i,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "bin_path": BIN_H1,
            "arg6": 0,
            "tier": 1,
            "initial_masks": masks,
            "orbit_budget": budget,
            "cand_timeout": ct,
            "label": f"(4,3) #{i:02d} |H|={h_sz} lr={lr_s} e={es}",
        })

    # (3, 4): 23 orbits (#02 uses tier=2)
    for i, (n_d, h_sz, lr, es) in enumerate(canonical_orbits_34()):
        lr_s = "none" if lr < 0 else f"{lr}{(lr + 1) % n_d}"
        tier = 2 if (i == 2 and es == "0011") else 1
        masks = build_masks(n_d, es, tier)
        budget = 220.0 if i in (0, 2) else (90.0 if i in (1, 3, 4) else 55.0)
        ct = 40.0 if i in (0, 2) else 25.0
        tasks.append({
            "task_id": f"34_{i}",
            "chunk": "34",
            "idx": i,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "bin_path": BIN_H1,
            "arg6": 0,
            "tier": tier,
            "initial_masks": masks,
            "orbit_budget": budget,
            "cand_timeout": ct,
            "label": f"(3,4) #{i:02d} |H|={h_sz} lr={lr_s} e={es}",
        })

    return tasks


def shrink_orbit(task_and_deadline):
    task, global_deadline = task_and_deadline
    t_start = time.time()
    n_d = task["n_d"]
    h_sz = task["h_sz"]
    lr = task["lr"]
    es = task["es"]
    arg6 = task["arg6"]
    bin_path = task["bin_path"]
    initial_masks = sorted(set(task["initial_masks"]))
    orbit_budget = task["orbit_budget"]
    cand_timeout = task["cand_timeout"]
    hard_end = min(t_start + orbit_budget, global_deadline)

    # Structural anchors required by gen_chiro_* flags
    anchors = set()
    if 127 in initial_masks:
        anchors.add(127)
    w_d = (1 << n_d) - 1
    if n_d >= 3 and "x" not in es and w_d in initial_masks:
        anchors.add(w_d)

    cur_opt = sorted(
        [m for m in initial_masks if m not in anchors],
        key=lambda m: (bin(m).count("1"), m),
    )

    cache = {}
    solver_calls = 0

    def eval_subset(opt_list, use_timeout=True):
        nonlocal solver_calls
        ms = sorted(anchors | set(opt_list))
        key = frozenset(ms)
        if key in cache:
            return cache[key]
        solver_calls += 1
        ct = cand_timeout if use_timeout else None
        cb = 3_000_000 if use_timeout else None
        if use_timeout:
            rem = hard_end - time.time()
            if rem <= 1.0:
                return False, 0.0, 0, 0, 0, 0, True
            ct = min(ct, rem)
        res = test_masks(
            bin_path, n_d, h_sz, lr, es, arg6, ms,
            solver_name="cadical195", max_iters=150,
            cand_timeout=ct, conf_budget=cb,
        )
        if res[0] or not res[6]:
            cache[key] = res
        return res

    # 1. Verify initial mask set cleanly in Cadical195 (skip upfront for 4 known-heavy runs;
    #    final_masks is always verified cleanly in BOTH Cadical195 and Glucose4 at step 4).
    heavy_skip_init = task["task_id"] in {"25_0", "43_0", "34_0", "34_2"}
    if not heavy_skip_init:
        init_res = eval_subset(cur_opt, use_timeout=False)
        if not init_res[0]:
            raise RuntimeError(f"{task['task_id']}: initial mask set m={len(initial_masks)} was NOT UNSAT!")
        best_info = init_res
        best_unlimited = True
    else:
        best_info = None
        best_unlimited = False

    shrink_budget = 60.0 if heavy_skip_init else orbit_budget
    hard_end = min(time.time() + shrink_budget, global_deadline)

    # 2. Binary / chunk deletion (ddmin)
    n = 2
    while len(cur_opt) >= 2 and time.time() < hard_end:
        chunk_sz = max(1, (len(cur_opt) + n - 1) // n)
        chunks = [cur_opt[i:i + chunk_sz] for i in range(0, len(cur_opt), chunk_sz)]
        reduced = False
        if len(chunks) > 1:
            for ch in chunks:
                if time.time() >= hard_end:
                    break
                if len(ch) < len(cur_opt):
                    res = eval_subset(ch, use_timeout=True)
                    if res[0]:
                        cur_opt = ch
                        best_info = res
                        best_unlimited = False
                        n = 2
                        reduced = True
                        break
            if reduced:
                continue
            for idx_c in range(len(chunks)):
                if time.time() >= hard_end:
                    break
                comp = [x for j, c in enumerate(chunks) if j != idx_c for x in c]
                res = eval_subset(comp, use_timeout=True)
                if res[0]:
                    cur_opt = comp
                    best_info = res
                    best_unlimited = False
                    n = max(len(chunks) - 1, 2)
                    reduced = True
                    break
        if reduced:
            continue
        if n >= len(cur_opt):
            break
        n = min(len(cur_opt), n * 2)

    # 3. Greedy 1-by-1 fixed-point deletion on optional masks
    is_1_minimal = False
    changed = True
    while changed and time.time() < hard_end:
        changed = False
        i = 0
        hit_budget = False
        while i < len(cur_opt):
            if time.time() >= hard_end:
                hit_budget = True
                break
            cand = cur_opt[:i] + cur_opt[i + 1:]
            res = eval_subset(cand, use_timeout=True)
            if res[0]:
                cur_opt = cand
                best_info = res
                best_unlimited = False
                changed = True
            else:
                if res[6]:
                    hit_budget = True
                i += 1
        if not changed and not hit_budget:
            is_1_minimal = True

    final_masks = sorted(anchors | set(cur_opt))

    # 4. Clean unlimited cross-verification in BOTH Cadical195 AND Glucose4
    if not best_unlimited:
        c_ok, c_dt, c_nv, c_ncl, c_it, c_cuts, _ = test_masks(
            bin_path, n_d, h_sz, lr, es, arg6, final_masks,
            solver_name="cadical195", max_iters=150,
            cand_timeout=None, conf_budget=None,
        )
        if not c_ok:
            raise RuntimeError(f"{task['task_id']}: final Cadical195 verification FAILED on m={len(final_masks)}!")
    else:
        c_ok, c_dt, c_nv, c_ncl, c_it, c_cuts, _ = best_info

    g_ok, g_dt, _, _, g_it, g_cuts, _ = test_masks(
        bin_path, n_d, h_sz, lr, es, arg6, final_masks,
        solver_name="glucose4", max_iters=150,
        cand_timeout=None, conf_budget=None,
    )
    if not g_ok:
        raise RuntimeError(f"{task['task_id']}: final Glucose4 cross-verification FAILED on m={len(final_masks)}!")

    shrink_sec = round(time.time() - t_start, 2)
    print(
        f"  [{task['label']:36s}] {len(initial_masks):2d} -> {len(final_masks):2d} "
        f"(1-min={str(is_1_minimal):5s}, cad={c_dt:.2f}s, glu={g_dt:.2f}s, "
        f"cl={c_ncl:,}, calls={solver_calls}, tot={shrink_sec:.1f}s)",
        flush=True,
    )

    return {
        "task_id": task["task_id"],
        "chunk": task["chunk"],
        "idx": task["idx"],
        "n_d": n_d,
        "h_sz": h_sz,
        "lr": lr,
        "es": es,
        "arg6": arg6,
        "bin": os.path.basename(bin_path),
        "tier": task["tier"],
        "original_m": len(initial_masks),
        "min_m": len(final_masks),
        "anchors": sorted(anchors),
        "masks": final_masks,
        "cadical_verified": c_ok,
        "glucose4_verified": g_ok,
        "cadical_time_s": round(c_dt, 2),
        "glucose4_time_s": round(g_dt, 2),
        "vars": c_nv,
        "clauses": c_ncl,
        "cadical_iters": c_it,
        "cadical_cuts": c_cuts,
        "glucose4_iters": g_it,
        "glucose4_cuts": g_cuts,
        "is_1_minimal": is_1_minimal,
        "solver_calls": solver_calls,
        "shrink_sec": shrink_sec,
    }


def write_outputs(results_by_id, t_start, total_tasks):
    chunk_order = {"61": 0, "52": 1, "25": 2, "43": 3, "34": 4}
    results = sorted(
        results_by_id.values(),
        key=lambda r: (chunk_order[r["chunk"]], r["idx"], -r["arg6"]),
    )
    wall_sec = round(time.time() - t_start, 2)

    orbits_done = 0
    r61 = [r for r in results if r["chunk"] == "61"]
    if len(r61) == 2 and all(r["cadical_verified"] and r["glucose4_verified"] for r in r61):
        orbits_done += 1
    orbits_done += sum(
        1 for r in results if r["chunk"] != "61" and r["cadical_verified"] and r["glucose4_verified"]
    )

    payload = {
        "wall_sec": wall_sec,
        "runs_completed": len(results),
        "runs_total": total_tasks,
        "orbits_verified": orbits_done,
        "orbits_total": 68,
        "solvers": ["cadical195", "glucose4"],
        "results": results,
    }
    tmp_json = OUT_JSON + ".tmp"
    with open(tmp_json, "w") as f:
        json.dump(payload, f, indent=2)
    os.replace(tmp_json, OUT_JSON)

    lines = [
        "# `VC-dim(P) <= 6` (`|S| = 7`) Minimal Unsatisfiable Witness Subsets (`MIN_CORES_UB6`)",
        "",
        f"- **Runs Completed & Dual-Verified (`Cadical195` + `Glucose4`):** **`{len(results)} / {total_tasks}`** (`{orbits_done} / 68` canonical orbits)",
        f"- **Wall Time Elapsed:** `{wall_sec:.2f}s` (`max_workers=4`, `0` `.cnf` files on disk)",
        f"- **Anchors Preserved:** `q = 127` (always) and `w_D = 2^n_d - 1` (when `n_d >= 3` and `edge_str` active)",
        "",
        "## 1. Chunk Summary",
        "",
        "| Chunk `(n_d, |M|)` | Completed | Orig `m` | Min `m` | 1-Minimal | Total Orig -> Min | Max `Cadical` / `Glucose4` |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]
    chunk_meta = [
        ("61", "`(6, 1)` (`gap=1` & `gap=0`)", 2),
        ("52", "`(5, 2)` (`3` `|H|=0` + `8` `|H|=1`)", 11),
        ("25", "`(2, 5)` (`|H|=1..4`, `edge=xxxxx`)", 4),
        ("43", "`(4, 3)` (`29` orbits)", 29),
        ("34", "`(3, 4)` (`23` orbits)", 23),
    ]
    for c, label, tot_c in chunk_meta:
        sub = [r for r in results if r["chunk"] == c]
        if not sub:
            lines.append(f"| {label} | `0 / {tot_c}` | — | — | — | — | — |")
            continue
        om_lo, om_hi = min(r["original_m"] for r in sub), max(r["original_m"] for r in sub)
        mm_lo, mm_hi = min(r["min_m"] for r in sub), max(r["min_m"] for r in sub)
        om_s = f"`{om_lo}`" if om_lo == om_hi else f"`{om_lo}..{om_hi}`"
        mm_s = f"`{mm_lo}`" if mm_lo == mm_hi else f"`{mm_lo}..{mm_hi}`"
        one_min = sum(1 for r in sub if r["is_1_minimal"])
        tot_o = sum(r["original_m"] for r in sub)
        tot_m = sum(r["min_m"] for r in sub)
        mc = max(r["cadical_time_s"] for r in sub)
        mg = max(r["glucose4_time_s"] for r in sub)
        lines.append(
            f"| {label} | **`{len(sub)} / {tot_c}`** | {om_s} | **{mm_s}** | `{one_min}/{len(sub)}` | `{tot_o} -> {tot_m}` | `{mc:.2f}s` / `{mg:.2f}s` |"
        )

    lines += [
        "",
        "## 2. Per-Orbit Minimal Cores",
        "",
        "| Task ID | Chunk | `#` | `|H|` | `lr` | `edge` | `gap` | Orig `m` | Min `m` | 1-Min | Clauses | `Cadical195` | `Glucose4` |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]
    for r in results:
        lines.append(
            f"| `{r['task_id']}` | `({r['n_d']},{7-r['n_d']})` | `{r['idx']}` | `{r['h_sz']}` | `{r['lr']}` | `{r['es']}` | `{r['arg6']}` | `{r['original_m']}` | **`{r['min_m']}`** | `{ 'Y' if r['is_1_minimal'] else 'N' }` | `{r['clauses']:,}` | `{r['cadical_time_s']:.2f}s` | `{r['glucose4_time_s']:.2f}s` |"
        )

    tmp_md = OUT_MD + ".tmp"
    with open(tmp_md, "w") as f:
        f.write("\n".join(lines) + "\n")
    os.replace(tmp_md, OUT_MD)


def order_chunk_tasks(tasks, chunk):
    sub = [t for t in tasks if t["chunk"] == chunk]
    if chunk == "43":
        heavy = {0, 1, 2, 3, 13}
        fast = [t for t in sub if t["idx"] not in heavy]
        slow = sorted([t for t in sub if t["idx"] in heavy], key=lambda t: [13, 3, 1, 2, 0].index(t["idx"]))
        return fast + slow
    if chunk == "34":
        heavy = {0, 1, 2, 3, 4}
        fast = [t for t in sub if t["idx"] not in heavy]
        slow = sorted([t for t in sub if t["idx"] in heavy], key=lambda t: [3, 4, 1, 2, 0].index(t["idx"]))
        return fast + slow
    return sub


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--total-budget", type=float, default=860.0)
    parser.add_argument("--chunks", type=str, default="61,52,25,43,34")
    parser.add_argument("--no-resume", action="store_true")
    args = parser.parse_args()

    t_start = time.time()
    global_deadline = t_start + args.total_budget
    all_tasks = build_all_tasks()

    results_by_id = {}
    if not args.no_resume and os.path.exists(OUT_JSON):
        with open(OUT_JSON) as f:
            prev = json.load(f)
        for r in prev.get("results", []):
            if r.get("cadical_verified") and r.get("glucose4_verified"):
                results_by_id[r["task_id"]] = r
        print(f"Resumed {len(results_by_id)} completed runs from {OUT_JSON}", flush=True)

    chunks = [c.strip() for c in args.chunks.split(",") if c.strip()]
    for chunk in chunks:
        if time.time() >= global_deadline:
            print(f"Global deadline reached before chunk ({chunk}); stopping cleanly.", flush=True)
            break
        ordered = [t for t in order_chunk_tasks(all_tasks, chunk) if t["task_id"] not in results_by_id]
        if not ordered:
            print(f"Chunk ({chunk}): already complete.", flush=True)
            continue

        # Process large chunks in sub-batches of 4 so incremental saves happen frequently
        batch_size = 4 if chunk in ("43", "34") else len(ordered)
        for b_idx in range(0, len(ordered), batch_size):
            if time.time() >= global_deadline:
                print(f"Global deadline reached during chunk ({chunk}); stopping cleanly.", flush=True)
                break
            batch = ordered[b_idx:b_idx + batch_size]
            print(f"=== Chunk ({chunk}) batch {b_idx}:{b_idx+len(batch)} ({len(batch)} runs, rem={global_deadline-time.time():.0f}s) ===", flush=True)
            with ProcessPoolExecutor(max_workers=min(args.workers, len(batch))) as ex:
                for res in ex.map(shrink_orbit, [(t, global_deadline) for t in batch]):
                    results_by_id[res["task_id"]] = res
            write_outputs(results_by_id, t_start, len(all_tasks))
            print(f"Saved incremental checkpoint: {len(results_by_id)}/{len(all_tasks)} runs -> {OUT_JSON}", flush=True)

    write_outputs(results_by_id, t_start, len(all_tasks))
    print(f"DONE: {len(results_by_id)}/{len(all_tasks)} runs verified in both Cadical195 and Glucose4 ({time.time()-t_start:.1f}s).", flush=True)


if __name__ == "__main__":
    main()
