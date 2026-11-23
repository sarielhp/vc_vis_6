#!/usr/bin/env python3
"""Standalone gap-free (use_gap = 0) dual-solver reproducer for Theorem 1.1:
  1. Positive control: explicit 968-vertex hexagon P_0 (seed46_compiled.json) -> SAT, 0 violations
  2. Stage 1 (|B| = 7, A = empty): all 6 certified-hull sizes |H| in {0..5} -> 6/6 UNSAT
  3. Stage 2 (3 <= |B| <= 6, A != empty): all 68 canonical dihedral orbits -> 68/68 UNSAT

Streams CNF clauses directly from gen_chiro_h0 / gen_chiro_h1 stdout pipes into
PySAT (CaDiCaL 1.9.5 and Glucose 4) with zero .cnf files written to disk.
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from cegar_engine import (  # noqa: E402
    build_sgn_tlit,
    bulk_cegar_enclosure,
    find_violated_n1_cuts,
    o_pos,
    stream_clauses,
)
from solve_ub6_43_34_25 import (  # noqa: E402
    build_masks,
    canonical_orbits_25,
    canonical_orbits_34,
    canonical_orbits_43,
)
from solve_ub6_52 import (  # noqa: E402
    build_masks_52,
    enumerate_h0_orbits,
    enumerate_h1_branches,
)
from solve_ub6_61 import build_masks_61  # noqa: E402

BIN_H0 = str(HERE / "gen_chiro_h0")
BIN_H1 = str(HERE / "gen_chiro_h1")
SEED46_JSON = HERE.parents[1] / "seed46_compiled.json"


def ensure_binaries() -> None:
    for src, out in [("gen_chiro_h0.cpp", BIN_H0), ("gen_chiro_h1.cpp", BIN_H1)]:
        if not os.path.exists(out):
            subprocess.run(
                ["g++", "-O3", "-std=c++17", str(HERE / src), "-o", out],
                check=True,
            )


def build_stage1_masks(h_sz: int) -> list[int]:
    n_d = 7 - h_sz
    full = (1 << 7) - 1
    p_ge5 = {m for m in range(128) if m.bit_count() >= 5}
    d_mask = (1 << n_d) - 1
    d_minus = {d_mask ^ (1 << k) for k in range(n_d)}
    w0 = p_ge5 | {d_mask} | d_minus
    if h_sz == 0:
        for i in range(7):
            miss = (1 << i) | (1 << ((i + 2) % 7)) | (1 << ((i + 4) % 7))
            w0.add(full ^ miss)
    return sorted(w0)


def build_all_74_tasks() -> list[dict]:
    tasks = []
    # Stage 1: 6 unbranched convex-7 runs (|H| = 0..5, use_gap = 0, use_no_c7 = 0)
    for h_sz in range(6):
        n_d = 7 - h_sz
        lr = -1 if h_sz == 0 else 0
        es = "-" if h_sz == 0 else ("x" * h_sz)
        tasks.append({
            "stage": 1,
            "label": f"Stage1 (|D|,|H|)=({n_d},{h_sz})",
            "bin": BIN_H1,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "use_no_c7": 0,
            "masks": build_stage1_masks(h_sz),
        })

    # Stage 2: 68 canonical dihedral orbits (use_gap = 0, use_no_c7 = 1)
    # 1. Split (6, 1): 1 orbit
    tasks.append({
        "stage": 2,
        "label": "Stage2 (6,1) |H|=0 e=0",
        "bin": BIN_H0,
        "n_d": 6,
        "h_sz": 0,
        "lr": -1,
        "es": "0",
        "use_no_c7": 1,
        "masks": build_masks_61(1),
    })

    # 2. Split (5, 2): 3 (|H|=0) + 8 (|H|=1) = 11 orbits
    for i, (es, _) in enumerate(enumerate_h0_orbits()):
        tasks.append({
            "stage": 2,
            "label": f"Stage2 (5,2) #{i:02d} |H|=0 e={es}",
            "bin": BIN_H0,
            "n_d": 5,
            "h_sz": 0,
            "lr": -1,
            "es": es,
            "use_no_c7": 1,
            "masks": build_masks_52(es, 0, 1),
        })
    for j, (eh, ea) in enumerate(enumerate_h1_branches()):
        es = f"{eh}{ea}"
        tasks.append({
            "stage": 2,
            "label": f"Stage2 (5,2) #{3+j:02d} |H|=1 lr=40 e={es}",
            "bin": BIN_H1,
            "n_d": 5,
            "h_sz": 1,
            "lr": 4,
            "es": es,
            "use_no_c7": 1,
            "masks": build_masks_52(es, 1, 1),
        })

    # 3. Split (4, 3): 29 orbits
    for i, (n_d, h_sz, lr, es) in enumerate(canonical_orbits_43()):
        tasks.append({
            "stage": 2,
            "label": f"Stage2 (4,3) #{i:02d} |H|={h_sz} lr={lr} e={es}",
            "bin": BIN_H1,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "use_no_c7": 1,
            "masks": build_masks(n_d, es, 1),
        })

    # 4. Split (3, 4): 23 orbits (tier 2 -> 68 masks on |H|=0, e=0011)
    for i, (n_d, h_sz, lr, es) in enumerate(canonical_orbits_34()):
        tier = 2 if (h_sz == 0 and es == "0011") else 1
        tasks.append({
            "stage": 2,
            "label": f"Stage2 (3,4) #{i:02d} |H|={h_sz} lr={lr} e={es}",
            "bin": BIN_H1,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "use_no_c7": 1,
            "masks": build_masks(n_d, es, tier),
        })

    # 5. Split (2, 5): 4 orbits
    for i, (n_d, h_sz, lr, es) in enumerate(canonical_orbits_25()):
        tasks.append({
            "stage": 2,
            "label": f"Stage2 (2,5) #{i:02d} |H|={h_sz} lr=01 e={es}",
            "bin": BIN_H1,
            "n_d": n_d,
            "h_sz": h_sz,
            "lr": lr,
            "es": es,
            "use_no_c7": 1,
            "masks": build_masks(n_d, es, 1),
        })
    return tasks


def check_seed46_positive_control(solver_name: str) -> dict:
    from fractions import Fraction

    data = json.loads(SEED46_JSON.read_text())
    S = [(Fraction(str(p[0])), Fraction(str(p[1]))) for p in data["points"]]
    W = {}
    for k, pt in data["witnesses"].items():
        mask = int(k) if k.isdigit() else sum(1 << i for i, c in enumerate(reversed(k)) if c == "1")
        W[mask] = (Fraction(str(pt[0])), Fraction(str(pt[1])))
    masks = sorted(W.keys())
    assert len(S) == 6 and len(masks) == 64

    def orient(a, b, c):
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

    pts = S + [W[m] for m in masks]
    args = ["6", "6", "0", "-1", "-", "0", "0", "0", "0", "0", "1", "2", "-"] + [str(m) for m in masks]
    s, nv, ncl = stream_clauses(BIN_H1, args, solver_name=solver_name)
    assump = []
    ms = set()
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            for k in range(j + 1, len(pts)):
                v = o_pos(len(pts), i, j, k)
                pos = orient(pts[i], pts[j], pts[k]) > 0
                assump.append(v if pos else -v)
                if pos:
                    ms.add(v)
    with s:
        sat = s.solve(assumptions=assump)
    assert sat, f"seed46 failed base CNF in {solver_name}"
    sgn, tlit = build_sgn_tlit(len(pts), ms)
    rnd, e_cuts = bulk_cegar_enclosure(6, masks, sgn, tlit, max_rounds=6)
    n1_cuts = find_violated_n1_cuts(6, masks, sgn, tlit, max_cuts=2000)
    assert rnd == 0 and not e_cuts and not n1_cuts
    return {"solver": solver_name, "vars": nv, "clauses": ncl, "sat": True, "violations": 0}


def run_single_task(item: tuple[dict, str]) -> dict:
    task, solver_name = item
    masks = task["masks"]
    args = [
        "7",
        str(task["n_d"]),
        str(task["h_sz"]),
        str(task["lr"]),
        task["es"],
        "0",  # use_gap = 0 everywhere!
        str(task["use_no_c7"]),
        "0",
        "0",
        "1",
        "1",
        "2",
        "-",
    ] + [str(m) for m in masks]
    t0 = time.time()
    s, nv, ncl = stream_clauses(task["bin"], args, solver_name=solver_name)
    tot_cuts = 0
    with s:
        for it in range(1, 201):
            if not s.solve():
                dt = round(time.time() - t0, 2)
                print(
                    f"[{solver_name:10s}] {task['label']:36s} -> UNSAT (|W_0|={len(masks)}, cl={ncl}, rnd={it-1}, cuts={tot_cuts}, {dt}s)",
                    flush=True,
                )
                return {
                    "label": task["label"],
                    "solver": solver_name,
                    "m": len(masks),
                    "clauses": ncl,
                    "rounds": it - 1,
                    "cuts": tot_cuts,
                    "sec": dt,
                    "status": "UNSAT",
                }
            sgn, tlit = build_sgn_tlit(7 + len(masks), set(s.get_model()))
            _, e_cuts = bulk_cegar_enclosure(7, masks, sgn, tlit, max_rounds=6)
            n1_cuts = find_violated_n1_cuts(7, masks, sgn, tlit, max_cuts=1500)
            new_cuts = e_cuts + n1_cuts
            if not new_cuts:
                raise RuntimeError(f"SURVIVED: {task['label']} ({solver_name})")
            s.append_formula(new_cuts)
            tot_cuts += len(new_cuts)
    raise RuntimeError(f"MAX ITERS EXCEEDED: {task['label']} ({solver_name})")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check-orbits", action="store_true", help="Verify orbit/mask counts and positive control only.")
    ap.add_argument("--solvers", default="cadical195,glucose4")
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()

    tasks = build_all_74_tasks()
    s1 = [t for t in tasks if t["stage"] == 1]
    s2 = [t for t in tasks if t["stage"] == 2]
    assert len(s1) == 6 and len(s2) == 68, f"Expected 6 + 68 = 74 tasks, got {len(s1)} + {len(s2)}"
    assert [len(t["masks"]) for t in s1] == [36, 29, 34, 34, 33, 32]
    print(f"Verified task decomposition: {len(s1)} Stage 1 + {len(s2)} Stage 2 = {len(tasks)} total instances.")

    ensure_binaries()
    solvers = [x.strip() for x in args.solvers.split(",") if x.strip()]
    for sv in solvers:
        res = check_seed46_positive_control(sv)
        print(f"Verified positive control seed46 ({sv}): SAT with 0 violations ({res['clauses']:,} clauses).")

    if args.check_orbits:
        return

    work = [(t, sv) for sv in solvers for t in tasks]
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        results = list(ex.map(run_single_task, work))
    assert all(r["status"] == "UNSAT" for r in results)
    print(f"ALL {len(results)} / {len(results)} SOLVER RUNS VERIFIED UNSAT.")


if __name__ == "__main__":
    main()
