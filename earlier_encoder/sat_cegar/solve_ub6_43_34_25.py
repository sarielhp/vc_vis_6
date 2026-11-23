#!/usr/bin/env python3
"""Test (4, 3), (3, 4), and (2, 5) for |S|=7 with adaptive mask tiers."""
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations_with_replacement, product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cegar_engine import stream_clauses, build_sgn_tlit, bulk_cegar_enclosure, find_violated_n1_cuts

BIN_H1 = os.path.join(HERE, "gen_chiro_h1")


def canonical_orbits_43():
    def canon(h_sz, lr_l, e_h, e_a):
        reps = []
        for s in range(4):
            nlr = (lr_l + s) % 4 if h_sz > 0 else -1
            neh = tuple((e + s) % 4 for e in e_h)
            nea = tuple(sorted((e + s) % 4 for e in e_a))
            reps.append((h_sz, nlr, neh, nea))
        for c in range(4):
            nlr = (c - lr_l - 1) % 4 if h_sz > 0 else -1
            neh = tuple((c - e - 1) % 4 for e in reversed(e_h))
            nea = tuple(sorted((c - e - 1) % 4 for e in e_a))
            reps.append((h_sz, nlr, neh, nea))
        return min(reps)

    orbits = set()
    for h_sz in (0, 1, 2):
        lrs = (-1,) if h_sz == 0 else (0, 1, 2, 3)
        for lr in lrs:
            avail = (0, 1, 2, 3) if h_sz == 0 else tuple(e for e in range(4) if e != lr)
            for e_h in product(avail, repeat=h_sz):
                for e_a in combinations_with_replacement(avail, 3 - h_sz):
                    orbits.add(canon(h_sz, lr, e_h, e_a))
    return [(4, h_sz, lr, "".join(map(str, e_h + e_a))) for h_sz, lr, e_h, e_a in sorted(orbits)]


def canonical_orbits_34():
    def canon(h_sz, lr_l, e_h, e_a):
        reps = []
        for s in range(3):
            nlr = (lr_l + s) % 3 if h_sz > 0 else -1
            neh = tuple((e + s) % 3 for e in e_h)
            nea = tuple(sorted((e + s) % 3 for e in e_a))
            reps.append((h_sz, nlr, neh, nea))
        for c in range(3):
            nlr = (c - lr_l - 1) % 3 if h_sz > 0 else -1
            neh = tuple((c - e - 1) % 3 for e in reversed(e_h))
            nea = tuple(sorted((c - e - 1) % 3 for e in e_a))
            reps.append((h_sz, nlr, neh, nea))
        return min(reps)

    orbits = set()
    for h_sz in (0, 1, 2, 3):
        lrs = (-1,) if h_sz == 0 else (0, 1, 2)
        for lr in lrs:
            avail = (0, 1, 2) if h_sz == 0 else tuple(e for e in range(3) if e != lr)
            for e_h in product(avail, repeat=h_sz):
                for e_a in combinations_with_replacement(avail, 4 - h_sz):
                    orbits.add(canon(h_sz, lr, e_h, e_a))
    return [(3, h_sz, lr, "".join(map(str, e_h + e_a))) for h_sz, lr, e_h, e_a in sorted(orbits)]


def canonical_orbits_25():
    return [(2, h_sz, 0, "xxxxx") for h_sz in (1, 2, 3, 4)]


def build_masks(n_d, edge_str, tier):
    d_mask = (1 << n_d) - 1
    m_sz = 7 - n_d
    # 1. All W(D u J)
    masks = {d_mask | (jm << n_d) for jm in range(1 << m_sz)}
    # 2. All pop=6
    for k in range(7):
        masks.add(127 ^ (1 << k))
    # 3. D \ {k}
    for k in range(n_d):
        masks.add(d_mask ^ (1 << k))
    # 4. S \ {i, j} for i, j in D
    for i in range(n_d):
        for j in range(i + 1, n_d):
            masks.add(127 ^ (1 << i) ^ (1 << j))
    # 5. Edge omasks if n_d >= 3
    if n_d >= 3 and "x" not in edge_str:
        for k in range(n_d):
            inc = {k, (k - 1) % n_d}
            omask = 127 ^ (1 << k)
            for i, ch in enumerate(edge_str):
                if int(ch) in inc:
                    omask ^= (1 << (n_d + i))
            masks.add(omask)
    # 6. All pop=5
    for m in range(128):
        if bin(m).count("1") == 5:
            masks.add(m)
    if tier >= 2:
        for m in range(128):
            if bin(m).count("1") == 4:
                masks.add(m)
    if tier >= 3:
        for m in range(128):
            if bin(m).count("1") == 3:
                masks.add(m)
    if tier >= 4:
        masks = set(range(128))
    return sorted(masks)


def solve_one(item):
    idx, n_d, h_sz, lr, es, tiers, max_iters = item
    lr_s = "none" if lr < 0 else f"{lr}{(lr + 1) % n_d}"
    label = f"({n_d},{7-n_d}) #{idx:02d} |H|={h_sz} lr={lr_s} e={es}"
    t0 = time.time()
    for tier in tiers:
        masks = build_masks(n_d, es, tier)
        mw = 2 if len(masks) <= 110 else 1
        args = [
            "7", str(n_d), str(h_sz), str(lr), es, "0",
            "1", "0", "0", "1", "1", str(mw), "-"
        ] + [str(m) for m in masks]
        s, nv, ncl = stream_clauses(BIN_H1, args)
        with s:
            tot_cuts = 0
            survived = False
            for it in range(1, max_iters + 1):
                r = s.solve()
                if not r:
                    dt = time.time() - t0
                    print(f"  [{label:36s}] UNSAT! (t={tier}, m={len(masks)}, cl={ncl}, iters={it-1}, cuts={tot_cuts}, tot={dt:.1f}s)", flush=True)
                    return {"idx": idx, "n_d": n_d, "h_sz": h_sz, "lr": lr, "es": es, "tier": tier, "m": len(masks), "status": "UNSAT", "iters": it - 1, "cuts": tot_cuts, "sec": round(dt, 2)}
                sgn, tlit = build_sgn_tlit(7 + len(masks), set(s.get_model()))
                rnd, cuts = bulk_cegar_enclosure(7, masks, sgn, tlit, max_rounds=6)
                n1_cuts = find_violated_n1_cuts(7, masks, sgn, tlit, max_cuts=1500)
                all_new = cuts + n1_cuts
                if not all_new:
                    print(f"  [{label:36s}] FIXPOINT t={tier} (m={len(masks)}, iter={it}, cuts={tot_cuts}, {time.time()-t0:.1f}s)", flush=True)
                    survived = True
                    break
                s.append_formula(all_new)
                tot_cuts += len(all_new)
            else:
                print(f"  [{label:36s}] MAX_ITERS t={tier} (m={len(masks)}, {time.time()-t0:.1f}s)", flush=True)
                survived = True
        if not survived:
            break
    dt = time.time() - t0
    return {"idx": idx, "n_d": n_d, "h_sz": h_sz, "lr": lr, "es": es, "tier": tiers[-1], "m": len(masks), "status": "SURVIVED", "iters": max_iters, "cuts": tot_cuts, "sec": round(dt, 2)}


if __name__ == "__main__":
    chunk = sys.argv[1]  # "43", "34", "25"
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    tiers = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [1, 2, 3]
    start = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    end = int(sys.argv[5]) if len(sys.argv) > 5 else None

    if chunk == "43":
        orbits = canonical_orbits_43()
    elif chunk == "34":
        orbits = canonical_orbits_34()
    elif chunk == "25":
        orbits = canonical_orbits_25()
    else:
        raise ValueError(chunk)

    if end is None:
        end = len(orbits)
    items = [(i, orbits[i][0], orbits[i][1], orbits[i][2], orbits[i][3], tiers, 150) for i in range(start, end)]
    print(f"Running chunk ({chunk}) [{start}:{end}] ({len(items)}/{len(orbits)} orbits), tiers={tiers}, workers={workers}", flush=True)
    t0 = time.time()
    if workers <= 1:
        results = [solve_one(it) for it in items]
    else:
        with ProcessPoolExecutor(max_workers=workers) as ex:
            results = list(ex.map(solve_one, items))
    unsat = sum(1 for r in results if r["status"] == "UNSAT")
    surv = [r for r in results if r["status"] != "UNSAT"]
    out_json = f"{HERE}/results_{chunk}_{start}_{end}.json"
    with open(out_json, "w") as f:
        json.dump(results, f, indent=2)
    print(f"SUMMARY ({chunk}) [{start}:{end}]: {unsat}/{len(results)} UNSAT, {len(surv)} survivors in {time.time()-t0:.1f}s -> {out_json}", flush=True)
    sys.exit(0 if not surv else 1)
