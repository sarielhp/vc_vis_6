#!/usr/bin/env python3
"""Test (5, 2) (|D|=5, |M|=2, |H| in {0, 1}) for |S|=7 across all 3 + 8 canonical branches."""
import os
import sys
import time
from collections import Counter
from itertools import combinations_with_replacement

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cegar_engine import stream_clauses, build_sgn_tlit, bulk_cegar_enclosure, find_violated_n1_cuts

BIN_H0 = os.path.join(HERE, "gen_chiro_h0")
BIN_H1 = os.path.join(HERE, "gen_chiro_h1")


def enumerate_h0_orbits():
    def d5_canon(t):
        forms = []
        for s in range(5):
            forms.append(tuple(sorted((x + s) % 5 for x in t)))
            forms.append(tuple(sorted((4 - x + s) % 5 for x in t)))
        return min(forms)

    all_15 = list(combinations_with_replacement(range(5), 2))
    counts = Counter(d5_canon(c) for c in all_15)
    orbits = sorted(counts.keys())
    assert len(orbits) == 3 and sum(counts.values()) == 15
    return [("".join(str(x) for x in o), counts[o]) for o in orbits]


def enumerate_h1_branches():
    branches = []
    for eh in (0, 1):
        for ea in range(4):
            branches.append((eh, ea))
    assert len(branches) == 8
    return branches


def build_masks_52(edge_str, h_size, tier):
    # Base core masks:
    # 1. W(D u J) for all J <= M (4 masks: w(D)=31, ..., w(S)=127)
    masks = {31 | (jm << 5) for jm in range(4)}
    # 2. pop=6 (single misses)
    for k in range(7):
        masks.add(127 ^ (1 << k))
    # 3. x_k(00) for k=0..4
    for k in range(5):
        masks.add(31 ^ (1 << k))
    # 4. |O|=2 non-adjacent pairs in D
    for k1, k2 in [(0, 2), (1, 3), (2, 4), (3, 0), (4, 1)]:
        masks.add(127 ^ (1 << k1) ^ (1 << k2))
    # 5. Prop 6.6 interior-anchor |O|=3 masks
    es = [int(c) for c in edge_str]
    for i, e in enumerate(es):
        y = 5 + i
        b, bp = (e + 2) % 5, (e + 4) % 5
        masks.add(127 ^ (1 << bp) ^ (1 << y) ^ (1 << b))
    # 6. Lemma 6.8 / adj pairs
    if len(es) == 2:
        e0, e1 = es[0], es[1]
        if (e1 - e0 + 5) % 5 == 2:
            b = (e0 + 4) % 5
            masks.add(127 ^ (1 << b) ^ (1 << 5) ^ (1 << 6))
        elif (e0 - e1 + 5) % 5 == 2:
            b = (e1 + 4) % 5
            masks.add(127 ^ (1 << b) ^ (1 << 5) ^ (1 << 6))
        elif (e1 - e0 + 5) % 5 == 1:
            for off in (2, 3, 4):
                masks.add(127 ^ (1 << ((e0 + off) % 5)) ^ (1 << 5) ^ (1 << 6))
        elif (e0 - e1 + 5) % 5 == 1:
            for off in (2, 3, 4):
                masks.add(127 ^ (1 << ((e1 + off) % 5)) ^ (1 << 5) ^ (1 << 6))

    # Add all pop=5
    for m in range(128):
        if bin(m).count("1") == 5:
            masks.add(m)
    if tier >= 2:
        # Add all pop=4
        for m in range(128):
            if bin(m).count("1") == 4:
                masks.add(m)
    if tier >= 3:
        # Add all pop=3
        for m in range(128):
            if bin(m).count("1") == 3:
                masks.add(m)
    if tier >= 4:
        masks = set(range(128))
    return sorted(masks)


def solve_one(label, bin_path, h_size, lr_l, edge_str, tier, use_gap=1, f_flags=0, use_4cyc=0, use_vis_ss=1, mw=2, max_iters=150):
    masks = build_masks_52(edge_str, h_size, tier)
    t0 = time.time()
    arg6 = use_gap if h_size == 0 else 0
    args = [
        "7", "5", str(h_size), str(lr_l), edge_str, str(arg6),
        "1", str(use_4cyc), str(f_flags), "1", str(use_vis_ss), str(mw), "-"
    ] + [str(m) for m in masks]
    s, nv, ncl = stream_clauses(bin_path, args)
    t_load = time.time() - t0
    with s:
        tot_cuts = 0
        for it in range(1, max_iters + 1):
            r = s.solve()
            if not r:
                print(f"  [{label:16s} t={tier}] UNSAT! (m={len(masks)}, cl={ncl}, load={t_load:.1f}s, iters={it-1}, cuts={tot_cuts}, tot={time.time()-t0:.1f}s)", flush=True)
                return False
            sgn, tlit = build_sgn_tlit(7 + len(masks), set(s.get_model()))
            rnd, cuts = bulk_cegar_enclosure(7, masks, sgn, tlit, max_rounds=6)
            n1_cuts = find_violated_n1_cuts(7, masks, sgn, tlit, max_cuts=1500)
            all_new = cuts + n1_cuts
            if not all_new:
                print(f"  [{label:16s} t={tier}] FIXPOINT SURVIVED (m={len(masks)}, iter={it}, cuts={tot_cuts}, tot={time.time()-t0:.1f}s)", flush=True)
                return True
            s.append_formula(all_new)
            tot_cuts += len(all_new)
    print(f"  [{label:16s} t={tier}] MAX_ITERS SURVIVED", flush=True)
    return True


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    tiers = [int(x) for x in sys.argv[2:]] if len(sys.argv) > 2 else [1, 2, 3]
    cases = []
    if mode in ("all", "h0"):
        for es, sz in enumerate_h0_orbits():
            cases.append((f"h0 e={es} (sz={sz})", BIN_H0, 0, -1, es))
    if mode in ("all", "h1"):
        for eh, ea in enumerate_h1_branches():
            es = f"{eh}{ea}"
            cases.append((f"h1 e={es}", BIN_H1, 1, 4, es))

    survivors = []
    for label, bin_path, h_size, lr_l, es in cases:
        closed = False
        for t in tiers:
            surv = solve_one(label, bin_path, h_size, lr_l, es, t)
            if not surv:
                closed = True
                break
        if not closed:
            survivors.append(label)
    print(f"SUMMARY (5,2) mode={mode} tiers={tiers}: {len(cases)-len(survivors)}/{len(cases)} UNSAT, survivors={survivors}", flush=True)
    sys.exit(0 if not survivors else 1)
