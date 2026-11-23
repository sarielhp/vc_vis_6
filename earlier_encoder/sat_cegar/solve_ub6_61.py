#!/usr/bin/env python3
"""Test (6, 1) (|D|=6, |H|=0, |A|=1) for |S|=7 with adaptive mask sets up to 128."""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cegar_engine import stream_clauses, build_sgn_tlit, bulk_cegar_enclosure, find_violated_n1_cuts

BIN_H0 = os.path.join(HERE, "gen_chiro_h0")


def build_masks_61(tier):
    # Base core masks for (6,1): D={0..5}, A={6}, edge="0" (u0=0, v0=1)
    # 1. W(D u J): w(D)=63, w(S)=127
    masks = {63, 127}
    # 2. pop=6 (single misses)
    for k in range(7):
        masks.add(127 ^ (1 << k))
    # 3. x_k(0) for k=0..5
    for k in range(6):
        masks.add(63 ^ (1 << k))
    # 4. Prop 6.5 alternating sources O_0={1,3,5}, O_1={0,2,4}
    masks.add(127 ^ ((1 << 1) | (1 << 3) | (1 << 5)))
    masks.add(127 ^ ((1 << 0) | (1 << 2) | (1 << 4)))
    # 5. Prop 6.6 interior-anchor |O|=3 masks for y=6, e=0
    for b_off, bp_off in [(2, 4), (3, 5), (2, 5)]:
        masks.add(127 ^ (1 << b_off) ^ (1 << bp_off) ^ (1 << 6))
    # 6. All pop=5 (21 masks)
    for m in range(128):
        if bin(m).count("1") == 5:
            masks.add(m)

    if tier >= 2:
        # Add all pop=4 (35 masks) -> ~72 masks total
        for m in range(128):
            if bin(m).count("1") == 4:
                masks.add(m)
    if tier >= 3:
        # Add pop=3 masks missing 6 or having {0,1} or D-only pop=3
        for m in range(128):
            if bin(m).count("1") == 3:
                masks.add(m)
    if tier >= 4:
        # All 128 masks
        masks = set(range(128))
    return sorted(masks)


def solve_tier(tier, use_gap=1, f_flags=0, use_4cyc=0, use_vis_ss=1, mw=2, max_iters=150):
    masks = build_masks_61(tier)
    t0 = time.time()
    args = [
        "7", "6", "0", "-1", "0", str(use_gap),
        "1", str(use_4cyc), str(f_flags), "1", str(use_vis_ss), str(mw), "-"
    ] + [str(m) for m in masks]
    s, nv, ncl = stream_clauses(BIN_H0, args)
    t_load = time.time() - t0
    print(f"[6,1 tier={tier}] m={len(masks)} vars={nv} cl={ncl} load={t_load:.1f}s", flush=True)
    with s:
        tot_cuts = 0
        for it in range(1, max_iters + 1):
            r = s.solve()
            if not r:
                print(f"[6,1 tier={tier}] UNSAT! (m={len(masks)}, iters={it-1}, cuts={tot_cuts}, tot={time.time()-t0:.1f}s)", flush=True)
                return False
            sgn, tlit = build_sgn_tlit(7 + len(masks), set(s.get_model()))
            rnd, cuts = bulk_cegar_enclosure(7, masks, sgn, tlit, max_rounds=6)
            n1_cuts = find_violated_n1_cuts(7, masks, sgn, tlit, max_cuts=1500)
            all_new = cuts + n1_cuts
            if not all_new:
                print(f"[6,1 tier={tier}] FIXPOINT SURVIVED (m={len(masks)}, iter={it}, cuts={tot_cuts}, tot={time.time()-t0:.1f}s)", flush=True)
                return True
            s.append_formula(all_new)
            tot_cuts += len(all_new)
            if it <= 5 or it % 10 == 0:
                print(f"  tier={tier} iter={it}: rnd={rnd} +{len(cuts)} e, +{len(n1_cuts)} n1 (tot={tot_cuts}, {time.time()-t0:.1f}s)", flush=True)
    print(f"[6,1 tier={tier}] MAX_ITERS SURVIVED", flush=True)
    return True


if __name__ == "__main__":
    tiers = [int(x) for x in sys.argv[1:]] if len(sys.argv) > 1 else [1, 2, 3]
    for t in tiers:
        survived = solve_tier(t)
        if not survived:
            print(f"DONE: (6, 1) CLOSED UNSAT at tier={t}!", flush=True)
            sys.exit(0)
    print("DONE: all requested tiers survived!", flush=True)
    sys.exit(1)
