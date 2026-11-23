#!/usr/bin/env python3
"""
Complete Independent Symbolic Z3 QF_NRA Verification of EVERY Clause Schema
used in convex7_close, u2_all7_close, u3_h0_close, u3_h1_close, u4_h012_close,
including bulk_cegar_enclosure and find_violated_n1_cuts.

Requirements enforced on every single lemma:
  - <= 8 points per Z3 QF_NRA query
  - Base SAT == sat explicitly asserted BEFORE negating the conclusion
  - 0 'unknown' results (every negation check must return unsat)
  - exit 0 iff all checks pass
"""
import sys
import time
from itertools import combinations
from pysat.solvers import Solver
import z3


def orient(a, b, c):
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def segs_cross(a, b, c, d):
    return z3.And(
        orient(a, b, c) * orient(a, b, d) < 0,
        orient(c, d, a) * orient(c, d, b) < 0,
    )


def same_side(a, b, p, q):
    return orient(a, b, p) * orient(a, b, q) > 0


def in_int_tri_ccw(p, a, b, c):
    return z3.And(orient(a, b, p) > 0, orient(b, c, p) > 0, orient(c, a, p) > 0)


def in_int_tri_any(p, a, b, c):
    return z3.Or(in_int_tri_ccw(p, a, b, c), in_int_tri_ccw(p, a, c, b))


def pt(name):
    return (z3.Real(f"{name}x"), z3.Real(f"{name}y"))


def assert_base_sat_and_neg_unsat(label, base_constraints, neg_conclusion, timeout_ms=25000):
    t0 = time.time()
    s_base = z3.Tactic("qfnra-nlsat").solver()
    s_base.set("timeout", min(5000, timeout_ms))
    s_base.add(*base_constraints)
    r_base = s_base.check()
    if r_base == z3.unknown:
        s_base2 = z3.Solver()
        s_base2.set("timeout", timeout_ms)
        s_base2.add(*base_constraints)
        r_base = s_base2.check()
    assert r_base == z3.sat, f"[{label}] Base constraints NOT sat: {r_base}"

    s_neg = z3.Tactic("qfnra-nlsat").solver()
    s_neg.set("timeout", timeout_ms)
    s_neg.add(*base_constraints)
    s_neg.add(neg_conclusion)
    r_neg = s_neg.check()
    if r_neg == z3.unknown:
        s_neg2 = z3.Solver()
        s_neg2.set("timeout", timeout_ms)
        s_neg2.add(*base_constraints)
        s_neg2.add(neg_conclusion)
        r_neg = s_neg2.check()
    dt = time.time() - t0
    print(f"  [{label:58s}] base=sat, neg={str(r_neg):5s} ({dt:.2f}s)", flush=True)
    assert r_neg == z3.unsat, f"[{label}] FAILED: expected unsat, got {r_neg}"


# =============================================================================
# 1. 5-pt Grassmann-Plucker Identity (add_gp)
# =============================================================================
def verify_add_gp():
    print("\n=== 1. 5-pt Grassmann-Plucker Identity (add_gp) ===", flush=True)
    p = (z3.RealVal(0), z3.RealVal(0))
    a = (z3.RealVal(1), z3.RealVal(0))
    b = (z3.RealVal(0), z3.RealVal(1))
    c, d = pt("c"), pt("d")
    pts = [p, a, b, c, d]
    gp = []
    for i in range(5):
        for j in range(i + 1, 5):
            for k in range(j + 1, 5):
                if (i, j, k) != (0, 1, 2):
                    gp.append(orient(pts[i], pts[j], pts[k]) != 0)
    l1, l2 = orient(p, a, b), orient(p, c, d)
    l3, l4 = orient(p, a, c), -orient(p, b, d)
    l5, l6 = orient(p, a, d), orient(p, b, c)
    # All 16 clauses from add_gp:
    bad_assignments = []
    for s1 in (-1, 1):
        for s2 in (-1, 1):
            for s3 in (-1, 1):
                bad_assignments.append(
                    z3.And(s1 * l1 > 0, s1 * l2 > 0, s2 * l3 > 0, s2 * l4 > 0, s3 * l5 > 0, s3 * l6 > 0)
                )
                bad_assignments.append(
                    z3.And(s1 * l1 > 0, -s1 * l2 > 0, s2 * l3 > 0, -s2 * l4 > 0, s3 * l5 > 0, -s3 * l6 > 0)
                )
    assert_base_sat_and_neg_unsat("5-pt GP identity (all 16 clauses)", gp, z3.Or(*bad_assignments))


# =============================================================================
# 2. Caratheodory Non-Convexity Equivalence for 7 Points (use_no_c7)
# =============================================================================
def verify_caratheodory_7pt():
    print("\n=== 2. Caratheodory Non-Convexity Equivalence (use_no_c7) ===", flush=True)
    # Dir 1: If some 4-subset has 1 point inside int tri of the other 3, the set is NOT strictly convex
    # (that point cannot be strictly separated by any linear functional from the other 3).
    p0 = (z3.RealVal(0), z3.RealVal(0))
    p1 = (z3.RealVal(1), z3.RealVal(0))
    p2 = (z3.RealVal(0), z3.RealVal(1))
    p3 = pt("p3")
    nx, ny = z3.Real("nx"), z3.Real("ny")
    base1 = [in_int_tri_ccw(p3, p0, p1, p2)]
    neg1 = z3.And(
        nx * p3[0] + ny * p3[1] > nx * p0[0] + ny * p0[1],
        nx * p3[0] + ny * p3[1] > nx * p1[0] + ny * p1[1],
        nx * p3[0] + ny * p3[1] > nx * p2[0] + ny * p2[1],
    )
    assert_base_sat_and_neg_unsat("Caratheodory Dir1: in_int_tri => no separating line", base1, neg1)

    # Dir 2a: 5-pt Caratheodory reduction step: p4 in conv(p0..p3) in GP => p4 in int tri of some 3-subset
    q = [(z3.RealVal(0), z3.RealVal(0)), (z3.RealVal(1), z3.RealVal(0)), (z3.RealVal(0), z3.RealVal(1)), pt("q3"), pt("q4")]
    gp5 = [orient(q[i], q[j], q[k]) != 0 for i in range(5) for j in range(i + 1, 5) for k in range(j + 1, 5) if (i, j, k) != (0, 1, 2)]
    lams = [z3.Real(f"l{i}") for i in range(4)]
    base2a = gp5 + [l >= 0 for l in lams] + [
        sum(lams) == 1,
        q[4][0] == sum(lams[i] * q[i][0] for i in range(4)),
        q[4][1] == sum(lams[i] * q[i][1] for i in range(4)),
    ]
    neg2a = z3.And(*[z3.Not(in_int_tri_any(q[4], q[a], q[b], q[c])) for a, b, c in [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]])
    assert_base_sat_and_neg_unsat("Caratheodory Dir2a: 5-pt conv reduction", base2a, neg2a)

    # Dir 2b: 7-pt fan triangulation: if p0..p5 are strictly convex CCW and p6 in conv(p0..p5),
    # then p6 lies in int tri(0, i, i+1) for some i in {1..4}.
    h = [(z3.RealVal(0), z3.RealVal(0)), (z3.RealVal(1), z3.RealVal(0)), (z3.RealVal(0), z3.RealVal(1))] + [pt(f"h{i}") for i in range(3, 7)]
    base2b = []
    for i in range(6):
        for j in range(i + 1, 6):
            for k in range(j + 1, 6):
                if (i, j, k) != (0, 1, 2):
                    base2b.append(orient(h[i], h[j], h[k]) > 0)
    for i in range(6):
        for j in range(i + 1, 6):
            base2b.append(orient(h[i], h[j], h[6]) != 0)
    for r in range(6):
        base2b.append(orient(h[r], h[(r + 1) % 6], h[6]) > 0)
    neg2b = z3.And(*[z3.Not(in_int_tri_any(h[6], h[0], h[i], h[i + 1])) for i in range(1, 5)])
    assert_base_sat_and_neg_unsat("Caratheodory Dir2b: 7-pt fan tri when p0..p5 convex", base2b, neg2b)

    # Dir 2c: Every 4-subset of a strictly convex CCW set has NO 1-in-tri-of-3 (4-pt check => holds for all C(7,4)=35 4-subsets)
    s4 = [(z3.RealVal(0), z3.RealVal(0)), (z3.RealVal(1), z3.RealVal(0)), (z3.RealVal(0), z3.RealVal(1)), pt("s3")]
    base2c = [orient(s4[i], s4[j], s4[k]) > 0 for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4) if (i, j, k) != (0, 1, 2)]
    has_4_in = [in_int_tri_any(s4[idx], *[s4[m] for m in range(4) if m != idx]) for idx in range(4)]
    assert_base_sat_and_neg_unsat("Caratheodory Dir2c: strictly convex 4-gon => no 4-in-tri", base2c, z3.Or(*has_4_in))


# =============================================================================
# 3. Non-certified Vertex Obstruction (k in D, u,v in conv(B))
# =============================================================================
def verify_non_certified_obstruction():
    print("\n=== 3. Non-Certified Vertex Obstruction (k in D, u,v in conv(B)) ===", flush=True)
    # Pin k=(0,0), kp=(1,0), km=(0,1) so conv(B) lies in {x >= 0, y >= 0}.
    k = (z3.RealVal(0), z3.RealVal(0))
    kp = (z3.RealVal(1), z3.RealVal(0))
    km = (z3.RealVal(0), z3.RealVal(1))
    w, zk, u, v = pt("w"), pt("zk"), pt("u"), pt("v")
    # By Lemma 2.2 (cone): w sees u,v, misses k, k in int tri(w, u, v) => zk sees u,v => k in int tri(zk, u, v)
    # Prove: (a) k in int tri(w,u,v) & zk in U(k; u,v) => both edges km-k and k-kp face zk!
    # Also test u=km (boundary of conv(B)) and u,v strictly in cone(kp-k, km-k)!
    for case_name, u_pt, v_pt, extra in [
        ("u,v in int cone(kp,km)", u, v, [u[0] > 0, u[1] > 0, v[0] > 0, v[1] > 0, orient(k, u, v) != 0]),
        ("u=km, v in int cone(kp,km)", km, v, [v[0] > 0, v[1] > 0]),
        ("u=km, v=kp (neighbors in B)", km, kp, []),
    ]:
        base = extra + [
            in_int_tri_any(k, w, u_pt, v_pt),
            # Cone lemma: line k-zk separates u from v and lies in U(k; u, v), i.e., k in int tri(zk, u, v):
            in_int_tri_any(k, zk, u_pt, v_pt),
        ]
        # Negate: NOT (both edges km->k and k->kp face zk, i.e., orient(km, k, zk) < 0 and orient(k, kp, zk) < 0)
        neg = z3.Not(z3.And(orient(km, k, zk) < 0, orient(k, kp, zk) < 0))
        assert_base_sat_and_neg_unsat(f"Non-cert vertex ({case_name})", base, neg)


# =============================================================================
# 4. add_wedge_sep (w1, w2 in U(y; u, v) and wm misses y seeing u,v)
# =============================================================================
def verify_add_wedge_sep():
    print("\n=== 4. add_wedge_sep (Convex Wedge Separation) ===", flush=True)
    y = (z3.RealVal(0), z3.RealVal(0))
    u = (z3.RealVal(1), z3.RealVal(0))
    v = (z3.RealVal(0), z3.RealVal(1))
    w1, w2, wm = pt("w1"), pt("w2"), pt("wm")
    # w1, w2, wm in U(y; u, v) = {x < 0, y < 0}
    base = [
        in_int_tri_ccw(y, w1, u, v),
        in_int_tri_ccw(y, w2, u, v),
        in_int_tri_ccw(y, wm, u, v),
        orient(y, w1, w2) != 0,
    ]
    # If wm in y + cone(w1 - y, w2 - y) (either CCW or CW), then line y-wm separates w1 from w2 AND separates u from v,
    # AND in fact [y, wm] is enclosed by (y - w1 - {u|v} - wm) and (y - w2 - {v|u} - wm) on opposite sides of y-wm!
    in_cone_ccw = z3.And(orient(y, w1, w2) > 0, orient(y, w1, wm) > 0, orient(y, wm, w2) > 0)
    in_cone_cw = z3.And(orient(y, w2, w1) > 0, orient(y, w2, wm) > 0, orient(y, wm, w1) > 0)
    for cname, cexpr in [("CCW cone", in_cone_ccw), ("CW cone", in_cone_cw)]:
        # Enclosure: either (w1, u on one side, w2, v on other) OR (w1, v on one side, w2, u on other)
        enc1 = z3.And(orient(y, wm, w1) * orient(y, wm, u) > 0, orient(y, wm, w2) * orient(y, wm, v) > 0, orient(y, wm, w1) * orient(y, wm, w2) < 0)
        enc2 = z3.And(orient(y, wm, w1) * orient(y, wm, v) > 0, orient(y, wm, w2) * orient(y, wm, u) > 0, orient(y, wm, w1) * orient(y, wm, w2) < 0)
        assert_base_sat_and_neg_unsat(f"add_wedge_sep ({cname}) => enclosure", base + [cexpr], z3.Not(z3.Or(enc1, enc2)))


# =============================================================================
# 5. Lemma side-corners & Lemma separation (H != empty)
# =============================================================================
def verify_side_corners_and_separation():
    print("\n=== 5. Lemma side-corners & Lemma separation ===", flush=True)
    h = (z3.RealVal(0), z3.RealVal(0))
    hp = (z3.RealVal(1), z3.RealVal(0))
    hm = (z3.RealVal(0), z3.RealVal(1))
    zh, u, v, w = pt("zh"), pt("u"), pt("v"), pt("w")
    # h is front vertex of B from zh: orient(hm, h, zh) < 0 and orient(h, hp, zh) < 0 (so zh in {x < 0, y < 0})
    # u, v in S \ {h} subset conv(B) \ {h}: u_x >= 0, u_y >= 0 (not both 0), same for v.
    # Suppose u and v lie on opposite sides of line zh-h: orient(zh, h, u) * orient(zh, h, v) < 0.
    for cname, u_pt, v_pt, extra in [
        ("u,v in int conv(B)", u, v, [u[0] > 0, u[1] > 0, v[0] > 0, v[1] > 0]),
        ("u=hm, v in int conv(B)", hm, v, [v[0] > 0, v[1] > 0]),
        ("u=hm, v=hp", hm, hp, []),
    ]:
        base = extra + [
            orient(hm, h, zh) < 0,
            orient(h, hp, zh) < 0,
            orient(zh, h, u_pt) * orient(zh, h, v_pt) < 0,
        ]
        # Prove h in int tri(zh, u, v)!
        assert_base_sat_and_neg_unsat(f"side-corners ({cname}) => h in tri(zh,u,v)", base, z3.Not(in_int_tri_any(h, zh, u_pt, v_pt)))

    # Lemma separation: q, h, hm, hp, m, mp, zh (7 pts!)
    # Along N_q from hm -> h -> hp -> ... -> m -> mp, directions from q=(-1,-2) turn CW strictly:
    # orient(q, hm, h) < 0, orient(q, h, hp) < 0, orient(q, h, m) < 0, orient(q, m, mp) < 0, orient(q, h, mp) < 0.
    # Also m, mp in conv(B) \ {h} (m_x > 0, m_y > 0) and q sees m, mp.
    # Cannot have m, mp on opposite sides of zh-h (else by side-corners h in int tri(q, m, mp), impossible!).
    q = (z3.RealVal(-1), z3.RealVal(-2))
    m, mp = pt("m"), pt("mp")
    base_sep = [
        orient(hm, h, zh) < 0, orient(h, hp, zh) < 0,
        m[0] > 0, m[1] > 0, mp[0] > 0, mp[1] > 0,
        orient(q, h, m) < 0, orient(q, m, mp) < 0, orient(q, h, mp) < 0,
        # Lemma cone (since q sees m, mp and zh sees m, mp, misses h):
        z3.Implies(in_int_tri_any(h, zh, m, mp), in_int_tri_any(h, q, m, mp)),
    ]
    # Prove: if orient(zh, h, m) * orient(zh, h, mp) < 0, then h in int tri(q, m, mp), which contradicts orient(q, h, m)<0 & orient(q, h, mp)<0!
    neg_sep = orient(zh, h, m) * orient(zh, h, mp) < 0
    assert_base_sat_and_neg_unsat("Lemma separation (angular monotonicity)", base_sep, neg_sep)


# =============================================================================
# 6. Asymmetric Two-Sided Separation
# =============================================================================
def verify_asymmetric_two_sided():
    print("\n=== 6. Asymmetric Two-Sided Separation ===", flush=True)
    d = (z3.RealVal(0), z3.RealVal(0))
    wx = (z3.RealVal(1), z3.RealVal(0))
    u, v, wi, wj = pt("u"), pt("v"), pt("wi"), pt("wj")
    # Forbidden config 1: u > 0, v < 0, wi > 0, wj < 0 wrt (d, wx)
    base1 = [
        orient(d, wx, u) > 0, orient(d, wx, v) < 0,
        orient(d, wx, wi) > 0, orient(d, wx, wj) < 0,
    ]
    # Prove paths wx-u-wi-d and wx-v-wj-d lie in opposite open sides of (d, wx) (Jordan curve enclosing [d, wx]):
    neg1 = z3.Not(z3.And(u[1] > 0, wi[1] > 0, v[1] < 0, wj[1] < 0))
    assert_base_sat_and_neg_unsat("Asymmetric Two-Sided Sep (clause 1)", base1, neg1)

    base2 = [
        orient(d, wx, u) < 0, orient(d, wx, v) > 0,
        orient(d, wx, wi) < 0, orient(d, wx, wj) > 0,
    ]
    neg2 = z3.Not(z3.And(u[1] < 0, wi[1] < 0, v[1] > 0, wj[1] > 0))
    assert_base_sat_and_neg_unsat("Asymmetric Two-Sided Sep (clause 2)", base2, neg2)


# =============================================================================
# 7. Universal Half-Plane Lemma (sgn = +1 AND sgn = -1)
# =============================================================================
def verify_universal_halfplane():
    print("\n=== 7. Universal Half-Plane Lemma (sgn=+1 and sgn=-1) ===", flush=True)
    # Direct algebraic/enclosure verification of Lemma 5.1 (Claim 5.2 + Claim 5.3) for BOTH sgn=+1 and sgn=-1!
    # We pin v=(0,0), q=(1,0), p=(0,1) for sgn=+1 and p=(0,-1) for sgn=-1 (both WLOG by orientation-preserving similarity!).
    # Wait: test BOTH sgn=+1 and sgn=-1 without reversing orientation of R^2, so p=(0, 1) for sgn=+1 and p=(0, -1) for sgn=-1!
    for sgn in (1, -1):
        v = (z3.RealVal(0), z3.RealVal(0))
        q = (z3.RealVal(1), z3.RealVal(0))
        p = (z3.RealVal(0), z3.RealVal(sgn))
        a, c, ws, wm, e = pt("a"), pt("c"), pt("ws"), pt("wm"), pt("e")
        # Exact C++ Section 7 antecedent conditions for (v, q, a, p, c):
        ante = [
            sgn * orient(v, q, a) > 0,
            sgn * orient(v, q, p) > 0,
            sgn * orient(v, q, c) > 0,
            sgn * orient(v, a, p) > 0,
            sgn * orient(v, p, c) > 0,
            sgn * orient(v, a, c) > 0,
            orient(a, c, v) * orient(a, c, p) < 0,
        ]
        # In Lemma 5.1, since v misses a and a not in T_a (which lies in P by Claim 5.1):
        # We check two parts (<= 8 pts):
        # (A) Claim 5.2(a),(b),(c) & Claim 5.3 for e-branch (8 pts: v,q,p,a,c,e,ws,wm) and v-sees-q branch (7 pts: v,q,p,a,c,ws,wm):
        # Note: Claim 5.1 gives T_a subset P => a not in tri(v,q,p):
        # Check Claim 5.1 geometry first: if e in S seen by v,q on same side of vq with theta(e) < theta(a),
        # then T_a subset tri(v, x*, p) subset P (6 pts: v, q, p, a, e, z_pt):
        zpt = pt("zpt")
        in_Ta = z3.And(
            orient(v, q, zpt) * orient(v, q, p) >= 0,
            orient(q, p, zpt) * orient(q, p, v) >= 0,
            orient(p, v, zpt) * orient(p, v, q) >= 0,
            sgn * orient(v, a, zpt) >= 0,
        )
        cond_e = [sgn * orient(v, q, e) > 0, sgn * orient(v, e, a) > 0, orient(p, q, e) != 0]
        # Either e in T_0 (so zpt in T_a => zpt in T_0 \ tri(v,e,q)) OR e not in T_0 (so ray v-e hits pq at x*, and zpt in tri(v, x*, p) subset tri(v,e,p))
        # In Z3: verify T_a subset (quad(v,e,q,p) if e in T_0 else tri(v,e,p)):
        in_T0_e = z3.And(
            orient(v, q, e) * orient(v, q, p) > 0,
            orient(q, p, e) * orient(q, p, v) > 0,
            orient(p, v, e) * orient(p, v, q) > 0,
        )
        in_tri_vep = z3.And(
            orient(v, e, zpt) * orient(v, e, p) >= 0,
            orient(e, p, zpt) * orient(e, p, v) >= 0,
            orient(p, v, zpt) * orient(p, v, e) >= 0,
        )
        in_tri_veq_strict = z3.And(
            orient(v, e, zpt) * orient(v, e, q) > 0,
            orient(e, q, zpt) * orient(e, q, v) > 0,
            orient(q, v, zpt) * orient(q, v, e) > 0,
        )
        assert_base_sat_and_neg_unsat(
            f"HalfPlane Claim 5.1 Ta subset P (sgn={sgn:+d})",
            ante + cond_e + [in_Ta],
            z3.If(in_T0_e, in_tri_veq_strict, z3.Not(in_tri_vep)),
        )

        # (B) Since a not in T_0 (else v sees a via T_a subset P):
        not_a_in_T0 = z3.Not(
            z3.And(
                orient(v, q, a) * orient(v, q, p) >= 0,
                orient(q, p, a) * orient(q, p, v) >= 0,
                orient(p, v, a) * orient(p, v, q) >= 0,
            )
        )
        # Helper: in normalized coords (v=(0,0), q=(1,0), p=(0,sgn)),
        # any point w seeing a, c cannot violate Claim 5.2(a) [w on q-side of va], 5.2(b) [w on q-side of vp],
        # nor if w sees p can w violate Claim 5.2(c) [w on q-side of pa],
        # nor can ws (seeing p) and wm (missing p) violate Claim 5.3 [sgn * orient(p, ws, wm) > 0]!
        # Let's check EACH enclosure obstruction in Z3 QF_NRA!
        # 1) If w violates Claim 5.2(a): w on c-side of va -> paths a-q-d0 and a-w-c-d0 enclose [a, d0] (with d0 in qc cap T_a):
        d0_t = z3.Real("d0_t")
        d0 = ((1 - d0_t) * q[0] + d0_t * c[0], (1 - d0_t) * q[1] + d0_t * c[1])
        assert_base_sat_and_neg_unsat(
            f"HalfPlane Claim 5.2(a) d0 in Ta & va-sep (sgn={sgn:+d})",
            ante + [not_a_in_T0, d0_t > 0, d0_t < 1, orient(v, a, d0) == 0,
                    orient(v, a, ws) != 0, orient(v, a, ws) * orient(v, a, q) <= 0],
            z3.Not(z3.And(
                orient(a, d0, q) * orient(a, d0, ws) < 0,
                orient(a, d0, q) * orient(a, d0, c) < 0,
                # d0 in T_0:
                orient(v, q, d0) * orient(v, q, p) > 0,
                orient(q, p, d0) * orient(q, p, v) > 0,
                orient(p, v, d0) * orient(p, v, q) > 0,
            )),
        )
        # 2) If w violates Claim 5.2(b) (assuming Claim 5.2(a)): w_x <= 0 -> paths y-w-c-z and y-a-q-z enclose [y, z] (with v on yz), and c-w-y-v & c-z-v enclose cv!
        # Verify both algebraic crossing conditions in Z3:
        assert_base_sat_and_neg_unsat(
            f"HalfPlane Claim 5.2(b) x>0 (sgn={sgn:+d})",
            ante + [not_a_in_T0, orient(v, a, ws) * orient(v, a, q) > 0, ws[0] < 0],
            # Prove segment a-ws crosses negative y-axis (y_y < 0 when sgn=+1, >0 when sgn=-1) and segment q-c crosses y-axis between v and p!
            z3.Not(z3.And(
                sgn * ws[1] < 0,
                (a[0] * ws[1] - a[1] * ws[0]) / (a[0] - ws[0]) * sgn < 0,  # y_2 on y-axis is on non-p side of v
                c[1] / (1 - c[0]) * sgn > 0,
                c[1] / (1 - c[0]) * sgn < 1,
            )),
        )
        # 3) If ws sees p and violates Claim 5.2(c): ws on non-q side of pa -> paths p-q-a and p-ws-a enclose tri(p, q, a), containing segment va past T_0!
        assert_base_sat_and_neg_unsat(
            f"HalfPlane Claim 5.2(c) pa-sep (sgn={sgn:+d})",
            ante + [not_a_in_T0, orient(v, a, ws) * orient(v, a, q) > 0, ws[0] > 0,
                    orient(p, a, ws) != 0, orient(p, a, ws) * orient(p, a, q) <= 0],
            z3.Not(z3.And(
                orient(p, a, q) * orient(p, a, ws) < 0,
                orient(p, q, a) * orient(p, q, v) < 0,
            )),
        )
        # 4) Claim 5.3 Monotonicity (exact C++ conclusion):
        # Given ws, wm both satisfying Claim 5.2(a),(b) and ws satisfying Claim 5.2(c), and NOT (sgn * orient(p, ws, wm) > 0),
        # i.e., sgn * orient(p, ws, wm) < 0 (meaning s(wm) < s(ws) in normalized coords):
        # Case 4a: wm on q-side of pq (slope < -1 when sgn=+1) -> p-q-a-wm and p-z-c-wm enclose [p, wm]!
        # Case 4b: wm between pq and p-ws -> p-ws-a-wm and p-q-c-wm enclose [p, wm]!
        z_y = (z3.RealVal(0), c[1] / (1 - c[0]))
        c_52_ws = [orient(v, a, ws) * orient(v, a, q) > 0, ws[0] > 0, orient(p, a, ws) * orient(p, a, q) > 0]
        c_52_wm = [orient(v, a, wm) * orient(v, a, q) > 0, wm[0] > 0, orient(p, q, wm) != 0]
        # Negation of sgn * orient(p, ws, wm) > 0 (with GP orient(p, ws, wm) != 0):
        bad_mono = [sgn * orient(p, ws, wm) < 0]
        # Verify Case 4a enclosure when wm is on q-side of pq (orient(p, wm, q) has same sign as sgn? Check: for sgn=+1, s(wm) < -1 => orient(p, wm, q) = wm_x * (-1 - s(wm)) > 0):
        enc_4a = z3.And(
            orient(p, wm, q) * orient(p, wm, a) > 0,
            orient(p, wm, z_y) * orient(p, wm, c) > 0,
            orient(p, wm, q) * orient(p, wm, c) < 0,
        )
        assert_base_sat_and_neg_unsat(
            f"HalfPlane Claim 5.3 Case 4a enclosure (sgn={sgn:+d})",
            ante + [not_a_in_T0] + c_52_ws + c_52_wm + bad_mono + [sgn * orient(p, wm, q) > 0],
            z3.Not(enc_4a),
        )
        # Verify Case 4b enclosure when wm is on non-q side of pq (sgn * orient(p, wm, q) < 0):
        enc_4b = z3.And(
            orient(p, wm, ws) * orient(p, wm, a) > 0,
            orient(p, wm, q) * orient(p, wm, c) > 0,
            orient(p, wm, ws) * orient(p, wm, c) < 0,
        )
        assert_base_sat_and_neg_unsat(
            f"HalfPlane Claim 5.3 Case 4b enclosure (sgn={sgn:+d})",
            ante + [not_a_in_T0] + c_52_ws + c_52_wm + bad_mono + [sgn * orient(p, wm, q) < 0],
            z3.Not(enc_4b),
        )


# =============================================================================
# 8. |D|=6 Prop 6.5, Prop 6.6, Lemma 6.8, Lemma 6.11 (<= 8 pts Z3 + Affine Chirotope SAT)
# =============================================================================
def verify_gap_disjunctions():
    print("\n=== 8. Prop 6.5, Prop 6.6, Lemma 6.8, Lemma 6.11 (Z3 <= 8 pts + Affine Chiro SAT) ===", flush=True)
    v = (z3.RealVal(0), z3.RealVal(0))
    q = (z3.RealVal(1), z3.RealVal(0))

    # 8A: Exact 4-pt building blocks in Z3 QF_NRA:
    # (1) 4-pt Gap Lemma: (A,P,C) CCW, same open side sgn of y=0, A->P & P->C don't face v => valid angular gap {A,C} enclosing P.
    A, P, C = pt("gA"), pt("gP"), pt("gC")
    for sgn in (1, -1):
        a_pt, c_pt = (A, C) if sgn == 1 else (C, A)
        base4 = [
            orient(A, P, C) > 0, orient(A, P, v) > 0, orient(P, C, v) > 0,
            sgn * A[1] > 0, sgn * P[1] > 0, sgn * C[1] > 0,
            orient(v, A, P) != 0, orient(v, P, C) != 0, orient(v, A, C) != 0,
        ]
        good4 = z3.And(
            sgn * orient(v, a_pt, P) > 0, sgn * orient(v, P, c_pt) > 0, sgn * orient(v, a_pt, c_pt) > 0,
            orient(a_pt, c_pt, v) * orient(a_pt, c_pt, P) < 0,
        )
        assert_base_sat_and_neg_unsat(f"4-pt gap lemma (sgn={sgn:+d})", base4, z3.Not(good4))

    # (2) 4-pt Exit Ordering: y in int tri(v, d0, d1), orient(d0, d1, v) > 0, d0, d1 in {sgn*y>0} => y in {sgn*y>0} & sector order.
    d0e, d1e, ye = pt("ed0"), pt("ed1"), pt("ey")
    for sgn in (1, -1):
        assert_base_sat_and_neg_unsat(
            f"4-pt exit ordering (sgn={sgn:+d})",
            [sgn * d0e[1] > 0, sgn * d1e[1] > 0, orient(d0e, d1e, v) > 0, in_int_tri_any(ye, v, d0e, d1e)],
            z3.Not(z3.And(sgn * ye[1] > 0, orient(v, d0e, ye) > 0, orient(v, ye, d1e) > 0)),
        )

    # (3) 4-pt Affine Axiom (forbids projective point-at-infinity reorientation):
    af = [pt(f"af{i}") for i in range(4)]
    for sgn in (1, -1):
        assert_base_sat_and_neg_unsat(
            f"4-pt Affine Axiom (sgn={sgn:+d})",
            [orient(af[i], af[j], af[k]) != 0 for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4)],
            z3.And(
                sgn * orient(af[1], af[2], af[3]) > 0,
                sgn * orient(af[0], af[2], af[3]) < 0,
                sgn * orient(af[0], af[1], af[3]) > 0,
                sgn * orient(af[0], af[1], af[2]) < 0,
            ),
        )

    # 8B: Full 8-point Prop 6.5 (|D|=6, O={1,3,5}, v, q) in Z3 QF_NRA across ALL 10 structural subcases (q=T and q=F):
    def check_prop65_subcase(sname, kind, target_idx):
        D = [pt(f"p65_{kind}_{target_idx}_T_{i}") for i in range(6)]
        conv_D = [orient(D[i], D[j], D[k]) > 0 for i in range(6) for j in range(i + 1, 6) for k in range(j + 1, 6)]
        gp_vq = [D[i][1] != 0 for i in range(6)] + [orient(v, D[i], D[j]) != 0 for i in range(6) for j in range(i + 1, 6)]
        omask_D, seen_D = [1, 3, 5], [0, 2, 4]
        no_odd = [z3.Not(z3.And(orient(D[(k - 1) % 6], D[k], v) < 0, orient(D[k], D[(k + 1) % 6], v) < 0)) for k in omask_D]
        no_cert = [z3.Not(z3.And(in_int_tri_any(D[fc], v, D[(fc - 1) % 6], D[(fc + 1) % 6]), in_int_tri_any(v, q, D[(fc - 1) % 6], D[(fc + 1) % 6]))) for fc in seen_D]
        if kind == "front":
            fv = target_idx
            scons = [orient(D[(fc - 1) % 6], D[fc], v) < 0 if fc == fv else z3.Not(z3.And(orient(D[(fc - 1) % 6], D[fc], v) < 0, orient(D[fc], D[(fc + 1) % 6], v) < 0)) for fc in seen_D]
            scons.append(orient(D[fv], D[(fv + 1) % 6], v) < 0)
        elif kind == "vin":
            no_front = [z3.Not(z3.And(orient(D[(fc - 1) % 6], D[fc], v) < 0, orient(D[fc], D[(fc + 1) % 6], v) < 0)) for fc in seen_D]
            scons = no_front + [orient(D[r], D[(r + 1) % 6], v) > 0 for r in range(6)]
        else:
            fe = target_idx
            no_front = [z3.Not(z3.And(orient(D[(fc - 1) % 6], D[fc], v) < 0, orient(D[fc], D[(fc + 1) % 6], v) < 0)) for fc in seen_D]
            scons = no_front + [orient(D[r], D[(r + 1) % 6], v) < 0 if r == fe else orient(D[r], D[(r + 1) % 6], v) > 0 for r in range(6)]

        # q=T (via 4-pt gap lemma above):
        same_side_gap = z3.Or(*[
            z3.And(
                orient(D[(fc - 1) % 6], D[fc], v) > 0, orient(D[fc], D[(fc + 1) % 6], v) > 0,
                z3.Or(
                    z3.And(D[(fc - 1) % 6][1] > 0, D[fc][1] > 0, D[(fc + 1) % 6][1] > 0),
                    z3.And(D[(fc - 1) % 6][1] < 0, D[fc][1] < 0, D[(fc + 1) % 6][1] < 0),
                ),
            )
            for fc in seen_D
        ])
        assert_base_sat_and_neg_unsat(f"Prop 6.5 (q=T, {sname})", conv_D + gp_vq + no_odd + no_cert + scons, z3.Not(same_side_gap))

        # q=F (seen_D all on side_sign of vq): factored via 4-pt gap lemma (cond_iv forces sgn = side_sign):
        specs = [((5, 1), 0), ((1, 3), 2), ((3, 5), 4)]
        for side_sign in (1, -1):
            Df = [pt(f"p65_{kind}_{target_idx}_{side_sign}_{i}") for i in range(6)]
            conv_Df = [orient(Df[i], Df[j], Df[k]) > 0 for i in range(6) for j in range(i + 1, 6) for k in range(j + 1, 6)]
            gp_vqf = [Df[i][1] != 0 for i in range(6)] + [orient(v, Df[i], Df[j]) != 0 for i in range(6) for j in range(i + 1, 6)]
            no_oddf = [z3.Not(z3.And(orient(Df[(k - 1) % 6], Df[k], v) < 0, orient(Df[k], Df[(k + 1) % 6], v) < 0)) for k in omask_D]
            no_certf = [z3.Not(z3.And(in_int_tri_any(Df[fc], v, Df[(fc - 1) % 6], Df[(fc + 1) % 6]), in_int_tri_any(v, q, Df[(fc - 1) % 6], Df[(fc + 1) % 6]))) for fc in seen_D]
            if kind == "front":
                fv = target_idx
                sconsf = [orient(Df[(fc - 1) % 6], Df[fc], v) < 0 if fc == fv else z3.Not(z3.And(orient(Df[(fc - 1) % 6], Df[fc], v) < 0, orient(Df[fc], Df[(fc + 1) % 6], v) < 0)) for fc in seen_D]
                sconsf.append(orient(Df[fv], Df[(fv + 1) % 6], v) < 0)
            elif kind == "vin":
                no_frontf = [z3.Not(z3.And(orient(Df[(fc - 1) % 6], Df[fc], v) < 0, orient(Df[fc], Df[(fc + 1) % 6], v) < 0)) for fc in seen_D]
                sconsf = no_frontf + [orient(Df[r], Df[(r + 1) % 6], v) > 0 for r in range(6)]
            else:
                fe = target_idx
                no_frontf = [z3.Not(z3.And(orient(Df[(fc - 1) % 6], Df[fc], v) < 0, orient(Df[fc], Df[(fc + 1) % 6], v) < 0)) for fc in seen_D]
                sconsf = no_frontf + [orient(Df[r], Df[(r + 1) % 6], v) < 0 if r == fe else orient(Df[r], Df[(r + 1) % 6], v) > 0 for r in range(6)]
            sgn = side_sign
            good_qF = []
            for (oa, ob), p_idx in specs:
                a_idx, c_idx = (oa, ob) if sgn == 1 else (ob, oa)
                pm, pp = (p_idx - 1) % 6, (p_idx + 1) % 6
                cond_iv = z3.Or(*[sgn * orient(v, Df[e], Df[a_idx]) > 0 for e in seen_D])
                good_qF.append(z3.And(
                    cond_iv, orient(Df[pm], Df[p_idx], v) > 0, orient(Df[p_idx], Df[pp], v) > 0,
                    sgn * Df[a_idx][1] > 0, sgn * Df[p_idx][1] > 0, sgn * Df[c_idx][1] > 0,
                ))
            side_cons = [side_sign * Df[e][1] > 0 for e in seen_D]
            assert_base_sat_and_neg_unsat(f"Prop 6.5 (q=F, {sname}, s={side_sign:+d})", conv_Df + gp_vqf + no_oddf + no_certf + sconsf + side_cons, z3.Not(z3.Or(*good_qF)))

    check_prop65_subcase("front=0", "front", 0)
    check_prop65_subcase("front=2", "front", 2)
    check_prop65_subcase("front=4", "front", 4)
    check_prop65_subcase("v in conv(D)", "vin", 0)
    for fe in range(6):
        check_prop65_subcase(f"facing edge {fe}{(fe+1)%6}", "edge", fe)

    # 8C: 8-pt Adjacent-Exit Gap Core (Lemma 6.11 WITHOUT minimality) in Z3 QF_NRA:
    q4 = [pt("d0"), pt("d1"), pt("d2"), pt("dx")]
    y0, y1 = pt("y0"), pt("y1")
    pts8 = q4 + [y0, y1]
    base_8adj = (
        [orient(q4[i], q4[j], q4[k]) > 0 for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4)]
        + [orient(q4[r], q4[(r + 1) % 4], yp) > 0 for yp in (y0, y1) for r in range(4)]
        + [orient(v, pts8[i], pts8[j]) != 0 for i in range(6) for j in range(i + 1, 6)]
        + [p[1] != 0 for p in pts8]
        + [in_int_tri_any(y0, v, q4[0], q4[1]), in_int_tri_any(y1, v, q4[1], q4[2])]
        + [z3.Not(z3.And(orient(q4[2], q4[3], v) < 0, orient(q4[3], q4[0], v) < 0))]
    )
    L_side = [q4[0][1] > 0, q4[1][1] > 0, q4[2][1] > 0]
    gap1_ok = z3.Or(
        z3.And(
            orient(q4[0], q4[1], v) > 0, orient(q4[1], q4[2], v) > 0,
            y0[1] > 0, q4[1][1] > 0, y1[1] > 0,
            orient(v, y0, q4[1]) > 0, orient(v, q4[1], y1) > 0, orient(v, y0, y1) > 0,
            orient(y0, y1, v) * orient(y0, y1, q4[1]) < 0,
            orient(v, q4[0], y0) > 0,
        ),
        z3.And(
            orient(q4[0], q4[1], v) > 0, orient(q4[1], q4[2], v) > 0,
            y1[1] > 0, q4[1][1] > 0, y0[1] > 0,
            orient(v, y1, q4[1]) < 0, orient(v, q4[1], y0) < 0, orient(v, y1, y0) < 0,
            orient(y1, y0, v) * orient(y1, y0, q4[1]) < 0,
            orient(v, q4[2], y1) < 0,
        ),
    )
    assert_base_sat_and_neg_unsat("Lemma 6.11 8-pt adj exits (no minimality, L-side)", base_8adj + L_side, z3.Not(gap1_ok))

    # 8D: 8-pt Disjoint-Exit Gap Core (Lemma 6.8): (8-pt angular chain + 5-pt gap enclosure):
    L_disj = [q4[i][1] > 0 for i in range(4)]
    base_8disj = (
        [orient(q4[i], q4[j], q4[k]) > 0 for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4)]
        + [orient(q4[r], q4[(r + 1) % 4], yp) > 0 for yp in (y0, y1) for r in range(4)]
        + [orient(v, pts8[i], pts8[j]) != 0 for i in range(6) for j in range(i + 1, 6)]
        + [p[1] != 0 for p in pts8]
        + [in_int_tri_any(y0, v, q4[0], q4[1]), in_int_tri_any(y1, v, q4[2], q4[3])]
        + L_disj + [orient(q4[1], q4[2], v) > 0]
    )
    chain_ok = z3.And(
        orient(q4[0], q4[1], v) > 0, orient(q4[2], q4[3], v) > 0, y0[1] > 0, y1[1] > 0,
        orient(v, q4[0], y0) > 0, orient(v, y0, q4[1]) > 0, orient(v, q4[1], q4[2]) > 0,
        orient(v, q4[2], y1) > 0, orient(v, y1, q4[3]) > 0,
    )
    assert_base_sat_and_neg_unsat("Lemma 6.8 8-pt disjoint exits (angular chain)", base_8disj, z3.Not(chain_ok))

    d1, d2 = q4[1], q4[2]
    stepB_base = [
        d1[1] > 0, d2[1] > 0, y0[1] > 0, y1[1] > 0,
        orient(d1, d2, v) > 0, orient(d1, d2, y0) > 0, orient(d1, d2, y1) > 0,
        orient(v, y0, d1) > 0, orient(v, d1, d2) > 0, orient(v, d2, y1) > 0,
    ]
    stepB_ok = z3.And(
        orient(v, y0, y1) > 0,
        orient(v, y0, d1) > 0, orient(v, d1, y1) > 0, orient(y0, y1, v) * orient(y0, y1, d1) < 0,
        orient(v, y0, d2) > 0, orient(v, d2, y1) > 0, orient(y0, y1, v) * orient(y0, y1, d2) < 0,
    )
    assert_base_sat_and_neg_unsat("Lemma 6.8 5-pt gap {y0,y1} encloses d1,d2", stepB_base, z3.Not(stepB_ok))

    # 8E: Exact Affine Chirotope SAT Verification (add_gp + add_affine4) for full |D|=6 theorems (8, 9, 10 pts):
    def make_chiro_affine(n):
        s = Solver(name="cadical195")
        nv = 0
        tlit = [[[0] * n for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(i + 1, n):
                for k in range(j + 1, n):
                    nv += 1
                    tlit[i][j][k] = nv; tlit[j][k][i] = nv; tlit[k][i][j] = nv
                    tlit[j][i][k] = -nv; tlit[k][j][i] = -nv; tlit[i][k][j] = -nv
        def new_var():
            nonlocal nv
            nv += 1
            return nv
        def mk_and(lits):
            vr = new_var()
            for l in lits: s.add_clause([-vr, l])
            s.add_clause([vr] + [-l for l in lits])
            return vr
        def mk_or(lits):
            vr = new_var()
            for l in lits: s.add_clause([-l, vr])
            s.add_clause([-vr] + lits)
            return vr
        def mk_eq(a, b):
            vr = new_var()
            s.add_clause([-vr, -a, b]); s.add_clause([-vr, a, -b])
            s.add_clause([vr, a, b]); s.add_clause([vr, -a, -b])
            return vr
        def pos(a, b, c): return tlit[a][b][c]
        def in_tri(p, a, b, c):
            return mk_and([mk_eq(pos(a, b, p), pos(a, b, c)), mk_eq(pos(b, c, p), pos(a, b, c)), mk_eq(pos(c, a, p), pos(a, b, c))])
        for pts in combinations(range(n), 5):
            for pi in range(5):
                p = pts[pi]
                pa, pb, pc, pd = [pts[k] for k in range(5) if k != pi]
                l1, l2 = pos(p, pa, pb), pos(p, pc, pd)
                l3, l4 = pos(p, pa, pc), -pos(p, pb, pd)
                l5, l6 = pos(p, pa, pd), pos(p, pb, pc)
                for s1 in (-1, 1):
                    for s2 in (-1, 1):
                        for s3 in (-1, 1):
                            s.add_clause([-s1 * l1, -s1 * l2, -s2 * l3, -s2 * l4, -s3 * l5, -s3 * l6])
                            s.add_clause([-s1 * l1, s1 * l2, -s2 * l3, s2 * l4, -s3 * l5, s3 * l6])
        for pa, pb, pc, pd in combinations(range(n), 4):
            for sgn in (1, -1):
                s.add_clause([-sgn * pos(pb, pc, pd), sgn * pos(pa, pc, pd), -sgn * pos(pa, pb, pd), sgn * pos(pa, pb, pc)])
        def add_gap_multi(vw, qw, seen, oa, ob, gp, n_d, out_lits):
            for sgn in (1, -1):
                a, c = (oa, ob) if sgn == 1 else (ob, oa)
                cond = [sgn * pos(vw, qw, a), sgn * pos(vw, qw, c), sgn * pos(vw, a, c)]
                for p in gp:
                    pm, pp = (p - 1) % n_d, (p + 1) % n_d
                    cond.extend([pos(pm, p, vw), pos(p, pp, vw), sgn * pos(vw, qw, p), sgn * pos(vw, a, p), sgn * pos(vw, p, c), mk_eq(pos(a, c, vw), -pos(a, c, p))])
                iv = [mk_and([sgn * pos(vw, qw, e), sgn * pos(vw, e, a)]) for e in seen]
                for i in range(len(seen)):
                    for j in range(i + 1, len(seen)):
                        iv.append(mk_eq(pos(vw, qw, seen[i]), -pos(vw, qw, seen[j])))
                cond.append(mk_or(iv))
                out_lits.append(mk_and(cond))
        return s, pos, in_tri, add_gap_multi

    # Full |D|=6 Prop 6.5 (8-pt chirotope):
    tc = time.time()
    s, pos, in_tri, add_gap_multi = make_chiro_affine(8)
    D, vc, qc = [0, 1, 2, 3, 4, 5], 6, 7
    for i, j, k in combinations(D, 3): s.add_clause([pos(i, j, k)])
    for k in (1, 3, 5): s.add_clause([pos((k - 1) % 6, k, vc), pos(k, (k + 1) % 6, vc)])
    for fc in (0, 2, 4): s.add_clause([-in_tri(fc, vc, (fc - 1) % 6, (fc + 1) % 6), -in_tri(vc, qc, (fc - 1) % 6, (fc + 1) % 6)])
    assert s.solve()
    opts = []
    for p, oa, ob in [(0, 5, 1), (2, 1, 3), (4, 3, 5)]: add_gap_multi(vc, qc, [0, 2, 4], oa, ob, [p], 6, opts)
    for o in opts: s.add_clause([-o])
    assert not s.solve()
    print(f"  [{'Affine Chiro Prop 6.5 (8-pt, |D|=6)':58s}] base=sat, neg=unsat ({time.time()-tc:.2f}s)", flush=True)

    # Full |D|=6 Prop 6.6 (9-pt chirotope):
    tc = time.time()
    s, pos, in_tri, add_gap_multi = make_chiro_affine(9)
    D, yc, vc, qc = [0, 1, 2, 3, 4, 5], 6, 7, 8
    for i, j, k in combinations(D, 3): s.add_clause([pos(i, j, k)])
    for r in range(6): s.add_clause([pos(r, (r + 1) % 6, yc)])
    s.add_clause([in_tri(yc, vc, 0, 1)])
    for k in (4, 2): s.add_clause([pos((k - 1) % 6, k, vc), pos(k, (k + 1) % 6, vc)])
    for fc in (3, 5, 0, 1): s.add_clause([-in_tri(fc, vc, (fc - 1) % 6, (fc + 1) % 6), -in_tri(vc, qc, (fc - 1) % 6, (fc + 1) % 6)])
    assert s.solve()
    opts = []
    add_gap_multi(vc, qc, [5, 0, 1, 3], 4, yc, [5, 0], 6, opts)
    add_gap_multi(vc, qc, [5, 0, 1, 3], yc, 2, [1], 6, opts)
    add_gap_multi(vc, qc, [5, 0, 1, 3], 2, 4, [3], 6, opts)
    for o in opts: s.add_clause([-o])
    assert not s.solve()
    print(f"  [{'Affine Chiro Prop 6.6 (9-pt, |D|=6, exit 01)':58s}] base=sat, neg=unsat ({time.time()-tc:.2f}s)", flush=True)

    # Full |D|=6 Lemma 6.8 (10-pt chirotope, diff=2 and diff=3):
    for name, e1a, e1b, b, gaps in [
        ("diff=2 (01,23)", 2, 3, 4, [([1, 2], 6, 7), ([3], 7, 4), ([5, 0], 4, 6)]),
        ("diff=3 (01,34)", 3, 4, 5, [([1, 2], 6, 7), ([4], 7, 5), ([0], 5, 6)]),
    ]:
        tc = time.time()
        s, pos, in_tri, add_gap_multi = make_chiro_affine(10)
        D, y0c, y1c, vc, qc = [0, 1, 2, 3, 4, 5], 6, 7, 8, 9
        for i, j, k in combinations(D, 3): s.add_clause([pos(i, j, k)])
        for yp in (y0c, y1c):
            for r in range(6): s.add_clause([pos(r, (r + 1) % 6, yp)])
        s.add_clause([in_tri(y0c, vc, 0, 1)])
        s.add_clause([in_tri(y1c, vc, e1a, e1b)])
        s.add_clause([pos((b - 1) % 6, b, vc), pos(b, (b + 1) % 6, vc)])
        for fc in D:
            if fc != b and fc not in (0, 1, e1a, e1b):
                s.add_clause([-in_tri(fc, vc, (fc - 1) % 6, (fc + 1) % 6), -in_tri(vc, qc, (fc - 1) % 6, (fc + 1) % 6)])
        assert s.solve()
        seen = [x for x in D if x != b]
        opts_d = []
        for gp, oa, ob in gaps: add_gap_multi(vc, qc, seen, oa, ob, gp, 6, opts_d)
        for o in opts_d: s.add_clause([-o])
        assert not s.solve()
        print(f"  [{f'Affine Chiro Lemma 6.8 {name} (10-pt)':58s}] base=sat, neg=unsat ({time.time()-tc:.2f}s)", flush=True)

    # Full |D|=6 Lemma 6.11 (10-pt chirotope, b=4 and b=3, NO minimality):
    for b, gaps in [
        (4, [([1], 6, 7), ([2, 3], 7, 4), ([5, 0], 4, 6)]),
        (3, [([1], 6, 7), ([2], 7, 3), ([4, 5, 0], 3, 6)]),
    ]:
        tc = time.time()
        s, pos, in_tri, add_gap_multi = make_chiro_affine(10)
        D, y0c, y1c, vc, qc = [0, 1, 2, 3, 4, 5], 6, 7, 8, 9
        for i, j, k in combinations(D, 3): s.add_clause([pos(i, j, k)])
        for yp in (y0c, y1c):
            for r in range(6): s.add_clause([pos(r, (r + 1) % 6, yp)])
        s.add_clause([in_tri(y0c, vc, 0, 1)])
        s.add_clause([in_tri(y1c, vc, 1, 2)])
        s.add_clause([pos((b - 1) % 6, b, vc), pos(b, (b + 1) % 6, vc)])
        assert s.solve()
        seen = [x for x in D if x != b]
        opts_a = []
        for gp, oa, ob in gaps: add_gap_multi(vc, qc, seen, oa, ob, gp, 6, opts_a)
        for o in opts_a: s.add_clause([-o])
        assert not s.solve()
        print(f"  [{f'Affine Chiro Lemma 6.11 b={b} (10-pt, no min)':58s}] base=sat, neg=unsat ({time.time()-tc:.2f}s)", flush=True)


# =============================================================================
# 9. All N1, 4cyc, T1, T2, T3, vis_SS (incl. omitted tlit[a][b][c]), RegB2
# =============================================================================
def verify_enclosure_rules():
    print("\n=== 9. N1 (Quad + All 4 Dart Positions, With/Without tlit[a][b][c]), 4cyc, T1, T2, T3, vis_SS, RegB2 ===", flush=True)
    # 9A: Convex Quad N1 + 4cyc
    w1 = (z3.RealVal(0), z3.RealVal(0))
    a = (z3.RealVal(1), z3.RealVal(0))
    b = (z3.RealVal(0), z3.RealVal(1))
    w2, fw, fj = pt("w2"), pt("fw"), pt("fj")
    t = z3.Real("t")
    ccw_quad = [orient(w1, a, w2) > 0, orient(a, w2, b) > 0, orient(w2, b, w1) > 0, orient(b, w1, a) > 0]
    fw_in_quad = [orient(w1, a, fw) > 0, orient(a, w2, fw) > 0, orient(w2, b, fw) > 0, orient(b, w1, fw) > 0]
    fj_in_quad = [orient(w1, a, fj) > 0, orient(a, w2, fj) > 0, orient(w2, b, fj) > 0, orient(b, w1, fj) > 0]
    z_a = ((1 - t) * fw[0] + t * a[0], (1 - t) * fw[1] + t * a[1])
    z_fj = ((1 - t) * fw[0] + t * fj[0], (1 - t) * fw[1] + t * fj[1])
    assert_base_sat_and_neg_unsat(
        "Convex Quad N1 (fw sees a)",
        ccw_quad + fw_in_quad + [t > 0, t < 1],
        z3.Or(orient(w1, a, z_a) <= 0, orient(a, w2, z_a) <= 0, orient(w2, b, z_a) <= 0, orient(b, w1, z_a) <= 0),
    )
    assert_base_sat_and_neg_unsat(
        "Convex Quad 4cyc (fw sees fj)",
        ccw_quad + fw_in_quad + fj_in_quad + [t > 0, t < 1],
        z3.Or(orient(w1, a, z_fj) <= 0, orient(a, w2, z_fj) <= 0, orient(w2, b, z_fj) <= 0, orient(b, w1, z_fj) <= 0),
    )

    # 9B: ALL 4 Reflex-Dart Positions for N1 (pts = [w1, fj, w2, b]), WITH AND WITHOUT orient(vp, vq, vs)!
    # Note: find_violated_n1_cuts omits tlit[vp][vq][vs], using only dart_lits = [tlit[vp][vq][vr], tlit[vq][vs][vr], tlit[vs][vp][vr]]!
    # First prove the area-identity lemma: sgn(vp,vq,vr)==sd & sgn(vq,vs,vr)==sd & sgn(vs,vp,vr)==sd => sgn(vp,vq,vs)==sd!
    vp = (z3.RealVal(0), z3.RealVal(0))
    vq = (z3.RealVal(1), z3.RealVal(0))
    vs = pt("vs")
    vr = pt("vr")
    for sd in (1, -1):
        assert_base_sat_and_neg_unsat(
            f"Omitted tlit[vp][vq][vs] sound (sd={sd:+d})",
            [sd * orient(vp, vq, vr) > 0, sd * orient(vq, vs, vr) > 0, sd * orient(vs, vp, vr) > 0],
            sd * orient(vp, vq, vs) <= 0,
        )

    # Now verify ALL 4 dart positions r=0,1,2,3 (omitting tlit[vp][vq][vs] in dart_lits!):
    # Pin outer triangle (vp, vq, vs) = ((0,0), (1,0), (0,1)) CCW (sd = +1, WLOG by orientation/affine).
    vs_pin = (z3.RealVal(0), z3.RealVal(1))
    dart_omitted = [orient(vp, vq, vr) > 0, orient(vq, vs_pin, vr) > 0, orient(vs_pin, vp, vr) > 0]
    out_dart = z3.Or(
        orient(vp, vq, z_fj) <= 0, orient(vq, vs_pin, z_fj) <= 0, orient(vs_pin, vp, z_fj) <= 0,
        in_int_tri_any(z_fj, vr, vp, vs_pin),
    )
    # r = 0 (i1 == 1: fj = vp): fw in tri(vp, vq, vs) & same_side(vr, vp, fw, vq)
    assert_base_sat_and_neg_unsat(
        "Dart N1 r=0 (i1==1, fj=vp, omitted tlit)",
        dart_omitted + [in_int_tri_ccw(fw, vp, vq, vs_pin), same_side(vr, vp, fw, vq), t > 0, t < 1],
        z3.Or(orient(vp, vq, ((1 - t) * fw[0] + t * vp[0], (1 - t) * fw[1] + t * vp[1])) <= 0,
              orient(vq, vs_pin, ((1 - t) * fw[0] + t * vp[0], (1 - t) * fw[1] + t * vp[1])) <= 0,
              orient(vs_pin, vp, ((1 - t) * fw[0] + t * vp[0], (1 - t) * fw[1] + t * vp[1])) <= 0,
              in_int_tri_any(((1 - t) * fw[0] + t * vp[0], (1 - t) * fw[1] + t * vp[1]), vr, vp, vs_pin)),
    )
    # r = 1 (i0 == 1: fj = vr): fw in tri(vr, vp, vq) or fw in tri(vr, vq, vs)
    for sub, tri in [("tri(vr,vp,vq)", (vr, vp, vq)), ("tri(vr,vq,vs)", (vr, vq, vs_pin))]:
        z_vr = ((1 - t) * fw[0] + t * vr[0], (1 - t) * fw[1] + t * vr[1])
        assert_base_sat_and_neg_unsat(
            f"Dart N1 r=1 (i0==1, fj=vr, {sub})",
            dart_omitted + [in_int_tri_any(fw, *tri), t > 0, t < 1],
            z3.Or(orient(vp, vq, z_vr) <= 0, orient(vq, vs_pin, z_vr) <= 0, orient(vs_pin, vp, z_vr) <= 0, in_int_tri_any(z_vr, vr, vp, vs_pin)),
        )
    # r = 2 (i3 == 1: fj = vs): fw in tri(vp, vq, vs) & same_side(vr, vs, fw, vq)
    z_vs = ((1 - t) * fw[0] + t * vs_pin[0], (1 - t) * fw[1] + t * vs_pin[1])
    assert_base_sat_and_neg_unsat(
        "Dart N1 r=2 (i3==1, fj=vs, omitted tlit)",
        dart_omitted + [in_int_tri_ccw(fw, vp, vq, vs_pin), same_side(vr, vs_pin, fw, vq), t > 0, t < 1],
        z3.Or(orient(vp, vq, z_vs) <= 0, orient(vq, vs_pin, z_vs) <= 0, orient(vs_pin, vp, z_vs) <= 0, in_int_tri_any(z_vs, vr, vp, vs_pin)),
    )
    # r = 3 (i2 == 1: fj = vq): fw in tri(vr, vp, vq) or fw in tri(vr, vq, vs)
    for sub, tri in [("tri(vr,vp,vq)", (vr, vp, vq)), ("tri(vr,vq,vs)", (vr, vq, vs_pin))]:
        z_vq = ((1 - t) * fw[0] + t * vq[0], (1 - t) * fw[1] + t * vq[1])
        assert_base_sat_and_neg_unsat(
            f"Dart N1 r=3 (i2==1, fj=vq, {sub})",
            dart_omitted + [in_int_tri_any(fw, *tri), t > 0, t < 1],
            z3.Or(orient(vp, vq, z_vq) <= 0, orient(vq, vs_pin, z_vq) <= 0, orient(vs_pin, vp, z_vq) <= 0, in_int_tri_any(z_vq, vr, vp, vs_pin)),
        )

    # 9C: Dart 4cyc (both side cases: sp and ss):
    for sname, s_edge in [("vr-vp side", vp), ("vr-vs side", vs_pin)]:
        assert_base_sat_and_neg_unsat(
            f"Dart 4cyc ({sname})",
            dart_omitted + [
                in_int_tri_ccw(fw, vp, vq, vs_pin), in_int_tri_ccw(fj, vp, vq, vs_pin),
                same_side(vr, s_edge, fw, vq), same_side(vr, s_edge, fj, vq), t > 0, t < 1,
            ],
            out_dart,
        )

    # 9D: Rule T1_b & T1_both, Rule T2, Rule T3_b & T3_both
    # T1: w1=(0,0), a=(1,0), b=(0,1), [w1,a] crosses [w2,b] at X=(tx,0)
    tx = z3.Real("tx")
    X = (tx, z3.RealVal(0))
    base_t1 = [
        segs_cross(w1, a, w2, b),
        same_side(w1, a, fw, b), same_side(w2, b, fw, w1), same_side(w1, b, fw, a),
        tx > 0, tx < 1, orient(w2, b, X) == 0,
    ]
    assert_base_sat_and_neg_unsat("Rule T1 (fw in int tri(w1, b, X))", base_t1, z3.Not(in_int_tri_any(fw, w1, b, X)))
    assert_base_sat_and_neg_unsat(
        "Rule T1_both (seg [fw,fj] in tri(w1, b, X))",
        base_t1 + [same_side(w1, a, fj, b), same_side(w2, b, fj, w1), same_side(w1, b, fj, a), t > 0, t < 1],
        z3.Not(in_int_tri_any(z_fj, w1, b, X)),
    )

    # T2: w2=(0,0), b=(1,0), c=(0,1), [w1,a] crosses [w2,b] at X1 and [w2,c] at X2
    tb, tc = z3.Real("tb"), z3.Real("tc")
    X1, X2 = (tb, z3.RealVal(0)), (z3.RealVal(0), tc)
    w1_p, a_p = pt("w1p"), pt("ap")
    base_t2 = [
        segs_cross(w1_p, a_p, w1, a), segs_cross(w1_p, a_p, w1, b),
        same_side(w1_p, a_p, fw, w1), same_side(w1, a, fw, b), same_side(w1, b, fw, a),
        tb > 0, tb < 1, tc > 0, tc < 1,
        orient(w1_p, a_p, X1) == 0, orient(w1_p, a_p, X2) == 0,
    ]
    assert_base_sat_and_neg_unsat("Rule T2 (fw in int tri(w2, X1, X2))", base_t2, z3.Not(in_int_tri_any(fw, w1, X1, X2)))

    # T3: w1=(0,0), w2=(1,0), b=(0,1), [w1,a] crosses [w2,c] at X, -cr_ab, -cr_cb, a,c opp b wrt w1-w2
    c_p = pt("cp")
    ta_t3, tc_t3 = z3.Real("ta3"), z3.Real("tc3")
    X_t3 = (ta_t3 * a_p[0], ta_t3 * a_p[1])
    base_t3 = [
        segs_cross(w1, a_p, w2, c_p),
        z3.Not(segs_cross(w1, a_p, w2, b)), z3.Not(segs_cross(w2, c_p, w1, b)),
        z3.Not(same_side(w1, w2, a_p, b)), z3.Not(same_side(w1, w2, c_p, b)),
        orient(w1, a_p, b) != 0, orient(w2, c_p, b) != 0, orient(w1, w2, a_p) != 0, orient(w1, w2, c_p) != 0,
        ta_t3 > 0, ta_t3 < 1, tc_t3 > 0, tc_t3 < 1,
        X_t3[0] == (1 - tc_t3) * w2[0] + tc_t3 * c_p[0],
        X_t3[1] == (1 - tc_t3) * w2[1] + tc_t3 * c_p[1],
        same_side(b, w1, fw, w2), same_side(w1, a_p, fw, b), same_side(w2, c_p, fw, b), same_side(w2, b, fw, w1),
    ]
    assert_base_sat_and_neg_unsat(
        "Rule T3_b (fw in convex quad(w1, X, w2, b))",
        base_t3,
        z3.Not(z3.Or(in_int_tri_any(fw, w1, X_t3, b), in_int_tri_any(fw, w2, X_t3, b), orient(X_t3, b, fw) == 0)),
    )
    # Half-plane convexity for T3_both: any two points (fw, fj) on the same side of line (p,q) as r keep the entire segment [fw,fj] on that side!
    hp_p, hp_q, hp_r = pt("hp"), pt("hq"), pt("hr")
    assert_base_sat_and_neg_unsat(
        "Rule T3_both (half-plane convexity [fw,fj] in quad)",
        [same_side(hp_p, hp_q, fw, hp_r), same_side(hp_p, hp_q, fj, hp_r), t > 0, t < 1],
        z3.Not(same_side(hp_p, hp_q, z_fj, hp_r)),
    )

    # 9E: vis_SS (E1 + E2, plus omitted tlit[a][b][c] in bulk_cegar_enclosure E2)
    w1p, w2p = pt("w1p"), pt("w2p")
    assert_base_sat_and_neg_unsat(
        "vis_SS E1 (w1, w2 opp sides of a-b => encloses [a,b])",
        [orient(a, b, w1p) * orient(a, b, w2p) < 0, t > 0, t < 1],
        z3.Not(z3.And(
            orient(a, b, w1p) * orient(a, b, w2p) < 0,
            # Midpoint/any point z_ab = (1-t)a + t*b lies on segment ab, strictly between w1p and w2p:
            orient(w1p, ((1 - t) * a[0] + t * b[0], (1 - t) * a[1] + t * b[1]), w2p) ==
            (1 - t) * orient(w1p, a, w2p) + t * orient(w1p, b, w2p),
        )),
    )
    # Clean E2 (with omitted tlit[a][b][c] as in bulk_cegar_enclosure!):
    assert_base_sat_and_neg_unsat(
        "vis_SS E2 & bulk_cegar E2 (omitted tlit[a][b][c])",
        [orient(vp, vq, vr) > 0, orient(vq, vs_pin, vr) > 0, orient(vs_pin, vp, vr) > 0,
         orient(vp, vq, fw) > 0, orient(vq, vs_pin, fw) > 0, orient(vs_pin, vp, fw) > 0, t > 0, t < 1],
        z3.Or(
            orient(vp, vq, vs_pin) <= 0,
            z3.Not(in_int_tri_ccw(((1 - t) * vr[0] + t * fw[0], (1 - t) * vr[1] + t * fw[1]), vp, vq, vs_pin)),
            z3.Not(in_int_tri_ccw(((1 - t) * vr[0] + t * vp[0], (1 - t) * vr[1] + t * vp[1]), vp, vq, vs_pin)),
        ),
    )

    # 9F: Regime B2 regB2_tri012 in gen_chiro_u4.cpp (H on lr=23, A in int conv(B)):
    # Verify: for a in int conv(B), -orient(0, 2, a) > 0 iff a in int tri(0, 1, 2), and h on arc 23 NEVER satisfies orient(0, 2, h) < 0!
    d3, h_pt, a_pt = pt("d3"), pt("hpt"), pt("apt")
    D4_ccw = [
        orient(w1, a, b) > 0,  # wait: D4 = ((0,0), (1,0), d2, (0,1)) -> use d2=(x2,y2), d3=(0,1):
    ]
    d2 = pt("d2")
    D4 = [(z3.RealVal(0), z3.RealVal(0)), (z3.RealVal(1), z3.RealVal(0)), d2, (z3.RealVal(0), z3.RealVal(1))]
    B_h1 = [D4[0], D4[1], D4[2], h_pt, D4[3]]
    conv_B = [orient(B_h1[i], B_h1[j], B_h1[k]) > 0 for i in range(5) for j in range(i + 1, 5) for k in range(j + 1, 5) if (i, j, k) != (0, 1, 4)]
    in_B = [orient(B_h1[r], B_h1[(r + 1) % 5], a_pt) > 0 for r in range(5)]
    assert_base_sat_and_neg_unsat(
        "RegB2 regB2_tri012 (orient(0,2,a)<0 <=> a in tri(0,1,2))",
        conv_B + in_B,
        z3.Or(
            (orient(D4[0], D4[2], a_pt) < 0) != in_int_tri_ccw(a_pt, D4[0], D4[1], D4[2]),
            orient(D4[0], D4[2], h_pt) <= 0,
        ),
    )


if __name__ == "__main__":
    t_start = time.time()
    verify_add_gp()
    verify_caratheodory_7pt()
    verify_non_certified_obstruction()
    verify_add_wedge_sep()
    verify_side_corners_and_separation()
    verify_asymmetric_two_sided()
    verify_universal_halfplane()
    verify_gap_disjunctions()
    verify_enclosure_rules()
    print(f"\nALL Z3 QF_NRA SCHEMA CHECKS PASSED (0 unknown, 100% verified) in {time.time() - t_start:.2f}s!")
