import Mathlib
import RootTask.Defs
import RootTask.Sec9Solution
import RootTask.CaseBSolution
import RootTask.CaseASolution
import RootTask.UnconditionalBridge
import RootTask.Sec7Combination
import RootTask.Sec8And11Master
import RootTask.All96Leaves
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.SixWedges
import RootTask.Sec5HalfPlane
import RootTask.Sec6Targets
import RootTask.Sec11VisibilityBridge
import RootTask.Sec8And11PolygonBridge
import RootTask.Sec2To5Bridge

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Unified End-to-End Lean 4 Verification of `upper_9.tex`
## "The Visibility VC-Dimension of Simple Polygons is at Most Nine"

Every theorem below is proved unconditionally in `ℝ × ℝ` with zero `sorry`s,
zero custom `axiom`s, and zero `native_decide` (`[propext, Classical.choice, Quot.sound]` only).
-/

/-- **Theorem 9.1(1)** (`upper_9.tex` Theorem `v-epigraph`(1), Section 9):
    No five V-functions `f_i(x) = max(a_i x + b_i, c_i x + d_i)` in `ℝ²` realize all `32` strict bitmasks. -/
theorem thm_9_1_part1_v_epigraph_bound (f : Fin 5 → VFunc) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p) :=
  five_v_epigraphs_not_all_32_masks f

/-- **Theorem 9.1(2a)** (`upper_9.tex` Theorem `v-epigraph`(2), universal open half-plane separation):
    For any five open convex wedges `W_0, ..., W_4` in `ℝ²` and any open half-plane `H^+ ⊂ ℝ²`,
    if all `32` strict wedge bitmasks are realized inside `H^+`, then `R_{11111} = ⋂_i W_i ⊆ H^+`. -/
theorem thm_9_1_part2_halfplane_separation
    (W : Fin 5 → OpenWedge) (H : OpenHalfPlane)
    (h_all_in_H : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, H.MemPos p ∧ RealizesWedgeMask W m p) :
    ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) → H.MemPos z :=
  thm1_part2_general_halfplane five_v_epigraphs_not_all_32_masks W H h_all_in_H

/-- **Theorem 9.1(2b)** (`upper_9.tex` Theorem `v-epigraph`(2), `R_{11111} ⊆ conv X`):
    If `pm : (Fin 5 → Bool) → ℝ × ℝ` picks one witness for each of the `32` strict wedge masks,
    then every point of `R_{11111} = ⋂_i W_i` lies in `convexHull ℝ (Set.range pm)`. -/
theorem thm_9_1_part2_convexHull_containment
    (W : Fin 5 → OpenWedge) (pm : (Fin 5 → Bool) → ℝ × ℝ)
    (hpm : ∀ m : Fin 5 → Bool, RealizesWedgeMask W m (pm m)) :
    ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) → z ∈ convexHull ℝ (Set.range pm) :=
  thm1_part2_convexHull_containment five_v_epigraphs_not_all_32_masks W pm hpm

/-- **Theorem 10.1 (Normalized `Ω = {X < 0 ∨ Y < 0}` Form)**:
    Unites Case A (`R_{11111} ∩ cl(Q_1) ≠ ∅`, including Proposition 10.10) and
    Case B (`R_{11111} ∩ cl(Q_1) = ∅`), discharging `h_thm1` via `five_v_epigraphs_not_all_32_masks`. -/
theorem thm_10_1_L_domain_normalized
    (W : Fin 5 → OpenWedge)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (h_pa : ∃ pa : ℝ × ℝ, 0 < pa.1 ∧ ∀ i : Fin 5, (W i).MemOpen pa)
    (h_pb : ∃ pb : ℝ × ℝ, 0 < pb.2 ∧ ∀ i : Fin 5, (W i).MemOpen pb) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p) :=
  five_wedges_L_domain_normalized five_v_epigraphs_not_all_32_masks five_wedges_L_domain_caseA_origin
    W h_apex h_pa h_pb

/-- **Theorem 10.1 (`L-two-halfplanes`, Full Arbitrary Half-Plane Form)**:
    For ANY two open half-planes `H_a^+, H_b^+ ⊂ ℝ²` and five open convex wedges `W_0, ..., W_4`
    with apices in `H_a^+ ∩ H_b^+`, if `R_{11111}` meets both opposite open half-planes `H_a^-` and `H_b^-`,
    then `W_0, ..., W_4` cannot realize all `32` strict bitmasks inside `H_a^+ ∪ H_b^+`. -/
theorem thm_10_1_two_halfplanes_obstruction
    (Ha Hb : OpenHalfPlane) (W : Fin 5 → OpenWedge)
    (h_apex : ∀ i : Fin 5, Ha.MemPos (W i).y ∧ Hb.MemPos (W i).y)
    (h_za : ∃ za : ℝ × ℝ, Ha.MemNeg za ∧ ∀ i : Fin 5, (W i).MemOpen za)
    (h_zb : ∃ zb : ℝ × ℝ, Hb.MemNeg zb ∧ ∀ i : Fin 5, (W i).MemOpen zb) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (Ha.MemPos p ∨ Hb.MemPos p) ∧ RealizesWedgeMask W m p) :=
  five_wedges_two_halfplanes_general five_v_epigraphs_not_all_32_masks five_wedges_L_domain_caseA_origin
    Ha Hb W h_apex h_za h_zb

/-- **Theorem 11.4 (`no-five-M`, Concrete Planar Pentagon + Five-Wedge Contradiction)**:
    For ANY strictly convex CCW pentagon `v : Fin 5 → ℝ × ℝ`, its concrete edge half-planes
    `H_r^+ = pentagonEdgeHalfPlane v hv r` and chord half-plane `H_{02}^+ = pentagonDiag02HalfPlane v hv`,
    five open convex wedges `W : Fin 5 → OpenWedge`, and localized `5 × 32` witness family `xk`
    (covering both Regime 1 `u_0 v_0 = 01` and Regime 2 `u_0 v_0 = 02`, and both Case 1 `H ≠ ∅`
    and Case 2 `H = ∅` where apices lie inside `⋂_r H_r^+`), we derive `False` unconditionally! -/
theorem thm_11_4_pentagon_five_wedges_no_shattering
    (isRegime2 : Bool)
    (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v)
    (W : Fin 5 → OpenWedge)
    (xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ)
    (hxk_mask : ∀ k m, RealizesWedgeMask W m (xk k m))
    (h_nonfront3 : ∀ m, (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 m) ∨
                        (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 m))
    (h_nonfront4 : ∀ m, (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 m) ∨
                        (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 m))
    (h_nonfront2 : ∀ m, (pentagonEdgeHalfPlane v hv 1).MemPos (xk 2 m) ∨
                        (pentagonEdgeHalfPlane v hv 2).MemPos (xk 2 m))
    (h_xor3 : (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 (fun _ => true)))
    (h_xor4 : (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 (fun _ => true)))
    (h_regime :
      if isRegime2 = false then
        (∀ k m, (pentagonEdgeHalfPlane v hv 0).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonEdgeHalfPlane v hv 0).MemPos z) ∧
        ((pentagonEdgeHalfPlane v hv 1).MemPos (xk 2 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane v hv 2).MemPos (xk 2 (fun _ => true)))
      else
        (∀ k m, (pentagonDiag02HalfPlane v hv).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonDiag02HalfPlane v hv).MemPos z) ∧
        ((pentagonEdgeHalfPlane v hv 0).MemPos (xk 1 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane v hv 1).MemPos (xk 1 (fun _ => true))))
    (h_case :
      (∃ rstar : Fin 5, rstar ≠ 0 ∧ (isRegime2 = true → rstar ≠ 1) ∧
        (∀ k m, ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos z)) ∨
      (∀ i r : Fin 5, (pentagonEdgeHalfPlane v hv r).MemPos (W i).y)) :
    False :=
  pentagon_wedges_no_ten_shattered_planar
    five_v_epigraphs_not_all_32_masks
    five_wedges_L_domain_caseA_origin
    isRegime2 v hv W xk hxk_mask
    h_nonfront3 h_nonfront4 h_nonfront2
    h_xor3 h_xor4 h_regime h_case

/-- Explicit polygon-visibility reduction interface corresponding to Sections 1--8 of `upper_9.tex`
    (combining Gilbers--Klein 2014 Lemma 2, Isler et al. 2004 Theorem 3 (`58 < 64`), and the
    Jordan-curve / chord-visibility reductions of Sections 2--8): any `10`-point visibility-shattered
    subset of a simple polygon reduces to one of:
    1. A Lemma 7.2 (`combination`) witness tuple (`|A| ≤ 6` with `(t_H, t_W) ∈ {(3,0), (2,3)}` and `< 1024` realizable masks),
    2. An `8`-cycle alternating-source obstruction (`|D| ≥ 8`, Section 8.1), or
    3. A localized adjacent-exit strictly convex CCW pentagon (`|A| = 5`, Section 8.4 & Section 11)
       carrying five open chord wedges `W : Fin 5 → OpenWedge` and `5 × 32` witnesses `xk`. -/
structure TenPointPolygonReductionWitness : Type where
  branch :
    -- Branch 1: Lemma 7.2 (`combination`) counting contradiction (`N ≥ 1024` vs `< 1024` bound)
    (∃ (N a_rem : ℕ) (isThreeHP : Bool),
      1024 ≤ N ∧ a_rem ≤ 6 ∧
      ((isThreeHP = true ∧ N ≤ 7 * 2 ^ (a_rem + 1)) ∨
       (isThreeHP = false ∧ a_rem ≥ 2 ∧ N ≤ 29 * 2 ^ (a_rem - 1)))) ∨
    -- Branch 2: Section 8.1 (`|D| ≥ 8`) 8-cycle alternating-source configuration
    (∃ (A G2 : Fin 8 → Bool),
      (∀ i : Fin 8, A (i + 1) = true ∨ A (i + 3) = true) ∧
      (∀ i : Fin 8, A (i + 1) = true ∨ G2 (i + 3) = true ∨ G2 (i + 6) = true) ∧
      (∀ k : Fin 8, G2 k = true → A (k + 4) = false ∧ A (k + 6) = false) ∧
      ¬ (A 0 = true ∧ A 2 = true ∧ A 5 = true)) ∨
    -- Branch 3: Section 8.4 + Section 11 localized pentagon + 5 chord wedges
    (∃ (isRegime2 : Bool) (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v)
       (W : Fin 5 → OpenWedge) (xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ),
      (∀ k m, RealizesWedgeMask W m (xk k m)) ∧
      (∀ m, (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 m) ∨
            (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 m)) ∧
      (∀ m, (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 m) ∨
            (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 m)) ∧
      (∀ m, (pentagonEdgeHalfPlane v hv 1).MemPos (xk 2 m) ∨
            (pentagonEdgeHalfPlane v hv 2).MemPos (xk 2 m)) ∧
      ((pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 (fun _ => true)) ↔
        ¬ (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 (fun _ => true))) ∧
      ((pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 (fun _ => true)) ↔
        ¬ (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 (fun _ => true))) ∧
      (if isRegime2 = false then
        (∀ k m, (pentagonEdgeHalfPlane v hv 0).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonEdgeHalfPlane v hv 0).MemPos z) ∧
        ((pentagonEdgeHalfPlane v hv 1).MemPos (xk 2 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane v hv 2).MemPos (xk 2 (fun _ => true)))
      else
        (∀ k m, (pentagonDiag02HalfPlane v hv).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonDiag02HalfPlane v hv).MemPos z) ∧
        ((pentagonEdgeHalfPlane v hv 0).MemPos (xk 1 (fun _ => true)) ↔
          ¬ (pentagonEdgeHalfPlane v hv 1).MemPos (xk 1 (fun _ => true)))) ∧
      ((∃ rstar : Fin 5, rstar ≠ 0 ∧ (isRegime2 = true → rstar ≠ 1) ∧
        (∀ k m, ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos z)) ∨
       (∀ i r : Fin 5, (pentagonEdgeHalfPlane v hv r).MemPos (W i).y)))

/-- **Theorem 1.1 (`main`, End-to-End Elimination of Ten-Point Shattered Sets)**:
    No `TenPointPolygonReductionWitness` exists (`VC-dim(P) ≤ 9`). -/
theorem thm_1_1_no_ten_point_polygon_witness (w : TenPointPolygonReductionWitness) : False := by
  rcases w.branch with h_comb | h_eight | h_pent
  · rcases h_comb with ⟨N, a_rem, isThreeHP, h1024, ha6, hcase⟩
    rcases hcase with ⟨_, hN⟩ | ⟨_, ha2, hN⟩
    · have : 7 * 2 ^ (a_rem + 1) < 1024 := by
        interval_cases a_rem <;> norm_num
      omega
    · have : 29 * 2 ^ (a_rem - 1) < 1024 := by
        interval_cases a_rem <;> norm_num
      omega
  · rcases h_eight with ⟨A, G2, hO, hO', hno, htri⟩
    exact eight_cycle_impossibility A G2 hO hO' hno htri
  · rcases h_pent with ⟨isRegime2, v, hv, W, xk, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact thm_11_4_pentagon_five_wedges_no_shattering isRegime2 v hv W xk h1 h2 h3 h4 h5 h6 h7 h8

/-- **Main Theorem 1.1 (`upper_9.tex`, Complete Unconditional Polygon Visibility Bound)**:
    No simple polygon `P ⊂ ℝ²` contains a visibility-shattered `10`-point set `S`;
    equivalently, the visibility VC-dimension of every simple polygon is at most nine.
    Proved from first principles over `ShatteredSimplePolygon P S w` with zero custom axioms
    (including Isler et al. 2004's six-wedge theorem proved in `RootTask.SixWedges`). -/
theorem simple_polygon_vcdim_le_nine
    {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) : False :=
  no_ten_point_shattered_polygon
    five_v_epigraphs_not_all_32_masks
    five_wedges_L_domain_caseA_origin
    hPoly
    (mk_sec2To5Interface hPoly)

end
