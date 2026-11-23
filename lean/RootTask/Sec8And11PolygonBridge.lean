import Mathlib
import RootTask.Sec6Targets
import RootTask.Sec8And11Master
import RootTask.Sec11VisibilityBridge

open scoped Classical BigOperators
open Finset

noncomputable section

/-!
# Sections 8 & 11 Full Polygon Bridge (`upper_9.tex` Sections 7, 8, 11)

Establishes from `ShatteredSimplePolygon P S w`, `Sec2To5Interface P S w`, `Sec6Targets`,
`Sec7Combination`, `Sec8And11Master`, and `Sec11VisibilityBridge`:
1. Section 7 (`combination_lemma_core`, `wedge_of_inIntTri`, `convexHull_erase_of_chord_opposite`),
2. Section 8.1 (`card_D_le_seven`: `|D| ≤ 7`),
3. Section 8.2 (`card_D_seven_M_le_two`: `|D| = 7 → |M| ≤ 2`),
4. Section 8.3 (`card_D_six_M_le_three`: `|D| = 6 → |M| ≤ 3`),
5. Section 8.4 (`opposite_endpoint_exit`, `pentagon_disjoint_exits_elim`, `adjacent_reduction`,
   `localization`, `forced_good_pair`),
6. Section 11 (`two_sided_visibility_separation`, `adjacent_ear_empty_and_chord_wedges`,
   `no_ten_point_shattered_polygon`).
-/

/-! ## Part 1: Wedge Extraction, `|M| ≤ 5`, and Section 7 Combination Bridge -/

lemma wedge_of_inIntTri {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {a b h : Fin n} (hab : a ≠ b) (ha : h ≠ a) (hb : h ≠ b)
    (hin : ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h)) :
    ∃ R : OpenWedge, IsWedgeTest P (WitnessSet {a, b} ∅ w) (S h) R := by
  have hcol : orient2D (S h) (S a) (S b) ≠ 0 :=
    hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne ha) (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hb)
  rcases lt_or_gt_of_ne hcol with hneg | hpos
  · have hccw : 0 < orient2D (S h) (S b) (S a) := by unfold orient2D at hneg ⊢; linarith
    let U := oppositeConeWedge (S h) (S b) (S a) hccw
    have hU_sep : ∀ x : ℝ × ℝ, U.MemOpen x → orient2D (S h) x (S b) * orient2D (S h) x (S a) < 0 :=
      fun x hx => oppositeConeWedge_separates (S h) (S b) (S a) x hccw hx
    have hU_sep' : ∀ x : ℝ × ℝ, U.MemOpen x → orient2D (S h) x (S a) * orient2D (S h) x (S b) < 0 := by
      intro x hx; rw [mul_comm]; exact hU_sep x hx
    have hU_see : ∀ x ∈ WitnessSet {a, b} ∅ w, Sees P x (S h) → U.MemOpen x := by
      intro x hx _
      rw [oppositeConeWedge_memOpen_iff_inIntTri]
      exact (hin x hx).symm23
    obtain ⟨R, _, _, hR⟩ := h25.wedge_extraction h a b (WitnessSet {a, b} ∅ w) U ha hb hab (fun _ h => h) rfl hU_sep' hU_see
    exact ⟨R, hR⟩
  · let U := oppositeConeWedge (S h) (S a) (S b) hpos
    have hU_sep : ∀ x : ℝ × ℝ, U.MemOpen x → orient2D (S h) x (S a) * orient2D (S h) x (S b) < 0 :=
      fun x hx => oppositeConeWedge_separates (S h) (S a) (S b) x hpos hx
    have hU_see : ∀ x ∈ WitnessSet {a, b} ∅ w, Sees P x (S h) → U.MemOpen x := by
      intro x hx _
      rw [oppositeConeWedge_memOpen_iff_inIntTri]
      exact hin x hx
    obtain ⟨R, _, _, hR⟩ := h25.wedge_extraction h a b (WitnessSet {a, b} ∅ w) U ha hb hab (fun _ h => h) rfl hU_sep hU_see
    exact ⟨R, hR⟩

lemma M_eq_interior_union_H {n : ℕ} (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) :
    let B := hullVertices S
    let H := certifiedVertices S w
    let D := B \ H
    Finset.univ \ D = interiorPoints S ∪ H := by
  intro B H D
  have hHB : H ⊆ B := Finset.filter_subset _ _
  ext x
  simp only [D, interiorPoints, B, H, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hx
    by_cases hxB : x ∈ hullVertices S
    · right; by_contra hxH; exact hx ⟨hxB, hxH⟩
    · left; exact hxB
  · rintro (hxA | hxH)
    · exact fun ⟨hxB, _⟩ => hxA hxB
    · exact fun ⟨_, hxNH⟩ => hxNH hxH

lemma M_card_le_five {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (h25 : Sec2To5Interface P S w) :
    (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card ≤ 5 := by
  rw [M_eq_interior_union_H S w]
  calc (interiorPoints S ∪ certifiedVertices S w).card
      ≤ (interiorPoints S).card + (certifiedVertices S w).card := Finset.card_union_le _ _
    _ ≤ 5 := h25.certified_structure.1

/-- General Section 7 counting lemma (`combination_lemma_core`, `upper_9.tex` Lemma 7.2):
    Given `Q ⊆ D` (`|Q| ∈ {1, 2}`), `M0 ⊆ M`, `F = (D \ Q) ∪ M0`, `M' = M \ M0`,
    half-plane tests on `WitnessSet F ∅ w` for `Q`, 2-corner interior triangles on `WitnessSet F ∅ w`
    for `H \ M0`, and either half-plane tests or `conv(F ∪ {w F})` containment for `A \ M0`,
    concludes `|M'| ≤ 4` (if `|Q| = 1`), `|M'| ≤ 2` (if `|Q| = 2`), and no point of `M'`
    can have a half-plane test when `(|Q| = 1 ∧ |M'| = 4)` or `|Q| = 2`. -/
theorem combination_lemma_core {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {Q M0 : Finset (Fin n)}
    (hQD : Q ⊆ hullVertices S \ certifiedVertices S w)
    (hQ_card : Q.card = 1 ∨ Q.card = 2)
    (hM0 : M0 ⊆ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hQ_hp : ∀ p ∈ Q, ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet (((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0) ∅ w) (S p) H_hp)
    (hH_cov : ∀ h ∈ certifiedVertices S w \ M0, ∃ a b : Fin n,
      a ∈ ((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0 ∧
      b ∈ ((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0 ∧
      a ≠ b ∧ ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h))
    (hA_cov : ∀ z ∈ interiorPoints S \ M0,
      (∃ H_hp : OpenHalfPlane,
        IsHalfPlaneTest P (WitnessSet (((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0) ∅ w) (S z) H_hp) ∨
      S z ∈ convexHull ℝ (((((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0).image S : Set (ℝ × ℝ)) ∪
        {w (((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0)})) :
    let D := hullVertices S \ certifiedVertices S w
    let M := Finset.univ \ D
    let F := (D \ Q) ∪ M0
    let M' := M \ M0
    (Q.card = 1 → M'.card ≤ 4) ∧
    (Q.card = 2 → M'.card ≤ 2) ∧
    (Q.card = 1 → M'.card = 4 → ∀ z ∈ M',
      ¬ ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) ∧
    (Q.card = 2 → ∀ z ∈ M',
      ¬ ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) := by
  intro D M F M'
  have hQ_disj_F : ∀ p ∈ Q, p ∉ F := by
    intro p hp hf
    simp only [F, Finset.mem_union, Finset.mem_sdiff] at hf
    rcases hf with ⟨_, hnq⟩ | hm0
    · exact hnq hp
    · exact (Finset.mem_sdiff.mp (hM0 hm0)).2 (hQD hp)
  have hM'_disj_F : ∀ z ∈ M', z ∉ F := by
    intro z hz hf
    simp only [M', M, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
    simp only [F, Finset.mem_union, Finset.mem_sdiff] at hf
    rcases hf with ⟨hzD, _⟩ | hm0
    · exact hz.1 hzD
    · exact hz.2 hm0
  have hM'_disj_Q : Disjoint Q M' := by
    rw [Finset.disjoint_left]
    intro p hp hz
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (hQD hp)
  have hM'_test : ∀ z ∈ M',
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) ∨
      (∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S z) R) := by
    intro z hz
    have hzM : z ∈ M := (Finset.mem_sdiff.mp hz).1
    have hzNM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
    rw [show M = interiorPoints S ∪ certifiedVertices S w from M_eq_interior_union_H S w] at hzM
    rcases Finset.mem_union.mp hzM with hzA | hzH
    · rcases hA_cov z (Finset.mem_sdiff.mpr ⟨hzA, hzNM0⟩) with hhp | hconv
      · exact Or.inl hhp
      · right
        exact h25.fan_corollary F F z Subset.rfl (hM'_disj_F z hz) hconv
    · right
      obtain ⟨a, b, haF, hbF, hab, hin⟩ := hH_cov z (Finset.mem_sdiff.mpr ⟨hzH, hzNM0⟩)
      have hza : z ≠ a := fun h => hM'_disj_F z hz (h ▸ haF)
      have hzb : z ≠ b := fun h => hM'_disj_F z hz (h ▸ hbF)
      obtain ⟨R, hR⟩ := wedge_of_inIntTri hPoly h25 hab hza hzb hin
      have hW_sub : WitnessSet F ∅ w ⊆ WitnessSet {a, b} ∅ w := by
        rintro x ⟨T, hFT, hTN, rfl⟩
        refine ⟨T, fun y hy => hFT ?_, hTN, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      exact ⟨R, isWedgeTest_mono hW_sub hR⟩
  have hM'_wedge : ∀ z ∈ M', ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S z) R := by
    intro z hz
    rcases hM'_test z hz with ⟨H, hH⟩ | ⟨R, hR⟩
    · exact halfPlaneTest_to_wedgeTest_on_finite P (WitnessSet F ∅ w) (witnessSet_finite F ∅ w) (S z) H hH
    · exact ⟨R, hR⟩
  have hno_2hp_3w : ∀ p1 p2 : Fin n, p1 ∈ Q → p2 ∈ Q → p1 ≠ p2 → M'.card < 3 := by
    intro p1 p2 hp1 hp2 hp12
    by_contra hle; push Not at hle
    obtain ⟨S3, hS3_sub, hS3_card⟩ := Finset.exists_subset_card_eq hle
    let eH : Fin 2 → Fin n := ![p1, p2]
    let eW := S3.equivFinOfCardEq hS3_card
    let aW : Fin 3 → Fin n := fun j => (eW.symm j).1
    have heH_inj : Function.Injective eH := by
      intro i j hij; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij hp12 | exact absurd hij.symm hp12
    have haW_inj : Function.Injective aW := fun i j hij => eW.symm.injective (Subtype.ext hij)
    have ha_inj : Function.Injective (Sum.elim eH aW) := by
      rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (heH_inj h)
      · exfalso
        dsimp at h
        have hp_in_Q : eH i ∈ Q := by fin_cases i <;> assumption
        have hj_in_M' : aW j ∈ M' := hS3_sub (eW.symm j).2
        exact Finset.disjoint_left.mp hM'_disj_Q hp_in_Q (h ▸ hj_in_M')
      · exfalso
        dsimp at h
        have hp_in_Q : eH j ∈ Q := by fin_cases j <;> assumption
        have hi_in_M' : aW i ∈ M' := hS3_sub (eW.symm i).2
        exact Finset.disjoint_left.mp hM'_disj_Q hp_in_Q (h.symm ▸ hi_in_M')
      · exact congrArg Sum.inr (haW_inj h)
    choose Hfn hHfn using fun i => hQ_hp (eH i) (by fin_cases i <;> assumption)
    choose Wfn hWfn using fun j => hM'_wedge (aW j) (hS3_sub (eW.symm j).2)
    exact no_two_hp_three_wedges_on_witnessSet hPoly h25 (Finset.disjoint_empty_right F) eH aW ha_inj
      (fun i => ⟨hQ_disj_F (eH i) (by fin_cases i <;> assumption), Finset.notMem_empty _⟩)
      (fun j => ⟨hM'_disj_F (aW j) (hS3_sub (eW.symm j).2), Finset.notMem_empty _⟩)
      Hfn Wfn hHfn hWfn
  have h1_le4 : Q.card = 1 → M'.card ≤ 4 := by
    intro hQ1
    by_contra hgt; push Not at hgt
    obtain ⟨p, hpQ⟩ := Finset.card_eq_one.mp hQ1
    have hp_mem : p ∈ Q := by rw [hpQ]; exact Finset.mem_singleton_self p
    obtain ⟨S5, hS5_sub, hS5_card⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ M'.card)
    let eW := S5.equivFinOfCardEq hS5_card
    let a6 : Fin 6 → Fin n := fun i => if h : i.val = 0 then p else (eW.symm ⟨i.val - 1, by omega⟩).1
    have ha6_inj : Function.Injective a6 := by
      intro i j hij
      by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
      · exact Fin.ext (hi0.trans hj0.symm)
      · exfalso; simp only [a6, hi0, ↓reduceDIte, hj0] at hij
        exact Finset.disjoint_left.mp hM'_disj_Q hp_mem (hij ▸ hS5_sub (eW.symm _).2)
      · exfalso; simp only [a6, hi0, ↓reduceDIte, hj0] at hij
        exact Finset.disjoint_left.mp hM'_disj_Q hp_mem (hij.symm ▸ hS5_sub (eW.symm _).2)
      · simp only [a6, hi0, hj0, ↓reduceDIte] at hij
        have heq := congrArg Fin.val (eW.symm.injective (Subtype.ext hij))
        ext; dsimp at heq; omega
    have hw6 : ∀ j : Fin 6, ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F ∅ w) (S (a6 j)) R := by
      intro j
      by_cases hj0 : j.val = 0
      · simp only [a6, hj0, ↓reduceDIte]
        obtain ⟨H, hH⟩ := hQ_hp p hp_mem
        exact halfPlaneTest_to_wedgeTest_on_finite P (WitnessSet F ∅ w) (witnessSet_finite F ∅ w) (S p) H hH
      · simp only [a6, hj0, ↓reduceDIte]
        exact hM'_wedge _ (hS5_sub (eW.symm _).2)
    choose R6 hR6 using hw6
    exact no_six_wedges_on_witnessSet hPoly (Finset.disjoint_empty_right F) a6 ha6_inj
      (fun j => by
        by_cases hj0 : j.val = 0
        · simp only [a6, hj0, ↓reduceDIte]; exact ⟨hQ_disj_F p hp_mem, Finset.notMem_empty _⟩
        · simp only [a6, hj0, ↓reduceDIte]; exact ⟨hM'_disj_F _ (hS5_sub (eW.symm _).2), Finset.notMem_empty _⟩)
      R6 hR6
  have h2_le2 : Q.card = 2 → M'.card ≤ 2 := by
    intro hQ2
    obtain ⟨p1, p2, hp12, rfl⟩ := Finset.card_eq_two.mp hQ2
    have hlt := hno_2hp_3w p1 p2 (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hp12
    omega
  have h1_no_hp : Q.card = 1 → M'.card = 4 → ∀ z ∈ M',
      ¬ ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp := by
    intro hQ1 hM4 z hz ⟨Hz, hHz⟩
    obtain ⟨p, hpQ⟩ := Finset.card_eq_one.mp hQ1
    have hp_mem : p ∈ Q := by rw [hpQ]; exact Finset.mem_singleton_self p
    have hpz : p ≠ z := fun h => Finset.disjoint_left.mp hM'_disj_Q hp_mem (h ▸ hz)
    obtain ⟨Hp, hHp⟩ := hQ_hp p hp_mem
    have hM3_card : (M'.erase z).card = 3 := by rw [Finset.card_erase_of_mem hz, hM4]
    let eH : Fin 2 → Fin n := ![p, z]
    let eW := (M'.erase z).equivFinOfCardEq hM3_card
    let aW : Fin 3 → Fin n := fun j => (eW.symm j).1
    have heH_inj : Function.Injective eH := by
      intro i j hij; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij hpz | exact absurd hij.symm hpz
    have ha_inj : Function.Injective (Sum.elim eH aW) := by
      rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (heH_inj h)
      · exfalso; dsimp [eH, aW] at h; fin_cases i
        · have hj := Finset.mem_of_mem_erase (eW.symm j).2
          rw [← h] at hj; exact Finset.disjoint_left.mp hM'_disj_Q hp_mem hj
        · exact (Finset.mem_erase.mp (eW.symm j).2).1 h.symm
      · exfalso; dsimp [eH, aW] at h; fin_cases j
        · have hi := Finset.mem_of_mem_erase (eW.symm i).2
          rw [h] at hi; exact Finset.disjoint_left.mp hM'_disj_Q hp_mem hi
        · exact (Finset.mem_erase.mp (eW.symm i).2).1 h
      · exact congrArg Sum.inr (eW.symm.injective (Subtype.ext h))
    choose Wfn hWfn using fun j => hM'_wedge (aW j) (Finset.mem_of_mem_erase (eW.symm j).2)
    exact no_two_hp_three_wedges_on_witnessSet hPoly h25 (Finset.disjoint_empty_right F) eH aW ha_inj
      (fun i => by fin_cases i; exact ⟨hQ_disj_F p hp_mem, Finset.notMem_empty _⟩; exact ⟨hM'_disj_F z hz, Finset.notMem_empty _⟩)
      (fun j => ⟨hM'_disj_F _ (Finset.mem_of_mem_erase (eW.symm j).2), Finset.notMem_empty _⟩)
      ![Hp, Hz] Wfn (fun i => by fin_cases i <;> assumption) hWfn
  have h2_no_hp : Q.card = 2 → ∀ z ∈ M',
      ¬ ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp := by
    intro hQ2 z hz ⟨Hz, hHz⟩
    obtain ⟨p1, p2, hp12, rfl⟩ := Finset.card_eq_two.mp hQ2
    have hp1z : p1 ≠ z := fun h => Finset.disjoint_left.mp hM'_disj_Q (Finset.mem_insert_self _ _) (h ▸ hz)
    have hp2z : p2 ≠ z := fun h => Finset.disjoint_left.mp hM'_disj_Q (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (h ▸ hz)
    obtain ⟨H1, hH1⟩ := hQ_hp p1 (Finset.mem_insert_self _ _)
    obtain ⟨H2, hH2⟩ := hQ_hp p2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    let a3 : Fin 3 → Fin n := ![p1, p2, z]
    have ha3_inj : Function.Injective a3 := by
      intro i j hij; fin_cases i <;> fin_cases j <;>
        first | rfl | exact absurd hij hp12 | exact absurd hij.symm hp12 | exact absurd hij hp1z | exact absurd hij.symm hp1z | exact absurd hij hp2z | exact absurd hij.symm hp2z
    exact no_three_halfplanes_on_witnessSet hPoly h25 (Finset.disjoint_empty_right F) a3 ha3_inj
      (fun i => by
        fin_cases i
        · exact ⟨hQ_disj_F p1 (Finset.mem_insert_self _ _), Finset.notMem_empty _⟩
        · exact ⟨hQ_disj_F p2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), Finset.notMem_empty _⟩
        · exact ⟨hM'_disj_F z hz, Finset.notMem_empty _⟩)
      ![H1, H2, Hz] (fun i => by fin_cases i <;> assumption)
  exact ⟨h1_le4, h2_le2, h1_no_hp, h2_no_hp⟩


/-! ## Part 2: Cyclic Order, Convex Hull Excision, and Sections 8.1–8.2 (`|D| ≤ 7`, `|D| = 7 → |M| ≤ 2`) -/

private lemma fin_val_sub_eq' {N : ℕ} [NeZero N] (x y : Fin N) :
    (x - y).val = if y ≤ x then x.val - y.val else N + x.val - y.val := by
  by_cases hy0 : y = 0
  · subst hy0; simp
  · have hy_pos : 0 < y.val := Nat.pos_of_ne_zero (fun h => hy0 (Fin.ext h))
    have heq : x - y = x + (-y) := sub_eq_add_neg x y
    rw [heq, Fin.val_add, Fin.val_neg]
    simp only [if_neg hy0]
    split_ifs with hle
    · have h1 : x.val + (N - y.val) = (x.val - y.val) + N := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hlt : x.val < y.val := Nat.lt_of_not_le hle
      have h1 : x.val + (N - y.val) = N + x.val - y.val := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]

private lemma fin_sub_split_lt' {N : ℕ} [NeZero N] {x y z : Fin N}
    (_h1 : 0 < (y - x).val) (_h2 : (y - x).val < (z - x).val) :
    (z - y).val + (y - x).val = (z - x).val := by
  have heq : z - x = (z - y) + (y - x) := by abel
  have hv := congrArg Fin.val heq
  rw [Fin.val_add] at hv
  have hsum_lt : (z - y).val + (y - x).val < N := by
    by_contra hge
    replace hge : N ≤ (z - y).val + (y - x).val := not_lt.mp hge
    have hlt2N : (z - y).val + (y - x).val - N < N := by
      have := (z - y).isLt; have := (y - x).isLt; omega
    have hmod : ((z - y).val + (y - x).val) % N = (z - y).val + (y - x).val - N := by
      have h1' : (z - y).val + (y - x).val = ((z - y).val + (y - x).val - N) + N := by omega
      conv_lhs => rw [h1', Nat.add_mod_right, Nat.mod_eq_of_lt hlt2N]
    rw [hmod] at hv
    have := (z - y).isLt
    omega
  rw [Nat.mod_eq_of_lt hsum_lt] at hv
  exact hv.symm

private lemma fin_sub_split_le' {N : ℕ} [NeZero N] {x y z : Fin N}
    (h : (y - x).val ≤ (z - x).val) :
    (z - y).val + (y - x).val = (z - x).val := by
  by_cases hyx : y = x
  · subst hyx; rw [sub_self]; simp
  · by_cases hyz : y = z
    · subst hyz; rw [sub_self]; simp
    · exact fin_sub_split_lt' (Nat.pos_of_ne_zero (fun h0 => hyx (sub_eq_zero.mp (Fin.ext h0))))
        (lt_of_le_of_ne h (fun h0 => hyz (sub_left_inj.mp (Fin.ext h0))))

private lemma ccwCycle_ccw3_of_lt' {n k : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D k) {a b c : Fin (k + 3)} (hab : a < b) (hbc : b < c) :
    0 < orient2D (S (cycD.toFun a)) (S (cycD.toFun b)) (S (cycD.toFun c)) :=
  cycD.ccw_tri a b c hab hbc

private lemma ccwCycle_subset_cyclicBetw {N M : ℕ} [NeZero N] [NeZero M]
    (f : Fin N → Fin M) (hf : StrictMono f) (i j k : Fin N)
    (h1 : 0 < (j - i).val) (h2 : (j - i).val < (k - i).val) :
    0 < (f j - f i).val ∧ (f j - f i).val < (f k - f i).val := by
  have hij : i ≠ j := fun h => by rw [h, sub_self, Fin.val_zero] at h1; exact Nat.lt_irrefl 0 h1
  have hjk : j ≠ k := fun h => by rw [h] at h2; exact lt_irrefl _ h2
  have hik : i ≠ k := fun h => by rw [h, sub_self, Fin.val_zero] at h2; omega
  have h1' := h1; have h2' := h2
  rw [fin_val_sub_eq' j i] at h1'
  rw [fin_val_sub_eq' j i, fin_val_sub_eq' k i] at h2'
  rw [fin_val_sub_eq' (f j) (f i), fin_val_sub_eq' (f k) (f i)]
  have hle_iff : ∀ a b : Fin N, f a ≤ f b ↔ a ≤ b := fun a b => hf.le_iff_le
  by_cases hij_le : i ≤ j <;> by_cases hik_le : i ≤ k
  · have hfij_le : f i ≤ f j := (hle_iff i j).mpr hij_le
    have hfik_le : f i ≤ f k := (hle_iff i k).mpr hik_le
    rw [if_pos hij_le] at h1'
    rw [if_pos hij_le, if_pos hik_le] at h2'
    rw [if_pos hfij_le, if_pos hfik_le]
    have hjk_lt : j < k := lt_of_le_of_ne (Fin.le_def.mpr (by omega)) hjk
    have hfjk_lt : (f j).val < (f k).val := Fin.lt_def.mp (hf hjk_lt)
    have hfij_lt : (f i).val < (f j).val := Fin.lt_def.mp (hf (lt_of_le_of_ne hij_le hij))
    exact ⟨by omega, by omega⟩
  · have hfij_le : f i ≤ f j := (hle_iff i j).mpr hij_le
    have hfik_nle : ¬ (f i ≤ f k) := fun h => hik_le ((hle_iff i k).mp h)
    rw [if_pos hij_le] at h1'
    rw [if_pos hij_le, if_neg hik_le] at h2'
    rw [if_pos hfij_le, if_neg hfik_nle]
    have hfij_lt : (f i).val < (f j).val := Fin.lt_def.mp (hf (lt_of_le_of_ne hij_le hij))
    have hfk_lt_i : (f k).val < (f i).val := Fin.lt_def.mp (hf (not_le.mp hik_le))
    have hfj_lt : (f j).val < M := (f j).isLt
    exact ⟨by omega, by omega⟩
  · have hfij_nle : ¬ (f i ≤ f j) := fun h => hij_le ((hle_iff i j).mp h)
    have hfik_le : f i ≤ f k := (hle_iff i k).mpr hik_le
    rw [if_neg hij_le] at h1'
    rw [if_neg hij_le, if_pos hik_le] at h2'
    exfalso; have := j.isLt; have := k.isLt; omega
  · have hfij_nle : ¬ (f i ≤ f j) := fun h => hij_le ((hle_iff i j).mp h)
    have hfik_nle : ¬ (f i ≤ f k) := fun h => hik_le ((hle_iff i k).mp h)
    rw [if_neg hij_le] at h1'
    rw [if_neg hij_le, if_neg hik_le] at h2'
    rw [if_neg hfij_nle, if_neg hfik_nle]
    have hjk_lt : j < k := lt_of_le_of_ne (Fin.le_def.mpr (by omega)) hjk
    have hfjk_lt : (f j).val < (f k).val := Fin.lt_def.mp (hf hjk_lt)
    have hfj_lt_i : (f j).val < (f i).val := Fin.lt_def.mp (hf (not_le.mp hij_le))
    have hfi_lt : (f i).val < M := (f i).isLt
    exact ⟨by omega, by omega⟩

lemma isConvexPos_subset {n : ℕ} {S : Fin n → ℝ × ℝ} {C B : Finset (Fin n)}
    (hCB : C ⊆ B) (hB : IsConvexPos S B) : IsConvexPos S C := by
  intro i hi
  have h1 : S i ∉ convexHull ℝ ((B.erase i).image S : Set (ℝ × ℝ)) := hB i (hCB hi)
  intro h2
  apply h1
  exact convexHull_mono (Finset.image_subset_image (Finset.erase_subset_erase i hCB)) h2

lemma nonadj_D_implies_nonadj_B {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (h25 : Sec2To5Interface P S w)
    (hD3 : 3 ≤ (hullVertices S \ certifiedVertices S w).card)
    {a b : Fin n}
    (ha : a ∈ hullVertices S \ certifiedVertices S w)
    (hb : b ∈ hullVertices S \ certifiedVertices S w)
    (hnadj : ¬ IsCCWEdge S (hullVertices S \ certifiedVertices S w) a b) :
    ¬ IsCCWEdge S (hullVertices S) a b := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  have haB : a ∈ B := (Finset.mem_sdiff.mp ha).1
  have hbB : b ∈ B := (Finset.mem_sdiff.mp hb).1
  by_cases hHe : H.Nonempty
  · obtain ⟨l, r, hlD, hrD, hlr, hD_lr, _, hD_pos, _, hEq, _, _⟩ :=
      h25.certified_structure.2 hHe
    have hD_lr' : IsCCWEdge S D l r := hD_lr hD3
    by_cases hab : a = b
    · subst hab; exact fun h => h.2.2.1 rfl
    · by_cases ha_lr : a ≠ l ∧ a ≠ r
      · rw [(hEq a ha ha_lr.1 ha_lr.2 b hbB).2]; exact hnadj
      · by_cases hb_lr : b ≠ l ∧ b ≠ r
        · rw [(hEq b hb hb_lr.1 hb_lr.2 a haB).1]; exact hnadj
        · push Not at ha_lr hb_lr
          by_cases hal : a = l
          · have hbr : b = r := by
              rcases eq_or_ne b l with rfl | hbl
              · exact False.elim (hab hal)
              · exact hb_lr hbl
            subst hal; subst hbr
            exact False.elim (hnadj hD_lr')
          · have har : a = r := ha_lr hal
            have hbl : b = l := by
              rcases eq_or_ne b r with rfl | hbr
              · exact False.elim (hab har)
              · by_contra hne; exact hal (by rcases eq_or_ne b l with rfl | hbl; contradiction; exact False.elim (hbr (hb_lr hbl)))
            rw [har, hbl]
            have hcard_pos : 0 < (D \ {l, r}).card := by
              have hle : (D \ {l, r}).card + ({l, r} : Finset (Fin n)).card ≥ D.card := by
                have := Finset.card_sdiff_add_card_inter D {l, r}
                have hinter : (D ∩ {l, r}).card ≤ ({l, r} : Finset (Fin n)).card :=
                  Finset.card_le_card Finset.inter_subset_right
                omega
              have h2 : ({l, r} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
              dsimp [D, B, H] at *
              omega
            obtain ⟨d, hd⟩ := Finset.card_pos.mp hcard_pos
            have hd_sdiff := Finset.mem_sdiff.mp hd
            have hd_nl : d ≠ l := fun h => hd_sdiff.2 (Finset.mem_insert_self _ _ |> fun m => h ▸ m)
            have hd_nr : d ≠ r := fun h => hd_sdiff.2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _) |> fun m => h ▸ m)
            intro hBrl
            have hdB : d ∈ B := (Finset.mem_sdiff.mp hd_sdiff.1).1
            have hpos := hBrl.2.2.2 d hdB hd_nr hd_nl
            have hpos2 := hD_pos d hd_sdiff.1 hd_nl hd_nr
            unfold orient2D at hpos hpos2; linarith
  · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHe
    have hDB : D = B := by dsimp [D]; rw [hH_empty, Finset.sdiff_empty]
    change ¬ IsCCWEdge S B a b
    rwa [← hDB]

private lemma grassmann_orient2D_id (a b c d z : ℝ × ℝ) :
    orient2D a c d * orient2D a b z + orient2D a b c * orient2D a d z =
      orient2D a b d * orient2D a c z := by
  unfold orient2D; ring

lemma mem_convexHull_of_ccwCycle_edge_nonneg {n k : ℕ} {S : Fin n → ℝ × ℝ}
    {K : Finset (Fin n)} (cyc : CCWCycle S K k) (z : ℝ × ℝ)
    (h_edge : ∀ i : Fin (k + 3), 0 ≤ orient2D (S (cyc.toFun i)) (S (cyc.toFun (i + 1))) z) :
    z ∈ convexHull ℝ (K.image S : Set (ℝ × ℝ)) := by
  let p : Fin (k + 3) → ℝ × ℝ := fun i => S (cyc.toFun i)
  have hp_in : ∀ i : Fin (k + 3), p i ∈ (K.image S : Set (ℝ × ℝ)) := fun i =>
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (ccwCycle_mem cyc i)))
  have helper_tri : ∀ (a b c : ℝ × ℝ), a ∈ (K.image S : Set (ℝ × ℝ)) →
      b ∈ (K.image S : Set (ℝ × ℝ)) → c ∈ (K.image S : Set (ℝ × ℝ)) →
      0 < orient2D a b c → 0 ≤ orient2D a b z → 0 ≤ orient2D b c z → 0 ≤ orient2D c a z →
      z ∈ convexHull ℝ (K.image S : Set (ℝ × ℝ)) := by
    intro a b c ha hb hc hdet h1 h2 h3
    have hdet_ne : orient2D a b c ≠ 0 := ne_of_gt hdet
    have hclosed : InClosedTri a b c z := by
      refine ⟨orient2D b c z / orient2D a b c, orient2D c a z / orient2D a b c,
        orient2D a b z / orient2D a b c, div_nonneg h2 (le_of_lt hdet),
        div_nonneg h3 (le_of_lt hdet), div_nonneg h1 (le_of_lt hdet), ?_, ?_, ?_⟩
      · rw [← add_div, ← add_div, orient2D_barycentric_sum, div_self hdet_ne]
      · have hx := orient2D_barycentric_x a b c z; field_simp [hdet_ne]; linarith
      · have hy := orient2D_barycentric_y a b c z; field_simp [hdet_ne]; linarith
    have hz_tri := (inClosedTri_iff_mem_convexHull a b c z).mp hclosed
    exact convexHull_tri_subset (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ hb)
      (subset_convexHull ℝ _ hc) hz_tri
  let A : Finset ℕ := (Finset.Icc 1 (k + 2)).filter
    (fun j => ∃ h : j < k + 3, 0 ≤ orient2D (p 0) (p ⟨j, h⟩) z)
  have h1A : 1 ∈ A := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by omega, ?_⟩
    have h0 := h_edge 0
    have h01 : (0 + 1 : Fin (k + 3)) = ⟨1, by omega⟩ := by ext; simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
    rwa [← h01]
  let m := A.max' ⟨1, h1A⟩
  have hm_mem : m ∈ A := Finset.max'_mem A ⟨1, h1A⟩
  rcases Finset.mem_filter.mp hm_mem with ⟨hm_icc, hm_lt, hm_pos⟩
  have hm_bounds : 1 ≤ m ∧ m ≤ k + 2 := Finset.mem_Icc.mp hm_icc
  let mi : Fin (k + 3) := ⟨m, hm_lt⟩
  by_cases hmlast : m = k + 2
  · have hmi_last : mi + 1 = 0 := by
      ext; simp [mi, hmlast, Fin.val_add]
    have h_last_pos := h_edge mi
    rw [hmi_last] at h_last_pos
    have hz_last0 : orient2D (p 0) (p mi) z = 0 := by
      have : orient2D (p mi) (p 0) z = -orient2D (p 0) (p mi) z := orient2D_swap12 _ _ _
      linarith
    let mip : Fin (k + 3) := ⟨m - 1, by omega⟩
    have hmip_succ : mip + 1 = mi := by
      ext; simp [mip, mi, Fin.val_add, Nat.mod_eq_of_lt (by omega : m - 1 + 1 < k + 3)]; omega
    have h_mip_pos : 0 ≤ orient2D (p 0) (p mip) z := by
      by_cases hm2 : m = 2
      · have hmip_eq1 : mip = (0 + 1 : Fin (k + 3)) := by
          ext; simp [mip, hm2, Nat.mod_eq_of_lt (by omega : 1 < k + 3)]
        rw [hmip_eq1]; exact h_edge 0
      · have h0_lt_1 : (0 : Fin (k + 3)) < 1 := Fin.lt_def.mpr (by simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3)])
        have h1_lt_mip : (1 : Fin (k + 3)) < mip := Fin.lt_def.mpr (by simp [mip, Nat.mod_eq_of_lt (by omega : 1 < k + 3)]; omega)
        have hmip_lt_mi : mip < mi := Fin.lt_def.mpr (by simp [mip, mi]; omega)
        have h01d := cyc.ccw_tri 0 1 mi h0_lt_1 (lt_trans h1_lt_mip hmip_lt_mi)
        have h0cd := cyc.ccw_tri 0 mip mi (lt_trans h0_lt_1 h1_lt_mip) hmip_lt_mi
        have h01z : 0 ≤ orient2D (p 0) (p 1) z := by
          have h01 : (0 + 1 : Fin (k + 3)) = 1 := by simp
          rw [← h01]; exact h_edge 0
        have gid := grassmann_orient2D_id (p 0) (p 1) (p mip) (p mi) z
        rw [hz_last0, mul_zero, add_zero] at gid
        nlinarith
    have h0_lt_mip : (0 : Fin (k + 3)) < mip := Fin.lt_def.mpr (by simp [mip]; omega)
    have hmip_lt_mi : mip < mi := Fin.lt_def.mpr (by simp [mip, mi]; omega)
    exact helper_tri (p 0) (p mip) (p mi) (hp_in 0) (hp_in mip) (hp_in mi)
      (cyc.ccw_tri 0 mip mi h0_lt_mip hmip_lt_mi)
      h_mip_pos (hmip_succ ▸ h_edge mip) h_last_pos
  · have hm1_le : m + 1 ≤ k + 2 := by omega
    have hm1_nmem : m + 1 ∉ A := fun h => by
      have := Finset.le_max' A (m + 1) h; omega
    have hm1_neg : orient2D (p 0) (p ⟨m + 1, by omega⟩) z < 0 := by
      by_contra hge; push Not at hge
      exact hm1_nmem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hm1_le⟩, by omega, hge⟩)
    have hmi1_eq : mi + 1 = ⟨m + 1, by omega⟩ := by
      ext; simp [mi, Fin.val_add, Nat.mod_eq_of_lt (by omega : m + 1 < k + 3)]
    rw [← hmi1_eq] at hm1_neg
    have h0_lt_mi : (0 : Fin (k + 3)) < mi := Fin.lt_def.mpr (by simp [mi]; omega)
    have hmi_lt_1 : mi < mi + 1 := Fin.lt_def.mpr (by rw [hmi1_eq]; exact Nat.lt_succ_self m)
    exact helper_tri (p 0) (p mi) (p (mi + 1)) (hp_in 0) (hp_in mi) (hp_in (mi + 1))
      (cyc.ccw_tri 0 mi (mi + 1) h0_lt_mi hmi_lt_1)
      hm_pos (h_edge mi) (by have := orient2D_swap12 (p 0) (p (mi + 1)) z; linarith)

private lemma ccwCycle_chord_same_sign_interval {n kB : ℕ} {S : Fin n → ℝ × ℝ}
    {B : Finset (Fin n)} (cycB : CCWCycle S B kB)
    (ib ic ia ic2 idx j : Fin (kB + 3))
    (hia_ic2 : ia ≠ ic2)
    (hia_out : ¬ (0 < (ia - ib).val ∧ (ia - ib).val < (ic - ib).val))
    (hic2_out : ¬ (0 < (ic2 - ib).val ∧ (ic2 - ib).val < (ic - ib).val))
    (hidx : 0 < (idx - ib).val ∧ (idx - ib).val < (ic - ib).val)
    (hj : (j - ib).val ≤ (ic - ib).val) :
    0 ≤ orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun idx)) *
        orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun j)) := by
  by_contra hneg; push Not at hneg
  have hia_idx : idx ≠ ia := fun h => hia_out (h ▸ hidx)
  have hic2_idx : idx ≠ ic2 := fun h => hic2_out (h ▸ hidx)
  have hia_j : j ≠ ia := by
    intro h; rw [h, orient2D_self_outer, mul_zero] at hneg; exact lt_irrefl 0 hneg
  have hic2_j : j ≠ ic2 := by
    intro h; rw [h, orient2D_self_right, mul_zero] at hneg; exact lt_irrefl 0 hneg
  have hidx_j : j ≠ idx := by
    intro h; rw [h] at hneg
    have : 0 ≤ orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun idx)) *
        orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun idx)) := mul_self_nonneg _
    linarith
  have hlt_or : ∀ u v : Fin (kB + 3), u ≠ v →
      (u - ib).val < (v - ib).val → (v - ib).val ≤ (ic - ib).val →
      (∀ x ∈ ({ia, ic2} : Finset (Fin (kB + 3))), x ≠ u → x ≠ v → (v - u).val < (x - u).val) := by
    intro u v huv huv_lt hv_le x hx hxu hxv
    have hx_ne_0 : 0 < (x - u).val := Nat.pos_of_ne_zero (fun h0 => hxu (sub_eq_zero.mp (Fin.ext h0)))
    have hvu_pos : 0 < (v - u).val := by
      have hs := fin_sub_split_le' (le_of_lt huv_lt); omega
    have hvu_ne : (x - u).val ≠ (v - u).val := fun h0 => hxv (sub_left_inj.mp (Fin.ext h0))
    by_contra hle
    have hxu_lt : (x - u).val < (v - u).val := lt_of_le_of_ne (not_lt.mp hle) hvu_ne
    have hs := fin_sub_split_le' (le_of_lt huv_lt)
    have hx_add : (x - ib).val = (x - u).val + (u - ib).val := by
      have h_eq : x - ib = (x - u) + (u - ib) := by abel
      rw [h_eq, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
    have hx_in : 0 < (x - ib).val ∧ (x - ib).val < (ic - ib).val := ⟨by omega, by omega⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hia_out hx_in
    · exact hic2_out hx_in
  have finish : ∀ u v : Fin (kB + 3), 0 < (v - u).val →
      (v - u).val < (ia - u).val → (v - u).val < (ic2 - u).val →
      0 < orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun u)) *
          orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun v)) := by
    intro u v hvu hva hvc
    have hne : (ia - u).val ≠ (ic2 - u).val := fun h0 => hia_ic2 (sub_left_inj.mp (Fin.ext h0))
    rcases lt_or_gt_of_ne hne with hac | hca
    · have hu := ccwCycle_ccw3 cycB (lt_trans hvu hva) hac
      have hva' : 0 < (ia - v).val := by
        have := fin_sub_split_lt' hvu hva; omega
      have hvc' : (ia - v).val < (ic2 - v).val := by
        have h1 := fin_sub_split_lt' hvu hva
        have h2 := fin_sub_split_lt' hvu hvc
        omega
      have hv := ccwCycle_ccw3 cycB hva' hvc'
      rw [orient2D_cycle, orient2D_cycle] at hu hv
      exact mul_pos hu hv
    · have hu := ccwCycle_ccw3 cycB (lt_trans hvu hvc) hca
      have hvc' : 0 < (ic2 - v).val := by
        have := fin_sub_split_lt' hvu hvc; omega
      have hva' : (ic2 - v).val < (ia - v).val := by
        have h1 := fin_sub_split_lt' hvu hva
        have h2 := fin_sub_split_lt' hvu hvc
        omega
      have hv := ccwCycle_ccw3 cycB hvc' hva'
      have hu' : orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun u)) < 0 := by
        rw [orient2D_cycle, orient2D_cycle] at hu
        have := orient2D_swap12 (S (cycB.toFun ic2)) (S (cycB.toFun ia)) (S (cycB.toFun u))
        linarith
      have hv' : orient2D (S (cycB.toFun ia)) (S (cycB.toFun ic2)) (S (cycB.toFun v)) < 0 := by
        rw [orient2D_cycle, orient2D_cycle] at hv
        have := orient2D_swap12 (S (cycB.toFun ic2)) (S (cycB.toFun ia)) (S (cycB.toFun v))
        linarith
      exact mul_pos_of_neg_of_neg hu' hv'
  rcases lt_or_gt_of_ne (fun h => hidx_j (sub_left_inj.mp (Fin.ext h))) with hj_lt | hidx_lt
  · have hpos := hlt_or j idx hidx_j hj_lt (le_of_lt hidx.2)
    have hidx_j_pos : 0 < (idx - j).val := Nat.pos_of_ne_zero (fun h0 => hidx_j (sub_eq_zero.mp (Fin.ext h0)).symm)
    have hmul := finish j idx hidx_j_pos
      (hpos ia (Finset.mem_insert_self _ _) hia_j.symm hia_idx.symm)
      (hpos ic2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hic2_j.symm hic2_idx.symm)
    linarith
  · have hpos := hlt_or idx j hidx_j.symm hidx_lt hj
    have hj_idx_pos : 0 < (j - idx).val := Nat.pos_of_ne_zero (fun h0 => hidx_j (sub_eq_zero.mp (Fin.ext h0)))
    have hmul := finish idx j hj_idx_pos
      (hpos ia (Finset.mem_insert_self _ _) hia_idx.symm hia_j.symm)
      (hpos ic2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hic2_idx.symm hic2_j.symm)
    linarith

lemma convexHull_erase_of_chord_opposite {n kB : ℕ} {S : Fin n → ℝ × ℝ}
    {B Q : Finset (Fin n)} (_hQB : Q ⊆ B) (hBQ3 : 3 ≤ (B \ Q).card)
    (cycB : CCWCycle S B kB) (hB_conv : IsConvexPos S B)
    (h_inj : ∀ a ∈ B, ∀ b ∈ B, S a = S b → a = b)
    (h_noncol : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, a ≠ b → b ≠ c → a ≠ c → orient2D (S a) (S b) (S c) ≠ 0)
    (anchors : Fin n → Fin n × Fin n)
    (h_anc : ∀ p ∈ Q, (anchors p).1 ∈ B \ Q ∧ (anchors p).2 ∈ B \ Q ∧
      (anchors p).1 ≠ (anchors p).2 ∧
      orient2D (S (anchors p).1) (S (anchors p).2) (S p) ≠ 0)
    (z : ℝ × ℝ) (hzB : z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)))
    (hzNQ : z ∉ convexHull ℝ ((B \ Q).image S : Set (ℝ × ℝ))) :
    ∃ p ∈ Q, 0 < orient2D (S (anchors p).1) (S (anchors p).2) (S p) *
      orient2D (S (anchors p).1) (S (anchors p).2) z := by
  let K := B \ Q
  let kK := K.card - 3
  have hkK : K.card = kK + 3 := by
    have hBQ3' : 3 ≤ K.card := hBQ3
    dsimp [kK]; omega
  have hK_conv : IsConvexPos S K := isConvexPos_subset Finset.sdiff_subset hB_conv
  obtain ⟨cycK⟩ := exists_ccwCycle S K
    (fun a ha b hb => h_inj a (Finset.sdiff_subset ha) b (Finset.sdiff_subset hb))
    (fun a ha b hb c hc => h_noncol a (Finset.sdiff_subset ha) b (Finset.sdiff_subset hb) c (Finset.sdiff_subset hc))
    hK_conv hkK
  have hnot_all : ¬ ∀ i : Fin (kK + 3), 0 ≤ orient2D (S (cycK.toFun i)) (S (cycK.toFun (i + 1))) z :=
    fun h => hzNQ (mem_convexHull_of_ccwCycle_edge_nonneg cycK z h)
  push Not at hnot_all
  rcases hnot_all with ⟨ik, hik_neg⟩
  let u := cycK.toFun ik
  let v := cycK.toFun (ik + 1)
  have huK : u ∈ K := ccwCycle_mem cycK ik
  have hvK : v ∈ K := ccwCycle_mem cycK (ik + 1)
  have huB : u ∈ B := Finset.sdiff_subset huK
  have hvB : v ∈ B := Finset.sdiff_subset hvK
  obtain ⟨ib, hib⟩ := ccwCycle_exists_index cycB huB
  obtain ⟨ic, hic⟩ := ccwCycle_exists_index cycB hvB
  have hib_ic : ib ≠ ic := by
    intro h; apply (fin_add_one_ne_self ik)
    exact cycK.inj (hib.symm.trans (congrArg cycB.toFun h |>.trans hic))
  have hic_ib_pos : 0 < (ic - ib).val := Nat.pos_of_ne_zero (fun h0 => hib_ic (sub_eq_zero.mp (Fin.ext h0)).symm)
  let pB : Fin (kB + 3) → ℝ × ℝ := fun i => S (cycB.toFun i)
  have hz_range : z ∈ convexHull ℝ (Set.range pB) := by
    have hr : Set.range pB = (B.image S : Set (ℝ × ℝ)) := by
      rw [← cycB.image_eq]; ext y; simp [pB]
    rwa [hr]
  obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pB cycB.ccw (S u) z hz_range
  rcases (inClosedTri_iff_mem_convexHull _ _ _ _).mpr hm with ⟨μ₁, μ₂, μ₃, hμ1, hμ2, hμ3, hsum, hz1, hz2⟩
  have hcomb := orient2D_convex_comb3 (S u) (S v) (pB m) (pB (m + 1)) (S u) z μ₁ μ₂ μ₃ hsum hz1 hz2
  rw [orient2D_self_outer, mul_zero, add_zero] at hcomb
  obtain ⟨idx, hidx_mem, μ, hμ_eq, hμ_pos, hidx_neg⟩ : ∃ idx : Fin (kB + 3),
      (idx = m ∨ idx = m + 1) ∧ ∃ μ : ℝ, (idx = m ∧ μ = μ₁ ∨ idx = m + 1 ∧ μ = μ₂) ∧
        0 < μ ∧ orient2D (S u) (S v) (pB idx) < 0 := by
    by_cases h1 : 0 < μ₁ ∧ orient2D (S u) (S v) (pB m) < 0
    · exact ⟨m, Or.inl rfl, μ₁, Or.inl ⟨rfl, rfl⟩, h1.1, h1.2⟩
    · refine ⟨m + 1, Or.inr rfl, μ₂, Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
      · by_contra hle; have h0 : μ₂ = 0 := by linarith
        rw [h0, zero_mul, add_zero] at hcomb
        have : 0 ≤ μ₁ * orient2D (S u) (S v) (pB m) := by
          by_cases hm0 : μ₁ = 0
          · rw [hm0, zero_mul]
          · have hμ1p : 0 < μ₁ := lt_of_le_of_ne hμ1 (Ne.symm hm0)
            have hge : 0 ≤ orient2D (S u) (S v) (pB m) := not_lt.mp (fun hlt => h1 ⟨hμ1p, hlt⟩)
            exact mul_nonneg (le_of_lt hμ1p) hge
        linarith
      · by_contra hge; push Not at hge
        have ht1 : 0 ≤ μ₁ * orient2D (S u) (S v) (pB m) := by
          by_cases hm0 : μ₁ = 0
          · rw [hm0, zero_mul]
          · have hμ1p : 0 < μ₁ := lt_of_le_of_ne hμ1 (Ne.symm hm0)
            exact mul_nonneg (le_of_lt hμ1p) (not_lt.mp (fun hlt => h1 ⟨hμ1p, hlt⟩))
        linarith [mul_nonneg hμ2 hge]
  have hK_nonneg : ∀ q ∈ K, 0 ≤ orient2D (S u) (S v) (S q) := by
    intro q hqK
    obtain ⟨iq, hiq⟩ := ccwCycle_exists_index cycK hqK
    rw [← hiq]
    by_cases hi1 : iq = ik
    · rw [hi1]; exact le_of_eq (orient2D_self_outer _ _).symm
    · by_cases hi2 : iq = ik + 1
      · rw [hi2]; exact le_of_eq (orient2D_self_right _ _).symm
      · exact le_of_lt (cycK.ccw ik iq hi1 hi2)
  have hq0_notK : cycB.toFun idx ∉ K := fun hK =>
    not_lt_of_ge (hK_nonneg _ hK) hidx_neg
  have hq0_Q : cycB.toFun idx ∈ Q := by
    have hB_idx : cycB.toFun idx ∈ B := ccwCycle_mem cycB idx
    by_contra hnq
    exact hq0_notK (Finset.mem_sdiff.mpr ⟨hB_idx, hnq⟩)
  have h_between_iff : ∀ j : Fin (kB + 3), orient2D (S u) (S v) (pB j) < 0 →
      0 < (j - ib).val ∧ (j - ib).val < (ic - ib).val := by
    intro j hj
    have hj_ne_ib : j ≠ ib := fun h => by rw [h] at hj; dsimp [pB] at hj; rw [hib, orient2D_self_outer] at hj; exact lt_irrefl 0 hj
    have hj_ne_ic : j ≠ ic := fun h => by rw [h] at hj; dsimp [pB] at hj; rw [hic, orient2D_self_right] at hj; exact lt_irrefl 0 hj
    have hpos_j : 0 < (j - ib).val := Nat.pos_of_ne_zero (fun h0 => hj_ne_ib (sub_eq_zero.mp (Fin.ext h0)))
    have h_ne_v : (j - ib).val ≠ (ic - ib).val := fun h0 => hj_ne_ic (sub_left_inj.mp (Fin.ext h0))
    refine ⟨hpos_j, lt_of_le_of_ne ?_ h_ne_v⟩
    by_contra hgt; push Not at hgt
    have hpos := ccwCycle_ccw3 cycB hic_ib_pos hgt
    dsimp [pB] at hj; rw [hib, hic] at hpos; linarith
  have hidx_betw : 0 < (idx - ib).val ∧ (idx - ib).val < (ic - ib).val := h_between_iff idx hidx_neg
  have h1vB : (1 : Fin (kB + 3)).val = 1 := Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.succ_pos _))
  have hm_le : (m - ib).val ≤ (ic - ib).val := by
    rcases hidx_mem with h_idx | h_idx
    · rw [← h_idx]; exact le_of_lt hidx_betw.2
    · rw [h_idx] at hidx_betw
      by_cases hmib : m = ib
      · subst hmib; rw [sub_self]; exact Nat.zero_le _
      · have hm1 : (m + 1 - ib).val = (m - ib).val + 1 := by
          have hne0 : (m - ib).val < kB + 2 := by
            by_contra hge
            have hmax : (m - ib).val = kB + 2 := by have := (m - ib).isLt; omega
            have hadd0 : (m - ib) + 1 = 0 := by ext; simp [Fin.val_add, hmax]
            have h' : m + 1 - ib = (m - ib) + 1 := by abel
            rw [h', hadd0] at hidx_betw; exact lt_irrefl 0 hidx_betw.1
          have h' : m + 1 - ib = (m - ib) + 1 := by abel
          rw [h', Fin.val_add, h1vB, Nat.mod_eq_of_lt (by omega)]
        omega
  have hm1_le : ((m + 1) - ib).val ≤ (ic - ib).val := by
    rcases hidx_mem with h_idx | h_idx
    · have h' : m + 1 - ib = (m - ib) + 1 := by abel
      have hm_lt : (m - ib).val < (ic - ib).val := h_idx ▸ hidx_betw.2
      have hic_lt : (ic - ib).val < kB + 3 := (ic - ib).isLt
      rw [h', Fin.val_add, h1vB, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [← h_idx]; exact le_of_lt hidx_betw.2
  let q0 := cycB.toFun idx
  obtain ⟨haK, hcK, hac_ne, hanc_ne0⟩ := h_anc q0 hq0_Q
  let a := (anchors q0).1
  let c := (anchors q0).2
  obtain ⟨ia, hia⟩ := ccwCycle_exists_index cycB (Finset.sdiff_subset haK)
  obtain ⟨ic2, hic2⟩ := ccwCycle_exists_index cycB (Finset.sdiff_subset hcK)
  have hia_ic2 : ia ≠ ic2 := fun h => hac_ne (hia.symm.trans (congrArg cycB.toFun h |>.trans hic2))
  have hia_out : ¬ (0 < (ia - ib).val ∧ (ia - ib).val < (ic - ib).val) := by
    rintro ⟨h1, h2⟩
    have h_ccw := ccwCycle_ccw3 cycB h1 h2
    rw [hib, hic, hia] at h_ccw
    have h_kn := hK_nonneg a haK
    unfold orient2D at h_ccw h_kn; linarith
  have hic2_out : ¬ (0 < (ic2 - ib).val ∧ (ic2 - ib).val < (ic - ib).val) := by
    rintro ⟨h1, h2⟩
    have h_ccw := ccwCycle_ccw3 cycB h1 h2
    rw [hib, hic, hic2] at h_ccw
    have h_kn := hK_nonneg c hcK
    unfold orient2D at h_ccw h_kn; linarith
  have hs_m := ccwCycle_chord_same_sign_interval cycB ib ic ia ic2 idx m hia_ic2 hia_out hic2_out hidx_betw hm_le
  have hs_m1 := ccwCycle_chord_same_sign_interval cycB ib ic ia ic2 idx (m + 1) hia_ic2 hia_out hic2_out hidx_betw hm1_le
  have hs_ib := ccwCycle_chord_same_sign_interval cycB ib ic ia ic2 idx ib hia_ic2 hia_out hic2_out hidx_betw (by rw [sub_self]; exact Nat.zero_le _)
  rw [hia, hic2] at hs_m hs_m1
  rw [hia, hic2, hib] at hs_ib
  change 0 ≤ orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (pB m) at hs_m
  change 0 ≤ orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (pB (m + 1)) at hs_m1
  change 0 ≤ orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (S u) at hs_ib
  have hcomb2 := orient2D_convex_comb3 (S a) (S c) (pB m) (pB (m + 1)) (S u) z μ₁ μ₂ μ₃ hsum hz1 hz2
  have hmul : orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) z =
      μ₁ * (orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (pB m)) +
      μ₂ * (orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (pB (m + 1))) +
      μ₃ * (orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (S u)) := by
    rw [hcomb2]; ring
  have hq0_sq : 0 < orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (S q0) :=
    mul_self_pos.mpr hanc_ne0
  refine ⟨q0, hq0_Q, ?_⟩
  rw [hmul]
  rcases hμ_eq with ⟨h_im, h_mu1⟩ | ⟨h_im, h_mu2⟩
  · have hpos1 : 0 < μ₁ * (orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (pB m)) := by
      rw [← h_mu1, ← h_im]; exact mul_pos hμ_pos hq0_sq
    linarith [mul_nonneg hμ2 hs_m1, mul_nonneg hμ3 hs_ib]
  · have hpos2 : 0 < μ₂ * (orient2D (S a) (S c) (S q0) * orient2D (S a) (S c) (pB (m + 1))) := by
      rw [← h_mu2, ← h_im]; exact mul_pos hμ_pos hq0_sq
    linarith [mul_nonneg hμ1 hs_m, mul_nonneg hμ3 hs_ib]

/-- Helper for Sections 8.2 & 8.3: if `Q ⊆ D` has `|Q| = 2`, `5 ≤ |D|`, every `p ∈ Q` is a back
    vertex of `B` from a valid non-adjacent odd source and has anchors `{a_p, c_p} ⊆ D \ Q` giving
    half-plane tests to `p` and to all `z ∈ A` on the `p`-side of chord `a_p c_p`, then `|M| ≤ 2`. -/
lemma combination_M_le_two_of_pureD_anchors {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {p1 p2 : Fin n} (hp12 : p1 ≠ p2)
    (hp1D : p1 ∈ hullVertices S \ certifiedVertices S w)
    (hp2D : p2 ∈ hullVertices S \ certifiedVertices S w)
    (hD5 : 5 ≤ (hullVertices S \ certifiedVertices S w).card)
    (hBack : ∀ q ∈ ({p1, p2} : Finset (Fin n)), ∃ O : Finset (Fin n), q ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) q (w (Finset.univ \ O)))
    (anchors : Fin n → Fin n × Fin n)
    (h_anc : ∀ p ∈ ({p1, p2} : Finset (Fin n)),
      (anchors p).1 ∈ (hullVertices S \ certifiedVertices S w) \ {p1, p2} ∧
      (anchors p).2 ∈ (hullVertices S \ certifiedVertices S w) \ {p1, p2} ∧
      (anchors p).1 ≠ (anchors p).2 ∧
      orient2D (S (anchors p).1) (S (anchors p).2) (S p) ≠ 0 ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {(anchors p).1, (anchors p).2} ∅ w) (S p) H_hp) ∧
      ∀ z : Fin n, z ∈ interiorPoints S →
        0 < orient2D (S (anchors p).1) (S (anchors p).2) (S p) *
            orient2D (S (anchors p).1) (S (anchors p).2) (S z) →
        ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {(anchors p).1, (anchors p).2} ∅ w) (S z) H_hp) :
    (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card ≤ 2 := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let Q : Finset (Fin n) := {p1, p2}
  let F := D \ Q
  have hQD : Q ⊆ D := by
    intro x hx; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hQ2 : Q.card = 2 := Finset.card_pair hp12
  have hH_cov : ∀ h ∈ H \ ∅, ∃ a b : Fin n,
      a ∈ F ∪ ∅ ∧ b ∈ F ∪ ∅ ∧ a ≠ b ∧ ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h) := by
    intro h hh
    have hHn : H.Nonempty := ⟨h, (Finset.mem_sdiff.mp hh).1⟩
    dsimp [F, D, B, H]
    exact h25.side_preservation hHn hD5 Q ∅ hQD (by omega) (Finset.empty_subset _) hBack h hh
  have hQ_hp : ∀ p ∈ Q, ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet (F ∪ ∅) ∅ w) (S p) H_hp := by
    intro p hp
    obtain ⟨haF, hcF, _, _, ⟨H_hp, hH⟩, _⟩ := h_anc p hp
    have hsub : WitnessSet (F ∪ ∅) ∅ w ⊆ WitnessSet {(anchors p).1, (anchors p).2} ∅ w := by
      rintro x ⟨T, hFT, hdisj, rfl⟩
      refine ⟨T, fun y hy => hFT ?_, hdisj, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_union_left _ haF
      · exact Finset.mem_union_left _ hcF
    exact ⟨H_hp, isHalfPlaneTest_mono hsub hH⟩
  have hn3 : 3 ≤ n := by
    have hdn : D.card ≤ n := (Finset.card_le_univ D).trans_eq (Fintype.card_fin n)
    dsimp [D, B, H] at hD5 hdn; omega
  obtain ⟨kB, _, ⟨cycB⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
  have hBQ_sub : D \ Q ⊆ B \ Q := Finset.sdiff_subset_sdiff Finset.sdiff_subset Subset.rfl
  have hBQ3 : 3 ≤ (B \ Q).card := by
    have hDQ : 3 ≤ (D \ Q).card := by
      have hcard_sdiff : (D \ Q).card = D.card - (Q ∩ D).card := Finset.card_sdiff
      have hinter : Q ∩ D = Q := Finset.inter_eq_left.mpr hQD
      have hQ2 : Q.card = 2 := Finset.card_pair hp12
      dsimp [D, B, H] at hcard_sdiff hinter hD5 ⊢
      rw [hinter, hQ2] at hcard_sdiff
      rw [hcard_sdiff]
      omega
    exact hDQ.trans (Finset.card_le_card hBQ_sub)
  have hA_cov : ∀ z ∈ interiorPoints S \ ∅,
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet (F ∪ ∅) ∅ w) (S z) H_hp) ∨
      S z ∈ convexHull ℝ (((F ∪ ∅).image S : Set (ℝ × ℝ)) ∪ {w (F ∪ ∅)}) := by
    intro z hz
    have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
    have hzB := mem_convexHull_hullVertices S hPoly.s_inj z
    by_cases hzNQ : S z ∈ convexHull ℝ (((B \ Q).image S : Set (ℝ × ℝ)))
    · right
      have hB_eq : ((B \ Q).image S : Set (ℝ × ℝ)) = ((F.image S : Set (ℝ × ℝ)) ∪ (H.image S : Set (ℝ × ℝ))) := by
        ext p
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_union]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxNQ⟩
          by_cases hxH : x ∈ certifiedVertices S w
          · exact Or.inr ⟨x, hxH, rfl⟩
          · exact Or.inl ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxB, hxH⟩, hxNQ⟩, rfl⟩
        · rintro (⟨x, hxF, rfl⟩ | ⟨x, hxH, rfl⟩)
          · rcases Finset.mem_sdiff.mp hxF with ⟨hxD, hxNQ⟩
            exact ⟨x, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxD).1, hxNQ⟩, rfl⟩
          · exact ⟨x, Finset.mem_sdiff.mpr
              ⟨Finset.filter_subset _ _ hxH, fun hxQ => (Finset.mem_sdiff.mp (hQD hxQ)).2 hxH⟩, rfl⟩
      have hconv_sub : convexHull ℝ ((B \ Q).image S : Set (ℝ × ℝ)) ⊆
          convexHull ℝ (((F ∪ ∅).image S : Set (ℝ × ℝ)) ∪ {w (F ∪ ∅)}) := by
        refine convexHull_min ?_ (convex_convexHull ℝ _)
        intro p hp
        rw [hB_eq] at hp
        simp only [Set.mem_union, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
        rcases hp with ⟨x, hxF, rfl⟩ | ⟨h, hhH, rfl⟩
        · exact subset_convexHull ℝ _ (Set.mem_union_left _
            (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ hxF))))
        · obtain ⟨a, b, haF, hbF, _, hin⟩ := hH_cov h (Finset.mem_sdiff.mpr ⟨hhH, Finset.notMem_empty _⟩)
          have hwt := hin (w (F ∪ ∅)) ⟨F ∪ ∅, fun t ht => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl
              · exact haF
              · exact hbF,
            Finset.disjoint_empty_right _, rfl⟩
          exact convexHull_tri_subset
            (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _)))
            (subset_convexHull ℝ _ (Set.mem_union_left _ ((Finset.mem_coe.mpr (Finset.mem_image_of_mem S haF)))))
            (subset_convexHull ℝ _ (Set.mem_union_left _ ((Finset.mem_coe.mpr (Finset.mem_image_of_mem S hbF))))) hwt.to_convexHull
      exact hconv_sub hzNQ
    · left
      have hQB : Q ⊆ B := hQD.trans Finset.sdiff_subset
      obtain ⟨p, hpQ, hside⟩ := convexHull_erase_of_chord_opposite hQB hBQ3 cycB
        (hullVertices_convexPos S Subset.rfl)
        (fun a _ b _ h => hPoly.s_inj h)
        (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
          (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
        anchors
        (fun p hp => by
          obtain ⟨haF, hcF, hac, hne, _⟩ := h_anc p hp
          exact ⟨hBQ_sub haF, hBQ_sub hcF, hac, hne⟩)
        (S z) hzB hzNQ
      obtain ⟨haF, hcF, _, _, _, hz_hp⟩ := h_anc p hpQ
      obtain ⟨H_hp, hH⟩ := hz_hp z hzA hside
      have hsub : WitnessSet (F ∪ ∅) ∅ w ⊆ WitnessSet {(anchors p).1, (anchors p).2} ∅ w := by
        rintro x ⟨T, hFT, hdisj, rfl⟩
        refine ⟨T, fun y hy => hFT ?_, hdisj, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Finset.mem_union_left _ haF
        · exact Finset.mem_union_left _ hcF
      exact ⟨H_hp, isHalfPlaneTest_mono hsub hH⟩
  have hres := (combination_lemma_core hPoly h25 hQD (Or.inr hQ2) (Finset.empty_subset _)
    hQ_hp hH_cov hA_cov).2.1 hQ2
  simpa [M] using hres

private lemma fin8_gap_o : ∀ i : Fin 8,
    1 < (i + 2 - i).val ∧ 1 < (i + 4 - (i + 2)).val ∧ 1 < (i - (i + 4)).val ∧
    (i + 2 - i).val + (i + 4 - (i + 2)).val + (i - (i + 4)).val = 8 ∧
    0 < ((i + 1) - i).val ∧ ((i + 1) - i).val < (i + 2 - i).val ∧
    0 < ((i + 3) - (i + 2)).val ∧ ((i + 3) - (i + 2)).val < (i + 4 - (i + 2)).val ∧
    0 < ((i + 5) - (i + 4)).val ∧ ((i + 5) - (i + 4)).val < (i - (i + 4)).val ∧
    0 < ((i + 6) - (i + 4)).val ∧ ((i + 6) - (i + 4)).val < (i - (i + 4)).val ∧
    0 < ((i + 7) - (i + 4)).val ∧ ((i + 7) - (i + 4)).val < (i - (i + 4)).val ∧
    i + 5 ≠ i + 6 ∧ i + 6 ≠ i + 7 ∧ i + 5 ≠ i + 7 ∧ i + 4 ≠ i ∧
    i + 4 ≠ i + 5 ∧ i + 4 ≠ i + 6 ∧ i + 4 ≠ i + 7 ∧
    i ≠ i + 5 ∧ i ≠ i + 6 ∧ i ≠ i + 7 := by decide

private lemma fin8_gap_o' : ∀ i : Fin 8,
    1 < (i + 2 - i).val ∧ 1 < (i + 5 - (i + 2)).val ∧ 1 < (i - (i + 5)).val ∧
    (i + 2 - i).val + (i + 5 - (i + 2)).val + (i - (i + 5)).val = 8 ∧
    0 < ((i + 1) - i).val ∧ ((i + 1) - i).val < (i + 2 - i).val ∧
    0 < ((i + 3) - (i + 2)).val ∧ ((i + 3) - (i + 2)).val < (i + 5 - (i + 2)).val ∧
    0 < ((i + 4) - (i + 2)).val ∧ ((i + 4) - (i + 2)).val < (i + 5 - (i + 2)).val ∧
    0 < ((i + 6) - (i + 5)).val ∧ ((i + 6) - (i + 5)).val < (i - (i + 5)).val ∧
    0 < ((i + 7) - (i + 5)).val ∧ ((i + 7) - (i + 5)).val < (i - (i + 5)).val := by decide

private lemma fin8_g2_safe : ∀ k : Fin 8,
    k ≠ k + 1 ∧
    k + 4 ≠ k ∧ k + 4 ≠ k + 1 ∧ (k + 4 - 1) ∉ ({k, k + 1} : Finset (Fin 8)) ∧
    (k + 4 + 1) ∉ ({k, k + 1} : Finset (Fin 8)) ∧ k - 1 ≠ k + 4 ∧ k + 2 ≠ k + 4 ∧
    k + 6 ≠ k ∧ k + 6 ≠ k + 1 ∧ (k + 6 - 1) ∉ ({k, k + 1} : Finset (Fin 8)) ∧
    (k + 6 + 1) ∉ ({k, k + 1} : Finset (Fin 8)) ∧ k - 1 ≠ k + 6 ∧ k + 2 ≠ k + 6 ∧
    (∀ t : Fin 8, (t - 1) ∉ ({k, k + 1} : Finset (Fin 8)) → t - 1 ≠ k ∧ t - 1 ≠ k + 1) ∧
    (∀ t : Fin 8, (t + 1) ∉ ({k, k + 1} : Finset (Fin 8)) → t + 1 ≠ k ∧ t + 1 ≠ k + 1) := by decide

private lemma fin8_k_rel : ∀ k : Fin 8,
    k - 1 ≠ k ∧ k + 2 ≠ k ∧ k - 1 ≠ k + 1 ∧ k + 2 ≠ k + 1 := by decide

private lemma fin8_t_rel : ∀ t : Fin 8, t - 1 ≠ t ∧ t + 1 ≠ t := by decide

/-- **Section 8.1 (`card_D_le_seven`, `upper_9.tex` lines 916–926)**:
    For any `ShatteredSimplePolygon`, `|D| = |B \ H| ≤ 7`. -/
theorem card_D_le_seven {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w) :
    (hullVertices S \ certifiedVertices S w).card ≤ 7 := by
  by_contra hgt; push Not at hgt
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  have hD8 : 8 ≤ D.card := hgt
  let kD := D.card - 3
  have hkD : D.card = kD + 3 := by omega
  obtain ⟨cycD⟩ := exists_ccwCycle S D
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Finset.sdiff_subset) hkD
  let toIdx : Fin 8 → Fin (kD + 3) := fun i => ⟨i.val, by omega⟩
  have h_strict : StrictMono toIdx := fun a b hab => Fin.lt_def.mpr (Fin.lt_def.mp hab)
  let d' : Fin 8 → Fin n := fun i => cycD.toFun (toIdx i)
  have hd'_inj : Function.Injective d' := cycD.inj.comp h_strict.injective
  have hd'_D : ∀ i : Fin 8, d' i ∈ D := fun i => ccwCycle_mem cycD (toIdx i)
  let A : Fin 8 → Bool := fun k =>
    decide (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {d' (k - 1), d' (k + 1)} ∅ w) (S (d' k)) H_hp)
  let G2 : Fin 8 → Bool := fun k =>
    decide (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {d' (k - 1), d' (k + 2)} ∅ w) (S (d' k)) H_hp) &&
    decide (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {d' (k - 1), d' (k + 2)} ∅ w) (S (d' (k + 1))) H_hp)
  have h_no_three8 : ∀ (a b c : Fin 8) (oa ob : Fin 8),
      a ≠ b → b ≠ c → a ≠ c → oa ≠ ob →
      oa ≠ a → oa ≠ b → oa ≠ c → ob ≠ a → ob ≠ b → ob ≠ c →
      (∃ H_hp, IsHalfPlaneTest P (WitnessSet {d' oa, d' ob} ∅ w) (S (d' a)) H_hp) →
      (∃ H_hp, IsHalfPlaneTest P (WitnessSet {d' oa, d' ob} ∅ w) (S (d' b)) H_hp) →
      (∃ H_hp, IsHalfPlaneTest P (WitnessSet {d' oa, d' ob} ∅ w) (S (d' c)) H_hp) →
      False := by
    intro a b c oa ob hab hbc hac _ ha1 hb1 hc1 ha2 hb2 hc2 ⟨Ha, hHa⟩ ⟨Hb, hHb⟩ ⟨Hc, hHc⟩
    let a3 : Fin 3 → Fin n := ![d' a, d' b, d' c]
    have ha3 : Function.Injective a3 := by
      intro x y hxy; fin_cases x <;> fin_cases y <;>
        first | rfl | exact absurd (hd'_inj hxy) hab | exact absurd (hd'_inj hxy) hac |
          exact absurd (hd'_inj hxy) hbc | exact absurd (hd'_inj hxy).symm hab |
          exact absurd (hd'_inj hxy).symm hac | exact absurd (hd'_inj hxy).symm hbc
    exact no_three_halfplanes_on_witnessSet hPoly h25 (Finset.disjoint_empty_right {d' oa, d' ob})
      a3 ha3 (fun i => by
        fin_cases i
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; refine ⟨⟨hd'_inj.ne ha1.symm, hd'_inj.ne ha2.symm⟩, Finset.notMem_empty _⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; refine ⟨⟨hd'_inj.ne hb1.symm, hd'_inj.ne hb2.symm⟩, Finset.notMem_empty _⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; refine ⟨⟨hd'_inj.ne hc1.symm, hd'_inj.ne hc2.symm⟩, Finset.notMem_empty _⟩)
      ![Ha, Hb, Hc] (fun i => by fin_cases i <;> assumption)
  have apply_gap : ∀ (i1 i2 i3 : Fin 8),
      1 < (i2 - i1).val → 1 < (i3 - i2).val → 1 < (i1 - i3).val →
      (i2 - i1).val + (i3 - i2).val + (i1 - i3).val = 8 →
      let o1 := d' i1; let o2 := d' i2; let o3 := d' i3
      (∀ m : Fin 8, 0 < (m - i1).val → (m - i1).val < (i2 - i1).val →
        ∃ H_hp, IsHalfPlaneTest P (WitnessSet {o1, o2} ∅ w) (S (d' m)) H_hp) ∨
      (∀ m : Fin 8, 0 < (m - i2).val → (m - i2).val < (i3 - i2).val →
        ∃ H_hp, IsHalfPlaneTest P (WitnessSet {o2, o3} ∅ w) (S (d' m)) H_hp) ∨
      (∀ m : Fin 8, 0 < (m - i3).val → (m - i3).val < (i1 - i3).val →
        ∃ H_hp, IsHalfPlaneTest P (WitnessSet {o3, o1} ∅ w) (S (d' m)) H_hp) := by
    intro i1 i2 i3 h12 h23 h31 hsum
    have hi12_lt : (i2 - i1).val < (i3 - i1).val := by
      have hi13_ne : i1 ≠ i3 := fun h => by rw [h, sub_self] at h31; omega
      have hi13_c := fin_sub_add_compl hi13_ne
      by_contra hge
      have hs' := fin_sub_split_le' (not_lt.mp hge)
      have hi23_ne : i2 ≠ i3 := fun h => by rw [h, sub_self] at h23; omega
      have hi32 := fin_sub_add_compl hi23_ne
      omega
    have hbet12 := ccwCycle_subset_cyclicBetw toIdx h_strict i1 i2 i3 (by omega) hi12_lt
    have hD12_pos := hbet12.1
    have hD13_lt := hbet12.2
    have h12D : 1 < (toIdx i2 - toIdx i1).val := by
      have := ccwCycle_subset_cyclicBetw toIdx h_strict i1 (i1 + 1) i2
        (by rw [add_sub_cancel_left]; decide) (by rw [add_sub_cancel_left]; exact h12)
      omega
    have h23D : 1 < (toIdx i3 - toIdx i2).val := by
      have hi21_ne : i1 ≠ i2 := fun h => by rw [h, sub_self] at h12; omega
      have hi21_c := fin_sub_add_compl hi21_ne
      have hi23_lt : (i3 - i2).val < (i1 - i2).val := by
        have := fin_sub_split_lt' (by omega : 0 < (i2 - i1).val) hi12_lt
        have hi31_c := fin_sub_add_compl (show i1 ≠ i3 from fun h => by rw [h, sub_self] at h31; omega)
        have hi32_ne : i3 ≠ i2 := fun h => by rw [h, sub_self] at h23; omega
        have hi32_c := fin_sub_add_compl hi32_ne
        omega
      have := ccwCycle_subset_cyclicBetw toIdx h_strict i2 (i2 + 1) i3
        (by rw [add_sub_cancel_left]; decide) (by rw [add_sub_cancel_left]; exact h23)
      omega
    have h31D : 1 < (toIdx i1 - toIdx i3).val := by
      have := ccwCycle_subset_cyclicBetw toIdx h_strict i3 (i3 + 1) i1
        (by rw [add_sub_cancel_left]; decide) (by rw [add_sub_cancel_left]; exact h31)
      omega
    have hsumD : (toIdx i2 - toIdx i1).val + (toIdx i3 - toIdx i2).val + (toIdx i1 - toIdx i3).val = kD + 3 := by
      have hs := fin_sub_split_lt' hD12_pos hD13_lt
      have hi13_ne : toIdx i1 ≠ toIdx i3 := fun h => by rw [h, sub_self, Fin.val_zero] at h31D; omega
      have hc := fin_sub_add_compl hi13_ne
      dsimp [kD] at *
      linarith
    obtain ⟨oa, ob, Γ, hcase, _, hΓ⟩ := gap_lemma hPoly h25 Subset.rfl cycD (toIdx i1) (toIdx i2) (toIdx i3)
      h12D h23D h31D hsumD
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left; intro m hm1 hm2
      have hbet := ccwCycle_subset_cyclicBetw toIdx h_strict i1 m i2 hm1 hm2
      have hmΓ : d' m ∈ D.filter (fun p => ∃ x : Fin (kD + 3), cycD.toFun x = p ∧
          0 < (x - toIdx i1).val ∧ (x - toIdx i1).val < (toIdx i2 - toIdx i1).val) :=
        Finset.mem_filter.mpr ⟨hd'_D m, toIdx m, rfl, hbet.1, hbet.2⟩
      exact (hΓ (d' m) hmΓ).2.2.1
    · right; left; intro m hm1 hm2
      have hbet := ccwCycle_subset_cyclicBetw toIdx h_strict i2 m i3 hm1 hm2
      have hmΓ : d' m ∈ D.filter (fun p => ∃ x : Fin (kD + 3), cycD.toFun x = p ∧
          0 < (x - toIdx i2).val ∧ (x - toIdx i2).val < (toIdx i3 - toIdx i2).val) :=
        Finset.mem_filter.mpr ⟨hd'_D m, toIdx m, rfl, hbet.1, hbet.2⟩
      exact (hΓ (d' m) hmΓ).2.2.1
    · right; right; intro m hm1 hm2
      have hbet := ccwCycle_subset_cyclicBetw toIdx h_strict i3 m i1 hm1 hm2
      have hmΓ : d' m ∈ D.filter (fun p => ∃ x : Fin (kD + 3), cycD.toFun x = p ∧
          0 < (x - toIdx i3).val ∧ (x - toIdx i3).val < (toIdx i1 - toIdx i3).val) :=
        Finset.mem_filter.mpr ⟨hd'_D m, toIdx m, rfl, hbet.1, hbet.2⟩
      exact (hΓ (d' m) hmΓ).2.2.1
  have hO : ∀ i : Fin 8, A (i + 1) = true ∨ A (i + 3) = true := by
    intro i
    obtain ⟨g1, g2, g3, g4, a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ :=
      fin8_gap_o i
    rcases apply_gap i (i + 2) (i + 4) g1 g2 g3 g4 with h1 | h2 | h3
    · left
      have hp := h1 (i + 1) a1 a2
      have heq1 : (i + 1) - 1 = i := by abel
      have heq2 : (i + 1) + 1 = i + 2 := by abel
      dsimp [A]; rw [heq1, heq2]; exact decide_eq_true hp
    · right
      have hp := h2 (i + 3) b1 b2
      have heq1 : (i + 3) - 1 = i + 2 := by abel
      have heq2 : (i + 3) + 1 = i + 4 := by abel
      dsimp [A]; rw [heq1, heq2]; exact decide_eq_true hp
    · exfalso
      exact h_no_three8 (i + 5) (i + 6) (i + 7) (i + 4) i
        n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 (h3 (i + 5) c1 c2) (h3 (i + 6) d1 d2) (h3 (i + 7) e1 e2)
  have hO' : ∀ i : Fin 8, A (i + 1) = true ∨ G2 (i + 3) = true ∨ G2 (i + 6) = true := by
    intro i
    obtain ⟨g1, g2, g3, g4, a1, a2, b1, b2, c1, c2, d1, d2, e1, e2⟩ := fin8_gap_o' i
    rcases apply_gap i (i + 2) (i + 5) g1 g2 g3 g4 with h1 | h2 | h3
    · left
      have heq1 : (i + 1) - 1 = i := by abel
      have heq2 : (i + 1) + 1 = i + 2 := by abel
      dsimp [A]; rw [heq1, heq2]; exact decide_eq_true (h1 (i + 1) a1 a2)
    · right; left
      have heq1 : (i + 3) - 1 = i + 2 := by abel
      have heq2 : (i + 3) + 2 = i + 5 := by abel
      have heq3 : (i + 3) + 1 = i + 4 := by abel
      dsimp [G2]; rw [heq1, heq2, heq3]
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (h2 (i + 3) b1 b2), decide_eq_true (h2 (i + 4) c1 c2)⟩
    · right; right
      have heq1 : (i + 6) - 1 = i + 5 := by abel
      have heq2 : (i + 6) + 2 = i := by
        calc (i + 6) + 2 = i + (6 + 2) := by abel
          _ = i + 0 := rfl
          _ = i := add_zero i
      have heq3 : (i + 6) + 1 = i + 7 := by abel
      dsimp [G2]; rw [heq1, heq2, heq3]
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (h3 (i + 6) d1 d2), decide_eq_true (h3 (i + 7) e1 e2)⟩
  have h_no_G2_A : ∀ k : Fin 8, G2 k = true → A (k + 4) = false ∧ A (k + 6) = false := by
    intro k hk
    dsimp [G2] at hk; rw [Bool.and_eq_true_iff] at hk
    have hk1 := of_decide_eq_true hk.1
    have hk2 := of_decide_eq_true hk.2
    obtain ⟨hk_kk1, h4a, h4b, h4c, h4d, h4e, h4f, h6a, h6b, h6c, h6d, h6e, h6f, hm_n, hp_n⟩ := fin8_g2_safe k
    obtain ⟨hkm1_k, hkp2_k, hkm1_k1, hkp2_k1⟩ := fin8_k_rel k
    have htest3 : ∀ t : Fin 8, A t = true →
        t ≠ k → t ≠ k + 1 → (t - 1) ∉ ({k, k + 1} : Finset (Fin 8)) → (t + 1) ∉ ({k, k + 1} : Finset (Fin 8)) →
        (k - 1) ≠ t → (k + 2) ≠ t → False := by
      intro t ht htk htk1 htm1 htp1 hkm1 hkp2
      have hAt := of_decide_eq_true ht
      obtain ⟨htm1_t, htp1_t⟩ := fin8_t_rel t
      have htm1_ne := hm_n t htm1
      have htp1_ne := hp_n t htp1
      let F3 : Finset (Fin n) := {d' (k - 1), d' (k + 2), d' (t - 1), d' (t + 1)}
      have hW1 : WitnessSet F3 ∅ w ⊆ WitnessSet {d' (k - 1), d' (k + 2)} ∅ w :=
        witnessSet_mono (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [F3]) Subset.rfl
      have hW2 : WitnessSet F3 ∅ w ⊆ WitnessSet {d' (t - 1), d' (t + 1)} ∅ w :=
        witnessSet_mono (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [F3]) Subset.rfl
      obtain ⟨H1, hH1⟩ := hk1
      obtain ⟨H2, hH2⟩ := hk2
      obtain ⟨H3, hH3⟩ := hAt
      let a3 : Fin 3 → Fin n := ![d' k, d' (k + 1), d' t]
      have ha3 : Function.Injective a3 := by
        intro x y hxy; fin_cases x <;> fin_cases y <;>
          first | rfl | exact absurd (hd'_inj hxy) hk_kk1 | exact absurd (hd'_inj hxy) hk_kk1.symm |
            exact absurd (hd'_inj hxy) htk.symm | exact absurd (hd'_inj hxy) htk |
            exact absurd (hd'_inj hxy) htk1.symm | exact absurd (hd'_inj hxy) htk1
      have hdisj : ∀ i : Fin 3, a3 i ∉ F3 ∧ a3 i ∉ (∅ : Finset (Fin n)) := by
        intro i; fin_cases i
        · refine ⟨?_, Finset.notMem_empty _⟩
          simp only [a3, F3, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hd'_inj.ne hkm1_k.symm, hd'_inj.ne hkp2_k.symm,
            hd'_inj.ne htm1_ne.1.symm, hd'_inj.ne htp1_ne.1.symm⟩
        · refine ⟨?_, Finset.notMem_empty _⟩
          simp only [a3, F3, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hd'_inj.ne hkm1_k1.symm, hd'_inj.ne hkp2_k1.symm,
            hd'_inj.ne htm1_ne.2.symm, hd'_inj.ne htp1_ne.2.symm⟩
        · refine ⟨?_, Finset.notMem_empty _⟩
          simp only [a3, F3, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hd'_inj.ne hkm1.symm, hd'_inj.ne hkp2.symm,
            hd'_inj.ne htm1_t.symm, hd'_inj.ne htp1_t.symm⟩
      exact no_three_halfplanes_on_witnessSet hPoly h25 (Finset.disjoint_empty_right F3) a3 ha3 hdisj
        ![H1, H2, H3] (fun i => by
          fin_cases i
          · exact isHalfPlaneTest_mono hW1 hH1
          · exact isHalfPlaneTest_mono hW1 hH2
          · exact isHalfPlaneTest_mono hW2 hH3)
    refine ⟨?_, ?_⟩
    · by_contra h4; have h4t : A (k + 4) = true := by revert h4; cases A (k + 4) <;> simp
      exact htest3 (k + 4) h4t h4a h4b h4c h4d h4e h4f
    · by_contra h6; have h6t : A (k + 6) = true := by revert h6; cases A (k + 6) <;> simp
      exact htest3 (k + 6) h6t h6a h6b h6c h6d h6e h6f
  have h_no_triple : ¬ (A 0 = true ∧ A 2 = true ∧ A 5 = true) := by
    rintro ⟨h0, h2, h5⟩
    obtain ⟨H0, hH0⟩ := of_decide_eq_true h0
    obtain ⟨H2, hH2⟩ := of_decide_eq_true h2
    obtain ⟨H5, hH5⟩ := of_decide_eq_true h5
    have h_eq11 : ((0 : Fin 8) - 1) = 7 := by decide
    have h_eq12 : ((0 : Fin 8) + 1) = 1 := by decide
    have h_eq21 : ((2 : Fin 8) - 1) = 1 := by decide
    have h_eq22 : ((2 : Fin 8) + 1) = 3 := by decide
    have h_eq51 : ((5 : Fin 8) - 1) = 4 := by decide
    have h_eq52 : ((5 : Fin 8) + 1) = 6 := by decide
    rw [h_eq11, h_eq12] at hH0; rw [h_eq21, h_eq22] at hH2; rw [h_eq51, h_eq52] at hH5
    let F3 : Finset (Fin n) := {d' 7, d' 1, d' 3, d' 4, d' 6}
    have hW0 : WitnessSet F3 ∅ w ⊆ WitnessSet {d' 7, d' 1} ∅ w :=
      witnessSet_mono (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [F3]) Subset.rfl
    have hW2 : WitnessSet F3 ∅ w ⊆ WitnessSet {d' 1, d' 3} ∅ w :=
      witnessSet_mono (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [F3]) Subset.rfl
    have hW5 : WitnessSet F3 ∅ w ⊆ WitnessSet {d' 4, d' 6} ∅ w :=
      witnessSet_mono (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [F3]) Subset.rfl
    let a3 : Fin 3 → Fin n := ![d' 0, d' 2, d' 5]
    have ha3 : Function.Injective a3 := by
      intro x y hxy; fin_cases x <;> fin_cases y <;> first | rfl | exact absurd (hd'_inj hxy) (by decide)
    exact no_three_halfplanes_on_witnessSet hPoly h25 (Finset.disjoint_empty_right F3) a3 ha3
      (fun i => by
        fin_cases i <;> refine ⟨?_, Finset.notMem_empty _⟩ <;> simp [a3, F3, hd'_inj.eq_iff])
      ![H0, H2, H5] (fun i => by
        fin_cases i
        · exact isHalfPlaneTest_mono hW0 hH0
        · exact isHalfPlaneTest_mono hW2 hH2
        · exact isHalfPlaneTest_mono hW5 hH5)
  exact eight_cycle_impossibility A G2 hO hO' h_no_G2_A h_no_triple

/-- Construct a `CCWCycle` on any `C ⊆ D` from an injective index map preserving cyclic order. -/
def ccwCycle_of_sub_cyclic {n kD m : ℕ} {S : Fin n → ℝ × ℝ} {D C : Finset (Fin n)}
    (cycD : CCWCycle S D kD) (idx : Fin (m + 3) → Fin (kD + 3))
    (hinj : Function.Injective idx)
    (himg : Finset.univ.image (fun i => cycD.toFun (idx i)) = C)
    (hord : ∀ a b c : Fin (m + 3), a < b → b < c →
      0 < (idx b - idx a).val ∧ (idx b - idx a).val < (idx c - idx a).val) :
    CCWCycle S C m where
  toFun i := cycD.toFun (idx i)
  inj a b h := hinj (cycD.inj h)
  image_eq := himg
  ccw_tri a b c hab hbc := by
    have ho := hord a b c hab hbc
    exact ccwCycle_ccw3 cycD ho.1 ho.2
  ccw i j hij hji := by
    have htri : ∀ a b c : Fin (m + 3), a < b → b < c →
        0 < orient2D (S (cycD.toFun (idx a))) (S (cycD.toFun (idx b))) (S (cycD.toFun (idx c))) :=
      fun a b c hab hbc => ccwCycle_ccw3 cycD (hord a b c hab hbc).1 (hord a b c hab hbc).2
    have h1v : (1 : Fin (m + 3)).val = 1 := Nat.mod_eq_of_lt (by omega : 1 < m + 3)
    by_cases hi_last : i + 1 = 0
    · have hj0 : (0 : Fin (m + 3)) < j := Fin.pos_of_ne_zero (fun h => hji (h ▸ hi_last.symm))
      have hi_eq_last : i.val = m + 2 := by
        by_contra hne
        have hlt : i.val + 1 < m + 3 := by have := i.isLt; omega
        have hv : (i + 1 : Fin (m + 3)).val = 0 := congrArg Fin.val hi_last
        rw [Fin.val_add, h1v, Nat.mod_eq_of_lt hlt] at hv
        omega
      have hji' : j < i := lt_of_le_of_ne (Fin.le_def.mpr (by have := j.isLt; omega)) hij
      have h := htri 0 j i hj0 hji'
      change 0 < orient2D (S (cycD.toFun (idx i))) (S (cycD.toFun (idx (i + 1)))) (S (cycD.toFun (idx j)))
      rw [hi_last, orient2D_cycle, orient2D_cycle]
      exact h
    · have hi_lt : i < i + 1 := by
        have hv : (i + 1 : Fin (m + 3)).val = i.val + 1 := by
          by_cases hmax : i.val + 1 = m + 3
          · exfalso; apply hi_last; ext; rw [Fin.val_add, h1v, hmax]; simp
          · have hlt : i.val + 1 < m + 3 := by have := i.isLt; omega
            rw [Fin.val_add, h1v, Nat.mod_eq_of_lt hlt]
        exact Fin.lt_def.mpr (by rw [hv]; omega)
      rcases lt_trichotomy i j with hij_lt | rfl | hji_lt
      · have hi1_lt_j : i + 1 < j := by
          have hval : (i + 1 : Fin (m + 3)).val = i.val + 1 := by
            rw [Fin.val_add, h1v, Nat.mod_eq_of_lt (by have := Fin.lt_def.mp hij_lt; omega)]
          exact Fin.lt_def.mpr (by
            rw [hval]; exact Nat.lt_of_le_of_ne (Fin.lt_def.mp hij_lt) (fun h => hji (Fin.ext (by rw [hval, h]))))
        exact htri i (i + 1) j hi_lt hi1_lt_j
      · exact False.elim (hij rfl)
      · have h := htri j i (i + 1) hji_lt hi_lt
        change 0 < orient2D (S (cycD.toFun (idx i))) (S (cycD.toFun (idx (i + 1)))) (S (cycD.toFun (idx j)))
        rw [orient2D_cycle, orient2D_cycle] at h
        exact h

private def toF7 (z : ZMod 7) : Fin 7 := ⟨z.val, z.val_lt⟩
private def toZ7 (i : Fin 7) : ZMod 7 := (i.val : ZMod 7)
private def idx7_0 (z : Fin 7) (k : Fin 6) : Fin 7 := z + ⟨k.val + 1, by omega⟩
private def idx7_1 (z : Fin 7) (k : Fin 6) : Fin 7 := z + ⟨if k.val < 5 then k.val + 2 else 1, by split_ifs <;> omega⟩

private lemma idx7_0_inj0 : ∀ a b : Fin 6, idx7_0 0 a = idx7_0 0 b → a = b := by decide
private lemma idx7_1_inj0 : ∀ a b : Fin 6, idx7_1 0 a = idx7_1 0 b → a = b := by decide
private lemma idx7_0_ne : ∀ (z0 : Fin 7) (k0 : Fin 6), idx7_0 z0 k0 ≠ z0 := by decide
private lemma idx7_1_ne : ∀ (z0 : Fin 7) (k0 : Fin 6), idx7_1 z0 k0 ≠ z0 := by decide
private lemma idx7_0_surj : ∀ (z0 ix0 : Fin 7), ix0 ≠ z0 → ∃ k : Fin 6, idx7_0 z0 k = ix0 := by decide
private lemma idx7_1_surj : ∀ (z0 ix0 : Fin 7), ix0 ≠ z0 → ∃ k : Fin 6, idx7_1 z0 k = ix0 := by decide
private lemma idx7_0_ord0 : ∀ a b c : Fin 6, a < b → b < c →
    0 < (idx7_0 0 b - idx7_0 0 a).val ∧ (idx7_0 0 b - idx7_0 0 a).val < (idx7_0 0 c - idx7_0 0 a).val := by decide
private lemma idx7_1_ord0 : ∀ a b c : Fin 6, a < b → b < c →
    0 < (idx7_1 0 b - idx7_1 0 a).val ∧ (idx7_1 0 b - idx7_1 0 a).val < (idx7_1 0 c - idx7_1 0 a).val := by decide
private lemma idx7_0_nadj0 : ∀ i j : Fin 6, i.val % 2 = 1 → j.val % 2 = 1 → idx7_0 0 j ≠ idx7_0 0 i + 1 := by decide
private lemma idx7_1_nadj0 : ∀ i j : Fin 6, i.val % 2 = 1 → j.val % 2 = 1 → idx7_1 0 j ≠ idx7_1 0 i + 1 := by decide
private lemma idx7_0_nadj_z : ∀ (z : Fin 7) (i j : Fin 6), i.val % 2 = 1 → j.val % 2 = 1 → idx7_0 z j ≠ idx7_0 z i + 1 := by decide
private lemma idx7_1_nadj_z : ∀ (z : Fin 7) (i j : Fin 6), i.val % 2 = 1 → j.val % 2 = 1 → idx7_1 z j ≠ idx7_1 z i + 1 := by decide
private lemma idx7_1_elem : ∀ (d : ZMod 7) (c1 : Fin 3),
    toF7 (d + (((⟨2 * c1.val + 1, by omega⟩ : Fin 6).val + 1 : ℕ) : ZMod 7)) =
      idx7_1 (toF7 d) ⟨2 * c1.val, by omega⟩ := by decide
private lemma fin6_ev_pred_ne_succ : ∀ x : Fin 6, x.val % 2 = 0 → x - 1 ≠ x + 1 := by decide
private lemma fin6_pred_ne : ∀ x : Fin 6, x - 1 ≠ x := by decide
private lemma fin6_succ_ne : ∀ x : Fin 6, x + 1 ≠ x := by decide

private lemma idx7_anc0 : ∀ (d : ZMod 7) (c0 : Fin 3),
    let s : Fin 6 := ⟨2 * c0.val, by omega⟩
    d + toZ7 (idx7_0 0 (s - 1)) ∈ anchorsIn7Minus d s ∧
    d + toZ7 (idx7_0 0 (s + 1)) ∈ anchorsIn7Minus d s := by decide
private lemma idx7_anc1 : ∀ (d : ZMod 7) (c1 : Fin 3),
    let s : Fin 6 := ⟨2 * c1.val + 1, by omega⟩
    let s0 : Fin 6 := ⟨2 * c1.val, by omega⟩
    d + (((s.val + 1 : ℕ) : ZMod 7)) = d + toZ7 (idx7_1 0 s0) ∧
    d + toZ7 (idx7_1 0 (s0 - 1)) ∈ anchorsIn7Minus d s ∧
    d + toZ7 (idx7_1 0 (s0 + 1)) ∈ anchorsIn7Minus d s := by decide

/-- **Section 8.2 (`card_D_seven_M_le_two`, `upper_9.tex` lines 928–930)**:
    If `|D| = 7`, then `|M| = |S \ D| ≤ 2` (hence `|S| ≤ 9`). -/
theorem card_D_seven_M_le_two {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD7 : (hullVertices S \ certifiedVertices S w).card = 7) :
    (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card ≤ 2 := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  obtain ⟨cycD⟩ := exists_ccwCycle S D
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Finset.sdiff_subset) hD7
  have hto_inv : ∀ i : Fin 7, toF7 (toZ7 i) = i := fun i => by
    ext; simp [toF7, toZ7, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  have htoZ_inv : ∀ z : ZMod 7, toZ7 (toF7 z) = z := fun z => ZMod.natCast_zmod_val z
  have hidx0_inj : ∀ z : Fin 7, Function.Injective (idx7_0 z) := fun z a b hab => by
    apply idx7_0_inj0 a b
    have := congrArg (· - z) hab
    simpa [idx7_0] using this
  have hidx1_inj : ∀ z : Fin 7, Function.Injective (idx7_1 z) := fun z a b hab => by
    apply idx7_1_inj0 a b
    have := congrArg (· - z) hab
    simpa [idx7_1] using this
  have hidx0_img : ∀ z : Fin 7, Finset.univ.image (fun k => cycD.toFun (idx7_0 z k)) = D.erase (cycD.toFun z) := by
    intro z; ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨cycD.inj.ne (idx7_0_ne z k), ccwCycle_mem cycD _⟩
    · rintro ⟨hxne, hxD⟩
      obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cycD hxD
      obtain ⟨k, hk⟩ := idx7_0_surj z ix (fun h => hxne (congrArg cycD.toFun h))
      exact ⟨k, congrArg cycD.toFun hk⟩
  have hidx1_img : ∀ z : Fin 7, Finset.univ.image (fun k => cycD.toFun (idx7_1 z k)) = D.erase (cycD.toFun z) := by
    intro z; ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨cycD.inj.ne (idx7_1_ne z k), ccwCycle_mem cycD _⟩
    · rintro ⟨hxne, hxD⟩
      obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cycD hxD
      obtain ⟨k, hk⟩ := idx7_1_surj z ix (fun h => hxne (congrArg cycD.toFun h))
      exact ⟨k, congrArg cycD.toFun hk⟩
  have hidx0_ord : ∀ z : Fin 7, ∀ a b c : Fin 6, a < b → b < c →
      0 < (idx7_0 z b - idx7_0 z a).val ∧ (idx7_0 z b - idx7_0 z a).val < (idx7_0 z c - idx7_0 z a).val := by
    intro z a b c hab hbc
    have hdiff : ∀ x y : Fin 6, idx7_0 z x - idx7_0 z y = idx7_0 0 x - idx7_0 0 y := fun x y => by
      dsimp [idx7_0]; abel
    rw [hdiff b a, hdiff c a]
    exact idx7_0_ord0 a b c hab hbc
  have hidx1_ord : ∀ z : Fin 7, ∀ a b c : Fin 6, a < b → b < c →
      0 < (idx7_1 z b - idx7_1 z a).val ∧ (idx7_1 z b - idx7_1 z a).val < (idx7_1 z c - idx7_1 z a).val := by
    intro z a b c hab hbc
    have hdiff : ∀ x y : Fin 6, idx7_1 z x - idx7_1 z y = idx7_1 0 x - idx7_1 0 y := fun x y => by
      dsimp [idx7_1]; abel
    rw [hdiff b a, hdiff c a]
    exact idx7_1_ord0 a b c hab hbc
  let cyc0 : (z : Fin 7) → CCWCycle S (D.erase (cycD.toFun z)) 3 := fun z =>
    ccwCycle_of_sub_cyclic cycD (idx7_0 z) (hidx0_inj z) (hidx0_img z) (hidx0_ord z)
  let cyc1 : (z : Fin 7) → CCWCycle S (D.erase (cycD.toFun z)) 3 := fun z =>
    ccwCycle_of_sub_cyclic cycD (idx7_1 z) (hidx1_inj z) (hidx1_img z) (hidx1_ord z)
  have toF7_add : ∀ a b : ZMod 7, toF7 (a + b) = toF7 a + toF7 b := fun a b => by
    ext; simp [toF7, Fin.val_add, ZMod.val_add]
  have toF7_nat : ∀ k : ℕ, (hk : k < 7) → toF7 (k : ZMod 7) = ⟨k, hk⟩ := fun k hk => by
    ext; simp [toF7, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have idx0_nadj : ∀ z : Fin 7, ∀ i j : Fin 6, i.val % 2 = 1 → j.val % 2 = 1 →
      idx7_0 z j ≠ idx7_0 z i + 1 := idx7_0_nadj_z
  have idx1_nadj : ∀ z : Fin 7, ∀ i j : Fin 6, i.val % 2 = 1 → j.val % 2 = 1 →
      idx7_1 z j ≠ idx7_1 z i + 1 := idx7_1_nadj_z
  let goodTriple (z : Fin 7) (cyc : CCWCycle S (D.erase (cycD.toFun z)) 3) (ig : Fin 6) : Prop :=
    ig.val % 2 = 0 ∧
    (∃ O : Finset (Fin n), cyc.toFun ig ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B (cyc.toFun ig) (w (Finset.univ \ O))) ∧
    cyc.toFun (ig - 1) ∈ D ∧ cyc.toFun (ig + 1) ∈ D ∧ cyc.toFun (ig - 1) ≠ cyc.toFun (ig + 1) ∧
    cyc.toFun (ig - 1) ≠ cyc.toFun ig ∧ cyc.toFun (ig + 1) ≠ cyc.toFun ig ∧
    orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig)) ≠ 0 ∧
    (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cyc.toFun (ig - 1), cyc.toFun (ig + 1)} ∅ w)
      (S (cyc.toFun ig)) H_hp) ∧
    (∀ z' : Fin n, z' ∈ interiorPoints S →
      0 < orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig)) *
          orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S z') →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cyc.toFun (ig - 1), cyc.toFun (ig + 1)} ∅ w)
        (S z') H_hp)
  have extract_good : ∀ (z : Fin 7) (cyc : CCWCycle S (D.erase (cycD.toFun z)) 3)
      (hnadj : ∀ i j : Fin 6, i.val % 2 = 1 → j.val % 2 = 1 →
        ∀ a b : Fin n, a = cyc.toFun i → b = cyc.toFun j → ¬ IsCCWEdge S D a b),
      ∃ ig : Fin 6, goodTriple z cyc ig := by
    intro z cyc hnadj
    have hCD : D.erase (cycD.toFun z) ⊆ hullVertices S \ certifiedVertices S w := Finset.erase_subset _ _
    obtain ⟨Tgt, hcard, hTgt⟩ := good_targets hPoly h25 (Or.inl rfl) hCD cyc
    rw [if_pos rfl] at hcard
    obtain ⟨ig, hig_mem⟩ := Finset.card_pos.mp (by omega : 0 < Tgt.card)
    obtain ⟨hig_ev, _, hbackB, _, _, hhp, hside⟩ := hTgt ig hig_mem
    let O_miss := (D.erase (cycD.toFun z)).filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cyc.toFun i = x)
    have hO_nmem : cyc.toFun ig ∉ O_miss := by
      intro hm; rcases (Finset.mem_filter.mp hm).2 with ⟨j, hj, heq⟩
      have := cyc.inj heq; rw [this] at hj; omega
    have hO_D : ∀ a ∈ O_miss ∩ D, ∀ b ∈ O_miss ∩ D, ¬ IsCCWEdge S B a b := by
      intro a ha b hb
      rcases (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2 with ⟨ia, hia, rfl⟩
      rcases (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2 with ⟨ib, hib, rfl⟩
      apply nonadj_D_implies_nonadj_B h25 (by dsimp [D, B, H] at *; omega : 3 ≤ D.card)
        (Finset.erase_subset _ _ (ccwCycle_mem cyc ia))
        (Finset.erase_subset _ _ (ccwCycle_mem cyc ib))
      exact hnadj ia ib hia hib _ _ rfl rfl
    have hm1B : cyc.toFun (ig - 1) ∈ D := Finset.erase_subset _ _ (ccwCycle_mem cyc (ig - 1))
    have hp1B : cyc.toFun (ig + 1) ∈ D := Finset.erase_subset _ _ (ccwCycle_mem cyc (ig + 1))
    have hne1 : ig - 1 ≠ ig + 1 := fin6_ev_pred_ne_succ ig hig_ev
    have hne2 : ig - 1 ≠ ig := fin6_pred_ne ig
    have hne3 : ig + 1 ≠ ig := fin6_succ_ne ig
    have hnoncol : orient2D (S (cyc.toFun (ig - 1))) (S (cyc.toFun (ig + 1))) (S (cyc.toFun ig)) ≠ 0 :=
      hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (Or.inl (Set.mem_range_self _)) (hPoly.s_inj.ne (cyc.inj.ne hne1))
        (hPoly.s_inj.ne (cyc.inj.ne hne3)) (hPoly.s_inj.ne (cyc.inj.ne hne2))
    refine ⟨ig, hig_ev, ⟨O_miss, hO_nmem, hO_D, hbackB⟩, hm1B, hp1B, cyc.inj.ne hne1,
      cyc.inj.ne hne2, cyc.inj.ne hne3, hnoncol, hhp, fun z' hz'A hz_side => ?_⟩
    have hz'_nD : z' ∉ B := (Finset.mem_sdiff.mp hz'A).2
    have hz'_nO : z' ∉ O_miss := fun h => hz'_nD (Finset.sdiff_subset (Finset.erase_subset _ _ (Finset.mem_filter.mp h).1))
    have hz'_conv := mem_convexHull_hullVertices S hPoly.s_inj z'
    exact (hside z' (fun h => hz'_nD (Finset.sdiff_subset (h ▸ hm1B)))
      (fun h => hz'_nD (Finset.sdiff_subset (h ▸ hp1B))) hz'_nO hz'_conv hz_side).2.1
  have hgood0 : ∀ z : Fin 7, ∃ ig : Fin 6, goodTriple z (cyc0 z) ig := fun z =>
    extract_good z (cyc0 z) (fun i j hi hj a b ha hb hed => by
      subst ha; subst hb; rw [isCCWEdge_iff_ccwCycle cycD] at hed
      rcases hed with ⟨r, hr1, hr2⟩
      have hi1 : r = idx7_0 z i := cycD.inj (hr1.symm : cycD.toFun r = cycD.toFun (idx7_0 z i))
      have hi2 : r + 1 = idx7_0 z j := cycD.inj (hr2.symm : cycD.toFun (r + 1) = cycD.toFun (idx7_0 z j))
      apply idx0_nadj z i j hi hj; rw [← hi2, ← hi1])
  have hgood1 : ∀ z : Fin 7, ∃ ig : Fin 6, goodTriple z (cyc1 z) ig := fun z =>
    extract_good z (cyc1 z) (fun i j hi hj a b ha hb hed => by
      subst ha; subst hb; rw [isCCWEdge_iff_ccwCycle cycD] at hed
      rcases hed with ⟨r, hr1, hr2⟩
      have hi1 : r = idx7_1 z i := cycD.inj (hr1.symm : cycD.toFun r = cycD.toFun (idx7_1 z i))
      have hi2 : r + 1 = idx7_1 z j := cycD.inj (hr2.symm : cycD.toFun (r + 1) = cycD.toFun (idx7_1 z j))
      apply idx1_nadj z i j hi hj; rw [← hi2, ← hi1])
  choose ig0 hig0 using hgood0
  choose ig1 hig1 using hgood1
  let choice0 : ZMod 7 → Fin 3 := fun d => ⟨(ig0 (toF7 d)).val / 2, by have := (ig0 (toF7 d)).isLt; omega⟩
  let choice1 : ZMod 7 → Fin 3 := fun d => ⟨(ig1 (toF7 d)).val / 2, by have := (ig1 (toF7 d)).isLt; omega⟩
  obtain ⟨d1, b1, d2, b2, hp12, _, _, hp2_na1, hp1_na2⟩ := seven_cycle_lemma choice0 choice1
  let off := fun (d : ZMod 7) (b : Bool) =>
    if b then (⟨2 * (choice1 d).val + 1, by omega⟩ : Fin 6) else ⟨2 * (choice0 d).val, by omega⟩
  let elemZ := fun (d : ZMod 7) (b : Bool) => d + (((off d b).val + 1 : ℕ) : ZMod 7)
  let ancZ := fun (d : ZMod 7) (b : Bool) => anchorsIn7Minus d (off d b)
  have hgood_extract : ∀ (d : ZMod 7) (b : Bool),
      ∃ a c : ZMod 7, a ∈ ancZ d b ∧ c ∈ ancZ d b ∧ a ≠ c ∧
        a ≠ elemZ d b ∧ c ≠ elemZ d b ∧
        (∃ O : Finset (Fin n), cycD.toFun (toF7 (elemZ d b)) ∉ O ∧
          (∀ x ∈ O ∩ D, ∀ y ∈ O ∩ D, ¬ IsCCWEdge S B x y) ∧
          IsBackVertexOf S B (cycD.toFun (toF7 (elemZ d b))) (w (Finset.univ \ O))) ∧
        orient2D (S (cycD.toFun (toF7 a))) (S (cycD.toFun (toF7 c))) (S (cycD.toFun (toF7 (elemZ d b)))) ≠ 0 ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P
          (WitnessSet {cycD.toFun (toF7 a), cycD.toFun (toF7 c)} ∅ w)
          (S (cycD.toFun (toF7 (elemZ d b)))) H_hp) ∧
        (∀ z' : Fin n, z' ∈ interiorPoints S →
          0 < orient2D (S (cycD.toFun (toF7 a))) (S (cycD.toFun (toF7 c))) (S (cycD.toFun (toF7 (elemZ d b)))) *
              orient2D (S (cycD.toFun (toF7 a))) (S (cycD.toFun (toF7 c))) (S z') →
          ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P
            (WitnessSet {cycD.toFun (toF7 a), cycD.toFun (toF7 c)} ∅ w) (S z') H_hp) := by
    intro d b
    cases b
    · have ht := hig0 (toF7 d)
      rcases ht with ⟨hev, hback, _, _, hne_ac, hne_ap, hne_cp, hnoncol, hhp, hside⟩
      let s : Fin 6 := ⟨2 * (choice0 d).val, by omega⟩
      have hs_eq : s = ig0 (toF7 d) := by ext; dsimp [s, choice0]; omega
      have h_elem : toF7 (elemZ d false) = idx7_0 (toF7 d) (ig0 (toF7 d)) := by
        dsimp [elemZ, off, idx7_0]; rw [toF7_add, ← hs_eq]
        congr 1; apply toF7_nat
      have ha_eq : toF7 (d + toZ7 (idx7_0 0 (s - 1))) = idx7_0 (toF7 d) (ig0 (toF7 d) - 1) := by
        rw [toF7_add, hto_inv, ← hs_eq]; dsimp [idx7_0]; simp only [zero_add]
      have hc_eq : toF7 (d + toZ7 (idx7_0 0 (s + 1))) = idx7_0 (toF7 d) (ig0 (toF7 d) + 1) := by
        rw [toF7_add, hto_inv, ← hs_eq]; dsimp [idx7_0]; simp only [zero_add]
      have hanc := idx7_anc0 d (choice0 d)
      refine ⟨d + toZ7 (idx7_0 0 (s - 1)), d + toZ7 (idx7_0 0 (s + 1)), hanc.1, hanc.2,
        fun h => hne_ac (congrArg cycD.toFun (by rw [← ha_eq, ← hc_eq, h])),
        fun h => hne_ap (congrArg cycD.toFun (by rw [← ha_eq, ← h_elem, h])),
        fun h => hne_cp (congrArg cycD.toFun (by rw [← hc_eq, ← h_elem, h])), ?_⟩
      change _ at hback hnoncol hhp hside
      have h_el_f : cycD.toFun (toF7 (elemZ d false)) = (cyc0 (toF7 d)).toFun (ig0 (toF7 d)) := by
        rw [h_elem]; rfl
      have h_f1 : cycD.toFun (toF7 (d + toZ7 (idx7_0 0 (s - 1)))) = (cyc0 (toF7 d)).toFun (ig0 (toF7 d) - 1) := by
        rw [ha_eq]; rfl
      have h_f2 : cycD.toFun (toF7 (d + toZ7 (idx7_0 0 (s + 1)))) = (cyc0 (toF7 d)).toFun (ig0 (toF7 d) + 1) := by
        rw [hc_eq]; rfl
      rw [h_el_f, h_f1, h_f2]
      exact ⟨hback, hnoncol, hhp, hside⟩
    · have ht := hig1 (toF7 d)
      rcases ht with ⟨hev, hback, _, _, hne_ac, hne_ap, hne_cp, hnoncol, hhp, hside⟩
      let s0 : Fin 6 := ⟨2 * (choice1 d).val, by omega⟩
      have hs_eq : s0 = ig1 (toF7 d) := by ext; dsimp [s0, choice1]; omega
      obtain ⟨_, h_a0, h_c0⟩ := idx7_anc1 d (choice1 d)
      have h_elem : toF7 (elemZ d true) = idx7_1 (toF7 d) (ig1 (toF7 d)) := by
        dsimp [elemZ, off]
        exact (idx7_1_elem d (choice1 d)).trans (congrArg (idx7_1 (toF7 d)) (by dsimp [s0] at hs_eq; exact hs_eq))
      have ha_eq : toF7 (d + toZ7 (idx7_1 0 (s0 - 1))) = idx7_1 (toF7 d) (ig1 (toF7 d) - 1) := by
        rw [toF7_add, hto_inv, ← hs_eq]; dsimp [idx7_1]; simp only [zero_add]
      have hc_eq : toF7 (d + toZ7 (idx7_1 0 (s0 + 1))) = idx7_1 (toF7 d) (ig1 (toF7 d) + 1) := by
        rw [toF7_add, hto_inv, ← hs_eq]; dsimp [idx7_1]; simp only [zero_add]
      refine ⟨d + toZ7 (idx7_1 0 (s0 - 1)), d + toZ7 (idx7_1 0 (s0 + 1)), h_a0, h_c0,
        fun h => hne_ac (congrArg cycD.toFun (by rw [← ha_eq, ← hc_eq, h])),
        fun h => hne_ap (congrArg cycD.toFun (by rw [← ha_eq, ← h_elem, h])),
        fun h => hne_cp (congrArg cycD.toFun (by rw [← hc_eq, ← h_elem, h])), ?_⟩
      have h_el_f : cycD.toFun (toF7 (elemZ d true)) = (cyc1 (toF7 d)).toFun (ig1 (toF7 d)) := by
        rw [h_elem]; rfl
      have h_f1 : cycD.toFun (toF7 (d + toZ7 (idx7_1 0 (s0 - 1)))) = (cyc1 (toF7 d)).toFun (ig1 (toF7 d) - 1) := by
        rw [ha_eq]; rfl
      have h_f2 : cycD.toFun (toF7 (d + toZ7 (idx7_1 0 (s0 + 1)))) = (cyc1 (toF7 d)).toFun (ig1 (toF7 d) + 1) := by
        rw [hc_eq]; rfl
      rw [h_el_f, h_f1, h_f2]
      exact ⟨hback, hnoncol, hhp, hside⟩
  obtain ⟨a1, c1, ha1_anc, hc1_anc, ha1_c1, ha1_ne, hc1_ne, hBack1, hnoncol1, hhp1, hside1⟩ := hgood_extract d1 b1
  obtain ⟨a2, c2, ha2_anc, hc2_anc, ha2_c2, ha2_ne, hc2_ne, hBack2, hnoncol2, hhp2, hside2⟩ := hgood_extract d2 b2
  let p1 := cycD.toFun (toF7 (elemZ d1 b1))
  let p2 := cycD.toFun (toF7 (elemZ d2 b2))
  have hp12_n : p1 ≠ p2 := cycD.inj.ne fun h => hp12 (by
    have := congrArg toZ7 h; rwa [htoZ_inv, htoZ_inv] at this)
  let anchors : Fin n → Fin n × Fin n := fun x =>
    if x = p1 then (cycD.toFun (toF7 a1), cycD.toFun (toF7 c1))
    else (cycD.toFun (toF7 a2), cycD.toFun (toF7 c2))
  refine combination_M_le_two_of_pureD_anchors hPoly h25 hp12_n
    (ccwCycle_mem cycD _) (ccwCycle_mem cycD _) (by dsimp [D, B, H] at *; omega)
    (fun q hq => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption)
    anchors
    (fun p hp => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · simp only [anchors, ↓reduceIte]
        have ha1_n2 : a1 ≠ elemZ d2 b2 := fun h => by
          have ha' : elemZ d2 b2 ∈ ancZ d1 b1 := h ▸ ha1_anc
          exact hp2_na1 ha'
        have hc1_n2 : c1 ≠ elemZ d2 b2 := fun h => by
          have hc' : elemZ d2 b2 ∈ ancZ d1 b1 := h ▸ hc1_anc
          exact hp2_na1 hc'
        refine ⟨Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, ?_⟩,
          Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, ?_⟩,
          cycD.inj.ne fun h => ha1_c1 (by simpa [htoZ_inv] using congrArg toZ7 h),
          hnoncol1, hhp1, hside1⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨cycD.inj.ne fun h => ha1_ne (by simpa [htoZ_inv] using congrArg toZ7 h),
                 cycD.inj.ne fun h => ha1_n2 (by simpa [htoZ_inv] using congrArg toZ7 h)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨cycD.inj.ne fun h => hc1_ne (by simpa [htoZ_inv] using congrArg toZ7 h),
                 cycD.inj.ne fun h => hc1_n2 (by simpa [htoZ_inv] using congrArg toZ7 h)⟩
      · simp only [anchors, if_neg hp12_n.symm]
        have ha2_n1 : a2 ≠ elemZ d1 b1 := fun h => by
          have ha' : elemZ d1 b1 ∈ ancZ d2 b2 := h ▸ ha2_anc
          exact hp1_na2 ha'
        have hc2_n1 : c2 ≠ elemZ d1 b1 := fun h => by
          have hc' : elemZ d1 b1 ∈ ancZ d2 b2 := h ▸ hc2_anc
          exact hp1_na2 hc'
        refine ⟨Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, ?_⟩,
          Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, ?_⟩,
          cycD.inj.ne fun h => ha2_c2 (by simpa [htoZ_inv] using congrArg toZ7 h),
          hnoncol2, hhp2, hside2⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨cycD.inj.ne fun h => ha2_n1 (by simpa [htoZ_inv] using congrArg toZ7 h),
                 cycD.inj.ne fun h => ha2_ne (by simpa [htoZ_inv] using congrArg toZ7 h)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨cycD.inj.ne fun h => hc2_n1 (by simpa [htoZ_inv] using congrArg toZ7 h),
                 cycD.inj.ne fun h => hc2_ne (by simpa [htoZ_inv] using congrArg toZ7 h)⟩)


/-! ## Part 3: Plane Reflection, Shared Section 7 Covering Helpers, and Section 8.3 (`|D| = 6 → |M| ≤ 3`) -/

private def reflPt (p : ℝ × ℝ) : ℝ × ℝ := (p.1, -p.2)

private lemma reflPt_invol (p : ℝ × ℝ) : reflPt (reflPt p) = p := by
  ext <;> simp [reflPt]

private lemma reflPt_inj : Function.Injective reflPt := by
  intro a b h
  have := congrArg reflPt h
  simpa [reflPt_invol] using this

private lemma reflPt_orient2D (a b c : ℝ × ℝ) :
    orient2D (reflPt a) (reflPt b) (reflPt c) = - orient2D a b c := by
  unfold orient2D reflPt; ring

private lemma reflPt_inIntTri (a b c z : ℝ × ℝ) :
    InIntTri (reflPt a) (reflPt b) (reflPt c) (reflPt z) ↔ InIntTri a b c z := by
  constructor <;> rintro ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, hz1, hz2⟩
  · refine ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, ?_, ?_⟩
    · simpa [reflPt] using hz1
    · dsimp [reflPt] at hz2; linarith
  · refine ⟨μ₁, μ₂, μ₃, h1, h2, h3, hsum, ?_, ?_⟩
    · simpa [reflPt] using hz1
    · dsimp [reflPt]; linarith

private def reflLin : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := reflPt
  map_add' x y := by ext <;> dsimp [reflPt] <;> ring
  map_smul' r x := by ext <;> dsimp [reflPt] <;> ring
  invFun := reflPt
  left_inv := reflPt_invol
  right_inv := reflPt_invol

private lemma reflPt_image_segment (x y : ℝ × ℝ) :
    reflPt '' segment ℝ x y = segment ℝ (reflPt x) (reflPt y) := by
  rw [segment_eq_image, segment_eq_image]
  ext p
  simp only [Set.mem_image, reflPt, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk]
  constructor
  · rintro ⟨q, ⟨t, ht, hq⟩, rfl⟩
    refine ⟨t, ht, Prod.ext ?_ ?_⟩
    · have := congrArg Prod.fst hq; dsimp at this; linarith
    · have := congrArg Prod.snd hq; dsimp at this; linarith
  · rintro ⟨t, ht, hp⟩
    refine ⟨((1 - t) * x.1 + t * y.1, (1 - t) * x.2 + t * y.2), ⟨t, ht, rfl⟩, Prod.ext ?_ ?_⟩
    · have := congrArg Prod.fst hp; dsimp at this; linarith
    · have := congrArg Prod.snd hp; dsimp at this; linarith

private lemma reflPt_image_convexHull (s : Set (ℝ × ℝ)) :
    reflPt '' convexHull ℝ s = convexHull ℝ (reflPt '' s) := by
  change ⇑reflLin.toAffineMap '' convexHull ℝ s = convexHull ℝ (⇑reflLin.toAffineMap '' s)
  exact AffineMap.image_convexHull reflLin.toAffineMap s

private lemma reflPt_sees (P : Set (ℝ × ℝ)) (x y : ℝ × ℝ) :
    Sees (reflPt '' P) (reflPt x) (reflPt y) ↔ Sees P x y := by
  unfold Sees
  rw [← reflPt_image_segment]
  exact Set.image_subset_image_iff reflPt_inj

private def reflHP (H : OpenHalfPlane) : OpenHalfPlane where
  n := (H.n.1, -H.n.2)
  c := H.c
  hn := by
    rcases H.hn with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (neg_ne_zero.mpr h2)

private lemma reflHP_memPos (H : OpenHalfPlane) (p : ℝ × ℝ) :
    (reflHP H).MemPos (reflPt p) ↔ H.MemPos p := by
  dsimp [OpenHalfPlane.MemPos, reflHP, reflPt]
  ring_nf

private lemma reflHP_memNeg (H : OpenHalfPlane) (p : ℝ × ℝ) :
    (reflHP H).MemNeg (reflPt p) ↔ H.MemNeg p := by
  dsimp [OpenHalfPlane.MemNeg, reflHP, reflPt]
  ring_nf

private lemma reflHP_invol (H : OpenHalfPlane) : reflHP (reflHP H) = H := by
  cases H; simp [reflHP]

private def reflWedge (R : OpenWedge) : OpenWedge where
  y := reflPt R.y
  u₁ := reflPt R.u₂
  u₂ := reflPt R.u₁
  h_nondeg := by
    dsimp [reflPt]
    linarith [R.h_nondeg]

private lemma reflWedge_memOpen (R : OpenWedge) (p : ℝ × ℝ) :
    (reflWedge R).MemOpen (reflPt p) ↔ R.MemOpen p := by
  dsimp [OpenWedge.MemOpen, reflWedge, reflPt]
  ring_nf; exact and_comm

private lemma reflWedge_memExt (R : OpenWedge) (p : ℝ × ℝ) :
    (reflWedge R).MemExt (reflPt p) ↔ R.MemExt p := by
  dsimp [OpenWedge.MemExt, reflWedge, reflPt]
  ring_nf; exact or_comm

private lemma reflWedge_invol (R : OpenWedge) : reflWedge (reflWedge R) = R := by
  cases R; simp [reflWedge, reflPt_invol]

private lemma reflPt_witnessSet {n : ℕ} (F N : Finset (Fin n)) (w : Finset (Fin n) → ℝ × ℝ) :
    WitnessSet F N (reflPt ∘ w) = reflPt '' WitnessSet F N w := by
  ext x
  simp only [WitnessSet, Set.mem_setOf_eq, Set.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨T, hFT, hTN, rfl⟩; exact ⟨w T, ⟨T, hFT, hTN, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨T, hFT, hTN, rfl⟩, rfl⟩; exact ⟨T, hFT, hTN, rfl⟩

private lemma reflPt_isHalfPlaneTest {P : Set (ℝ × ℝ)} {W' : Set (ℝ × ℝ)} {a : ℝ × ℝ}
    {H : OpenHalfPlane} (h : IsHalfPlaneTest P W' a H) :
    IsHalfPlaneTest (reflPt '' P) (reflPt '' W') (reflPt a) (reflHP H) := by
  rintro x ⟨y, hy, rfl⟩
  have := h y hy
  rwa [reflHP_memPos, reflHP_memNeg, reflPt_sees]

private lemma reflPt_isWedgeTest {P : Set (ℝ × ℝ)} {W' : Set (ℝ × ℝ)} {a : ℝ × ℝ}
    {R : OpenWedge} (h : IsWedgeTest P W' a R) :
    IsWedgeTest (reflPt '' P) (reflPt '' W') (reflPt a) (reflWedge R) := by
  rintro x ⟨y, hy, rfl⟩
  have := h y hy
  rwa [reflWedge_memOpen, reflWedge_memExt, reflPt_sees]

private lemma reflPt_hullVertices {n : ℕ} (S : Fin n → ℝ × ℝ) :
    hullVertices (reflPt ∘ S) = hullVertices S := by
  ext i
  simp only [hullVertices, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  have himg : (((Finset.univ.erase i).image (reflPt ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
      reflPt '' (((Finset.univ.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    ext x; simp
  rw [himg, ← reflPt_image_convexHull]
  refine not_congr ⟨fun ⟨y, hy, hyx⟩ => reflPt_inj hyx ▸ hy, fun hx => ⟨S i, hx, rfl⟩⟩

private lemma reflPt_interiorPoints {n : ℕ} (S : Fin n → ℝ × ℝ) :
    interiorPoints (reflPt ∘ S) = interiorPoints S := by
  simp [interiorPoints, reflPt_hullVertices]

private lemma reflPt_isConvexPos {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) :
    IsConvexPos (reflPt ∘ S) C ↔ IsConvexPos S C := by
  constructor <;> intro h i hi hmem <;> apply h i hi
  · have himg : (((C.erase i).image (reflPt ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
        reflPt '' (((C.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by ext x; simp
    rw [himg, ← reflPt_image_convexHull]
    exact ⟨S i, hmem, rfl⟩
  · have himg : (((C.erase i).image (reflPt ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
        reflPt '' (((C.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by ext x; simp
    rw [himg, ← reflPt_image_convexHull] at hmem
    rcases hmem with ⟨y, hy, hyx⟩
    rwa [← reflPt_inj hyx]

private lemma reflPt_isCCWEdge {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (a b : Fin n) :
    IsCCWEdge (reflPt ∘ S) C a b ↔ IsCCWEdge S C b a := by
  constructor <;> rintro ⟨ha, hb, hab, hall⟩ <;> refine ⟨hb, ha, hab.symm, fun r hr hrb hra => ?_⟩
  · have h := hall r hr hra hrb
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, reflPt_orient2D] at h
    unfold orient2D at h ⊢; linarith
  · have h := hall r hr hra hrb
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, reflPt_orient2D]
    unfold orient2D at h ⊢; linarith

private lemma reflPt_isFrontVertexOf {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (f : Fin n)
    (v : ℝ × ℝ) :
    IsFrontVertexOf (reflPt ∘ S) C f (reflPt v) ↔ IsFrontVertexOf S C f v := by
  constructor <;> rintro ⟨hf, hall⟩ <;> refine ⟨hf, fun a b hed heq => ?_⟩
  · rw [← reflPt_isCCWEdge S C b a] at hed
    have h := hall b a hed (heq.symm)
    rw [Function.comp_apply, Function.comp_apply, reflPt_orient2D] at h
    unfold orient2D at h ⊢; linarith
  · rw [reflPt_isCCWEdge] at hed
    have h := hall b a hed (heq.symm)
    rw [Function.comp_apply, Function.comp_apply, reflPt_orient2D]
    unfold orient2D at h ⊢; linarith

private lemma reflPt_isBackVertexOf {n : ℕ} (S : Fin n → ℝ × ℝ) (C : Finset (Fin n)) (p : Fin n)
    (v : ℝ × ℝ) :
    IsBackVertexOf (reflPt ∘ S) C p (reflPt v) ↔ IsBackVertexOf S C p v := by
  constructor <;> rintro ⟨hp, hall⟩ <;> refine ⟨hp, fun a b hed heq => ?_⟩
  · rw [← reflPt_isCCWEdge S C b a] at hed
    have h := hall b a hed (heq.symm)
    rw [Function.comp_apply, Function.comp_apply, reflPt_orient2D] at h
    unfold orient2D at h ⊢; linarith
  · rw [reflPt_isCCWEdge] at hed
    have h := hall b a hed (heq.symm)
    rw [Function.comp_apply, Function.comp_apply, reflPt_orient2D]
    unfold orient2D at h ⊢; linarith

private lemma reflPt_certifiedVertices {n : ℕ} (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) :
    certifiedVertices (reflPt ∘ S) (reflPt ∘ w) = certifiedVertices S w := by
  ext f
  simp only [certifiedVertices, reflPt_hullVertices, Finset.mem_filter]
  refine and_congr_right fun _ => exists_congr fun T => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hb, hc, hf⟩
    exact ⟨fun b h => hc b ((reflPt_isCCWEdge S _ f b).mpr h),
           fun c h => hb c ((reflPt_isCCWEdge S _ c f).mpr h),
           (reflPt_isFrontVertexOf S _ f (w T)).mp hf⟩
  · rintro ⟨hb, hc, hf⟩
    exact ⟨fun b h => hc b ((reflPt_isCCWEdge S _ b f).mp h),
           fun c h => hb c ((reflPt_isCCWEdge S _ f c).mp h),
           (reflPt_isFrontVertexOf S _ f (w T)).mpr hf⟩

private lemma reflPt_shattered {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hPoly : ShatteredSimplePolygon P S w) :
    ShatteredSimplePolygon (reflPt '' P) (reflPt ∘ S) (reflPt ∘ w) where
  s_in_P i := Set.mem_image_of_mem reflPt (hPoly.s_in_P i)
  w_in_P T := Set.mem_image_of_mem reflPt (hPoly.w_in_P T)
  shatters T i := by rw [Function.comp_apply, Function.comp_apply, reflPt_sees]; exact hPoly.shatters T i
  s_inj a b h := hPoly.s_inj (reflPt_inj h)
  w_inj a b h := hPoly.w_inj (reflPt_inj h)
  s_ne_w i T h := hPoly.s_ne_w i T (reflPt_inj h)
  no_three_collinear := by
    rintro p q r hp hq hr hpq hqr hpr
    have hpull : ∀ x ∈ Set.range (reflPt ∘ S) ∪ Set.range (reflPt ∘ w),
        ∃ x0 ∈ Set.range S ∪ Set.range w, x = reflPt x0 := by
      rintro x (⟨i, rfl⟩ | ⟨T, rfl⟩)
      · exact ⟨S i, Or.inl ⟨i, rfl⟩, rfl⟩
      · exact ⟨w T, Or.inr ⟨T, rfl⟩, rfl⟩
    obtain ⟨p0, hp0, rfl⟩ := hpull p hp
    obtain ⟨q0, hq0, rfl⟩ := hpull q hq
    obtain ⟨r0, hr0, rfl⟩ := hpull r hr
    rw [reflPt_orient2D]
    exact neg_ne_zero.mpr (hPoly.no_three_collinear p0 q0 r0 hp0 hq0 hr0
      (fun h => hpq (congrArg reflPt h)) (fun h => hqr (congrArg reflPt h)) (fun h => hpr (congrArg reflPt h)))
  open_vis_nbhd T hT := by
    obtain ⟨ε, hε, hnb⟩ := hPoly.open_vis_nbhd T hT
    refine ⟨ε, hε, fun u hu => ?_⟩
    have hu' : dist (reflPt u) (w T) < ε := by
      have hd : dist (reflPt u) (w T) = dist u (reflPt (w T)) := by
        dsimp [Prod.dist_eq, Real.dist_eq, reflPt]
        refine congrArg (max |u.1 - (w T).1|) ?_
        rw [← abs_neg (-u.2 - (w T).2)]
        congr 1; ring
      exact hd ▸ hu
    obtain ⟨hP', hsees⟩ := hnb (reflPt u) hu'
    refine ⟨⟨reflPt u, hP', reflPt_invol u⟩, fun i hi => ?_⟩
    have hs := hsees i hi
    dsimp [Function.comp]
    conv_lhs => rw [← reflPt_invol u]
    exact (reflPt_sees P (reflPt u) (S i)).mpr hs
  triangle_enclosure := by
    rintro _ ⟨x, hxP, rfl⟩ _ ⟨y, hyP, rfl⟩ _ ⟨z, hzP, rfl⟩ hxy hyz hxz
    rw [reflPt_sees] at hxy hyz hxz
    have himg : ({reflPt x, reflPt y, reflPt z} : Set (ℝ × ℝ)) = reflPt '' {x, y, z} := by
      ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨x, Or.inl rfl, rfl⟩
        · exact ⟨y, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨z, Or.inr (Or.inr rfl), rfl⟩
      · rintro ⟨a, rfl | rfl | rfl, rfl⟩ <;> tauto
    rw [himg, ← reflPt_image_convexHull]
    exact Set.image_mono (hPoly.triangle_enclosure x hxP y hyP z hzP hxy hyz hxz)
  two_path_enclosure := by
    rintro s t π₁ π₂ hst hP1 hP2 hL1 hR2
    have hpull : ∀ π, IsPolygonalPathIn (reflPt '' P) s t π →
        IsPolygonalPathIn P (reflPt s) (reflPt t) (π.map reflPt) := by
      rintro π ⟨hne, hh, hl, hPπ, hch⟩
      refine ⟨mt List.map_eq_nil_iff.mp hne, ?_, ?_, ?_, ?_⟩
      · rw [List.head_map, hh]
      · rw [List.getLast_map, hl]
      · intro w hw
        rw [List.mem_map] at hw
        rcases hw with ⟨u, hu, rfl⟩
        rcases hPπ u hu with ⟨v, hv, rfl⟩
        rwa [reflPt_invol]
      · exact List.isChain_map_of_isChain _ (fun u v huv => by
          have := (reflPt_sees P (reflPt u) (reflPt v)).mp
          rw [reflPt_invol, reflPt_invol] at this
          exact this huv) hch
    have hL' : InteriorOnRight (reflPt s) (reflPt t) (π₁.map reflPt) := by
      refine ⟨by simpa using hL1.1, fun k hk hk0 hk1 => ?_⟩
      rw [List.getElem_map, reflPt_orient2D]
      exact neg_lt_zero.mpr (hL1.2 k (by simpa using hk) hk0 (by simpa using hk1))
    have hR' : InteriorOnLeft (reflPt s) (reflPt t) (π₂.map reflPt) := by
      refine ⟨by simpa using hR2.1, fun k hk hk0 hk1 => ?_⟩
      rw [List.getElem_map, reflPt_orient2D]
      exact neg_pos.mpr (hR2.2 k (by simpa using hk) hk0 (by simpa using hk1))
    have hs := hPoly.two_path_enclosure (reflPt s) (reflPt t) (π₂.map reflPt) (π₁.map reflPt)
      (fun h => hst (reflPt_inj h)) (hpull π₂ hP2) (hpull π₁ hP1) hR' hL'
    rw [← reflPt_sees P (reflPt s) (reflPt t), reflPt_invol, reflPt_invol] at hs
    exact hs
  gk14_no_ten_convex B hB := hPoly.gk14_no_ten_convex B (fun i hi hmem => by
    apply hB i hi
    have himg : (((B.erase i).image (reflPt ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) =
        reflPt '' (((B.erase i).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by ext x; simp
    rw [himg, ← reflPt_image_convexHull]
    exact ⟨S i, hmem, rfl⟩)
  isler_six_wedges R hR := by
    apply hPoly.isler_six_wedges (fun i => reflWedge (R i))
    intro m
    obtain ⟨p, hp⟩ := hR m
    refine ⟨reflPt p, fun i => ?_⟩
    have := hp i
    by_cases hmi : m i <;> simp only [hmi, ↓reduceIte, Bool.false_eq_true] at this ⊢
    · rwa [reflWedge_memOpen]
    · rwa [reflWedge_memExt]

private lemma reflPt_sec2to5 {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hPoly : ShatteredSimplePolygon P S w)
    (h25 : Sec2To5Interface P S w) :
    Sec2To5Interface (reflPt '' P) (reflPt ∘ S) (reflPt ∘ w) where
  three_halfplanes H hH := by
    apply h25.three_halfplanes (fun i => reflHP (H i))
    intro m
    obtain ⟨p, hp⟩ := hH m
    refine ⟨reflPt p, fun i => ?_⟩
    have := hp i
    by_cases hmi : m i <;> simp only [hmi, ↓reduceIte, Bool.false_eq_true] at this ⊢
    · rwa [reflHP_memPos]
    · rwa [reflHP_memNeg]
  two_hp_three_wedges H R hHR := by
    apply h25.two_hp_three_wedges (fun i => reflHP (H i)) (fun j => reflWedge (R j))
    intro mH mW
    obtain ⟨p, hpH, hpW⟩ := hHR mH mW
    refine ⟨reflPt p, fun i => ?_, fun j => ?_⟩
    · have := hpH i
      by_cases hmi : mH i <;> simp only [hmi, ↓reduceIte, Bool.false_eq_true] at this ⊢
      · rwa [reflHP_memPos]
      · rwa [reflHP_memNeg]
    · have := hpW j
      by_cases hmj : mW j <;> simp only [hmj, ↓reduceIte, Bool.false_eq_true] at this ⊢
      · rwa [reflWedge_memOpen]
      · rwa [reflWedge_memExt]
  cone_lemma := by
    rintro _ _ _ _ _ ⟨a, haP, rfl⟩ ⟨b, hbP, rfl⟩ ⟨c, hcP, rfl⟩ ⟨w0, hwP, rfl⟩ ⟨x, hxP, rfl⟩
      hwb hwc hwa hin hxb hxc hab hac hwa_ne
    rw [reflPt_sees] at hwb hwc hwa hxb hxc
    rw [reflPt_inIntTri] at hin
    rw [reflPt_orient2D] at hab hac hwa_ne
    rw [reflPt_inIntTri]
    exact h25.cone_lemma a b c w0 x haP hbP hcP hwP hxP hwb hwc hwa hin hxb hxc
      (neg_ne_zero.mp hab) (neg_ne_zero.mp hac) (neg_ne_zero.mp hwa_ne)
  wedge_extraction a b c W' U hab hac hbc hW_sub hUy hU_sep hU_see := by
    let W0 : Set (ℝ × ℝ) := reflPt '' W'
    let U0 : OpenWedge := reflWedge U
    have hW0_sub : W0 ⊆ WitnessSet {b, c} ∅ w := by
      rintro _ ⟨x, hx, rfl⟩
      have hxs := hW_sub hx
      rw [reflPt_witnessSet] at hxs
      rcases hxs with ⟨z, hz, hzx⟩
      have heq : reflPt x = z := by rw [← hzx, reflPt_invol]
      rwa [heq]
    have hU0_y : U0.y = S a := by
      dsimp [U0, reflWedge]; rw [hUy, Function.comp_apply, reflPt_invol]
    have hU0_sep : ∀ x, U0.MemOpen x → orient2D (S a) x (S b) * orient2D (S a) x (S c) < 0 := by
      intro x hx
      dsimp [U0] at hx
      rw [← reflPt_invol x, reflWedge_memOpen] at hx
      have hs := hU_sep (reflPt x) hx
      dsimp [Function.comp] at hs
      rw [reflPt_orient2D, reflPt_orient2D] at hs
      linarith
    have hU0_see : ∀ x ∈ W0, Sees P x (S a) → U0.MemOpen x := by
      rintro _ ⟨y, hy, rfl⟩ hsee
      rw [← reflPt_sees P (reflPt y) (S a), reflPt_invol] at hsee
      have hu := hU_see y hy hsee
      dsimp [U0]; rwa [reflWedge_memOpen]
    obtain ⟨R0, hR0y, hR0_sub, hR0_test⟩ :=
      h25.wedge_extraction a b c W0 U0 hab hac hbc hW0_sub hU0_y hU0_sep hU0_see
    refine ⟨reflWedge R0, ?_, fun z hz => ?_, ?_⟩
    · dsimp [reflWedge]; rw [hR0y]
    · have hz' : R0.MemOpen (reflPt z) := by
        rwa [← reflPt_invol z, reflWedge_memOpen] at hz
      have h1 := hR0_sub (reflPt z) hz'
      dsimp [U0] at h1
      rwa [reflWedge_memOpen] at h1
    · have himg : reflPt '' W0 = W' := by
        ext x
        simp only [W0, Set.mem_image]
        constructor
        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩; rwa [reflPt_invol]
        · intro hx; exact ⟨reflPt x, ⟨x, hx, rfl⟩, reflPt_invol x⟩
      simpa [himg, reflPt_witnessSet] using reflPt_isWedgeTest hR0_test
  fan_corollary Tw F a hFT haT hconv := by
    have hconv' : S a ∈ convexHull ℝ (((F.image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ∪ {w Tw}) := by
      have himg : (((F.image (reflPt ∘ S) : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ∪ {(reflPt ∘ w) Tw}) =
          reflPt '' (((F.image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ∪ {w Tw}) := by
        ext p
        simp only [Set.mem_union, Set.mem_singleton_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe, Function.comp_apply]
        constructor
        · rintro (⟨i, hi, rfl⟩ | rfl)
          · exact ⟨S i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
          · exact ⟨w Tw, Or.inr rfl, rfl⟩
        · rintro ⟨q, (⟨i, hi, rfl⟩ | rfl), rfl⟩
          · exact Or.inl ⟨i, hi, rfl⟩
          · exact Or.inr rfl
      rw [himg, ← reflPt_image_convexHull] at hconv
      rcases hconv with ⟨y, hy, hyx⟩
      exact reflPt_inj hyx ▸ hy
    obtain ⟨R0, hR0⟩ := h25.fan_corollary Tw F a hFT haT hconv'
    refine ⟨reflWedge R0, ?_⟩
    simpa [reflPt_witnessSet] using reflPt_isWedgeTest hR0
  hidden_targets T hTB hex := by
    rw [reflPt_hullVertices] at hTB
    rw [reflPt_interiorPoints]
    refine h25.hidden_targets T hTB fun t ht => ?_
    obtain ⟨b, c, Tv, hb, hc, hbc, hbT, hcT, htT, hin⟩ := hex t ht
    rw [reflPt_hullVertices] at hb hc
    dsimp [Function.comp] at hin
    rw [reflPt_inIntTri] at hin
    exact ⟨b, c, Tv, hb, hc, hbc, hbT, hcT, htT, hin⟩
  hidden_front C Tv f b c hCB hC3 hfC hed1 hed2 hbT hcT hfT hfront := by
    rw [reflPt_hullVertices] at hCB
    rw [reflPt_isCCWEdge] at hed1 hed2
    dsimp [Function.comp] at hfront
    rw [reflPt_isFrontVertexOf] at hfront
    obtain ⟨hin, hall⟩ := h25.hidden_front C Tv f c b hCB hC3 hfC hed2 hed1 hcT hbT hfT hfront
    refine ⟨(reflPt_inIntTri _ _ _ _).mpr hin.symm23, fun Tx hbTx hcTx => ?_⟩
    obtain ⟨hinX, hfX⟩ := hall Tx hcTx hbTx
    exact ⟨(reflPt_inIntTri _ _ _ _).mpr hinX.symm23,
           (reflPt_isFrontVertexOf S C f (w Tx)).mpr hfX⟩
  front_restoration C D' f v hCD' hD' hC3 hv hf := by
    rcases hv with ⟨T, rfl⟩
    rw [reflPt_isConvexPos] at hD'
    dsimp [Function.comp] at hf ⊢
    rw [reflPt_isFrontVertexOf] at hf ⊢
    exact h25.front_restoration C D' f (w T) hCD' hD' hC3 ⟨T, rfl⟩ hf
  certified_structure := by
    dsimp
    rw [reflPt_hullVertices, reflPt_certifiedVertices, reflPt_interiorPoints]
    obtain ⟨hcard, hne⟩ := h25.certified_structure
    refine ⟨hcard, fun hH => ?_⟩
    obtain ⟨l, r, hlD, hrD, hlr, hed, hH_neg, hD_pos, hH_tri, h_edges, h1, h2⟩ := hne hH
    refine ⟨r, l, hrD, hlD, Ne.symm hlr, fun hD3 => (reflPt_isCCWEdge S _ r l).mpr (hed hD3),
      fun h hh => ?_, fun d hd hdr hdl => ?_, fun h T hh hrT hlT => ?_,
      fun d hd hdr hdl x hxB => ?_, fun hH1 h hh => ?_, fun hH2 => ?_⟩
    · rw [reflPt_orient2D]
      have := hH_neg h hh; unfold orient2D at this ⊢; linarith
    · rw [reflPt_orient2D]
      have := hD_pos d hd hdl hdr; unfold orient2D at this ⊢; linarith
    · rw [reflPt_inIntTri]
      exact (hH_tri h T hh hlT hrT).symm23
    · rw [reflPt_isCCWEdge, reflPt_isCCWEdge, reflPt_isCCWEdge, reflPt_isCCWEdge]
      exact (h_edges d hd hdl hdr x hxB).symm
    · rw [reflPt_isCCWEdge, reflPt_isCCWEdge]
      exact (h1 hH1 h hh).symm
    · -- Predecessor pair `(h2, h1)` of `r` on `hullVertices S` lies in `certifiedVertices S w`
      obtain ⟨h1', h2', hh1', hh2', h12', _, _⟩ := h2 hH2
      let B := hullVertices S
      let H := certifiedVertices S w
      have hlB : l ∈ B := (Finset.mem_sdiff.mp hlD).1
      have hrB : r ∈ B := (Finset.mem_sdiff.mp hrD).1
      have hlH : l ∉ H := (Finset.mem_sdiff.mp hlD).2
      have hrH : r ∉ H := (Finset.mem_sdiff.mp hrD).2
      have hH_sub_B : H ⊆ B := by
        intro x hx; exact (Finset.mem_filter.mp hx).1
      have h4_sub : ({l, r, h1', h2'} : Finset (Fin n)) ⊆ B := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hlB
        · exact hrB
        · exact hH_sub_B hh1'
        · exact hH_sub_B hh2'
      have h4_card : ({l, r, h1', h2'} : Finset (Fin n)).card = 4 := by
        have h1l : h1' ≠ l := fun h => hlH (h ▸ hh1')
        have h1r : h1' ≠ r := fun h => hrH (h ▸ hh1')
        have h2l : h2' ≠ l := fun h => hlH (h ▸ hh2')
        have h2r : h2' ≠ r := fun h => hrH (h ▸ hh2')
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h12']
        · simp [hlr, h1l.symm, h2l.symm, h1r.symm, h2r.symm]
        · simp [hlr, h1l.symm, h2l.symm, h1r.symm, h2r.symm]
      have hB4 : 4 ≤ B.card := h4_card ▸ Finset.card_le_card h4_sub
      have hn3 : 3 ≤ n := by have := Finset.card_le_univ B; rw [Fintype.card_fin] at this; omega
      obtain ⟨kB, hkB_eq, ⟨cycB⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
      have hkB1 : 1 ≤ kB := by dsimp [B] at hB4; omega
      obtain ⟨ir, hir⟩ := ccwCycle_exists_index cycB hrB
      let m := kB + 3
      have hm4 : 4 ≤ m := by omega
      have hne_m1 : ir - 1 ≠ ir := by
        intro h
        have h10 : (1 : Fin m) = 0 := by
          have := congrArg (fun x => ir - x) h
          simpa using this.symm
        have hval := congrArg Fin.val h10
        simp only [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < m)] at hval
        omega
      have h2_eq : (2 : Fin m) = 1 + 1 := Fin.ext (by
        change 2 % m = (1 % m + 1 % m) % m
        rw [Nat.mod_eq_of_lt (by omega : 2 < m), Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt (by omega : 2 < m)])
      have hne_m2 : ir - 2 ≠ ir := by
        intro h
        have h20 : (2 : Fin m) = 0 := sub_eq_self.mp h
        have hval := congrArg Fin.val h20
        change 2 % m = 0 at hval
        rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
      have hsub_add1 : ir - 2 + 1 = ir - 1 := by
        rw [h2_eq, ← sub_sub, sub_add_cancel]
      have hne_m21 : ir - 2 ≠ ir - 1 := by
        intro h
        have := congrArg (· + 1) h
        rw [hsub_add1, sub_add_cancel] at this
        exact hne_m1 this
      let v1 := cycB.toFun (ir - 1)
      let v2 := cycB.toFun (ir - 2)
      have hv1B : v1 ∈ B := ccwCycle_mem cycB (ir - 1)
      have hv2B : v2 ∈ B := ccwCycle_mem cycB (ir - 2)
      have hv1r : v1 ≠ r := hir ▸ cycB.inj.ne hne_m1
      have hv2r : v2 ≠ r := hir ▸ cycB.inj.ne hne_m2
      have hv21 : v2 ≠ v1 := cycB.inj.ne hne_m21
      have e_v1r : IsCCWEdge S B v1 r := by
        have e := ccwCycle_isCCWEdge cycB (ir - 1)
        rwa [sub_add_cancel, hir] at e
      have e_v2v1 : IsCCWEdge S B v2 v1 := by
        have e := ccwCycle_isCCWEdge cycB (ir - 2)
        rwa [hsub_add1] at e
      have hB_conv := hullVertices_convexPos S (Subset.rfl : B ⊆ B)
      have h_tri_contra : ∀ x a b c : Fin n, x ∈ B → a ∈ B → b ∈ B → c ∈ B →
          x ≠ a → x ≠ b → x ≠ c →
          0 < orient2D (S a) (S b) (S c) →
          0 < orient2D (S a) (S b) (S x) →
          0 < orient2D (S b) (S c) (S x) →
          0 < orient2D (S c) (S a) (S x) → False := by
        intro x a b c hxB haB hbB hcB hxa hxb hxc habc o1 o2 o3
        have hin := (inIntTri_iff_orient_pos habc).mpr ⟨o1, o2, o3⟩
        apply hB_conv x hxB
        refine convexHull_mono ?_ hin.to_convexHull
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_erase.mpr ⟨hxa.symm, haB⟩))
        · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_erase.mpr ⟨hxb.symm, hbB⟩))
        · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_erase.mpr ⟨hxc.symm, hcB⟩))
      have hv1H : v1 ∈ H := by
        by_contra hv1nH
        have hv1D : v1 ∈ B \ H := Finset.mem_sdiff.mpr ⟨hv1B, hv1nH⟩
        by_cases hv1l : v1 = l
        · rw [hv1l] at e_v1r
          have ho := e_v1r.2.2.2 h1' (hH_sub_B hh1') (fun h => hlH (h ▸ hh1')) (fun h => hrH (h ▸ hh1'))
          linarith [hH_neg h1' hh1']
        · have ho1 := hD_pos v1 hv1D hv1l hv1r
          have ho2 := e_v1r.2.2.2 l hlB (Ne.symm hv1l) hlr
          unfold orient2D at ho1 ho2; linarith
      have hv2H : v2 ∈ H := by
        by_contra hv2nH
        have hv2D : v2 ∈ B \ H := Finset.mem_sdiff.mpr ⟨hv2B, hv2nH⟩
        by_cases hv2l : v2 = l
        · have hex_other : ∃ h0 ∈ H, h0 ≠ v1 := by
            by_cases h1eq : h1' = v1
            · exact ⟨h2', hh2', fun h => h12' (h1eq.trans h.symm)⟩
            · exact ⟨h1', hh1', h1eq⟩
          obtain ⟨h0, hh0, hh0_ne⟩ := hex_other
          have hh0B : h0 ∈ B := hH_sub_B hh0
          have hh0l : h0 ≠ l := fun h => hlH (h ▸ hh0)
          have hh0r : h0 ≠ r := fun h => hrH (h ▸ hh0)
          rw [hv2l] at e_v2v1
          have o12 := e_v2v1.2.2.2 r hrB (Ne.symm hlr) hv1r.symm
          have o1 := e_v2v1.2.2.2 h0 hh0B hh0l hh0_ne
          have o2 := e_v1r.2.2.2 h0 hh0B hh0_ne hh0r
          have o3 : 0 < orient2D (S r) (S l) (S h0) := by
            have := hH_neg h0 hh0; unfold orient2D at this ⊢; linarith
          exact h_tri_contra h0 l v1 r hh0B hlB hv1B hrB hh0l hh0_ne hh0r o12 o1 o2 o3
        · have o12 : 0 < orient2D (S r) (S v2) (S v1) := by
            have := e_v2v1.2.2.2 r hrB hv2r.symm hv1r.symm
            unfold orient2D at this ⊢; linarith
          have o1 : 0 < orient2D (S r) (S v2) (S l) := by
            have := hD_pos v2 hv2D hv2l hv2r
            unfold orient2D at this ⊢; linarith
          have hv1_nl : v1 ≠ l := fun h => hlH (h ▸ hv1H)
          have o2' := e_v2v1.2.2.2 l hlB (Ne.symm hv2l) hv1_nl.symm
          have o3' := e_v1r.2.2.2 l hlB hv1_nl.symm hlr
          exact h_tri_contra l r v2 v1 hlB hrB hv2B hv1B hlr (Ne.symm hv2l) hv1_nl.symm o12 o1 o2' o3'
      refine ⟨v1, v2, hv1H, hv2H, hv21.symm, ?_, ?_⟩
      · rw [reflPt_isCCWEdge]; exact e_v1r
      · rw [reflPt_isCCWEdge]; exact e_v2v1
  side_preservation := by
    dsimp
    rw [reflPt_hullVertices, reflPt_certifiedVertices]
    intro hH hD5 Q M0 hQD hQ2 hM0 hBack h hh
    have hBack' : ∀ p ∈ Q, ∃ O, p ∉ O ∧
        (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
          ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)) := by
      intro p hp
      obtain ⟨O, hpO, hO_nadj, hback⟩ := hBack p hp
      refine ⟨O, hpO, fun a ha b hb hed => hO_nadj b hb a ha ((reflPt_isCCWEdge S _ b a).mpr hed),
        (reflPt_isBackVertexOf S _ p _).mp hback⟩
    obtain ⟨a, b, haF, hbF, hab, hin⟩ := h25.side_preservation hH hD5 Q M0 hQD hQ2 hM0 hBack' h hh
    refine ⟨a, b, haF, hbF, hab, fun x hx => ?_⟩
    rw [reflPt_witnessSet] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (reflPt_inIntTri _ _ _ _).mpr (hin y hy)
  exit_edge_lemma := by
    dsimp
    rw [reflPt_hullVertices, reflPt_certifiedVertices]
    intro hD3 y hy
    obtain ⟨u, v, hed, hpos, hin, h_not_lr, hW, h_uniq⟩ := h25.exit_edge_lemma hD3 y hy
    refine ⟨v, u, (reflPt_isCCWEdge S _ v u).mpr hed, ?_, ?_, ?_, ?_, ?_⟩
    · rw [reflPt_orient2D]
      unfold orient2D at hpos ⊢; linarith
    · rw [reflPt_inIntTri]
      exact hin.symm23
    · intro l r hH hlr hlrh heq
      rw [reflPt_isCCWEdge] at hlr
      apply h_not_lr r l hH hlr (fun h hh => by
        have := hlrh h hh
        rw [reflPt_orient2D] at this
        unfold orient2D at this ⊢; linarith)
      have := Prod.mk.inj heq
      exact Prod.ext this.2 this.1
    · intro x hx
      rw [reflPt_witnessSet] at hx
      rcases hx with ⟨z, hz, rfl⟩
      rw [reflPt_inIntTri]
      exact (hW z (by simpa only [Finset.pair_comm] using hz)).symm23
    · intro u' v' hed' hpos' hconv
      rw [reflPt_isCCWEdge] at hed'
      rw [reflPt_orient2D] at hpos'
      have hpos0 : 0 < orient2D (S v') (S u') (w (hullVertices S \ certifiedVertices S w)) := by
        unfold orient2D at hpos' ⊢; linarith
      have himg : ({reflPt (w (hullVertices S \ certifiedVertices S w)), reflPt (S u'), reflPt (S v')} : Set (ℝ × ℝ)) =
          reflPt '' {w (hullVertices S \ certifiedVertices S w), S v', S u'} := by
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact ⟨w (hullVertices S \ certifiedVertices S w), Or.inl rfl, rfl⟩
          · exact ⟨S u', Or.inr (Or.inr rfl), rfl⟩
          · exact ⟨S v', Or.inr (Or.inl rfl), rfl⟩
        · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
      rw [himg, ← reflPt_image_convexHull] at hconv
      rcases hconv with ⟨z, hz, hzx⟩
      rw [reflPt_inj hzx] at hz
      have := h_uniq v' u' hed' hpos0 hz
      exact ⟨this.2, this.1⟩
  endpoint_back_criterion := by
    dsimp
    rw [reflPt_hullVertices, reflPt_certifiedVertices]
    intro hH hD5 l r p y hlD hrD hlr hed hH_neg hpy hBack
    rw [reflPt_isCCWEdge] at hed
    have hH_neg' : ∀ h ∈ certifiedVertices S w, orient2D (S r) (S l) (S h) < 0 := fun h hh => by
      have := hH_neg h hh
      rw [reflPt_orient2D] at this
      unfold orient2D at this ⊢; linarith
    have hBack' : ∃ O, p ∉ O ∧
        (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
          ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)) := by
      obtain ⟨O, hpO, hO_nadj, hback⟩ := hBack
      refine ⟨O, hpO, fun a ha b hb hed0 => hO_nadj b hb a ha ((reflPt_isCCWEdge S _ b a).mpr hed0),
        (reflPt_isBackVertexOf S _ p _).mp hback⟩
    obtain ⟨h_exit, h_nback⟩ := h25.endpoint_back_criterion hH hD5 r l p y hrD hlD (Ne.symm hlr) hed hH_neg'
      (by rcases hpy with h | h; exact Or.inr h; exact Or.inl h) hBack'
    refine ⟨fun h hh u v heduv hin => ?_, ?_⟩
    · rw [reflPt_isCCWEdge] at heduv
      rw [reflPt_inIntTri] at hin
      exact (h_exit h hh v u heduv hin.symm23).symm
    · rintro ⟨O', hyO', hO'_nadj, hback'⟩
      apply h_nback
      refine ⟨O', hyO', fun a ha b hb hed0 => hO'_nadj b hb a ha ((reflPt_isCCWEdge S _ b a).mpr hed0),
        (reflPt_isBackVertexOf S _ y _).mp hback'⟩
  half_plane_lemma := by
    intro Tv Tq a p c hpTv haTv hcTv haTq hpTq hcTq hang1 hang2 hcross hsee
    have h_ang : ∀ x y z u, AngleLt (reflPt x) (reflPt y) (reflPt z) (reflPt u) ↔ AngleLt x y z u := by
      intro x y z u
      unfold AngleLt OnSameSide
      rw [reflPt_orient2D, reflPt_orient2D, reflPt_orient2D]
      ring_nf
    have h_cr : ∀ x y z u, SegmentsCross (reflPt x) (reflPt y) (reflPt z) (reflPt u) ↔ SegmentsCross x y z u := by
      intro x y z u
      unfold SegmentsCross
      rw [reflPt_orient2D, reflPt_orient2D, reflPt_orient2D, reflPt_orient2D]
      ring_nf
    dsimp [Function.comp] at hang1 hang2 hcross
    rw [h_ang] at hang1 hang2
    rw [h_cr] at hcross
    have hsee' : Sees P (w Tv) (w Tq) ∨ ∃ e ∈ Tv, e ∈ Tq ∧ AngleLt (w Tv) (w Tq) (S e) (S a) := by
      rcases hsee with h1 | ⟨e, he1, he2, h3⟩
      · exact Or.inl ((reflPt_sees P _ _).mp h1)
      · exact Or.inr ⟨e, he1, he2, (h_ang _ _ _ _).mp h3⟩
    obtain ⟨H_hp, hH_hp⟩ := h25.half_plane_lemma Tv Tq a p c hpTv haTv hcTv haTq hpTq hcTq hang1 hang2 hcross hsee'
    refine ⟨reflHP H_hp, ?_⟩
    have := reflPt_isHalfPlaneTest hH_hp
    rwa [reflPt_witnessSet]

/-- Shared `conv B ⊆ conv D ∪ conv({l, r} ∪ H)` covering lemma via `h25.certified_structure`. -/
lemma convexHull_B_subset_convD_union_lrH {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD3 : 3 ≤ (hullVertices S \ certifiedVertices S w).card)
    {l r : Fin n} (hlD : l ∈ hullVertices S \ certifiedVertices S w)
    (hrD : r ∈ hullVertices S \ certifiedVertices S w)
    (h_edges : ∀ d ∈ hullVertices S \ certifiedVertices S w, d ≠ l → d ≠ r →
      ∀ x ∈ hullVertices S,
        (IsCCWEdge S (hullVertices S) x d ↔ IsCCWEdge S (hullVertices S \ certifiedVertices S w) x d) ∧
        (IsCCWEdge S (hullVertices S) d x ↔ IsCCWEdge S (hullVertices S \ certifiedVertices S w) d x)) :
    let B := hullVertices S
    let H := certifiedVertices S w
    let D := B \ H
    convexHull ℝ (B.image S : Set (ℝ × ℝ)) ⊆
      convexHull ℝ (D.image S : Set (ℝ × ℝ)) ∪
      convexHull ℝ ((insert l (insert r H)).image S : Set (ℝ × ℝ)) := by
  intro B H D z hzB
  have hn3 : 3 ≤ n := by
    have hdn : D.card ≤ n := (Finset.card_le_univ D).trans_eq (Fintype.card_fin n)
    dsimp [D, B, H] at hD3 hdn; omega
  obtain ⟨kB, _, ⟨cycB⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
  let pB : Fin (kB + 3) → ℝ × ℝ := fun i => S (cycB.toFun i)
  have hz_range : z ∈ convexHull ℝ (Set.range pB) := by
    have hr : Set.range pB = (B.image S : Set (ℝ × ℝ)) := by
      dsimp [B]; conv_rhs => rw [← cycB.image_eq]
      ext y; simp [pB]
    rwa [hr]
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover pB cycB.ccw (S l) z hz_range
  let u := cycB.toFun i
  let v := cycB.toFun (i + 1)
  have huB : u ∈ B := ccwCycle_mem cycB i
  have hvB : v ∈ B := ccwCycle_mem cycB (i + 1)
  have huv : IsCCWEdge S B u v := ccwCycle_isCCWEdge cycB i
  by_cases h_bothD : u ∈ D ∧ v ∈ D
  · left
    refine convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S h_bothD.1)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S h_bothD.2)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hlD))) hi
  · right
    have h_in_lrH : ∀ x ∈ B, ¬ (u ∈ D ∧ v ∈ D) → (x = u ∨ x = v) → x ∈ insert l (insert r H) := by
      intro x hxB hnot hxv
      by_cases hxH : x ∈ H
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxH)
      · have hxD : x ∈ D := Finset.mem_sdiff.mpr ⟨hxB, hxH⟩
        by_cases hxl : x = l
        · subst hxl; exact Finset.mem_insert_self _ _
        · by_cases hxr : x = r
          · subst hxr; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · exfalso; apply hnot
            rcases hxv with rfl | rfl
            · exact ⟨hxD, ((h_edges u hxD hxl hxr v hvB).2.mp huv).2.1⟩
            · exact ⟨((h_edges v hxD hxl hxr u huB).1.mp huv).1, hxD⟩
    have hu_mem : u ∈ insert l (insert r H) := h_in_lrH u huB h_bothD (Or.inl rfl)
    have hv_mem : v ∈ insert l (insert r H) := h_in_lrH v hvB h_bothD (Or.inr rfl)
    have hl_mem : l ∈ insert l (insert r H) := Finset.mem_insert_self _ _
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hu_mem)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hv_mem)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hl_mem))) hi

/-- General Section 7 covering bridge (`combination_cover_from_convD`):
    combines `h25.certified_structure`, `h25.side_preservation`, and `convexHull_B_subset_convD_union_lrH`
    with `combination_lemma_core` whenever `Q ⊆ D`, `|Q| ∈ {1, 2}`, `Q ∩ {l, r} = ∅`, and `conv D` is covered. -/
lemma combination_cover_from_convD {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : 5 ≤ (hullVertices S \ certifiedVertices S w).card)
    {Q M0 : Finset (Fin n)}
    (hQD : Q ⊆ hullVertices S \ certifiedVertices S w)
    (hQ_card : Q.card = 1 ∨ Q.card = 2)
    (hM0 : M0 ⊆ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hBack : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)))
    (hQ_hp : ∀ p ∈ Q, ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet (((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0) ∅ w) (S p) H_hp)
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      l ∈ hullVertices S \ certifiedVertices S w → r ∈ hullVertices S \ certifiedVertices S w → l ≠ r →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ∉ Q ∧ r ∉ Q)
    (h_convD_cov : ∀ z ∈ interiorPoints S \ M0,
      S z ∈ convexHull ℝ (((hullVertices S \ certifiedVertices S w).image S : Set (ℝ × ℝ))) →
      (∃ H_hp : OpenHalfPlane,
        IsHalfPlaneTest P (WitnessSet (((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0) ∅ w) (S z) H_hp) ∨
      S z ∈ convexHull ℝ (((((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0).image S : Set (ℝ × ℝ)) ∪
        {w (((hullVertices S \ certifiedVertices S w) \ Q) ∪ M0)})) :
    let D := hullVertices S \ certifiedVertices S w
    let M := Finset.univ \ D
    let F := (D \ Q) ∪ M0
    let M' := M \ M0
    (Q.card = 1 → M'.card ≤ 4) ∧
    (Q.card = 2 → M'.card ≤ 2) ∧
    (Q.card = 1 → M'.card = 4 → ∀ z ∈ M',
      ¬ ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) ∧
    (Q.card = 2 → ∀ z ∈ M',
      ¬ ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) := by
  intro D M F M'
  have hQ_le2 : Q.card ≤ 2 := by rcases hQ_card with h | h <;> omega
  have hH_cov : ∀ h ∈ certifiedVertices S w \ M0, ∃ a b : Fin n, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧
      ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h) := by
    intro h hh
    have hHne : (certifiedVertices S w).Nonempty := ⟨h, (Finset.mem_sdiff.mp hh).1⟩
    exact h25.side_preservation hHne hD5 Q M0 hQD hQ_le2 hM0 hBack h hh
  refine combination_lemma_core hPoly h25 hQD hQ_card hM0 hQ_hp hH_cov ?_
  intro z hz
  have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
  have hzB : S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ)) :=
    mem_convexHull_hullVertices S hPoly.s_inj z
  by_cases hHne : (certifiedVertices S w).Nonempty
  · obtain ⟨l, r, hlD, hrD, hlr, hed, hH_neg, _, _, h_edges, _, _⟩ := h25.certified_structure.2 hHne
    obtain ⟨hlQ, hrQ⟩ := h_not_lr l r hHne hlD hrD hlr (hed (by omega)) hH_neg
    have hB_cov := convexHull_B_subset_convD_union_lrH hPoly h25 (by omega) hlD hrD h_edges hzB
    rcases hB_cov with hzD | hzH
    · exact h_convD_cov z hz hzD
    · right
      refine convexHull_min ?_ (convex_convexHull ℝ _) hzH
      intro p hp
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨x, hx, rfl⟩
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hxH
      · exact subset_convexHull ℝ _ (Set.mem_union_left _
          (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hlD, hlQ⟩)))))
      · exact subset_convexHull ℝ _ (Set.mem_union_left _
          (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hrD, hrQ⟩)))))
      · by_cases hxM0 : x ∈ M0
        · exact subset_convexHull ℝ _ (Set.mem_union_left _
            (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ hxM0))))
        · obtain ⟨a, b, haF, hbF, _, hin⟩ := hH_cov x (Finset.mem_sdiff.mpr ⟨hxH, hxM0⟩)
          have hwt := hin (w F) ⟨F, fun t ht => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl <;> assumption, Finset.disjoint_empty_right _, rfl⟩
          exact convexHull_tri_subset
            (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _)))
            (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S haF))))
            (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hbF))))
            hwt.to_convexHull
  · have hH_emp : certifiedVertices S w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
    have hBD : hullVertices S = D := by dsimp [D]; rw [hH_emp, Finset.sdiff_empty]
    rw [hBD] at hzB
    exact h_convD_cov z hz hzB

private def ccwCycle_rev {n m : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C m) (c0 : Fin (m + 3)) :
    CCWCycle (reflPt ∘ S) C m where
  toFun i := cyc.toFun (c0 - i)
  inj a b h := sub_right_inj.mp (cyc.inj h)
  image_eq := by
    conv_rhs => rw [← cyc.image_eq]
    ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨c0 - i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨c0 - i, by rw [sub_sub_cancel]⟩
  ccw := by
    intro i j hij1 hij2
    have hne_ji : c0 - j ≠ c0 - i := fun h => hij1 (sub_right_inj.mp h)
    have hne_ji1 : c0 - j ≠ c0 - (i + 1) := fun h => hij2 (sub_right_inj.mp h)
    have heq_sub : c0 - (i + 1) + 1 = c0 - i := by abel
    have hccw := cyc.ccw (c0 - (i + 1)) (c0 - j) hne_ji1 (by rw [heq_sub]; exact hne_ji)
    rw [heq_sub] at hccw
    dsimp [Function.comp] at hccw ⊢
    rw [reflPt_orient2D]
    unfold orient2D at hccw ⊢; linarith
  ccw_tri a b c hab hbc := by
    have hac : a < c := lt_trans hab hbc
    have h1 : 0 < ((c0 - b) - (c0 - c)).val := by
      have hcb : (c0 - b) - (c0 - c) = c - b := by abel
      rw [hcb, fin_val_sub_eq', if_pos (le_of_lt hbc)]
      have := Fin.lt_def.mp hbc; omega
    have h2 : ((c0 - b) - (c0 - c)).val < ((c0 - a) - (c0 - c)).val := by
      have hcb : (c0 - b) - (c0 - c) = c - b := by abel
      have hca : (c0 - a) - (c0 - c) = c - a := by abel
      rw [hcb, hca, fin_val_sub_eq', fin_val_sub_eq', if_pos (le_of_lt hbc), if_pos (le_of_lt hac)]
      have := Fin.lt_def.mp hab; omega
    have hccw := ccwCycle_ccw3 cyc h1 h2
    dsimp [Function.comp]
    rw [reflPt_orient2D]
    unfold orient2D at hccw ⊢; linarith

private def ccwCycle_shift {n m : ℕ} {S : Fin n → ℝ × ℝ} {C : Finset (Fin n)}
    (cyc : CCWCycle S C m) (c0 : Fin (m + 3)) :
    CCWCycle S C m where
  toFun i := cyc.toFun (c0 + i)
  inj a b h := add_left_cancel (cyc.inj h)
  image_eq := by
    conv_rhs => rw [← cyc.image_eq]
    ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨c0 + i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨i - c0, by rw [add_sub_cancel]⟩
  ccw i j hij1 hij2 := by
    have heq_add : c0 + i + 1 = c0 + (i + 1) := by abel
    have h := cyc.ccw (c0 + i) (c0 + j) (fun he => hij1 (add_left_cancel he))
      (fun he => hij2 (by rw [heq_add] at he; exact add_left_cancel he))
    dsimp [Function.comp] at h ⊢
    rwa [← heq_add]
  ccw_tri a b c hab hbc := by
    have hac : a < c := lt_trans hab hbc
    have h1 : 0 < ((c0 + b) - (c0 + a)).val := by
      have heq : (c0 + b) - (c0 + a) = b - a := by abel
      rw [heq, fin_val_sub_eq', if_pos (le_of_lt hab)]
      have := Fin.lt_def.mp hab; omega
    have h2 : ((c0 + b) - (c0 + a)).val < ((c0 + c) - (c0 + a)).val := by
      have heq1 : (c0 + b) - (c0 + a) = b - a := by abel
      have heq2 : (c0 + c) - (c0 + a) = c - a := by abel
      rw [heq1, heq2, fin_val_sub_eq', fin_val_sub_eq', if_pos (le_of_lt hab), if_pos (le_of_lt hac)]
      have := Fin.lt_def.mp hbc; omega
    exact ccwCycle_ccw3 cyc h1 h2

private def ccwCycle_cast {n m : ℕ} {S : Fin n → ℝ × ℝ} {C₁ C₂ : Finset (Fin n)}
    (h : C₁ = C₂) (c : CCWCycle S C₁ m) : CCWCycle S C₂ m where
  toFun := c.toFun
  inj := c.inj
  image_eq := h ▸ c.image_eq
  ccw := c.ccw
  ccw_tri := c.ccw_tri

private lemma fin6_sub1_add1 (a : Fin 6) : a - 1 + 1 = a := by revert a; decide
private lemma fin6_add5_eq_sub1 (a : Fin 6) : a + 5 = a - 1 := by revert a; decide
private lemma fin6_sub5_eq_add1 (a : Fin 6) : a - 5 = a + 1 := by revert a; decide
private lemma fin6_add1_add1 (a : Fin 6) : a + 1 + 1 = a + 2 := by revert a; decide
private lemma fin6_add2_ne_add1 (a : Fin 6) : a + 2 ≠ a + 1 := by revert a; decide
private lemma fin6_1_add_sub1 (a : Fin 6) : 1 + (a - 1) = (1 + a) - 1 := by revert a; decide
private lemma fin6_1_add_add1 (a : Fin 6) : 1 + (a + 1) = (1 + a) + 1 := by revert a; decide
private lemma fin6_add1_sub1 (a : Fin 6) : a + 1 - 1 = a := by revert a; decide
private lemma fin6_sub1_sub1 (a : Fin 6) : a - 1 - 1 = a - 2 := by revert a; decide
private lemma fin6_add0 (a : Fin 6) : a + 0 = a := by revert a; decide
private lemma fin6_sub0 (a : Fin 6) : a - 0 = a := by revert a; decide
private lemma fin6_antipodal_ne (i0 : Fin 6) :
    i0 - 1 ≠ i0 + 3 ∧ i0 + 1 ≠ i0 + 3 ∧ (i0 + 3) - 1 ≠ i0 ∧ (i0 + 3) + 1 ≠ i0 := by
  revert i0; decide
private lemma fin6_adj_or_antipodal (i0 i1 : Fin 6) (hodd : i1.val % 2 ≠ i0.val % 2)
    (hant : i1 ≠ i0 + 3) : i1 = i0 + 1 ∨ i1 = i0 - 1 := by
  revert i0 i1; decide

private def hexIdxEr0 : Fin 5 → Fin 6 := ![1, 2, 3, 4, 5]
private def hexIdxEr1 : Fin 5 → Fin 6 := ![2, 3, 4, 5, 0]

private lemma hex_er0_inj : Function.Injective hexIdxEr0 := by decide
private lemma hex_er1_inj : Function.Injective hexIdxEr1 := by decide
private lemma hex_er0_ord : ∀ a b c : Fin 5, a < b → b < c →
    0 < (hexIdxEr0 b - hexIdxEr0 a).val ∧ (hexIdxEr0 b - hexIdxEr0 a).val < (hexIdxEr0 c - hexIdxEr0 a).val := by decide
private lemma hex_er1_ord : ∀ a b c : Fin 5, a < b → b < c →
    0 < (hexIdxEr1 b - hexIdxEr1 a).val ∧ (hexIdxEr1 b - hexIdxEr1 a).val < (hexIdxEr1 c - hexIdxEr1 a).val := by decide
private lemma hex_er0_pure_split : ∀ (j : Fin 6), j ≠ 5 → j ≠ 0 → j ≠ 1 → ∀ m : Fin 5,
    ((hexIdxEr0 m = j - 1 ∨ hexIdxEr0 m = j ∨ hexIdxEr0 m = j + 1) ∧
     (hexIdxEr0 (m + 1) = j - 1 ∨ hexIdxEr0 (m + 1) = j ∨ hexIdxEr0 (m + 1) = j + 1)) ∨
    (hexIdxEr0 m ≠ 0 ∧ hexIdxEr0 m ≠ j ∧ hexIdxEr0 (m + 1) ≠ 0 ∧ hexIdxEr0 (m + 1) ≠ j) := by decide
private lemma hex_er1_pure_split : ∀ (j : Fin 6), j ≠ 0 → j ≠ 1 → j ≠ 2 → ∀ m : Fin 5,
    ((hexIdxEr1 m = j - 1 ∨ hexIdxEr1 m = j ∨ hexIdxEr1 m = j + 1) ∧
     (hexIdxEr1 (m + 1) = j - 1 ∨ hexIdxEr1 (m + 1) = j ∨ hexIdxEr1 (m + 1) = j + 1)) ∨
    (hexIdxEr1 m ≠ 1 ∧ hexIdxEr1 m ≠ j ∧ hexIdxEr1 (m + 1) ≠ 1 ∧ hexIdxEr1 (m + 1) ≠ j) := by decide
private lemma hex_er0_mixed_split : ∀ (k j d_anc : Fin 6),
    (k = 1 ∨ k = 2 ∨ k = 3) → (j = k ∧ d_anc = k - 1 ∨ j = k + 1 ∧ d_anc = k + 2) →
    j ≠ 5 → j ≠ 0 → j ≠ 1 → ∀ m : Fin 5,
    (hexIdxEr0 m = k ∧ hexIdxEr0 (m + 1) = k + 1) ∨
    ((hexIdxEr0 m = j ∨ hexIdxEr0 m = d_anc) ∧ (hexIdxEr0 (m + 1) = j ∨ hexIdxEr0 (m + 1) = d_anc)) ∨
    (hexIdxEr0 m ≠ 0 ∧ hexIdxEr0 m ≠ j ∧ hexIdxEr0 (m + 1) ≠ 0 ∧ hexIdxEr0 (m + 1) ≠ j) := by decide
private lemma hex_er1_mixed_split : ∀ (k j d_anc : Fin 6),
    (k = 1 ∨ k = 2 ∨ k = 3) → (j = k ∧ d_anc = k - 1 ∨ j = k + 1 ∧ d_anc = k + 2) →
    j ≠ 0 → j ≠ 1 → j ≠ 2 → ∀ m : Fin 5,
    (hexIdxEr1 m = k ∧ hexIdxEr1 (m + 1) = k + 1) ∨
    ((hexIdxEr1 m = j ∨ hexIdxEr1 m = d_anc) ∧ (hexIdxEr1 (m + 1) = j ∨ hexIdxEr1 (m + 1) = d_anc)) ∨
    (hexIdxEr1 m ≠ 1 ∧ hexIdxEr1 m ≠ j ∧ hexIdxEr1 (m + 1) ≠ 1 ∧ hexIdxEr1 (m + 1) ≠ j) := by decide
private lemma hex_size2_split : ∀ (g1 : Fin 6) (m : Fin 6),
    ((m = g1 - 1 ∨ m = g1 ∨ m = g1 + 1 ∨ m = g1 + 2) ∧
     (m + 1 = g1 - 1 ∨ m + 1 = g1 ∨ m + 1 = g1 + 1 ∨ m + 1 = g1 + 2)) ∨
    (m ≠ g1 ∧ m ≠ g1 + 1 ∧ m + 1 ≠ g1 ∧ m + 1 ≠ g1 + 1) := by decide
private lemma fin6_sub1_ne : ∀ x : Fin 6, x - 1 ≠ x := by decide
private lemma fin6_add1_ne : ∀ x : Fin 6, x + 1 ≠ x := by decide
private lemma fin6_sub1_ne_add1 : ∀ x : Fin 6, x - 1 ≠ x + 1 := by decide
private lemma fin6_sub1_add2_ne : ∀ x : Fin 6, x - 1 ≠ x + 2 := by decide

/-- Helper for Section 8.3: minimal point `a0 ∈ M` on exit edge `(u0, v0)` makes `△(u0, v0, a0)` empty of `M \ {a0}`. -/
private lemma exit_minimal_empty {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD3 : 3 ≤ (hullVertices S \ certifiedVertices S w).card)
    {u0 v0 a0 : Fin n}
    (huv_edge : IsCCWEdge S (hullVertices S \ certifiedVertices S w) u0 v0)
    (hwD_pos : 0 < orient2D (S u0) (S v0) (w (hullVertices S \ certifiedVertices S w)))
    (ha0_tri : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S u0) (S v0) (S a0))
    (ha0_min : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S u0) (S v0) (S y) →
      orient2D (S u0) (S v0) (S a0) ≤ orient2D (S u0) (S v0) (S y)) :
    ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase a0,
      ¬ InClosedTri (S u0) (S v0) (S a0) (S z) := by
  intro z hz hzin
  have hzM : z ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w) := Finset.mem_of_mem_erase hz
  have hza0 : z ≠ a0 := (Finset.mem_erase.mp hz).1
  have ha0_pos : 0 < orient2D (S u0) (S v0) (S a0) := by
    rcases ha0_tri with ⟨μ₁, μ₂, μ₃, h1, _, _, hsum, ha1, ha2⟩
    have hid : orient2D (S u0) (S v0) (S a0) = μ₁ * orient2D (S u0) (S v0) (w (hullVertices S \ certifiedVertices S w)) := by
      unfold orient2D; rw [ha1, ha2]
      linear_combination ((S u0).2 * (S v0).1 - (S u0).1 * (S v0).2) * hsum
    rw [hid]; exact mul_pos h1 hwD_pos
  have hsub := exitRegion_single_disjoint (w (hullVertices S \ certifiedVertices S w))
    (S u0) (S v0) (S a0) (S z) ha0_pos ha0_tri.to_inClosedTri hzin
  obtain ⟨uz, vz, _, _, hz_tri, _, _, h_uniq⟩ := h25.exit_edge_lemma hD3 z hzM
  have huz := h_uniq u0 v0 huv_edge hwD_pos ((inClosedTri_iff_mem_convexHull _ _ _ _).mp hsub.1)
  have hz_tri0 : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S u0) (S v0) (S z) := by
    rw [huz.1, huz.2]; exact hz_tri
  exact hza0 (hPoly.s_inj (hsub.2 (ha0_min z hzM hz_tri0)))

private lemma hex_lift_hp {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {a b z : Fin n} {F : Finset (Fin n)} (haF : a ∈ F) (hbF : b ∈ F)
    (h : ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a, b} ∅ w) (S z) H_hp) :
    ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp := by
  obtain ⟨Hp, hHp⟩ := h
  refine ⟨Hp, isHalfPlaneTest_mono (fun x hx => ?_) hHp⟩
  rcases hx with ⟨T, hFT, hTN, rfl⟩
  refine ⟨T, fun y hy => hFT ?_, hTN, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> assumption

private lemma hex_oStar_nadj {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    {a0 : Fin n} (ha0_notD : a0 ∉ hullVertices S \ certifiedVertices S w)
    (ib' ib : Fin 6) (hn1 : ib ≠ ib' + 1) (hn2 : ib' ≠ ib + 1) :
    ∀ a ∈ ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) ∩ (hullVertices S \ certifiedVertices S w),
    ∀ b ∈ ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) ∩ (hullVertices S \ certifiedVertices S w),
    ¬ IsCCWEdge S (hullVertices S) a b := by
  intro a ha b hb hed
  have haD := (Finset.mem_inter.mp ha).2
  have hbD := (Finset.mem_inter.mp hb).2
  have ha_or : a = cycD.toFun ib' ∨ a = cycD.toFun ib := by
    rcases (by simpa using (Finset.mem_inter.mp ha).1 : a = cycD.toFun ib' ∨ a = a0 ∨ a = cycD.toFun ib) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (ha0_notD haD)
    · exact Or.inr rfl
  have hb_or : b = cycD.toFun ib' ∨ b = cycD.toFun ib := by
    rcases (by simpa using (Finset.mem_inter.mp hb).1 : b = cycD.toFun ib' ∨ b = a0 ∨ b = cycD.toFun ib) with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (ha0_notD hbD)
    · exact Or.inr rfl
  exact nonadj_D_implies_nonadj_B h25 (by omega) haD hbD (fun he => by
    rw [isCCWEdge_iff_ccwCycle cycD] at he
    rcases he with ⟨r, hr1, hr2⟩
    rcases ha_or with rfl | rfl <;> rcases hb_or with rfl | rfl
    · exact fin6_add1_ne _ (cycD.inj (hr1.symm.trans hr2)).symm
    · have h1 := cycD.inj hr1.symm; have h2 := cycD.inj hr2.symm; exact hn1 (h2.symm.trans (by rw [h1]))
    · have h1 := cycD.inj hr1.symm; have h2 := cycD.inj hr2.symm; exact hn2 (h2.symm.trans (by rw [h1]))
    · exact fin6_add1_ne _ (cycD.inj (hr1.symm.trans hr2)).symm) hed

private lemma hex_mk_back_O {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    {a0 : Fin n} (ha0_notD : a0 ∉ hullVertices S \ certifiedVertices S w)
    (q ib' ib : Fin 6) (hn1 : ib ≠ ib' + 1) (hn2 : ib' ≠ ib + 1) (hq1 : q ≠ ib') (hq2 : q ≠ ib)
    (hb : IsBackVertexOf S (hullVertices S) (cycD.toFun q) (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib}))) :
    ∃ O, cycD.toFun q ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun q) (w (Finset.univ \ O)) := by
  refine ⟨{cycD.toFun ib', a0, cycD.toFun ib}, ?_, hex_oStar_nadj h25 hD6 cycD ha0_notD ib' ib hn1 hn2, hb⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨cycD.inj.ne hq1, fun h => ha0_notD (h ▸ ccwCycle_mem cycD q), cycD.inj.ne hq2⟩

private lemma hex_convD_erase0_hp {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hside0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
          orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S z) H_hp)
    {M0 : Finset (Fin n)} (z : Fin n) (F : Finset (Fin n))
    (hz : z ∈ interiorPoints S \ M0) (h5F : cycD.toFun 5 ∈ F) (h1F : cycD.toFun 1 ∈ F)
    (hzD : S z ∈ convexHull ℝ ((hullVertices S \ certifiedVertices S w).image S : Set (ℝ × ℝ)))
    (hzn : S z ∉ convexHull ℝ ((((hullVertices S \ certifiedVertices S w).erase (cycD.toFun 0)).image S : Set (ℝ × ℝ)))) :
    ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp := by
  let D := hullVertices S \ certifiedVertices S w
  let Q1 : Finset (Fin n) := {cycD.toFun 0}
  have hD_er : D.erase (cycD.toFun 0) = D \ Q1 := (Finset.sdiff_singleton_eq_erase _ _).symm
  change S z ∉ convexHull ℝ ((D.erase (cycD.toFun 0)).image S : Set (ℝ × ℝ)) at hzn
  rw [hD_er] at hzn
  have hDQ1 : 3 ≤ (D \ Q1).card := by
    have hs : D \ Q1 = D.erase (cycD.toFun 0) := Finset.sdiff_singleton_eq_erase _ _
    rw [hs, Finset.card_erase_of_mem (ccwCycle_mem cycD 0)]; omega
  obtain ⟨p, hpQ, hside⟩ := convexHull_erase_of_chord_opposite (Finset.singleton_subset_iff.mpr (ccwCycle_mem cycD 0))
    hDQ1 cycD (hullVertices_convexPos S Finset.sdiff_subset)
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (fun _ => (cycD.toFun 5, cycD.toFun 1))
    (fun p hp => by
      rw [Finset.mem_singleton] at hp; subst hp
      refine ⟨Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 5, by simp [cycD.inj.ne (by decide : (5 : Fin 6) ≠ 0)]⟩,
        Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 1, by simp [cycD.inj.ne (by decide : (1 : Fin 6) ≠ 0)]⟩,
        cycD.inj.ne (by decide : (5 : Fin 6) ≠ 1),
        hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
          (Or.inl (Set.mem_range_self _)) (hPoly.s_inj.ne (cycD.inj.ne (by decide : (5 : Fin 6) ≠ 1)))
          (hPoly.s_inj.ne (cycD.inj.ne (by decide : (1 : Fin 6) ≠ 0)))
          (hPoly.s_inj.ne (cycD.inj.ne (by decide : (5 : Fin 6) ≠ 0)))⟩)
    (S z) hzD hzn
  rw [Finset.mem_singleton] at hpQ; subst hpQ
  exact hex_lift_hp h5F h1F (hside0 z (Finset.mem_sdiff.mp hz).1 hside)

private lemma hex_convD_erase1_hp {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hside1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
          orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S z) H_hp)
    {M0 : Finset (Fin n)} (z : Fin n) (F : Finset (Fin n))
    (hz : z ∈ interiorPoints S \ M0) (h0F : cycD.toFun 0 ∈ F) (h2F : cycD.toFun 2 ∈ F)
    (hzD : S z ∈ convexHull ℝ ((hullVertices S \ certifiedVertices S w).image S : Set (ℝ × ℝ)))
    (hzn : S z ∉ convexHull ℝ ((((hullVertices S \ certifiedVertices S w).erase (cycD.toFun 1)).image S : Set (ℝ × ℝ)))) :
    ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp := by
  let D := hullVertices S \ certifiedVertices S w
  let Q1 : Finset (Fin n) := {cycD.toFun 1}
  have hD_er : D.erase (cycD.toFun 1) = D \ Q1 := (Finset.sdiff_singleton_eq_erase _ _).symm
  change S z ∉ convexHull ℝ ((D.erase (cycD.toFun 1)).image S : Set (ℝ × ℝ)) at hzn
  rw [hD_er] at hzn
  have hDQ1 : 3 ≤ (D \ Q1).card := by
    have hs : D \ Q1 = D.erase (cycD.toFun 1) := Finset.sdiff_singleton_eq_erase _ _
    rw [hs, Finset.card_erase_of_mem (ccwCycle_mem cycD 1)]; omega
  obtain ⟨p, hpQ, hside⟩ := convexHull_erase_of_chord_opposite (Finset.singleton_subset_iff.mpr (ccwCycle_mem cycD 1))
    hDQ1 cycD (hullVertices_convexPos S Finset.sdiff_subset)
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (fun _ => (cycD.toFun 0, cycD.toFun 2))
    (fun p hp => by
      rw [Finset.mem_singleton] at hp; subst hp
      refine ⟨Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 0, by simp [cycD.inj.ne (by decide : (0 : Fin 6) ≠ 1)]⟩,
        Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [cycD.inj.ne (by decide : (2 : Fin 6) ≠ 1)]⟩,
        cycD.inj.ne (by decide : (0 : Fin 6) ≠ 2),
        hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
          (Or.inl (Set.mem_range_self _)) (hPoly.s_inj.ne (cycD.inj.ne (by decide : (0 : Fin 6) ≠ 2)))
          (hPoly.s_inj.ne (cycD.inj.ne (by decide : (2 : Fin 6) ≠ 1)))
          (hPoly.s_inj.ne (cycD.inj.ne (by decide : (0 : Fin 6) ≠ 1)))⟩)
    (S z) hzD hzn
  rw [Finset.mem_singleton] at hpQ; subst hpQ
  exact hex_lift_hp h0F h2F (hside1 z (Finset.mem_sdiff.mp hz).1 hside)

private def hex_make_cyc_er0 {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 3) : CCWCycle S (D.erase (cycD.toFun 0)) 2 :=
  ccwCycle_of_sub_cyclic cycD hexIdxEr0 hex_er0_inj
    (by ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨j, rfl⟩
          fin_cases j <;> exact ⟨cycD.inj.ne (by decide), ccwCycle_mem cycD _⟩
        · rintro ⟨hx0, hxD⟩
          obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cycD hxD
          have hix0 : ix ≠ 0 := fun h => hx0 (congrArg cycD.toFun h)
          fin_cases ix
          · exact absurd rfl hix0
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨4, rfl⟩)
    hex_er0_ord

private def hex_make_cyc_er1 {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 3) : CCWCycle S (D.erase (cycD.toFun 1)) 2 :=
  ccwCycle_of_sub_cyclic cycD hexIdxEr1 hex_er1_inj
    (by ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · rintro ⟨j, rfl⟩
          fin_cases j <;> exact ⟨cycD.inj.ne (by decide), ccwCycle_mem cycD _⟩
        · rintro ⟨hx1, hxD⟩
          obtain ⟨ix, rfl⟩ := ccwCycle_exists_index cycD hxD
          have hix1 : ix ≠ 1 := fun h => hx1 (congrArg cycD.toFun h)
          fin_cases ix
          · exact ⟨4, rfl⟩
          · exact absurd rfl hix1
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨3, rfl⟩)
    hex_er1_ord

private lemma hex_pure_singleton_with_p01 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hBack0 : ∃ O : Finset (Fin n), cycD.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 0) (w (Finset.univ \ O)))
    (hhp0 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S (cycD.toFun 0)) H_hp)
    (hside0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
          orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S z) H_hp)
    (hBack1 : ∃ O : Finset (Fin n), cycD.toFun 1 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ O)))
    (hhp1 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) H_hp)
    (hside1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
          orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S z) H_hp)
    {a0 : Fin n} (ha0M : a0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (p j ib' ib : Fin 6) (hp01 : p = 0 ∨ p = 1)
    (hjm1 : j ≠ p - 1) (hjeq : j ≠ p) (hjp1 : j ≠ p + 1)
    (hn1 : ib ≠ ib' + 1) (hn2 : ib' ≠ ib + 1) (hj_ib' : j ≠ ib') (hj_ib : j ≠ ib)
    (hz_j : ∀ z : Fin n, z ≠ cycD.toFun (j - 1) → z ≠ cycD.toFun (j + 1) → z ∉ ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({cycD.toFun j, cycD.toFun (j - 1), cycD.toFun (j + 1)} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      SegmentsCross (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})) (S z) (S (cycD.toFun (j - 1))) (S (cycD.toFun (j + 1))) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun (j - 1), cycD.toFun (j + 1)} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib}))))
    (hjb : IsBackVertexOf S (hullVertices S) (cycD.toFun j) (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})))
    (hhpj : ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun (j - 1), cycD.toFun (j + 1)} ∅ w) (S (cycD.toFun j)) H_hp)
    (hnlr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      l ∈ hullVertices S \ certifiedVertices S w → r ∈ hullVertices S \ certifiedVertices S w →
      l ≠ r → IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ cycD.toFun p ∧ r ≠ cycD.toFun p ∧ l ≠ cycD.toFun j ∧ r ≠ cycD.toFun j) :
    False := by
  let B := hullVertices S; let H := certifiedVertices S w; let D := B \ H
  let M := Finset.univ \ D; let M0 : Finset (Fin n) := {a0}
  have hM0_sub : M0 ⊆ M := Finset.singleton_subset_iff.mpr ha0M
  have ha0_notD : a0 ∉ D := (Finset.mem_sdiff.mp ha0M).2
  have hM'_card : 3 ≤ (M \ M0).card := by
    have hs : M \ M0 = M.erase a0 := Finset.sdiff_singleton_eq_erase a0 M
    rw [hs, Finset.card_erase_of_mem ha0M]; omega
  let Q : Finset (Fin n) := {cycD.toFun p, cycD.toFun j}
  have hpj : cycD.toFun p ≠ cycD.toFun j := cycD.inj.ne hjeq.symm
  have hQ2 : Q.card = 2 := Finset.card_pair hpj
  have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
  have hjm1_ne_p : j - 1 ≠ p := fun h => hjp1 (by rw [← h, sub_add_cancel])
  have hjp1_ne_p : j + 1 ≠ p := fun h => hjm1 (by rw [← h, add_sub_cancel_right])
  have hjm1F : cycD.toFun (j - 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne hjm1_ne_p, cycD.inj.ne (fin6_sub1_ne j)]⟩)
  have hjp1F : cycD.toFun (j + 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne hjp1_ne_p, cycD.inj.ne (fin6_add1_ne j)]⟩)
  have hpm1F : cycD.toFun (p - 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne (fin6_sub1_ne p), cycD.inj.ne hjm1.symm]⟩)
  have hpp1F : cycD.toFun (p + 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne (fin6_add1_ne p), cycD.inj.ne hjp1.symm]⟩)
  have hBackp : ∃ O, cycD.toFun p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B (cycD.toFun p) (w (Finset.univ \ O)) := by
    rcases hp01 with rfl | rfl <;> assumption
  have hhpp : ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (p - 1), cycD.toFun (p + 1)} ∅ w) (S (cycD.toFun p)) H_hp := by
    rcases hp01 with rfl | rfl
    · rw [show (0 - 1 : Fin 6) = 5 from rfl, show (0 + 1 : Fin 6) = 1 from rfl]; exact hhp0
    · rw [show (1 - 1 : Fin 6) = 0 from rfl, show (1 + 1 : Fin 6) = 2 from rfl]; exact hhp1
  have hO_sub : ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) ⊆ D ∪ M0 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
  have h_tri_gap : ∀ z ∈ interiorPoints S \ M0,
      S z ∈ convexHull ℝ (({cycD.toFun j, cycD.toFun (j - 1), cycD.toFun (j + 1)} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet ((D \ Q) ∪ M0) ∅ w) (S z) H_hp := by
    intro z hz hconv
    have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
    have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
    have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
    exact hex_lift_hp hjm1F hjp1F (hz_j z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD _)))
      (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD _))) (fun h => hz_nDM0 (hO_sub h)) hconv).2.1
  have h_tri_pure_opaque : ∀ (ia ib : Fin 6),
      (ia = j - 1 ∨ ia = j ∨ ia = j + 1) →
      (ib = j - 1 ∨ ib = j ∨ ib = j + 1) →
      convexHull ℝ ({S (cycD.toFun ia), S (cycD.toFun ib), S (cycD.toFun (j - 1))} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({cycD.toFun j, cycD.toFun (j - 1), cycD.toFun (j + 1)} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
    intro ia ib hx hy
    refine convexHull_tri_subset ?_ ?_ (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by simp))))
    · rcases hx with rfl | rfl | rfl <;> exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by simp)))
    · rcases hy with rfl | rfl | rfl <;> exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by simp)))
  have h_right_pure_opaque : ∀ (ia ib : Fin 6), ia ≠ p → ia ≠ j → ib ≠ p → ib ≠ j →
      convexHull ℝ ({S (cycD.toFun ia), S (cycD.toFun ib), S (cycD.toFun (j - 1))} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((((D \ Q) ∪ M0).image S : Set (ℝ × ℝ)) ∪ {w ((D \ Q) ∪ M0)}) := by
    intro ia ib h1 h2 h3 h4
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne h1, cycD.inj.ne h2]⟩))))))
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne h3, cycD.inj.ne h4]⟩))))))
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hjm1F))))
  let make_cyc_er0 := hex_make_cyc_er0 cycD
  let make_cyc_er1 := hex_make_cyc_er1 cycD
  have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
    (fun x hx => by
      simp [Q] at hx; rcases hx with rfl | rfl
      · exact hBackp
      · exact hex_mk_back_O h25 hD6 cycD ha0_notD j ib' ib hn1 hn2 hj_ib' hj_ib hjb)
    (fun x hx => by
      simp [Q] at hx; rcases hx with rfl | rfl
      · exact hex_lift_hp hpm1F hpp1F hhpp
      · exact hex_lift_hp hjm1F hjp1F hhpj)
    (fun l r hHne hlD hrD hlne hlr hH_neg => by
      have h_lr := hnlr l r hHne hlD hrD hlne hlr hH_neg
      simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨h_lr.1, h_lr.2.2.1⟩, ⟨h_lr.2.1, h_lr.2.2.2⟩⟩)
    (fun z hz hzD => by
      rcases hp01 with rfl | rfl
      · by_cases hzm : S z ∈ convexHull ℝ ((D.erase (cycD.toFun 0)).image S : Set (ℝ × ℝ))
        · let p0 : Fin 5 → ℝ × ℝ := fun i => S (make_cyc_er0.toFun i)
          have hz_r : S z ∈ convexHull ℝ (Set.range p0) := by
            have hr : Set.range p0 = ((D.erase (cycD.toFun 0)).image S : Set (ℝ × ℝ)) := by
              conv_rhs => rw [← make_cyc_er0.image_eq]
              ext y; simp [p0]
            rwa [hr]
          obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover p0 make_cyc_er0.ccw (S (cycD.toFun (j - 1))) (S z) hz_r
          rcases hex_er0_pure_split j hjm1 hjeq hjp1 m with ⟨hm1, hm2⟩ | ⟨h1, h2, h3, h4⟩
          · left; exact h_tri_gap z hz (h_tri_pure_opaque (hexIdxEr0 m) (hexIdxEr0 (m + 1)) hm1 hm2 hm)
          · right; exact h_right_pure_opaque (hexIdxEr0 m) (hexIdxEr0 (m + 1)) h1 h2 h3 h4 hm
        · left; exact hex_convD_erase0_hp hPoly hD6 cycD hside0 z ((D \ Q) ∪ M0) hz hpm1F hpp1F hzD hzm
      · by_cases hzm : S z ∈ convexHull ℝ ((D.erase (cycD.toFun 1)).image S : Set (ℝ × ℝ))
        · let p1 : Fin 5 → ℝ × ℝ := fun i => S (make_cyc_er1.toFun i)
          have hz_r : S z ∈ convexHull ℝ (Set.range p1) := by
            have hr : Set.range p1 = ((D.erase (cycD.toFun 1)).image S : Set (ℝ × ℝ)) := by
              conv_rhs => rw [← make_cyc_er1.image_eq]
              ext y; simp [p1]
            rwa [hr]
          obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover p1 make_cyc_er1.ccw (S (cycD.toFun (j - 1))) (S z) hz_r
          rcases hex_er1_pure_split j hjm1 hjeq hjp1 m with ⟨hm1, hm2⟩ | ⟨h1, h2, h3, h4⟩
          · left; exact h_tri_gap z hz (h_tri_pure_opaque (hexIdxEr1 m) (hexIdxEr1 (m + 1)) hm1 hm2 hm)
          · right; exact h_right_pure_opaque (hexIdxEr1 m) (hexIdxEr1 (m + 1)) h1 h2 h3 h4 hm
        · left; exact hex_convD_erase1_hp hPoly hD6 cycD hside1 z ((D \ Q) ∪ M0) hz hpm1F hpp1F hzD hzm)
  have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega

private lemma hex_mixed_singleton_with_p01 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hBack0 : ∃ O : Finset (Fin n), cycD.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 0) (w (Finset.univ \ O)))
    (hhp0 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S (cycD.toFun 0)) H_hp)
    (hside0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
          orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S z) H_hp)
    (hBack1 : ∃ O : Finset (Fin n), cycD.toFun 1 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ O)))
    (hhp1 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) H_hp)
    (hside1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
          orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S z) H_hp)
    (k : Fin 6) {a0 : Fin n} (ha0M : a0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (h_empty_tri : ∀ z ∈ interiorPoints S \ ({a0} : Finset (Fin n)),
      ¬ InClosedTri (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0) (S z))
    (p j d_anc ib' ib : Fin 6) (oa ob : Fin n)
    (hp01 : p = 0 ∨ p = 1) (hk123 : k = 1 ∨ k = 2 ∨ k = 3)
    (hjd : j = k ∧ d_anc = k - 1 ∨ j = k + 1 ∧ d_anc = k + 2)
    (hoaob : oa = cycD.toFun d_anc ∧ ob = a0 ∨ oa = a0 ∧ ob = cycD.toFun d_anc)
    (hjm1 : j ≠ p - 1) (hjeq : j ≠ p) (hjp1 : j ≠ p + 1) (hda_p : d_anc ≠ p)
    (hn1 : ib ≠ ib' + 1) (hn2 : ib' ≠ ib + 1) (hj_ib' : j ≠ ib') (hj_ib : j ≠ ib)
    (hz_j : ∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({cycD.toFun j, oa, ob} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      SegmentsCross (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})) (S z) (S oa) (S ob) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib}))))
    (hjb : IsBackVertexOf S (hullVertices S) (cycD.toFun j) (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})))
    (hhpj : ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S (cycD.toFun j)) H_hp)
    (hnlr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      l ∈ hullVertices S \ certifiedVertices S w → r ∈ hullVertices S \ certifiedVertices S w →
      l ≠ r → IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ cycD.toFun p ∧ r ≠ cycD.toFun p ∧ l ≠ cycD.toFun j ∧ r ≠ cycD.toFun j) :
    False := by
  let B := hullVertices S; let H := certifiedVertices S w; let D := B \ H
  let M := Finset.univ \ D; let M0 : Finset (Fin n) := {a0}
  have hM0_sub : M0 ⊆ M := Finset.singleton_subset_iff.mpr ha0M
  have ha0_notD : a0 ∉ D := (Finset.mem_sdiff.mp ha0M).2
  have hM'_card : 3 ≤ (M \ M0).card := by
    have hs : M \ M0 = M.erase a0 := Finset.sdiff_singleton_eq_erase a0 M
    rw [hs, Finset.card_erase_of_mem ha0M]; omega
  let Q : Finset (Fin n) := {cycD.toFun p, cycD.toFun j}
  have hpj : cycD.toFun p ≠ cycD.toFun j := cycD.inj.ne hjeq.symm
  have hQ2 : Q.card = 2 := Finset.card_pair hpj
  have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
  have ha0F : a0 ∈ (D \ Q) ∪ M0 := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hda_ne_j : d_anc ≠ j := by
    rcases hjd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fin6_sub1_ne _
    · exact fin6_add2_ne_add1 _
  have hdaF : cycD.toFun d_anc ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne hda_p, cycD.inj.ne hda_ne_j]⟩)
  have hoaF : oa ∈ (D \ Q) ∪ M0 := by rcases hoaob with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact hdaF; exact ha0F
  have hobF : ob ∈ (D \ Q) ∪ M0 := by rcases hoaob with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact ha0F; exact hdaF
  have hpm1F : cycD.toFun (p - 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne (fin6_sub1_ne p), cycD.inj.ne hjm1.symm]⟩)
  have hpp1F : cycD.toFun (p + 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne (fin6_add1_ne p), cycD.inj.ne hjp1.symm]⟩)
  have hBackp : ∃ O, cycD.toFun p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B (cycD.toFun p) (w (Finset.univ \ O)) := by
    rcases hp01 with rfl | rfl <;> assumption
  have hhpp : ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (p - 1), cycD.toFun (p + 1)} ∅ w) (S (cycD.toFun p)) H_hp := by
    rcases hp01 with rfl | rfl
    · rw [show (0 - 1 : Fin 6) = 5 from rfl, show (0 + 1 : Fin 6) = 1 from rfl]; exact hhp0
    · rw [show (1 - 1 : Fin 6) = 0 from rfl, show (1 + 1 : Fin 6) = 2 from rfl]; exact hhp1
  have hO_sub : ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) ⊆ D ∪ M0 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
  have hoa_mem : oa ∈ D ∪ M0 := by rcases hoaob with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact Finset.mem_union_left _ (ccwCycle_mem cycD _); exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hob_mem : ob ∈ D ∪ M0 := by rcases hoaob with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact Finset.mem_union_right _ (Finset.mem_singleton_self _); exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
  have h_pair_mem : ∀ x : Fin n, (x = cycD.toFun j ∨ x = cycD.toFun d_anc ∨ x = a0) →
      x ∈ ({cycD.toFun j, oa, ob} : Finset (Fin n)) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · rcases hoaob with ⟨rfl, _⟩ | ⟨_, rfl⟩; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr rfl)
    · rcases hoaob with ⟨_, rfl⟩ | ⟨rfl, _⟩; exact Or.inr (Or.inr rfl); exact Or.inr (Or.inl rfl)
  have h_tri_mixed_opaque : ∀ (ia ib : Fin 6),
      (ia = j ∨ ia = d_anc) → (ib = j ∨ ib = d_anc) →
      convexHull ℝ ({S (cycD.toFun ia), S (cycD.toFun ib), S a0} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({cycD.toFun j, oa, ob} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
    intro ia ib hx hy
    refine convexHull_tri_subset ?_ ?_
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (h_pair_mem a0 (Or.inr (Or.inr rfl))))))
    · rcases hx with rfl | rfl
      · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (h_pair_mem (cycD.toFun ia) (Or.inl rfl))))
      · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (h_pair_mem (cycD.toFun ia) (Or.inr (Or.inl rfl)))))
    · rcases hy with rfl | rfl
      · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (h_pair_mem (cycD.toFun ib) (Or.inl rfl))))
      · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (h_pair_mem (cycD.toFun ib) (Or.inr (Or.inl rfl)))))
  have h_right_mixed_opaque : ∀ (ia ib : Fin 6), ia ≠ p → ia ≠ j → ib ≠ p → ib ≠ j →
      convexHull ℝ ({S (cycD.toFun ia), S (cycD.toFun ib), S a0} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((((D \ Q) ∪ M0).image S : Set (ℝ × ℝ)) ∪ {w ((D \ Q) ∪ M0)}) := by
    intro ia ib h1 h2 h3 h4
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne h1, cycD.inj.ne h2]⟩))))))
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne h3, cycD.inj.ne h4]⟩))))))
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F))))
  let make_cyc_er0 := hex_make_cyc_er0 cycD
  let make_cyc_er1 := hex_make_cyc_er1 cycD
  have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
    (fun x hx => by
      simp [Q] at hx; rcases hx with rfl | rfl
      · exact hBackp
      · exact hex_mk_back_O h25 hD6 cycD ha0_notD j ib' ib hn1 hn2 hj_ib' hj_ib hjb)
    (fun x hx => by
      simp [Q] at hx; rcases hx with rfl | rfl
      · exact hex_lift_hp hpm1F hpp1F hhpp
      · exact hex_lift_hp hoaF hobF hhpj)
    (fun l r hHne hlD hrD hlne hlr hH_neg => by
      have h_lr := hnlr l r hHne hlD hrD hlne hlr hH_neg
      simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨h_lr.1, h_lr.2.2.1⟩, ⟨h_lr.2.1, h_lr.2.2.2⟩⟩)
    (fun z hz hzD => by
      rcases hp01 with rfl | rfl
      · by_cases hzm : S z ∈ convexHull ℝ ((D.erase (cycD.toFun 0)).image S : Set (ℝ × ℝ))
        · let p0 : Fin 5 → ℝ × ℝ := fun i => S (make_cyc_er0.toFun i)
          have hz_r : S z ∈ convexHull ℝ (Set.range p0) := by
            have hr : Set.range p0 = ((D.erase (cycD.toFun 0)).image S : Set (ℝ × ℝ)) := by
              conv_rhs => rw [← make_cyc_er0.image_eq]
              ext y; simp [p0]
            rwa [hr]
          obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover p0 make_cyc_er0.ccw (S a0) (S z) hz_r
          rcases hex_er0_mixed_split k j d_anc hk123 hjd hjm1 hjeq hjp1 m with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ | ⟨h1, h2, h3, h4⟩
          · exfalso; apply h_empty_tri z hz
            have hhm : S z ∈ convexHull ℝ ({S (cycD.toFun (hexIdxEr0 m)), S (cycD.toFun (hexIdxEr0 (m + 1))), S a0} : Set (ℝ × ℝ)) := hm
            rw [hm1, hm2] at hhm
            exact (inClosedTri_iff_mem_convexHull _ _ _ _).mpr hhm
          · left; refine hex_lift_hp hoaF hobF ?_
            have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
            have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
            have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
            exact (hz_j z (fun h => hz_nDM0 (h ▸ hoa_mem)) (fun h => hz_nDM0 (h ▸ hob_mem)) (fun h => hz_nDM0 (hO_sub h))
              (h_tri_mixed_opaque (hexIdxEr0 m) (hexIdxEr0 (m + 1)) hm1 hm2 hm)).2.1
          · right; exact h_right_mixed_opaque (hexIdxEr0 m) (hexIdxEr0 (m + 1)) h1 h2 h3 h4 hm
        · left; exact hex_convD_erase0_hp hPoly hD6 cycD hside0 z ((D \ Q) ∪ M0) hz hpm1F hpp1F hzD hzm
      · by_cases hzm : S z ∈ convexHull ℝ ((D.erase (cycD.toFun 1)).image S : Set (ℝ × ℝ))
        · let p1 : Fin 5 → ℝ × ℝ := fun i => S (make_cyc_er1.toFun i)
          have hz_r : S z ∈ convexHull ℝ (Set.range p1) := by
            have hr : Set.range p1 = ((D.erase (cycD.toFun 1)).image S : Set (ℝ × ℝ)) := by
              conv_rhs => rw [← make_cyc_er1.image_eq]
              ext y; simp [p1]
            rwa [hr]
          obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover p1 make_cyc_er1.ccw (S a0) (S z) hz_r
          rcases hex_er1_mixed_split k j d_anc hk123 hjd hjm1 hjeq hjp1 m with ⟨hm1, hm2⟩ | ⟨hm1, hm2⟩ | ⟨h1, h2, h3, h4⟩
          · exfalso; apply h_empty_tri z hz
            have hhm : S z ∈ convexHull ℝ ({S (cycD.toFun (hexIdxEr1 m)), S (cycD.toFun (hexIdxEr1 (m + 1))), S a0} : Set (ℝ × ℝ)) := hm
            rw [hm1, hm2] at hhm
            exact (inClosedTri_iff_mem_convexHull _ _ _ _).mpr hhm
          · left; refine hex_lift_hp hoaF hobF ?_
            have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
            have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
            have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
            exact (hz_j z (fun h => hz_nDM0 (h ▸ hoa_mem)) (fun h => hz_nDM0 (h ▸ hob_mem)) (fun h => hz_nDM0 (hO_sub h))
              (h_tri_mixed_opaque (hexIdxEr1 m) (hexIdxEr1 (m + 1)) hm1 hm2 hm)).2.1
          · right; exact h_right_mixed_opaque (hexIdxEr1 m) (hexIdxEr1 (m + 1)) h1 h2 h3 h4 hm
        · left; exact hex_convD_erase1_hp hPoly hD6 cycD hside1 z ((D \ Q) ∪ M0) hz hpm1F hpp1F hzD hzm)
  have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega

private lemma hex_pure_size2_gap {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    {a0 : Fin n} (ha0M : a0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (g1 ib' ib : Fin 6) (hn1 : ib ≠ ib' + 1) (hn2 : ib' ≠ ib + 1)
    (hg1_ib' : g1 ≠ ib') (hg1_ib : g1 ≠ ib) (hg2_ib' : g1 + 1 ≠ ib') (hg2_ib : g1 + 1 ≠ ib)
    (hz_g : ∀ z : Fin n, z ≠ cycD.toFun (g1 - 1) → z ≠ cycD.toFun (g1 + 2) → z ∉ ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({cycD.toFun g1, cycD.toFun (g1 + 1), cycD.toFun (g1 - 1), cycD.toFun (g1 + 2)} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      SegmentsCross (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})) (S z) (S (cycD.toFun (g1 - 1))) (S (cycD.toFun (g1 + 2))) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun (g1 - 1), cycD.toFun (g1 + 2)} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib}))))
    (hg1b : IsBackVertexOf S (hullVertices S) (cycD.toFun g1) (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})))
    (hg2b : IsBackVertexOf S (hullVertices S) (cycD.toFun (g1 + 1)) (w (Finset.univ \ {cycD.toFun ib', a0, cycD.toFun ib})))
    (hhp1' : ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (g1 - 1), cycD.toFun (g1 + 2)} ∅ w) (S (cycD.toFun g1)) H_hp)
    (hhp2' : ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (g1 - 1), cycD.toFun (g1 + 2)} ∅ w) (S (cycD.toFun (g1 + 1))) H_hp)
    (hnlr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      l ∈ hullVertices S \ certifiedVertices S w → r ∈ hullVertices S \ certifiedVertices S w →
      l ≠ r → IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ cycD.toFun g1 ∧ r ≠ cycD.toFun g1 ∧ l ≠ cycD.toFun (g1 + 1) ∧ r ≠ cycD.toFun (g1 + 1)) :
    False := by
  let B := hullVertices S; let H := certifiedVertices S w; let D := B \ H
  let M := Finset.univ \ D; let M0 : Finset (Fin n) := {a0}
  have hM0_sub : M0 ⊆ M := Finset.singleton_subset_iff.mpr ha0M
  have ha0_notD : a0 ∉ D := (Finset.mem_sdiff.mp ha0M).2
  have hM'_card : 3 ≤ (M \ M0).card := by
    have hs : M \ M0 = M.erase a0 := Finset.sdiff_singleton_eq_erase a0 M
    rw [hs, Finset.card_erase_of_mem ha0M]; omega
  let Q : Finset (Fin n) := {cycD.toFun g1, cycD.toFun (g1 + 1)}
  have hg12 : cycD.toFun g1 ≠ cycD.toFun (g1 + 1) := cycD.inj.ne (fin6_add1_ne g1).symm
  have hQ2 : Q.card = 2 := Finset.card_pair hg12
  have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
  have hm1_F : cycD.toFun (g1 - 1) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by
      simp [Q, cycD.inj.ne (fin6_sub1_ne g1), cycD.inj.ne (fin6_sub1_ne_add1 g1)]⟩)
  have hp2_F : cycD.toFun (g1 + 2) ∈ (D \ Q) ∪ M0 :=
    Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by
      intro h; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact (by decide : ∀ x : Fin 6, x + 2 ≠ x) _ (cycD.inj h)
      · exact (by decide : ∀ x : Fin 6, x + 2 ≠ x + 1) _ (cycD.inj h)⟩)
  have hO_sub : ({cycD.toFun ib', a0, cycD.toFun ib} : Finset (Fin n)) ⊆ D ∪ M0 := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact Finset.mem_union_left _ (ccwCycle_mem cycD _)
  have h_tri_s2_opaque : ∀ (ia ib : Fin 6),
      (ia = g1 - 1 ∨ ia = g1 ∨ ia = g1 + 1 ∨ ia = g1 + 2) →
      (ib = g1 - 1 ∨ ib = g1 ∨ ib = g1 + 1 ∨ ib = g1 + 2) →
      convexHull ℝ ({S (cycD.toFun ia), S (cycD.toFun ib), S (cycD.toFun (g1 - 1))} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({cycD.toFun g1, cycD.toFun (g1 + 1), cycD.toFun (g1 - 1), cycD.toFun (g1 + 2)} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
    intro ia ib hx hy
    refine convexHull_tri_subset ?_ ?_ (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by simp))))
    · rcases hx with rfl | rfl | rfl | rfl <;> exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by simp)))
    · rcases hy with rfl | rfl | rfl | rfl <;> exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by simp)))
  have h_right_s2_opaque : ∀ (ia ib : Fin 6), ia ≠ g1 → ia ≠ g1 + 1 → ib ≠ g1 → ib ≠ g1 + 1 →
      convexHull ℝ ({S (cycD.toFun ia), S (cycD.toFun ib), S (cycD.toFun (g1 - 1))} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ((((D \ Q) ∪ M0).image S : Set (ℝ × ℝ)) ∪ {w ((D \ Q) ∪ M0)}) := by
    intro ia ib h1 h2 h3 h4
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne h1, cycD.inj.ne h2]⟩))))))
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [Q, cycD.inj.ne h3, cycD.inj.ne h4]⟩))))))
      (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hm1_F))))
  have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
    (fun x hx => by
      simp [Q] at hx; rcases hx with rfl | rfl
      · exact hex_mk_back_O h25 hD6 cycD ha0_notD g1 ib' ib hn1 hn2 hg1_ib' hg1_ib hg1b
      · exact hex_mk_back_O h25 hD6 cycD ha0_notD (g1 + 1) ib' ib hn1 hn2 hg2_ib' hg2_ib hg2b)
    (fun x hx => by
      simp [Q] at hx; rcases hx with rfl | rfl
      · exact hex_lift_hp hm1_F hp2_F hhp1'
      · exact hex_lift_hp hm1_F hp2_F hhp2')
    (fun l r hHne hlD hrD hlne hlr hH_neg => by
      have h_lr := hnlr l r hHne hlD hrD hlne hlr hH_neg
      simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨h_lr.1, h_lr.2.2.1⟩, ⟨h_lr.2.1, h_lr.2.2.2⟩⟩)
    (fun z hz hzD => by
      let pD : Fin 6 → ℝ × ℝ := fun i => S (cycD.toFun i)
      have hz_r : S z ∈ convexHull ℝ (Set.range pD) := by
        have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
          dsimp [D, B, H]; conv_rhs => rw [← cycD.image_eq]
          ext y; simp [pD]
        rwa [hr]
      obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S (cycD.toFun (g1 - 1))) (S z) hz_r
      rcases hex_size2_split g1 m with ⟨hm1, hm2⟩ | ⟨h1, h2, h3, h4⟩
      · left; refine hex_lift_hp hm1_F hp2_F ?_
        have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
        have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
        have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
        exact (hz_g z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD _)))
          (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD _))) (fun h => hz_nDM0 (hO_sub h))
          (h_tri_s2_opaque m (m + 1) hm1 hm2 hm)).2.1
      · right; exact h_right_s2_opaque m (m + 1) h1 h2 h3 h4 hm)
  have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega

/-- Normalized Section 8.3 contradiction (`|D| = 6`, `4 ≤ |M|`, `0` good from `O0`, `1` good from `O1`,
    with exit edge `(cycD k, cycD (k+1))` for `k ∈ {0, 1, 2, 3}`). -/
private lemma hex_four_cases_contradiction {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hBack0 : ∃ O : Finset (Fin n), cycD.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 0) (w (Finset.univ \ O)))
    (hhp0 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S (cycD.toFun 0)) H_hp)
    (hside0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
          orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S z) H_hp)
    (hBack1 : ∃ O : Finset (Fin n), cycD.toFun 1 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ O)))
    (hhp1 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) H_hp)
    (hside1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
          orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S z) H_hp)
    (k : Fin 6) (hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3)
    {a0 : Fin n} (ha0M : a0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hwD_pos : 0 < orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (w (hullVertices S \ certifiedVertices S w)))
    (ha0_tri : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0))
    (ha0_min : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y) →
      orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0) ≤
        orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y))
    (h_H_ex : (certifiedVertices S w).Nonempty → ∃ h0 ∈ certifiedVertices S w,
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S h0)) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let M0 : Finset (Fin n) := {a0}
  have hM0_sub : M0 ⊆ M := Finset.singleton_subset_iff.mpr ha0M
  have hM'_card : 3 ≤ (M \ M0).card := by
    have hs : M \ M0 = M.erase a0 := Finset.sdiff_singleton_eq_erase a0 M
    rw [hs, Finset.card_erase_of_mem ha0M]; omega
  have ha0_notD : a0 ∉ D := (Finset.mem_sdiff.mp ha0M).2
  have h_empty_tri : ∀ z ∈ interiorPoints S \ M0,
      ¬ InClosedTri (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0) (S z) := by
    intro z hz
    have hzM : z ∈ M := by dsimp [M]; rw [M_eq_interior_union_H S w]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hz).1
    have hza0 : z ≠ a0 := fun h => (Finset.mem_sdiff.mp hz).2 (h ▸ Finset.mem_singleton_self _)
    exact exit_minimal_empty hPoly h25 (by omega) (ccwCycle_isCCWEdge cycD k) hwD_pos ha0_tri ha0_min z
      (Finset.mem_erase.mpr ⟨hza0, hzM⟩)
  have h_not_lr_back : ∀ x ∈ D,
      (∃ O, x ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B x (w (Finset.univ \ O))) →
      ∀ l r : Fin n, H.Nonempty → l ∈ D → r ∈ D → l ≠ r → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
      (l = x ∨ r = x) →
      ∃ il : Fin 6, l = cycD.toFun il ∧ r = cycD.toFun (il + 1) ∧
        ((il = k - 1 ∧ x = cycD.toFun (k - 1) ∧ cycD.toFun k ≠ cycD.toFun 0 ∧ cycD.toFun k ≠ cycD.toFun 1 ∧
          ¬ ∃ O', cycD.toFun k ∉ O' ∧ (∀ a ∈ O' ∩ D, ∀ b ∈ O' ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B (cycD.toFun k) (w (Finset.univ \ O'))) ∨
         (il = k + 1 ∧ x = cycD.toFun (k + 2) ∧ cycD.toFun (k + 1) ≠ cycD.toFun 0 ∧ cycD.toFun (k + 1) ≠ cycD.toFun 1 ∧
          ¬ ∃ O', cycD.toFun (k + 1) ∉ O' ∧ (∀ a ∈ O' ∩ D, ∀ b ∈ O' ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B (cycD.toFun (k + 1)) (w (Finset.univ \ O')))) := by
    intro x hxD hBackx l r hHne hlD hrD hlne hlr hH_neg hx_lr
    obtain ⟨h0, hh0, h0_tri⟩ := h_H_ex hHne
    rw [isCCWEdge_iff_ccwCycle cycD] at hlr
    rcases hlr with ⟨il, rfl, rfl⟩
    have h_not_same : il ≠ k := by
      intro heq; subst heq
      have := h25.exit_edge_lemma (by omega) h0 (by rw [M_eq_interior_union_H S w]; exact Finset.mem_union_right _ hh0)
      rcases this with ⟨u, v, _, _, _, h_nlr, _, h_uniq⟩
      have hu := h_uniq (cycD.toFun il) (cycD.toFun (il + 1)) (ccwCycle_isCCWEdge cycD il) hwD_pos h0_tri.to_convexHull
      exact h_nlr _ _ hHne (ccwCycle_isCCWEdge cycD il) hH_neg (Prod.ext hu.1.symm hu.2.symm)
    rcases hx_lr with rfl | rfl
    · obtain ⟨h_ex, h_nb⟩ := h25.endpoint_back_criterion hHne (by omega)
        (cycD.toFun il) (cycD.toFun (il + 1)) (cycD.toFun il) (cycD.toFun (il + 1))
        hlD hrD hlne (ccwCycle_isCCWEdge cycD il) hH_neg (Or.inl ⟨rfl, rfl⟩) hBackx
      have h_or := h_ex h0 hh0 (cycD.toFun k) (cycD.toFun (k + 1)) (ccwCycle_isCCWEdge cycD k) h0_tri
      rcases h_or with hk0 | hk1
      · have hil : il + 1 = k := cycD.inj hk0.symm
        have hil' : il = k - 1 := eq_sub_of_add_eq hil
        refine ⟨il, rfl, rfl, Or.inl ?_⟩
        refine ⟨hil', congrArg cycD.toFun hil', fun h0' => ?_, fun h1' => ?_, ?_⟩
        · apply h_nb; rw [← hk0, h0']; exact hBack0
        · apply h_nb; rw [← hk0, h1']; exact hBack1
        · rw [← hk0] at h_nb; exact h_nb
      · exfalso; exact h_not_same (add_right_cancel (cycD.inj hk1.symm))
    · obtain ⟨h_ex, h_nb⟩ := h25.endpoint_back_criterion hHne (by omega)
        (cycD.toFun il) (cycD.toFun (il + 1)) (cycD.toFun (il + 1)) (cycD.toFun il)
        hlD hrD hlne (ccwCycle_isCCWEdge cycD il) hH_neg (Or.inr ⟨rfl, rfl⟩) hBackx
      have h_or := h_ex h0 hh0 (cycD.toFun k) (cycD.toFun (k + 1)) (ccwCycle_isCCWEdge cycD k) h0_tri
      rcases h_or with hk0 | hk1
      · exfalso; exact h_not_same (cycD.inj hk0.symm)
      · have hil : il = k + 1 := cycD.inj hk1.symm
        have hil2 : il + 1 = k + 2 := by rw [hil]; exact fin6_add1_add1 k
        refine ⟨il, rfl, rfl, Or.inr ?_⟩
        refine ⟨hil, congrArg cycD.toFun hil2, fun h0' => ?_, fun h1' => ?_, ?_⟩
        · apply h_nb; rw [← hk1, h0']; exact hBack0
        · apply h_nb; rw [← hk1, h1']; exact hBack1
        · rw [← hk1] at h_nb; exact h_nb
  have h_not_lr_k0 : k = 0 → ∀ x ∈ D,
      (∃ O, x ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B x (w (Finset.univ \ O))) →
      ∀ l r : Fin n, H.Nonempty → l ∈ D → r ∈ D → l ≠ r → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ x ∧ r ≠ x := by
    intro hk0 x hxD hBx l r hHne hlD hrD hlne hlr hH_neg
    subst hk0
    constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back x hxD hBx l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
    · rcases hcas with ⟨_, _, hne0, _⟩ | ⟨_, _, _, hne1, _⟩
      · exact hne0 rfl
      · exact hne1 (congrArg cycD.toFun (by decide : (0 + 1 : Fin 6) = 1))
    · rcases hcas with ⟨_, _, hne0, _⟩ | ⟨_, _, _, hne1, _⟩
      · exact hne0 rfl
      · exact hne1 (congrArg cycD.toFun (by decide : (0 + 1 : Fin 6) = 1))
  have h_int_setup : ∀ (ib' iu0 iv0 ib id_v : Fin 6), iv0 = iu0 + 1 →
      0 < (iu0 - ib').val → (iu0 - ib').val < (iv0 - ib').val →
      (iv0 - ib').val < (ib - ib').val → (ib - ib').val < (id_v - ib').val →
      iu0 = k →
      (0 < orient2D (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (w D) ∧
       InIntTri (w D) (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S a0) ∧
       (∀ x ∈ WitnessSet {cycD.toFun iu0, cycD.toFun iv0} ∅ w,
         InIntTri x (S (cycD.toFun iu0)) (S (cycD.toFun iv0)) (S a0)) ∧
       (∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
         (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → (cycD.toFun iu0, cycD.toFun iv0) ≠ (l, r))) := by
    intro ib' iu0 iv0 ib id_v hiv0 _ _ _ _ hiu
    subst hiu; subst hiv0
    refine ⟨hwD_pos, ha0_tri, ?_, fun l r hHne hlr hH_neg => ?_⟩
    · obtain ⟨u, v, _, _, _, _, hW, h_uniq⟩ := h25.exit_edge_lemma (by omega) a0 ha0M
      have hu := h_uniq (cycD.toFun iu0) (cycD.toFun (iu0 + 1)) (ccwCycle_isCCWEdge cycD iu0) hwD_pos ha0_tri.to_convexHull
      rw [← hu.1, ← hu.2] at hW; exact hW
    · obtain ⟨u, v, _, _, _, h_nlr, _, h_uniq⟩ := h25.exit_edge_lemma (by omega) a0 ha0M
      have hu := h_uniq (cycD.toFun iu0) (cycD.toFun (iu0 + 1)) (ccwCycle_isCCWEdge cycD iu0) hwD_pos ha0_tri.to_convexHull
      rw [← hu.1, ← hu.2] at h_nlr; exact h_nlr l r hHne hlr hH_neg
  let lift_hp := @hex_lift_hp n P S w
  let mk_back_O := hex_mk_back_O h25 hD6 cycD ha0_notD
  let pure_singleton_with_p01 := hex_pure_singleton_with_p01 hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 ha0M
  let mixed_singleton_with_p01 := hex_mixed_singleton_with_p01 hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 k ha0M h_empty_tri
  let pure_size2_gap := hex_pure_size2_gap hPoly h25 hD6 hM4 cycD ha0M
  -- Now split on `k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3`
  rcases hk with rfl | rfl | rfl | rfl
  · -- k = 0 (`01`)
    have hs2 := h_int_setup 4 0 1 2 3 rfl (by decide) (by decide) (by decide) (by decide) rfl
    have hs3 := h_int_setup 5 0 1 3 4 rfl (by decide) (by decide) (by decide) (by decide) rfl
    obtain ⟨_, oa2, ob2, Γ2, hΓ2, hG2, hgap2, hz2⟩ :=
      interior_anchor hPoly h25 rfl cycD ha0M 4 0 1 2 3 rfl (by decide) (by decide) (by decide) (by decide) hs2
    obtain ⟨_, oa3, ob3, Γ3, hΓ3, hG3, hgap3, hz3⟩ :=
      interior_anchor hPoly h25 rfl cycD ha0M 5 0 1 3 4 rfl (by decide) (by decide) (by decide) (by decide) hs3
    have hO2_sub : ({cycD.toFun 4, a0, cycD.toFun 2} : Finset (Fin n)) ⊆ D ∪ M0 := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_union_left _ (ccwCycle_mem cycD 4)
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · exact Finset.mem_union_left _ (ccwCycle_mem cycD 2)
    have hO3_sub : ({cycD.toFun 5, a0, cycD.toFun 3} : Finset (Fin n)) ⊆ D ∪ M0 := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_union_left _ (ccwCycle_mem cycD 5)
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · exact Finset.mem_union_left _ (ccwCycle_mem cycD 3)
    rcases hΓ2 with ⟨hoa2, hob2, rfl⟩ | ⟨hoa2, hob2, rfl⟩ | ⟨hoa2, hob2, rfl⟩
    · -- O*2 gapL: {5, 0} anchors {4, a0}
      rw [hoa2, hob2] at hG2 hgap2 hz2
      have h5b := hgap2 (cycD.toFun 5) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 5, 5, rfl, by decide, by decide⟩)
      have h0b := hgap2 (cycD.toFun 0) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)
      let Q : Finset (Fin n) := {cycD.toFun 5, cycD.toFun 0}
      have h50 : cycD.toFun 5 ≠ cycD.toFun 0 := cycD.inj.ne (by decide)
      have hQ2 : Q.card = 2 := Finset.card_pair h50
      have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
      have h4F : cycD.toFun 4 ∈ (D \ Q) ∪ M0 :=
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, cycD.inj.ne (by decide : (4:Fin 6)≠5), cycD.inj.ne (by decide : (4:Fin 6)≠0)]⟩)
      have ha0F : a0 ∈ (D \ Q) ∪ M0 := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hD_F : ∀ j : Fin 6, j ≠ 5 → j ≠ 0 → cycD.toFun j ∈ (D \ Q) ∪ M0 := fun j hj5 hj0 =>
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD j, by simp [Q, cycD.inj.ne hj5, cycD.inj.ne hj0]⟩)
      have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
        (fun p hp => by
          simp [Q] at hp; rcases hp with rfl | rfl
          · exact mk_back_O 5 4 2 (by decide) (by decide) (by decide) (by decide) h5b.1
          · exact mk_back_O 0 4 2 (by decide) (by decide) (by decide) (by decide) h0b.1)
        (fun p hp => by
          simp [Q] at hp; rcases hp with rfl | rfl
          · exact lift_hp h4F ha0F h5b.2.2
          · exact lift_hp h4F ha0F h0b.2.2)
        (fun l r hHne hlD hrD hlne hlr hH_neg => by
          have h_5 := h_not_lr_k0 rfl (cycD.toFun 5) (ccwCycle_mem cycD 5)
            (mk_back_O 5 4 2 (by decide) (by decide) (by decide) (by decide) h5b.1) l r hHne hlD hrD hlne hlr hH_neg
          have h_0 := h_not_lr_k0 rfl (cycD.toFun 0) (ccwCycle_mem cycD 0)
            (mk_back_O 0 4 2 (by decide) (by decide) (by decide) (by decide) h0b.1) l r hHne hlD hrD hlne hlr hH_neg
          simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨⟨h_5.1, h_0.1⟩, ⟨h_5.2, h_0.2⟩⟩)
        (fun z hz hzD => by
          let pD : Fin 6 → ℝ × ℝ := fun i => S (cycD.toFun i)
          have hz_r : S z ∈ convexHull ℝ (Set.range pD) := by
            have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
              dsimp [D, B, H]; conv_rhs => rw [← cycD.image_eq]
              ext y; simp [pD]
            rwa [hr]
          obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S a0) (S z) hz_r
          have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
          have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
          have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
          fin_cases m
          · exfalso; exact h_empty_tri z hz ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hm)
          · right; exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 1 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 2 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
          · right; exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 2 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
          · right; exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
          · left; refine lift_hp h4F ha0F (hz2 z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 4)))
              (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _)) (fun h => hz_nDM0 (hO2_sub h)) ?_).2.1
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 5, 5, rfl, by decide, by decide⟩)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm
          · left; refine lift_hp h4F ha0F (hz2 z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 4)))
              (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _)) (fun h => hz_nDM0 (hO2_sub h)) ?_).2.1
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 5, 5, rfl, by decide, by decide⟩)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm)
      have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega
    · -- O*2 gapR: {1} anchors {a0, 2}; now inspect O*3!
      rw [hoa2, hob2] at hG2 hgap2 hz2
      have h1b := hgap2 (cycD.toFun 1) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)
      rcases hΓ3 with ⟨hoa3, hob3, rfl⟩ | ⟨hoa3, hob3, rfl⟩ | ⟨hoa3, hob3, rfl⟩
      · -- O*3 gapL: {0} anchors {5, a0}. Pair Q = {0, 1} with M0 = {a0}!
        rw [hoa3, hob3] at hG3 hgap3 hz3
        have h0b := hgap3 (cycD.toFun 0) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)
        let Q : Finset (Fin n) := {cycD.toFun 0, cycD.toFun 1}
        have h01 : cycD.toFun 0 ≠ cycD.toFun 1 := cycD.inj.ne (by decide)
        have hQ2 : Q.card = 2 := Finset.card_pair h01
        have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
        have h5F : cycD.toFun 5 ∈ (D \ Q) ∪ M0 :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 5, by simp [Q, cycD.inj.ne (by decide : (5:Fin 6)≠0), cycD.inj.ne (by decide : (5:Fin 6)≠1)]⟩)
        have h2F : cycD.toFun 2 ∈ (D \ Q) ∪ M0 :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, cycD.inj.ne (by decide : (2:Fin 6)≠0), cycD.inj.ne (by decide : (2:Fin 6)≠1)]⟩)
        have ha0F : a0 ∈ (D \ Q) ∪ M0 := Finset.mem_union_right _ (Finset.mem_singleton_self _)
        have hD_F : ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → cycD.toFun j ∈ (D \ Q) ∪ M0 := fun j hj0 hj1 =>
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD j, by simp [Q, cycD.inj.ne hj0, cycD.inj.ne hj1]⟩)
        have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
          (fun p hp => by
            simp [Q] at hp; rcases hp with rfl | rfl
            · exact mk_back_O 0 5 3 (by decide) (by decide) (by decide) (by decide) h0b.1
            · exact mk_back_O 1 4 2 (by decide) (by decide) (by decide) (by decide) h1b.1)
          (fun p hp => by
            simp [Q] at hp; rcases hp with rfl | rfl
            · exact lift_hp h5F ha0F h0b.2.2
            · exact lift_hp ha0F h2F h1b.2.2)
          (fun l r hHne hlD hrD hlne hlr hH_neg => by
            have h_0 := h_not_lr_k0 rfl (cycD.toFun 0) (ccwCycle_mem cycD 0)
              (mk_back_O 0 5 3 (by decide) (by decide) (by decide) (by decide) h0b.1) l r hHne hlD hrD hlne hlr hH_neg
            have h_1 := h_not_lr_k0 rfl (cycD.toFun 1) (ccwCycle_mem cycD 1)
              (mk_back_O 1 4 2 (by decide) (by decide) (by decide) (by decide) h1b.1) l r hHne hlD hrD hlne hlr hH_neg
            simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨⟨h_0.1, h_1.1⟩, ⟨h_0.2, h_1.2⟩⟩)
          (fun z hz hzD => by
            let pD : Fin 6 → ℝ × ℝ := fun i => S (cycD.toFun i)
            have hz_r : S z ∈ convexHull ℝ (Set.range pD) := by
              have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
                dsimp [D, B, H]; conv_rhs => rw [← cycD.image_eq]
                ext y; simp [pD]
              rwa [hr]
            obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S a0) (S z) hz_r
            have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
            have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
            have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
            fin_cases m
            · exfalso; exact h_empty_tri z hz ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hm)
            · left; refine lift_hp ha0F h2F (hz2 z (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _))
                (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 2))) (fun h => hz_nDM0 (hO2_sub h)) ?_).2.1
              exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm
            · right; exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 2 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
            · right; exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
            · right; exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 5 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
            · left; refine lift_hp h5F ha0F (hz3 z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 5)))
                (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _)) (fun h => hz_nDM0 (hO3_sub h)) ?_).2.1
              exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm)
        have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega
      · -- O*3 gapR: {1, 2} anchors {a0, 3}. Q = {1, 2}!
        rw [hoa3, hob3] at hG3 hgap3 hz3
        have h1b' := hgap3 (cycD.toFun 1) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)
        have h2b' := hgap3 (cycD.toFun 2) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩)
        let Q : Finset (Fin n) := {cycD.toFun 1, cycD.toFun 2}
        have h12 : cycD.toFun 1 ≠ cycD.toFun 2 := cycD.inj.ne (by decide)
        have hQ2 : Q.card = 2 := Finset.card_pair h12
        have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
        have h3F : cycD.toFun 3 ∈ (D \ Q) ∪ M0 :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, cycD.inj.ne (by decide : (3:Fin 6)≠1), cycD.inj.ne (by decide : (3:Fin 6)≠2)]⟩)
        have ha0F : a0 ∈ (D \ Q) ∪ M0 := Finset.mem_union_right _ (Finset.mem_singleton_self _)
        have hD_F : ∀ j : Fin 6, j ≠ 1 → j ≠ 2 → cycD.toFun j ∈ (D \ Q) ∪ M0 := fun j hj1 hj2 =>
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD j, by simp [Q, cycD.inj.ne hj1, cycD.inj.ne hj2]⟩)
        have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
          (fun p hp => by
            simp [Q] at hp; rcases hp with rfl | rfl
            · exact mk_back_O 1 5 3 (by decide) (by decide) (by decide) (by decide) h1b'.1
            · exact mk_back_O 2 5 3 (by decide) (by decide) (by decide) (by decide) h2b'.1)
          (fun p hp => by
            simp [Q] at hp; rcases hp with rfl | rfl
            · exact lift_hp ha0F h3F h1b'.2.2
            · exact lift_hp ha0F h3F h2b'.2.2)
          (fun l r hHne hlD hrD hlne hlr hH_neg => by
            have h_1 := h_not_lr_k0 rfl (cycD.toFun 1) (ccwCycle_mem cycD 1)
              (mk_back_O 1 5 3 (by decide) (by decide) (by decide) (by decide) h1b'.1) l r hHne hlD hrD hlne hlr hH_neg
            have h_2 := h_not_lr_k0 rfl (cycD.toFun 2) (ccwCycle_mem cycD 2)
              (mk_back_O 2 5 3 (by decide) (by decide) (by decide) (by decide) h2b'.1) l r hHne hlD hrD hlne hlr hH_neg
            simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨⟨h_1.1, h_2.1⟩, ⟨h_1.2, h_2.2⟩⟩)
          (fun z hz hzD => by
            let pD : Fin 6 → ℝ × ℝ := fun i => S (cycD.toFun i)
            have hz_r : S z ∈ convexHull ℝ (Set.range pD) := by
              have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
                dsimp [D, B, H]; conv_rhs => rw [← cycD.image_eq]
                ext y; simp [pD]
              rwa [hr]
            obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S a0) (S z) hz_r
            have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
            have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
            have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
            fin_cases m
            · exfalso; exact h_empty_tri z hz ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hm)
            · left; refine lift_hp ha0F h3F (hz3 z (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _))
                (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 3))) (fun h => hz_nDM0 (hO3_sub h)) ?_).2.1
              exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm
            · left; refine lift_hp ha0F h3F (hz3 z (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _))
                (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 3))) (fun h => hz_nDM0 (hO3_sub h)) ?_).2.1
              exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp)))))
                (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm
            · right; exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
            · right; exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 5 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
            · right; exact convexHull_tri_subset
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 5 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 0 (by decide) (by decide))))))
                (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm)
        have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega
      · -- O*3 gapMid: {4} anchors {3, 5}, paired with p1 = 1!
        rw [hoa3, hob3] at hG3 hgap3 hz3
        have h4b := hgap3 (cycD.toFun 4) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 4, 4, rfl, by decide, by decide⟩)
        refine pure_singleton_with_p01 1 4 5 3 (Or.inr rfl) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) ?_ h4b.1 (by simpa using h4b.2.2) ?_
        · intro z h1 h2 hO hconv
          refine hz3 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
          rcases hx with rfl | rfl | rfl
          · exact Or.inl ⟨ccwCycle_mem cycD 4, 4, rfl, by decide, by decide⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · intro l r hHne hlD hrD hlne hlr hH_neg
          have h1_nlr := h_not_lr_k0 rfl (cycD.toFun 1) (ccwCycle_mem cycD 1) hBack1 l r hHne hlD hrD hlne hlr hH_neg
          have h4_nlr := h_not_lr_k0 rfl (cycD.toFun 4) (ccwCycle_mem cycD 4)
            (mk_back_O 4 5 3 (by decide) (by decide) (by decide) (by decide) h4b.1) l r hHne hlD hrD hlne hlr hH_neg
          exact ⟨h1_nlr.1, h1_nlr.2, h4_nlr.1, h4_nlr.2⟩
    · -- O*2 gapMid: {3} anchors {2, 4}, paired with p0 = 0!
      rw [hoa2, hob2] at hG2 hgap2 hz2
      have h3b := hgap2 (cycD.toFun 3) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 3, 3, rfl, by decide, by decide⟩)
      refine pure_singleton_with_p01 0 3 4 2 (Or.inl rfl) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h3b.1 (by simpa using h3b.2.2) ?_
      · intro z h1 h2 hO hconv
        refine hz2 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 3, 3, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_nlr := h_not_lr_k0 rfl (cycD.toFun 0) (ccwCycle_mem cycD 0) hBack0 l r hHne hlD hrD hlne hlr hH_neg
        have h3_nlr := h_not_lr_k0 rfl (cycD.toFun 3) (ccwCycle_mem cycD 3)
          (mk_back_O 3 4 2 (by decide) (by decide) (by decide) (by decide) h3b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h0_nlr.1, h0_nlr.2, h3_nlr.1, h3_nlr.2⟩
  · -- k = 1 (`12`): O*2 = {5, a0, 3}
    have hs2 := h_int_setup 5 1 2 3 4 rfl (by decide) (by decide) (by decide) (by decide) rfl
    obtain ⟨_, oa2, ob2, Γ2, hΓ2, hG2, hgap2, hz2⟩ :=
      interior_anchor hPoly h25 rfl cycD ha0M 5 1 2 3 4 rfl (by decide) (by decide) (by decide) (by decide) hs2
    have hO2_sub : ({cycD.toFun 5, a0, cycD.toFun 3} : Finset (Fin n)) ⊆ D ∪ M0 := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_union_left _ (ccwCycle_mem cycD 5)
      · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · exact Finset.mem_union_left _ (ccwCycle_mem cycD 3)
    rcases hΓ2 with ⟨hoa2, hob2, rfl⟩ | ⟨hoa2, hob2, rfl⟩ | ⟨hoa2, hob2, rfl⟩
    · -- gapL: {0, 1} anchors {5, a0}
      rw [hoa2, hob2] at hG2 hgap2 hz2
      have h0b := hgap2 (cycD.toFun 0) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)
      have h1b := hgap2 (cycD.toFun 1) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)
      let Q : Finset (Fin n) := {cycD.toFun 0, cycD.toFun 1}
      have h01 : cycD.toFun 0 ≠ cycD.toFun 1 := cycD.inj.ne (by decide)
      have hQ2 : Q.card = 2 := Finset.card_pair h01
      have hQD : Q ⊆ D := by intro x hx; simp [Q] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _
      have h5F : cycD.toFun 5 ∈ (D \ Q) ∪ M0 :=
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 5, by simp [Q, cycD.inj.ne (by decide : (5:Fin 6)≠0), cycD.inj.ne (by decide : (5:Fin 6)≠1)]⟩)
      have ha0F : a0 ∈ (D \ Q) ∪ M0 := Finset.mem_union_right _ (Finset.mem_singleton_self _)
      have hD_F : ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → cycD.toFun j ∈ (D \ Q) ∪ M0 := fun j hj0 hj1 =>
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD j, by simp [Q, cycD.inj.ne hj0, cycD.inj.ne hj1]⟩)
      have h_lr_excl_k1 : ∀ (q : Fin 6), q ≠ 3 →
          (∃ O, cycD.toFun q ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B (cycD.toFun q) (w (Finset.univ \ O))) →
          ∀ l r : Fin n, H.Nonempty → l ∈ D → r ∈ D → l ≠ r → IsCCWEdge S D l r →
          (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ cycD.toFun q ∧ r ≠ cycD.toFun q := by
        intro q hq3 hBq l r hHne hlD hrD hlne hlr hH_neg
        constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun q) (ccwCycle_mem cycD q) hBq l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
        · rcases hcas with ⟨_, hxq, _, hne1, _⟩ | ⟨_, hxq, _, _, _⟩
          · exact hne1 rfl
          · exact hq3 (cycD.inj hxq)
        · rcases hcas with ⟨_, hxq, _, hne1, _⟩ | ⟨_, hxq, _, _, _⟩
          · exact hne1 rfl
          · exact hq3 (cycD.inj hxq)
      have hcomb := combination_cover_from_convD hPoly h25 (by omega) hQD (Or.inr hQ2) hM0_sub
        (fun p hp => by
          simp [Q] at hp; rcases hp with rfl | rfl
          · exact mk_back_O 0 5 3 (by decide) (by decide) (by decide) (by decide) h0b.1
          · exact mk_back_O 1 5 3 (by decide) (by decide) (by decide) (by decide) h1b.1)
        (fun p hp => by
          simp [Q] at hp; rcases hp with rfl | rfl
          · exact lift_hp h5F ha0F h0b.2.2
          · exact lift_hp h5F ha0F h1b.2.2)
        (fun l r hHne hlD hrD hlne hlr hH_neg => by
          have h_0 := h_lr_excl_k1 0 (by decide)
            (mk_back_O 0 5 3 (by decide) (by decide) (by decide) (by decide) h0b.1) l r hHne hlD hrD hlne hlr hH_neg
          have h_1 := h_lr_excl_k1 1 (by decide)
            (mk_back_O 1 5 3 (by decide) (by decide) (by decide) (by decide) h1b.1) l r hHne hlD hrD hlne hlr hH_neg
          simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨⟨h_0.1, h_1.1⟩, ⟨h_0.2, h_1.2⟩⟩)
        (fun z hz hzD => by
          let pD : Fin 6 → ℝ × ℝ := fun i => S (cycD.toFun i)
          have hz_r : S z ∈ convexHull ℝ (Set.range pD) := by
            have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
              dsimp [D, B, H]; conv_rhs => rw [← cycD.image_eq]
              ext y; simp [pD]
            rwa [hr]
          obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S a0) (S z) hz_r
          have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 (Finset.sdiff_subset hd)
          have hz_nM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
          have hz_nDM0 : z ∉ D ∪ M0 := fun h => (Finset.mem_union.mp h).elim hz_nD hz_nM0
          fin_cases m
          · left; refine lift_hp h5F ha0F (hz2 z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 5)))
              (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _)) (fun h => hz_nDM0 (hO2_sub h)) ?_).2.1
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm
          · exfalso; exact h_empty_tri z hz ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hm)
          · right; exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 2 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
          · right; exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 3 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
          · right; exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 4 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hD_F 5 (by decide) (by decide))))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S ha0F)))) hm
          · left; refine lift_hp h5F ha0F (hz2 z (fun h => hz_nDM0 (Finset.mem_union_left _ (h ▸ ccwCycle_mem cycD 5)))
              (fun h => hz_nM0 (h ▸ Finset.mem_singleton_self _)) (fun h => hz_nDM0 (hO2_sub h)) ?_).2.1
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ (by simp))))) hm)
      have hle := hcomb.2.1 hQ2; change (M \ M0).card ≤ 2 at hle; omega
    · -- gapR: {2} anchors {a0, 3}, paired with p0 = 0!
      rw [hoa2, hob2] at hG2 hgap2 hz2
      have h2b := hgap2 (cycD.toFun 2) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩)
      refine mixed_singleton_with_p01 0 2 3 5 3 a0 (cycD.toFun 3) (Or.inl rfl) (Or.inl rfl)
        (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h2b.1 h2b.2.2 ?_
      · intro z h1 h2 hO hconv
        refine hz2 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_nlr : l ≠ cycD.toFun 0 ∧ r ≠ cycD.toFun 0 := by
          constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun 0) (ccwCycle_mem cycD 0) hBack0 l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (0 : Fin 6) ≠ 3) (cycD.inj hx)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (0 : Fin 6) ≠ 3) (cycD.inj hx)
        have h2_nlr : l ≠ cycD.toFun 2 ∧ r ≠ cycD.toFun 2 := by
          constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun 2) (ccwCycle_mem cycD 2)
            (mk_back_O 2 5 3 (by decide) (by decide) (by decide) (by decide) h2b.1) l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (2 : Fin 6) ≠ 3) (cycD.inj hx)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (2 : Fin 6) ≠ 3) (cycD.inj hx)
        exact ⟨h0_nlr.1, h0_nlr.2, h2_nlr.1, h2_nlr.2⟩
    · -- gapMid: {4} anchors {3, 5}, paired with p0 = 0!
      rw [hoa2, hob2] at hG2 hgap2 hz2
      have h4b := hgap2 (cycD.toFun 4) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 4, 4, rfl, by decide, by decide⟩)
      refine pure_singleton_with_p01 0 4 5 3 (Or.inl rfl) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h4b.1 (by simpa using h4b.2.2) ?_
      · intro z h1 h2 hO hconv
        refine hz2 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 4, 4, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_nlr : l ≠ cycD.toFun 0 ∧ r ≠ cycD.toFun 0 := by
          constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun 0) (ccwCycle_mem cycD 0) hBack0 l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (0 : Fin 6) ≠ 3) (cycD.inj hx)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (0 : Fin 6) ≠ 3) (cycD.inj hx)
        have h4_nlr : l ≠ cycD.toFun 4 ∧ r ≠ cycD.toFun 4 := by
          constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun 4) (ccwCycle_mem cycD 4)
            (mk_back_O 4 5 3 (by decide) (by decide) (by decide) (by decide) h4b.1) l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (4 : Fin 6) ≠ 3) (cycD.inj hx)
          · rcases hcas with ⟨_, _, _, hne1, _⟩ | ⟨_, hx, _, _, _⟩; exact hne1 rfl; exact (by decide : (4 : Fin 6) ≠ 3) (cycD.inj hx)
        exact ⟨h0_nlr.1, h0_nlr.2, h4_nlr.1, h4_nlr.2⟩
  · -- k = 2 (`23`): O*1 = {1, a0, 4}
    have hs1 := h_int_setup 1 2 3 4 5 rfl (by decide) (by decide) (by decide) (by decide) rfl
    obtain ⟨_, oa1, ob1, Γ1, hΓ1, hG1, hgap1, hz1⟩ :=
      interior_anchor hPoly h25 rfl cycD ha0M 1 2 3 4 5 rfl (by decide) (by decide) (by decide) (by decide) hs1
    have h_nlr_k2 : ∀ (q : Fin 6), q ≠ 1 → q ≠ 4 →
        (∃ O, cycD.toFun q ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B (cycD.toFun q) (w (Finset.univ \ O))) →
        ∀ l r : Fin n, H.Nonempty → l ∈ D → r ∈ D → l ≠ r → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ cycD.toFun q ∧ r ≠ cycD.toFun q := by
      intro q hq1 hq4 hBq l r hHne hlD hrD hlne hlr hH_neg
      constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun q) (ccwCycle_mem cycD q) hBq l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
      · rcases hcas with ⟨_, hx, _, _, _⟩ | ⟨_, hx, _, _, _⟩
        · exact hq1 (cycD.inj hx)
        · exact hq4 (cycD.inj hx)
      · rcases hcas with ⟨_, hx, _, _, _⟩ | ⟨_, hx, _, _, _⟩
        · exact hq1 (cycD.inj hx)
        · exact hq4 (cycD.inj hx)
    rcases hΓ1 with ⟨hoa1, hob1, hΓ_eq⟩ | ⟨hoa1, hob1, hΓ_eq⟩ | ⟨hoa1, hob1, hΓ_eq⟩
    · -- gapL: {2} anchors {1, a0}, paired with p0 = 0!
      rw [hoa1, hob1, hΓ_eq] at hgap1 hz1
      have h2b := hgap1 (cycD.toFun 2) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩)
      refine mixed_singleton_with_p01 0 2 1 1 4 (cycD.toFun 1) a0 (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h2b.1 h2b.2.2 ?_
      · intro z h1 h2 hO hconv
        refine hz1 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 2, 2, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_n := h_nlr_k2 0 (by decide) (by decide) hBack0 l r hHne hlD hrD hlne hlr hH_neg
        have h2_n := h_nlr_k2 2 (by decide) (by decide)
          (mk_back_O 2 1 4 (by decide) (by decide) (by decide) (by decide) h2b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h0_n.1, h0_n.2, h2_n.1, h2_n.2⟩
    · -- gapR: {3} anchors {a0, 4}, paired with p0 = 0!
      rw [hoa1, hob1, hΓ_eq] at hgap1 hz1
      have h3b := hgap1 (cycD.toFun 3) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 3, 3, rfl, by decide, by decide⟩)
      refine mixed_singleton_with_p01 0 3 4 1 4 a0 (cycD.toFun 4) (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h3b.1 h3b.2.2 ?_
      · intro z h1 h2 hO hconv
        refine hz1 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 3, 3, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_n := h_nlr_k2 0 (by decide) (by decide) hBack0 l r hHne hlD hrD hlne hlr hH_neg
        have h3_n := h_nlr_k2 3 (by decide) (by decide)
          (mk_back_O 3 1 4 (by decide) (by decide) (by decide) (by decide) h3b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h0_n.1, h0_n.2, h3_n.1, h3_n.2⟩
    · -- gapMid: {5, 0} anchors {4, 1}
      rw [hoa1, hob1, hΓ_eq] at hgap1 hz1
      have h5b := hgap1 (cycD.toFun 5) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 5, 5, rfl, by decide, by decide⟩)
      have h0b := hgap1 (cycD.toFun 0) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)
      refine pure_size2_gap 5 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        ?_ h5b.1 (by simpa using h0b.1)
        (by simpa [Finset.pair_comm] using h5b.2.2) (by simpa [Finset.pair_comm] using h0b.2.2) ?_
      · intro z h1 h2 hO hconv
        refine hz1 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 5, 5, rfl, by decide, by decide⟩
        · exact Or.inl ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h5_n := h_nlr_k2 5 (by decide) (by decide)
          (mk_back_O 5 1 4 (by decide) (by decide) (by decide) (by decide) h5b.1) l r hHne hlD hrD hlne hlr hH_neg
        have h0_n := h_nlr_k2 0 (by decide) (by decide)
          (mk_back_O 0 1 4 (by decide) (by decide) (by decide) (by decide) h0b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h5_n.1, h5_n.2, h0_n.1, h0_n.2⟩
  · -- k = 3 (`34`): O*1 = {2, a0, 5}
    have hs1 := h_int_setup 2 3 4 5 0 rfl (by decide) (by decide) (by decide) (by decide) rfl
    obtain ⟨_, oa1, ob1, Γ1, hΓ1, hG1, hgap1, hz1⟩ :=
      interior_anchor hPoly h25 rfl cycD ha0M 2 3 4 5 0 rfl (by decide) (by decide) (by decide) (by decide) hs1
    have h_nlr_k3 : ∀ (q : Fin 6), q ≠ 2 → q ≠ 5 →
        (∃ O, cycD.toFun q ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B (cycD.toFun q) (w (Finset.univ \ O))) →
        ∀ l r : Fin n, H.Nonempty → l ∈ D → r ∈ D → l ≠ r → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ cycD.toFun q ∧ r ≠ cycD.toFun q := by
      intro q hq2 hq5 hBq l r hHne hlD hrD hlne hlr hH_neg
      constructor <;> intro h <;> obtain ⟨_, _, _, hcas⟩ := h_not_lr_back (cycD.toFun q) (ccwCycle_mem cycD q) hBq l r hHne hlD hrD hlne hlr hH_neg (by first | exact Or.inl h | exact Or.inr h)
      · rcases hcas with ⟨_, hx, _, _, _⟩ | ⟨_, hx, _, _, _⟩
        · exact hq2 (cycD.inj hx)
        · exact hq5 (cycD.inj hx)
      · rcases hcas with ⟨_, hx, _, _, _⟩ | ⟨_, hx, _, _, _⟩
        · exact hq2 (cycD.inj hx)
        · exact hq5 (cycD.inj hx)
    rcases hΓ1 with ⟨hoa1, hob1, hΓ_eq⟩ | ⟨hoa1, hob1, hΓ_eq⟩ | ⟨hoa1, hob1, hΓ_eq⟩
    · -- gapL: {3} anchors {2, a0}, paired with p0 = 0!
      rw [hoa1, hob1, hΓ_eq] at hgap1 hz1
      have h3b := hgap1 (cycD.toFun 3) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 3, 3, rfl, by decide, by decide⟩)
      refine mixed_singleton_with_p01 0 3 2 2 5 (cycD.toFun 2) a0 (Or.inl rfl) (Or.inr (Or.inr rfl))
        (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h3b.1 h3b.2.2 ?_
      · intro z h1 h2 hO hconv
        refine hz1 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 3, 3, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_n := h_nlr_k3 0 (by decide) (by decide) hBack0 l r hHne hlD hrD hlne hlr hH_neg
        have h3_n := h_nlr_k3 3 (by decide) (by decide)
          (mk_back_O 3 2 5 (by decide) (by decide) (by decide) (by decide) h3b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h0_n.1, h0_n.2, h3_n.1, h3_n.2⟩
    · -- gapR: {4} anchors {a0, 5}, paired with p1 = 1!
      rw [hoa1, hob1, hΓ_eq] at hgap1 hz1
      have h4b := hgap1 (cycD.toFun 4) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 4, 4, rfl, by decide, by decide⟩)
      refine mixed_singleton_with_p01 1 4 5 2 5 a0 (cycD.toFun 5) (Or.inr rfl) (Or.inr (Or.inr rfl))
        (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) ?_ h4b.1 h4b.2.2 ?_
      · intro z h1 h2 hO hconv
        refine hz1 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 4, 4, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h1_n := h_nlr_k3 1 (by decide) (by decide) hBack1 l r hHne hlD hrD hlne hlr hH_neg
        have h4_n := h_nlr_k3 4 (by decide) (by decide)
          (mk_back_O 4 2 5 (by decide) (by decide) (by decide) (by decide) h4b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h1_n.1, h1_n.2, h4_n.1, h4_n.2⟩
    · -- gapMid: {0, 1} anchors {5, 2}
      rw [hoa1, hob1, hΓ_eq] at hgap1 hz1
      have h0b := hgap1 (cycD.toFun 0) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩)
      have h1b := hgap1 (cycD.toFun 1) (Finset.mem_filter.mpr ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩)
      refine pure_size2_gap 0 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        ?_ h0b.1 (by simpa using h1b.1)
        (by rw [show (0 - 1 : Fin 6) = 5 from rfl, show (0 + 2 : Fin 6) = 2 from rfl]; exact h0b.2.2)
        (by rw [show (0 - 1 : Fin 6) = 5 from rfl, show (0 + 2 : Fin 6) = 2 from rfl, show (0 + 1 : Fin 6) = 1 from rfl]; exact h1b.2.2) ?_
      · intro z h1 h2 hO hconv
        refine hz1 z h1 h2 hO (convexHull_mono (Finset.image_subset_image fun x hx => ?_) hconv)
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_filter] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨ccwCycle_mem cycD 0, 0, rfl, by decide, by decide⟩
        · exact Or.inl ⟨ccwCycle_mem cycD 1, 1, rfl, by decide, by decide⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · intro l r hHne hlD hrD hlne hlr hH_neg
        have h0_n := h_nlr_k3 0 (by decide) (by decide)
          (mk_back_O 0 2 5 (by decide) (by decide) (by decide) (by decide) h0b.1) l r hHne hlD hrD hlne hlr hH_neg
        have h1_n := h_nlr_k3 1 (by decide) (by decide)
          (mk_back_O 1 2 5 (by decide) (by decide) (by decide) (by decide) h1b.1) l r hHne hlD hrD hlne hlr hH_neg
        exact ⟨h0_n.1, h0_n.2, h1_n.1, h1_n.2⟩

private lemma hex_refl_step {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hBack0 : ∃ O : Finset (Fin n), cycD.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 0) (w (Finset.univ \ O)))
    (hhp0 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S (cycD.toFun 0)) H_hp)
    (hside0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
          orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S z) H_hp)
    (hBack1 : ∃ O : Finset (Fin n), cycD.toFun 1 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ O)))
    (hhp1 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) H_hp)
    (hside1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
          orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S z) H_hp)
    {k : Fin 6} (hk : k = 4 ∨ k = 5)
    {a0 : Fin n} (ha0M : a0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hwD_pos : 0 < orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (w (hullVertices S \ certifiedVertices S w)))
    (ha0_tri : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0))
    (ha0_min : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y) →
      orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0) ≤
        orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y))
    (hkH : (certifiedVertices S w).Nonempty → ∃ h0 ∈ certifiedVertices S w,
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S h0)) :
    False := by
  let D := hullVertices S \ certifiedVertices S w
  let P' := reflPt '' P
  let S' := reflPt ∘ S
  let w' := reflPt ∘ w
  have hPoly' := reflPt_shattered hPoly
  have h25' := reflPt_sec2to5 hPoly h25
  have hD_eq' : hullVertices S' \ certifiedVertices S' w' = D := by
    simp [S', w', D, reflPt_hullVertices, reflPt_certifiedVertices]
  let cycD' : CCWCycle S' (hullVertices S' \ certifiedVertices S' w') 3 :=
    ccwCycle_cast hD_eq'.symm (ccwCycle_rev cycD 1)
  have hD6' : (hullVertices S' \ certifiedVertices S' w').card = 6 := by rwa [hD_eq']
  have hM4' : 4 ≤ (Finset.univ \ (hullVertices S' \ certifiedVertices S' w')).card := by rwa [hD_eq']
  have ha0M' : a0 ∈ Finset.univ \ (hullVertices S' \ certifiedVertices S' w') := by rwa [hD_eq']
  have hc0 : cycD'.toFun 0 = cycD.toFun 1 := rfl
  have hc1 : cycD'.toFun 1 = cycD.toFun 0 := rfl
  have hc2 : cycD'.toFun 2 = cycD.toFun 5 := rfl
  have hc3 : cycD'.toFun 3 = cycD.toFun 4 := rfl
  have hc5 : cycD'.toFun 5 = cycD.toFun 2 := rfl
  have hB0' : ∃ O, cycD'.toFun 0 ∉ O ∧ (∀ a ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'),
      ∀ b ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'), ¬ IsCCWEdge S' (hullVertices S') a b) ∧
      IsBackVertexOf S' (hullVertices S') (cycD'.toFun 0) (w' (Finset.univ \ O)) := by
    obtain ⟨O, h1, h2, h3⟩ := hBack1
    refine ⟨O, h1, fun a ha b hb hed => ?_, ?_⟩
    · rw [hD_eq'] at ha hb; dsimp [D] at ha hb
      dsimp [S'] at hed; rw [reflPt_hullVertices] at hed
      exact h2 b hb a ha ((reflPt_isCCWEdge S (hullVertices S) a b).mp hed)
    · rw [hc0]; dsimp [S', w']
      rw [reflPt_hullVertices, reflPt_isBackVertexOf]; exact h3
  have hB1' : ∃ O, cycD'.toFun 1 ∉ O ∧ (∀ a ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'),
      ∀ b ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'), ¬ IsCCWEdge S' (hullVertices S') a b) ∧
      IsBackVertexOf S' (hullVertices S') (cycD'.toFun 1) (w' (Finset.univ \ O)) := by
    obtain ⟨O, h1, h2, h3⟩ := hBack0
    refine ⟨O, h1, fun a ha b hb hed => ?_, ?_⟩
    · rw [hD_eq'] at ha hb; dsimp [D] at ha hb
      dsimp [S'] at hed; rw [reflPt_hullVertices] at hed
      exact h2 b hb a ha ((reflPt_isCCWEdge S (hullVertices S) a b).mp hed)
    · rw [hc1]; dsimp [S', w']
      rw [reflPt_hullVertices, reflPt_isBackVertexOf]; exact h3
  have hhp0' : ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycD'.toFun 5, cycD'.toFun 1} ∅ w') (S' (cycD'.toFun 0)) H_hp := by
    obtain ⟨Hp, hHp⟩ := hhp1
    refine ⟨reflHP Hp, ?_⟩
    rw [hc5, hc1, hc0]; dsimp [P', S', w']
    rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
  have hhp1' : ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycD'.toFun 0, cycD'.toFun 2} ∅ w') (S' (cycD'.toFun 1)) H_hp := by
    obtain ⟨Hp, hHp⟩ := hhp0
    refine ⟨reflHP Hp, ?_⟩
    rw [hc0, hc2, hc1]; dsimp [P', S', w']
    rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
  have hs0' : ∀ z ∈ interiorPoints S', 0 < orient2D (S' (cycD'.toFun 5)) (S' (cycD'.toFun 1)) (S' (cycD'.toFun 0)) *
      orient2D (S' (cycD'.toFun 5)) (S' (cycD'.toFun 1)) (S' z) →
      ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycD'.toFun 5, cycD'.toFun 1} ∅ w') (S' z) H_hp := by
    intro z hz hprod
    rw [reflPt_interiorPoints] at hz
    simp only [hc5, hc1, hc0] at hprod ⊢
    dsimp [P', S', w'] at hprod ⊢
    rw [reflPt_orient2D, reflPt_orient2D] at hprod
    have hprod' : 0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
        orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) := by
      unfold orient2D at hprod ⊢; linear_combination hprod
    obtain ⟨Hp, hHp⟩ := hside1 z hz hprod'
    refine ⟨reflHP Hp, ?_⟩
    rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
  have hs1' : ∀ z ∈ interiorPoints S', 0 < orient2D (S' (cycD'.toFun 0)) (S' (cycD'.toFun 2)) (S' (cycD'.toFun 1)) *
      orient2D (S' (cycD'.toFun 0)) (S' (cycD'.toFun 2)) (S' z) →
      ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycD'.toFun 0, cycD'.toFun 2} ∅ w') (S' z) H_hp := by
    intro z hz hprod
    rw [reflPt_interiorPoints] at hz
    simp only [hc0, hc2, hc1] at hprod ⊢
    dsimp [P', S', w'] at hprod ⊢
    rw [reflPt_orient2D, reflPt_orient2D] at hprod
    have hprod' : 0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
        orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) := by
      unfold orient2D at hprod ⊢; linear_combination hprod
    obtain ⟨Hp, hHp⟩ := hside0 z hz hprod'
    refine ⟨reflHP Hp, ?_⟩
    rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
  rcases hk with rfl | rfl
  · rw [show (4 + 1 : Fin 6) = 5 from rfl] at hwD_pos ha0_tri ha0_min hkH
    refine hex_four_cases_contradiction hPoly' h25' hD6' hM4' cycD'
      hB0' hhp0' hs0' hB1' hhp1' hs1' 2 (Or.inr (Or.inr (Or.inl rfl))) ha0M' ?_ ?_ ?_ ?_
    · rw [show (2 + 1 : Fin 6) = 3 from rfl, hc2, hc3, hD_eq']
      dsimp [S', w']; rw [reflPt_orient2D]; unfold orient2D at hwD_pos ⊢; linarith
    · rw [show (2 + 1 : Fin 6) = 3 from rfl, hc2, hc3, hD_eq']
      dsimp [S', w']; rw [reflPt_inIntTri]; exact ha0_tri.symm23
    · intro y hy hy_tri
      rw [show (2 + 1 : Fin 6) = 3 from rfl, hc2, hc3] at hy_tri ⊢
      dsimp [S', w'] at hy hy_tri ⊢
      rw [reflPt_hullVertices, reflPt_certifiedVertices] at hy hy_tri
      rw [reflPt_inIntTri] at hy_tri
      rw [reflPt_orient2D, reflPt_orient2D]
      have := ha0_min y hy hy_tri.symm23
      unfold orient2D at this ⊢; linarith
    · intro hHne'
      rw [reflPt_certifiedVertices] at hHne'
      obtain ⟨h0, hh0, h0t⟩ := hkH hHne'
      refine ⟨h0, by rwa [reflPt_certifiedVertices], ?_⟩
      rw [show (2 + 1 : Fin 6) = 3 from rfl, hc2, hc3, hD_eq']
      dsimp [S', w']; rw [reflPt_inIntTri]; exact h0t.symm23
  · rw [show (5 + 1 : Fin 6) = 0 from rfl] at hwD_pos ha0_tri ha0_min hkH
    refine hex_four_cases_contradiction hPoly' h25' hD6' hM4' cycD'
      hB0' hhp0' hs0' hB1' hhp1' hs1' 1 (Or.inr (Or.inl rfl)) ha0M' ?_ ?_ ?_ ?_
    · rw [show (1 + 1 : Fin 6) = 2 from rfl, hc1, hc2, hD_eq']
      dsimp [S', w']; rw [reflPt_orient2D]; unfold orient2D at hwD_pos ⊢; linarith
    · rw [show (1 + 1 : Fin 6) = 2 from rfl, hc1, hc2, hD_eq']
      dsimp [S', w']; rw [reflPt_inIntTri]; exact ha0_tri.symm23
    · intro y hy hy_tri
      rw [show (1 + 1 : Fin 6) = 2 from rfl, hc1, hc2] at hy_tri ⊢
      dsimp [S', w'] at hy hy_tri ⊢
      rw [reflPt_hullVertices, reflPt_certifiedVertices] at hy hy_tri
      rw [reflPt_inIntTri] at hy_tri
      rw [reflPt_orient2D, reflPt_orient2D]
      have := ha0_min y hy hy_tri.symm23
      unfold orient2D at this ⊢; linarith
    · intro hHne'
      rw [reflPt_certifiedVertices] at hHne'
      obtain ⟨h0, hh0, h0t⟩ := hkH hHne'
      refine ⟨h0, by rwa [reflPt_certifiedVertices], ?_⟩
      rw [show (1 + 1 : Fin 6) = 2 from rfl, hc1, hc2, hD_eq']
      dsimp [S', w']; rw [reflPt_inIntTri]; exact h0t.symm23

private lemma hex_normalized_contradiction {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6)
    (hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 3)
    (hBack0 : ∃ O : Finset (Fin n), cycD.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 0) (w (Finset.univ \ O)))
    (hhp0 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S (cycD.toFun 0)) H_hp)
    (hside0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S (cycD.toFun 0)) *
          orient2D (S (cycD.toFun 5)) (S (cycD.toFun 1)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 5, cycD.toFun 1} ∅ w) (S z) H_hp)
    (hBack1 : ∃ O : Finset (Fin n), cycD.toFun 1 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ O)))
    (hhp1 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) H_hp)
    (hside1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S (cycD.toFun 1)) *
          orient2D (S (cycD.toFun 0)) (S (cycD.toFun 2)) (S z) →
      ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, cycD.toFun 2} ∅ w) (S z) H_hp) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  have hex_edge : ∃ k : Fin 6, (H.Nonempty → ∃ h0 ∈ H, InIntTri (w D) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S h0)) ∧
      ∃ y0 ∈ M, 0 < orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (w D) ∧
        InIntTri (w D) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y0) := by
    by_cases hHne : H.Nonempty
    · obtain ⟨h0, hh0⟩ := hHne
      have hh0M : h0 ∈ M := by dsimp [M]; rw [M_eq_interior_union_H S w]; exact Finset.mem_union_right _ hh0
      obtain ⟨u, v, hed, hpos, hin, _, _, _⟩ := h25.exit_edge_lemma (by omega) h0 hh0M
      rw [isCCWEdge_iff_ccwCycle cycD] at hed
      rcases hed with ⟨k, rfl, rfl⟩
      exact ⟨k, fun _ => ⟨h0, hh0, hin⟩, h0, hh0M, hpos, hin⟩
    · have hMne : M.Nonempty := Finset.card_pos.mp (by dsimp [M, D, B, H]; omega)
      obtain ⟨y0, hy0⟩ := hMne
      obtain ⟨u, v, hed, hpos, hin, _, _, _⟩ := h25.exit_edge_lemma (by omega) y0 hy0
      rw [isCCWEdge_iff_ccwCycle cycD] at hed
      rcases hed with ⟨k, rfl, rfl⟩
      exact ⟨k, fun hH => False.elim (hHne hH), y0, hy0, hpos, hin⟩
  obtain ⟨k, hkH, y0, hy0M, hwD_pos, hy0_tri⟩ := hex_edge
  let M_uv := M.filter (fun y => InIntTri (w D) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y))
  have hy0_uv : y0 ∈ M_uv := Finset.mem_filter.mpr ⟨hy0M, hy0_tri⟩
  obtain ⟨a0, ha0_uv, ha0_min⟩ := Finset.exists_min_image M_uv (fun y => orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y)) ⟨y0, hy0_uv⟩
  have ha0M : a0 ∈ M := (Finset.mem_filter.mp ha0_uv).1
  have ha0_tri : InIntTri (w D) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0) := (Finset.mem_filter.mp ha0_uv).2
  have ha0_min' : ∀ y ∈ M, InIntTri (w D) (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y) →
      orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S a0) ≤ orient2D (S (cycD.toFun k)) (S (cycD.toFun (k + 1))) (S y) :=
    fun y hyM hy_tri => ha0_min y (Finset.mem_filter.mpr ⟨hyM, hy_tri⟩)
  fin_cases k
  · exact hex_four_cases_contradiction hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 0 (Or.inl rfl) ha0M hwD_pos ha0_tri ha0_min' hkH
  · exact hex_four_cases_contradiction hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 1 (Or.inr (Or.inl rfl)) ha0M hwD_pos ha0_tri ha0_min' hkH
  · exact hex_four_cases_contradiction hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 2 (Or.inr (Or.inr (Or.inl rfl))) ha0M hwD_pos ha0_tri ha0_min' hkH
  · exact hex_four_cases_contradiction hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 3 (Or.inr (Or.inr (Or.inr rfl))) ha0M hwD_pos ha0_tri ha0_min' hkH
  · exact hex_refl_step hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 (Or.inl rfl) ha0M hwD_pos ha0_tri ha0_min' hkH
  · exact hex_refl_step hPoly h25 hD6 hM4 cycD hBack0 hhp0 hside0 hBack1 hhp1 hside1 (Or.inr rfl) ha0M hwD_pos ha0_tri ha0_min' hkH

/-- **Section 8.3 (`card_D_six_M_le_three`, `upper_9.tex` lines 932–961)**:
    If `|D| = 6`, then `|M| = |S \ D| ≤ 3` (hence `|S| ≤ 9`). -/
theorem card_D_six_M_le_three {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD6 : (hullVertices S \ certifiedVertices S w).card = 6) :
    (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card ≤ 3 := by
  by_contra hlt; push Not at hlt
  have hM4 : 4 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card := hlt
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  obtain ⟨cycD⟩ := exists_ccwCycle S D
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Finset.sdiff_subset) hD6
  let cycD1 := ccwCycle_shift cycD 1
  obtain ⟨Tgt0, hT0_card, hT0⟩ := good_targets hPoly h25 (Or.inl rfl) (Subset.rfl : D ⊆ D) cycD
  obtain ⟨Tgt1, hT1_card, hT1⟩ := good_targets hPoly h25 (Or.inl rfl) (Subset.rfl : D ⊆ D) cycD1
  have hT0_1 : Tgt0.card = 1 := by simp [hT0_card]
  have hT1_1 : Tgt1.card = 1 := by simp [hT1_card]
  obtain ⟨i0, hi0_eq⟩ := Finset.card_eq_one.mp hT0_1
  obtain ⟨j1, hj1_eq⟩ := Finset.card_eq_one.mp hT1_1
  have hi0_mem : i0 ∈ Tgt0 := hi0_eq ▸ Finset.mem_singleton_self _
  have hj1_mem : j1 ∈ Tgt1 := hj1_eq ▸ Finset.mem_singleton_self _
  have h0_res := hT0 i0 hi0_mem
  have h1_res := hT1 j1 hj1_mem
  let i1 : Fin 6 := 1 + j1
  have hi0_ev : i0.val % 2 = 0 := h0_res.1
  have hj1_ev : j1.val % 2 = 0 := h1_res.1
  have hi1_odd : i1.val % 2 = 1 := by
    dsimp [i1]; rw [Fin.val_add]; have h1v : (1 : Fin 6).val = 1 := by decide
    rw [h1v]; omega
  have hO0_nadj : ∀ a ∈ D.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycD.toFun i = x) ∩ D,
      ∀ b ∈ D.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycD.toFun i = x) ∩ D, ¬ IsCCWEdge S B a b := by
    intro a ha b hb hed
    rcases (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2 with ⟨ia, hia, rfl⟩
    rcases (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2 with ⟨ib, hib, rfl⟩
    refine nonadj_D_implies_nonadj_B h25 (by omega)
      (ccwCycle_mem cycD ia) (ccwCycle_mem cycD ib) (fun he => ?_) hed
    rw [isCCWEdge_iff_ccwCycle cycD] at he
    rcases he with ⟨r, hr1, hr2⟩
    have h1 := cycD.inj hr1.symm; have h2 := cycD.inj hr2.symm
    have hmod : ((r + 1 : Fin 6).val % 2) ≠ r.val % 2 := by
      rw [Fin.val_add]; have h1v : (1 : Fin 6).val = 1 := by decide
      rw [h1v]; omega
    rw [h1] at hmod
    have hia1 : ia + 1 = ib := by rw [← h1, h2]
    rw [hia1] at hmod; omega
  have hO1_nadj : ∀ a ∈ D.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycD1.toFun i = x) ∩ D,
      ∀ b ∈ D.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycD1.toFun i = x) ∩ D, ¬ IsCCWEdge S B a b := by
    intro a ha b hb hed
    rcases (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2 with ⟨ia, hia, rfl⟩
    rcases (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2 with ⟨ib, hib, rfl⟩
    refine nonadj_D_implies_nonadj_B h25 (by omega)
      (ccwCycle_mem cycD1 ia) (ccwCycle_mem cycD1 ib) (fun he => ?_) hed
    rw [isCCWEdge_iff_ccwCycle cycD1] at he
    rcases he with ⟨r, hr1, hr2⟩
    have h1 := cycD1.inj hr1.symm; have h2 := cycD1.inj hr2.symm
    have hmod : ((r + 1 : Fin 6).val % 2) ≠ r.val % 2 := by
      rw [Fin.val_add]; have h1v : (1 : Fin 6).val = 1 := by decide
      rw [h1v]; omega
    rw [h1] at hmod
    have hia1 : ia + 1 = ib := by rw [← h1, h2]
    rw [hia1] at hmod; omega
  let O0 := D.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycD.toFun i = x)
  let O1 := D.filter (fun x => ∃ i : Fin 6, i.val % 2 = 1 ∧ cycD1.toFun i = x)
  have hi0_nO0 : cycD.toFun i0 ∉ O0 := fun hm => by
    rcases (Finset.mem_filter.mp hm).2 with ⟨r, hr, heq⟩; rw [cycD.inj heq] at hr; omega
  have hj1_nO1 : cycD1.toFun j1 ∉ O1 := fun hm => by
    rcases (Finset.mem_filter.mp hm).2 with ⟨r, hr, heq⟩; rw [cycD1.inj heq] at hr; omega
  have hBack_i0 : ∃ O, cycD.toFun i0 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B (cycD.toFun i0) (w (Finset.univ \ O)) :=
    ⟨O0, hi0_nO0, hO0_nadj, h0_res.2.2.1⟩
  have hBack_i1 : ∃ O, cycD.toFun i1 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B (cycD.toFun i1) (w (Finset.univ \ O)) :=
    ⟨O1, hj1_nO1, hO1_nadj, h1_res.2.2.1⟩
  have hside_i0 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun (i0 - 1))) (S (cycD.toFun (i0 + 1))) (S (cycD.toFun i0)) *
          orient2D (S (cycD.toFun (i0 - 1))) (S (cycD.toFun (i0 + 1))) (S z) →
      ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (i0 - 1), cycD.toFun (i0 + 1)} ∅ w) (S z) H_hp := by
    intro z hz hprod
    have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp hz).2 (Finset.sdiff_subset hd)
    have h1 := h0_res.2.2.2.2.2.2 z (fun h => hz_nD (h ▸ ccwCycle_mem cycD _)) (fun h => hz_nD (h ▸ ccwCycle_mem cycD _))
      (fun h => hz_nD (Finset.mem_filter.mp h).1) (mem_convexHull_hullVertices S hPoly.s_inj z) hprod
    exact h1.2.1
  have hside_i1 : ∀ z ∈ interiorPoints S,
      0 < orient2D (S (cycD.toFun (i1 - 1))) (S (cycD.toFun (i1 + 1))) (S (cycD.toFun i1)) *
          orient2D (S (cycD.toFun (i1 - 1))) (S (cycD.toFun (i1 + 1))) (S z) →
      ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (i1 - 1), cycD.toFun (i1 + 1)} ∅ w) (S z) H_hp := by
    intro z hz hprod
    have hz_nD : z ∉ D := fun hd => (Finset.mem_sdiff.mp hz).2 (Finset.sdiff_subset hd)
    have hsub1 : (1 + (j1 - 1) : Fin 6) = i1 - 1 := fin6_1_add_sub1 j1
    have hsub2 : (1 + (j1 + 1) : Fin 6) = i1 + 1 := fin6_1_add_add1 j1
    have h1 := h1_res.2.2.2.2.2.2 z
      (fun h => hz_nD (h ▸ ccwCycle_mem cycD1 _)) (fun h => hz_nD (h ▸ ccwCycle_mem cycD1 _))
      (fun h => hz_nD (Finset.mem_filter.mp h).1) (mem_convexHull_hullVertices S hPoly.s_inj z)
      (by simpa [cycD1, ccwCycle_shift, hsub1, hsub2] using hprod)
    simpa [cycD1, ccwCycle_shift, hsub1, hsub2] using h1.2.1
  have hhp_i0 : ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (i0 - 1), cycD.toFun (i0 + 1)} ∅ w) (S (cycD.toFun i0)) H_hp :=
    h0_res.2.2.2.2.2.1
  have hhp_i1 : ∃ H_hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun (i1 - 1), cycD.toFun (i1 + 1)} ∅ w) (S (cycD.toFun i1)) H_hp := by
    have hsub1 : (1 + (j1 - 1) : Fin 6) = i1 - 1 := fin6_1_add_sub1 j1
    have hsub2 : (1 + (j1 + 1) : Fin 6) = i1 + 1 := fin6_1_add_add1 j1
    simpa [cycD1, ccwCycle_shift, hsub1, hsub2] using h1_res.2.2.2.2.2.1
  by_cases hant : i1 = i0 + 3
  · let anchors : Fin n → Fin n × Fin n := fun x =>
      if x = cycD.toFun i0 then (cycD.toFun (i0 - 1), cycD.toFun (i0 + 1))
      else (cycD.toFun (i1 - 1), cycD.toFun (i1 + 1))
    have hi01_ne : cycD.toFun i0 ≠ cycD.toFun i1 := cycD.inj.ne (fun h => by rw [← h] at hi1_odd; omega)
    have hanti := fin6_antipodal_ne i0
    rw [← hant] at hanti
    obtain ⟨hm1_n1, hp1_n1, h1m1_n0, h1p1_n0⟩ := hanti
    have hmle := combination_M_le_two_of_pureD_anchors hPoly h25 hi01_ne (ccwCycle_mem cycD i0) (ccwCycle_mem cycD i1)
      (by omega) (fun q hq => by simp at hq; rcases hq with rfl | rfl; exact hBack_i0; exact hBack_i1)
      anchors (fun p hp => by
        simp at hp; rcases hp with rfl | rfl
        · simp only [anchors, ↓reduceIte]
          refine ⟨Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [cycD.inj.ne (fin6_sub1_ne i0), cycD.inj.ne hm1_n1]⟩,
            Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [cycD.inj.ne (fin6_add1_ne i0), cycD.inj.ne hp1_n1]⟩,
            cycD.inj.ne (fin6_sub1_ne_add1 i0), ?_, hhp_i0, hside_i0⟩
          exact hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
            (Or.inl (Set.mem_range_self _)) (hPoly.s_inj.ne (cycD.inj.ne (fin6_sub1_ne_add1 i0)))
            (hPoly.s_inj.ne (cycD.inj.ne (fin6_add1_ne i0))) (hPoly.s_inj.ne (cycD.inj.ne (fin6_sub1_ne i0)))
        · simp only [anchors, if_neg hi01_ne.symm]
          refine ⟨Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [cycD.inj.ne h1m1_n0, cycD.inj.ne (fin6_sub1_ne i1)]⟩,
            Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD _, by simp [cycD.inj.ne h1p1_n0, cycD.inj.ne (fin6_add1_ne i1)]⟩,
            cycD.inj.ne (fin6_sub1_ne_add1 i1), ?_, hhp_i1, hside_i1⟩
          exact hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
            (Or.inl (Set.mem_range_self _)) (hPoly.s_inj.ne (cycD.inj.ne (fin6_sub1_ne_add1 i1)))
            (hPoly.s_inj.ne (cycD.inj.ne (fin6_add1_ne i1))) (hPoly.s_inj.ne (cycD.inj.ne (fin6_sub1_ne i1))))
    omega
  · have h_adj : i1 = i0 + 1 ∨ i1 = i0 - 1 := fin6_adj_or_antipodal i0 i1 (by omega) hant
    rcases h_adj with hi1_p | hi1_m
    · let cycS := ccwCycle_shift cycD i0
      have hs0 : cycS.toFun 0 = cycD.toFun i0 := by dsimp [cycS, ccwCycle_shift]; rw [fin6_add0]
      have hs1 : cycS.toFun 1 = cycD.toFun i1 := by dsimp [cycS, ccwCycle_shift]; rw [hi1_p]
      have hs2 : cycS.toFun 2 = cycD.toFun (i1 + 1) := by
        dsimp [cycS, ccwCycle_shift]; rw [hi1_p, fin6_add1_add1]
      have hs5 : cycS.toFun 5 = cycD.toFun (i0 - 1) := by
        dsimp [cycS, ccwCycle_shift]; rw [fin6_add5_eq_sub1]
      have h1m : i1 - 1 = i0 := by rw [hi1_p]; exact fin6_add1_sub1 i0
      refine hex_normalized_contradiction hPoly h25 hD6 hM4 cycS ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hs0]; exact hBack_i0
      · rw [hs5, hs1, hs0, hi1_p]; exact hhp_i0
      · intro z hz hprod; simp only [hs5, hs1, hs0, hi1_p] at hprod ⊢; exact hside_i0 z hz hprod
      · rw [hs1]; exact hBack_i1
      · rw [hs0, hs2, hs1, ← h1m]; exact hhp_i1
      · intro z hz hprod; simp only [hs0, hs2, hs1, ← h1m] at hprod ⊢; exact hside_i1 z hz hprod
    · let P' := reflPt '' P; let S' := reflPt ∘ S; let w' := reflPt ∘ w
      have hPoly' := reflPt_shattered hPoly
      have h25' := reflPt_sec2to5 hPoly h25
      have hD_eq' : hullVertices S' \ certifiedVertices S' w' = D := by
        dsimp [D, B, H]; simp [S', w', reflPt_hullVertices, reflPt_certifiedVertices]
      let cycR : CCWCycle S' (hullVertices S' \ certifiedVertices S' w') 3 :=
        ccwCycle_cast hD_eq'.symm (ccwCycle_rev cycD i0)
      have hD6' : (hullVertices S' \ certifiedVertices S' w').card = 6 := by rwa [hD_eq']
      have hM4' : 4 ≤ (Finset.univ \ (hullVertices S' \ certifiedVertices S' w')).card := by rwa [hD_eq']
      have h_eq0 : cycR.toFun 0 = cycD.toFun i0 := by dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; rw [fin6_sub0]
      have h_eq1 : cycR.toFun 1 = cycD.toFun i1 := by dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; rw [hi1_m]
      have h_eq5 : cycR.toFun 5 = cycD.toFun (i0 + 1) := by dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; rw [fin6_sub5_eq_add1]
      have h_eq2 : cycR.toFun 2 = cycD.toFun (i1 - 1) := by
        dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; rw [hi1_m, fin6_sub1_sub1]
      have hB0' : ∃ O, cycR.toFun 0 ∉ O ∧ (∀ a ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'),
          ∀ b ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'), ¬ IsCCWEdge S' (hullVertices S') a b) ∧
          IsBackVertexOf S' (hullVertices S') (cycR.toFun 0) (w' (Finset.univ \ O)) := by
        obtain ⟨O, h1, h2, h3⟩ := hBack_i0
        refine ⟨O, by rwa [h_eq0], fun a ha b hb hed => ?_, ?_⟩
        · rw [hD_eq'] at ha hb; dsimp [D, B, H] at ha hb
          dsimp [S'] at hed; rw [reflPt_hullVertices] at hed
          exact h2 b hb a ha ((reflPt_isCCWEdge S (hullVertices S) a b).mp hed)
        · rw [h_eq0]; dsimp [S', w']; rw [reflPt_hullVertices, reflPt_isBackVertexOf]; exact h3
      have hB1' : ∃ O, cycR.toFun 1 ∉ O ∧ (∀ a ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'),
          ∀ b ∈ O ∩ (hullVertices S' \ certifiedVertices S' w'), ¬ IsCCWEdge S' (hullVertices S') a b) ∧
          IsBackVertexOf S' (hullVertices S') (cycR.toFun 1) (w' (Finset.univ \ O)) := by
        obtain ⟨O, h1, h2, h3⟩ := hBack_i1
        refine ⟨O, by rwa [h_eq1], fun a ha b hb hed => ?_, ?_⟩
        · rw [hD_eq'] at ha hb; dsimp [D, B, H] at ha hb
          dsimp [S'] at hed; rw [reflPt_hullVertices] at hed
          exact h2 b hb a ha ((reflPt_isCCWEdge S (hullVertices S) a b).mp hed)
        · rw [h_eq1]; dsimp [S', w']; rw [reflPt_hullVertices, reflPt_isBackVertexOf]; exact h3
      have hhp0' : ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycR.toFun 5, cycR.toFun 1} ∅ w') (S' (cycR.toFun 0)) H_hp := by
        obtain ⟨Hp, hHp⟩ := hhp_i0
        refine ⟨reflHP Hp, ?_⟩
        rw [h_eq5, h_eq1, h_eq0, hi1_m]; dsimp [P', S', w']
        rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
      have hhp1' : ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycR.toFun 0, cycR.toFun 2} ∅ w') (S' (cycR.toFun 1)) H_hp := by
        obtain ⟨Hp, hHp⟩ := hhp_i1
        refine ⟨reflHP Hp, ?_⟩
        have hi1p : i1 + 1 = i0 := by rw [hi1_m]; exact fin6_sub1_add1 i0
        rw [h_eq0, h_eq2, h_eq1, ← hi1p]; dsimp [P', S', w']
        rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
      have hs0' : ∀ z ∈ interiorPoints S', 0 < orient2D (S' (cycR.toFun 5)) (S' (cycR.toFun 1)) (S' (cycR.toFun 0)) *
          orient2D (S' (cycR.toFun 5)) (S' (cycR.toFun 1)) (S' z) →
          ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycR.toFun 5, cycR.toFun 1} ∅ w') (S' z) H_hp := by
        intro z hz hprod
        rw [reflPt_interiorPoints] at hz
        simp only [h_eq5, h_eq1, h_eq0, hi1_m] at hprod ⊢
        dsimp [P', S', w'] at hprod ⊢
        rw [reflPt_orient2D, reflPt_orient2D] at hprod
        have hprod' : 0 < orient2D (S (cycD.toFun (i0 - 1))) (S (cycD.toFun (i0 + 1))) (S (cycD.toFun i0)) *
            orient2D (S (cycD.toFun (i0 - 1))) (S (cycD.toFun (i0 + 1))) (S z) := by
          unfold orient2D at hprod ⊢; linear_combination hprod
        obtain ⟨Hp, hHp⟩ := hside_i0 z hz hprod'
        refine ⟨reflHP Hp, ?_⟩
        rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
      have hs1' : ∀ z ∈ interiorPoints S', 0 < orient2D (S' (cycR.toFun 0)) (S' (cycR.toFun 2)) (S' (cycR.toFun 1)) *
          orient2D (S' (cycR.toFun 0)) (S' (cycR.toFun 2)) (S' z) →
          ∃ H_hp, IsHalfPlaneTest P' (WitnessSet {cycR.toFun 0, cycR.toFun 2} ∅ w') (S' z) H_hp := by
        intro z hz hprod
        rw [reflPt_interiorPoints] at hz
        have hi1p : i1 + 1 = i0 := by rw [hi1_m]; exact fin6_sub1_add1 i0
        simp only [h_eq0, h_eq2, h_eq1, ← hi1p] at hprod ⊢
        dsimp [P', S', w'] at hprod ⊢
        rw [reflPt_orient2D, reflPt_orient2D] at hprod
        have hprod' : 0 < orient2D (S (cycD.toFun (i1 - 1))) (S (cycD.toFun (i1 + 1))) (S (cycD.toFun i1)) *
            orient2D (S (cycD.toFun (i1 - 1))) (S (cycD.toFun (i1 + 1))) (S z) := by
          unfold orient2D at hprod ⊢; linear_combination hprod
        obtain ⟨Hp, hHp⟩ := hside_i1 z hz hprod'
        refine ⟨reflHP Hp, ?_⟩
        rw [reflPt_witnessSet, Finset.pair_comm]; exact reflPt_isHalfPlaneTest hHp
      exact hex_normalized_contradiction hPoly' h25' hD6' hM4' cycR hB0' hhp0' hs0' hB1' hhp1' hs1'

/-! ## Part 4: Section 8.4 — Five Non-Certified Vertices (`|D| = 5, |M| = 5`) -/

/-- For any `10`-point `ShatteredSimplePolygon`, `|D| = 5` and `|M| = 5`. -/
theorem ten_points_D5_M5 {P : Set (ℝ × ℝ)}
    {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w) :
    (hullVertices S \ certifiedVertices S w).card = 5 ∧
    (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card = 5 := by
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  have hD7 : D.card ≤ 7 := card_D_le_seven hPoly h25
  have hM5 : M.card ≤ 5 := M_card_le_five h25
  have hsum : D.card + M.card = 10 := by
    have := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin 10)) D
    rw [Finset.univ_inter, Finset.card_fin] at this
    change M.card + D.card = 10 at this
    omega
  have hn7 : D.card ≠ 7 := fun h => by
    have h2 := card_D_seven_M_le_two hPoly h25 h
    change M.card ≤ 2 at h2
    omega
  have hn6 : D.card ≠ 6 := fun h => by
    have h3 := card_D_six_M_le_three hPoly h25 h
    change M.card ≤ 3 at h3
    omega
  change D.card = 5 ∧ M.card = 5
  omega

private lemma orient2D_const_lt_convexHull {u v : ℝ × ℝ} {c : ℝ} {s : Set (ℝ × ℝ)}
    (hs : ∀ x ∈ s, c < orient2D u v x) {p : ℝ × ℝ} (hp : p ∈ convexHull ℝ s) :
    c < orient2D u v p := by
  have hK : Convex ℝ {x : ℝ × ℝ | c < orient2D u v x} := by
    intro a ha b hb α β hα hβ hαβ
    dsimp at ha hb ⊢
    have hid : orient2D u v (α • a + β • b) = α * orient2D u v a + β * orient2D u v b := by
      unfold orient2D; dsimp
      linear_combination (u.2 * v.1 - u.1 * v.2) * hαβ
    rw [hid]
    have hcsum : c = α * c + β * c := by rw [← add_mul, hαβ, one_mul]
    have h1 : α * c ≤ α * orient2D u v a := mul_le_mul_of_nonneg_left (le_of_lt ha) hα
    have h2 : β * c ≤ β * orient2D u v b := mul_le_mul_of_nonneg_left (le_of_lt hb) hβ
    have hne : α ≠ 0 ∨ β ≠ 0 := by
      by_contra h0; push Not at h0; linarith
    rcases hne with hα0 | hβ0
    · have hlt : α * c < α * orient2D u v a :=
        mul_lt_mul_of_pos_left ha (lt_of_le_of_ne hα (Ne.symm hα0))
      linarith
    · have hlt : β * c < β * orient2D u v b :=
        mul_lt_mul_of_pos_left hb (lt_of_le_of_ne hβ (Ne.symm hβ0))
      linarith
  exact convexHull_min hs hK hp

private lemma orient2D_const_le_convexHull {u v : ℝ × ℝ} {c : ℝ} {s : Set (ℝ × ℝ)}
    (hs : ∀ x ∈ s, c ≤ orient2D u v x) {p : ℝ × ℝ} (hp : p ∈ convexHull ℝ s) :
    c ≤ orient2D u v p := by
  have hK : Convex ℝ {x : ℝ × ℝ | c ≤ orient2D u v x} := by
    intro a ha b hb α β hα hβ hαβ
    dsimp at ha hb ⊢
    have hid : orient2D u v (α • a + β • b) = α * orient2D u v a + β * orient2D u v b := by
      unfold orient2D; dsimp
      linear_combination (u.2 * v.1 - u.1 * v.2) * hαβ
    rw [hid]
    have hcsum : c = α * c + β * c := by rw [← add_mul, hαβ, one_mul]
    have h1 : α * c ≤ α * orient2D u v a := mul_le_mul_of_nonneg_left ha hα
    have h2 : β * c ≤ β * orient2D u v b := mul_le_mul_of_nonneg_left hb hβ
    linarith
  exact convexHull_min hs hK hp

private lemma pentagon_gapMid_b1b3_cover {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y : Fin n} (hyM : y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hcross_b2 : SegmentsCross (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2}))
      (S (cyc0.toFun 3)) (S (cyc0.toFun 2)) (S (cyc0.toFun 4)))
    (hgap_mid : GoodAnchorPair P S w {cyc0.toFun 4, y, cyc0.toFun 2} (cyc0.toFun 2) (cyc0.toFun 4))
    (ho_b3b1b2 : 0 < orient2D (S (cyc0.toFun 4)) (S (cyc0.toFun 2)) (S (cyc0.toFun 3)))
    (ho_b3b1y : orient2D (S (cyc0.toFun 4)) (S (cyc0.toFun 2)) (S y) < 0)
    (l r : Fin n) (hlC : l ∈ ({cyc0.toFun 2, cyc0.toFun 3, cyc0.toFun 4} : Finset (Fin n)))
    (hrC : r ∈ ({cyc0.toFun 2, cyc0.toFun 3, cyc0.toFun 4} : Finset (Fin n)))
    (h_edges : ∀ d ∈ hullVertices S \ certifiedVertices S w, d ≠ l → d ≠ r →
      ∀ x ∈ hullVertices S,
        (IsCCWEdge S (hullVertices S) x d ↔ IsCCWEdge S (hullVertices S \ certifiedVertices S w) x d) ∧
        (IsCCWEdge S (hullVertices S) d x ↔ IsCCWEdge S (hullVertices S \ certifiedVertices S w) d x))
    (hH_b3b1 : ∀ h ∈ certifiedVertices S w, 0 < orient2D (S (cyc0.toFun 4)) (S (cyc0.toFun 2)) (S h))
    (hH_cross : ∀ h ∈ certifiedVertices S w,
      SegmentsCross (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2})) (S h) (S (cyc0.toFun 2)) (S (cyc0.toFun 4)))
    {z : Fin n} (hz_nD : z ∉ hullVertices S \ certifiedVertices S w)
    (hzB : S z ∈ convexHull ℝ ((hullVertices S).image S : Set (ℝ × ℝ))) :
    let F := (hullVertices S \ certifiedVertices S w) \ {cyc0.toFun 3} ∪ ∅
    (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) ∨
    S z ∈ convexHull ℝ ((F.image S : Set (ℝ × ℝ)) ∪ {w F}) := by
  intro F
  let B := hullVertices S; let H := certifiedVertices S w; let D := B \ H
  let b1 := cyc0.toFun 2; let b2 := cyc0.toFun 3; let b3 := cyc0.toFun 4
  let O_star : Finset (Fin n) := {b3, y, b1}
  let v := w (Finset.univ \ O_star)
  have hb1F : b1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 2,
    Finset.mem_singleton.not.mpr (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3))⟩)
  have hb3F : b3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 4,
    Finset.mem_singleton.not.mpr (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3))⟩)
  have hn3 : 3 ≤ n := by have hle := Finset.card_le_univ D; rw [Fintype.card_fin] at hle; dsimp [D, B, H] at hle hD5; omega
  obtain ⟨kB, _, ⟨cycB⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
  let CapPts : Finset (Fin n) := {b1, b2, b3} ∪ H
  let pB : Fin (kB + 3) → ℝ × ℝ := fun i => S (cycB.toFun i)
  have hzB' : S z ∈ convexHull ℝ (Set.range pB) := by
    have hr : Set.range pB = (B.image S : Set (ℝ × ℝ)) := by
      dsimp [B]; conv_rhs => rw [← cycB.image_eq]
      ext p; simp [pB]
    rwa [hr]
  obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pB cycB.ccw (S b3) (S z) hzB'
  let u := cycB.toFun m; let vB := cycB.toFun (m + 1)
  have huB : u ∈ B := ccwCycle_mem cycB m
  have hvBB : vB ∈ B := ccwCycle_mem cycB (m + 1)
  have huvB : IsCCWEdge S B u vB := ccwCycle_isCCWEdge cycB m
  have h_edge_split : (u ∈ F ∧ vB ∈ F) ∨ (u ∈ CapPts ∧ vB ∈ CapPts) := by
    by_cases huH : u ∈ H <;> by_cases hvH : vB ∈ H
    · right; exact ⟨Finset.mem_union_right _ huH, Finset.mem_union_right _ hvH⟩
    · have hvD : vB ∈ D := Finset.mem_sdiff.mpr ⟨hvBB, hvH⟩
      right; refine ⟨Finset.mem_union_right _ huH, Finset.mem_union_left _ ?_⟩
      by_contra hnv
      have h_vD := (h_edges vB hvD (fun h => hnv (h ▸ hlC)) (fun h => hnv (h ▸ hrC)) u huB).1.mp huvB
      exact (Finset.mem_sdiff.mp h_vD.1).2 huH
    · have huD : u ∈ D := Finset.mem_sdiff.mpr ⟨huB, huH⟩
      right; refine ⟨Finset.mem_union_left _ ?_, Finset.mem_union_right _ hvH⟩
      by_contra hnu
      have h_uD := (h_edges u huD (fun h => hnu (h ▸ hlC)) (fun h => hnu (h ▸ hrC)) vB hvBB).2.mp huvB
      exact (Finset.mem_sdiff.mp h_uD.2.1).2 hvH
    · have huD : u ∈ D := Finset.mem_sdiff.mpr ⟨huB, huH⟩
      have hvD : vB ∈ D := Finset.mem_sdiff.mpr ⟨hvBB, hvH⟩
      by_cases hu2 : u = b2
      · right
        refine ⟨hu2 ▸ Finset.mem_union_left _ (by dsimp [b2]; simp), ?_⟩
        by_contra hnv
        have h_vD := (h_edges vB hvD (fun h => hnv (Finset.mem_union_left _ (h ▸ hlC)))
          (fun h => hnv (Finset.mem_union_left _ (h ▸ hrC))) u huB).1.mp huvB
        rw [hu2] at h_vD
        have hvb3 : vB = b3 := isCCWEdge_unique_succ cyc0 h_vD (ccwCycle_isCCWEdge cyc0 3)
        exact hnv (Finset.mem_union_left _ (by rw [hvb3]; dsimp [b3]; simp))
      · by_cases hv2 : vB = b2
        · right
          refine ⟨?_, hv2 ▸ Finset.mem_union_left _ (by dsimp [b2]; simp)⟩
          by_contra hnu
          have h_uD := (h_edges u huD (fun h => hnu (Finset.mem_union_left _ (h ▸ hlC)))
            (fun h => hnu (Finset.mem_union_left _ (h ▸ hrC))) vB hvBB).2.mp huvB
          rw [hv2] at h_uD
          have hub1 : u = b1 := isCCWEdge_unique_pred cyc0 h_uD (ccwCycle_isCCWEdge cyc0 2)
          exact hnu (Finset.mem_union_left _ (by rw [hub1]; dsimp [b1]; simp))
        · left
          exact ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨huD, Finset.mem_singleton.not.mpr hu2⟩),
                 Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvD, Finset.mem_singleton.not.mpr hv2⟩)⟩
  rcases h_edge_split with ⟨huF, hvF⟩ | ⟨huC, hvC⟩
  · right
    exact convexHull_mono Set.subset_union_left (convexHull_tri_subset
      (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S huF)))
      (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hvF)))
      (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb3F))) hm)
  · have hb3C : b3 ∈ CapPts := Finset.mem_union_left _ (by simp)
    have hz_cap : S z ∈ convexHull ℝ (CapPts.image S : Set (ℝ × ℝ)) :=
      convexHull_tri_subset
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S huC)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hvC)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb3C))) hm
    have hz_ny : z ≠ y := by
      intro hzy; subst hzy
      have hnn : 0 ≤ orient2D (S b3) (S b1) (S z) :=
        orient2D_const_le_convexHull (fun p hp => by
          rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨g, hg, rfl⟩
          rcases Finset.mem_union.mp hg with hg3 | hgH
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hg3
            rcases hg3 with rfl | rfl | rfl
            · rw [orient2D_self_right]
            · exact le_of_lt ho_b3b1b2
            · rw [orient2D_self_outer]
          · exact le_of_lt (hH_b3b1 g hgH)) hz_cap
      linarith
    have hz_nO : z ∉ O_star := by
      simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hz_nD (h ▸ ccwCycle_mem cyc0 4), hz_ny, fun h => hz_nD (h ▸ ccwCycle_mem cyc0 2)⟩
    have hz_nb1 : z ≠ b1 := fun h => hz_nD (h ▸ ccwCycle_mem cyc0 2)
    have hz_nb3 : z ≠ b3 := fun h => hz_nD (h ▸ ccwCycle_mem cyc0 4)
    have hCap_cross : ∀ g ∈ CapPts, g = b1 ∨ g = b3 ∨ SegmentsCross v (S g) (S b1) (S b3) := by
      intro g hg
      rcases Finset.mem_union.mp hg with hg3 | hgH
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hg3
        rcases hg3 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hcross_b2)
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (hH_cross g hgH))
    obtain ⟨Hp, hHp⟩ := (cap_crossing_of_vertices_cross hPoly h25 hgap_mid CapPts hCap_cross
      hz_nO hz_nb1 hz_nb3 hz_cap).2.1
    left
    exact ⟨Hp, isHalfPlaneTest_mono (witnessSet_mono (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hb1F; exact hb3F]) Subset.rfl) hHp⟩

private lemma pentagon_gapMid_norm_absurd {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y : Fin n} (hyM : y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy_tri : InIntTri (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2}))
      (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y))
    (hBack_b2 : IsBackVertexOf S (hullVertices S) (cyc0.toFun 3)
      (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2})))
    (hgap_mid : GoodAnchorPair P S w {cyc0.toFun 4, y, cyc0.toFun 2} (cyc0.toFun 2) (cyc0.toFun 4))
    (hcross_b2 : SegmentsCross (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2}))
      (S (cyc0.toFun 3)) (S (cyc0.toFun 2)) (S (cyc0.toFun 4)))
    (hhp_b2 : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet {cyc0.toFun 2, cyc0.toFun 4} ∅ w) (S (cyc0.toFun 3)) H_hp)
    (hcap_mid : ∀ z : Fin n, z ≠ cyc0.toFun 2 → z ≠ cyc0.toFun 4 →
      z ∉ ({cyc0.toFun 4, y, cyc0.toFun 2} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({cyc0.toFun 3, cyc0.toFun 2, cyc0.toFun 4} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      SegmentsCross (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2})) (S z) (S (cyc0.toFun 2)) (S (cyc0.toFun 4)) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 2, cyc0.toFun 4} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ {cyc0.toFun 4, y, cyc0.toFun 2})))) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let u0 := cyc0.toFun 0
  let v0 := cyc0.toFun 1
  let b1 := cyc0.toFun 2
  let b2 := cyc0.toFun 3
  let b3 := cyc0.toFun 4
  let O_star : Finset (Fin n) := {b3, y, b1}
  let v := w (Finset.univ \ O_star)
  let Q : Finset (Fin n) := {b2}
  let F : Finset (Fin n) := (D \ Q) ∪ ∅
  have hD3 : 3 ≤ D.card := by change 3 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hD5' : 5 ≤ D.card := by change 5 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hy_nD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
  have hb2D : b2 ∈ D := ccwCycle_mem cyc0 3
  have hb1F : b1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 2,
    Finset.mem_singleton.not.mpr (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3))⟩)
  have hb3F : b3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 4,
    Finset.mem_singleton.not.mpr (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3))⟩)
  have hu0F : u0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 0,
    Finset.mem_singleton.not.mpr (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3))⟩)
  have hv0F : v0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 1,
    Finset.mem_singleton.not.mpr (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 3))⟩)
  have hQ_sub : Q ⊆ D := Finset.singleton_subset_iff.mpr hb2D
  have hQ_card : Q.card = 1 := Finset.card_singleton b2
  have hM0_sub : (∅ : Finset (Fin n)) ⊆ M := Finset.empty_subset M
  have hBack_Q : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B p (w (Finset.univ \ O)) := by
    intro p hp; rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨O_star, ?_, ?_, hBack_b2⟩
    · simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 4), fun h => hy_nD (h ▸ hb2D), cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 2)⟩
    · intro a ha b hb hed
      refine nonadj_D_implies_nonadj_B h25 hD3
        (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2 (fun he => ?_) hed
      rw [isCCWEdge_iff_ccwCycle cyc0] at he
      rcases he with ⟨r, hr1, hr2⟩
      have haO := (Finset.mem_inter.mp ha).1; have hbO := (Finset.mem_inter.mp hb).1
      have haD := (Finset.mem_inter.mp ha).2; have hbD := (Finset.mem_inter.mp hb).2
      simp only [O_star, Finset.mem_insert, Finset.mem_singleton] at haO hbO
      rcases haO with rfl | rfl | rfl <;> rcases hbO with rfl | rfl | rfl
      · exact (by decide : (4 : Fin 5) + 1 ≠ 4) (by
          have h1 : (4 : Fin 5) = r := cyc0.inj hr1; have h2 : (4 : Fin 5) = r + 1 := cyc0.inj hr2
          rw [← h1] at h2; exact h2.symm)
      · exact hy_nD hbD
      · exact (by decide : (4 : Fin 5) + 1 ≠ 2) (by
          have h1 : (4 : Fin 5) = r := cyc0.inj hr1; have h2 : (2 : Fin 5) = r + 1 := cyc0.inj hr2
          rw [← h1] at h2; exact h2.symm)
      · exact hy_nD haD
      · exact hy_nD haD
      · exact hy_nD haD
      · exact (by decide : (2 : Fin 5) + 1 ≠ 4) (by
          have h1 : (2 : Fin 5) = r := cyc0.inj hr1; have h2 : (4 : Fin 5) = r + 1 := cyc0.inj hr2
          rw [← h1] at h2; exact h2.symm)
      · exact hy_nD hbD
      · exact (by decide : (2 : Fin 5) + 1 ≠ 2) (by
          have h1 : (2 : Fin 5) = r := cyc0.inj hr1; have h2 : (2 : Fin 5) = r + 1 := cyc0.inj hr2
          rw [← h1] at h2; exact h2.symm)
  have hQ_hp : ∀ p ∈ Q, ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S p) H_hp := by
    intro p hp; rw [Finset.mem_singleton] at hp; subst hp
    obtain ⟨Hp, hHp⟩ := hhp_b2
    exact ⟨Hp, isHalfPlaneTest_mono (witnessSet_mono (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hb1F; exact hb3F]) Subset.rfl) hHp⟩
  have hH_cov : ∀ h ∈ H \ ∅, ∃ a b : Fin n, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧
      ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h) := by
    intro h hh
    exact h25.side_preservation ⟨h, (Finset.mem_sdiff.mp hh).1⟩ hD5' Q ∅ hQ_sub (by rw [hQ_card]; decide) hM0_sub hBack_Q h hh
  have ho_b3b1b2 : 0 < orient2D (S b3) (S b1) (S b2) := by
    have h := cyc0.ccw_tri 2 3 4 (by decide) (by decide)
    dsimp [b1, b2, b3]; unfold orient2D at h ⊢; linarith
  have ho_b3b1u0 : orient2D (S b3) (S b1) (S u0) < 0 := by
    have h := cyc0.ccw_tri 0 2 4 (by decide) (by decide)
    dsimp [u0, b1, b3]; unfold orient2D at h ⊢; linarith
  have ho_b3b1v0 : orient2D (S b3) (S b1) (S v0) < 0 := by
    have h := cyc0.ccw_tri 1 2 4 (by decide) (by decide)
    dsimp [v0, b1, b3]; unfold orient2D at h ⊢; linarith
  have ho_b3b1v : orient2D (S b3) (S b1) v < 0 := by
    have hsc := hcross_b2.2
    have hsw : orient2D (S b1) (S b3) (S b2) < 0 := by
      unfold orient2D at ho_b3b1b2 ⊢; linarith
    unfold orient2D at hsc hsw ⊢
    nlinarith only [hsc, hsw]
  have ho_b3b1y : orient2D (S b3) (S b1) (S y) < 0 := by
    rcases hy_tri with ⟨μ1, μ2, μ3, h1, h2, h3, hs, hy1, hy2⟩
    have hid := orient2D_convex_comb3 (S b3) (S b1) v (S u0) (S v0) (S y) μ1 μ2 μ3 hs hy1 hy2
    rw [hid]
    nlinarith only [h1, h2, h3, ho_b3b1v, ho_b3b1u0, ho_b3b1v0]
  have hy_nH_of_pos : (∀ h ∈ H, 0 < orient2D (S b3) (S b1) (S h)) → y ∉ H := fun hpos hyH => by
    have h := hpos y hyH; linarith
  have hcomb := combination_lemma_core hPoly h25 hQ_sub (Or.inl hQ_card) hM0_sub hQ_hp hH_cov ?_
  · have hle := hcomb.1 hQ_card
    change M.card ≤ 4 at hle
    change 5 ≤ M.card at hM5
    omega
  · intro z hz
    have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
    have hz_nB : z ∉ B := (Finset.mem_sdiff.mp hzA).2
    have hz_nD : z ∉ D := fun hd => hz_nB (Finset.sdiff_subset hd)
    have hzB : S z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := mem_convexHull_hullVertices S hPoly.s_inj z
    have h_cover_from_D_or_lrH : ∀ l r : Fin n, H.Nonempty → l ∈ D → r ∈ D → l ≠ r →
        l ≠ b2 → r ≠ b2 →
        (∀ d ∈ D, d ≠ l → d ≠ r → ∀ x ∈ B,
          (IsCCWEdge S B x d ↔ IsCCWEdge S D x d) ∧ (IsCCWEdge S B d x ↔ IsCCWEdge S D d x)) →
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) H_hp) ∨
        S z ∈ convexHull ℝ ((F.image S : Set (ℝ × ℝ)) ∪ {w F}) := by
      intro l r hHne hlD hrD hlr hl2 hr2 h_edges
      rcases convexHull_B_subset_convD_union_lrH hPoly h25 hD3 hlD hrD h_edges hzB with hzD | hzH
      · let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc0.toFun i)
        have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
          have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
            dsimp [D, B, H]; conv_rhs => rw [← cyc0.image_eq]
            ext p; simp [pD]
          rwa [hr]
        rcases pentagon_fan_triangulation_from_4 pD cyc0.ccw (S z) hzD' with h401 | h124 | h234
        · right
          exact convexHull_mono Set.subset_union_left (convexHull_tri_subset
            (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb3F)))
            (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hu0F)))
            (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hv0F))) h401)
        · right
          exact convexHull_mono Set.subset_union_left (convexHull_tri_subset
            (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hv0F)))
            (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb1F)))
            (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb3F))) h124)
        · have hz_ny : z ≠ y := by
            intro hzy; subst hzy
            have hnn : 0 ≤ orient2D (S b3) (S b1) (S z) :=
              orient2D_const_le_convexHull (fun x hx => by
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
                rcases hx with rfl | rfl | rfl
                · rw [orient2D_self_right]
                · exact le_of_lt ho_b3b1b2
                · rw [orient2D_self_outer]) h234
            linarith
          have hz_nO : z ∉ O_star := by
            simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hz_nD (h ▸ ccwCycle_mem cyc0 4), hz_ny, fun h => hz_nD (h ▸ ccwCycle_mem cyc0 2)⟩
          have hz_nb1 : z ≠ b1 := fun h => hz_nD (h ▸ ccwCycle_mem cyc0 2)
          have hz_nb3 : z ≠ b3 := fun h => hz_nD (h ▸ ccwCycle_mem cyc0 4)
          have hconv_sub : S z ∈ convexHull ℝ (({b2, b1, b3} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
            refine convexHull_tri_subset
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_insert_self _ _))))
              (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))) h234
          obtain ⟨Hp, hHp⟩ := (hcap_mid z hz_nb1 hz_nb3 hz_nO hconv_sub).2.1
          left
          exact ⟨Hp, isHalfPlaneTest_mono (witnessSet_mono (fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> [exact hb1F; exact hb3F]) Subset.rfl) hHp⟩
      · right
        have hlF : l ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hlD, Finset.mem_singleton.not.mpr hl2⟩)
        have hrF : r ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hrD, Finset.mem_singleton.not.mpr hr2⟩)
        refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _) hzH
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨x, hx, rfl⟩
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hxH
        · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hlF)))
        · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hrF)))
        · obtain ⟨a, b, haF, hbF, _, hin⟩ := hH_cov x (Finset.mem_sdiff.mpr ⟨hxH, Finset.notMem_empty _⟩)
          have hwt := hin (w F) ⟨F, fun t ht => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl <;> assumption, Finset.disjoint_empty_right _, rfl⟩
          exact convexHull_tri_subset
            (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _)))
            (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S haF))))
            (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hbF))))
            hwt.to_convexHull
    by_cases hHne : H.Nonempty
    · obtain ⟨l, r, hlD, hrD, hlr, hed', hH_neg, _, _, h_edges, hH1, hH2⟩ := h25.certified_structure.2 hHne
      have hed := hed' hD3
      by_cases hb2_lr : b2 ≠ l ∧ b2 ≠ r
      · exact h_cover_from_D_or_lrH l r hHne hlD hrD hlr hb2_lr.1.symm hb2_lr.2.symm h_edges
      · push Not at hb2_lr
        have hH_sub_B : H ⊆ B := fun x hx => (Finset.mem_filter.mp hx).1
        have hD_sub_B : D ⊆ B := Finset.sdiff_subset
        have hH_nmem_D : ∀ h ∈ H, ∀ x ∈ D, h ≠ x := fun h hh x hx he => (Finset.mem_sdiff.mp hx).2 (he ▸ hh)
        have hlr_cyc : ∃ i : Fin 5, cyc0.toFun i = l ∧ cyc0.toFun (i + 1) = r := by
          rw [isCCWEdge_iff_ccwCycle cyc0] at hed
          rcases hed with ⟨i, hi1, hi2⟩
          exact ⟨i, hi1.symm, hi2.symm⟩
        rcases hlr_cyc with ⟨il, hil, hir⟩
        have hb2_case : (l = b1 ∧ r = b2) ∨ (l = b2 ∧ r = b3) := by
          by_cases hlb2 : l = b2
          · right
            have hil3 : il = 3 := cyc0.inj (hil.trans hlb2)
            rw [hil3] at hir
            exact ⟨hlb2, hir.symm⟩
          · have hrb2 : r = b2 := (hb2_lr (Ne.symm hlb2)).symm
            left
            have hir3 : il + 1 = 3 := cyc0.inj (hir.trans hrb2)
            have hil2 : il = 2 := by
              have := congrArg (· - 1) hir3; simpa using this
            rw [hil2] at hil
            exact ⟨hil.symm, hrb2⟩
        have h_ccw_b1b2b3 : 0 < orient2D (S b1) (S b2) (S b3) := by
          unfold orient2D at ho_b3b1b2 ⊢; linarith
        have hv_b1b2_b2b3 : 0 < orient2D v (S b1) (S b2) ∧ 0 < orient2D v (S b2) (S b3) := by
          have hsc := hcross_b2.1
          have hsum : orient2D v (S b1) (S b2) + orient2D v (S b2) (S b3) + orient2D v (S b3) (S b1) =
              orient2D (S b1) (S b2) (S b3) := by unfold orient2D; ring
          have hv31 : orient2D v (S b3) (S b1) < 0 := by
            unfold orient2D at ho_b3b1v ⊢; linarith
          have hsame : 0 < orient2D v (S b1) (S b2) * orient2D v (S b2) (S b3) := by
            have heq : orient2D v (S b2) (S b1) = -orient2D v (S b1) (S b2) := by unfold orient2D; ring
            rw [heq] at hsc; linarith
          rcases mul_pos_iff.mp hsame with hpp | ⟨hn1, hn2⟩
          · exact hpp
          · linarith
        have hn3 : 3 ≤ n := by have hle := Finset.card_le_univ D; rw [Fintype.card_fin] at hle; omega
        obtain ⟨kB, _, ⟨cycB⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
        rcases hb2_case with ⟨hl_eq, hr_eq⟩ | ⟨hl_eq, hr_eq⟩
        · subst hl_eq; subst hr_eq
          have hv0b1_B : IsCCWEdge S B v0 b1 :=
            (h_edges v0 (ccwCycle_mem cyc0 1) (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2))
              (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 3)) b1 (hD_sub_B (ccwCycle_mem cyc0 2))).2.mpr
              (by simpa [v0, b1] using ccwCycle_isCCWEdge cyc0 1)
          have hb2b3_B : IsCCWEdge S B b2 b3 :=
            (h_edges b3 (ccwCycle_mem cyc0 4) (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 2))
              (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3)) b2 (hD_sub_B (ccwCycle_mem cyc0 3))).1.mpr
              (by simpa [b2, b3] using ccwCycle_isCCWEdge cyc0 3)
          have hH_b3b1 : ∀ h ∈ H, 0 < orient2D (S b3) (S b1) (S h) := by
            intro h hh
            have hhB := hH_sub_B hh
            have hh_nv0 : h ≠ v0 := hH_nmem_D h hh v0 (ccwCycle_mem cyc0 1)
            have hh_nb1 : h ≠ b1 := hH_nmem_D h hh b1 (ccwCycle_mem cyc0 2)
            have ho1 : 0 < orient2D (S v0) (S b1) (S h) := hv0b1_B.2.2.2 h hhB hh_nv0 hh_nb1
            have ho2 : orient2D (S b1) (S b2) (S h) < 0 := hH_neg h hh
            have ho_v0b1b2 := cyc0.ccw_tri 1 2 3 (by decide) (by decide)
            have ho_v0b1b3 := cyc0.ccw_tri 1 2 4 (by decide) (by decide)
            have hid : orient2D (S v0) (S b1) (S b2) * orient2D (S b3) (S b1) (S h) =
                orient2D (S v0) (S b1) (S b3) * (-orient2D (S b1) (S b2) (S h)) +
                orient2D (S b1) (S b2) (S b3) * orient2D (S v0) (S b1) (S h) := by
              unfold orient2D; ring
            nlinarith
          have hy_nH : y ∉ H := hy_nH_of_pos hH_b3b1
          obtain ⟨h1, hh1, e_b1h1⟩ : ∃ h1 ∈ H, IsCCWEdge S B b1 h1 := by
            by_cases hH1c : H.card = 1
            · obtain ⟨h, hh_eq⟩ := Finset.card_eq_one.mp hH1c
              have hhH : h ∈ H := by
                have hmem : h ∈ ({h} : Finset (Fin n)) := Finset.mem_singleton_self h
                rwa [← hh_eq] at hmem
              exact ⟨h, hhH, (hH1 hH1c h hhH).1⟩
            · obtain ⟨h1, _, hh1, _, _, e1, _⟩ := hH2 (by change 2 ≤ H.card; have := hHne.card_pos; omega)
              exact ⟨h1, hh1, e1⟩
          have hb1_nf : ¬ IsFrontVertexOf S B b1 v := by
            intro hf
            have hh1_nO : h1 ∉ O_star := by
              simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hH_nmem_D h1 hh1 b3 (ccwCycle_mem cyc0 4), fun e => hy_nH (e ▸ hh1),
                     hH_nmem_D h1 hh1 b1 (ccwCycle_mem cyc0 2)⟩
            have hv0_nO : v0 ∉ O_star := by
              simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 4), fun e => hy_nD (e ▸ ccwCycle_mem cyc0 1),
                     cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)⟩
            have hb1_cert : b1 ∈ H := by
              refine Finset.mem_filter.mpr ⟨hD_sub_B (ccwCycle_mem cyc0 2), Finset.univ \ O_star,
                fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))),
                fun b hb => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩,
                fun c hc => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hf⟩
              · rw [isCCWEdge_unique_pred cycB hb hv0b1_B]; exact hv0_nO
              · rw [isCCWEdge_unique_succ cycB hc e_b1h1]; exact hh1_nO
            exact (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 2)).2 hb1_cert
          have hv_b1h1 : 0 < orient2D v (S b1) (S h1) := by
            have hh1_nb1 : h1 ≠ b1 := e_b1h1.2.2.1.symm
            have hne_col : orient2D v (S b1) (S h1) ≠ 0 := hPoly.no_three_collinear _ _ _
              (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
              (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hh1_nb1.symm) (hPoly.s_ne_w _ _).symm
            by_cases hv0_pos : 0 < orient2D (S v0) (S b1) v
            · have ho_v0b1b2 := cyc0.ccw_tri 1 2 3 (by decide) (by decide)
              have ho_v0b1h1 := hv0b1_B.2.2.2 h1 (hH_sub_B hh1)
                (hH_nmem_D h1 hh1 v0 (ccwCycle_mem cyc0 1)) hh1_nb1
              have ho_b1h1b2 : 0 < orient2D (S b1) (S h1) (S b2) := by
                have := hH_neg h1 hh1; unfold orient2D at this ⊢; linarith
              have hid : orient2D (S v0) (S b1) (S b2) * orient2D (S b1) (S h1) v =
                  orient2D (S v0) (S b1) (S h1) * orient2D (S b1) (S b2) v +
                  orient2D (S b1) (S h1) (S b2) * orient2D (S v0) (S b1) v := by
                unfold orient2D; ring
              have hb1b2v : 0 < orient2D (S b1) (S b2) v := by
                have := hv_b1b2_b2b3.1; unfold orient2D at this ⊢; linarith
              have hpos : 0 < orient2D (S b1) (S h1) v := by nlinarith
              unfold orient2D at hpos ⊢; linarith
            · have hv0_neg : orient2D (S v0) (S b1) v < 0 := lt_of_le_of_ne (not_lt.mp hv0_pos)
                (hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
                  (Or.inr (Set.mem_range_self _)) (hPoly.s_inj.ne (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)))
                  (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _))
              have hnot_neg : ¬ orient2D (S b1) (S h1) v < 0 := fun hn => hb1_nf (by
                refine ⟨hD_sub_B (ccwCycle_mem cyc0 2), fun a b hab hor => ?_⟩
                rcases hor with rfl | rfl
                · rw [isCCWEdge_unique_succ cycB hab e_b1h1]; exact hn
                · rw [isCCWEdge_unique_pred cycB hab hv0b1_B]; exact hv0_neg)
              have hpos : 0 < orient2D (S b1) (S h1) v :=
                lt_of_le_of_ne (not_lt.mp hnot_neg) (fun h => hne_col (by unfold orient2D at h ⊢; linarith))
              unfold orient2D at hpos ⊢; linarith
          refine pentagon_gapMid_b1b3_cover hPoly h25 hD5 cyc0 hyM hcross_b2 hgap_mid ho_b3b1b2 ho_b3b1y
            b1 b2 (by dsimp [b1]; simp) (by dsimp [b2]; simp) h_edges hH_b3b1 (fun h hh => ?_) hz_nD hzB
          have hh_b1 : 0 < orient2D v (S b1) (S h) := by
            by_cases hh_eq : h = h1
            · rwa [hh_eq]
            · have hh_nb1 : h ≠ b1 := hH_nmem_D h hh b1 (ccwCycle_mem cyc0 2)
              have ho_b1h1h := e_b1h1.2.2.2 h (hH_sub_B hh) hh_nb1 hh_eq
              have ho_b1h1b2 : 0 < orient2D (S b1) (S h1) (S b2) := by
                have := hH_neg h1 hh1; unfold orient2D at this ⊢; linarith
              have ho_b1hb2 : 0 < orient2D (S b1) (S h) (S b2) := by
                have := hH_neg h hh; unfold orient2D at this ⊢; linarith
              have hb1b2v : 0 < orient2D (S b1) (S b2) v := by
                have := hv_b1b2_b2b3.1; unfold orient2D at this ⊢; linarith
              have hb1h1v : 0 < orient2D (S b1) (S h1) v := by
                unfold orient2D at hv_b1h1 ⊢; linarith
              have hid : orient2D (S b1) (S h1) (S b2) * orient2D (S b1) (S h) v =
                  orient2D (S b1) (S h) (S b2) * orient2D (S b1) (S h1) v +
                  orient2D (S b1) (S h1) (S h) * orient2D (S b1) (S b2) v := by
                unfold orient2D; ring
              have hpos : 0 < orient2D (S b1) (S h) v := by nlinarith
              unfold orient2D at hpos ⊢; linarith
          have hh_b3 : 0 < orient2D v (S h) (S b3) := by
            have ho_b2b3h : 0 < orient2D (S b2) (S b3) (S h) := hb2b3_B.2.2.2 h (hH_sub_B hh)
              (hH_nmem_D h hh b2 (ccwCycle_mem cyc0 3)) (hH_nmem_D h hh b3 (ccwCycle_mem cyc0 4))
            have ho_b3b1h := hH_b3b1 h hh
            have ho_vb1b3 : 0 < orient2D v (S b1) (S b3) := by
              unfold orient2D at ho_b3b1v ⊢; linarith
            have hid : orient2D (S b1) (S b2) (S b3) * orient2D v (S h) (S b3) =
                orient2D (S b2) (S b3) (S h) * orient2D v (S b1) (S b3) +
                orient2D (S b3) (S b1) (S h) * orient2D v (S b2) (S b3) := by
              unfold orient2D; ring
            nlinarith [hv_b1b2_b2b3.2]
          refine ⟨?_, ?_⟩
          · have : orient2D v (S h) (S b1) < 0 := by unfold orient2D at hh_b1 ⊢; linarith
            exact mul_neg_of_neg_of_pos this hh_b3
          · have ho_b1b3v : 0 < orient2D (S b1) (S b3) v := by unfold orient2D at ho_b3b1v ⊢; linarith
            have ho_b1b3h : orient2D (S b1) (S b3) (S h) < 0 := by
              have := hH_b3b1 h hh; unfold orient2D at this ⊢; linarith
            exact mul_neg_of_pos_of_neg ho_b1b3v ho_b1b3h
        · subst hl_eq; subst hr_eq
          have hb1b2_B : IsCCWEdge S B b1 b2 :=
            (h_edges b1 (ccwCycle_mem cyc0 2) (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3))
              (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 4)) b2 (hD_sub_B (ccwCycle_mem cyc0 3))).2.mpr
              (ccwCycle_isCCWEdge cyc0 2)
          have hb3u0_B : IsCCWEdge S B b3 u0 :=
            (h_edges u0 (ccwCycle_mem cyc0 0) (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3))
              (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4)) b3 (hD_sub_B (ccwCycle_mem cyc0 4))).1.mpr
              (ccwCycle_isCCWEdge cyc0 4)
          have hH_b3b1 : ∀ h ∈ H, 0 < orient2D (S b3) (S b1) (S h) := by
            intro h hh
            have hhB := hH_sub_B hh
            have hh_nb3 : h ≠ b3 := hH_nmem_D h hh b3 (ccwCycle_mem cyc0 4)
            have hh_nu0 : h ≠ u0 := hH_nmem_D h hh u0 (ccwCycle_mem cyc0 0)
            have ho1 : 0 < orient2D (S b3) (S u0) (S h) := hb3u0_B.2.2.2 h hhB hh_nb3 hh_nu0
            have ho2 : orient2D (S b2) (S b3) (S h) < 0 := hH_neg h hh
            have ho_b2b3u0 : 0 < orient2D (S b2) (S b3) (S u0) := by
              have := cyc0.ccw_tri 0 3 4 (by decide) (by decide); unfold orient2D at this ⊢; linarith
            have ho_b1b3u0 : 0 < orient2D (S b1) (S b3) (S u0) := by
              have := cyc0.ccw_tri 0 2 4 (by decide) (by decide); unfold orient2D at this ⊢; linarith
            have hid : orient2D (S b2) (S b3) (S u0) * orient2D (S b3) (S b1) (S h) =
                orient2D (S b1) (S b3) (S u0) * (-orient2D (S b2) (S b3) (S h)) +
                orient2D (S b1) (S b2) (S b3) * orient2D (S b3) (S u0) (S h) := by
              unfold orient2D; ring
            nlinarith
          have hy_nH : y ∉ H := hy_nH_of_pos hH_b3b1
          obtain ⟨ib3, hib3⟩ := ccwCycle_exists_index cycB (hD_sub_B (ccwCycle_mem cyc0 4))
          let h_last := cycB.toFun (ib3 - 1)
          have e_hlb3 : IsCCWEdge S B h_last b3 := by
            have e := ccwCycle_isCCWEdge cycB (ib3 - 1)
            rwa [sub_add_cancel, hib3] at e
          have hhlH : h_last ∈ H := by
            by_contra hnh
            have hhlD : h_last ∈ D := Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycB (ib3 - 1), hnh⟩
            by_cases hhl2 : h_last = b2
            · rw [hhl2] at e_hlb3
              obtain ⟨h0, hh0⟩ := hHne
              have ho_n := hH_neg h0 hh0
              have ho_p := e_hlb3.2.2.2 h0 (hH_sub_B hh0)
                (hH_nmem_D h0 hh0 b2 (ccwCycle_mem cyc0 3))
                (hH_nmem_D h0 hh0 b3 (ccwCycle_mem cyc0 4))
              linarith
            · have h_n3 : h_last ≠ b3 := e_hlb3.2.2.1
              have hed_D := (h_edges h_last hhlD hhl2 h_n3 b3 (hD_sub_B (ccwCycle_mem cyc0 4))).2.mp e_hlb3
              have : h_last = b2 := isCCWEdge_unique_pred cyc0 hed_D (ccwCycle_isCCWEdge cyc0 3)
              exact hhl2 this
          have hb3_nf : ¬ IsFrontVertexOf S B b3 v := by
            intro hf
            have hhl_nO : h_last ∉ O_star := by
              simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hH_nmem_D h_last hhlH b3 (ccwCycle_mem cyc0 4), fun e => hy_nH (e ▸ hhlH),
                     hH_nmem_D h_last hhlH b1 (ccwCycle_mem cyc0 2)⟩
            have hu0_nO : u0 ∉ O_star := by
              simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4), fun e => hy_nD (e ▸ ccwCycle_mem cyc0 0),
                     cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2)⟩
            have hb3_cert : b3 ∈ H := by
              refine Finset.mem_filter.mpr ⟨hD_sub_B (ccwCycle_mem cyc0 4), Finset.univ \ O_star,
                fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_self _ _),
                fun b hb => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩,
                fun c hc => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hf⟩
              · rw [isCCWEdge_unique_pred cycB hb e_hlb3]; exact hhl_nO
              · rw [isCCWEdge_unique_succ cycB hc hb3u0_B]; exact hu0_nO
            exact (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 4)).2 hb3_cert
          have hv_hlb3 : 0 < orient2D v (S h_last) (S b3) := by
            have hne_col : orient2D v (S h_last) (S b3) ≠ 0 := hPoly.no_three_collinear _ _ _
              (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
              (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne e_hlb3.2.2.1) (hPoly.s_ne_w _ _).symm
            by_cases hu0_pos : 0 < orient2D (S b3) (S u0) v
            · have ho_b2b3u0 : 0 < orient2D (S b2) (S b3) (S u0) := by
                have := cyc0.ccw_tri 0 3 4 (by decide) (by decide); unfold orient2D at this ⊢; linarith
              have ho_b2hlb3 : 0 < orient2D (S b2) (S h_last) (S b3) := by
                have := hH_neg h_last hhlH; unfold orient2D at this ⊢; linarith
              have ho_hlb3u0 : 0 < orient2D (S h_last) (S b3) (S u0) := by
                have ho := hb3u0_B.2.2.2 h_last (hH_sub_B hhlH)
                  (hH_nmem_D h_last hhlH b3 (ccwCycle_mem cyc0 4))
                  (hH_nmem_D h_last hhlH u0 (ccwCycle_mem cyc0 0))
                unfold orient2D at ho ⊢; linarith
              have hb2b3v : 0 < orient2D (S b2) (S b3) v := by
                have := hv_b1b2_b2b3.2; unfold orient2D at this ⊢; linarith
              have hid : orient2D (S b2) (S b3) (S u0) * orient2D (S h_last) (S b3) v =
                  orient2D (S h_last) (S b3) (S u0) * orient2D (S b2) (S b3) v +
                  orient2D (S b2) (S h_last) (S b3) * orient2D (S b3) (S u0) v := by
                unfold orient2D; ring
              have hpos : 0 < orient2D (S h_last) (S b3) v := by nlinarith
              unfold orient2D at hpos ⊢; linarith
            · have hu0_neg : orient2D (S b3) (S u0) v < 0 := lt_of_le_of_ne (not_lt.mp hu0_pos)
                (hPoly.no_three_collinear _ _ _ (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
                  (Or.inr (Set.mem_range_self _)) (hPoly.s_inj.ne (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 0)))
                  (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _))
              have hnot_neg : ¬ orient2D (S h_last) (S b3) v < 0 := fun hn => hb3_nf (by
                refine ⟨hD_sub_B (ccwCycle_mem cyc0 4), fun a b hab hor => ?_⟩
                rcases hor with rfl | rfl
                · rw [isCCWEdge_unique_succ cycB hab hb3u0_B]; exact hu0_neg
                · rw [isCCWEdge_unique_pred cycB hab e_hlb3]; exact hn)
              have hpos : 0 < orient2D (S h_last) (S b3) v :=
                lt_of_le_of_ne (not_lt.mp hnot_neg) (fun h => hne_col (by unfold orient2D at h ⊢; linarith))
              unfold orient2D at hpos ⊢; linarith
          refine pentagon_gapMid_b1b3_cover hPoly h25 hD5 cyc0 hyM hcross_b2 hgap_mid ho_b3b1b2 ho_b3b1y
            b2 b3 (by dsimp [b2]; simp) (by dsimp [b3]; simp) h_edges hH_b3b1 (fun h hh => ?_) hz_nD hzB
          have hh_b3 : 0 < orient2D v (S h) (S b3) := by
            by_cases hh_eq : h = h_last
            · rwa [hh_eq]
            · have hh_nb3 : h ≠ b3 := hH_nmem_D h hh b3 (ccwCycle_mem cyc0 4)
              have ho_hhlb3 : 0 < orient2D (S h) (S h_last) (S b3) := by
                have ho := e_hlb3.2.2.2 h (hH_sub_B hh) hh_eq hh_nb3
                unfold orient2D at ho ⊢; linarith
              have ho_b2hlb3 : 0 < orient2D (S b2) (S h_last) (S b3) := by
                have := hH_neg h_last hhlH; unfold orient2D at this ⊢; linarith
              have ho_b2hb3 : 0 < orient2D (S b2) (S h) (S b3) := by
                have := hH_neg h hh; unfold orient2D at this ⊢; linarith
              have hb2b3v : 0 < orient2D (S b2) (S b3) v := by
                have := hv_b1b2_b2b3.2; unfold orient2D at this ⊢; linarith
              have hhlb3v : 0 < orient2D (S h_last) (S b3) v := by
                unfold orient2D at hv_hlb3 ⊢; linarith
              have hid : orient2D (S b2) (S h_last) (S b3) * orient2D (S h) (S b3) v =
                  orient2D (S b2) (S h) (S b3) * orient2D (S h_last) (S b3) v +
                  orient2D (S h) (S h_last) (S b3) * orient2D (S b2) (S b3) v := by
                unfold orient2D; ring
              have hpos : 0 < orient2D (S h) (S b3) v := by nlinarith
              unfold orient2D at hpos ⊢; linarith
          have hh_b1 : 0 < orient2D v (S b1) (S h) := by
            have ho_b1b2h : 0 < orient2D (S b1) (S b2) (S h) := hb1b2_B.2.2.2 h (hH_sub_B hh)
              (hH_nmem_D h hh b1 (ccwCycle_mem cyc0 2)) (hH_nmem_D h hh b2 (ccwCycle_mem cyc0 3))
            have ho_b3b1h := hH_b3b1 h hh
            have ho_vb1b3 : 0 < orient2D v (S b1) (S b3) := by
              unfold orient2D at ho_b3b1v ⊢; linarith
            have hid : orient2D (S b1) (S b2) (S b3) * orient2D v (S b1) (S h) =
                orient2D (S b1) (S b2) (S h) * orient2D v (S b1) (S b3) +
                orient2D (S b3) (S b1) (S h) * orient2D v (S b1) (S b2) := by
              unfold orient2D; ring
            nlinarith [hv_b1b2_b2b3.1]
          refine ⟨?_, ?_⟩
          · have : orient2D v (S h) (S b1) < 0 := by unfold orient2D at hh_b1 ⊢; linarith
            exact mul_neg_of_neg_of_pos this hh_b3
          · have ho_b1b3v : 0 < orient2D (S b1) (S b3) v := by unfold orient2D at ho_b3b1v ⊢; linarith
            have ho_b1b3h : orient2D (S b1) (S b3) (S h) < 0 := by
              have := hH_b3b1 h hh; unfold orient2D at this ⊢; linarith
            exact mul_neg_of_pos_of_neg ho_b1b3v ho_b1b3h
    · have hH_emp : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      have hBD : B = D := by dsimp [D]; rw [hH_emp, Finset.sdiff_empty]
      rw [hBD] at hzB
      let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc0.toFun i)
      have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
        have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
          dsimp [D, B, H]; conv_rhs => rw [← cyc0.image_eq]
          ext p; simp [pD]
        rwa [hr]
      rcases pentagon_fan_triangulation_from_4 pD cyc0.ccw (S z) hzD' with h401 | h124 | h234
      · right
        exact convexHull_mono Set.subset_union_left (convexHull_tri_subset
          (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb3F)))
          (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hu0F)))
          (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hv0F))) h401)
      · right
        exact convexHull_mono Set.subset_union_left (convexHull_tri_subset
          (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hv0F)))
          (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb1F)))
          (subset_convexHull ℝ (F.image S : Set (ℝ × ℝ)) (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hb3F))) h124)
      · have hz_ny : z ≠ y := by
          intro hzy; subst hzy
          have hnn : 0 ≤ orient2D (S b3) (S b1) (S z) :=
            orient2D_const_le_convexHull (fun x hx => by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
              rcases hx with rfl | rfl | rfl
              · rw [orient2D_self_right]
              · exact le_of_lt ho_b3b1b2
              · rw [orient2D_self_outer]) h234
          linarith
        have hz_nO : z ∉ O_star := by
          simp only [O_star, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hz_nD (h ▸ ccwCycle_mem cyc0 4), hz_ny, fun h => hz_nD (h ▸ ccwCycle_mem cyc0 2)⟩
        have hz_nb1 : z ≠ b1 := fun h => hz_nD (h ▸ ccwCycle_mem cyc0 2)
        have hz_nb3 : z ≠ b3 := fun h => hz_nD (h ▸ ccwCycle_mem cyc0 4)
        have hconv_sub : S z ∈ convexHull ℝ (({b2, b1, b3} : Finset (Fin n)).image S : Set (ℝ × ℝ)) :=
          convexHull_tri_subset
            (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
            (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_insert_self _ _))))
            (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))) h234
        obtain ⟨Hp, hHp⟩ := (hcap_mid z hz_nb1 hz_nb3 hz_nO hconv_sub).2.1
        left
        exact ⟨Hp, isHalfPlaneTest_mono (witnessSet_mono (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> [exact hb1F; exact hb3F]) Subset.rfl) hHp⟩

/-- Pentagon version of Proposition 6.6 (`interior_anchor`, `upper_9.tex` lines 965–966):
    When `|D| = 5` and `|M| = 5`, `O*(y) = {b3, y, b1}` (`b3 = iu0 - 1, b1 = iu0 + 2`) cannot
    select `gapMid = {b2}`, so it strictly selects either `u0 = cycD iu0` (anchors `{b3, y}`)
    or `v0 = cycD (iu0 + 1)` (anchors `{y, b1}`). -/
theorem pentagon_interior_anchor_2 {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y : Fin n} (hyM : y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (iu0 : Fin 5)
    (h_exit_v :
      0 < orient2D (S (cycD.toFun iu0)) (S (cycD.toFun (iu0 + 1))) (w (hullVertices S \ certifiedVertices S w)) ∧
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun iu0)) (S (cycD.toFun (iu0 + 1))) (S y) ∧
      (∀ x ∈ WitnessSet {cycD.toFun iu0, cycD.toFun (iu0 + 1)} ∅ w,
        InIntTri x (S (cycD.toFun iu0)) (S (cycD.toFun (iu0 + 1))) (S y)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun iu0, cycD.toFun (iu0 + 1)) ≠ (l, r))) :
    let b3 := cycD.toFun (iu0 - 1)
    let u0 := cycD.toFun iu0
    let v0 := cycD.toFun (iu0 + 1)
    let b1 := cycD.toFun (iu0 + 2)
    let O_star : Finset (Fin n) := {b3, y, b1}
    let v := w (Finset.univ \ O_star)
    (InIntTri v (S u0) (S v0) (S y) ∧
      ¬ IsFrontVertexOf S (hullVertices S \ certifiedVertices S w) b3 v ∧
      ¬ IsFrontVertexOf S (hullVertices S \ certifiedVertices S w) u0 v ∧
      ¬ IsFrontVertexOf S (hullVertices S \ certifiedVertices S w) v0 v ∧
      ¬ IsFrontVertexOf S (hullVertices S \ certifiedVertices S w) b1 v) ∧
    ∃ (oa ob : Fin n) (Γ : Finset (Fin n)),
      ((oa = b3 ∧ ob = y ∧ Γ = {u0}) ∨ (oa = y ∧ ob = b1 ∧ Γ = {v0})) ∧
      GoodAnchorPair P S w O_star oa ob ∧
      (∀ p ∈ Γ,
        IsBackVertexOf S (hullVertices S) p v ∧
        SegmentsCross v (S p) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S p) H_hp)) ∧
      (∀ z : Fin n, z ≠ oa → z ≠ ob → z ∉ O_star →
        S z ∈ convexHull ℝ ((Γ ∪ {oa, ob}).image S : Set (ℝ × ℝ)) →
        SegmentsCross v (S z) (S oa) (S ob) ∧
        (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {oa, ob} ∅ w) (S z) H_hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v)) := by
  intro b3 u0 v0 b1 O_star v
  have ho1 : (0 : ℕ) < (iu0 - (iu0 - 1)).val := by
    have : iu0 - (iu0 - 1) = (1 : Fin 5) := by abel
    rw [this]; decide
  have ho2 : (iu0 - (iu0 - 1)).val < ((iu0 + 1) - (iu0 - 1)).val := by
    have h1 : iu0 - (iu0 - 1) = (1 : Fin 5) := by abel
    have h2 : (iu0 + 1) - (iu0 - 1) = (2 : Fin 5) := by abel
    rw [h1, h2]; decide
  have ho3 : ((iu0 + 1) - (iu0 - 1)).val < ((iu0 + 2) - (iu0 - 1)).val := by
    have h1 : (iu0 + 1) - (iu0 - 1) = (2 : Fin 5) := by abel
    have h2 : (iu0 + 2) - (iu0 - 1) = (3 : Fin 5) := by abel
    rw [h1, h2]; decide
  have ho4 : ((iu0 + 2) - (iu0 - 1)).val < ((iu0 + 3) - (iu0 - 1)).val := by
    have h1 : (iu0 + 2) - (iu0 - 1) = (3 : Fin 5) := by abel
    have h2 : (iu0 + 3) - (iu0 - 1) = (4 : Fin 5) := by abel
    rw [h1, h2]; decide
  obtain ⟨hpart1, oa, ob, Γ, hcases, hgap, hΓ, hz_cap⟩ :=
    interior_anchor hPoly h25 rfl cycD hyM (iu0 - 1) iu0 (iu0 + 1) (iu0 + 2) (iu0 + 3) rfl
      ho1 ho2 ho3 ho4 h_exit_v
  have hgapL_eq : (hullVertices S \ certifiedVertices S w).filter (fun p => ∃ m : Fin 5, cycD.toFun m = p ∧
      0 < (m - (iu0 - 1)).val ∧ (m - (iu0 - 1)).val ≤ (iu0 - (iu0 - 1)).val) = {u0} := by
    ext p; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, m, rfl, hm1, hm2⟩
      have h1 : (iu0 - (iu0 - 1) : Fin 5).val = 1 := by
        have : (iu0 - (iu0 - 1) : Fin 5) = 1 := by abel
        rw [this]; decide
      rw [h1] at hm2
      have hval : (m - (iu0 - 1)).val = 1 := by omega
      have hme : m - (iu0 - 1) = 1 := Fin.ext hval
      have hm_eq : m = iu0 := by
        calc m = (m - (iu0 - 1)) + (iu0 - 1) := by abel
          _ = 1 + (iu0 - 1) := by rw [hme]
          _ = iu0 := by abel
      rw [hm_eq]
    · rintro rfl
      exact ⟨ccwCycle_mem cycD iu0, iu0, rfl, ho1, le_rfl⟩
  have hgapR_eq : (hullVertices S \ certifiedVertices S w).filter (fun p => ∃ m : Fin 5, cycD.toFun m = p ∧
      ((iu0 + 1) - (iu0 - 1)).val ≤ (m - (iu0 - 1)).val ∧ (m - (iu0 - 1)).val < ((iu0 + 2) - (iu0 - 1)).val) = {v0} := by
    ext p; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, m, rfl, hm1, hm2⟩
      have h2 : ((iu0 + 1) - (iu0 - 1) : Fin 5).val = 2 := by
        have : (iu0 + 1) - (iu0 - 1) = (2 : Fin 5) := by abel
        rw [this]; decide
      have h3 : ((iu0 + 2) - (iu0 - 1) : Fin 5).val = 3 := by
        have : (iu0 + 2) - (iu0 - 1) = (3 : Fin 5) := by abel
        rw [this]; decide
      rw [h2] at hm1; rw [h3] at hm2
      have hme : m - (iu0 - 1) = 2 := Fin.ext (by omega)
      have hm_eq : m = iu0 + 1 := by
        calc m = (m - (iu0 - 1)) + (iu0 - 1) := by abel
          _ = 2 + (iu0 - 1) := by rw [hme]
          _ = iu0 + 1 := by have : (2 : Fin 5) = 1 + 1 := rfl; rw [this]; abel
      rw [hm_eq]
    · rintro rfl
      exact ⟨ccwCycle_mem cycD (iu0 + 1), iu0 + 1, rfl, le_rfl, ho3⟩
  have hgapMid_eq : (hullVertices S \ certifiedVertices S w).filter (fun p => ∃ m : Fin 5, cycD.toFun m = p ∧
      0 < (m - (iu0 + 2)).val ∧ (m - (iu0 + 2)).val < ((iu0 - 1) - (iu0 + 2)).val) = {cycD.toFun (iu0 + 3)} := by
    ext p; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, m, rfl, hm1, hm2⟩
      have h2 : ((iu0 - 1) - (iu0 + 2) : Fin 5).val = 2 := by
        have : (iu0 - 1) - (iu0 + 2) = (2 : Fin 5) := by
          calc (iu0 - 1) - (iu0 + 2) = (-3 : Fin 5) := by abel
            _ = 2 := by decide
        rw [this]; decide
      rw [h2] at hm2
      have hme : m - (iu0 + 2) = 1 := Fin.ext (by omega)
      have hm_eq : m = iu0 + 3 := by
        calc m = (m - (iu0 + 2)) + (iu0 + 2) := by abel
          _ = 1 + (iu0 + 2) := by rw [hme]
          _ = iu0 + 3 := by have : (3 : Fin 5) = 1 + 2 := rfl; rw [this]; abel
      rw [hm_eq]
    · rintro rfl
      refine ⟨ccwCycle_mem cycD (iu0 + 3), iu0 + 3, rfl, ?_, ?_⟩
      · have : (iu0 + 3) - (iu0 + 2) = (1 : Fin 5) := by abel
        rw [this]; decide
      · have h1 : (iu0 + 3) - (iu0 + 2) = (1 : Fin 5) := by abel
        have h2 : (iu0 - 1) - (iu0 + 2) = (2 : Fin 5) := by
          calc (iu0 - 1) - (iu0 + 2) = (-3 : Fin 5) := by abel
            _ = 2 := by decide
        rw [h1, h2]; decide
  rcases hcases with ⟨hoa, hob, hΓeq⟩ | ⟨hoa, hob, hΓeq⟩ | ⟨hoa, hob, hΓeq⟩
  · rw [hoa, hob] at hgap
    rw [hoa, hob, hΓeq, hgapL_eq] at hΓ hz_cap
    exact ⟨hpart1, b3, y, {u0}, Or.inl ⟨rfl, rfl, rfl⟩, hgap, hΓ, hz_cap⟩
  · rw [hoa, hob] at hgap
    rw [hoa, hob, hΓeq, hgapR_eq] at hΓ hz_cap
    exact ⟨hpart1, y, b1, {v0}, Or.inr ⟨rfl, rfl, rfl⟩, hgap, hΓ, hz_cap⟩
  · rw [hoa, hob] at hgap
    rw [hoa, hob, hΓeq, hgapMid_eq] at hΓ hz_cap
    exfalso
    let cyc0 := ccwCycle_shift cycD iu0
    have h0_eq : cyc0.toFun 0 = u0 := by dsimp [cyc0, ccwCycle_shift, u0]; simp
    have h1_eq : cyc0.toFun 1 = v0 := rfl
    have h2_eq : cyc0.toFun 2 = b1 := rfl
    have h3_eq : cyc0.toFun 3 = cycD.toFun (iu0 + 3) := rfl
    have h4_eq : cyc0.toFun 4 = b3 := by
      dsimp [cyc0, ccwCycle_shift, b3]; congr 1
      calc iu0 + 4 = iu0 + (-1 : Fin 5) := rfl
        _ = iu0 - 1 := by abel
    have h_b2 := hΓ (cycD.toFun (iu0 + 3)) (Finset.mem_singleton_self _)
    refine pentagon_gapMid_norm_absurd hPoly h25 hD5 hM5 cyc0 hyM
      (by simpa [h0_eq, h1_eq, h2_eq, h4_eq] using hpart1.1)
      (by simpa [h3_eq, h4_eq, h2_eq] using h_b2.1)
      (by simpa [h2_eq, h4_eq] using hgap)
      (by simpa [h3_eq, h2_eq, h4_eq] using h_b2.2.1)
      (by simpa [h3_eq, h2_eq, h4_eq] using h_b2.2.2)
      (fun z hz2 hz4 hzO hzconv => by
        rw [h2_eq] at hz2; rw [h4_eq] at hz4 hzO; rw [h2_eq] at hzO
        rw [h3_eq, h2_eq, h4_eq] at hzconv
        simpa [h2_eq, h4_eq] using hz_cap z hz2 hz4 hzO hzconv)

private lemma certified_edge_unique_of_neg {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hHne : (certifiedVertices S w).Nonempty)
    (hD3 : 3 ≤ (hullVertices S \ certifiedVertices S w).card)
    {l r l0 r0 : Fin n}
    (hlr : IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r)
    (hlr_neg : ∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0)
    (hl0r0 : IsCCWEdge S (hullVertices S \ certifiedVertices S w) l0 r0)
    (hl0D : l0 ∈ hullVertices S \ certifiedVertices S w)
    (hr0D : r0 ∈ hullVertices S \ certifiedVertices S w)
    (hl0r0_ne : l0 ≠ r0)
    (h_edges : ∀ d ∈ hullVertices S \ certifiedVertices S w, d ≠ l0 → d ≠ r0 →
      ∀ x ∈ hullVertices S,
        (IsCCWEdge S (hullVertices S) x d ↔ IsCCWEdge S (hullVertices S \ certifiedVertices S w) x d) ∧
        (IsCCWEdge S (hullVertices S) d x ↔ IsCCWEdge S (hullVertices S \ certifiedVertices S w) d x)) :
    l = l0 ∧ r = r0 := by
  let H := certifiedVertices S w
  let B := hullVertices S
  let D := B \ H
  have hD_B : D ⊆ B := Finset.sdiff_subset
  obtain ⟨h0, hh0⟩ := hHne
  have hh0_nD : h0 ∉ D := fun hd => (Finset.mem_sdiff.mp hd).2 hh0
  have hh0_B : h0 ∈ B := (Finset.mem_filter.mp hh0).1
  have hD3 : 3 ≤ D.card := by change 3 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  by_cases hll0 : l = l0
  · refine ⟨hll0, ?_⟩
    by_contra hrr0
    have h1 : 0 < orient2D (S l0) (S r) (S r0) :=
      hll0 ▸ hlr.2.2.2 r0 hr0D (fun e => hl0r0_ne (hll0.symm.trans e.symm)) (Ne.symm hrr0)
    have h2 : 0 < orient2D (S l0) (S r0) (S r) :=
      hl0r0.2.2.2 r hlr.2.1 (fun e => hlr.2.2.1 (hll0.trans e.symm)) hrr0
    unfold orient2D at h1 h2; linarith
  · by_cases hlr0 : l = r0
    · have hrl0 : r ≠ l0 := by
        intro h
        obtain ⟨d, hdD, hdl0, hdr0⟩ : ∃ d ∈ D, d ≠ l0 ∧ d ≠ r0 := by
          have hc : 2 < D.card := by omega
          have hsub : (D \ {l0, r0}).Nonempty := by
            by_contra he
            rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
            have := Finset.card_le_card he
            have hc2 : ({l0, r0} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
            omega
          obtain ⟨d, hd⟩ := hsub
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hd
          exact ⟨d, hd.1, hd.2.1, hd.2.2⟩
        have h1 := hlr.2.2.2 d hdD (by rw [hlr0]; exact hdr0) (by rw [h]; exact hdl0)
        have h2 := hl0r0.2.2.2 d hdD hdl0 hdr0
        rw [hlr0, h] at h1
        unfold orient2D at h1 h2; linarith
      have hB_lr : IsCCWEdge S B l r :=
        (h_edges r hlr.2.1 hrl0 (by rw [← hlr0]; exact hlr.2.2.1.symm) l (hD_B hlr.1)).1.mpr hlr
      have hpos := orient2D_pos_of_isCCWEdge_B hPoly hB_lr (z := h0)
        (fun e => hh0_nD (e ▸ hlr.1)) (fun e => hh0_nD (e ▸ hlr.2.1))
      linarith [hlr_neg h0 hh0]
    · have hB_lr : IsCCWEdge S B l r :=
        (h_edges l hlr.1 hll0 hlr0 r (hD_B hlr.2.1)).2.mpr hlr
      have hpos := orient2D_pos_of_isCCWEdge_B hPoly hB_lr (z := h0)
        (fun e => hh0_nD (e ▸ hlr.1)) (fun e => hh0_nD (e ▸ hlr.2.1))
      linarith [hlr_neg h0 hh0]

private lemma pentagon_Ostar_nadj {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y : Fin n} (hy_notD : y ∉ hullVertices S \ certifiedVertices S w)
    (ib1 ib2 : Fin 5) (hn1 : ib2 ≠ ib1 + 1) (hn2 : ib1 ≠ ib2 + 1) :
    ∀ a ∈ ({cycD.toFun ib1, y, cycD.toFun ib2} : Finset (Fin n)) ∩ (hullVertices S \ certifiedVertices S w),
    ∀ b ∈ ({cycD.toFun ib1, y, cycD.toFun ib2} : Finset (Fin n)) ∩ (hullVertices S \ certifiedVertices S w),
    ¬ IsCCWEdge S (hullVertices S) a b := by
  intro a ha b hb hed
  have haD := (Finset.mem_inter.mp ha).2
  have hbD := (Finset.mem_inter.mp hb).2
  have ha_or : a = cycD.toFun ib1 ∨ a = cycD.toFun ib2 := by
    rcases (by simpa using (Finset.mem_inter.mp ha).1 : a = cycD.toFun ib1 ∨ a = y ∨ a = cycD.toFun ib2) with
      rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (hy_notD haD)
    · exact Or.inr rfl
  have hb_or : b = cycD.toFun ib1 ∨ b = cycD.toFun ib2 := by
    rcases (by simpa using (Finset.mem_inter.mp hb).1 : b = cycD.toFun ib1 ∨ b = y ∨ b = cycD.toFun ib2) with
      rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (hy_notD hbD)
    · exact Or.inr rfl
  refine nonadj_D_implies_nonadj_B h25 (by rw [hD5]; decide) haD hbD (fun he => ?_) hed
  rw [isCCWEdge_iff_ccwCycle cycD] at he
  rcases he with ⟨r, hr1, hr2⟩
  rcases ha_or with rfl | rfl <;> rcases hb_or with rfl | rfl
  · exact (by decide : ∀ x : Fin 5, x ≠ x + 1) _ (cycD.inj (hr1.symm.trans hr2))
  · have h1 := cycD.inj hr1.symm; have h2 := cycD.inj hr2.symm; exact hn1 (h2.symm.trans (by rw [h1]))
  · have h1 := cycD.inj hr1.symm; have h2 := cycD.inj hr2.symm; exact hn2 (h2.symm.trans (by rw [h1]))
  · exact (by decide : ∀ x : Fin 5, x ≠ x + 1) _ (cycD.inj (hr1.symm.trans hr2))

private lemma pentagon_Q2_M02_absurd {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (Q : Finset (Fin n)) (hQ_sub : Q ⊆ hullVertices S \ certifiedVertices S w) (hQ_card : Q.card = 2)
    (y0 y1 : Fin n) (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w)) (hy01 : y0 ≠ y1)
    (hBack_Q : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)))
    (hQ_hp : ∀ p ∈ Q, ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet (((hullVertices S \ certifiedVertices S w) \ Q) ∪ {y0, y1}) ∅ w) (S p) H_hp)
    (hQ_H_disj : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q)
    (h_convD_cov : ∀ z ∈ interiorPoints S \ {y0, y1},
      S z ∈ convexHull ℝ (((hullVertices S \ certifiedVertices S w).image S) : Set (ℝ × ℝ)) →
      (∃ H_hp : OpenHalfPlane,
        IsHalfPlaneTest P (WitnessSet (((hullVertices S \ certifiedVertices S w) \ Q) ∪ {y0, y1}) ∅ w) (S z) H_hp) ∨
      S z ∈ convexHull ℝ (((((hullVertices S \ certifiedVertices S w) \ Q) ∪ {y0, y1}).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let M0 : Finset (Fin n) := {y0, y1}
  let F : Finset (Fin n) := (D \ Q) ∪ M0
  have hM0_sub : M0 ⊆ M := fun x hx => by
    simp only [M0, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hM0_card : M0.card = 2 := Finset.card_pair hy01
  have hM'_card : 3 ≤ (M \ M0).card := by
    have := Finset.card_sdiff_add_card_inter M M0
    have hi : M ∩ M0 = M0 := Finset.inter_eq_right.mpr hM0_sub
    rw [hi, hM0_card] at this
    change 5 ≤ M.card at hM5
    omega
  have hD3 : 3 ≤ D.card := by change 3 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hD5' : 5 ≤ D.card := by change 5 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hH_cov : ∀ h ∈ H \ M0, ∃ a b : Fin n, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧
      ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h) := by
    intro h hh
    exact h25.side_preservation ⟨h, (Finset.mem_sdiff.mp hh).1⟩ hD5' Q M0
      hQ_sub (by omega) hM0_sub hBack_Q h hh
  have hcomb := combination_lemma_core hPoly h25 hQ_sub (Or.inr hQ_card) hM0_sub hQ_hp hH_cov (fun z hz => by
    have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
    have hzB : S z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := mem_convexHull_hullVertices S hPoly.s_inj z
    by_cases hHne : H.Nonempty
    · obtain ⟨l, r, hlD, hrD, hlr, hed', hH_neg, _, _, h_edges, _, _⟩ := h25.certified_structure.2 hHne
      have hed := hed' hD3
      obtain ⟨hlQ, hrQ⟩ := hQ_H_disj l r hHne hed hH_neg
      have hlF : l ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hlD, hlQ⟩)
      have hrF : r ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hrD, hrQ⟩)
      rcases convexHull_B_subset_convD_union_lrH hPoly h25 hD3 hlD hrD h_edges hzB with hzD | hzH
      · rcases h_convD_cov z hz hzD with hhp | hconv
        · exact Or.inl hhp
        · exact Or.inr (convexHull_mono Set.subset_union_left hconv)
      · right
        refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _) hzH
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨x, hx, rfl⟩
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hxH
        · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hlF)))
        · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hrF)))
        · by_cases hxM0 : x ∈ M0
          · exact subset_convexHull ℝ _ (Set.mem_union_left _
              (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (Finset.mem_union_right _ hxM0))))
          · obtain ⟨a, b, haF, hbF, _, hin⟩ := hH_cov x (Finset.mem_sdiff.mpr ⟨hxH, hxM0⟩)
            have hwt := hin (w F) ⟨F, fun t ht => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl <;> assumption, Finset.disjoint_empty_right _, rfl⟩
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _)))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S haF))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hbF))))
              hwt.to_convexHull
    · have hH_emp : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      have hBD : B = D := by dsimp [D]; rw [hH_emp, Finset.sdiff_empty]
      rw [hBD] at hzB
      rcases h_convD_cov z hz hzB with hhp | hconv
      · exact Or.inl hhp
      · exact Or.inr (convexHull_mono Set.subset_union_left hconv))
  have hle := hcomb.2.1 hQ_card
  change (M \ M0).card ≤ 2 at hle
  omega

private lemma pentagon_Q1_M00_absurd {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (p : Fin n) (hpD : p ∈ hullVertices S \ certifiedVertices S w)
    (hBack_p : ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)))
    (hp_hp : ∃ H_hp : OpenHalfPlane,
      IsHalfPlaneTest P (WitnessSet ((hullVertices S \ certifiedVertices S w).erase p) ∅ w) (S p) H_hp)
    (h_H_disj : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) → l ≠ p ∧ r ≠ p)
    (h_convD_cov : ∀ z ∈ interiorPoints S,
      S z ∈ convexHull ℝ (((hullVertices S \ certifiedVertices S w).image S) : Set (ℝ × ℝ)) →
      (∃ H_hp : OpenHalfPlane,
        IsHalfPlaneTest P (WitnessSet ((hullVertices S \ certifiedVertices S w).erase p) ∅ w) (S z) H_hp) ∨
      S z ∈ convexHull ℝ ((((hullVertices S \ certifiedVertices S w).erase p).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ))) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let Q : Finset (Fin n) := {p}
  let F : Finset (Fin n) := (D \ Q) ∪ ∅
  have hFeq : F = D.erase p := by dsimp [F, Q]; rw [Finset.union_empty, Finset.sdiff_singleton_eq_erase]
  have hQ_sub : Q ⊆ D := Finset.singleton_subset_iff.mpr hpD
  have hQ_card : Q.card = 1 := Finset.card_singleton p
  have hM0_sub : (∅ : Finset (Fin n)) ⊆ M := Finset.empty_subset M
  have hD3 : 3 ≤ D.card := by change 3 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hD5' : 5 ≤ D.card := by change 5 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hH_cov : ∀ h ∈ H \ ∅, ∃ a b : Fin n, a ∈ F ∧ b ∈ F ∧ a ≠ b ∧
      ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h) := by
    intro h hh
    exact h25.side_preservation ⟨h, (Finset.mem_sdiff.mp hh).1⟩ hD5' Q ∅
      hQ_sub (by omega) hM0_sub (fun q hq => by rw [Finset.mem_singleton] at hq; subst hq; exact hBack_p) h hh
  have hFeq' : ((hullVertices S \ certifiedVertices S w) \ {p}) ∪ ∅ =
      (hullVertices S \ certifiedVertices S w).erase p := by
    rw [Finset.union_empty, Finset.sdiff_singleton_eq_erase]
  have hcomb := combination_lemma_core hPoly h25 hQ_sub (Or.inl hQ_card) hM0_sub
    (fun q hq => by rw [Finset.mem_singleton] at hq; subst hq; rw [hFeq']; exact hp_hp)
    hH_cov (fun z hz => by
      have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
      have hzB : S z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := mem_convexHull_hullVertices S hPoly.s_inj z
      by_cases hHne : H.Nonempty
      · obtain ⟨l, r, hlD, hrD, hlr, hed', hH_neg, _, _, h_edges, _, _⟩ := h25.certified_structure.2 hHne
        have hed := hed' hD3
        obtain ⟨hlp, hrp⟩ := h_H_disj l r hHne hed hH_neg
        have hlF : l ∈ F := by rw [hFeq]; exact Finset.mem_erase.mpr ⟨hlp, hlD⟩
        have hrF : r ∈ F := by rw [hFeq]; exact Finset.mem_erase.mpr ⟨hrp, hrD⟩
        rcases convexHull_B_subset_convD_union_lrH hPoly h25 hD3 hlD hrD h_edges hzB with hzD | hzH
        · rw [hFeq']
          rcases h_convD_cov z hzA hzD with hhp | hconv
          · exact Or.inl hhp
          · exact Or.inr (convexHull_mono Set.subset_union_left hconv)
        · right
          refine convexHull_min (fun y hy => ?_) (convex_convexHull ℝ _) hzH
          rcases Finset.mem_image.mp (Finset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hxH
          · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hlF)))
          · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hrF)))
          · obtain ⟨a, b, haF, hbF, _, hin⟩ := hH_cov x (Finset.mem_sdiff.mpr ⟨hxH, Finset.notMem_empty _⟩)
            have hwt := hin (w F) ⟨F, fun t ht => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl <;> assumption, Finset.disjoint_empty_right _, rfl⟩
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _)))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S haF))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hbF))))
              hwt.to_convexHull
      · have hH_emp : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
        have hBD : B = D := by dsimp [D]; rw [hH_emp, Finset.sdiff_empty]
        rw [hBD] at hzB
        rw [hFeq']
        rcases h_convD_cov z hzA hzB with hhp | hconv
        · exact Or.inl hhp
        · exact Or.inr (convexHull_mono Set.subset_union_left hconv))
  have hle := hcomb.1 hQ_card
  rw [Finset.sdiff_empty] at hle
  omega

private lemma segmentsCross_of_conv3 {v y0 r a b z : ℝ × ℝ}
    (hc : orient2D y0 r v ≠ 0)
    (hcross_a : SegmentsCross v a y0 r) (hcross_b : SegmentsCross v b y0 r)
    (hz_tri : z ∈ convexHull ℝ ({y0, a, b} : Set (ℝ × ℝ)))
    (hz_ne : orient2D y0 r z ≠ 0) :
    SegmentsCross v z y0 r := by
  have hid : ∀ p, orient2D v y0 p + orient2D v p r + orient2D y0 r p = orient2D y0 r v := by
    intro p; unfold orient2D; ring
  have hsign : ∀ p, SegmentsCross v p y0 r →
      orient2D y0 r v * orient2D y0 r p < 0 ∧
      0 < orient2D y0 r v * orient2D v y0 p ∧
      0 < orient2D y0 r v * orient2D v p r := by
    intro p ⟨h1, h2⟩
    have h2' : orient2D y0 r v * orient2D y0 r p < 0 := h2
    have h1' : 0 < orient2D v y0 p * orient2D v p r := by
      have heq : orient2D v p y0 = - orient2D v y0 p := by unfold orient2D; ring
      rw [heq] at h1; linarith
    have hp_id := hid p
    rcases lt_or_gt_of_ne hc with hn | hp
    · have hyr_pos : 0 < orient2D y0 r p := by nlinarith
      have hsum_neg : orient2D v y0 p + orient2D v p r < 0 := by linarith
      rcases mul_pos_iff.mp h1' with ⟨hvy_p, hvp_p⟩ | ⟨hvy_n, hvp_n⟩
      · linarith
      · exact ⟨h2', mul_pos_of_neg_of_neg hn hvy_n, mul_pos_of_neg_of_neg hn hvp_n⟩
    · have hyr_neg : orient2D y0 r p < 0 := by nlinarith
      have hsum_pos : 0 < orient2D v y0 p + orient2D v p r := by linarith
      rcases mul_pos_iff.mp h1' with ⟨hvy_p, hvp_p⟩ | ⟨hvy_n, hvp_n⟩
      · exact ⟨h2', mul_pos hp hvy_p, mul_pos hp hvp_p⟩
      · linarith
  obtain ⟨ha1, ha2, ha3⟩ := hsign a hcross_a
  obtain ⟨hb1, hb2, hb3⟩ := hsign b hcross_b
  rw [← inClosedTri_iff_mem_convexHull] at hz_tri
  rcases hz_tri with ⟨t1, s1, s2, ht1, hs1, hs2, hts, hz1, hz2⟩
  have hz_yr_neg : orient2D y0 r v * orient2D y0 r z < 0 := by
    have hle : orient2D y0 r v * orient2D y0 r z ≤ 0 := by
      have hid_z : orient2D y0 r z =
          t1 * orient2D y0 r y0 + s1 * orient2D y0 r a + s2 * orient2D y0 r b :=
        orient2D_convex_comb3 y0 r y0 a b z t1 s1 s2 hts hz1 hz2
      rw [hid_z, orient2D_self_outer, mul_zero, zero_add]
      nlinarith [mul_nonneg hs1 (le_of_lt (neg_pos.mpr ha1)),
        mul_nonneg hs2 (le_of_lt (neg_pos.mpr hb1))]
    exact lt_of_le_of_ne hle (mul_ne_zero hc hz_ne)
  have hs_pos : 0 < s1 + s2 := by
    by_contra hle
    have hs10 : s1 = 0 := by linarith
    have hs20 : s2 = 0 := by linarith
    have ht11 : t1 = 1 := by linarith
    rw [ht11, hs10, hs20] at hz1 hz2
    simp only [one_mul, zero_mul, add_zero] at hz1 hz2
    have hz_eq : z = y0 := Prod.ext hz1 hz2
    rw [hz_eq, orient2D_self_outer] at hz_ne
    exact hz_ne rfl
  have hc_vy_pos : 0 < orient2D y0 r v * orient2D v y0 z := by
    have hid_vy : orient2D v y0 z =
        t1 * orient2D v y0 y0 + s1 * orient2D v y0 a + s2 * orient2D v y0 b :=
      orient2D_convex_comb3 v y0 y0 a b z t1 s1 s2 hts hz1 hz2
    rw [hid_vy, orient2D_self_right, mul_zero, zero_add]
    have heq : orient2D y0 r v * (s1 * orient2D v y0 a + s2 * orient2D v y0 b) =
        s1 * (orient2D y0 r v * orient2D v y0 a) + s2 * (orient2D y0 r v * orient2D v y0 b) := by ring
    rw [heq]
    by_cases hs1p : 0 < s1
    · nlinarith [mul_pos hs1p ha2, mul_nonneg hs2 (le_of_lt hb2)]
    · have hs10 : s1 = 0 := by linarith
      rw [hs10, zero_mul, zero_add]
      exact mul_pos (by linarith) hb2
  have hc_vr_pos : 0 < orient2D y0 r v * orient2D v z r := by
    have hid_vr : orient2D v z r = -(t1 * orient2D v r y0 + s1 * orient2D v r a + s2 * orient2D v r b) := by
      have hid := orient2D_convex_comb3 v r y0 a b z t1 s1 s2 hts hz1 hz2
      have h1 : orient2D v z r = -orient2D v r z := by unfold orient2D; ring
      rw [h1, hid]
    have hc2 : 0 ≤ t1 * (orient2D y0 r v * orient2D v y0 r) := by
      have heq : orient2D v y0 r = orient2D y0 r v := by unfold orient2D; ring
      rw [heq]; exact mul_nonneg ht1 (mul_self_nonneg _)
    have hvr_a : orient2D v r a = -orient2D v a r := by unfold orient2D; ring
    have hvr_b : orient2D v r b = -orient2D v b r := by unfold orient2D; ring
    have hv_yr : orient2D v r y0 = -orient2D v y0 r := by unfold orient2D; ring
    rw [hvr_a, hvr_b, hv_yr] at hid_vr
    have heq : orient2D y0 r v * orient2D v z r =
        t1 * (orient2D y0 r v * orient2D v y0 r) +
        (s1 * (orient2D y0 r v * orient2D v a r) + s2 * (orient2D y0 r v * orient2D v b r)) := by
      rw [hid_vr]; ring
    rw [heq]
    have hpos : 0 < s1 * (orient2D y0 r v * orient2D v a r) + s2 * (orient2D y0 r v * orient2D v b r) := by
      by_cases hs1p : 0 < s1
      · nlinarith [mul_pos hs1p ha3, mul_nonneg hs2 (le_of_lt hb3)]
      · have hs10 : s1 = 0 := by linarith
        rw [hs10, zero_mul, zero_add]
        exact mul_pos (by linarith) hb3
    linarith
  refine ⟨?_, hz_yr_neg⟩
  have heq : orient2D v z y0 = - orient2D v y0 z := by unfold orient2D; ring
  rw [heq]
  have hp : 0 < (orient2D y0 r v * orient2D v y0 z) * (orient2D y0 r v * orient2D v z r) :=
    mul_pos hc_vy_pos hc_vr_pos
  have hc2 : 0 < (orient2D y0 r v) ^ 2 := sq_pos_of_ne_zero hc
  nlinarith

private lemma segmentsCross_of_conv_anchor {v y0 r a z : ℝ × ℝ}
    (hc : orient2D y0 r v ≠ 0)
    (hcross_a : SegmentsCross v a y0 r)
    (hz_tri : z ∈ convexHull ℝ ({y0, r, a} : Set (ℝ × ℝ)))
    (hz_ne : orient2D y0 r z ≠ 0) :
    SegmentsCross v z y0 r := by
  have hid : ∀ p, orient2D v y0 p + orient2D v p r + orient2D y0 r p = orient2D y0 r v := by
    intro p; unfold orient2D; ring
  have hsign : orient2D y0 r v * orient2D y0 r a < 0 ∧
      0 < orient2D y0 r v * orient2D v y0 a ∧
      0 < orient2D y0 r v * orient2D v a r := by
    rcases hcross_a with ⟨h1, h2⟩
    have h1' : 0 < orient2D v y0 a * orient2D v a r := by
      have heq : orient2D v a y0 = - orient2D v y0 a := by unfold orient2D; ring
      rw [heq] at h1; linarith
    have ha_id := hid a
    rcases lt_or_gt_of_ne hc with hn | hp
    · have hyr_pos : 0 < orient2D y0 r a := by nlinarith
      rcases mul_pos_iff.mp h1' with ⟨hvy_p, hvp_p⟩ | ⟨hvy_n, hvp_n⟩
      · linarith
      · exact ⟨h2, mul_pos_of_neg_of_neg hn hvy_n, mul_pos_of_neg_of_neg hn hvp_n⟩
    · have hyr_neg : orient2D y0 r a < 0 := by nlinarith
      rcases mul_pos_iff.mp h1' with ⟨hvy_p, hvp_p⟩ | ⟨hvy_n, hvp_n⟩
      · exact ⟨h2, mul_pos hp hvy_p, mul_pos hp hvp_p⟩
      · linarith
  rcases hsign with ⟨ha1, ha2, ha3⟩
  rw [← inClosedTri_iff_mem_convexHull] at hz_tri
  rcases hz_tri with ⟨t1, t2, s, ht1, ht2, hs, hts, hz1, hz2⟩
  have hid_yr : orient2D y0 r z = s * orient2D y0 r a := by
    have h := orient2D_convex_comb3 y0 r y0 r a z t1 t2 s hts hz1 hz2
    rw [orient2D_self_outer, orient2D_self_right, mul_zero, mul_zero, zero_add, zero_add] at h
    exact h
  have hs_pos : 0 < s := by
    rcases eq_or_lt_of_le hs with h0 | hp
    · rw [← h0, zero_mul] at hid_yr; exact False.elim (hz_ne hid_yr)
    · exact hp
  have hz_yr_neg : orient2D y0 r v * orient2D y0 r z < 0 := by
    rw [hid_yr]; nlinarith [mul_pos hs_pos (neg_pos.mpr ha1)]
  have hc_vy_pos : 0 < orient2D y0 r v * orient2D v y0 z := by
    have hid_vy : orient2D v y0 z = t2 * orient2D v y0 r + s * orient2D v y0 a := by
      have h := orient2D_convex_comb3 v y0 y0 r a z t1 t2 s hts hz1 hz2
      rw [orient2D_self_right, mul_zero, zero_add] at h; exact h
    have hc2 : 0 ≤ t2 * (orient2D y0 r v * orient2D v y0 r) := by
      have heq : orient2D v y0 r = orient2D y0 r v := by unfold orient2D; ring
      rw [heq]; exact mul_nonneg ht2 (mul_self_nonneg _)
    have heq : orient2D y0 r v * orient2D v y0 z =
        t2 * (orient2D y0 r v * orient2D v y0 r) + s * (orient2D y0 r v * orient2D v y0 a) := by
      rw [hid_vy]; ring
    rw [heq]; linarith [mul_pos hs_pos ha2]
  have hc_vr_pos : 0 < orient2D y0 r v * orient2D v z r := by
    have hid_vr : orient2D v z r = t1 * orient2D v y0 r + s * orient2D v a r := by
      have h := orient2D_convex_comb3 v r y0 r a z t1 t2 s hts hz1 hz2
      have h1 : orient2D v z r = -orient2D v r z := by unfold orient2D; ring
      have h2 : orient2D v r y0 = -orient2D v y0 r := by unfold orient2D; ring
      have h3 : orient2D v r a = -orient2D v a r := by unfold orient2D; ring
      rw [h1, h, orient2D_self_right, mul_zero, add_zero, h2, h3]; ring
    have hc2 : 0 ≤ t1 * (orient2D y0 r v * orient2D v y0 r) := by
      have heq : orient2D v y0 r = orient2D y0 r v := by unfold orient2D; ring
      rw [heq]; exact mul_nonneg ht1 (mul_self_nonneg _)
    have heq : orient2D y0 r v * orient2D v z r =
        t1 * (orient2D y0 r v * orient2D v y0 r) + s * (orient2D y0 r v * orient2D v a r) := by
      rw [hid_vr]; ring
    rw [heq]; linarith [mul_pos hs_pos ha3]
  refine ⟨?_, hz_yr_neg⟩
  have heq : orient2D v z y0 = - orient2D v y0 z := by unfold orient2D; ring
  rw [heq]
  have hp : 0 < (orient2D y0 r v * orient2D v y0 z) * (orient2D y0 r v * orient2D v z r) :=
    mul_pos hc_vy_pos hc_vr_pos
  have hc2 : 0 < (orient2D y0 r v) ^ 2 := sq_pos_of_ne_zero hc
  nlinarith

private lemma pentagon_exit_nonfacing_local {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    {D : Finset (Fin n)} (hDB : D = hullVertices S \ certifiedVertices S w)
    (cycD : CCWCycle S D 2) {y : Fin n} (hyM : y ∈ Finset.univ \ D)
    {v : ℝ × ℝ} (i : Fin 5)
    (hy_tri : InIntTri v (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y))
    (h_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun i, cycD.toFun (i + 1)) ≠ (l, r)) :
    0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) v := by
  have hy_notD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
  have he_D : IsCCWEdge S D (cycD.toFun i) (cycD.toFun (i + 1)) := ccwCycle_isCCWEdge cycD i
  have hD3 : 3 ≤ D.card := by
    rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]; omega
  have he_B := isCCWEdge_B_of_D_ne_lr h25 (hDB ▸ hD3) (hDB ▸ he_D)
    (fun l r hH _ _ _ hlrD hHn => h_not_lr l r hH (hDB ▸ hlrD) hHn)
  have hccw : 0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y) :=
    orient2D_pos_of_isCCWEdge_B hPoly he_B
      (fun h => hy_notD (h ▸ ccwCycle_mem cycD i))
      (fun h => hy_notD (h ▸ ccwCycle_mem cycD (i + 1)))
  rcases hy_tri with ⟨μ₁, _, _, hm1, _, _, hs, hy1, hy2⟩
  have hid : orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y) =
      μ₁ * orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) v := by
    unfold orient2D; rw [hy1, hy2]
    linear_combination ((S (cycD.toFun i)).2 * (S (cycD.toFun (i + 1))).1 -
      (S (cycD.toFun i)).1 * (S (cycD.toFun (i + 1))).2) * hs
  nlinarith

private lemma segmentsCross_of_angleLt {v0 q sa sp sc : ℝ × ℝ}
    (h : ((AngleLt v0 q sa sp ∧ AngleLt v0 q sp sc ∧
        0 < orient2D sa sp sc ∧ 0 < orient2D sa sp v0 ∧ 0 < orient2D sp sc v0) ∨
       (AngleLt v0 q sc sp ∧ AngleLt v0 q sp sa ∧
        0 < orient2D sa sp sc ∧ 0 < orient2D sa sp v0 ∧ 0 < orient2D sp sc v0))) :
    SegmentsCross v0 sp sa sc := by
  rcases h with ⟨hap, hpc, ho1, ho2, ho3⟩ | ⟨hcp, hpa, ho1, ho2, ho3⟩
  · have hac := hap.trans hpc
    have hva : 0 < orient2D v0 sa sp := by unfold orient2D at ho2 ⊢; linarith
    have hvqa : 0 < orient2D v0 q sa := by
      rcases mul_pos_iff.mp hap.2 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    have hvac : 0 < orient2D v0 sa sc := by
      rcases mul_pos_iff.mp hac.2 with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · linarith
    refine ⟨?_, ?_⟩
    · have h1 : orient2D v0 sp sa < 0 := by unfold orient2D at ho2 ⊢; linarith
      have h2 : 0 < orient2D v0 sp sc := by unfold orient2D at ho3 ⊢; linarith
      exact mul_neg_of_neg_of_pos h1 h2
    · have h1 : 0 < orient2D sa sc v0 := by unfold orient2D at hvac ⊢; linarith
      have h2 : orient2D sa sc sp < 0 := by unfold orient2D at ho1 ⊢; linarith
      exact mul_neg_of_pos_of_neg h1 h2
  · have hca := hcp.trans hpa
    have hvp : 0 < orient2D v0 sp sc := by unfold orient2D at ho3 ⊢; linarith
    have hvqc : orient2D v0 q sc < 0 := by
      rcases mul_pos_iff.mp hcp.2 with ⟨_, h2⟩ | ⟨h1, _⟩
      · have : orient2D v0 sc sp < 0 := by unfold orient2D at hvp ⊢; linarith
        linarith
      · exact h1
    have hvca : orient2D v0 sc sa < 0 := by
      rcases mul_pos_iff.mp hca.2 with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · exact h2
    refine ⟨?_, ?_⟩
    · have h1 : orient2D v0 sp sa < 0 := by unfold orient2D at ho2 ⊢; linarith
      have h2 : 0 < orient2D v0 sp sc := by unfold orient2D at ho3 ⊢; linarith
      exact mul_neg_of_neg_of_pos h1 h2
    · have h1 : 0 < orient2D sa sc v0 := by unfold orient2D at hvca ⊢; linarith
      have h2 : orient2D sa sc sp < 0 := by unfold orient2D at ho1 ⊢; linarith
      exact mul_neg_of_pos_of_neg h1 h2

private lemma opposite_endpoint_ig0_absurd {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (cycB : CCWCycle S (hullVertices S) 3)
    {h y0 : Fin n}
    (hhH : h ∈ certifiedVertices S w) (hH_card1 : (certifiedVertices S w).card = 1)
    (e_lh : IsCCWEdge S (hullVertices S) (cyc0.toFun 0) h)
    (hB0 : cycB.toFun 0 = cyc0.toFun 4) (hB1 : cycB.toFun 1 = cyc0.toFun 0)
    (hB2 : cycB.toFun 2 = h) (hB3 : cycB.toFun 3 = cyc0.toFun 1)
    (hB4 : cycB.toFun 4 = cyc0.toFun 2) (hB5 : cycB.toFun 5 = cyc0.toFun 3)
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0_A : y0 ∈ interiorPoints S) (hy0_nH : y0 ∉ certifiedVertices S w)
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cyc0.toFun 4)) (S (cyc0.toFun 0)) (S y0) (S z))
    (hl_cross : SegmentsCross (w (Finset.univ \ {cyc0.toFun 3, y0, cyc0.toFun 1}))
      (S (cyc0.toFun 0)) (S y0) (S (cyc0.toFun 1)))
    (hl_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, cyc0.toFun 1} ∅ w) (S (cyc0.toFun 0)) Hp)
    (hh_gap : GoodAnchorPair P S w {cyc0.toFun 3, y0, cyc0.toFun 1} y0 (cyc0.toFun 1))
    (hh_cross : SegmentsCross (w (Finset.univ \ {cyc0.toFun 3, y0, cyc0.toFun 1}))
      (S h) (S y0) (S (cyc0.toFun 1)))
    (hh_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, cyc0.toFun 1} ∅ w) (S h) Hp) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let l := cyc0.toFun 0
  let r := cyc0.toFun 1
  let d1 := cyc0.toFun 2
  let d2 := cyc0.toFun 3
  let d3 := cyc0.toFun 4
  let O0 : Finset (Fin n) := {d2, y0, r}
  let v0 := w (Finset.univ \ O0)
  have hD_sub_B : D ⊆ B := Finset.sdiff_subset
  have hhB : h ∈ B := (Finset.mem_filter.mp hhH).1
  have hy0_nD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  let F0 : Finset (Fin n) := {r, d1, d2, d3, y0}
  have hy0_F0 : y0 ∈ F0 := by simp [F0]
  have hr_F0 : r ∈ F0 := by simp [F0]
  have hd1_F0 : d1 ∈ F0 := by simp [F0]
  have hd2_F0 : d2 ∈ F0 := by simp [F0]
  have hd3_F0 : d3 ∈ F0 := by simp [F0]
  let A := interiorPoints S
  have hA_card : A.card = 4 := by
    have hm_eq : M = A ∪ H := M_eq_interior_union_H S w
    have hdisj : Disjoint A H := Finset.disjoint_left.mpr fun x hxA hxH =>
      (Finset.mem_sdiff.mp hxA).2 (Finset.mem_filter.mp hxH).1
    have hc : (A ∪ H).card = A.card + H.card := Finset.card_union_of_disjoint hdisj
    have hMc : M.card = 5 := le_antisymm (M_card_le_five h25) hM5
    rw [hm_eq] at hMc
    change H.card = 1 at hH_card1
    omega
  let A' := A.erase y0
  have hA'_card : A'.card = 3 := by dsimp [A']; rw [Finset.card_erase_of_mem hy0_A, hA_card]
  have h5_inj : Function.Injective (fun i : Fin 5 =>
      if i.val < 2 then if i.val = 0 then l else h
      else ((A'.equivFin.symm ⟨i.val - 2, by omega⟩ : {x // x ∈ A'}) : Fin n)) := by
    have hl_nA : l ∉ A' := fun hm => (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hm)).2 (hD_sub_B (ccwCycle_mem cyc0 0))
    have hh_nA : h ∉ A' := fun hm => (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hm)).2 hhB
    have hl_nh : l ≠ h := e_lh.2.2.1
    intro i j hij
    by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
    · simp only [hi, hj, ↓reduceIte] at hij
      by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
      · exact Fin.ext (hi0.trans hj0.symm)
      · simp only [hi0, hj0, ↓reduceIte] at hij; exact absurd hij hl_nh
      · simp only [hi0, hj0, ↓reduceIte] at hij; exact absurd hij.symm hl_nh
      · exact Fin.ext (by omega)
    · exfalso
      simp only [hi, hj, ↓reduceIte] at hij
      by_cases hi0 : i.val = 0
      · simp only [hi0, ↓reduceIte] at hij; exact hl_nA (hij ▸ (A'.equivFin.symm _).2)
      · simp only [hi0, ↓reduceIte] at hij; exact hh_nA (hij ▸ (A'.equivFin.symm _).2)
    · exfalso
      simp only [hi, hj, ↓reduceIte] at hij
      by_cases hj0 : j.val = 0
      · simp only [hj0, ↓reduceIte] at hij; exact hl_nA (hij.symm ▸ (A'.equivFin.symm _).2)
      · simp only [hj0, ↓reduceIte] at hij; exact hh_nA (hij.symm ▸ (A'.equivFin.symm _).2)
    · simp only [hi, hj, ↓reduceIte] at hij
      have he := congrArg Fin.val (A'.equivFin.symm.injective (Subtype.ext hij))
      exact Fin.ext (by dsimp at he; omega)
  let f5 : Fin 5 → Fin n := fun i =>
    if i.val < 2 then if i.val = 0 then l else h
    else ((A'.equivFin.symm ⟨i.val - 2, by omega⟩ : {x // x ∈ A'}) : Fin n)
  have hf5_out : ∀ i : Fin 5, f5 i ∉ F0 := by
    intro i hm
    have hD_sub : ∀ x ∈ F0, x = y0 ∨ x ∈ D := fun x hx => by
      simp only [F0, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (ccwCycle_mem cyc0 1)
      · exact Or.inr (ccwCycle_mem cyc0 2)
      · exact Or.inr (ccwCycle_mem cyc0 3)
      · exact Or.inr (ccwCycle_mem cyc0 4)
      · exact Or.inl rfl
    rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4) with
      hi0 | hi1 | hi2 | hi3 | hi4
    · have hf0 : f5 i = l := by dsimp [f5]; rw [if_pos (by omega), if_pos hi0]
      rw [hf0] at hm
      simp only [F0, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with e | e | e | e | e
      · exact cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1) e
      · exact cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2) e
      · exact cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3) e
      · exact cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4) e
      · exact hy0_nD (e ▸ ccwCycle_mem cyc0 0)
    · have hf1 : f5 i = h := by dsimp [f5]; rw [if_pos (by omega), if_neg (by omega)]
      rw [hf1] at hm
      rcases hD_sub h hm with e | e
      · exact hy0_nH (e ▸ hhH)
      · exact (Finset.mem_sdiff.mp e).2 hhH
    · have hf2 : f5 i = (A'.equivFin.symm ⟨0, by omega⟩ : {x // x ∈ A'}).1 := by
        simp [f5, hi2]
      have hzA' := (A'.equivFin.symm ⟨0, by omega⟩).2
      rw [hf2] at hm
      rcases hD_sub _ hm with e | e
      · exact (Finset.mem_erase.mp hzA').1 e
      · exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hzA')).2 (hD_sub_B e)
    · have hf3 : f5 i = (A'.equivFin.symm ⟨1, by omega⟩ : {x // x ∈ A'}).1 := by
        simp [f5, hi3]
      have hzA' := (A'.equivFin.symm ⟨1, by omega⟩).2
      rw [hf3] at hm
      rcases hD_sub _ hm with e | e
      · exact (Finset.mem_erase.mp hzA').1 e
      · exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hzA')).2 (hD_sub_B e)
    · have hf4 : f5 i = (A'.equivFin.symm ⟨2, by omega⟩ : {x // x ∈ A'}).1 := by
        simp [f5, hi4]
      have hzA' := (A'.equivFin.symm ⟨2, by omega⟩).2
      rw [hf4] at hm
      rcases hD_sub _ hm with e | e
      · exact (Finset.mem_erase.mp hzA').1 e
      · exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hzA')).2 (hD_sub_B e)
  have htests : ∀ i : Fin 5,
      (i.val < 2 → ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F0 ∅ w) (S (f5 i)) H_hp) ∧
      (2 ≤ i.val → (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F0 ∅ w) (S (f5 i)) H_hp) ∨
        ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F0 ∅ w) (S (f5 i)) R) := by
    intro i
    constructor
    · intro hi
      by_cases hi0 : i.val = 0
      · have hf0 : f5 i = l := by dsimp [f5]; rw [if_pos (by omega), if_pos hi0]
        rw [hf0]; exact hex_lift_hp hy0_F0 hr_F0 hl_hp
      · have hf1 : f5 i = h := by dsimp [f5]; rw [if_pos (by omega), if_neg hi0]
        rw [hf1]; exact hex_lift_hp hy0_F0 hr_F0 hh_hp
    · intro hi
      let z := f5 i
      have hlt2 : ¬ i.val < 2 := by omega
      have hzA' : z ∈ A' := by
        dsimp [z, f5]; simp only [hlt2, ↓reduceIte]; exact (A'.equivFin.symm _).2
      have hzA : z ∈ A := Finset.mem_of_mem_erase hzA'
      have hz_nB : z ∉ B := (Finset.mem_sdiff.mp hzA).2
      have hz_ny0 : z ≠ y0 := (Finset.mem_erase.mp hzA').1
      have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => hz_nB (hD_sub_B hd)⟩
      have hzB : S z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := mem_convexHull_hullVertices S hPoly.s_inj z
      let pB : Fin 6 → ℝ × ℝ := fun j => S (cycB.toFun j)
      have hzB' : S z ∈ convexHull ℝ (Set.range pB) := by
        have hr : Set.range pB = (B.image S : Set (ℝ × ℝ)) := by
          dsimp [B]; conv_rhs => rw [← cycB.image_eq]
          ext p; simp [pB]
        rwa [hr]
      obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pB cycB.ccw (S y0) (S z) hzB'
      have hz_F0_wedge : S z ∈ convexHull ℝ ((F0.image S : Set (ℝ × ℝ)) ∪ {w F0}) →
          ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F0 ∅ w) (S z) R :=
        fun hconv => h25.fan_corollary F0 F0 z Subset.rfl (hf5_out i) hconv
      rcases (by omega : m.val = 0 ∨ m.val = 1 ∨ m.val = 2 ∨ m.val = 3 ∨ m.val = 4 ∨ m.val = 5) with
        hm0 | hm1 | hm2 | hm3 | hm4 | hm5
      · exfalso
        have hme : m = 0 := Fin.ext hm0
        rw [hme] at hm
        change S z ∈ convexHull ℝ {S (cycB.toFun 0), S (cycB.toFun 1), S y0} at hm
        rw [hB0, hB1] at hm
        exact hy0_empty z (Finset.mem_erase.mpr ⟨hz_ny0, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hm)
      · left
        have hme : m = 1 := Fin.ext hm1
        rw [hme] at hm
        change S z ∈ convexHull ℝ {S (cycB.toFun 1), S (cycB.toFun 2), S y0} at hm
        rw [hB1, hB2] at hm
        have hcv : orient2D (S y0) (S r) v0 ≠ 0 := by
          have := hl_cross.2
          intro h; rw [h, zero_mul] at this; exact lt_irrefl 0 this
        have hcz : orient2D (S y0) (S r) (S z) ≠ 0 := hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
          (hPoly.s_inj.ne (fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 1)))
          (hPoly.s_inj.ne (fun e => hz_nB (hD_sub_B (e ▸ ccwCycle_mem cyc0 1))))
          (hPoly.s_inj.ne hz_ny0.symm)
        have heq1 : ({S l, S h, S y0} : Set (ℝ × ℝ)) = {S y0, S l, S h} := by
          ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro (rfl | rfl | rfl)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl rfl
          · rintro (rfl | rfl | rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
        rw [heq1] at hm
        have hcross_z := segmentsCross_of_conv3 hcv hl_cross hh_cross hm hcz
        have hz_nO0 : z ∉ O0 := by
          simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => hz_nB (hD_sub_B (e ▸ ccwCycle_mem cyc0 3)), hz_ny0,
                 fun e => hz_nB (hD_sub_B (e ▸ ccwCycle_mem cyc0 1))⟩
        exact hex_lift_hp hy0_F0 hr_F0 (goodAnchorPair_universal_crossing hPoly h25 hh_gap hz_nO0 hcross_z).1
      · left
        have hme : m = 2 := Fin.ext hm2
        rw [hme] at hm
        change S z ∈ convexHull ℝ {S (cycB.toFun 2), S (cycB.toFun 3), S y0} at hm
        rw [hB2, hB3] at hm
        have hcv : orient2D (S y0) (S r) v0 ≠ 0 := by
          have := hh_cross.2
          intro h; rw [h, zero_mul] at this; exact lt_irrefl 0 this
        have hcz : orient2D (S y0) (S r) (S z) ≠ 0 := hPoly.no_three_collinear _ _ _
          (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
          (hPoly.s_inj.ne (fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 1)))
          (hPoly.s_inj.ne (fun e => hz_nB (hD_sub_B (e ▸ ccwCycle_mem cyc0 1))))
          (hPoly.s_inj.ne hz_ny0.symm)
        have heq : ({S h, S r, S y0} : Set (ℝ × ℝ)) = {S y0, S r, S h} := by
          ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro (rfl | rfl | rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl
          · rintro (rfl | rfl | rfl)
            · exact Or.inr (Or.inr rfl)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl rfl
        rw [heq] at hm
        have hcross_z := segmentsCross_of_conv_anchor hcv hh_cross hm hcz
        have hz_nO0 : z ∉ O0 := by
          simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => hz_nB (hD_sub_B (e ▸ ccwCycle_mem cyc0 3)), hz_ny0,
                 fun e => hz_nB (hD_sub_B (e ▸ ccwCycle_mem cyc0 1))⟩
        exact hex_lift_hp hy0_F0 hr_F0 (goodAnchorPair_universal_crossing hPoly h25 hh_gap hz_nO0 hcross_z).1
      · right
        have hme : m = 3 := Fin.ext hm3
        rw [hme] at hm
        change S z ∈ convexHull ℝ {S (cycB.toFun 3), S (cycB.toFun 4), S y0} at hm
        rw [hB3, hB4] at hm
        exact hz_F0_wedge (convexHull_mono Set.subset_union_left (convexHull_tri_subset
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hr_F0)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1_F0)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0_F0))) hm))
      · right
        have hme : m = 4 := Fin.ext hm4
        rw [hme] at hm
        change S z ∈ convexHull ℝ {S (cycB.toFun 4), S (cycB.toFun 5), S y0} at hm
        rw [hB4, hB5] at hm
        exact hz_F0_wedge (convexHull_mono Set.subset_union_left (convexHull_tri_subset
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1_F0)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2_F0)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0_F0))) hm))
      · right
        have hme : m = 5 := Fin.ext hm5
        rw [hme] at hm
        change S z ∈ convexHull ℝ {S (cycB.toFun 5), S (cycB.toFun (5 + 1)), S y0} at hm
        rw [show (5 + 1 : Fin 6) = 0 from by decide, hB5, hB0] at hm
        exact hz_F0_wedge (convexHull_mono Set.subset_union_left (convexHull_tri_subset
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2_F0)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3_F0)))
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0_F0))) hm))
  let aH : Fin 2 → Fin n := fun i => f5 ⟨i.val, by omega⟩
  let aW : Fin 3 → Fin n := fun j => f5 ⟨j.val + 2, by omega⟩
  have ha_inj : Function.Injective (Sum.elim aH aW) := by
    rintro (i | i) (j | j) hij
    · dsimp only [aH, aW, Sum.elim] at hij
      have := congrArg Fin.val (h5_inj hij)
      exact congrArg Sum.inl (Fin.ext (by dsimp at this; exact this))
    · dsimp only [aH, aW, Sum.elim] at hij
      have := congrArg Fin.val (h5_inj hij)
      exfalso; dsimp at this; omega
    · dsimp only [aH, aW, Sum.elim] at hij
      have := congrArg Fin.val (h5_inj hij)
      exfalso; dsimp at this; omega
    · dsimp only [aH, aW, Sum.elim] at hij
      have := congrArg Fin.val (h5_inj hij)
      exact congrArg Sum.inr (Fin.ext (by dsimp at this; omega))
  have hw2 : ∀ i : Fin 2, ∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F0 ∅ w) (S (aH i)) H_hp :=
    fun i => (htests ⟨i.val, by omega⟩).1 (by dsimp; omega)
  have hw3 : ∀ j : Fin 3, ∃ R : OpenWedge, IsWedgeTest P (WitnessSet F0 ∅ w) (S (aW j)) R := fun j => by
    rcases (htests ⟨j.val + 2, by omega⟩).2 (by dsimp; omega) with ⟨H_hp, hHp⟩ | ⟨R, hR⟩
    · exact halfPlaneTest_to_wedgeTest_on_finite P (WitnessSet F0 ∅ w) (witnessSet_finite F0 ∅ w)
        (S (aW j)) H_hp hHp
    · exact ⟨R, hR⟩
  choose H2 hH2 using hw2
  choose R3 hR3 using hw3
  exact no_two_hp_three_wedges_on_witnessSet hPoly h25 (Finset.disjoint_empty_right F0)
    aH aW ha_inj (fun i => ⟨hf5_out _, Finset.notMem_empty _⟩) (fun j => ⟨hf5_out _, Finset.notMem_empty _⟩)
    H2 R3 hH2 hR3

private lemma opposite_endpoint_ig2_absurd {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (cycB : CCWCycle S (hullVertices S) 3)
    {h y0 : Fin n}
    (hy0_nD : y0 ∉ hullVertices S \ certifiedVertices S w)
    (hB0 : cycB.toFun 0 = cyc0.toFun 4) (hB1 : cycB.toFun 1 = cyc0.toFun 0)
    (hB2 : cycB.toFun 2 = h) (hB3 : cycB.toFun 3 = cyc0.toFun 1)
    (hB5 : cycB.toFun 5 = cyc0.toFun 3)
    (h_cert_not_d1 : ∀ la ra : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) la ra →
      (∀ hc ∈ certifiedVertices S w, orient2D (S la) (S ra) (S hc) < 0) →
      la ≠ cyc0.toFun 2 ∧ ra ≠ cyc0.toFun 2)
    (hy0_in_d3lh : InIntTri (S (cyc0.toFun 4)) (S (cyc0.toFun 0)) (S h) (S y0))
    (hd1_gap : GoodAnchorPair P S w {cyc0.toFun 3, y0, cyc0.toFun 1} (cyc0.toFun 1) (cyc0.toFun 3))
    (hd1_cross : SegmentsCross (w (Finset.univ \ {cyc0.toFun 3, y0, cyc0.toFun 1}))
      (S (cyc0.toFun 2)) (S (cyc0.toFun 1)) (S (cyc0.toFun 3)))
    (hd1_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 1, cyc0.toFun 3} ∅ w) (S (cyc0.toFun 2)) Hp)
    (hd1_back : IsBackVertexOf S (hullVertices S) (cyc0.toFun 2)
      (w (Finset.univ \ {cyc0.toFun 3, y0, cyc0.toFun 1}))) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let l := cyc0.toFun 0
  let r := cyc0.toFun 1
  let d1 := cyc0.toFun 2
  let d2 := cyc0.toFun 3
  let d3 := cyc0.toFun 4
  let O0 : Finset (Fin n) := {d2, y0, r}
  have hD_sub_B : D ⊆ B := Finset.sdiff_subset
  have hr_F : r ∈ D.erase d1 := Finset.mem_erase.mpr ⟨cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2), ccwCycle_mem cyc0 1⟩
  have hd2_F : d2 ∈ D.erase d1 := Finset.mem_erase.mpr ⟨cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 2), ccwCycle_mem cyc0 3⟩
  have hd3_F : d3 ∈ D.erase d1 := Finset.mem_erase.mpr ⟨cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 2), ccwCycle_mem cyc0 4⟩
  have hl_F : l ∈ D.erase d1 := Finset.mem_erase.mpr ⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2), ccwCycle_mem cyc0 0⟩
  have hd1_nO0 : d1 ∉ O0 := by
    simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 2),
           cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1)⟩
  refine pentagon_Q1_M00_absurd hPoly h25 hD5 hM5 d1 (ccwCycle_mem cyc0 2)
    ⟨O0, hd1_nO0, pentagon_Ostar_nadj h25 hD5 cyc0 hy0_nD 3 1 (by decide) (by decide), hd1_back⟩
    (hex_lift_hp hr_F hd2_F hd1_hp) h_cert_not_d1 (fun z hzA _hzD => ?_)
  have hz_nB : z ∉ B := (Finset.mem_sdiff.mp hzA).2
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc0.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
    have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
      dsimp [D, B, H]; conv_rhs => rw [← cyc0.image_eq]
      ext p; simp [pD]
    rwa [hr]
  obtain ⟨m, hm⟩ := convexHull_ray_exit_polygon_cover pD cyc0.ccw (S r) (S z) hzD'
  rcases (by omega : m.val = 0 ∨ m.val = 1 ∨ m.val = 2 ∨ m.val = 3 ∨ m.val = 4) with
    hm0 | hm1 | hm2 | hm3 | hm4
  · exfalso
    have hme : m = 0 := Fin.ext hm0
    rw [hme] at hm
    change S z ∈ convexHull ℝ {S (cyc0.toFun 0), S (cyc0.toFun 1), S r} at hm
    have heq : ({S l, S r, S r} : Set (ℝ × ℝ)) = {S l, S r} := by ext x; simp
    change S z ∈ convexHull ℝ {S l, S r, S r} at hm
    rw [heq] at hm
    have ho0 : orient2D (S l) (S r) (S z) = 0 := by
      rw [convexHull_pair] at hm
      rcases hm with ⟨a, b, _, _, hs, h1⟩
      have h1x : (S z).1 = a * (S l).1 + b * (S r).1 := by simpa using congrArg Prod.fst h1.symm
      have h1y : (S z).2 = a * (S l).2 + b * (S r).2 := by simpa using congrArg Prod.snd h1.symm
      have ha : a = 1 - b := by linarith only [hs]
      unfold orient2D; rw [h1x, h1y, ha]; ring
    exact hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)))
      (hPoly.s_inj.ne (fun e => hz_nB (hD_sub_B (by rw [← e]; exact ccwCycle_mem cyc0 1))))
      (hPoly.s_inj.ne (fun e => hz_nB (hD_sub_B (by rw [← e]; exact ccwCycle_mem cyc0 0)))) ho0
  · exfalso
    have hme : m = 1 := Fin.ext hm1
    rw [hme] at hm
    change S z ∈ convexHull ℝ {S (cyc0.toFun 1), S (cyc0.toFun 2), S r} at hm
    have heq : ({S r, S d1, S r} : Set (ℝ × ℝ)) = {S r, S d1} := by ext x; simp [or_comm]
    change S z ∈ convexHull ℝ {S r, S d1, S r} at hm
    rw [heq] at hm
    have ho0 : orient2D (S r) (S d1) (S z) = 0 := by
      rw [convexHull_pair] at hm
      rcases hm with ⟨a, b, _, _, hs, h1⟩
      have h1x : (S z).1 = a * (S r).1 + b * (S d1).1 := by simpa using congrArg Prod.fst h1.symm
      have h1y : (S z).2 = a * (S r).2 + b * (S d1).2 := by simpa using congrArg Prod.snd h1.symm
      have ha : a = 1 - b := by linarith only [hs]
      unfold orient2D; rw [h1x, h1y, ha]; ring
    exact hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)))
      (hPoly.s_inj.ne (fun e => hz_nB (hD_sub_B (by rw [← e]; exact ccwCycle_mem cyc0 2))))
      (hPoly.s_inj.ne (fun e => hz_nB (hD_sub_B (by rw [← e]; exact ccwCycle_mem cyc0 1)))) ho0
  · left
    have hme : m = 2 := Fin.ext hm2
    rw [hme] at hm
    change S z ∈ convexHull ℝ {S (cyc0.toFun 2), S (cyc0.toFun 3), S r} at hm
    have hzy0_ne : z ≠ y0 := by
      intro h; subst h
      have hy0_rd2 : 0 < orient2D (S r) (S d2) (S z) := by
        obtain ⟨t1, t2, t3, ht1, ht2, ht3, htsum, hy1, hy2⟩ := hy0_in_d3lh
        have hid := orient2D_convex_comb3 (S r) (S d2) (S d3) (S l) (S h) (S z) t1 t2 t3 htsum hy1 hy2
        rw [hid]
        have ho1 : 0 < orient2D (S r) (S d2) (S d3) := by
          have ht := cycB.ccw_tri 0 3 5 (by decide) (by decide); rw [hB0, hB3, hB5] at ht; unfold orient2D at ht ⊢; linarith only [ht]
        have ho2 : 0 < orient2D (S r) (S d2) (S l) := by
          have ht := cycB.ccw_tri 1 3 5 (by decide) (by decide); rw [hB1, hB3, hB5] at ht; unfold orient2D at ht ⊢; linarith only [ht]
        have ho3 : 0 < orient2D (S r) (S d2) (S h) := by
          have ht := cycB.ccw_tri 2 3 5 (by decide) (by decide); rw [hB2, hB3, hB5] at ht; unfold orient2D at ht ⊢; linarith only [ht]
        nlinarith only [ht1, ht2, ht3, ho1, ho2, ho3, hid]
      have hge : 0 ≤ orient2D (S d2) (S r) (S z) := orient2D_const_le_convexHull (fun p hp => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · have ht := cyc0.ccw_tri 1 2 3 (by decide) (by decide)
          change orient2D (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) > 0 at ht
          change 0 ≤ orient2D (S (cyc0.toFun 3)) (S (cyc0.toFun 1)) (S (cyc0.toFun 2))
          unfold orient2D at ht ⊢; linarith only [ht]
        · change 0 ≤ orient2D (S (cyc0.toFun 3)) (S (cyc0.toFun 1)) (S (cyc0.toFun 3))
          rw [orient2D_self_outer]
        · change 0 ≤ orient2D (S d2) (S r) (S r)
          rw [orient2D_self_right]) hm
      unfold orient2D at hy0_rd2 hge; linarith only [hy0_rd2, hge]
    have hcap := cap_crossing_of_vertices_cross hPoly h25 hd1_gap {r, d1, d2}
      (fun g hg => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hd1_cross)
        · exact Or.inr (Or.inl rfl))
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun e => hz_nB (hD_sub_B (by rw [e]; exact ccwCycle_mem cyc0 3)), hzy0_ne,
                 fun e => hz_nB (hD_sub_B (by rw [e]; exact ccwCycle_mem cyc0 1))⟩)
      (fun e => hz_nB (hD_sub_B (by rw [e]; exact ccwCycle_mem cyc0 1)))
      (fun e => hz_nB (hD_sub_B (by rw [e]; exact ccwCycle_mem cyc0 3)))
      (by have heq : (({r, d1, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) =
              {S (cyc0.toFun 2), S (cyc0.toFun 3), S r} := by
            ext p; simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_insert,
              Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, r, d1, d2]
            constructor
            · rintro ⟨x, rfl | rfl | rfl, rfl⟩
              · exact Or.inr (Or.inr rfl)
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
            · rintro (rfl | rfl | rfl)
              · exact ⟨cyc0.toFun 2, Or.inr (Or.inl rfl), rfl⟩
              · exact ⟨cyc0.toFun 3, Or.inr (Or.inr rfl), rfl⟩
              · exact ⟨cyc0.toFun 1, Or.inl rfl, rfl⟩
          rwa [heq])
    exact hex_lift_hp hr_F hd2_F hcap.2.1
  · right
    have hme : m = 3 := Fin.ext hm3
    rw [hme] at hm
    change S z ∈ convexHull ℝ {S (cyc0.toFun 3), S (cyc0.toFun 4), S r} at hm
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2_F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3_F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hr_F))) hm
  · right
    have hme : m = 4 := Fin.ext hm4
    rw [hme] at hm
    change S z ∈ convexHull ℝ {S (cyc0.toFun 4), S (cyc0.toFun (4 + 1)), S r} at hm
    rw [show (4 + 1 : Fin 5) = 0 from by decide] at hm
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3_F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hl_F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hr_F))) hm

private lemma opposite_endpoint_hd3_d1_absurd {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y0 y1 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y1)
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cyc0.toFun 4)) (S (cyc0.toFun 0)) (S y0) (S z))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (S y1) (S z))
    (h_cert_not_d31 : ∀ la ra : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) la ra →
      (∀ hc ∈ certifiedVertices S w, orient2D (S la) (S ra) (S hc) < 0) →
      la ∉ ({cyc0.toFun 4, cyc0.toFun 2} : Finset (Fin n)) ∧
      ra ∉ ({cyc0.toFun 4, cyc0.toFun 2} : Finset (Fin n)))
    (hd1_back_O1 : ∃ O, cyc0.toFun 2 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 2) (w (Finset.univ \ O)))
    (hd1_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, cyc0.toFun 3} ∅ w) (S (cyc0.toFun 2)) Hp)
    (hd1_cap : ∀ z : Fin n, z ≠ y1 → z ≠ cyc0.toFun 3 → z ∉ ({cyc0.toFun 0, y1, cyc0.toFun 3} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({cyc0.toFun 2, y1, cyc0.toFun 3} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, cyc0.toFun 3} ∅ w) (S z) Hp)
    (hd3_back : ∃ O, cyc0.toFun 4 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 4) (w (Finset.univ \ O)))
    (hd3_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 3, y0} ∅ w) (S (cyc0.toFun 4)) Hp)
    (hd3_cap : ∀ z : Fin n, z ≠ cyc0.toFun 3 → z ≠ y0 → z ∉ ({cyc0.toFun 3, y0, cyc0.toFun 1} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({cyc0.toFun 4, cyc0.toFun 3, y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 3, y0} ∅ w) (S z) Hp) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let l := cyc0.toFun 0
  let r := cyc0.toFun 1
  let d1 := cyc0.toFun 2
  let d2 := cyc0.toFun 3
  let d3 := cyc0.toFun 4
  have hD_sub_B : D ⊆ B := Finset.sdiff_subset
  let Q : Finset (Fin n) := {d3, d1}
  let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
  have hd31_ne : d3 ≠ d1 := cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 2)
  have hlF : l ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 0, by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2)⟩⟩)
  have hrF : r ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 1, by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)⟩⟩)
  have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 3, by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 2)⟩⟩)
  have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
    (fun x hx => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ccwCycle_mem cyc0 4
      · exact ccwCycle_mem cyc0 2)
    (Finset.card_pair hd31_ne) y0 y1 hy0M hy1M hy01
    (fun q hq => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl; exact hd3_back; exact hd1_back_O1)
    (fun q hq => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hex_lift_hp hd2F hy0F hd3_hp
      · exact hex_lift_hp hy1F hd2F hd1_hp)
    h_cert_not_d31
    (fun z hz _hzD => ?_)
  have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
  have hz_nB : z ∉ B := (Finset.mem_sdiff.mp hzA).2
  have hz_ny0 : z ≠ y0 := fun h => (Finset.mem_sdiff.mp hz).2 (h ▸ Finset.mem_insert_self _ _)
  have hz_ny1 : z ≠ y1 := fun h => (Finset.mem_sdiff.mp hz).2 (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => hz_nB (hD_sub_B hd)⟩
  let cyc_disj := ccwCycle_shift cyc0 4
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc_disj.toFun i)
  have hpd0 : pD 0 = S d3 := rfl
  have hpd1 : pD 1 = S l := rfl
  have hpd2 : pD 2 = S r := rfl
  have hpd3 : pD 3 = S d1 := rfl
  have hpd4 : pD 4 = S d2 := rfl
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
    have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
      dsimp [D, B, H]; conv_rhs => rw [← cyc_disj.image_eq]
      ext p; simp [pD]
    rwa [hr]
  have hcov := convD_cover_case3b_disjoint_03 pD cyc_disj.ccw (S y0) (S y1) (F.image S : Set (ℝ × ℝ))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))
    (by rw [hpd1]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S hlF))
    (by rw [hpd2]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S hrF))
    (by rw [hpd4]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F)) hzD'
  rw [hpd0, hpd1, hpd2, hpd3, hpd4] at hcov
  rcases hcov with ((hF | hc1') | hc2') | (he1 | he2)
  · exact Or.inr hF
  · left
    refine hex_lift_hp hd2F hy0F (hd3_cap z (fun h => hz_nB (hD_sub_B (by rw [h]; exact ccwCycle_mem cyc0 3))) hz_ny0 ?_ ?_)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hz_nB (hD_sub_B (by rw [h]; exact ccwCycle_mem cyc0 3)), hz_ny0,
             fun h => hz_nB (hD_sub_B (by rw [h]; exact ccwCycle_mem cyc0 1))⟩
    · have heq : ({S d2, S d3, S y0} : Set (ℝ × ℝ)) = (({d3, d2, y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_image,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact ⟨d2, Or.inr (Or.inl rfl), rfl⟩
          · exact ⟨d3, Or.inl rfl, rfl⟩
          · exact ⟨y0, Or.inr (Or.inr rfl), rfl⟩
        · rintro ⟨x, rfl | rfl | rfl, rfl⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
      rwa [← heq]
  · left
    refine hex_lift_hp hy1F hd2F (hd1_cap z hz_ny1 (fun h => hz_nB (hD_sub_B (by rw [h]; exact ccwCycle_mem cyc0 3))) ?_ ?_)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hz_nB (hD_sub_B (by rw [h]; exact ccwCycle_mem cyc0 0)), hz_ny1,
             fun h => hz_nB (hD_sub_B (by rw [h]; exact ccwCycle_mem cyc0 3))⟩
    · have heq : ({S y1, S d1, S d2} : Set (ℝ × ℝ)) = (({d1, y1, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_image,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact ⟨y1, Or.inr (Or.inl rfl), rfl⟩
          · exact ⟨d1, Or.inl rfl, rfl⟩
          · exact ⟨d2, Or.inr (Or.inr rfl), rfl⟩
        · rintro ⟨x, rfl | rfl | rfl, rfl⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
      rwa [← heq]
  · exfalso
    exact hy0_empty z (Finset.mem_erase.mpr ⟨hz_ny0, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1)
  · exfalso
    exact hy1_empty z (Finset.mem_erase.mpr ⟨hz_ny1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he2)

private lemma opposite_endpoint_cy_targets {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (cycB : CCWCycle S (hullVertices S) 3)
    {h y0 : Fin n}
    (hhH : h ∈ certifiedVertices S w)
    (e_lh : IsCCWEdge S (hullVertices S) (cyc0.toFun 0) h)
    (e_hr : IsCCWEdge S (hullVertices S) h (cyc0.toFun 1))
    (hhB : h ∈ hullVertices S)
    (hr_d1_B : IsCCWEdge S (hullVertices S) (cyc0.toFun 1) (cyc0.toFun 2))
    (hd1_d2_B : IsCCWEdge S (hullVertices S) (cyc0.toFun 2) (cyc0.toFun 3))
    (hd2_d3_B : IsCCWEdge S (hullVertices S) (cyc0.toFun 3) (cyc0.toFun 4))
    (hB_card : (hullVertices S).card = 6) (hn3 : 3 ≤ n)
    (hB0 : cycB.toFun 0 = cyc0.toFun 4) (hB1 : cycB.toFun 1 = cyc0.toFun 0)
    (hB2 : cycB.toFun 2 = h) (hB3 : cycB.toFun 3 = cyc0.toFun 1)
    (hB4 : cycB.toFun 4 = cyc0.toFun 2) (hB5 : cycB.toFun 5 = cyc0.toFun 3)
    (hy0_A : y0 ∈ interiorPoints S)
    (hy0_nD : y0 ∉ hullVertices S \ certifiedVertices S w)
    (hy0_nH : y0 ∉ certifiedVertices S w)
    (hy0_W : ∀ x ∈ WitnessSet {cyc0.toFun 4, cyc0.toFun 0} ∅ w,
      InIntTri x (S (cyc0.toFun 4)) (S (cyc0.toFun 0)) (S y0))
    (hy0_orient : 0 < orient2D (S h) (S (cyc0.toFun 4)) (w (hullVertices S \ certifiedVertices S w)) ∧
      0 < orient2D (S h) (S (cyc0.toFun 4)) (S y0) ∧
      0 < orient2D (S (cyc0.toFun 4)) (S y0) (S (cyc0.toFun 1)) ∧
      0 < orient2D (S y0) (S h) (S (cyc0.toFun 1)))
    (hy0_in_d3lh : InIntTri (S (cyc0.toFun 4)) (S (cyc0.toFun 0)) (S h) (S y0))
    (hl_back_B : IsBackVertexOf S (hullVertices S) (cyc0.toFun 0)
      (w (Finset.univ \ {cyc0.toFun 3, y0, cyc0.toFun 1})))
    (hpart0_1 : InIntTri (w (Finset.univ \ {cyc0.toFun 3, y0, cyc0.toFun 1}))
      (S (cyc0.toFun 4)) (S (cyc0.toFun 0)) (S y0)) :
    let O0 : Finset (Fin n) := {cyc0.toFun 3, y0, cyc0.toFun 1}
    let v0 := w (Finset.univ \ O0)
    ∃ (p oa ob : Fin n),
      ((p = h ∧ oa = y0 ∧ ob = cyc0.toFun 1) ∨
       (p = cyc0.toFun 2 ∧ oa = cyc0.toFun 1 ∧ ob = cyc0.toFun 3) ∨
       (p = cyc0.toFun 4 ∧ oa = cyc0.toFun 3 ∧ ob = y0)) ∧
      GoodAnchorPair P S w O0 oa ob ∧
      SegmentsCross v0 (S p) (S oa) (S ob) ∧
      p ∉ O0 := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let l := cyc0.toFun 0
  let r := cyc0.toFun 1
  let d1 := cyc0.toFun 2
  let d2 := cyc0.toFun 3
  let d3 := cyc0.toFun 4
  let O0 : Finset (Fin n) := {d2, y0, r}
  let v0 := w (Finset.univ \ O0)
  have hD_sub_B : D ⊆ B := Finset.sdiff_subset
  have ho_d3lh : 0 < orient2D (S d3) (S l) (S h) := by
    have := cycB.ccw_tri 0 1 2 (by decide) (by decide); rwa [hB0, hB1, hB2] at this
  have ho_lhr : 0 < orient2D (S l) (S h) (S r) := by
    have := cycB.ccw_tri 1 2 3 (by decide) (by decide); rwa [hB1, hB2, hB3] at this
  obtain ⟨ho_d3ly0, ho_lhy0, _⟩ := (inIntTri_iff_orient_pos ho_d3lh).mp hy0_in_d3lh
  let cyFun : Fin 6 → Fin n := ![h, r, d1, d2, d3, y0]
  have hcy_lt4 : ∀ (m : Fin 6) (hm : m.val < 4), cyFun m = cycB.toFun ⟨m.val + 2, by omega⟩ := by
    intro m hm
    fin_cases m <;> simp at hm <;> simp [cyFun, hB2, hB3, hB4, hB5, r, d1, d2, d3]
  have hcy_inj : Function.Injective cyFun := by
    let idxB : Fin 5 → Fin 6 := ![2, 3, 4, 5, 0]
    have hidx_inj : Function.Injective idxB := by decide
    have hcy_B : ∀ m : Fin 5, cyFun ⟨m.val, by omega⟩ = cycB.toFun (idxB m) := by
      intro m; fin_cases m <;> simp [cyFun, idxB, hB0, hB2, hB3, hB4, hB5, r, d1, d2, d3]
    intro a b hab
    by_cases ha5 : a.val = 5 <;> by_cases hb5 : b.val = 5
    · exact Fin.ext (ha5.trans hb5.symm)
    · exfalso
      have hae : a = 5 := Fin.ext ha5
      have hb_eq : cyFun b = cycB.toFun (idxB ⟨b.val, by omega⟩) := by
        simpa [Fin.eta] using hcy_B ⟨b.val, by omega⟩
      have h1 : cyFun a = y0 := by rw [hae]; rfl
      rw [h1, hb_eq] at hab
      exact (Finset.mem_sdiff.mp hy0_A).2 (hab ▸ ccwCycle_mem cycB _)
    · exfalso
      have hbe : b = 5 := Fin.ext hb5
      have ha_eq : cyFun a = cycB.toFun (idxB ⟨a.val, by omega⟩) := by
        simpa [Fin.eta] using hcy_B ⟨a.val, by omega⟩
      have h1 : cyFun b = y0 := by rw [hbe]; rfl
      rw [h1, ha_eq] at hab
      exact (Finset.mem_sdiff.mp hy0_A).2 (hab.symm ▸ ccwCycle_mem cycB _)
    · have ha' := hcy_B ⟨a.val, by omega⟩
      have hb' := hcy_B ⟨b.val, by omega⟩
      simp only [Fin.eta] at ha' hb'
      rw [ha', hb'] at hab
      have heq := congrArg Fin.val (hidx_inj (cycB.inj hab))
      exact Fin.ext (by dsimp at heq; exact heq)
  have hcy_tri : ∀ i j k : Fin 6, i < j → j < k →
      0 < orient2D (S (cyFun i)) (S (cyFun j)) (S (cyFun k)) := by
    obtain ⟨t1, t2, t3, ht1, ht2, ht3, htsum, hy_t1, hy_t2⟩ := hy0_in_d3lh
    have h_rest : ∀ x : Fin n, x = r ∨ x = d1 ∨ x = d2 →
        0 < orient2D (S d3) (S y0) (S x) ∧ 0 < orient2D (S y0) (S h) (S x) := by
      intro x hx
      refine opposite_endpoint_hexagon_convex_step (S d3) (S l) (S h) (S y0) (S x) t1 t2 t3
        ht1 ht2 ht3 htsum hy_t1 hy_t2 ?_ ?_ ?_
      · rcases hx with rfl | rfl | rfl
        · have := cycB.ccw_tri 0 1 3 (by decide) (by decide); rwa [hB0, hB1, hB3] at this
        · have := cycB.ccw_tri 0 1 4 (by decide) (by decide); rwa [hB0, hB1, hB4] at this
        · have := cycB.ccw_tri 0 1 5 (by decide) (by decide); rwa [hB0, hB1, hB5] at this
      · rcases hx with rfl | rfl | rfl
        · have := cycB.ccw_tri 0 2 3 (by decide) (by decide); rwa [hB0, hB2, hB3] at this
        · have := cycB.ccw_tri 0 2 4 (by decide) (by decide); rwa [hB0, hB2, hB4] at this
        · have := cycB.ccw_tri 0 2 5 (by decide) (by decide); rwa [hB0, hB2, hB5] at this
      · rcases hx with rfl | rfl | rfl
        · have := cycB.ccw_tri 1 2 3 (by decide) (by decide); rwa [hB1, hB2, hB3] at this
        · have := cycB.ccw_tri 1 2 4 (by decide) (by decide); rwa [hB1, hB2, hB4] at this
        · have := cycB.ccw_tri 1 2 5 (by decide) (by decide); rwa [hB1, hB2, hB5] at this
    have h_ab_y0 : ∀ ia ib : Fin 6, 2 ≤ ia.val → ia < ib →
        0 < orient2D (S (cycB.toFun ia)) (S (cycB.toFun ib)) (S y0) := by
      intro ia ib hia hlt
      have h1 : 0 ≤ orient2D (S (cycB.toFun ia)) (S (cycB.toFun ib)) (S d3) := by
        dsimp [d3]; rw [← hB0]
        by_cases h0a : (0 : Fin 6) = ia
        · omega
        · have := cycB.ccw_tri 0 ia ib (Fin.pos_of_ne_zero (Ne.symm h0a)) hlt
          unfold orient2D at this ⊢; linarith
      have h2 : 0 < orient2D (S (cycB.toFun ia)) (S (cycB.toFun ib)) (S l) := by
        dsimp [l]; rw [← hB1]
        have h1a : (1 : Fin 6) < ia := by omega
        have := cycB.ccw_tri 1 ia ib h1a hlt
        unfold orient2D at this ⊢; linarith
      have h3 : 0 ≤ orient2D (S (cycB.toFun ia)) (S (cycB.toFun ib)) (S h) := by
        rw [← hB2]
        by_cases h2a : (2 : Fin 6) = ia
        · rw [← h2a, orient2D_self_outer]
        · have h2a' : (2 : Fin 6) < ia := by omega
          have := cycB.ccw_tri 2 ia ib h2a' hlt
          unfold orient2D at this ⊢; linarith
      have hid := orient2D_convex_comb3 (S (cycB.toFun ia)) (S (cycB.toFun ib)) (S d3) (S l) (S h) (S y0)
        t1 t2 t3 htsum hy_t1 hy_t2
      rw [hid]; nlinarith
    intro i j k hij hjk
    by_cases hk5 : k.val = 5
    · have hk_eq : k = 5 := Fin.ext hk5
      rw [hk_eq, show cyFun 5 = y0 from rfl]
      by_cases hj4 : j.val = 4
      · have hj_eq : j = 4 := Fin.ext hj4
        rw [hj_eq, show cyFun 4 = d3 from rfl]
        have hi4 : i.val < 4 := by omega
        fin_cases i <;> simp at hi4
        · change 0 < orient2D (S h) (S d3) (S y0); exact hy0_orient.2.1
        · change 0 < orient2D (S r) (S d3) (S y0)
          have ht := (h_rest r (Or.inl rfl)).1; unfold orient2D at ht ⊢; linarith only [ht]
        · change 0 < orient2D (S d1) (S d3) (S y0)
          have ht := (h_rest d1 (Or.inr (Or.inl rfl))).1; unfold orient2D at ht ⊢; linarith only [ht]
        · change 0 < orient2D (S d2) (S d3) (S y0)
          have ht := (h_rest d2 (Or.inr (Or.inr rfl))).1; unfold orient2D at ht ⊢; linarith only [ht]
      · rw [hcy_lt4 i (by omega), hcy_lt4 j (by omega)]
        have hi2 : 2 ≤ (⟨i.val + 2, by omega⟩ : Fin 6).val := by dsimp; omega
        exact h_ab_y0 ⟨i.val + 2, by omega⟩ ⟨j.val + 2, by omega⟩ hi2 (Fin.mk_lt_mk.mpr (by omega))
    · by_cases hk4 : k.val = 4
      · have hk_eq : k = 4 := Fin.ext hk4
        rw [hk_eq, show cyFun 4 = cyc0.toFun 4 from rfl, ← hB0, hcy_lt4 i (by omega), hcy_lt4 j (by omega)]
        have h0lt : (0 : Fin 6) < ⟨i.val + 2, by omega⟩ := Fin.mk_lt_mk.mpr (by dsimp; omega)
        have hij_lt : (⟨i.val + 2, by omega⟩ : Fin 6) < ⟨j.val + 2, by omega⟩ :=
          Fin.mk_lt_mk.mpr (by omega)
        have ht := cycB.ccw_tri 0 ⟨i.val + 2, by omega⟩ ⟨j.val + 2, by omega⟩ h0lt hij_lt
        unfold orient2D at ht ⊢; linarith only [ht]
      · rw [hcy_lt4 i (by omega), hcy_lt4 j (by omega), hcy_lt4 k (by omega)]
        exact cycB.ccw_tri _ _ _ (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
  have hcy_ccw : StrictConvexCCWPoly (S ∘ cyFun) := by
    intro i j hji hj1
    dsimp [Function.comp]
    by_cases hi5 : i.val = 5
    · have hi_eq : i = 5 := Fin.ext hi5
      rw [hi_eq]
      have hi1_eq : (5 + 1 : Fin 6) = 0 := by decide
      rw [hi1_eq]
      have hj0 : (0 : Fin 6) < j := Fin.pos_of_ne_zero (fun h => hj1 (h.trans (by rw [hi_eq]; exact hi1_eq.symm)))
      have hj5 : j < 5 := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (fun h => hji (h.trans hi_eq.symm))
      have ht := hcy_tri 0 j 5 hj0 hj5
      unfold orient2D at ht ⊢; linarith only [ht]
    · have hi1_val : (i + 1).val = i.val + 1 := by
        change (i.val + 1) % 6 = i.val + 1; exact Nat.mod_eq_of_lt (by omega)
      rcases lt_trichotomy j i with hji_lt | hji_eq | hij_lt
      · have ht := hcy_tri j i (i + 1) hji_lt (Fin.lt_def.mpr (by rw [hi1_val]; omega))
        unfold orient2D at ht ⊢; linarith only [ht]
      · exact False.elim (hji hji_eq)
      · have hi1j : i + 1 < j := lt_of_le_of_ne (Fin.le_def.mpr (by rw [hi1_val]; omega)) (Ne.symm hj1)
        exact hcy_tri i (i + 1) j (Fin.lt_def.mpr (by rw [hi1_val]; omega)) hi1j
  let Cy : Finset (Fin n) := Finset.univ.image cyFun
  let cycCy : CCWCycle S Cy 3 := ⟨cyFun, hcy_inj, rfl, hcy_ccw, hcy_tri⟩
  have hCy_odd : ∀ i : Fin 6, i.val % 2 = 1 → cycCy.toFun i ∈ O0 := by
    intro i hi
    fin_cases i <;> simp at hi ⊢ <;> simp [cycCy, cyFun, O0]
  have hCy_even : ∀ i : Fin 6, i.val % 2 = 0 → cycCy.toFun i ∉ O0 := by
    intro i hi hmem
    fin_cases i <;> simp at hi <;> simp only [cycCy, cyFun, O0, Finset.mem_insert, Finset.mem_singleton] at hmem
    · rcases hmem with e | e | e
      · exact (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 3)).2 (by rw [show cyc0.toFun 3 = d2 from rfl, ← e]; exact hhH)
      · exact hy0_nH (e ▸ hhH)
      · exact (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 1)).2 (by rw [show cyc0.toFun 1 = r from rfl, ← e]; exact hhH)
    · rcases hmem with e | e | e
      · exact cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3) e
      · exact hy0_nD (e ▸ ccwCycle_mem cyc0 2)
      · exact cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1) e
    · rcases hmem with e | e | e
      · exact cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3) e
      · exact hy0_nD (e ▸ ccwCycle_mem cyc0 4)
      · exact cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1) e
  have hd3_y0_v0 : 0 < orient2D (S d3) (S y0) v0 := by
    have hl_in_Tv0 : l ∈ Finset.univ \ O0 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 0),
             cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)⟩⟩
    have hd3_in_Tv0 : d3 ∈ Finset.univ \ O0 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 4),
             cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1)⟩⟩
    have hv0_tri : InIntTri v0 (S d3) (S l) (S y0) := hy0_W v0 ⟨Finset.univ \ O0, fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption, Finset.disjoint_empty_right _, rfl⟩
    have hd3lv0 : 0 < orient2D (S d3) (S l) v0 := by
      rcases hpart0_1 with ⟨μ₁, _, _, hm1, _, _, hs, hy1, hy2⟩
      have hid := orient2D_convex_comb3 (S d3) (S l) v0 (S d3) (S l) (S y0) _ _ _ hs hy1 hy2
      rw [orient2D_self_outer, orient2D_self_right, mul_zero, mul_zero, add_zero, add_zero] at hid
      nlinarith
    have hc : 0 < orient2D v0 (S d3) (S l) := by unfold orient2D at hd3lv0 ⊢; linarith
    have := (inIntTri_iff_orient_pos hc).mp hv0_tri
    have hpos := this.1; unfold orient2D at hpos ⊢; linarith
  have hCy_odd_nf : ∀ i : Fin 6, i.val % 2 = 1 → ¬ IsFrontVertexOf S Cy (cycCy.toFun i) v0 := by
    intro i hi hf
    have hB_ge3 : 3 ≤ B.card := by change B.card = 6 at hB_card; omega
    have hlt6 : i.val < 6 := i.isLt
    rcases (by omega : i.val = 1 ∨ i.val = 3 ∨ i.val = 5) with hi1 | hi3 | hi5
    · have hi_eq : i = 1 := Fin.ext hi1; rw [hi_eq] at hf
      change IsFrontVertexOf S Cy (cycCy.toFun 1) v0 at hf
      rw [isFrontVertexOf_iff_ccwCycle cycCy 1 v0] at hf
      have : IsFrontVertexOf S {h, r, d1} r v0 := by
        refine ⟨by simp, fun a b hab hor => ?_⟩
        rcases hor with rfl | rfl
        · have hb_or : b = h ∨ b = d1 := by
            have hb := hab.2.1; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (hab.2.2.1 rfl)
            · exact Or.inr rfl
          rcases hb_or with rfl | rfl
          · exfalso
            have h1 := hab.2.2.2 d1 (by simp)
              (fun e => cycB.inj.ne (by decide : (4 : Fin 6) ≠ 3) (by rw [hB4, hB3]; exact e))
              (fun e => cycB.inj.ne (by decide : (4 : Fin 6) ≠ 2) (by rw [hB4, hB2]; exact e))
            have h2 := cycB.ccw_tri 2 3 4 (by decide) (by decide)
            rw [hB2, hB3, hB4] at h2; unfold orient2D at h1 h2; linarith
          · exact hf.2
        · have ha_or : a = h ∨ a = d1 := by
            have ha := hab.1; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (hab.2.2.1 rfl)
            · exact Or.inr rfl
          rcases ha_or with rfl | rfl
          · exact hf.1
          · exfalso
            have h1 := hab.2.2.2 h (by simp)
              (fun e => cycB.inj.ne (by decide : (2 : Fin 6) ≠ 4) (by rw [hB2, hB4]; exact e))
              (fun e => cycB.inj.ne (by decide : (2 : Fin 6) ≠ 3) (by rw [hB2, hB3]; exact e))
            have h2 := cycB.ccw_tri 2 3 4 (by decide) (by decide)
            rw [hB2, hB3, hB4] at h2; unfold orient2D at h1 h2; linarith
      have hfB := h25.front_restoration {h, r, d1} B r v0 (fun x hx => by
        simp at hx; rcases hx with rfl | rfl | rfl
        · exact hhB
        · exact hD_sub_B (ccwCycle_mem cyc0 1)
        · exact hD_sub_B (ccwCycle_mem cyc0 2)) (hullVertices_convexPos S Subset.rfl)
        (by
          have hr_nd1 : r ∉ ({d1} : Finset (Fin n)) := by
            simp only [Finset.mem_singleton]
            exact fun e => cycB.inj.ne (by decide : (3 : Fin 6) ≠ 4) (by rw [hB3, hB4]; exact e)
          have hh_nrd1 : h ∉ ({r, d1} : Finset (Fin n)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun e => cycB.inj.ne (by decide : (2 : Fin 6) ≠ 3) (by rw [hB2, hB3]; exact e),
                   fun e => cycB.inj.ne (by decide : (2 : Fin 6) ≠ 4) (by rw [hB2, hB4]; exact e)⟩
          rw [Finset.card_insert_of_notMem hh_nrd1, Finset.card_insert_of_notMem hr_nd1, Finset.card_singleton])
        (Set.mem_range_self _) this
      exact nonfront_hullVertices_of_nbrs_seen hPoly h25 hn3 (ccwCycle_mem cyc0 1)
        (fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
        (fun x hx hadj => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          rcases hadj with e | e
          · rw [isCCWEdge_unique_pred cycB e e_hr]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun e => (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 3)).2 (by rw [show cyc0.toFun 3 = d2 from rfl, ← e]; exact hhH),
                   fun e => hy0_nH (e ▸ hhH),
                   fun e => (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 1)).2 (by change cyc0.toFun 1 ∈ H; rw [← e]; exact hhH)⟩
          · rw [isCCWEdge_unique_succ cycB e hr_d1_B]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 2),
                   cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1)⟩⟩) hfB
    · have hi_eq : i = 3 := Fin.ext hi3; rw [hi_eq] at hf
      change IsFrontVertexOf S Cy (cycCy.toFun 3) v0 at hf
      rw [isFrontVertexOf_iff_ccwCycle cycCy 3 v0] at hf
      have hB_d2 : IsFrontVertexOf S {d1, d2, d3} d2 v0 := by
        refine ⟨by simp, fun a b hab hor => ?_⟩
        rcases hor with rfl | rfl
        · have hb_or : b = d1 ∨ b = d3 := by
            have hb := hab.2.1; simp only [Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (hab.2.2.1 rfl)
            · exact Or.inr rfl
          rcases hb_or with rfl | rfl
          · exfalso
            have h1 := hab.2.2.2 d3 (by simp) (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3)) (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 2))
            have h2 := cyc0.ccw_tri 2 3 4 (by decide) (by decide)
            unfold orient2D at h1 h2; linarith
          · exact hf.2
        · have ha_or : a = d1 ∨ a = d3 := by
            have ha := hab.1; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl | rfl
            · exact Or.inl rfl
            · exact False.elim (hab.2.2.1 rfl)
            · exact Or.inr rfl
          rcases ha_or with rfl | rfl
          · exact hf.1
          · exfalso
            have h1 := hab.2.2.2 d1 (by simp) (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 4)) (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3))
            have h2 := cyc0.ccw_tri 2 3 4 (by decide) (by decide)
            unfold orient2D at h1 h2; linarith
      have hfB := h25.front_restoration {d1, d2, d3} B d2 v0 (fun x hx => by
        simp at hx; rcases hx with rfl | rfl | rfl <;> exact hD_sub_B (ccwCycle_mem cyc0 _))
        (hullVertices_convexPos S Subset.rfl)
        (by
          have hd2_nd3 : d2 ∉ ({d3} : Finset (Fin n)) := by
            simp only [Finset.mem_singleton]
            exact cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 4)
          have hd1_n23 : d1 ∉ ({d2, d3} : Finset (Fin n)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3), cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 4)⟩
          rw [Finset.card_insert_of_notMem hd1_n23, Finset.card_insert_of_notMem hd2_nd3, Finset.card_singleton])
        (Set.mem_range_self _) hB_d2
      exact nonfront_hullVertices_of_nbrs_seen hPoly h25 hn3 (ccwCycle_mem cyc0 3)
        (fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_self _ _))
        (fun x hx hadj => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          rcases hadj with e | e
          · rw [isCCWEdge_unique_pred cycB e hd1_d2_B]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 2),
                   cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1)⟩
          · rw [isCCWEdge_unique_succ cycB e hd2_d3_B]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 4),
                   cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1)⟩⟩) hfB
    · have hi_eq : i = 5 := Fin.ext hi5; rw [hi_eq] at hf
      change IsFrontVertexOf S Cy (cycCy.toFun 5) v0 at hf
      rw [isFrontVertexOf_iff_ccwCycle cycCy 5 v0] at hf
      have hf1 : orient2D (S d3) (S y0) v0 < 0 := by simpa [cycCy, cyFun] using hf.1
      linarith
  have hCy_no_cert : ¬ ∃ (io_min io_star ig : Fin 6),
      io_min.val % 2 = 1 ∧ io_star.val % 2 = 1 ∧ ig.val % 2 = 0 ∧
      ((io_star + 1 = ig ∧ ig + 1 = io_min) ∨ (io_min + 1 = ig ∧ ig + 1 = io_star)) ∧
      ¬ Sees P v0 (w Finset.univ) ∧
      IsFrontVertexOf S Cy (cycCy.toFun ig) v0 ∧
      InIntTri (w Finset.univ) (S (cycCy.toFun io_min)) (S (cycCy.toFun io_star)) v0 := by
    rintro ⟨io_min, io_star, ig, hm, hs, hig, hadj, hsee, hf, htri⟩
    have hlt6 : ig.val < 6 := ig.isLt
    rcases (by omega : ig.val = 0 ∨ ig.val = 2 ∨ ig.val = 4) with hig0 | hig2 | hig4
    · have hig_eq : ig = 0 := Fin.ext hig0; rw [hig_eq] at hf
      change IsFrontVertexOf S Cy (cycCy.toFun 0) v0 at hf
      rw [isFrontVertexOf_iff_ccwCycle cycCy 0 v0] at hf
      have hf1 : orient2D (S y0) (S h) v0 < 0 := by simpa [cycCy, cyFun] using hf.1
      have hf2 : orient2D (S h) (S r) v0 < 0 := by simpa [cycCy, cyFun] using hf.2
      have hlhv : 0 < orient2D (S l) (S h) v0 := hl_back_B.2 l h e_lh (Or.inl rfl)
      have hid : orient2D (S y0) (S h) (S r) * orient2D (S l) (S h) v0 =
          orient2D (S l) (S h) (S r) * orient2D (S y0) (S h) v0 +
          orient2D (S l) (S h) (S y0) * orient2D (S h) (S r) v0 := by
        unfold orient2D; ring
      nlinarith [hy0_orient.2.2.2, ho_lhr, ho_lhy0]
    · have hig_eq : ig = 2 := Fin.ext hig2; rw [hig_eq] at hf hadj
      have hB_ge3 : 3 ≤ B.card := by change B.card = 6 at hB_card; omega
      change IsFrontVertexOf S Cy (cycCy.toFun 2) v0 at hf
      rw [isFrontVertexOf_iff_ccwCycle cycCy 2 v0] at hf
      have hf1 : orient2D (S r) (S d1) v0 < 0 := by simpa [cycCy, cyFun] using hf.1
      have hf2 : orient2D (S d1) (S d2) v0 < 0 := by simpa [cycCy, cyFun] using hf.2
      have hccw : 0 < orient2D (S d1) (S d2) (S r) := by
        have := cyc0.ccw_tri 1 2 3 (by decide) (by decide); unfold orient2D at this ⊢; linarith
      have hccw_v : 0 < orient2D v0 (S d2) (S r) := by
        have hid := orient2D_barycentric_sum (S d1) (S d2) (S r) v0
        unfold orient2D at hid hf1 hf2 hccw ⊢; linarith only [hid, hf1, hf2, hccw]
      have hd1_tri' : InIntTri v0 (S d2) (S r) (S d1) :=
        (inIntTri_iff_orient_pos hccw_v).mpr
          ⟨by unfold orient2D at hf2 ⊢; linarith only [hf2],
           by unfold orient2D at hccw ⊢; linarith only [hccw],
           by unfold orient2D at hf1 ⊢; linarith only [hf1]⟩
      have hd1_tri : InIntTri v0 (S r) (S d2) (S d1) := hd1_tri'.symm23
      have hq_tri : InIntTri (w Finset.univ) (S r) (S d2) v0 := by
        rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hs' : io_star = 1 := by
            have := congrArg (· - 1) h1; simpa using this
          have hm' : io_min = 3 := by rw [← h2]; decide
          rw [hs', hm'] at htri
          rcases htri with ⟨a1, a2, a3, h1', h2', h3', hs'', e1, e2⟩
          exact ⟨a1, a3, a2, h1', h3', h2', by linarith only [hs''],
            by dsimp [cycCy, cyFun] at e1 ⊢; linarith only [e1],
            by dsimp [cycCy, cyFun] at e2 ⊢; linarith only [e2]⟩
        · have hm' : io_min = 1 := by
            have := congrArg (· - 1) h1; simpa using this
          have hs' : io_star = 3 := by rw [← h2]; decide
          rw [hs', hm'] at htri
          simpa [cycCy, cyFun] using htri
      exact contradict_cert_even_front hPoly h25 (ccwCycle_mem cyc0 2) (hD_sub_B (ccwCycle_mem cyc0 1))
        (hD_sub_B (ccwCycle_mem cyc0 3)) (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2))
        (cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 2)) (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 3))
        (by simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 2),
                   cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1)⟩)
        hsee hd1_tri hq_tri
    · have hig_eq : ig = 4 := Fin.ext hig4; rw [hig_eq] at hf
      change IsFrontVertexOf S Cy (cycCy.toFun 4) v0 at hf
      rw [isFrontVertexOf_iff_ccwCycle cycCy 4 v0] at hf
      have hf2 : orient2D (S d3) (S y0) v0 < 0 := by simpa [cycCy, cyFun] using hf.2
      linarith only [hf2, hd3_y0_v0]
  obtain ⟨Tgt, hTgt_card, hTgt⟩ := good_targets_core hPoly (Or.inl rfl) cycCy hCy_odd hCy_even hCy_odd_nf hCy_no_cert
  rw [if_pos rfl] at hTgt_card
  obtain ⟨ig, hig_mem⟩ := Finset.card_pos.mp (by omega : 0 < Tgt.card)
  obtain ⟨_, _, hig_gap, hig_orient⟩ := hTgt ig hig_mem
  have hlt : ig.val < 6 := ig.isLt
  rcases (by omega : ig.val = 0 ∨ ig.val = 2 ∨ ig.val = 4) with h0 | h2 | h4
  · have hig_eq : ig = 0 := Fin.ext h0; rw [hig_eq] at hig_gap hig_orient
    exact ⟨h, y0, r, Or.inl ⟨rfl, rfl, rfl⟩,
      by simpa [cycCy, cyFun] using hig_gap,
      segmentsCross_of_angleLt (by simpa [cycCy, cyFun] using hig_orient),
      hCy_even 0 (by decide)⟩
  · have hig_eq : ig = 2 := Fin.ext h2; rw [hig_eq] at hig_gap hig_orient
    exact ⟨d1, r, d2, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
      by simpa [cycCy, cyFun] using hig_gap,
      segmentsCross_of_angleLt (by simpa [cycCy, cyFun] using hig_orient),
      hCy_even 2 (by decide)⟩
  · have hig_eq : ig = 4 := Fin.ext h4; rw [hig_eq] at hig_gap hig_orient
    exact ⟨d3, d2, y0, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩),
      by simpa [cycCy, cyFun] using hig_gap,
      segmentsCross_of_angleLt (by simpa [cycCy, cyFun] using hig_orient),
      hCy_even 4 (by decide)⟩

/-- Right-handed **Proposition 8.5 (`opposite-endpoint-exit`, `upper_9.tex` lines 969–999)**:
    When `|D| = 5`, `|M| = 5`, `H ≠ ∅` with certified edge `lr = (cycD il, cycD (il + 1))`,
    `e(H) = {r d1}` (`(il + 1, il + 2)`), and `e⁻¹(d3 l) ≠ ∅` (`(il + 4, il)`), gives `False`. -/
theorem opposite_endpoint_exit_right {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (il : Fin 5)
    (hHne : (certifiedVertices S w).Nonempty)
    (hlr_neg : ∀ h ∈ certifiedVertices S w,
      orient2D (S (cycD.toFun il)) (S (cycD.toFun (il + 1))) (S h) < 0)
    (hH_r_d1 : ∀ h ∈ certifiedVertices S w,
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S h) ∧
      ∀ x ∈ WitnessSet {cycD.toFun (il + 1), cycD.toFun (il + 2)} ∅ w,
        InIntTri x (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S h))
    (he_d3l : ∃ y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 4))) (S (cycD.toFun il)) (S y0)) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let cyc0 := ccwCycle_shift cycD il
  have hc0 : cyc0.toFun 0 = cycD.toFun il := by dsimp [cyc0, ccwCycle_shift]; simp
  have hc1 : cyc0.toFun 1 = cycD.toFun (il + 1) := rfl
  have hc2 : cyc0.toFun 2 = cycD.toFun (il + 2) := rfl
  have hc3 : cyc0.toFun 3 = cycD.toFun (il + 3) := rfl
  have hc4 : cyc0.toFun 4 = cycD.toFun (il + 4) := rfl
  let l := cyc0.toFun 0
  let r := cyc0.toFun 1
  let d1 := cyc0.toFun 2
  let d2 := cyc0.toFun 3
  let d3 := cyc0.toFun 4
  have hH_sub_B : H ⊆ B := fun x hx => (Finset.mem_filter.mp hx).1
  have hD_sub_B : D ⊆ B := Finset.sdiff_subset
  have hD3 : 3 ≤ D.card := by change 3 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  obtain ⟨l0, r0, hl0D, hr0D, hl0r0_ne, hed0', hH_neg0, hD_pos0, hH_Tri0, h_edges0, hH1, hH2⟩ :=
    h25.certified_structure.2 hHne
  have hed0 := hed0' hD3
  have hlreq : l = l0 ∧ r = r0 :=
    certified_edge_unique_of_neg hPoly h25 hHne hD3 (ccwCycle_isCCWEdge cyc0 0)
      (by simpa [l, r, hc0, hc1] using hlr_neg) hed0 hl0D hr0D hl0r0_ne h_edges0
  obtain ⟨hl_eq, hr_eq⟩ := hlreq
  have hH_neg : ∀ h ∈ H, orient2D (S l) (S r) (S h) < 0 := by simpa [l, r, hc0, hc1] using hlr_neg
  have h_not_lr : ∀ la ra : Fin n, H.Nonempty → IsCCWEdge S D la ra →
      (∀ h ∈ H, orient2D (S la) (S ra) (S h) < 0) →
      (d3, l) ≠ (la, ra) ∧ (r, d1) ≠ (la, ra) := by
    intro la ra hH' hed_la hneg_la
    have heq := certified_edge_unique_of_neg hPoly h25 hH' hD3 hed_la hneg_la
      (ccwCycle_isCCWEdge cyc0 0) (ccwCycle_mem cyc0 0) (ccwCycle_mem cyc0 1)
      (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)) (fun d hd hl' hr' x hx => by
        have h_ed := h_edges0 d hd
        rw [← hl_eq] at h_ed; rw [← hr_eq] at h_ed
        exact h_ed hl' hr' x hx)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' := congrArg Prod.fst h; exact (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 0)) (h'.trans heq.1)
    · have h' := congrArg Prod.fst h; exact (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 0)) (h'.trans heq.1)
  have h_edges : ∀ d ∈ D, d ≠ l → d ≠ r → ∀ x ∈ B,
      (IsCCWEdge S B x d ↔ IsCCWEdge S D x d) ∧ (IsCCWEdge S B d x ↔ IsCCWEdge S D d x) := by
    intro d hd hdl hdr x hx
    have h_ed := h_edges0 d hd
    rw [← hl_eq] at h_ed; rw [← hr_eq] at h_ed
    exact h_ed hdl hdr x hx
  have he_d3l' : ∃ y ∈ M, InIntTri (w D) (S d3) (S l) (S y) := by
    simpa [M, D, B, H, d3, l, hc0, hc4] using he_d3l
  let S_d3l := M.filter (fun y => InIntTri (w D) (S d3) (S l) (S y))
  have hSd3l_ne : S_d3l.Nonempty := by
    obtain ⟨y, hyM, hy_tri⟩ := he_d3l'; exact ⟨y, Finset.mem_filter.mpr ⟨hyM, hy_tri⟩⟩
  obtain ⟨y0, hy0_fil, hy0_min⟩ := Finset.exists_min_image S_d3l (fun y => orient2D (S d3) (S l) (S y)) hSd3l_ne
  have hy0M : y0 ∈ M := (Finset.mem_filter.mp hy0_fil).1
  have hy0_tri : InIntTri (w D) (S d3) (S l) (S y0) := (Finset.mem_filter.mp hy0_fil).2
  have hy0_min' : ∀ y ∈ M, InIntTri (w D) (S d3) (S l) (S y) → orient2D (S d3) (S l) (S y0) ≤ orient2D (S d3) (S l) (S y) :=
    fun y hyM hy_t => hy0_min y (Finset.mem_filter.mpr ⟨hyM, hy_t⟩)
  have hy0_nD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hd3l_pos : 0 < orient2D (S d3) (S l) (w D) :=
    pentagon_exit_nonfacing_local hPoly h25 rfl cyc0 hy0M 4
      (by simpa [d3, l] using hy0_tri) (fun la ra hH' hed_la hneg_la => (h_not_lr la ra hH' hed_la hneg_la).1)
  have hr1_pos : 0 < orient2D (S r) (S d1) (w D) := by
    obtain ⟨h0, hh0⟩ := hHne
    have hh0M : h0 ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh0⟩
    exact pentagon_exit_nonfacing_local hPoly h25 rfl cyc0 hh0M 1
      (by simpa [r, d1, hc1, hc2] using (hH_r_d1 h0 hh0).1)
      (fun la ra hH' hed_la hneg_la => (h_not_lr la ra hH' hed_la hneg_la).2)
  have hy0_nH : y0 ∉ H := by
    intro hy0H
    obtain ⟨u, v, _, _, _, _, _, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
    have h1 := h_uniq d3 l (by simpa [d3, l] using ccwCycle_isCCWEdge cyc0 4) hd3l_pos hy0_tri.to_convexHull
    have hhy0_ch := (hH_r_d1 y0 hy0H).1.to_convexHull
    have h2 := h_uniq r d1 (ccwCycle_isCCWEdge cyc0 1) hr1_pos (by simpa [r, d1, hc1, hc2] using hhy0_ch)
    exact (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1)) (h1.1.trans h2.1.symm)
  have hy0_A : y0 ∈ interiorPoints S := by
    have := hy0M; change y0 ∈ Finset.univ \ D at this; rw [M_eq_interior_union_H S w] at this
    exact (Finset.mem_union.mp this).resolve_right hy0_nH
  have hy0_W : ∀ x ∈ WitnessSet {d3, l} ∅ w, InIntTri x (S d3) (S l) (S y0) := by
    obtain ⟨u, v, _, _, _, _, hW, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
    have h1 := h_uniq d3 l (by simpa [d3, l] using ccwCycle_isCCWEdge cyc0 4) hd3l_pos hy0_tri.to_convexHull
    rw [← h1.1, ← h1.2] at hW; exact hW
  let S_rd1 := M.filter (fun y => InIntTri (w D) (S r) (S d1) (S y))
  have hSrd1_ne : S_rd1.Nonempty := by
    obtain ⟨h0, hh0⟩ := hHne
    have hh0M : h0 ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh0⟩
    exact ⟨h0, Finset.mem_filter.mpr ⟨hh0M, by simpa [r, d1, hc1, hc2] using (hH_r_d1 h0 hh0).1⟩⟩
  obtain ⟨y1, hy1_fil, hy1_min⟩ := Finset.exists_min_image S_rd1 (fun y => orient2D (S r) (S d1) (S y)) hSrd1_ne
  have hy1M : y1 ∈ M := (Finset.mem_filter.mp hy1_fil).1
  have hy1_tri : InIntTri (w D) (S r) (S d1) (S y1) := (Finset.mem_filter.mp hy1_fil).2
  have hy1_min' : ∀ y ∈ M, InIntTri (w D) (S r) (S d1) (S y) → orient2D (S r) (S d1) (S y1) ≤ orient2D (S r) (S d1) (S y) :=
    fun y hyM hy_t => hy1_min y (Finset.mem_filter.mpr ⟨hyM, hy_t⟩)
  have hy1_nD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have hy1_W : ∀ x ∈ WitnessSet {r, d1} ∅ w, InIntTri x (S r) (S d1) (S y1) := by
    obtain ⟨u, v, _, _, _, _, hW, h_uniq⟩ := h25.exit_edge_lemma hD3 y1 hy1M
    have h1 := h_uniq r d1 (ccwCycle_isCCWEdge cyc0 1) hr1_pos hy1_tri.to_convexHull
    rw [← h1.1, ← h1.2] at hW; exact hW
  have hy01 : y0 ≠ y1 := by
    intro h; subst h
    obtain ⟨u, v, _, _, _, _, _, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
    have h1 := h_uniq d3 l (by simpa [d3, l] using ccwCycle_isCCWEdge cyc0 4) hd3l_pos hy0_tri.to_convexHull
    have h2 := h_uniq r d1 (ccwCycle_isCCWEdge cyc0 1) hr1_pos hy1_tri.to_convexHull
    exact (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1)) (h1.1.trans h2.1.symm)
  have hy0_empty : ∀ z ∈ M.erase y0, ¬ InClosedTri (S d3) (S l) (S y0) (S z) :=
    exit_minimal_empty hPoly h25 hD3 (by simpa [d3, l] using ccwCycle_isCCWEdge cyc0 4) hd3l_pos hy0_tri hy0_min'
  have hy1_empty : ∀ z ∈ M.erase y1, ¬ InClosedTri (S r) (S d1) (S y1) (S z) :=
    exit_minimal_empty hPoly h25 hD3 (ccwCycle_isCCWEdge cyc0 1) hr1_pos hy1_tri hy1_min'
  have hO1_res := pentagon_interior_anchor_2 hPoly h25 hD5 hM5 cyc0 hy1M 1
    ⟨hr1_pos, hy1_tri, hy1_W, fun la ra hH' hed_la hneg_la heq =>
      (h_not_lr la ra hH' hed_la hneg_la).2 (by simpa [r, d1] using heq)⟩
  dsimp only at hO1_res
  obtain ⟨_, oa1, ob1, Γ1, hcases1, _, hΓ1, hz1_cap⟩ := hO1_res
  have h_r_not_back : ∀ O' : Finset (Fin n), r ∉ O' →
      (∀ a ∈ O' ∩ D, ∀ b ∈ O' ∩ D, ¬ IsCCWEdge S B a b) → ¬ IsBackVertexOf S B r (w (Finset.univ \ O')) := by
    have hD5' : 5 ≤ D.card := by change 5 ≤ (hullVertices S \ certifiedVertices S w).card; omega
    have h_ep := h25.endpoint_back_criterion hHne hD5' l r r l
      (ccwCycle_mem cyc0 0) (ccwCycle_mem cyc0 1) (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1))
      (ccwCycle_isCCWEdge cyc0 0) hH_neg (Or.inr ⟨rfl, rfl⟩)
    intro O' hrO hO' hback
    obtain ⟨h_all_l, _⟩ := h_ep ⟨O', hrO, hO', hback⟩
    obtain ⟨h0, hh0⟩ := hHne
    rcases h_all_l h0 hh0 r d1 (ccwCycle_isCCWEdge cyc0 1)
      (by simpa [r, d1, hc1, hc2] using (hH_r_d1 h0 hh0).1) with h0l | h1l
    · exact cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 0) h0l
    · exact cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 0) h1l
  have hO1_d1 : oa1 = y1 ∧ ob1 = cyc0.toFun (1 + 2) ∧ Γ1 = {cyc0.toFun (1 + 1)} := by
    rcases hcases1 with ⟨hoa, hob, hΓeq⟩ | ⟨hoa, hob, hΓeq⟩
    · exfalso
      have hrb := (hΓ1 (cyc0.toFun 1) (by rw [hΓeq]; exact Finset.mem_singleton_self _)).1
      exact h_r_not_back {cyc0.toFun (1 - 1), y1, cyc0.toFun (1 + 2)}
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 1 - 1),
                   fun e => hy1_nD (e ▸ ccwCycle_mem cyc0 1),
                   cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 1 + 2)⟩)
        (pentagon_Ostar_nadj h25 hD5 cyc0 hy1_nD (1 - 1) (1 + 2) (by decide) (by decide))
        (by simpa using hrb)
    · exact ⟨hoa, hob, hΓeq⟩
  rw [hO1_d1.1, hO1_d1.2.1, hO1_d1.2.2] at hΓ1 hz1_cap
  have hd1_back_O1 : ∃ O, d1 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B d1 (w (Finset.univ \ O)) :=
    ⟨{cyc0.toFun (1 - 1), y1, cyc0.toFun (1 + 2)},
      by simp only [d1, Finset.mem_insert, Finset.mem_singleton, not_or]
         exact ⟨cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1 - 1),
                fun e => hy1_nD (e ▸ ccwCycle_mem cyc0 2),
                cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1 + 2)⟩,
      pentagon_Ostar_nadj h25 hD5 cyc0 hy1_nD (1 - 1) (1 + 2) (by decide) (by decide),
      (hΓ1 (cyc0.toFun (1 + 1)) (Finset.mem_singleton_self _)).1⟩
  have hd1_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d2} ∅ w) (S d1) Hp := by
    simpa [d2] using (hΓ1 (cyc0.toFun (1 + 1)) (Finset.mem_singleton_self _)).2.2
  have hd1_cap : ∀ z : Fin n, z ≠ y1 → z ≠ d2 → z ∉ ({l, y1, d2} : Finset (Fin n)) →
      S z ∈ convexHull ℝ (({d1, y1, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d2} ∅ w) (S z) Hp := by
    intro z hzy1 hzd2 hzO hzconv
    have heq : (({cyc0.toFun (1 + 1)} ∪ {y1, cyc0.toFun (1 + 2)} : Finset (Fin n)).image S : Set (ℝ × ℝ)) =
        (({d1, y1, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
      ext p; simp [d1, d2, or_left_comm]
    have hz1 := hz1_cap z hzy1 hzd2 (by simpa [l, d2] using hzO) (by rwa [heq])
    simpa [d2] using hz1.2.1
  have hO0_res := pentagon_interior_anchor_2 hPoly h25 hD5 hM5 cyc0 hy0M 4
    ⟨hd3l_pos, by simpa [d3, l] using hy0_tri, by simpa [d3, l] using hy0_W,
      fun la ra hH' hed_la hneg_la heq => (h_not_lr la ra hH' hed_la hneg_la).1 (by simpa [d3, l] using heq)⟩
  dsimp only at hO0_res
  obtain ⟨hpart0, oa0, ob0, Γ0, hcases0, hgap0, hΓ0, hz0_cap⟩ := hO0_res
  have hO0_l : oa0 = y0 ∧ ob0 = cyc0.toFun (4 + 2) ∧ Γ0 = {cyc0.toFun (4 + 1)} := by
    rcases hcases0 with ⟨hoa, hob, hΓeq⟩ | ⟨hoa, hob, hΓeq⟩
    · exfalso
      rw [hoa, hob, hΓeq] at hΓ0 hz0_cap
      refine opposite_endpoint_hd3_d1_absurd hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty
        (fun la ra hH' hed_la hneg_la => by
          have heq := certified_edge_unique_of_neg hPoly h25 hH' hD3 hed_la hneg_la
            (ccwCycle_isCCWEdge cyc0 0) (ccwCycle_mem cyc0 0) (ccwCycle_mem cyc0 1)
            (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)) (fun d hd hl' hr' x hx => by
              have h_ed := h_edges0 d hd
              rw [← hl_eq] at h_ed; rw [← hr_eq] at h_ed
              exact h_ed hl' hr' x hx)
          rw [heq.1, heq.2]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2)⟩,
                 ⟨cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)⟩⟩)
        hd1_back_O1 hd1_hp hd1_cap
        ⟨{cyc0.toFun (4 - 1), y0, cyc0.toFun (4 + 2)}, ?_, ?_, ?_⟩ ?_ ?_
      · simp only [d3, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 4 - 1),
               fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 4),
               cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 4 + 2)⟩
      · exact pentagon_Ostar_nadj h25 hD5 cyc0 hy0_nD (4 - 1) (4 + 2) (by decide) (by decide)
      · exact (hΓ0 (cyc0.toFun 4) (Finset.mem_singleton_self _)).1
      · simpa [d2] using (hΓ0 (cyc0.toFun 4) (Finset.mem_singleton_self _)).2.2
      · intro z hzd2 hzy0 hzO hzconv
        have heq : (({cyc0.toFun 4} ∪ {cyc0.toFun (4 - 1), y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) =
            (({d3, d2, y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
          have h41 : (4 - 1 : Fin 5) = 3 := by decide
          ext p
          simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨x, rfl | rfl | rfl, rfl⟩
            · exact ⟨_, Or.inl rfl, rfl⟩
            · exact ⟨_, Or.inr (Or.inl (by rw [h41])), rfl⟩
            · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
          · rintro ⟨x, rfl | rfl | rfl, rfl⟩
            · exact ⟨_, Or.inl rfl, rfl⟩
            · exact ⟨_, Or.inr (Or.inl (by rw [h41])), rfl⟩
            · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
        have hz0 := hz0_cap z hzd2 hzy0 (by simpa [d2, r] using hzO) (by rwa [heq])
        simpa [d2] using hz0.2.1
    · exact ⟨hoa, hob, hΓeq⟩
  rw [hO0_l.1, hO0_l.2.1] at hgap0
  rw [hO0_l.1, hO0_l.2.1, hO0_l.2.2] at hΓ0 hz0_cap
  let O0 : Finset (Fin n) := {d2, y0, r}
  let v0 := w (Finset.univ \ O0)
  have hO0_eq : ({cyc0.toFun (4 - 1), y0, cyc0.toFun (4 + 2)} : Finset (Fin n)) = O0 := rfl
  have hl_Γ0 : l ∈ ({cyc0.toFun (4 + 1)} : Finset (Fin n)) := Finset.mem_singleton_self _
  have hl_back_B : IsBackVertexOf S B l v0 := (hΓ0 l hl_Γ0).1
  have hl_cross : SegmentsCross v0 (S l) (S y0) (S r) := by simpa [r] using (hΓ0 l hl_Γ0).2.1
  have hl_hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, r} ∅ w) (S l) Hp := by
    simpa [r] using (hΓ0 l hl_Γ0).2.2
  have hH_card1 : H.card = 1 := by
    by_contra hnc
    have h2H : 2 ≤ H.card := Nat.succ_le_of_lt (lt_of_le_of_ne hHne.card_pos (Ne.symm hnc))
    obtain ⟨h1, h2, hh1, hh2, hh12, e_lh1, e_h1h2⟩ := hH2 h2H
    rw [← hl_eq] at e_lh1
    have hv0_l : l ∈ Finset.univ \ O0 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3), fun e => hy0_nD (e ▸ ccwCycle_mem cyc0 0),
             cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)⟩⟩
    have hv0_h2 : h2 ∈ Finset.univ \ O0 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 3)).2 (by dsimp [d2] at e; rw [← e]; exact hh2),
             fun e => hy0_nH (by rw [← e]; exact hh2),
             fun e => (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 1)).2 (by dsimp [r] at e; rw [← e]; exact hh2)⟩⟩
    obtain ⟨_, Tz, hh1_nTz, hb_Tz, hc_Tz, hfront_Tz⟩ := Finset.mem_filter.mp hh1
    have hl_Tz : l ∈ Tz := hb_Tz l e_lh1
    have hh2_Tz : h2 ∈ Tz := hc_Tz h2 e_h1h2
    have hB3 : 3 ≤ B.card := by have := Finset.card_le_card hD_sub_B; omega
    have hfront_v0 := (h25.hidden_front B Tz h1 l h2 Subset.rfl hB3 (hH_sub_B hh1) e_lh1 e_h1h2 hl_Tz hh2_Tz hh1_nTz hfront_Tz).2
      (Finset.univ \ O0) hv0_l hv0_h2
    have hor1 := hl_back_B.2 l h1 e_lh1 (Or.inl rfl)
    have hor2 := hfront_v0.2.2 l h1 e_lh1 (Or.inr rfl)
    linarith
  obtain ⟨h, hh_eq⟩ := Finset.card_eq_one.mp hH_card1
  have hhH : h ∈ H := by
    have hm : h ∈ ({h} : Finset (Fin n)) := Finset.mem_singleton_self h
    rwa [← hh_eq] at hm
  obtain ⟨e_lh, e_hr⟩ := hH1 hH_card1 h hhH
  rw [← hl_eq] at e_lh; rw [← hr_eq] at e_hr
  have hhB : h ∈ B := hH_sub_B hhH
  have hd3_l_B : IsCCWEdge S B d3 l :=
    (h_edges d3 (ccwCycle_mem cyc0 4) (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 0))
      (cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1)) l (hD_sub_B (ccwCycle_mem cyc0 0))).2.mpr
      (by simpa [d3, l] using ccwCycle_isCCWEdge cyc0 4)
  have hr_d1_B : IsCCWEdge S B r d1 :=
    (h_edges d1 (ccwCycle_mem cyc0 2) (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 0))
      (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1)) r (hD_sub_B (ccwCycle_mem cyc0 1))).1.mpr
      (by simpa [r, d1] using ccwCycle_isCCWEdge cyc0 1)
  have hd1_d2_B : IsCCWEdge S B d1 d2 :=
    (h_edges d1 (ccwCycle_mem cyc0 2) (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 0))
      (cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 1)) d2 (hD_sub_B (ccwCycle_mem cyc0 3))).2.mpr
      (ccwCycle_isCCWEdge cyc0 2)
  have hd2_d3_B : IsCCWEdge S B d2 d3 :=
    (h_edges d2 (ccwCycle_mem cyc0 3) (cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 0))
      (cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 1)) d3 (hD_sub_B (ccwCycle_mem cyc0 4))).2.mpr
      (ccwCycle_isCCWEdge cyc0 3)
  have hB_card : B.card = 6 := by
    have := Finset.card_sdiff_add_card_inter B H
    have hi : B ∩ H = H := Finset.inter_eq_right.mpr hH_sub_B
    rw [hi, hH_card1] at this
    change D.card + 1 = B.card at this
    change D.card = 5 at hD5
    omega
  have hn3 : 3 ≤ n := by have hle := Finset.card_le_univ D; rw [Fintype.card_fin] at hle; change D.card = 5 at hD5; omega
  obtain ⟨kB, hkB, ⟨cycB0⟩⟩ := exists_ccwCycle_hullVertices hPoly hn3
  have hkB3 : kB = 3 := by change B.card = kB + 3 at hkB; omega
  subst hkB3
  obtain ⟨iB0, hiB0⟩ := ccwCycle_exists_index cycB0 (hD_sub_B (ccwCycle_mem cyc0 4))
  let cycB : CCWCycle S B 3 := ccwCycle_shift cycB0 iB0
  have hB0 : cycB.toFun 0 = d3 := by dsimp [cycB, ccwCycle_cast, ccwCycle_shift]; simpa using hiB0
  have hB1 : cycB.toFun 1 = l := isCCWEdge_unique_succ cycB (hB0 ▸ ccwCycle_isCCWEdge cycB 0) hd3_l_B
  have hB2 : cycB.toFun 2 = h := isCCWEdge_unique_succ cycB (hB1 ▸ ccwCycle_isCCWEdge cycB 1) e_lh
  have hB3 : cycB.toFun 3 = r := isCCWEdge_unique_succ cycB (hB2 ▸ ccwCycle_isCCWEdge cycB 2) e_hr
  have hB4 : cycB.toFun 4 = d1 := isCCWEdge_unique_succ cycB (hB3 ▸ ccwCycle_isCCWEdge cycB 3) hr_d1_B
  have hB5 : cycB.toFun 5 = d2 := isCCWEdge_unique_succ cycB (hB4 ▸ ccwCycle_isCCWEdge cycB 4) hd1_d2_B
  have hy0_pos_edge_B : ∀ a b : Fin n, IsCCWEdge S B a b → 0 < orient2D (S a) (S b) (S y0) := by
    intro a b hab
    have hnn : 0 ≤ orient2D (S a) (S b) (S y0) := orient2D_const_le_convexHull (fun p hp => by
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨j, hj, rfl⟩
      by_cases hja : j = a
      · rw [hja, orient2D_self_outer]
      · by_cases hjb : j = b
        · rw [hjb, orient2D_self_right]
        · exact le_of_lt (hab.2.2.2 j hj hja hjb)) (mem_convexHull_hullVertices S hPoly.s_inj y0)
    have hne : orient2D (S a) (S b) (S y0) ≠ 0 := hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab.2.2.1)
      (hPoly.s_inj.ne (fun h => (Finset.mem_sdiff.mp hy0_A).2 (h ▸ hab.2.1)))
      (hPoly.s_inj.ne (fun h => (Finset.mem_sdiff.mp hy0_A).2 (h ▸ hab.1)))
    exact lt_of_le_of_ne hnn hne.symm
  have ho_d3lh : 0 < orient2D (S d3) (S l) (S h) := by
    have := cycB.ccw_tri 0 1 2 (by decide) (by decide); rwa [hB0, hB1, hB2] at this
  have ho_hrd3 : 0 < orient2D (S h) (S r) (S d3) := by
    have := cycB.ccw_tri 0 2 3 (by decide) (by decide)
    rw [hB0, hB2, hB3] at this; unfold orient2D at this ⊢; linarith
  have ho_hd1d3 : 0 < orient2D (S h) (S d1) (S d3) := by
    have := cycB.ccw_tri 0 2 4 (by decide) (by decide)
    rw [hB0, hB2, hB4] at this; unfold orient2D at this ⊢; linarith
  have ho_d3lr : 0 < orient2D (S d3) (S l) (S r) := by
    have := cycB.ccw_tri 0 1 3 (by decide) (by decide); rwa [hB0, hB1, hB3] at this
  have ho_d3hr : 0 < orient2D (S d3) (S h) (S r) := by
    have := cycB.ccw_tri 0 2 3 (by decide) (by decide); rwa [hB0, hB2, hB3] at this
  have ho_lhr : 0 < orient2D (S l) (S h) (S r) := by
    have := cycB.ccw_tri 1 2 3 (by decide) (by decide); rwa [hB1, hB2, hB3] at this
  have ho_d3ly0 : 0 < orient2D (S d3) (S l) (S y0) := hy0_pos_edge_B d3 l hd3_l_B
  have ho_lhy0 : 0 < orient2D (S l) (S h) (S y0) := hy0_pos_edge_B l h e_lh
  have hy0_orient : 0 < orient2D (S h) (S d3) (w D) ∧ 0 < orient2D (S h) (S d3) (S y0) ∧
      0 < orient2D (S d3) (S y0) (S r) ∧ 0 < orient2D (S y0) (S h) (S r) := by
    have hh_tri : InIntTri (w D) (S r) (S d1) (S h) := by simpa [r, d1, hc1, hc2] using (hH_r_d1 h hhH).1
    rcases hh_tri with ⟨μ0, μ1, μ2, hm0, hm1, hm2, hmsum, hh1, hh2⟩
    rcases hy0_tri with ⟨ν0, ν1, ν2, hn0, hn1, hn2, hnsum, hy01', hy02'⟩
    exact prop_opposite_endpoint_exit_orient (S d3) (S l) (S h) (S r) (S d1) (w D) (S y0)
      μ0 μ1 μ2 ν0 ν1 ν2 hm0 hm1 hm2 hmsum hh1 hh2 hn0 hn1 hn2 hnsum hy01' hy02'
      ho_hrd3 ho_hd1d3 ho_d3lh ho_d3lr ho_d3hr ho_lhr ho_d3ly0 ho_lhy0
  have hy0_in_d3lh : InIntTri (S d3) (S l) (S h) (S y0) :=
    (inIntTri_iff_orient_pos ho_d3lh).mpr ⟨ho_d3ly0, ho_lhy0, hy0_orient.2.1⟩
  obtain ⟨p, oa, ob, hcases, hgap, hcross, hp_nO0⟩ := opposite_endpoint_cy_targets hPoly h25 cyc0 cycB
    hhH e_lh e_hr hhB hr_d1_B hd1_d2_B hd2_d3_B hB_card hn3 hB0 hB1 hB2 hB3 hB4 hB5
    hy0_A hy0_nD hy0_nH hy0_W hy0_orient hy0_in_d3lh hl_back_B hpart0.1
  obtain ⟨hp_hp, hp_back⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap hp_nO0 hcross
  rcases hcases with ⟨hp_e, hoa_e, hob_e⟩ | ⟨hp_e, hoa_e, hob_e⟩ | ⟨hp_e, hoa_e, hob_e⟩
  · rw [hp_e] at hcross hp_hp; rw [hoa_e, hob_e] at hgap hcross hp_hp
    exact opposite_endpoint_ig0_absurd hPoly h25 hD5 hM5 cyc0 cycB hhH hH_card1 e_lh
      hB0 hB1 hB2 hB3 hB4 hB5 hy0M hy0_A hy0_nH hy0_empty hl_cross hl_hp hgap hcross hp_hp
  · rw [hp_e] at hcross hp_hp hp_back; rw [hoa_e, hob_e] at hgap hcross hp_hp
    exact opposite_endpoint_ig2_absurd hPoly h25 hD5 hM5 cyc0 cycB hy0_nD hB0 hB1 hB2 hB3 hB5
      (fun la ra hH' hed_la hneg_la => by
        have heq := certified_edge_unique_of_neg hPoly h25 hH' hD3 hed_la hneg_la
          (ccwCycle_isCCWEdge cyc0 0) (ccwCycle_mem cyc0 0) (ccwCycle_mem cyc0 1)
          (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)) (fun d hd hl' hr' x hx => by
            have h_ed := h_edges0 d hd
            rw [← hl_eq] at h_ed; rw [← hr_eq] at h_ed
            exact h_ed hl' hr' x hx)
        rw [heq.1, heq.2]
        exact ⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2), cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)⟩)
      hy0_in_d3lh hgap hcross hp_hp (hp_back (hD_sub_B (ccwCycle_mem cyc0 2)))
  · rw [hp_e] at hcross hp_hp hp_back hp_nO0; rw [hoa_e, hob_e] at hgap hcross hp_hp
    refine opposite_endpoint_hd3_d1_absurd hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty
      (fun la ra hH' hed_la hneg_la => by
        have heq := certified_edge_unique_of_neg hPoly h25 hH' hD3 hed_la hneg_la
          (ccwCycle_isCCWEdge cyc0 0) (ccwCycle_mem cyc0 0) (ccwCycle_mem cyc0 1)
          (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)) (fun d hd hl' hr' x hx => by
            have h_ed := h_edges0 d hd
            rw [← hl_eq] at h_ed; rw [← hr_eq] at h_ed
            exact h_ed hl' hr' x hx)
        rw [heq.1, heq.2]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨⟨cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2)⟩,
               ⟨cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 4), cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)⟩⟩)
      hd1_back_O1 hd1_hp hd1_cap
      ⟨O0, hp_nO0, pentagon_Ostar_nadj h25 hD5 cyc0 hy0_nD 3 1 (by decide) (by decide),
        hp_back (hD_sub_B (ccwCycle_mem cyc0 4))⟩
      hp_hp (fun z hzd2 hzy0 hzO hzconv => ?_)
    have hz_nO0 : z ∉ O0 := by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzO
      exact ⟨hzO.1, hzO.2.1, hzO.2.2⟩
    exact (cap_crossing_of_vertices_cross hPoly h25 hgap {d3, d2, y0}
      (fun g hg => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl
        · exact Or.inr (Or.inr hcross)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl))
      hz_nO0 hzd2 hzy0 hzconv).2.1

/-- **Proposition 8.5 (`opposite-endpoint-exit`, `upper_9.tex` lines 969–999)**, full symmetric form:
    rules out both `(e(H) = {r d1}, e⁻¹(d3 l) ≠ ∅)` and `(e(H) = {d3 l}, e⁻¹(r d1) ≠ ∅)`. -/
theorem opposite_endpoint_exit {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (il : Fin 5)
    (hHne : (certifiedVertices S w).Nonempty)
    (hlr_neg : ∀ h ∈ certifiedVertices S w,
      orient2D (S (cycD.toFun il)) (S (cycD.toFun (il + 1))) (S h) < 0) :
    ¬ ((∀ h ∈ certifiedVertices S w,
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S h) ∧
        ∀ x ∈ WitnessSet {cycD.toFun (il + 1), cycD.toFun (il + 2)} ∅ w,
          InIntTri x (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S h)) ∧
       ∃ y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 4))) (S (cycD.toFun il)) (S y0)) ∧
    ¬ ((∀ h ∈ certifiedVertices S w,
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 4))) (S (cycD.toFun il)) (S h) ∧
        ∀ x ∈ WitnessSet {cycD.toFun (il + 4), cycD.toFun il} ∅ w,
          InIntTri x (S (cycD.toFun (il + 4))) (S (cycD.toFun il)) (S h)) ∧
       ∃ y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S y0)) := by
  constructor
  · rintro ⟨hH_rd1, he_d3l⟩
    exact opposite_endpoint_exit_right hPoly h25 hD5 hM5 cycD il hHne hlr_neg hH_rd1 he_d3l
  · rintro ⟨hH_d3l, he_rd1⟩
    let P' := reflPt '' P
    let S' := reflPt ∘ S
    let w' := reflPt ∘ w
    have hPoly' := reflPt_shattered hPoly
    have h25' := reflPt_sec2to5 hPoly h25
    have hD_eq' : hullVertices S' \ certifiedVertices S' w' = hullVertices S \ certifiedVertices S w := by
      simp [S', w', reflPt_hullVertices, reflPt_certifiedVertices]
    let cycR : CCWCycle S' (hullVertices S' \ certifiedVertices S' w') 2 :=
      ccwCycle_cast hD_eq'.symm (ccwCycle_rev cycD (il + 2))
    have hi1 : cycR.toFun 1 = cycD.toFun (il + 1) := by
      dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; congr 1
      rw [sub_eq_add_neg, add_assoc]; congr 1
    have hi2 : cycR.toFun 2 = cycD.toFun il := by
      dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; congr 1; abel
    have hi3 : cycR.toFun 3 = cycD.toFun (il + 4) := by
      dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; congr 1
      rw [sub_eq_add_neg, add_assoc]; congr 1
    have hi0 : cycR.toFun 0 = cycD.toFun (il + 2) := by
      dsimp [cycR, ccwCycle_cast, ccwCycle_rev]; simp
    refine opposite_endpoint_exit_right hPoly' h25' (by rwa [hD_eq']) (by rwa [hD_eq']) cycR 1
      (by simpa [S', w', reflPt_certifiedVertices] using hHne) ?_ ?_ ?_
    · intro h hh
      have hh' : h ∈ certifiedVertices S w := by simpa [S', w', reflPt_certifiedVertices] using hh
      have h1 : (1 + 1 : Fin 5) = 2 := by decide
      rw [h1, hi1, hi2]
      dsimp [S']; rw [reflPt_orient2D]
      have ho := hlr_neg h hh'
      unfold orient2D at ho ⊢; linarith
    · intro h hh
      have hh' : h ∈ certifiedVertices S w := by simpa [S', w', reflPt_certifiedVertices] using hh
      have h2 : (1 + 1 : Fin 5) = 2 := by decide
      have h3 : (1 + 2 : Fin 5) = 3 := by decide
      rw [h2, h3, hi2, hi3, hD_eq']
      refine ⟨?_, fun x hx => ?_⟩
      · dsimp only [S', w', Function.comp_apply]
        rw [reflPt_inIntTri]
        exact (hH_d3l h hh').1.symm23
      · rw [reflPt_witnessSet] at hx
        rcases hx with ⟨z, hz, rfl⟩
        dsimp only [S', Function.comp_apply]
        rw [reflPt_inIntTri]
        have hz' : z ∈ WitnessSet {cycD.toFun (il + 4), cycD.toFun il} ∅ w := by
          rwa [Finset.pair_comm] at hz
        exact ((hH_d3l h hh').2 z hz').symm23
    · obtain ⟨y0, hy0M, hy0_t⟩ := he_rd1
      refine ⟨y0, by rwa [hD_eq'], ?_⟩
      have h5 : (1 + 4 : Fin 5) = 0 := by decide
      rw [h5, hi0, hi1, hD_eq']
      dsimp only [S', w', Function.comp_apply]
      rw [reflPt_inIntTri]
      exact hy0_t.symm23

private lemma reflPt_mem_convexHull (T : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    reflPt p ∈ convexHull ℝ (reflPt '' T) ↔ p ∈ convexHull ℝ T := by
  rw [← reflPt_image_convexHull]
  constructor
  · rintro ⟨q, hq, hqq⟩; rwa [← reflPt_inj hqq]
  · intro hp; exact ⟨p, hp, rfl⟩

private lemma finset3_image_eq {n : ℕ} (S : Fin n → ℝ × ℝ) (a b c : Fin n) :
    (({a, b, c} : Finset (Fin n)).image S : Set (ℝ × ℝ)) = {S a, S b, S c} := by
  ext p
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl | rfl | rfl, rfl⟩ <;> tauto
  · rintro (rfl | rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨c, Or.inr (Or.inr rfl), rfl⟩

private lemma finset4_image_eq {n : ℕ} (S : Fin n → ℝ × ℝ) (a b c d : Fin n) :
    (({a, b, c, d} : Finset (Fin n)).image S : Set (ℝ × ℝ)) = {S a, S b, S c, S d} := by
  ext p
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl | rfl | rfl | rfl, rfl⟩ <;> tauto
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨d, Or.inr (Or.inr (Or.inr rfl)), rfl⟩

private lemma convexHull_inIntTri_subset {w u v y : ℝ × ℝ} (hy : InIntTri w u v y) :
    convexHull ℝ ({u, v, y} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({w, u, v} : Set (ℝ × ℝ)) := by
  refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact subset_convexHull ℝ _ (by simp)
  · exact subset_convexHull ℝ _ (by simp)
  · exact hy.to_convexHull

private lemma minimal_on_exit_edge {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) k)
    (i : Fin (k + 3))
    (hnf : 0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (w (hullVertices S \ certifiedVertices S w)))
    (hex : ∃ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y)) :
    ∃ y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0) ∧
      (∀ x ∈ WitnessSet {cycD.toFun i, cycD.toFun (i + 1)} ∅ w,
        InIntTri x (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun i, cycD.toFun (i + 1)) ≠ (l, r)) ∧
      (∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
        ¬ InClosedTri (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0) (S z)) := by
  let H := certifiedVertices S w
  let D := hullVertices S \ H
  let M := Finset.univ \ D
  let u0 := cycD.toFun i
  let v0 := cycD.toFun (i + 1)
  have hD3 : 3 ≤ D.card := by
    dsimp [D, H]; rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]; omega
  have hed : IsCCWEdge S D u0 v0 := ccwCycle_isCCWEdge cycD i
  let E := M.filter (fun y => InIntTri (w D) (S u0) (S v0) (S y))
  have hE_ne : E.Nonempty := by
    obtain ⟨y, hyM, hy_tri⟩ := hex
    exact ⟨y, Finset.mem_filter.mpr ⟨hyM, hy_tri⟩⟩
  let f : Fin n → ℝ := fun y => orient2D (S u0) (S v0) (S y)
  obtain ⟨y0, hy0E, hy0_min⟩ := Finset.exists_min_image E f hE_ne
  have hy0M : y0 ∈ M := (Finset.mem_filter.mp hy0E).1
  have hy0_tri : InIntTri (w D) (S u0) (S v0) (S y0) := (Finset.mem_filter.mp hy0E).2
  obtain ⟨uy, vy, _, _, _, hnot_lr_uv, hW_uv, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
  obtain ⟨rfl, rfl⟩ := h_uniq u0 v0 hed hnf hy0_tri.to_convexHull
  have he_B_u0v0 : IsCCWEdge S (hullVertices S) u0 v0 :=
    isCCWEdge_B_of_D_ne_lr h25 hD3 hed (fun l r hH _ _ _ hlrD hHn => hnot_lr_uv l r hH hlrD hHn)
  have hf_y0_pos : 0 < f y0 := orient2D_pos_of_isCCWEdge_B hPoly he_B_u0v0
    (fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cycD i))
    (fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cycD (i + 1)))
  refine ⟨y0, hy0M, hy0_tri, hW_uv, hnot_lr_uv, fun z hz hclosed => ?_⟩
  have hz_ne : z ≠ y0 := (Finset.mem_erase.mp hz).1
  have hzM : z ∈ M := (Finset.mem_erase.mp hz).2
  have hz_conv : S z ∈ convexHull ℝ ({w D, S u0, S v0} : Set (ℝ × ℝ)) :=
    convexHull_inIntTri_subset hy0_tri ((inClosedTri_iff_mem_convexHull _ _ _ _).mp hclosed)
  obtain ⟨uz, vz, _, _, hinz, _, _, h_uniqz⟩ := h25.exit_edge_lemma hD3 z hzM
  obtain ⟨rfl, rfl⟩ := h_uniqz u0 v0 hed hnf hz_conv
  have hle : f y0 ≤ f z := hy0_min z (Finset.mem_filter.mpr ⟨hzM, hinz⟩)
  rcases hclosed with ⟨t0, t1, t2, ht0, ht1, ht2, hts, hz1, hz2⟩
  have ht2_lt : t2 < 1 := by
    by_contra hge
    have ht21 : t2 = 1 := by linarith
    have ht00 : t0 = 0 := by linarith
    have ht10 : t1 = 0 := by linarith
    rw [ht00, ht10, ht21] at hz1 hz2
    simp only [zero_mul, one_mul, zero_add] at hz1 hz2
    exact hz_ne (hPoly.s_inj (Prod.ext hz1 hz2))
  have hid := orient2D_convex_comb3 (S u0) (S v0) (S u0) (S v0) (S y0) (S z) t0 t1 t2 hts hz1 hz2
  rw [orient2D_self_outer, orient2D_self_right, mul_zero, mul_zero, zero_add, zero_add] at hid
  change f z = t2 * f y0 at hid
  nlinarith

private lemma two_minimal_on_exit_edge {n k : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) k)
    (i : Fin (k + 3))
    (hnf : 0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (w (hullVertices S \ certifiedVertices S w)))
    (h2 : 2 ≤ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).filter
      (fun y => InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y))).card) :
    ∃ y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      ∃ y0' ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        y0 ≠ y0' ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0') ∧
        (∀ x ∈ WitnessSet {cycD.toFun i, cycD.toFun (i + 1)} ∅ w,
          InIntTri x (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0) ∧
          InIntTri x (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0')) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun i, cycD.toFun (i + 1)) ≠ (l, r)) ∧
        (∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
          ¬ InClosedTri (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0) (S z)) ∧
        (∀ z ∈ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0).erase y0',
          ¬ InClosedTri (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y0') (S z) ∧
          S z ∉ convexHull ℝ ({S (cycD.toFun i), S (cycD.toFun (i + 1)), S y0, S y0'} : Set (ℝ × ℝ))) := by
  let H := certifiedVertices S w
  let D := hullVertices S \ H
  let M := Finset.univ \ D
  let u0 := cycD.toFun i
  let v0 := cycD.toFun (i + 1)
  have hD3 : 3 ≤ D.card := by
    dsimp [D, H]; rw [← cycD.image_eq, Finset.card_image_of_injective Finset.univ cycD.inj, Finset.card_fin]; omega
  have hed : IsCCWEdge S D u0 v0 := ccwCycle_isCCWEdge cycD i
  let E := M.filter (fun y => InIntTri (w D) (S u0) (S v0) (S y))
  have hE_card : 2 ≤ E.card := by dsimp [E, M, D, H, u0, v0]; exact h2
  have hE_ne : E.Nonempty := Finset.card_pos.mp (by omega)
  let f : Fin n → ℝ := fun y => orient2D (S u0) (S v0) (S y)
  obtain ⟨y0, hy0E, hy0_min⟩ := Finset.exists_min_image E f hE_ne
  have hy0M : y0 ∈ M := (Finset.mem_filter.mp hy0E).1
  have hy0_tri : InIntTri (w D) (S u0) (S v0) (S y0) := (Finset.mem_filter.mp hy0E).2
  have hE'_ne : (E.erase y0).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hy0E]; omega)
  obtain ⟨y0', hy0'E', hy0'_min⟩ := Finset.exists_min_image (E.erase y0) f hE'_ne
  have hy01 : y0 ≠ y0' := (Finset.mem_erase.mp hy0'E').1.symm
  have hy0'E : y0' ∈ E := Finset.mem_of_mem_erase hy0'E'
  have hy0'M : y0' ∈ M := (Finset.mem_filter.mp hy0'E).1
  have hy0'_tri : InIntTri (w D) (S u0) (S v0) (S y0') := (Finset.mem_filter.mp hy0'E).2
  have hfy0_le : f y0 ≤ f y0' := hy0_min y0' hy0'E
  obtain ⟨uy, vy, _, _, _, hnot_lr_uv, hW_uv, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
  obtain ⟨uy', vy', _, _, _, _, hW_uv', h_uniq'⟩ := h25.exit_edge_lemma hD3 y0' hy0'M
  obtain ⟨rfl, rfl⟩ := h_uniq u0 v0 hed hnf hy0_tri.to_convexHull
  obtain ⟨rfl, rfl⟩ := h_uniq' u0 v0 hed hnf hy0'_tri.to_convexHull
  have he_B_u0v0 : IsCCWEdge S (hullVertices S) u0 v0 :=
    isCCWEdge_B_of_D_ne_lr h25 hD3 hed (fun l r hH _ _ _ hlrD hHn => hnot_lr_uv l r hH hlrD hHn)
  have hf_y0_pos : 0 < f y0 := orient2D_pos_of_isCCWEdge_B hPoly he_B_u0v0
    (fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cycD i))
    (fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cycD (i + 1)))
  have hf_y0'_pos : 0 < f y0' := orient2D_pos_of_isCCWEdge_B hPoly he_B_u0v0
    (fun h => (Finset.mem_sdiff.mp hy0'M).2 (h ▸ ccwCycle_mem cycD i))
    (fun h => (Finset.mem_sdiff.mp hy0'M).2 (h ▸ ccwCycle_mem cycD (i + 1)))
  refine ⟨y0, hy0M, y0', hy0'M, hy01, hy0_tri, hy0'_tri,
    (fun x hx => ⟨hW_uv x hx, hW_uv' x hx⟩), hnot_lr_uv, ?_, ?_⟩
  · intro z hz hclosed
    have hz_ne : z ≠ y0 := (Finset.mem_erase.mp hz).1
    have hzM : z ∈ M := (Finset.mem_erase.mp hz).2
    obtain ⟨hz_fan, hle_y0⟩ := exitRegion_single_disjoint (w D) (S u0) (S v0) (S y0) (S z)
      hf_y0_pos hy0_tri.to_inClosedTri hclosed
    obtain ⟨uz, vz, _, _, hinz, _, _, h_uniqz⟩ := h25.exit_edge_lemma hD3 z hzM
    obtain ⟨rfl, rfl⟩ := h_uniqz u0 v0 hed hnf ((inClosedTri_iff_mem_convexHull _ _ _ _).mp hz_fan)
    exact hz_ne (hPoly.s_inj (hle_y0 (hy0_min z (Finset.mem_filter.mpr ⟨hzM, hinz⟩))))
  · intro z hz
    have hz_ne' : z ≠ y0' := (Finset.mem_erase.mp hz).1
    have hz_ne0 : z ≠ y0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzM : z ∈ M := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
    have h_quad : S z ∉ convexHull ℝ ({S u0, S v0, S y0, S y0'} : Set (ℝ × ℝ)) := by
      intro hq
      obtain ⟨hz_fan, h_ord⟩ := exitRegion_two_same_edge_disjoint (w D) (S u0) (S v0) (S y0) (S y0') (S z)
        hf_y0_pos hfy0_le hy0_tri.to_inClosedTri hy0'_tri.to_inClosedTri hq
      obtain ⟨uz, vz, _, _, hinz, _, _, h_uniqz⟩ := h25.exit_edge_lemma hD3 z hzM
      obtain ⟨rfl, rfl⟩ := h_uniqz u0 v0 hed hnf ((inClosedTri_iff_mem_convexHull _ _ _ _).mp hz_fan)
      have hle : f y0' ≤ f z := hy0'_min z (Finset.mem_erase.mpr ⟨hz_ne0, Finset.mem_filter.mpr ⟨hzM, hinz⟩⟩)
      have hcol : orient2D (S y0) (S y0') (S z) ≠ 0 := hPoly.no_three_collinear _ _ _
        (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_inj.ne hy01) (hPoly.s_inj.ne hz_ne'.symm) (hPoly.s_inj.ne hz_ne0.symm)
      rcases (h_ord hle).2 hcol with h | h
      · exact hz_ne0 (hPoly.s_inj h)
      · exact hz_ne' (hPoly.s_inj h)
    refine ⟨fun hcl => h_quad (convexHull_mono (fun p hp => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl <;> [exact Or.inl rfl; exact Or.inr (Or.inl rfl); exact Or.inr (Or.inr (Or.inr rfl))]) ((inClosedTri_iff_mem_convexHull _ _ _ _).mp hcl)), h_quad⟩

private lemma elim02_disjoint_exits {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y0 y1 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y1)
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y0) (S z))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) (S y1) (S z))
    (h_Q_H_disj : ∀ Q : Finset (Fin n),
      Q ⊆ {cyc0.toFun 0, cyc0.toFun 1, cyc0.toFun 2, cyc0.toFun 3} →
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
         ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O))) →
      ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q)
    (h0b : ∃ O, cyc0.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
       ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 0) (w (Finset.univ \ O)))
    (h0hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 4, y0} ∅ w) (S (cyc0.toFun 0)) Hp)
    (h0cap : ∀ z : Fin n, z ∉ (hullVertices S \ certifiedVertices S w) → z ≠ y0 → z ≠ y1 →
      S z ∈ convexHull ℝ ({S (cyc0.toFun 0), S (cyc0.toFun 4), S y0} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 4, y0} ∅ w) (S z) Hp)
    (h2b : ∃ O, cyc0.toFun 2 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
       ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 2) (w (Finset.univ \ O)))
    (h2hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 1, y1} ∅ w) (S (cyc0.toFun 2)) Hp)
    (h2cap : ∀ z : Fin n, z ∉ (hullVertices S \ certifiedVertices S w) → z ≠ y0 → z ≠ y1 →
      S z ∈ convexHull ℝ ({S (cyc0.toFun 2), S (cyc0.toFun 1), S y1} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 1, y1} ∅ w) (S z) Hp) :
    False := by
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  let d0 := cyc0.toFun 0; let d1 := cyc0.toFun 1; let d2 := cyc0.toFun 2
  let d3 := cyc0.toFun 3; let d4 := cyc0.toFun 4
  let Q : Finset (Fin n) := {d0, d2}
  let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
  have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl; exact h0b; exact h2b
  have hd1F : d1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 1, by
    simp only [Q, d0, d1, d2, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 3, by
    simp only [Q, d0, d2, d3, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 4, by
    simp only [Q, d0, d2, d4, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cyc0 _)
    (Finset.card_pair (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2))) y0 y1 hy0M hy1M hy01 hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hex_lift_hp hd4F hy0F h0hp
      · exact hex_lift_hp hd1F hy1F h2hp)
    (h_Q_H_disj Q (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d2]) hBackQ)
    (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hny01 : z ≠ y0 ∧ z ≠ y1 := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact hm
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc0.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
    have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
      ext p; simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, pD]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨cyc0.toFun i, ccwCycle_mem cyc0 i, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ D := hx
        dsimp [D] at hx'; rw [← cyc0.image_eq] at hx'
        rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
    rw [hr]; exact hzD_conv
  have hcov := convD_cover_case3b_disjoint_02 pD cyc0.ccw (S y0) (S y1) (F.image S : Set (ℝ × ℝ))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
  rcases hcov with ((hF | hc0) | hc2) | (he0 | he1)
  · exact Or.inr hF
  · left
    have hset : ({pD 4, pD 0, S y0} : Set (ℝ × ℝ)) = {S d0, S d4, S y0} := by
      change {S d4, S d0, S y0} = {S d0, S d4, S y0}; exact Set.insert_comm _ _ _
    rw [hset] at hc0
    exact hex_lift_hp hd4F hy0F (h0cap z hzD hny01.1 hny01.2 hc0)
  · left
    have hset : ({pD 1, pD 2, S y1} : Set (ℝ × ℝ)) = {S d2, S d1, S y1} := by
      change {S d1, S d2, S y1} = {S d2, S d1, S y1}; exact Set.insert_comm _ _ _
    rw [hset] at hc2
    exact hex_lift_hp hd1F hy1F (h2cap z hzD hny01.1 hny01.2 hc2)
  · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
  · exact False.elim (hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1))

private lemma elim03_disjoint_exits {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y0 y1 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y1)
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y0) (S z))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) (S y1) (S z))
    (h_Q_H_disj : ∀ Q : Finset (Fin n),
      Q ⊆ {cyc0.toFun 0, cyc0.toFun 1, cyc0.toFun 2, cyc0.toFun 3} →
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
         ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O))) →
      ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q)
    (h0b : ∃ O, cyc0.toFun 0 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
       ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 0) (w (Finset.univ \ O)))
    (h0hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 4, y0} ∅ w) (S (cyc0.toFun 0)) Hp)
    (h0cap : ∀ z : Fin n, z ∉ (hullVertices S \ certifiedVertices S w) → z ≠ y0 → z ≠ y1 →
      S z ∈ convexHull ℝ ({S (cyc0.toFun 0), S (cyc0.toFun 4), S y0} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {cyc0.toFun 4, y0} ∅ w) (S z) Hp)
    (h3b : ∃ O, cyc0.toFun 3 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
       ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 3) (w (Finset.univ \ O)))
    (h3hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, cyc0.toFun 4} ∅ w) (S (cyc0.toFun 3)) Hp)
    (h3cap : ∀ z : Fin n, z ∉ (hullVertices S \ certifiedVertices S w) → z ≠ y0 → z ≠ y1 →
      S z ∈ convexHull ℝ ({S (cyc0.toFun 3), S y1, S (cyc0.toFun 4)} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, cyc0.toFun 4} ∅ w) (S z) Hp) :
    False := by
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  let d0 := cyc0.toFun 0; let d1 := cyc0.toFun 1; let d2 := cyc0.toFun 2
  let d3 := cyc0.toFun 3; let d4 := cyc0.toFun 4
  let Q : Finset (Fin n) := {d0, d3}
  let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
  have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl; exact h0b; exact h3b
  have hd1F : d1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 1, by
    simp only [Q, d0, d1, d3, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 2, by
    simp only [Q, d0, d2, d3, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 4, by
    simp only [Q, d0, d3, d4, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cyc0 _)
    (Finset.card_pair (cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3))) y0 y1 hy0M hy1M hy01 hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hex_lift_hp hd4F hy0F h0hp
      · exact hex_lift_hp hy1F hd4F h3hp)
    (h_Q_H_disj Q (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d3]) hBackQ)
    (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hny01 : z ≠ y0 ∧ z ≠ y1 := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact hm
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc0.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
    have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
      ext p; simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, pD]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨cyc0.toFun i, ccwCycle_mem cyc0 i, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ D := hx
        dsimp [D] at hx'; rw [← cyc0.image_eq] at hx'
        rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
    rw [hr]; exact hzD_conv
  have hcov := convD_cover_case3b_disjoint_03 pD cyc0.ccw (S y0) (S y1) (F.image S : Set (ℝ × ℝ))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
  rcases hcov with ((hF | hc0) | hc3) | (he0 | he1)
  · exact Or.inr hF
  · left
    have hset : ({pD 4, pD 0, S y0} : Set (ℝ × ℝ)) = {S d0, S d4, S y0} := by
      change {S d4, S d0, S y0} = {S d0, S d4, S y0}; exact Set.insert_comm _ _ _
    rw [hset] at hc0
    exact hex_lift_hp hd4F hy0F (h0cap z hzD hny01.1 hny01.2 hc0)
  · left
    have hset : ({S y1, pD 3, pD 4} : Set (ℝ × ℝ)) = {S d3, S y1, S d4} := by
      change {S y1, S d3, S d4} = {S d3, S y1, S d4}; exact Set.insert_comm _ _ _
    rw [hset] at hc3
    exact hex_lift_hp hy1F hd4F (h3cap z hzD hny01.1 hny01.2 hc3)
  · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
  · exact False.elim (hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1))

private lemma elim13_disjoint_exits {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y0 y1 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y1)
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y0) (S z))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) (S y1) (S z))
    (h_Q_H_disj : ∀ Q : Finset (Fin n),
      Q ⊆ {cyc0.toFun 0, cyc0.toFun 1, cyc0.toFun 2, cyc0.toFun 3} →
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
         ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O))) →
      ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q)
    (h1b : ∃ O, cyc0.toFun 1 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
       ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 1) (w (Finset.univ \ O)))
    (h1hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, cyc0.toFun 2} ∅ w) (S (cyc0.toFun 1)) Hp)
    (h1cap : ∀ z : Fin n, z ∉ (hullVertices S \ certifiedVertices S w) → z ≠ y0 → z ≠ y1 →
      S z ∈ convexHull ℝ ({S (cyc0.toFun 1), S y0, S (cyc0.toFun 2)} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, cyc0.toFun 2} ∅ w) (S z) Hp)
    (h3b : ∃ O, cyc0.toFun 3 ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
       ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) (cyc0.toFun 3) (w (Finset.univ \ O)))
    (h3hp : ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, cyc0.toFun 4} ∅ w) (S (cyc0.toFun 3)) Hp)
    (h3cap : ∀ z : Fin n, z ∉ (hullVertices S \ certifiedVertices S w) → z ≠ y0 → z ≠ y1 →
      S z ∈ convexHull ℝ ({S (cyc0.toFun 3), S y1, S (cyc0.toFun 4)} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, cyc0.toFun 4} ∅ w) (S z) Hp) :
    False := by
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  let d0 := cyc0.toFun 0; let d1 := cyc0.toFun 1; let d2 := cyc0.toFun 2
  let d3 := cyc0.toFun 3; let d4 := cyc0.toFun 4
  let Q : Finset (Fin n) := {d1, d3}
  let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
  have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl; exact h1b; exact h3b
  have hd0F : d0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 0, by
    simp only [Q, d0, d1, d3, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 2, by
    simp only [Q, d1, d2, d3, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 4, by
    simp only [Q, d1, d3, d4, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cyc0.inj.ne (by decide), cyc0.inj.ne (by decide)⟩⟩)
  have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cyc0 _)
    (Finset.card_pair (cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 3))) y0 y1 hy0M hy1M hy01 hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hex_lift_hp hy0F hd2F h1hp
      · exact hex_lift_hp hy1F hd4F h3hp)
    (h_Q_H_disj Q (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d1, d3]) hBackQ)
    (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hny01 : z ≠ y0 ∧ z ≠ y1 := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact hm
  let cycR : CCWCycle (reflPt ∘ S) D 2 := ccwCycle_rev cyc0 3
  let pDR : Fin 5 → ℝ × ℝ := fun i => reflPt (S (cycR.toFun i))
  have hzR : reflPt (S z) ∈ convexHull ℝ (Set.range pDR) := by
    have hr : Set.range pDR = reflPt '' (D.image S : Set (ℝ × ℝ)) := by
      ext p; simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, Finset.mem_image, pDR]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨S (cycR.toFun i), ⟨cycR.toFun i, ccwCycle_mem cycR i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        have hcr := cycR.image_eq
        dsimp [D] at hcr
        have hx' : x ∈ hullVertices S \ certifiedVertices S w := hx
        rw [← hcr] at hx'
        rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
    rw [hr]; exact (reflPt_mem_convexHull (D.image S : Set (ℝ × ℝ)) (S z)).mpr hzD_conv
  have hDR0 : pDR 0 = reflPt (S d3) := rfl
  have hDR1 : pDR 1 = reflPt (S d2) := rfl
  have hDR2 : pDR 2 = reflPt (S d1) := rfl
  have hDR3 : pDR 3 = reflPt (S d0) := rfl
  have hDR4 : pDR 4 = reflPt (S d4) := rfl
  have hcov := convD_cover_case3b_disjoint_02 pDR cycR.ccw (reflPt (S y1)) (reflPt (S y0))
    ((F.image (reflPt ∘ S)) : Set (ℝ × ℝ))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy1F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy0F))
    (by rw [hDR1]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hd2F))
    (by rw [hDR3]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hd0F))
    (by rw [hDR4]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hd4F)) hzR
  rw [hDR0, hDR1, hDR2, hDR3, hDR4] at hcov
  have pull_mem : ∀ {T : Set (ℝ × ℝ)}, reflPt (S z) ∈ convexHull ℝ (reflPt '' T) →
      S z ∈ convexHull ℝ T := fun {T} hzT => (reflPt_mem_convexHull T (S z)).mp hzT
  rcases hcov with ((hF | hc3) | hc1) | (he1 | he0)
  · right; refine pull_mem ?_
    have him : reflPt '' (F.image S : Set (ℝ × ℝ)) = (F.image (reflPt ∘ S) : Set (ℝ × ℝ)) := by ext p; simp [Finset.coe_image]
    rwa [him]
  · left
    have hc3' : S z ∈ convexHull ℝ ({S d3, S y1, S d4} : Set (ℝ × ℝ)) := by
      refine pull_mem ?_
      have him : reflPt '' ({S d3, S y1, S d4} : Set (ℝ × ℝ)) = {reflPt (S d4), reflPt (S d3), reflPt (S y1)} := by
        ext p; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
        · rintro (rfl | rfl | rfl) <;> first | exact ⟨_, Or.inl rfl, rfl⟩ | exact ⟨_, Or.inr (Or.inl rfl), rfl⟩ | exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
      rwa [him]
    exact hex_lift_hp hy1F hd4F (h3cap z hzD hny01.1 hny01.2 hc3')
  · left
    have hc1' : S z ∈ convexHull ℝ ({S d1, S y0, S d2} : Set (ℝ × ℝ)) := by
      refine pull_mem ?_
      have him : reflPt '' ({S d1, S y0, S d2} : Set (ℝ × ℝ)) = {reflPt (S d2), reflPt (S d1), reflPt (S y0)} := by
        ext p; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
        · rintro (rfl | rfl | rfl) <;> first | exact ⟨_, Or.inl rfl, rfl⟩ | exact ⟨_, Or.inr (Or.inl rfl), rfl⟩ | exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
      rwa [him]
    exact hex_lift_hp hy0F hd2F (h1cap z hzD hny01.1 hny01.2 hc1')
  · exfalso
    have he1' : S z ∈ convexHull ℝ ({S d2, S d3, S y1} : Set (ℝ × ℝ)) := by
      refine pull_mem ?_
      have him : reflPt '' ({S d2, S d3, S y1} : Set (ℝ × ℝ)) = {reflPt (S d3), reflPt (S d2), reflPt (S y1)} := by
        ext p; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
        · rintro (rfl | rfl | rfl) <;> first | exact ⟨_, Or.inl rfl, rfl⟩ | exact ⟨_, Or.inr (Or.inl rfl), rfl⟩ | exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
      rwa [him]
    exact hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1')
  · exfalso
    have he0' : S z ∈ convexHull ℝ ({S d0, S d1, S y0} : Set (ℝ × ℝ)) := by
      refine pull_mem ?_
      have him : reflPt '' ({S d0, S d1, S y0} : Set (ℝ × ℝ)) = {reflPt (S d1), reflPt (S d0), reflPt (S y0)} := by
        ext p; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
        · rintro (rfl | rfl | rfl) <;> first | exact ⟨_, Or.inl rfl, rfl⟩ | exact ⟨_, Or.inr (Or.inl rfl), rfl⟩ | exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
      rwa [him]
    exact hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0')

private lemma elim12_M_disjoint_exits {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {y0 y1 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y1)
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y0) (S z))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) (S y1) (S z))
    (h_Q_H_disj : ∀ Q : Finset (Fin n),
      Q ⊆ {cyc0.toFun 0, cyc0.toFun 1, cyc0.toFun 2, cyc0.toFun 3} →
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
         ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
        IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O))) →
      ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q)
    (hO01_nadj : ∀ a ∈ ({cyc0.toFun 4, y0, y1} : Finset (Fin n)) ∩ (hullVertices S \ certifiedVertices S w),
      ∀ b ∈ ({cyc0.toFun 4, y0, y1} : Finset (Fin n)) ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b)
    (hΓM : ∀ p ∈ ({cyc0.toFun 1, cyc0.toFun 2} : Finset (Fin n)),
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ {cyc0.toFun 4, y0, y1})) ∧
      SegmentsCross (w (Finset.univ \ {cyc0.toFun 4, y0, y1})) (S p) (S y0) (S y1) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S p) H_hp))
    (hcapM : ∀ (z : Fin n), z ≠ y0 → z ≠ y1 → z ∉ ({cyc0.toFun 4, y0, y1} : Finset (Fin n)) →
      S z ∈ convexHull ℝ ((({cyc0.toFun 1, cyc0.toFun 2} ∪ {y0, y1} : Finset (Fin n)).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) →
      SegmentsCross (w (Finset.univ \ {cyc0.toFun 4, y0, y1})) (S z) (S y0) (S y1) ∧
      (∃ H_hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S z) H_hp) ∧
      (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z (w (Finset.univ \ {cyc0.toFun 4, y0, y1})))) :
    False := by
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  let d0 := cyc0.toFun 0; let d1 := cyc0.toFun 1; let d2 := cyc0.toFun 2
  let d3 := cyc0.toFun 3; let d4 := cyc0.toFun 4
  let Q : Finset (Fin n) := {d1, d2}
  let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
  have hd01 : d0 ≠ d1 := cyc0.inj.ne (by decide)
  have hd02 : d0 ≠ d2 := cyc0.inj.ne (by decide)
  have hd12 : d1 ≠ d2 := cyc0.inj.ne (by decide)
  have hd13 : d1 ≠ d3 := cyc0.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cyc0.inj.ne (by decide)
  have hd23 : d2 ≠ d3 := cyc0.inj.ne (by decide)
  have hd24 : d2 ≠ d4 := cyc0.inj.ne (by decide)
  have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    have hpM := hΓM p (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact hp)
    refine ⟨{d4, y0, y1}, ?_, hO01_nadj, hpM.1⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases hp with rfl | rfl
    · exact ⟨hd14, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 1), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 1)⟩
    · exact ⟨hd24, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 2), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 2)⟩
  have hd0F : d0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 0, by simp [Q, hd01, hd02]⟩)
  have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 3, by simp [Q, hd13.symm, hd23.symm]⟩)
  have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cyc0 4, by simp [Q, hd14.symm, hd24.symm]⟩)
  have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cyc0 _)
    (Finset.card_pair hd12) y0 y1 hy0M hy1M hy01 hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      exact hex_lift_hp hy0F hy1F (hΓM p (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact hp)).2.2)
    (h_Q_H_disj Q (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d1, d2]) hBackQ)
    (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hny01 : z ≠ y0 ∧ z ≠ y1 := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact hm
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cyc0.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
    have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
      ext p; simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, pD]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨cyc0.toFun i, ccwCycle_mem cyc0 i, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hcr := cyc0.image_eq; dsimp [D] at hcr
        have hx' : x ∈ hullVertices S \ certifiedVertices S w := hx
        rw [← hcr] at hx'
        rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
    rw [hr]; exact hzD_conv
  have hcov := convD_cover_case3a_M pD cyc0.ccw (S y0) (S y1) (F.image S : Set (ℝ × ℝ))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd0F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
  rcases hcov with ((hF | he0) | he1) | hcM
  · exact Or.inr hF
  · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
  · exact False.elim (hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1))
  · left
    have hset : ({S y0, pD 1, pD 2, S y1} : Set (ℝ × ℝ)) =
        ((({cyc0.toFun 1, cyc0.toFun 2} ∪ {y0, y1} : Finset (Fin n)).image S : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
      have hu : ({cyc0.toFun 1, cyc0.toFun 2} ∪ {y0, y1} : Finset (Fin n)) = {y0, cyc0.toFun 1, cyc0.toFun 2, y1} := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => by rcases h with (rfl | rfl) | (rfl | rfl) <;> tauto,
               fun h => by rcases h with rfl | rfl | rfl | rfl <;> tauto⟩
      rw [hu, finset4_image_eq]
    rw [hset] at hcM
    have hc := hcapM z hny01.1 hny01.2 (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cyc0 4), hny01.1, hny01.2⟩) hcM
    exact hex_lift_hp hy0F hy1F hc.2.1

private lemma pentagon_disjoint_exits_core {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cyc0 : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (hy0_ex : 0 < orient2D (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
      ∃ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y))
    (hy1_ex : 0 < orient2D (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) (w (hullVertices S \ certifiedVertices S w)) ∧
      ∃ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cyc0.toFun 2)) (S (cyc0.toFun 3)) (S y)) :
    False := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  let d0 := cyc0.toFun 0
  let d1 := cyc0.toFun 1
  let d2 := cyc0.toFun 2
  let d3 := cyc0.toFun 3
  let d4 := cyc0.toFun 4
  have hD_sub_B : D ⊆ B := Finset.sdiff_subset
  have hD5' : D.card = 5 := hD5
  have hD3 : 3 ≤ D.card := by omega
  have hd01 : d0 ≠ d1 := cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1)
  have hd02 : d0 ≠ d2 := cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2)
  have hd03 : d0 ≠ d3 := cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 3)
  have hd04 : d0 ≠ d4 := cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 4)
  have hd12 : d1 ≠ d2 := cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 2)
  have hd13 : d1 ≠ d3 := cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 3)
  have hd14 : d1 ≠ d4 := cyc0.inj.ne (by decide : (1 : Fin 5) ≠ 4)
  have hd23 : d2 ≠ d3 := cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 3)
  have hd24 : d2 ≠ d4 := cyc0.inj.ne (by decide : (2 : Fin 5) ≠ 4)
  have hd34 : d3 ≠ d4 := cyc0.inj.ne (by decide : (3 : Fin 5) ≠ 4)
  obtain ⟨y0, hy0M, hy0_tri, hy0_W, h_not_lr01, hy0_empty⟩ :=
    minimal_on_exit_edge hPoly h25 cyc0 0 hy0_ex.1 hy0_ex.2
  obtain ⟨y1, hy1M, hy1_tri, hy1_W, h_not_lr23, hy1_empty⟩ :=
    minimal_on_exit_edge hPoly h25 cyc0 2 hy1_ex.1 hy1_ex.2
  have hy01 : y0 ≠ y1 := by
    intro h; subst h
    obtain ⟨uy, vy, _, _, _, _, _, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
    obtain ⟨rfl, rfl⟩ := h_uniq d0 d1 (ccwCycle_isCCWEdge cyc0 0) hy0_ex.1 hy0_tri.to_convexHull
    obtain ⟨h02, _⟩ := h_uniq d2 d3 (ccwCycle_isCCWEdge cyc0 2) hy1_ex.1 hy1_tri.to_convexHull
    exact cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 2) h02.symm
  have h_Q_H_disj : ∀ Q : Finset (Fin n),
      (Q ⊆ {d0, d1, d2, d3}) →
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O))) →
      ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q := by
    intro Q hQsub hQback l r hHne hed hHneg
    rw [isCCWEdge_iff_ccwCycle cyc0] at hed
    rcases hed with ⟨il, rfl, rfl⟩
    have h_opp := opposite_endpoint_exit hPoly h25 hD5 hM5 cyc0 il hHne hHneg
    have h_forbid_end : ∀ p y : Fin n,
        (p = cyc0.toFun il ∧ y = cyc0.toFun (il + 1) ∨
         p = cyc0.toFun (il + 1) ∧ y = cyc0.toFun il) →
        (∃ O : Finset (Fin n), p ∉ O ∧
          (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
          IsBackVertexOf S B p (w (Finset.univ \ O))) →
        ∀ h ∈ H, ∀ u v : Fin n, IsCCWEdge S D u v → InIntTri (w D) (S u) (S v) (S h) →
          (u = y ∨ v = y) := fun p y hpy hback =>
      (h25.endpoint_back_criterion hHne (by omega)
        (cyc0.toFun il) (cyc0.toFun (il + 1)) p y
        (ccwCycle_mem cyc0 il) (ccwCycle_mem cyc0 (il + 1))
        (cyc0.inj.ne (fin_add_one_ne_self il)) (ccwCycle_isCCWEdge cyc0 il)
        hHneg hpy hback).1
    have h_e_of_H : ∀ h ∈ H, ∃ ih : Fin 5,
        InIntTri (w D) (S (cyc0.toFun ih)) (S (cyc0.toFun (ih + 1))) (S h) ∧
        (∀ x ∈ WitnessSet {cyc0.toFun ih, cyc0.toFun (ih + 1)} ∅ w,
          InIntTri x (S (cyc0.toFun ih)) (S (cyc0.toFun (ih + 1))) (S h)) ∧
        ih ≠ il := by
      intro h hh
      have hhM : h ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh⟩
      obtain ⟨u, v, hed_h, _, hin_h, hnot_h, hW_h, _⟩ := h25.exit_edge_lemma hD3 h hhM
      rw [isCCWEdge_iff_ccwCycle cyc0] at hed_h
      rcases hed_h with ⟨ih, rfl, rfl⟩
      refine ⟨ih, hin_h, hW_h, fun heq => ?_⟩
      subst heq
      exact hnot_h _ _ hHne (ccwCycle_isCCWEdge cyc0 ih) hHneg rfl
    have h4_not_Q : cyc0.toFun 4 ∉ Q := fun hmem => by
      have hsub := hQsub hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
      rcases hsub with h | h | h | h
      · exact cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 0) h
      · exact cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 1) h
      · exact cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 2) h
      · exact cyc0.inj.ne (by decide : (4 : Fin 5) ≠ 3) h
    fin_cases il
    · exact False.elim (h_not_lr01 _ _ hHne (ccwCycle_isCCWEdge cyc0 0) hHneg rfl)
    · refine ⟨fun h1Q => ?_, fun h2Q => ?_⟩
      · apply h_opp.1.elim ⟨?_, y0, hy0M, by simpa using hy0_tri⟩
        intro h hh
        obtain ⟨ih, hin, hW, hne⟩ := h_e_of_H h hh
        have hinc := h_forbid_end (cyc0.toFun 1) (cyc0.toFun 2) (Or.inl ⟨rfl, rfl⟩) (hQback _ h1Q)
          h hh (cyc0.toFun ih) (cyc0.toFun (ih + 1)) (ccwCycle_isCCWEdge cyc0 ih) hin
        have hih2 : ih = 2 := by
          rcases hinc with e | e
          · exact cyc0.inj e
          · exfalso; apply hne
            have he1 : ih + 1 = 2 := cyc0.inj e
            calc ih = (ih + 1) - 1 := by abel
              _ = 2 - 1 := by rw [he1]
              _ = 1 := by decide
        subst hih2
        exact ⟨by simpa using hin, fun x hx => by simpa using hW x hx⟩
      · apply h_opp.2.elim ⟨?_, y1, hy1M, by simpa using hy1_tri⟩
        intro h hh
        obtain ⟨ih, hin, hW, hne⟩ := h_e_of_H h hh
        have hinc := h_forbid_end (cyc0.toFun 2) (cyc0.toFun 1) (Or.inr ⟨rfl, rfl⟩) (hQback _ h2Q)
          h hh (cyc0.toFun ih) (cyc0.toFun (ih + 1)) (ccwCycle_isCCWEdge cyc0 ih) hin
        have hih0 : ih = 0 := by
          rcases hinc with e | e
          · exact False.elim (hne (cyc0.inj e))
          · have he1 : ih + 1 = 1 := cyc0.inj e
            exact calc ih = (ih + 1) - 1 := by abel
              _ = 1 - 1 := by rw [he1]
              _ = 0 := by decide
        subst hih0
        exact ⟨by simpa using hin, fun x hx => by simpa using hW x hx⟩
    · exact False.elim (h_not_lr23 _ _ hHne (ccwCycle_isCCWEdge cyc0 2) hHneg rfl)
    · refine ⟨fun h3Q => ?_, h4_not_Q⟩
      apply h_opp.1.elim ⟨?_, y1, hy1M, by simpa using hy1_tri⟩
      intro h hh
      obtain ⟨ih, hin, hW, hne⟩ := h_e_of_H h hh
      have hinc := h_forbid_end (cyc0.toFun 3) (cyc0.toFun 4) (Or.inl ⟨rfl, rfl⟩) (hQback _ h3Q)
        h hh (cyc0.toFun ih) (cyc0.toFun (ih + 1)) (ccwCycle_isCCWEdge cyc0 ih) hin
      have hih4 : ih = 4 := by
        rcases hinc with e | e
        · exact cyc0.inj e
        · exfalso; apply hne
          have he1 : ih + 1 = 4 := cyc0.inj e
          calc ih = (ih + 1) - 1 := by abel
            _ = 4 - 1 := by rw [he1]
            _ = 3 := by decide
      subst hih4
      exact ⟨by simpa using hin, fun x hx => by simpa using hW x hx⟩
    · refine ⟨h4_not_Q, fun h0Q => ?_⟩
      apply h_opp.2.elim ⟨?_, y0, hy0M, by simpa using hy0_tri⟩
      intro h hh
      obtain ⟨ih, hin, hW, hne⟩ := h_e_of_H h hh
      have hinc := h_forbid_end (cyc0.toFun 0) (cyc0.toFun 4) (Or.inr ⟨rfl, rfl⟩) (hQback _ h0Q)
        h hh (cyc0.toFun ih) (cyc0.toFun (ih + 1)) (ccwCycle_isCCWEdge cyc0 ih) hin
      have hih3 : ih = 3 := by
        rcases hinc with e | e
        · exact False.elim (hne (cyc0.inj e))
        · have he1 : ih + 1 = 4 := cyc0.inj e
          exact calc ih = (ih + 1) - 1 := by abel
            _ = 4 - 1 := by rw [he1]
            _ = 3 := by decide
      subst hih3
      exact ⟨by simpa using hin, fun x hx => by simpa using hW x hx⟩
  have hO0_nadj : ∀ a ∈ ({d4, y0, d2} : Finset (Fin n)) ∩ D,
      ∀ b ∈ ({d4, y0, d2} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b :=
    pentagon_Ostar_nadj h25 hD5 cyc0 (Finset.mem_sdiff.mp hy0M).2 4 2 (by decide) (by decide)
  have hO1_nadj : ∀ a ∈ ({d1, y1, d4} : Finset (Fin n)) ∩ D,
      ∀ b ∈ ({d1, y1, d4} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b :=
    pentagon_Ostar_nadj h25 hD5 cyc0 (Finset.mem_sdiff.mp hy1M).2 1 4 (by decide) (by decide)
  obtain ⟨_, oa0, ob0, Γ0, hcases0, _, hΓ0, hcap0⟩ :=
    pentagon_interior_anchor_2 hPoly h25 hD5 hM5 cyc0 hy0M 0
      ⟨hy0_ex.1, hy0_tri, hy0_W, h_not_lr01⟩
  obtain ⟨_, oa1, ob1, Γ1, hcases1, _, hΓ1, hcap1⟩ :=
    pentagon_interior_anchor_2 hPoly h25 hD5 hM5 cyc0 hy1M 2
      ⟨hy1_ex.1, hy1_tri, hy1_W, h_not_lr23⟩
  have mk_cap0 : ∀ (hoa : oa0 = d4 ∧ ob0 = y0 ∧ Γ0 = {d0}),
      (∃ O, d0 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d0 (w (Finset.univ \ O))) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S d0) Hp) ∧
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d0, S d4, S y0} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S z) Hp) := by
    rintro ⟨hoa, hob, hΓeq⟩
    have h0 := hΓ0 d0 (by rw [hΓeq]; exact Finset.mem_singleton_self _)
    rw [hoa, hob] at h0
    refine ⟨⟨{d4, y0, d2}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd04, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 0), hd02⟩, hO0_nadj, h0.1⟩,
      h0.2.2, fun z hznD hny0 _ hconv => ?_⟩
    have hc := hcap0 z (by rw [hoa]; exact fun h => hznD (h ▸ ccwCycle_mem cyc0 4)) (by rw [hob]; exact hny0) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hznD (h ▸ ccwCycle_mem cyc0 4), hny0, fun h => hznD (h ▸ ccwCycle_mem cyc0 2)⟩) (by
      rw [hoa, hob, hΓeq]
      have hset : ({S d0, S d4, S y0} : Set (ℝ × ℝ)) = (({d0} ∪ {d4, y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        rw [Finset.singleton_union, finset3_image_eq]
      rwa [← hset])
    rw [hoa, hob] at hc; exact hc.2.1
  have mk_cap1 : ∀ (hoa : oa0 = y0 ∧ ob0 = d2 ∧ Γ0 = {d1}),
      (∃ O, d1 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d1 (w (Finset.univ \ O))) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, d2} ∅ w) (S d1) Hp) ∧
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d1, S y0, S d2} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, d2} ∅ w) (S z) Hp) := by
    rintro ⟨hoa, hob, hΓeq⟩
    have h1 := hΓ0 d1 (by rw [hΓeq]; exact Finset.mem_singleton_self _)
    rw [hoa, hob] at h1
    refine ⟨⟨{d4, y0, d2}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd14, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 1), hd12⟩, hO0_nadj, h1.1⟩,
      h1.2.2, fun z hznD hny0 _ hconv => ?_⟩
    have hc := hcap0 z (by rw [hoa]; exact hny0) (by rw [hob]; exact fun h => hznD (h ▸ ccwCycle_mem cyc0 2)) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hznD (h ▸ ccwCycle_mem cyc0 4), hny0, fun h => hznD (h ▸ ccwCycle_mem cyc0 2)⟩) (by
      rw [hoa, hob, hΓeq]
      have hset : ({S d1, S y0, S d2} : Set (ℝ × ℝ)) = (({d1} ∪ {y0, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        rw [Finset.singleton_union, finset3_image_eq]
      rwa [← hset])
    rw [hoa, hob] at hc; exact hc.2.1
  have mk_cap2 : ∀ (hoa : oa1 = d1 ∧ ob1 = y1 ∧ Γ1 = {d2}),
      (∃ O, d2 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d2 (w (Finset.univ \ O))) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {d1, y1} ∅ w) (S d2) Hp) ∧
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d2, S d1, S y1} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {d1, y1} ∅ w) (S z) Hp) := by
    rintro ⟨hoa, hob, hΓeq⟩
    have h2 := hΓ1 d2 (by rw [hΓeq]; exact Finset.mem_singleton_self _)
    rw [hoa, hob] at h2
    refine ⟨⟨{d1, y1, d4}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd12.symm, fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 2), hd24⟩, hO1_nadj, h2.1⟩,
      h2.2.2, fun z hznD _ hny1 hconv => ?_⟩
    have hc := hcap1 z (by rw [hoa]; exact fun h => hznD (h ▸ ccwCycle_mem cyc0 1)) (by rw [hob]; exact hny1) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hznD (h ▸ ccwCycle_mem cyc0 1), hny1, fun h => hznD (h ▸ ccwCycle_mem cyc0 4)⟩) (by
      rw [hoa, hob, hΓeq]
      have hset : ({S d2, S d1, S y1} : Set (ℝ × ℝ)) = (({d2} ∪ {d1, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        rw [Finset.singleton_union, finset3_image_eq]
      rwa [← hset])
    rw [hoa, hob] at hc; exact hc.2.1
  have mk_cap3 : ∀ (hoa : oa1 = y1 ∧ ob1 = d4 ∧ Γ1 = {d3}),
      (∃ O, d3 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d3 (w (Finset.univ \ O))) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d4} ∅ w) (S d3) Hp) ∧
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d3, S y1, S d4} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d4} ∅ w) (S z) Hp) := by
    rintro ⟨hoa, hob, hΓeq⟩
    have h3 := hΓ1 d3 (by rw [hΓeq]; exact Finset.mem_singleton_self _)
    rw [hoa, hob] at h3
    refine ⟨⟨{d1, y1, d4}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd13.symm, fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 3), hd34⟩, hO1_nadj, h3.1⟩,
      h3.2.2, fun z hznD _ hny1 hconv => ?_⟩
    have hc := hcap1 z (by rw [hoa]; exact hny1) (by rw [hob]; exact fun h => hznD (h ▸ ccwCycle_mem cyc0 4)) (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hznD (h ▸ ccwCycle_mem cyc0 1), hny1, fun h => hznD (h ▸ ccwCycle_mem cyc0 4)⟩) (by
      rw [hoa, hob, hΓeq]
      have hset : ({S d3, S y1, S d4} : Set (ℝ × ℝ)) = (({d3} ∪ {y1, d4} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        rw [Finset.singleton_union, finset3_image_eq]
      rwa [← hset])
    rw [hoa, hob] at hc; exact hc.2.1
  rcases hcases0 with c0 | c1 <;> rcases hcases1 with c2 | c3
  · obtain ⟨h0b, h0hp, h0cap⟩ := mk_cap0 c0
    obtain ⟨h2b, h2hp, h2cap⟩ := mk_cap2 c2
    exact elim02_disjoint_exits hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty h_Q_H_disj h0b h0hp h0cap h2b h2hp h2cap
  · obtain ⟨h0b, h0hp, h0cap⟩ := mk_cap0 c0
    obtain ⟨h3b, h3hp, h3cap⟩ := mk_cap3 c3
    exact elim03_disjoint_exits hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty h_Q_H_disj h0b h0hp h0cap h3b h3hp h3cap
  · obtain ⟨h1b, h1hp, h1cap⟩ := mk_cap1 c1
    obtain ⟨h2b, h2hp, h2cap⟩ := mk_cap2 c2
    have hO01_nadj : ∀ a ∈ ({d4, y0, y1} : Finset (Fin n)) ∩ D,
        ∀ b ∈ ({d4, y0, y1} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b := by
      intro a ha b hb hed
      have haD := (Finset.mem_inter.mp ha).2; have hbD := (Finset.mem_inter.mp hb).2
      have ha4 : a = d4 := by
        rcases (by simpa using (Finset.mem_inter.mp ha).1 : a = d4 ∨ a = y0 ∨ a = y1) with rfl | rfl | rfl
        · rfl
        · exact False.elim ((Finset.mem_sdiff.mp hy0M).2 haD)
        · exact False.elim ((Finset.mem_sdiff.mp hy1M).2 haD)
      have hb4 : b = d4 := by
        rcases (by simpa using (Finset.mem_inter.mp hb).1 : b = d4 ∨ b = y0 ∨ b = y1) with rfl | rfl | rfl
        · rfl
        · exact False.elim ((Finset.mem_sdiff.mp hy0M).2 hbD)
        · exact False.elim ((Finset.mem_sdiff.mp hy1M).2 hbD)
      exact hed.2.2.1 (ha4.trans hb4.symm)
    obtain ⟨oaM, obM, ΓM, hcasesM, _, hΓM, hcapM⟩ :=
      pairs_in_M hPoly h25 rfl cyc0 hy0M hy1M hy01
        (hy0_W (w (Finset.univ \ {d4, y0, y1})) ⟨Finset.univ \ {d4, y0, y1}, fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          rcases hx with rfl | rfl
          · exact ⟨hd04, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 0), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 0)⟩
          · exact ⟨hd14, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 1), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 1)⟩,
          Finset.disjoint_empty_right _, rfl⟩)
        (hy1_W (w (Finset.univ \ {d4, y0, y1})) ⟨Finset.univ \ {d4, y0, y1}, fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          rcases hx with rfl | rfl
          · exact ⟨hd24, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 2), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 2)⟩
          · exact ⟨hd34, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 3), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 3)⟩,
          Finset.disjoint_empty_right _, rfl⟩)
        (fun l r hH hed hHn => ⟨h_not_lr01 l r hH hed hHn, h_not_lr23 l r hH hed hHn⟩)
    rcases hcasesM with ⟨hoa, hob, hΓeq⟩ | ⟨hoa, hob, hΓeq⟩ | ⟨hoa, hob, hΓeq⟩
    · have h0 := hΓM d0 (by rw [hΓeq]; exact Finset.mem_singleton_self _)
      rw [hoa, hob] at h0
      refine elim02_disjoint_exits hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty h_Q_H_disj
        ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd04, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 0), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 0)⟩, hO01_nadj, h0.1⟩
        h0.2.2 (fun z hznD hny0 hny1 hconv => by
          have hc := hcapM z (by rw [hoa]; exact fun h => hznD (h ▸ ccwCycle_mem cyc0 4)) (by rw [hob]; exact hny0) (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hznD (h ▸ ccwCycle_mem cyc0 4), hny0, hny1⟩) (by
            rw [hoa, hob, hΓeq]
            have hset : ({S d0, S d4, S y0} : Set (ℝ × ℝ)) = (({d0} ∪ {d4, y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
              rw [Finset.singleton_union, finset3_image_eq]
            rwa [← hset])
          rw [hoa, hob] at hc; exact hc.2.1)
        h2b h2hp h2cap
    · refine elim12_M_disjoint_exits hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty h_Q_H_disj
        hO01_nadj (fun p hp => by have h := hΓM p (hΓeq ▸ hp); rwa [hoa, hob] at h)
        (fun z hzy0 hzy1 hzO hzconv => by
          have hc := hcapM z (hoa.symm ▸ hzy0) (hob.symm ▸ hzy1) hzO (by rwa [hoa, hob, hΓeq])
          rwa [hoa, hob] at hc)
    · have h3 := hΓM d3 (by rw [hΓeq]; exact Finset.mem_singleton_self _)
      rw [hoa, hob] at h3
      refine elim13_disjoint_exits hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty h_Q_H_disj h1b h1hp h1cap
        ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd34, fun h => (Finset.mem_sdiff.mp hy0M).2 (h ▸ ccwCycle_mem cyc0 3), fun h => (Finset.mem_sdiff.mp hy1M).2 (h ▸ ccwCycle_mem cyc0 3)⟩, hO01_nadj, h3.1⟩
        h3.2.2 (fun z hznD hny0 hny1 hconv => by
          have hc := hcapM z (by rw [hoa]; exact hny1) (by rw [hob]; exact fun h => hznD (h ▸ ccwCycle_mem cyc0 4)) (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hznD (h ▸ ccwCycle_mem cyc0 4), hny0, hny1⟩) (by
            rw [hoa, hob, hΓeq]
            have hset : ({S d3, S y1, S d4} : Set (ℝ × ℝ)) = (({d3} ∪ {y1, d4} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
              rw [Finset.singleton_union, finset3_image_eq]
            rwa [← hset])
          rw [hoa, hob] at hc; exact hc.2.1)
  · obtain ⟨h1b, h1hp, h1cap⟩ := mk_cap1 c1
    obtain ⟨h3b, h3hp, h3cap⟩ := mk_cap3 c3
    exact elim13_disjoint_exits hPoly h25 hD5 hM5 cyc0 hy0M hy1M hy01 hy0_empty hy1_empty h_Q_H_disj h1b h1hp h1cap h3b h3hp h3cap

/-- **Section 8.4 Disjoint Exit Edges Elimination (`upper_9.tex` lines 1001–1007)**:
    For a pentagon `D` (`|D| = 5`, `|M| = 5`), no two points of `M` can exit across disjoint
    edges of `conv D`. Consequently, `{e(y) : y ∈ M}` is contained in two adjacent edges `{il, il+1}`
    and `{il+1, il+2}` (and up to cyclic relabeling, `{e(y) : y ∈ M} ⊆ {01, 12}`). -/
theorem pentagon_disjoint_exits_elim {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (i1 i2 : Fin 5) (hdisj : i1 ≠ i2 ∧ i2 ≠ i1 + 1 ∧ i1 ≠ i2 + 1)
    (hy1 : 0 < orient2D (S (cycD.toFun i1)) (S (cycD.toFun (i1 + 1))) (w (hullVertices S \ certifiedVertices S w)) ∧
      ∃ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i1)) (S (cycD.toFun (i1 + 1))) (S y))
    (hy2 : 0 < orient2D (S (cycD.toFun i2)) (S (cycD.toFun (i2 + 1))) (w (hullVertices S \ certifiedVertices S w)) ∧
      ∃ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun i2)) (S (cycD.toFun (i2 + 1))) (S y)) :
    False := by
  have hcase : i2 = i1 + 2 ∨ i1 = i2 + 2 := by
    let d : Fin 5 := i2 - i1
    have hdv : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 ∨ d.val = 4 := by omega
    rcases hdv with h0 | h1 | h2 | h3 | h4
    · exact False.elim (hdisj.1 (sub_eq_zero.mp (Fin.ext h0)).symm)
    · exact False.elim (hdisj.2.1 ((by calc i2 = (i2 - i1) + i1 := by abel
      _ = 1 + i1 := congrArg (· + i1) (Fin.ext h1)
      _ = i1 + 1 := add_comm _ _)))
    · left; exact eq_add_of_sub_eq' (Fin.ext h2)
    · right
      have hd3 : d = 3 := Fin.ext h3
      have h12 : i1 - i2 = 2 := by
        calc i1 - i2 = -(i2 - i1) := by abel
          _ = -(3 : Fin 5) := congrArg Neg.neg hd3
          _ = 2 := by decide
      exact eq_add_of_sub_eq' h12
    · exact False.elim (hdisj.2.2 (by
        have hsub : i2 - i1 = (-1 : Fin 5) := Fin.ext h4
        calc i1 = i2 - (-1 : Fin 5) := by rw [← hsub]; abel
          _ = i2 + 1 := by abel))
  rcases hcase with h2 | h1
  · subst h2
    exact pentagon_disjoint_exits_core hPoly h25 hD5 hM5 (ccwCycle_shift cycD i1)
      (by simpa [ccwCycle_shift] using hy1) (by simpa [ccwCycle_shift, add_assoc] using hy2)
  · subst h1
    exact pentagon_disjoint_exits_core hPoly h25 hD5 hM5 (ccwCycle_shift cycD i2)
      (by simpa [ccwCycle_shift] using hy2) (by simpa [ccwCycle_shift, add_assoc] using hy1)

/-- Consequence of `pentagon_disjoint_exits_elim`: for any `10`-point shattered polygon with
    `|D| = 5`, `|M| = 5`, there is an anchor rotation `il : Fin 5` such that EVERY `y ∈ M` exits
    `D` through `(cycD il, cycD (il+1))` or `(cycD (il+1), cycD (il+2))`. -/
theorem pentagon_exits_adjacent_pair {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2) :
    ∃ il : Fin 5, ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun il)) (S (cycD.toFun (il + 1))) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun il)) (S (cycD.toFun (il + 1))) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun il, cycD.toFun (il + 1)} ∅ w,
          InIntTri x (S (cycD.toFun il)) (S (cycD.toFun (il + 1))) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun il, cycD.toFun (il + 1)) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun (il + 1), cycD.toFun (il + 2)} ∅ w,
          InIntTri x (S (cycD.toFun (il + 1))) (S (cycD.toFun (il + 2))) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun (il + 1), cycD.toFun (il + 2)) ≠ (l, r))) := by
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  have hD5' : D.card = 5 := hD5
  have hM5' : 5 ≤ M.card := hM5
  have hD3 : 3 ≤ D.card := by omega
  have h_ex_edge : ∀ y ∈ M, ∃ i : Fin 5,
      0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (w D) ∧
      InIntTri (w D) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y) ∧
      (∀ x ∈ WitnessSet {cycD.toFun i, cycD.toFun (i + 1)} ∅ w,
        InIntTri x (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun i, cycD.toFun (i + 1)) ≠ (l, r)) := by
    intro y hy
    obtain ⟨u, v, hed, hnf, hin, hnot_lr, hW, _⟩ := h25.exit_edge_lemma hD3 y hy
    rw [isCCWEdge_iff_ccwCycle cycD] at hed
    rcases hed with ⟨i, rfl, rfl⟩
    exact ⟨i, hnf, hin, hW, hnot_lr⟩
  let used : Fin 5 → Prop := fun i =>
    0 < orient2D (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (w D) ∧
    ∃ y ∈ M, InIntTri (w D) (S (cycD.toFun i)) (S (cycD.toFun (i + 1))) (S y)
  have hno_disj : ∀ i1 i2 : Fin 5, used i1 → used i2 → ¬ (i1 ≠ i2 ∧ i2 ≠ i1 + 1 ∧ i1 ≠ i2 + 1) :=
    fun i1 i2 h1 h2 hd => pentagon_disjoint_exits_elim hPoly h25 hD5 hM5 cycD i1 i2 hd h1 h2
  obtain ⟨y_any, hy_any⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  obtain ⟨i0, hi0_nf, hi0_in, _, _⟩ := h_ex_edge y_any hy_any
  have hu0 : used i0 := ⟨hi0_nf, y_any, hy_any, hi0_in⟩
  by_cases hu_prev : used (i0 - 1)
  · refine ⟨i0 - 1, fun y hy => ?_⟩
    obtain ⟨iy, hynf, hyin, hyW, hynot⟩ := h_ex_edge y hy
    have huy : used iy := ⟨hynf, y, hy, hyin⟩
    have hn1 := hno_disj i0 iy hu0 huy
    have hn2 := hno_disj (i0 - 1) iy hu_prev huy
    have hcases : iy = i0 - 1 ∨ iy = i0 := by
      let d : Fin 5 := iy - i0
      have hdv : d.val = 0 ∨ d.val = 1 ∨ d.val = 2 ∨ d.val = 3 ∨ d.val = 4 := by omega
      rcases hdv with h0 | h1 | h2 | h3 | h4
      · right; exact (sub_eq_zero.mp (Fin.ext h0))
      · exfalso; apply hn2
        have hiy : iy = i0 + 1 := by
          calc iy = (iy - i0) + i0 := by abel
            _ = 1 + i0 := congrArg (· + i0) (Fin.ext h1)
            _ = i0 + 1 := add_comm _ _
        refine ⟨fun h => absurd (add_left_cancel (by
            calc i0 + 4 = i0 - 1 := by abel
              _ = iy := h
              _ = i0 + 1 := hiy)) (by decide),
          fun h => absurd (add_left_cancel (by
            calc i0 + 1 = iy := hiy.symm
              _ = (i0 - 1) + 1 := h
              _ = i0 + 0 := by abel)) (by decide),
          fun h => absurd (add_left_cancel (by
            calc i0 + 4 = i0 - 1 := by abel
              _ = iy + 1 := h
              _ = (i0 + 1) + 1 := by rw [hiy]
              _ = i0 + 2 := by abel)) (by decide)⟩
      · exfalso; apply hn1
        have hiy : iy = i0 + 2 := eq_add_of_sub_eq' (Fin.ext h2)
        refine ⟨fun h => absurd (add_left_cancel (by
            calc i0 + 2 = iy := hiy.symm
              _ = i0 := h.symm
              _ = i0 + 0 := (add_zero i0).symm)) (by decide),
          fun h => absurd (add_left_cancel (hiy.symm.trans h)) (by decide),
          fun h => absurd (add_left_cancel (by
            calc i0 + 0 = i0 := add_zero i0
              _ = iy + 1 := h
              _ = (i0 + 2) + 1 := by rw [hiy]
              _ = i0 + 3 := by abel)) (by decide)⟩
      · exfalso; apply hn1
        have hiy : iy = i0 + 3 := eq_add_of_sub_eq' (Fin.ext h3)
        refine ⟨fun h => absurd (add_left_cancel (by
            calc i0 + 3 = iy := hiy.symm
              _ = i0 := h.symm
              _ = i0 + 0 := (add_zero i0).symm)) (by decide),
          fun h => absurd (add_left_cancel (hiy.symm.trans h)) (by decide),
          fun h => absurd (add_left_cancel (by
            calc i0 + 0 = i0 := add_zero i0
              _ = iy + 1 := h
              _ = (i0 + 3) + 1 := by rw [hiy]
              _ = i0 + 4 := by abel)) (by decide)⟩
      · left
        have hiy : iy = i0 + 4 := eq_add_of_sub_eq' (Fin.ext h4)
        rw [hiy]; abel
    rcases hcases with hiy | hiy
    · left; rw [← hiy]; exact ⟨hynf, hyin, hyW, hynot⟩
    · right
      have he1 : (i0 - 1 : Fin 5) + 1 = i0 := by abel
      have he2 : (i0 - 1 : Fin 5) + 2 = i0 + 1 := by
        calc (i0 - 1 : Fin 5) + 2 = (i0 - 1) + 1 + 1 := by rw [add_assoc]; rfl
          _ = i0 + 1 := by abel
      rw [he1, he2, ← hiy]; exact ⟨hynf, hyin, hyW, hynot⟩
  · refine ⟨i0, fun y hy => ?_⟩
    obtain ⟨iy, hynf, hyin, hyW, hynot⟩ := h_ex_edge y hy
    have huy : used iy := ⟨hynf, y, hy, hyin⟩
    have hn1 := hno_disj i0 iy hu0 huy
    have hcases : iy = i0 ∨ iy = i0 + 1 := by
      by_contra hbad; push Not at hbad
      by_cases hip : iy = i0 - 1
      · subst hip; exact hu_prev huy
      · exact hn1 ⟨Ne.symm hbad.1, hbad.2, fun heq => hip (by rw [heq]; abel)⟩
    rcases hcases with hiy | hiy
    · left; rw [← hiy]; exact ⟨hynf, hyin, hyW, hynot⟩
    · right
      have h12 : i0 + 2 = (i0 + 1) + 1 := by rw [add_assoc]; rfl
      rw [h12, ← hiy]; exact ⟨hynf, hyin, hyW, hynot⟩

private lemma adj_pair_H_disj {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    (h_no01 : (certifiedVertices S w).Nonempty → ∀ l r : Fin n,
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))
    {Q : Finset (Fin n)}
    (h_two_forbid : cycD.toFun 2 ∈ Q → (certifiedVertices S w).Nonempty → ∀ l r : Fin n,
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))
    (hQ_back : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ (hullVertices S \ certifiedVertices S w),
        ∀ b ∈ O ∩ (hullVertices S \ certifiedVertices S w), ¬ IsCCWEdge S (hullVertices S) a b) ∧
      IsBackVertexOf S (hullVertices S) p (w (Finset.univ \ O)))
    (hQ_23_or_40 :
      (Q ⊆ {cycD.toFun 0, cycD.toFun 1, cycD.toFun 2}) ∨
      (Q = {cycD.toFun 2, cycD.toFun 3}) ∨
      (Q = {cycD.toFun 4, cycD.toFun 0})) :
    ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ∉ Q ∧ r ∉ Q := by
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  have hD3 : 3 ≤ D.card := by
    have h5 : D.card = 5 := hD5
    omega
  have hD5' : 5 ≤ D.card := le_of_eq hD5.symm
  intro l r hHne hed hHneg
  rw [isCCWEdge_iff_ccwCycle cycD] at hed
  rcases hed with ⟨il, rfl, rfl⟩
  have h_all_H_01_12 : ∀ h ∈ H,
      (IsCCWEdge S D (cycD.toFun 0) (cycD.toFun 1) ∧ InIntTri (w D) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S h)) ∨
      (IsCCWEdge S D (cycD.toFun 1) (cycD.toFun 2) ∧ InIntTri (w D) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S h)) := by
    intro h hh
    have hhM : h ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh⟩
    rcases h_adj h hhM with ⟨_, hin, _, _⟩ | ⟨_, hin, _, _⟩
    · exact Or.inl ⟨ccwCycle_isCCWEdge cycD 0, hin⟩
    · exact Or.inr ⟨ccwCycle_isCCWEdge cycD 1, hin⟩
  have h_forbid_2 : cycD.toFun 2 ∈ Q → il = 2 → False := fun h2Q heq => by
    subst heq
    have h23 : (2 + 1 : Fin 5) = 3 := by decide
    have hep := (h25.endpoint_back_criterion hHne hD5' (cycD.toFun 2) (cycD.toFun 3)
      (cycD.toFun 2) (cycD.toFun 3) (ccwCycle_mem cycD 2) (ccwCycle_mem cycD 3)
      (cycD.inj.ne (by decide)) (by rw [← h23]; exact ccwCycle_isCCWEdge cycD 2)
      (by simpa [h23] using hHneg) (Or.inl ⟨rfl, rfl⟩) (hQ_back _ h2Q)).1
    obtain ⟨h0, hh0⟩ := hHne
    rcases h_all_H_01_12 h0 hh0 with ⟨hed0, hin0⟩ | ⟨hed1, hin1⟩
    · rcases hep h0 hh0 _ _ hed0 hin0 with e | e
      · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 3) e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 3) e
    · rcases hep h0 hh0 _ _ hed1 hin1 with e | e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 3) e
      · exact cycD.inj.ne (by decide : (2 : Fin 5) ≠ 3) e
  have h_forbid_3 : cycD.toFun 3 ∈ Q → il = 3 → False := fun h3Q heq => by
    subst heq
    have h34 : (3 + 1 : Fin 5) = 4 := by decide
    have hep := (h25.endpoint_back_criterion hHne hD5' (cycD.toFun 3) (cycD.toFun 4)
      (cycD.toFun 3) (cycD.toFun 4) (ccwCycle_mem cycD 3) (ccwCycle_mem cycD 4)
      (cycD.inj.ne (by decide)) (by rw [← h34]; exact ccwCycle_isCCWEdge cycD 3)
      (by simpa [h34] using hHneg) (Or.inl ⟨rfl, rfl⟩) (hQ_back _ h3Q)).1
    obtain ⟨h0, hh0⟩ := hHne
    rcases h_all_H_01_12 h0 hh0 with ⟨hed0, hin0⟩ | ⟨hed1, hin1⟩
    · rcases hep h0 hh0 _ _ hed0 hin0 with e | e
      · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 4) e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 4) e
    · rcases hep h0 hh0 _ _ hed1 hin1 with e | e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 4) e
      · exact cycD.inj.ne (by decide : (2 : Fin 5) ≠ 4) e
  have h_forbid_4 : cycD.toFun 4 ∈ Q → il = 3 → False := fun h4Q heq => by
    subst heq
    have h34 : (3 + 1 : Fin 5) = 4 := by decide
    have hep := (h25.endpoint_back_criterion hHne hD5' (cycD.toFun 3) (cycD.toFun 4)
      (cycD.toFun 4) (cycD.toFun 3) (ccwCycle_mem cycD 3) (ccwCycle_mem cycD 4)
      (cycD.inj.ne (by decide)) (by rw [← h34]; exact ccwCycle_isCCWEdge cycD 3)
      (by simpa [h34] using hHneg) (Or.inr ⟨rfl, rfl⟩) (hQ_back _ h4Q)).1
    obtain ⟨h0, hh0⟩ := hHne
    rcases h_all_H_01_12 h0 hh0 with ⟨hed0, hin0⟩ | ⟨hed1, hin1⟩
    · rcases hep h0 hh0 _ _ hed0 hin0 with e | e
      · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 3) e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 3) e
    · rcases hep h0 hh0 _ _ hed1 hin1 with e | e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 3) e
      · exact cycD.inj.ne (by decide : (2 : Fin 5) ≠ 3) e
  have h_forbid_0 : cycD.toFun 0 ∈ Q → il = 4 → False := fun h0Q heq => by
    subst heq
    have h40 : (4 + 1 : Fin 5) = 0 := by decide
    have hep := (h25.endpoint_back_criterion hHne hD5' (cycD.toFun 4) (cycD.toFun 0)
      (cycD.toFun 0) (cycD.toFun 4) (ccwCycle_mem cycD 4) (ccwCycle_mem cycD 0)
      (cycD.inj.ne (by decide)) (by rw [← h40]; exact ccwCycle_isCCWEdge cycD 4)
      (by simpa [h40] using hHneg) (Or.inr ⟨rfl, rfl⟩) (hQ_back _ h0Q)).1
    obtain ⟨h0, hh0⟩ := hHne
    rcases h_all_H_01_12 h0 hh0 with ⟨hed0, hin0⟩ | ⟨hed1, hin1⟩
    · rcases hep h0 hh0 _ _ hed0 hin0 with e | e
      · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 4) e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 4) e
    · rcases hep h0 hh0 _ _ hed1 hin1 with e | e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 4) e
      · exact cycD.inj.ne (by decide : (2 : Fin 5) ≠ 4) e
  have h_forbid_1 : cycD.toFun 1 ∈ Q → il = 1 → False := fun h1Q heq => by
    subst heq
    have h12 : (1 + 1 : Fin 5) = 2 := by decide
    have hH_all_01 : ∀ h ∈ H, InIntTri (w D) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S h) := by
      intro h hh
      have hhM : h ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh⟩
      rcases h_adj h hhM with ⟨_, hin, _, _⟩ | ⟨_, _, _, hnot⟩
      · exact hin
      · exact False.elim (hnot _ _ hHne (by rw [← h12]; exact ccwCycle_isCCWEdge cycD 1) (by simpa [h12] using hHneg) rfl)
    have hep := (h25.endpoint_back_criterion hHne hD5' (cycD.toFun 1) (cycD.toFun 2)
      (cycD.toFun 1) (cycD.toFun 2) (ccwCycle_mem cycD 1) (ccwCycle_mem cycD 2)
      (cycD.inj.ne (by decide)) (by rw [← h12]; exact ccwCycle_isCCWEdge cycD 1)
      (by simpa [h12] using hHneg) (Or.inl ⟨rfl, rfl⟩) (hQ_back _ h1Q)).1
    obtain ⟨h0, hh0⟩ := hHne
    rcases hep h0 hh0 _ _ (ccwCycle_isCCWEdge cycD 0) (hH_all_01 h0 hh0) with e | e
    · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 2) e
    · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 2) e
  have h_forbid_1r : cycD.toFun 1 ∈ Q → il = 1 → False := h_forbid_1
  fin_cases il
  · exact False.elim (h_no01 hHne _ _ (ccwCycle_isCCWEdge cycD 0) hHneg rfl)
  · refine ⟨fun h1Q => h_forbid_1 h1Q rfl, fun h2Q =>
      h_two_forbid h2Q hHne _ _ (ccwCycle_isCCWEdge cycD 1) hHneg rfl⟩
  · have hn3 : cycD.toFun 3 ∉ Q := fun h3Q => by
      rcases hQ_23_or_40 with h | h | h
      · rcases Finset.mem_insert.mp (h h3Q) with e | e
        · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 0) e
        · rcases Finset.mem_insert.mp e with e | e
          · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1) e
          · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 2) (Finset.mem_singleton.mp e)
      · exact h_forbid_2 (h ▸ Finset.mem_insert_self _ _) rfl
      · rcases Finset.mem_insert.mp (h.subset h3Q) with e | e
        · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 4) e
        · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 0) (Finset.mem_singleton.mp e)
    constructor
    · intro h2Q
      rcases hQ_23_or_40 with _ | _ | h
      · exact h_forbid_2 h2Q rfl
      · exact h_forbid_2 h2Q rfl
      · rcases Finset.mem_insert.mp (h.subset h2Q) with e | e
        · exact cycD.inj.ne (by decide : (2 : Fin 5) ≠ 4) e
        · exact cycD.inj.ne (by decide : (2 : Fin 5) ≠ 0) (Finset.mem_singleton.mp e)
    · simpa using hn3
  · constructor
    · intro h3Q
      rcases hQ_23_or_40 with h | _ | h
      · rcases Finset.mem_insert.mp (h h3Q) with e | e
        · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 0) e
        · rcases Finset.mem_insert.mp e with e | e
          · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1) e
          · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 2) (Finset.mem_singleton.mp e)
      · exact h_forbid_3 h3Q rfl
      · rcases Finset.mem_insert.mp (h.subset h3Q) with e | e
        · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 4) e
        · exact cycD.inj.ne (by decide : (3 : Fin 5) ≠ 0) (Finset.mem_singleton.mp e)
    · intro h4Q
      rcases hQ_23_or_40 with h | h | _
      · rcases Finset.mem_insert.mp (h h4Q) with e | e
        · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 0) e
        · rcases Finset.mem_insert.mp e with e | e
          · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1) e
          · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 2) (Finset.mem_singleton.mp e)
      · rcases Finset.mem_insert.mp (h.subset h4Q) with e | e
        · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 2) e
        · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 3) (Finset.mem_singleton.mp e)
      · exact h_forbid_4 h4Q rfl
  · constructor
    · intro h4Q
      rcases hQ_23_or_40 with h | h | heq
      · rcases Finset.mem_insert.mp (h h4Q) with e | e
        · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 0) e
        · rcases Finset.mem_insert.mp e with e | e
          · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1) e
          · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 2) (Finset.mem_singleton.mp e)
      · rcases Finset.mem_insert.mp (h.subset h4Q) with e | e
        · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 2) e
        · exact cycD.inj.ne (by decide : (4 : Fin 5) ≠ 3) (Finset.mem_singleton.mp e)
      · exact h_forbid_0 (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) rfl
    · exact fun h0Q => h_forbid_0 (by simpa using h0Q) rfl

private lemma finset_pair_union_pair {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b} ∪ {c, d} : Finset α) = {a, b, c, d} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]

private lemma reflPt_image_tri (a b c : ℝ × ℝ) :
    reflPt '' ({a, b, c} : Set (ℝ × ℝ)) = {reflPt c, reflPt a, reflPt b} := by
  ext p
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
  · rintro (rfl | rfl | rfl)
    · exact ⟨c, Or.inr (Or.inr rfl), rfl⟩
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩

private lemma reflPt_image_tri_swap12 (a b c : ℝ × ℝ) :
    reflPt '' ({a, b, c} : Set (ℝ × ℝ)) = {reflPt b, reflPt a, reflPt c} := by
  ext p
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto
  · rintro (rfl | rfl | rfl)
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨c, Or.inr (Or.inr rfl), rfl⟩

private lemma range_cyc_local {n k : ℕ} (S : Fin n → ℝ × ℝ) {D : Finset (Fin n)} (cyc : CCWCycle S D k) :
    Set.range (fun i => S (cyc.toFun i)) = (D.image S : Set (ℝ × ℝ)) := by
  ext p; simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨cyc.toFun i, ccwCycle_mem cyc i, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← cyc.image_eq] at hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩

/-- **Proposition 8.6 (`adjacent-reduction`, `upper_9.tex` lines 1009–1017)**:
    When `|D| = 5, |M| = 5`, `{e(y) : y ∈ M} ⊆ {01, 12}` with both `e⁻¹(01)` and `e⁻¹(12)` nonempty,
    and `y0, y1 ∈ M` are minimal on `01, 12` respectively, then `1 ∉ {l, r}` (when `H ≠ ∅`), and all
    four sources `O*(y0) = {4, y0, 2}`, `O*(y1) = {0, y1, 3}`, `O*_{01}(4) = {y0, y1, 4}`, and
    `O*_{01}(3) = {y0, y1, 3}` select `{1}` with anchors `{y0, 2}`, `{0, y1}`, `{y0, y1}`, `{y0, y1}`. -/
theorem adjacent_reduction {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 y1 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0_ex : 0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0) ∧
      (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
        InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r)))
    (hy1_ex : 0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1) ∧
      (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
        InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)))
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0) (S z))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1) (S z)) :
    let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
    let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
    (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ d1 ∧ r ≠ d1) ∧
    (let O0 := ({d4, y0, d2} : Finset (Fin n))
     let v0 := w (Finset.univ \ O0)
     GoodAnchorPair P S w O0 y0 d2 ∧
     IsBackVertexOf S (hullVertices S) d1 v0 ∧
     SegmentsCross v0 (S d1) (S y0) (S d2) ∧
     (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, d2} ∅ w) (S d1) Hp) ∧
     (∀ z : Fin n, z ≠ y0 → z ≠ d2 → z ∉ O0 →
       S z ∈ convexHull ℝ (({d1, y0, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
       SegmentsCross v0 (S z) (S y0) (S d2) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, d2} ∅ w) (S z) Hp) ∧
       (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v0))) ∧
    (let O1 := ({d0, y1, d3} : Finset (Fin n))
     let v1 := w (Finset.univ \ O1)
     GoodAnchorPair P S w O1 d0 y1 ∧
     IsBackVertexOf S (hullVertices S) d1 v1 ∧
     SegmentsCross v1 (S d1) (S d0) (S y1) ∧
     (∃ Hp, IsHalfPlaneTest P (WitnessSet {d0, y1} ∅ w) (S d1) Hp) ∧
     (∀ z : Fin n, z ≠ d0 → z ≠ y1 → z ∉ O1 →
       S z ∈ convexHull ℝ (({d1, d0, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
       SegmentsCross v1 (S z) (S d0) (S y1) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {d0, y1} ∅ w) (S z) Hp) ∧
       (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v1))) ∧
    (let O4 := ({d4, y0, y1} : Finset (Fin n))
     let v4 := w (Finset.univ \ O4)
     GoodAnchorPair P S w O4 y0 y1 ∧
     IsBackVertexOf S (hullVertices S) d1 v4 ∧
     SegmentsCross v4 (S d1) (S y0) (S y1) ∧
     (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S d1) Hp) ∧
     (∀ z : Fin n, z ≠ y0 → z ≠ y1 → z ∉ O4 →
       S z ∈ convexHull ℝ (({d1, y0, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
       SegmentsCross v4 (S z) (S y0) (S y1) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S z) Hp) ∧
       (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v4))) ∧
    (let O3 := ({d3, y0, y1} : Finset (Fin n))
     let v3 := w (Finset.univ \ O3)
     GoodAnchorPair P S w O3 y0 y1 ∧
     IsBackVertexOf S (hullVertices S) d1 v3 ∧
     SegmentsCross v3 (S d1) (S y0) (S y1) ∧
     (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S d1) Hp) ∧
     (∀ z : Fin n, z ≠ y0 → z ≠ y1 → z ∉ O3 →
       S z ∈ convexHull ℝ (({d1, y0, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
       SegmentsCross v3 (S z) (S y0) (S y1) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S z) Hp) ∧
       (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v3))) := by
  intro d0 d1 d2 d3 d4
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  have hD3 : 3 ≤ D.card := by
    have h5 : D.card = 5 := hD5
    omega
  have hd01 : d0 ≠ d1 := cycD.inj.ne (by decide)
  have hd02 : d0 ≠ d2 := cycD.inj.ne (by decide)
  have hd03 : d0 ≠ d3 := cycD.inj.ne (by decide)
  have hd04 : d0 ≠ d4 := cycD.inj.ne (by decide)
  have hd12 : d1 ≠ d2 := cycD.inj.ne (by decide)
  have hd13 : d1 ≠ d3 := cycD.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cycD.inj.ne (by decide)
  have hd23 : d2 ≠ d3 := cycD.inj.ne (by decide)
  have hd24 : d2 ≠ d4 := cycD.inj.ne (by decide)
  have hd34 : d3 ≠ d4 := cycD.inj.ne (by decide)
  have hy0_nD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy1_nD : y1 ∉ D := (Finset.mem_sdiff.mp hy1M).2
  have hy01 : y0 ≠ y1 := by
    intro h; subst h
    obtain ⟨uy, vy, _, _, _, _, _, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
    obtain ⟨rfl, rfl⟩ := h_uniq d0 d1 (ccwCycle_isCCWEdge cycD 0) hy0_ex.1 hy0_ex.2.1.to_convexHull
    obtain ⟨h10, _⟩ := h_uniq d1 d2 (ccwCycle_isCCWEdge cycD 1) hy1_ex.1 hy1_ex.2.1.to_convexHull
    exact hd01 h10.symm
  have h1_not_lr : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ d1 ∧ r ≠ d1 := by
    intro l r hHne hed hHneg
    rw [isCCWEdge_iff_ccwCycle cycD] at hed
    rcases hed with ⟨il, rfl, rfl⟩
    fin_cases il
    · exact False.elim (hy0_ex.2.2.2 _ _ hHne (ccwCycle_isCCWEdge cycD 0) hHneg rfl)
    · exact False.elim (hy1_ex.2.2.2 _ _ hHne (ccwCycle_isCCWEdge cycD 1) hHneg rfl)
    · exact ⟨cycD.inj.ne (by decide : (2 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1)⟩
    · exact ⟨cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1)⟩
    · exact ⟨cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (0 : Fin 5) ≠ 1)⟩
  have h_not_lr_pair : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
      (d0, d1) ≠ (l, r) ∧ (d1, d2) ≠ (l, r) := by
    intro l r hHne hed hHneg
    exact ⟨hy0_ex.2.2.2 l r hHne hed hHneg, hy1_ex.2.2.2 l r hHne hed hHneg⟩
  have hO0_nadj : ∀ a ∈ ({d4, y0, d2} : Finset (Fin n)) ∩ D,
      ∀ b ∈ ({d4, y0, d2} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b :=
    pentagon_Ostar_nadj h25 hD5 cycD hy0_nD 4 2 (by decide) (by decide)
  have hO1_nadj : ∀ a ∈ ({d0, y1, d3} : Finset (Fin n)) ∩ D,
      ∀ b ∈ ({d0, y1, d3} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b :=
    pentagon_Ostar_nadj h25 hD5 cycD hy1_nD 0 3 (by decide) (by decide)
  have hO4_nadj : ∀ a ∈ ({d4, y0, y1} : Finset (Fin n)) ∩ D,
      ∀ b ∈ ({d4, y0, y1} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b := by
    intro a ha b hb hed
    have haD := (Finset.mem_inter.mp ha).2; have hbD := (Finset.mem_inter.mp hb).2
    have ha4 : a = d4 := by
      rcases (by simpa using (Finset.mem_inter.mp ha).1 : a = d4 ∨ a = y0 ∨ a = y1) with rfl | rfl | rfl
      · rfl
      · exact False.elim (hy0_nD haD)
      · exact False.elim (hy1_nD haD)
    have hb4 : b = d4 := by
      rcases (by simpa using (Finset.mem_inter.mp hb).1 : b = d4 ∨ b = y0 ∨ b = y1) with rfl | rfl | rfl
      · rfl
      · exact False.elim (hy0_nD hbD)
      · exact False.elim (hy1_nD hbD)
    exact hed.2.2.1 (ha4.trans hb4.symm)
  have hO3_nadj : ∀ a ∈ ({d3, y0, y1} : Finset (Fin n)) ∩ D,
      ∀ b ∈ ({d3, y0, y1} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b := by
    intro a ha b hb hed
    have haD := (Finset.mem_inter.mp ha).2; have hbD := (Finset.mem_inter.mp hb).2
    have ha3 : a = d3 := by
      rcases (by simpa using (Finset.mem_inter.mp ha).1 : a = d3 ∨ a = y0 ∨ a = y1) with rfl | rfl | rfl
      · rfl
      · exact False.elim (hy0_nD haD)
      · exact False.elim (hy1_nD haD)
    have hb3 : b = d3 := by
      rcases (by simpa using (Finset.mem_inter.mp hb).1 : b = d3 ∨ b = y0 ∨ b = y1) with rfl | rfl | rfl
      · rfl
      · exact False.elim (hy0_nD hbD)
      · exact False.elim (hy1_nD hbD)
    exact hed.2.2.1 (ha3.trans hb3.symm)
  obtain ⟨_, oa0, ob0, Γ0, hcases0, hgap0, hΓ0, hcap0⟩ :=
    pentagon_interior_anchor_2 hPoly h25 hD5 hM5 cycD hy0M 0 hy0_ex
  obtain ⟨_, oa1, ob1, Γ1, hcases1, hgap1, hΓ1, hcap1⟩ :=
    pentagon_interior_anchor_2 hPoly h25 hD5 hM5 cycD hy1M 1 hy1_ex
  obtain ⟨oa4, ob4, Γ4, hcases4, hgap4, hΓ4, hcap4⟩ :=
    adjacent_exits_b4 hPoly h25 rfl cycD hy0M hy1M hy01
      (hy0_ex.2.2.1 (w (Finset.univ \ {d4, y0, y1})) ⟨Finset.univ \ {d4, y0, y1}, fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        rcases hx with rfl | rfl
        · exact ⟨hd04, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 0)⟩
        · exact ⟨hd14, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1)⟩,
        Finset.disjoint_empty_right _, rfl⟩)
      (hy1_ex.2.2.1 (w (Finset.univ \ {d4, y0, y1})) ⟨Finset.univ \ {d4, y0, y1}, fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        rcases hx with rfl | rfl
        · exact ⟨hd14, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1)⟩
        · exact ⟨hd24, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 2), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2)⟩,
        Finset.disjoint_empty_right _, rfl⟩)
      h_not_lr_pair
  obtain ⟨oa3, ob3, Γ3, hcases3, hgap3, hΓ3, hcap3⟩ :=
    adjacent_exits_b3 hPoly h25 rfl cycD hy0M hy1M hy01
      (hy0_ex.2.2.1 (w (Finset.univ \ {d3, y0, y1})) ⟨Finset.univ \ {d3, y0, y1}, fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        rcases hx with rfl | rfl
        · exact ⟨hd03, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 0)⟩
        · exact ⟨hd13, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1)⟩,
        Finset.disjoint_empty_right _, rfl⟩)
      (hy1_ex.2.2.1 (w (Finset.univ \ {d3, y0, y1})) ⟨Finset.univ \ {d3, y0, y1}, fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        rcases hx with rfl | rfl
        · exact ⟨hd13, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1)⟩
        · exact ⟨hd23, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 2), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2)⟩,
        Finset.disjoint_empty_right _, rfl⟩)
      h_not_lr_pair
  have hQ_disj_fn : ∀ {Q : Finset (Fin n)},
      (∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O))) →
      ((Q ⊆ {d0, d1, d2}) ∨ (Q = {d2, d3}) ∨ (Q = {d4, d0})) →
      ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q :=
    fun hQb hQsub => adj_pair_H_disj hPoly h25 hD5 cycD h_adj
      (fun hHne l r hed hHn => hy0_ex.2.2.2 l r hHne hed hHn)
      (fun _ hHne l r hed hHn => hy1_ex.2.2.2 l r hHne hed hHn)
      hQb hQsub
  have range_cyc : ∀ (S' : Fin n → ℝ × ℝ) (cyc : CCWCycle S' D 2),
      Set.range (fun i => S' (cyc.toFun i)) = (D.image S' : Set (ℝ × ℝ)) := by
    intro S' cyc; ext p
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨cyc.toFun i, ccwCycle_mem cyc i, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hcr := cyc.image_eq; dsimp [D] at hcr
      have hx' : x ∈ hullVertices S \ certifiedVertices S w := hx
      rw [← hcr] at hx'
      rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  have elim02 :
      (∃ O, d0 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d0 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S d0) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d0, S d4, S y0} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S z) Hp) →
      (∃ O, d2 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d2 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d3} ∅ w) (S d2) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d2, S y1, S d3} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d3} ∅ w) (S z) Hp) →
      False := by
    intro h0b h0hp h0cap h2b h2hp h2cap
    let Q : Finset (Fin n) := {d0, d2}
    let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
    have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl; exact h0b; exact h2b
    have hd1F : d1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 1, by simp [Q, hd01.symm, hd12]⟩)
    have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd03.symm, hd23.symm]⟩)
    have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd04.symm, hd24.symm]⟩)
    have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
      (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
      (Finset.card_pair hd02) y0 y1 hy0M hy1M hy01 hBackQ
      (fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hex_lift_hp hd4F hy0F h0hp
        · exact hex_lift_hp hy1F hd3F h2hp)
      (hQ_disj_fn hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d2])))
      (fun z hz hzD_conv => ?_)
    have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
    have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
    have hny01 : z ≠ y0 ∧ z ≠ y1 := by
      have hm := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hm
    let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
    have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
    have hcov := convD_cover_case3b_adjacent_02 pD cycD.ccw (S y0) (S y1) (F.image S : Set (ℝ × ℝ))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
    rcases hcov with ((hF | hc0) | hc2) | (he0 | he1)
    · exact Or.inr hF
    · left
      have hset : ({pD 4, pD 0, S y0} : Set (ℝ × ℝ)) = {S d0, S d4, S y0} := by
        change {S d4, S d0, S y0} = {S d0, S d4, S y0}; exact Set.insert_comm _ _ _
      rw [hset] at hc0
      exact hex_lift_hp hd4F hy0F (h0cap z hzD hny01.1 hny01.2 hc0)
    · left
      have hset : ({S y1, pD 2, pD 3} : Set (ℝ × ℝ)) = {S d2, S y1, S d3} := by
        change {S y1, S d2, S d3} = {S d2, S y1, S d3}; exact Set.insert_comm _ _ _
      rw [hset] at hc2
      exact hex_lift_hp hy1F hd3F (h2cap z hzD hny01.1 hny01.2 hc2)
    · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
    · exact False.elim (hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1))
  have elim01 :
      (∃ O, d0 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d0 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S d0) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d0, S d4, S y0} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S z) Hp) →
      (∃ O, d1 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d1 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S d1) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d1, S y0, S y1} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S z) Hp) →
      False := by
    intro h0b h0hp h0cap h1b h1hp h1cap
    let Q : Finset (Fin n) := {d0, d1}
    let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
    have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl; exact h0b; exact h1b
    have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, hd02.symm, hd12.symm]⟩)
    have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd03.symm, hd13.symm]⟩)
    have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd04.symm, hd14.symm]⟩)
    have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
      (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
      (Finset.card_pair hd01) y0 y1 hy0M hy1M hy01 hBackQ
      (fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hex_lift_hp hd4F hy0F h0hp
        · exact hex_lift_hp hy0F hy1F h1hp)
      (hQ_disj_fn hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d1])))
      (fun z hz hzD_conv => ?_)
    have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
    have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
    have hny01 : z ≠ y0 ∧ z ≠ y1 := by
      have hm := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hm
    let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
    have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
    have hcov := convD_cover_case3b_adjacent_01 pD cycD.ccw (S y0) (S y1) (F.image S : Set (ℝ × ℝ))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
    rcases hcov with ((hF | hc0) | hc1) | (he0 | he1)
    · exact Or.inr hF
    · left
      have hset : ({pD 4, pD 0, S y0} : Set (ℝ × ℝ)) = {S d0, S d4, S y0} := by
        change {S d4, S d0, S y0} = {S d0, S d4, S y0}; exact Set.insert_comm _ _ _
      rw [hset] at hc0
      exact hex_lift_hp hd4F hy0F (h0cap z hzD hny01.1 hny01.2 hc0)
    · left
      have hset : ({S y0, pD 1, S y1} : Set (ℝ × ℝ)) = {S d1, S y0, S y1} := by
        change {S y0, S d1, S y1} = {S d1, S y0, S y1}; exact Set.insert_comm _ _ _
      rw [hset] at hc1
      exact hex_lift_hp hy0F hy1F (h1cap z hzD hny01.1 hny01.2 hc1)
    · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
    · exact False.elim (hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1))
  have elim12 :
      (∃ O, d1 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d1 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S d1) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d1, S y0, S y1} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y1} ∅ w) (S z) Hp) →
      (∃ O, d2 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d2 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d3} ∅ w) (S d2) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d2, S y1, S d3} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d3} ∅ w) (S z) Hp) →
      False := by
    intro h1b h1hp h1cap h2b h2hp h2cap
    let Q : Finset (Fin n) := {d1, d2}
    let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
    have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl; exact h1b; exact h2b
    have hd0F : d0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 0, by simp [Q, hd01, hd02]⟩)
    have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd13.symm, hd23.symm]⟩)
    have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd14.symm, hd24.symm]⟩)
    have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
      (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
      (Finset.card_pair hd12) y0 y1 hy0M hy1M hy01 hBackQ
      (fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hex_lift_hp hy0F hy1F h1hp
        · exact hex_lift_hp hy1F hd3F h2hp)
      (hQ_disj_fn hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d1, d2])))
      (fun z hz hzD_conv => ?_)
    have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
    have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
    have hny01 : z ≠ y0 ∧ z ≠ y1 := by
      have hm := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hm
    let cycR : CCWCycle (reflPt ∘ S) D 2 := ccwCycle_rev cycD 2
    let pDR : Fin 5 → ℝ × ℝ := fun i => reflPt (S (cycR.toFun i))
    have hzR : reflPt (S z) ∈ convexHull ℝ (Set.range pDR) := by
      rw [show Set.range pDR = Set.range (fun i => (reflPt ∘ S) (cycR.toFun i)) from rfl,
        range_cyc (reflPt ∘ S) cycR]
      have him : (D.image (reflPt ∘ S) : Set (ℝ × ℝ)) = reflPt '' (D.image S : Set (ℝ × ℝ)) := by
        ext p; simp [Finset.coe_image]
      rw [him]; exact (reflPt_mem_convexHull (D.image S : Set (ℝ × ℝ)) (S z)).mpr hzD_conv
    have hDR0 : pDR 0 = reflPt (S d2) := rfl
    have hDR1 : pDR 1 = reflPt (S d1) := rfl
    have hDR2 : pDR 2 = reflPt (S d0) := rfl
    have hDR4 : pDR 4 = reflPt (S d3) := rfl
    have hcov := convD_cover_case3b_adjacent_01 pDR cycR.ccw (reflPt (S y1)) (reflPt (S y0))
      ((F.image (reflPt ∘ S)) : Set (ℝ × ℝ))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy1F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy0F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hd0F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hd4F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hd3F)) hzR
    rw [hDR0, hDR1, hDR2, hDR4] at hcov
    have pull_mem : ∀ {T : Set (ℝ × ℝ)}, reflPt (S z) ∈ convexHull ℝ (reflPt '' T) →
        S z ∈ convexHull ℝ T := fun {T} hzT => (reflPt_mem_convexHull T (S z)).mp hzT
    rcases hcov with ((hF | hc2) | hc1) | (he1 | he0)
    · right; refine pull_mem ?_
      have him : reflPt '' (F.image S : Set (ℝ × ℝ)) = (F.image (reflPt ∘ S) : Set (ℝ × ℝ)) := by ext p; simp [Finset.coe_image]
      rwa [him]
    · left
      have hc2' : S z ∈ convexHull ℝ ({S d2, S y1, S d3} : Set (ℝ × ℝ)) := by
        refine pull_mem ?_
        rw [reflPt_image_tri]; exact hc2
      exact hex_lift_hp hy1F hd3F (h2cap z hzD hny01.1 hny01.2 hc2')
    · left
      have hc1' : S z ∈ convexHull ℝ ({S d1, S y0, S y1} : Set (ℝ × ℝ)) := by
        refine pull_mem ?_
        rw [reflPt_image_tri]; exact hc1
      exact hex_lift_hp hy0F hy1F (h1cap z hzD hny01.1 hny01.2 hc1')
    · exfalso
      have he1' : S z ∈ convexHull ℝ ({S d1, S d2, S y1} : Set (ℝ × ℝ)) := by
        refine pull_mem ?_
        rw [reflPt_image_tri_swap12]; exact he1
      exact hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1')
    · exfalso
      have he0' : S z ∈ convexHull ℝ ({S d0, S d1, S y0} : Set (ℝ × ℝ)) := by
        refine pull_mem ?_
        rw [reflPt_image_tri_swap12]; exact he0
      exact hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0')
  have elim23 :
      (∃ O, d2 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d2 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d4} ∅ w) (S d2) Hp) →
      (∃ O, d3 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d3 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d4} ∅ w) (S d3) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d2, S d3, S y1, S d4} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d4} ∅ w) (S z) Hp) →
      False := by
    intro h2b h2hp h3b h3hp h23cap
    let Q : Finset (Fin n) := {d2, d3}
    let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
    have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl; exact h2b; exact h3b
    have hd0F : d0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 0, by simp [Q, hd02, hd03]⟩)
    have hd1F : d1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 1, by simp [Q, hd12, hd13]⟩)
    have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd24.symm, hd34.symm]⟩)
    have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
      (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
      (Finset.card_pair hd23) y0 y1 hy0M hy1M hy01 hBackQ
      (fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hex_lift_hp hy1F hd4F h2hp
        · exact hex_lift_hp hy1F hd4F h3hp)
      (hQ_disj_fn hBackQ (Or.inr (Or.inl rfl)))
      (fun z hz hzD_conv => ?_)
    have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
    have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
    have hny01 : z ≠ y0 ∧ z ≠ y1 := by
      have hm := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hm
    let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
    have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
    obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S y1) (S z) hzD'
    fin_cases i
    · right
      exact convexHull_tri_subset
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd0F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))) hi
    · exact False.elim (hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hi))
    · left
      have hsub : convexHull ℝ ({pD 2, pD 3, S y1} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({S d2, S d3, S y1, S d4} : Set (ℝ × ℝ)) :=
        convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d2]))
          (subset_convexHull ℝ _ (by simp [pD, d3])) (subset_convexHull ℝ _ (by simp))
      exact hex_lift_hp hy1F hd4F (h23cap z hzD hny01.1 hny01.2 (hsub hi))
    · left
      have hsub : convexHull ℝ ({pD 3, pD 4, S y1} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({S d2, S d3, S y1, S d4} : Set (ℝ × ℝ)) :=
        convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d3]))
          (subset_convexHull ℝ _ (by simp [pD, d4])) (subset_convexHull ℝ _ (by simp))
      exact hex_lift_hp hy1F hd4F (h23cap z hzD hny01.1 hny01.2 (hsub hi))
    · right
      exact convexHull_tri_subset
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd0F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy1F))) hi
  have elim40 :
      (∃ O, d4 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d4 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {d3, y0} ∅ w) (S d4) Hp) →
      (∃ O, d0 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d0 (w (Finset.univ \ O))) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {d3, y0} ∅ w) (S d0) Hp) →
      (∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
        S z ∈ convexHull ℝ ({S d4, S d0, S d3, S y0} : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {d3, y0} ∅ w) (S z) Hp) →
      False := by
    intro h4b h4hp h0b h0hp h40cap
    let Q : Finset (Fin n) := {d4, d0}
    let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
    have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl; exact h4b; exact h0b
    have hd1F : d1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 1, by simp [Q, hd14, hd01.symm]⟩)
    have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, hd24, hd02.symm]⟩)
    have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd34, hd03.symm]⟩)
    have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
      (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
      (Finset.card_pair hd04.symm) y0 y1 hy0M hy1M hy01 hBackQ
      (fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hex_lift_hp hd3F hy0F h4hp
        · exact hex_lift_hp hd3F hy0F h0hp)
      (hQ_disj_fn hBackQ (Or.inr (Or.inr rfl)))
      (fun z hz hzD_conv => ?_)
    have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
    have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
    have hny01 : z ≠ y0 ∧ z ≠ y1 := by
      have hm := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hm
    let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
    have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
    obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S y0) (S z) hzD'
    fin_cases i
    · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr hi))
    · right
      exact convexHull_tri_subset
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))) hi
    · right
      exact convexHull_tri_subset
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))) hi
    · left
      have hsub : convexHull ℝ ({pD 3, pD 4, S y0} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({S d4, S d0, S d3, S y0} : Set (ℝ × ℝ)) :=
        convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d3]))
          (subset_convexHull ℝ _ (by simp [pD, d4])) (subset_convexHull ℝ _ (by simp))
      exact hex_lift_hp hd3F hy0F (h40cap z hzD hny01.1 hny01.2 (hsub hi))
    · left
      have hsub : convexHull ℝ ({pD 4, pD 0, S y0} : Set (ℝ × ℝ)) ⊆ convexHull ℝ ({S d4, S d0, S d3, S y0} : Set (ℝ × ℝ)) :=
        convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d4]))
          (subset_convexHull ℝ _ (by simp [pD, d0])) (subset_convexHull ℝ _ (by simp))
      exact hex_lift_hp hd3F hy0F (h40cap z hzD hny01.1 hny01.2 (hsub hi))
  have hO0_sel1 : oa0 = y0 ∧ ob0 = d2 ∧ Γ0 = {d1} := by
    rcases hcases0 with ⟨hoa0, hob0, hΓ0eq⟩ | h1
    · exfalso
      have h0_inst := hΓ0 d0 (by rw [hΓ0eq]; exact Finset.mem_singleton_self _)
      rw [hoa0, hob0] at h0_inst
      have h0b : ∃ O, d0 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d0 (w (Finset.univ \ O)) :=
        ⟨{d4, y0, d2}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd04, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), hd02⟩,
          hO0_nadj, h0_inst.1⟩
      have h0cap' : ∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
          S z ∈ convexHull ℝ ({S d0, S d4, S y0} : Set (ℝ × ℝ)) →
          ∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, y0} ∅ w) (S z) Hp := fun z hznD hny0 _ hc => by
        have hrec := hcap0 z (by rw [hoa0]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 4)) (by rw [hob0]; exact hny0)
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hny0, fun h => hznD (h ▸ ccwCycle_mem cycD 2)⟩)
          (by rw [hoa0, hob0, hΓ0eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
        rw [hoa0, hob0] at hrec; exact hrec.2.1
      rcases hcases1 with ⟨hoa1, hob1, hΓ1eq⟩ | ⟨hoa1, hob1, hΓ1eq⟩
      · -- O*(y1) -> 1 (anchors {d0, y1}); use O*_{01}(3)
        have h1_inst := hΓ1 d1 (by rw [hΓ1eq]; exact Finset.mem_singleton_self _)
        rw [hoa1, hob1] at h1_inst
        rcases hcases3 with ⟨hoa3, hob3, hΓ3eq⟩ | ⟨hoa3, hob3, hΓ3eq⟩ | ⟨hoa3, hob3, hΓ3eq⟩
        · have h4_3 := hΓ3 d4 (by rw [hΓ3eq]; exact Finset.mem_insert_self _ _)
          have h0_3 := hΓ3 d0 (by rw [hΓ3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          rw [hoa3, hob3] at h4_3 h0_3
          refine elim40
            ⟨{d3, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd34.symm, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 4), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 4)⟩, hO3_nadj, h4_3.1⟩
            h4_3.2.2 h0b
            (by rw [show ({d3, y0} : Finset (Fin n)) = {d3, y0} from rfl]; exact h0_3.2.2)
            (fun z hznD hny0 hny1 hc => by
              have hrec := hcap3 z (by rw [hoa3]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 3)) (by rw [hob3]; exact hny0)
                (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 3), hny0, hny1⟩)
                (by
                  rw [hoa3, hob3, hΓ3eq, finset_pair_union_pair, finset4_image_eq]; exact hc)
              rw [hoa3, hob3] at hrec; exact hrec.2.1)
        · have h1_3 := hΓ3 d1 (by rw [hΓ3eq]; exact Finset.mem_singleton_self _)
          rw [hoa3, hob3] at h1_3
          refine elim01 h0b h0_inst.2.2 h0cap'
            ⟨{d3, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd13, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1)⟩, hO3_nadj, h1_3.1⟩
            h1_3.2.2 (fun z hznD hny0 hny1 hc => by
              have hrec := hcap3 z (by rw [hoa3]; exact hny0) (by rw [hob3]; exact hny1)
                (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 3), hny0, hny1⟩)
                (by rw [hoa3, hob3, hΓ3eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
              rw [hoa3, hob3] at hrec; exact hrec.2.1)
        · have h2_3 := hΓ3 d2 (by rw [hΓ3eq]; exact Finset.mem_singleton_self _)
          rw [hoa3, hob3] at h2_3
          refine elim02 h0b h0_inst.2.2 h0cap'
            ⟨{d3, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd23, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 2), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2)⟩, hO3_nadj, h2_3.1⟩
            h2_3.2.2 (fun z hznD hny0 hny1 hc => by
              have hrec := hcap3 z (by rw [hoa3]; exact hny1) (by rw [hob3]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 3))
                (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 3), hny0, hny1⟩)
                (by rw [hoa3, hob3, hΓ3eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
              rw [hoa3, hob3] at hrec; exact hrec.2.1)
      · -- O*(y1) -> 2 (anchors {y1, d3})
        have h2_inst := hΓ1 d2 (by rw [hΓ1eq]; exact Finset.mem_singleton_self _)
        rw [hoa1, hob1] at h2_inst
        refine elim02 h0b h0_inst.2.2 h0cap'
          ⟨{d0, y1, d3}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd02.symm, fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2), hd23⟩, hO1_nadj, h2_inst.1⟩
          h2_inst.2.2 (fun z hznD _ hny1 hc => by
            have hrec := hcap1 z (by rw [hoa1]; exact hny1) (by rw [hob1]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 3))
              (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 0), hny1, fun h => hznD (h ▸ ccwCycle_mem cycD 3)⟩)
              (by rw [hoa1, hob1, hΓ1eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
            rw [hoa1, hob1] at hrec; exact hrec.2.1)
    · exact h1
  have hO1_sel1 : oa1 = d0 ∧ ob1 = y1 ∧ Γ1 = {d1} := by
    rcases hcases1 with h1 | ⟨hoa1, hob1, hΓ1eq⟩
    · exact h1
    · exfalso
      have h2_inst := hΓ1 d2 (by rw [hΓ1eq]; exact Finset.mem_singleton_self _)
      rw [hoa1, hob1] at h2_inst
      have h2b : ∃ O, d2 ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧ IsBackVertexOf S B d2 (w (Finset.univ \ O)) :=
        ⟨{d0, y1, d3}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd02.symm, fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2), hd23⟩,
          hO1_nadj, h2_inst.1⟩
      have h2cap' : ∀ z : Fin n, z ∉ D → z ≠ y0 → z ≠ y1 →
          S z ∈ convexHull ℝ ({S d2, S y1, S d3} : Set (ℝ × ℝ)) →
          ∃ Hp, IsHalfPlaneTest P (WitnessSet {y1, d3} ∅ w) (S z) Hp := fun z hznD _ hny1 hc => by
        have hrec := hcap1 z (by rw [hoa1]; exact hny1) (by rw [hob1]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 3))
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 0), hny1, fun h => hznD (h ▸ ccwCycle_mem cycD 3)⟩)
          (by rw [hoa1, hob1, hΓ1eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
        rw [hoa1, hob1] at hrec; exact hrec.2.1
      rcases hcases4 with ⟨hoa4, hob4, hΓ4eq⟩ | ⟨hoa4, hob4, hΓ4eq⟩ | ⟨hoa4, hob4, hΓ4eq⟩
      · have h0_4 := hΓ4 d0 (by rw [hΓ4eq]; exact Finset.mem_singleton_self _)
        rw [hoa4, hob4] at h0_4
        refine elim02
          ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd04, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 0)⟩, hO4_nadj, h0_4.1⟩
          h0_4.2.2 (fun z hznD hny0 hny1 hc => by
            have hrec := hcap4 z (by rw [hoa4]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 4)) (by rw [hob4]; exact hny0)
              (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hny0, hny1⟩)
              (by rw [hoa4, hob4, hΓ4eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
            rw [hoa4, hob4] at hrec; exact hrec.2.1)
          h2b h2_inst.2.2 h2cap'
      · have h1_4 := hΓ4 d1 (by rw [hΓ4eq]; exact Finset.mem_singleton_self _)
        rw [hoa4, hob4] at h1_4
        refine elim12
          ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd14, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1)⟩, hO4_nadj, h1_4.1⟩
          h1_4.2.2 (fun z hznD hny0 hny1 hc => by
            have hrec := hcap4 z (by rw [hoa4]; exact hny0) (by rw [hob4]; exact hny1)
              (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hny0, hny1⟩)
              (by rw [hoa4, hob4, hΓ4eq]; rw [Finset.singleton_union, finset3_image_eq]; exact hc)
            rw [hoa4, hob4] at hrec; exact hrec.2.1)
          h2b h2_inst.2.2 h2cap'
      · have h2_4 := hΓ4 d2 (by rw [hΓ4eq]; exact Finset.mem_insert_self _ _)
        have h3_4 := hΓ4 d3 (by rw [hΓ4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [hoa4, hob4] at h2_4 h3_4
        refine elim23 h2b h2_4.2.2
          ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd34, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 3), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 3)⟩, hO4_nadj, h3_4.1⟩
          h3_4.2.2 (fun z hznD hny0 hny1 hc => by
            have hrec := hcap4 z (by rw [hoa4]; exact hny1) (by rw [hob4]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 4))
              (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hny0, hny1⟩)
              (by
                rw [hoa4, hob4, hΓ4eq, finset_pair_union_pair, finset4_image_eq]; exact hc)
            rw [hoa4, hob4] at hrec; exact hrec.2.1)
  have h1_inst_O0 := hΓ0 d1 (by rw [hO0_sel1.2.2]; exact Finset.mem_singleton_self _)
  rw [hO0_sel1.1, hO0_sel1.2.1] at h1_inst_O0
  have h1_inst_O1 := hΓ1 d1 (by rw [hO1_sel1.2.2]; exact Finset.mem_singleton_self _)
  rw [hO1_sel1.1, hO1_sel1.2.1] at h1_inst_O1
  have hO4_sel1 : oa4 = y0 ∧ ob4 = y1 ∧ Γ4 = {d1} := by
    rcases hcases4 with ⟨hoa4, hob4, hΓ4eq⟩ | h1 | ⟨hoa4, hob4, hΓ4eq⟩
    · exfalso
      have h0_4 := hΓ4 d0 (by rw [hΓ4eq]; exact Finset.mem_singleton_self _)
      rw [hoa4, hob4] at h0_4
      let Q : Finset (Fin n) := {d0, d1}
      let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
      have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
          IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
        · exact ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd04, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 0)⟩, hO4_nadj, h0_4.1⟩
        · exact ⟨{d4, y0, d2}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd14, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), hd12⟩, hO0_nadj, h1_inst_O0.1⟩
      have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, hd02.symm, hd12.symm]⟩)
      have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd03.symm, hd13.symm]⟩)
      have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd04.symm, hd14.symm]⟩)
      have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
        (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
        (Finset.card_pair hd01) y0 y1 hy0M hy1M hy01 hBackQ
        (fun p hp => by
          simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
          · exact hex_lift_hp hd4F hy0F h0_4.2.2
          · exact hex_lift_hp hy0F hd2F h1_inst_O0.2.2)
        (hQ_disj_fn hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d1])))
        (fun z hz hzD_conv => ?_)
      have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
      have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
      have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
      have hny01 : z ≠ y0 ∧ z ≠ y1 := by
        have hm := (Finset.mem_sdiff.mp hz).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
        exact hm
      let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
      have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
      have hcov := convD_cover_case3b_single_M0 pD cycD.ccw (S y0) (F.image S : Set (ℝ × ℝ))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
        (fun i hi0 hi1 => Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by fin_cases i <;> first | exact absurd rfl hi0 | exact absurd rfl hi1 | assumption))) hzD'
      rcases hcov with ((hF | hc0) | hc1) | he0
      · exact Or.inr hF
      · left
        have hc0' : S z ∈ convexHull ℝ (({d0} ∪ {d4, y0} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
          rw [Finset.singleton_union, finset3_image_eq]
          have hset : ({pD (Fin.last 4), pD 0, S y0} : Set (ℝ × ℝ)) = {S d0, S d4, S y0} := by
            change {S d4, S d0, S y0} = {S d0, S d4, S y0}; exact Set.insert_comm _ _ _
          rwa [← hset]
        have hrec := hcap4 z (by rw [hoa4]; exact fun h => hzD (h ▸ ccwCycle_mem cycD 4)) (by rw [hob4]; exact hny01.1)
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 4), hny01.1, hny01.2⟩)
          (by rw [hoa4, hob4, hΓ4eq]; exact hc0')
        rw [hoa4, hob4] at hrec; exact hex_lift_hp hd4F hy0F hrec.2.1
      · left
        have hc1' : S z ∈ convexHull ℝ (({d1} ∪ {y0, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
          rw [Finset.singleton_union, finset3_image_eq]
          have hset : ({S y0, pD 1, pD 2} : Set (ℝ × ℝ)) = {S d1, S y0, S d2} := by
            change {S y0, S d1, S d2} = {S d1, S y0, S d2}; exact Set.insert_comm _ _ _
          rwa [← hset]
        have hrec := hcap0 z (by rw [hO0_sel1.1]; exact hny01.1) (by rw [hO0_sel1.2.1]; exact fun h => hzD (h ▸ ccwCycle_mem cycD 2))
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 4), hny01.1, fun h => hzD (h ▸ ccwCycle_mem cycD 2)⟩)
          (by rw [hO0_sel1.1, hO0_sel1.2.1, hO0_sel1.2.2]; exact hc1')
        rw [hO0_sel1.1, hO0_sel1.2.1] at hrec; exact hex_lift_hp hy0F hd2F hrec.2.1
      · exact False.elim (hy0_empty z (Finset.mem_erase.mpr ⟨hny01.1, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
    · exact h1
    · exfalso
      have h2_4 := hΓ4 d2 (by rw [hΓ4eq]; exact Finset.mem_insert_self _ _)
      have h3_4 := hΓ4 d3 (by rw [hΓ4eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [hoa4, hob4] at h2_4 h3_4
      refine elim23
        ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd24, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 2), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2)⟩, hO4_nadj, h2_4.1⟩
        h2_4.2.2
        ⟨{d4, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd34, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 3), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 3)⟩, hO4_nadj, h3_4.1⟩
        h3_4.2.2 (fun z hznD hny0 hny1 hc => by
          have hrec := hcap4 z (by rw [hoa4]; exact hny1) (by rw [hob4]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 4))
            (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hny0, hny1⟩)
            (by
              rw [hoa4, hob4, hΓ4eq, finset_pair_union_pair, finset4_image_eq]; exact hc)
          rw [hoa4, hob4] at hrec; exact hrec.2.1)
  have hO3_sel1 : oa3 = y0 ∧ ob3 = y1 ∧ Γ3 = {d1} := by
    rcases hcases3 with ⟨hoa3, hob3, hΓ3eq⟩ | h1 | ⟨hoa3, hob3, hΓ3eq⟩
    · exfalso
      have h4_3 := hΓ3 d4 (by rw [hΓ3eq]; exact Finset.mem_insert_self _ _)
      have h0_3 := hΓ3 d0 (by rw [hΓ3eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [hoa3, hob3] at h4_3 h0_3
      refine elim40
        ⟨{d3, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd34.symm, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 4), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 4)⟩, hO3_nadj, h4_3.1⟩
        h4_3.2.2
        ⟨{d3, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd03, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 0)⟩, hO3_nadj, h0_3.1⟩
        h0_3.2.2 (fun z hznD hny0 hny1 hc => by
          have hrec := hcap3 z (by rw [hoa3]; exact fun h => hznD (h ▸ ccwCycle_mem cycD 3)) (by rw [hob3]; exact hny0)
            (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 3), hny0, hny1⟩)
            (by
              rw [hoa3, hob3, hΓ3eq, finset_pair_union_pair, finset4_image_eq]; exact hc)
          rw [hoa3, hob3] at hrec; exact hrec.2.1)
    · exact h1
    · exfalso
      have h2_3 := hΓ3 d2 (by rw [hΓ3eq]; exact Finset.mem_singleton_self _)
      rw [hoa3, hob3] at h2_3
      let Q : Finset (Fin n) := {d1, d2}
      let F : Finset (Fin n) := (D \ Q) ∪ {y0, y1}
      have hBackQ : ∀ p ∈ Q, ∃ O, p ∉ O ∧ (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
          IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
        · exact ⟨{d0, y1, d3}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd01.symm, fun h => hy1_nD (h ▸ ccwCycle_mem cycD 1), hd13⟩, hO1_nadj, h1_inst_O1.1⟩
        · exact ⟨{d3, y0, y1}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd23, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 2), fun h => hy1_nD (h ▸ ccwCycle_mem cycD 2)⟩, hO3_nadj, h2_3.1⟩
      have hd0F : d0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 0, by simp [Q, hd01, hd02]⟩)
      have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd13.symm, hd23.symm]⟩)
      have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd14.symm, hd24.symm]⟩)
      have hy0F : y0 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have hy1F : y1 ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5 Q
        (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
        (Finset.card_pair hd12) y0 y1 hy0M hy1M hy01 hBackQ
        (fun p hp => by
          simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp; rcases hp with rfl | rfl
          · exact hex_lift_hp hd0F hy1F h1_inst_O1.2.2
          · exact hex_lift_hp hy1F hd3F h2_3.2.2)
        (hQ_disj_fn hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d1, d2])))
        (fun z hz hzD_conv => ?_)
      have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
      have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
      have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
      have hny01 : z ≠ y0 ∧ z ≠ y1 := by
        have hm := (Finset.mem_sdiff.mp hz).2
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
        exact hm
      let cycR : CCWCycle (reflPt ∘ S) D 2 := ccwCycle_rev cycD 2
      let pDR : Fin 5 → ℝ × ℝ := fun i => reflPt (S (cycR.toFun i))
      have hzR : reflPt (S z) ∈ convexHull ℝ (Set.range pDR) := by
        rw [show Set.range pDR = Set.range (fun i => (reflPt ∘ S) (cycR.toFun i)) from rfl,
          range_cyc (reflPt ∘ S) cycR]
        have him : (D.image (reflPt ∘ S) : Set (ℝ × ℝ)) = reflPt '' (D.image S : Set (ℝ × ℝ)) := by ext p; simp [Finset.coe_image]
        rw [him]; exact (reflPt_mem_convexHull (D.image S : Set (ℝ × ℝ)) (S z)).mpr hzD_conv
      have hDR0 : pDR 0 = reflPt (S d2) := rfl
      have hDR1 : pDR 1 = reflPt (S d1) := rfl
      have hDR2 : pDR 2 = reflPt (S d0) := rfl
      have hDR4' : pDR (Fin.last 4) = reflPt (S d3) := rfl
      have hcov := convD_cover_case3b_single_M0 pDR cycR.ccw (reflPt (S y1))
        ((F.image (reflPt ∘ S)) : Set (ℝ × ℝ))
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy1F))
        (fun i hi0 hi1 => Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (by
          fin_cases i
          · exact absurd rfl hi0
          · exact absurd rfl hi1
          · exact hd0F
          · exact hd4F
          · exact hd3F))) hzR
      rw [hDR0, hDR1, hDR2, hDR4'] at hcov
      have pull_mem : ∀ {T : Set (ℝ × ℝ)}, reflPt (S z) ∈ convexHull ℝ (reflPt '' T) →
          S z ∈ convexHull ℝ T := fun {T} hzT => (reflPt_mem_convexHull T (S z)).mp hzT
      rcases hcov with ((hF | hc2) | hc1) | he1
      · right; refine pull_mem ?_
        have him : reflPt '' (F.image S : Set (ℝ × ℝ)) = (F.image (reflPt ∘ S) : Set (ℝ × ℝ)) := by ext p; simp [Finset.coe_image]
        rwa [him]
      · left
        have hc2' : S z ∈ convexHull ℝ ({S d2, S y1, S d3} : Set (ℝ × ℝ)) := by
          refine pull_mem ?_
          rw [reflPt_image_tri]; exact hc2
        have hrec := hcap3 z (by rw [hoa3]; exact hny01.2) (by rw [hob3]; exact fun h => hzD (h ▸ ccwCycle_mem cycD 3))
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 3), hny01.1, hny01.2⟩)
          (by rw [hoa3, hob3, hΓ3eq, Finset.singleton_union, finset3_image_eq]; exact hc2')
        rw [hoa3, hob3] at hrec; exact hex_lift_hp hy1F hd3F hrec.2.1
      · left
        have hc1' : S z ∈ convexHull ℝ ({S d1, S d0, S y1} : Set (ℝ × ℝ)) := by
          refine pull_mem ?_
          rw [reflPt_image_tri]; exact hc1
        have hrec := hcap1 z (by rw [hO1_sel1.1]; exact fun h => hzD (h ▸ ccwCycle_mem cycD 0)) (by rw [hO1_sel1.2.1]; exact hny01.2)
          (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 0), hny01.2, fun h => hzD (h ▸ ccwCycle_mem cycD 3)⟩)
          (by rw [hO1_sel1.1, hO1_sel1.2.1, hO1_sel1.2.2, Finset.singleton_union, finset3_image_eq]; exact hc1')
        rw [hO1_sel1.1, hO1_sel1.2.1] at hrec; exact hex_lift_hp hd0F hy1F hrec.2.1
      · exfalso
        have he1' : S z ∈ convexHull ℝ ({S d1, S d2, S y1} : Set (ℝ × ℝ)) := by
          refine pull_mem ?_
          rw [reflPt_image_tri_swap12]; exact he1
        exact hy1_empty z (Finset.mem_erase.mpr ⟨hny01.2, hzM⟩) ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he1')
  have h1_inst_O4 := hΓ4 d1 (by rw [hO4_sel1.2.2]; exact Finset.mem_singleton_self _)
  rw [hO4_sel1.1, hO4_sel1.2.1] at h1_inst_O4
  have h1_inst_O3 := hΓ3 d1 (by rw [hO3_sel1.2.2]; exact Finset.mem_singleton_self _)
  rw [hO3_sel1.1, hO3_sel1.2.1] at h1_inst_O3
  refine ⟨h1_not_lr,
    ⟨by rwa [hO0_sel1.1, hO0_sel1.2.1] at hgap0, h1_inst_O0.1, h1_inst_O0.2.1, h1_inst_O0.2.2,
      fun z hz1 hz2 hzO hzconv => by
        have hc := hcap0 z (by rw [hO0_sel1.1]; exact hz1) (by rw [hO0_sel1.2.1]; exact hz2) hzO
          (by rw [hO0_sel1.1, hO0_sel1.2.1, hO0_sel1.2.2, Finset.singleton_union]; exact hzconv)
        rwa [hO0_sel1.1, hO0_sel1.2.1] at hc⟩,
    ⟨by rwa [hO1_sel1.1, hO1_sel1.2.1] at hgap1, h1_inst_O1.1, h1_inst_O1.2.1, h1_inst_O1.2.2,
      fun z hz1 hz2 hzO hzconv => by
        have hc := hcap1 z (by rw [hO1_sel1.1]; exact hz1) (by rw [hO1_sel1.2.1]; exact hz2) hzO
          (by rw [hO1_sel1.1, hO1_sel1.2.1, hO1_sel1.2.2, Finset.singleton_union]; exact hzconv)
        rwa [hO1_sel1.1, hO1_sel1.2.1] at hc⟩,
    ⟨by rwa [hO4_sel1.1, hO4_sel1.2.1] at hgap4, h1_inst_O4.1, h1_inst_O4.2.1, h1_inst_O4.2.2,
      fun z hz1 hz2 hzO hzconv => by
        have hc := hcap4 z (by rw [hO4_sel1.1]; exact hz1) (by rw [hO4_sel1.2.1]; exact hz2) hzO
          (by rw [hO4_sel1.1, hO4_sel1.2.1, hO4_sel1.2.2, Finset.singleton_union]; exact hzconv)
        rwa [hO4_sel1.1, hO4_sel1.2.1] at hc⟩,
    ⟨by rwa [hO3_sel1.1, hO3_sel1.2.1] at hgap3, h1_inst_O3.1, h1_inst_O3.2.1, h1_inst_O3.2.2,
      fun z hz1 hz2 hzO hzconv => by
        have hc := hcap3 z (by rw [hO3_sel1.1]; exact hz1) (by rw [hO3_sel1.2.1]; exact hz2) hzO
          (by rw [hO3_sel1.1, hO3_sel1.2.1, hO3_sel1.2.2, Finset.singleton_union]; exact hzconv)
        rwa [hO3_sel1.1, hO3_sel1.2.1] at hc⟩⟩

private lemma reflPt_segmentsCross (a b c d : ℝ × ℝ) :
    SegmentsCross (reflPt a) (reflPt b) (reflPt c) (reflPt d) ↔ SegmentsCross a b c d := by
  unfold SegmentsCross
  simp only [reflPt_orient2D, neg_mul_neg]

private lemma reflPt_angleLt (v q a b : ℝ × ℝ) :
    AngleLt (reflPt v) (reflPt q) (reflPt a) (reflPt b) ↔ AngleLt v q a b := by
  unfold AngleLt OnSameSide
  simp only [reflPt_orient2D, neg_mul_neg]

private lemma reflPt_goodAnchorPair {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {O_miss : Finset (Fin n)} {oa ob : Fin n} :
    GoodAnchorPair (reflPt '' P) (reflPt ∘ S) (reflPt ∘ w) O_miss oa ob ↔
      GoodAnchorPair P S w O_miss oa ob := by
  unfold GoodAnchorPair
  simp only [Function.comp_apply, reflPt_angleLt, reflPt_sees]

/-- **Proposition 8.7 (`localization`, `upper_9.tex` lines 1019–1025)**:
    When `|S| = 10`, `|D| = 5`, `{e(y) : y ∈ M} ⊆ {01, 12}`, `y0 ∈ M` is minimal on `01`, and
    `O*(y0) = {4, y0, 2}` selects `1` from `v0 = w(S \ O*(y0))`, then `1 ∉ {l, r}`, no point
    `z ∈ M \ {y0}` has `v0 z` crossing `y0 2`, `△(0, 1, y0) ∩ M' = △(y0, 1, 2) ∩ M' = ∅`,
    and `M' ∩ conv D ⊆ conv {0, y0, 2, 3, 4}`. -/
theorem localization {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card = 5)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0_ex : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r)))
    (hy0_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0,
      ¬ InClosedTri (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0) (S z))
    (hO0_sel1 :
      let O0 := ({cycD.toFun 4, y0, cycD.toFun 2} : Finset (Fin n))
      let v0 := w (Finset.univ \ O0)
      GoodAnchorPair P S w O0 y0 (cycD.toFun 2) ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) v0 ∧
      SegmentsCross v0 (S (cycD.toFun 1)) (S y0) (S (cycD.toFun 2)) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) Hp) ∧
      (∀ z : Fin n, z ≠ y0 → z ≠ cycD.toFun 2 → z ∉ O0 →
        S z ∈ convexHull ℝ (({cycD.toFun 1, y0, cycD.toFun 2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
        SegmentsCross v0 (S z) (S y0) (S (cycD.toFun 2)) ∧
        (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, cycD.toFun 2} ∅ w) (S z) Hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v0))) :
    let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
    let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
    let D := hullVertices S \ certifiedVertices S w
    let M' := (Finset.univ \ D).erase y0
    let F : Finset (Fin n) := {d0, y0, d2, d3, d4}
    let v0 := w (Finset.univ \ {d4, y0, d2})
    (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S D l r → (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ d1 ∧ r ≠ d1) ∧
    (∀ z ∈ M', ¬ SegmentsCross v0 (S z) (S y0) (S d2)) ∧
    (∀ z ∈ M', ¬ InClosedTri (S d0) (S d1) (S y0) (S z)) ∧
    (∀ z ∈ M', ¬ InClosedTri (S y0) (S d1) (S d2) (S z)) ∧
    (∀ z ∈ M', S z ∈ convexHull ℝ (D.image S : Set (ℝ × ℝ)) →
      S z ∈ convexHull ℝ (F.image S : Set (ℝ × ℝ))) := by
  intro d0 d1 d2 d3 d4 D M' F v0
  let B := hullVertices S
  let H := certifiedVertices S w
  let M := Finset.univ \ D
  let O0 : Finset (Fin n) := {d4, y0, d2}
  have hD3 : 3 ≤ D.card := by change 3 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hD5' : 5 ≤ D.card := by change 5 ≤ (hullVertices S \ certifiedVertices S w).card; omega
  have hy0_nD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hd01 : d0 ≠ d1 := cycD.inj.ne (by decide)
  have hd12 : d1 ≠ d2 := cycD.inj.ne (by decide)
  have hd13 : d1 ≠ d3 := cycD.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cycD.inj.ne (by decide)
  have hd0F : d0 ∈ F := Finset.mem_insert_self _ _
  have hy0F : y0 ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hd2F : d2 ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hd3F : d3 ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hd4F : d4 ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
  have hO0_nadj : ∀ a ∈ O0 ∩ D, ∀ b ∈ O0 ∩ D, ¬ IsCCWEdge S B a b :=
    pentagon_Ostar_nadj h25 hD5 cycD hy0_nD 4 2 (by decide) (by decide)
  have hd1_nO0 : d1 ∉ O0 := by
    simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd14, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), hd12⟩
  have h1_not_lr : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ d1 ∧ r ≠ d1 := by
    intro l r hHne hed hHneg
    rw [isCCWEdge_iff_ccwCycle cycD] at hed
    rcases hed with ⟨il, rfl, rfl⟩
    fin_cases il
    · exact False.elim (hy0_ex.2 _ _ hHne (ccwCycle_isCCWEdge cycD 0) hHneg rfl)
    · exfalso
      have h12 : (1 + 1 : Fin 5) = 2 := by decide
      have hH_01 : ∀ h ∈ H, InIntTri (w D) (S d0) (S d1) (S h) := by
        intro h hh
        have hhM : h ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh⟩
        rcases h_adj h hhM with ⟨hin, _⟩ | ⟨_, hnot⟩
        · exact hin
        · exact False.elim (hnot _ _ hHne (by rw [← h12]; exact ccwCycle_isCCWEdge cycD 1) (by simpa [h12] using hHneg) rfl)
      have hed12 : IsCCWEdge S D d1 d2 := by simpa only [d1, d2, ← h12] using ccwCycle_isCCWEdge cycD 1
      have hep := (h25.endpoint_back_criterion hHne hD5' d1 d2 d1 d2
        (ccwCycle_mem cycD 1) (ccwCycle_mem cycD 2) hd12 hed12
        (by simpa [h12] using hHneg) (Or.inl ⟨rfl, rfl⟩)
        ⟨O0, hd1_nO0, hO0_nadj, hO0_sel1.2.1⟩).1
      obtain ⟨h0, hh0⟩ := hHne
      rcases hep h0 hh0 _ _ (ccwCycle_isCCWEdge cycD 0) (hH_01 h0 hh0) with e | e
      · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 2) e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 2) e
    · exact ⟨cycD.inj.ne (by decide : (2 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1)⟩
    · exact ⟨cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1)⟩
    · exact ⟨cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (0 : Fin 5) ≠ 1)⟩
  let Q : Finset (Fin n) := {d1}
  let M0 : Finset (Fin n) := {y0}
  have hFeq : (D \ Q) ∪ M0 = F := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Q, M0, F, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨hxD, hx1⟩ | rfl)
      · dsimp [D, B, H] at hxD; rw [← cycD.image_eq] at hxD
        rcases Finset.mem_image.mp hxD with ⟨i, _, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact False.elim (hx1 rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact Or.inl ⟨ccwCycle_mem cycD 0, hd01⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨ccwCycle_mem cycD 2, hd12.symm⟩
      · exact Or.inl ⟨ccwCycle_mem cycD 3, hd13.symm⟩
      · exact Or.inl ⟨ccwCycle_mem cycD 4, hd14.symm⟩
  have hQ_sub : Q ⊆ D := Finset.singleton_subset_iff.mpr (ccwCycle_mem cycD 1)
  have hQ_card : Q.card = 1 := Finset.card_singleton d1
  have hM0_sub : M0 ⊆ M := Finset.singleton_subset_iff.mpr hy0M
  have hM'_card : M'.card = 4 := by
    dsimp [M', M, D, B, H] at hM5 ⊢
    rw [Finset.card_erase_of_mem hy0M, hM5]
  have hBackQ : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
      IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
    rw [Finset.mem_singleton] at hp; subst hp
    exact ⟨O0, hd1_nO0, hO0_nadj, hO0_sel1.2.1⟩
  have hH_cov : ∀ h ∈ H \ M0, ∃ a b : Fin n, a ∈ (D \ Q) ∪ M0 ∧ b ∈ (D \ Q) ∪ M0 ∧ a ≠ b ∧
      ∀ x ∈ WitnessSet {a, b} ∅ w, InIntTri x (S a) (S b) (S h) := fun h hh =>
    h25.side_preservation ⟨h, (Finset.mem_sdiff.mp hh).1⟩ hD5' Q M0 hQ_sub (by omega) hM0_sub hBackQ h hh
  have hQ_hp : ∀ p ∈ Q, ∃ Hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet ((D \ Q) ∪ M0) ∅ w) (S p) Hp :=
    fun p hp => by
      rw [Finset.mem_singleton] at hp; subst hp; rw [hFeq]
      exact hex_lift_hp hy0F hd2F hO0_sel1.2.2.2.1
  have h_convD_cov : ∀ z ∈ M', S z ∈ convexHull ℝ (D.image S : Set (ℝ × ℝ)) →
      (∃ Hp, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) Hp) ∨
      S z ∈ convexHull ℝ (F.image S : Set (ℝ × ℝ)) := by
    intro z hz hzD_conv
    have hznD : z ∉ D := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hz).2).2
    have hzy0 : z ≠ y0 := (Finset.mem_erase.mp hz).1
    let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
    have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
      have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
        ext p; simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, pD]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨cycD.toFun i, ccwCycle_mem cycD i, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ D := hx
          dsimp [D] at hx'; rw [← cycD.image_eq] at hx'
          rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
      rwa [hr]
    have hcov := convD_cover_case3b_single_M0 pD cycD.ccw (S y0) (F.image S : Set (ℝ × ℝ))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))
      (fun i hi0 hi1 => Finset.mem_coe.mpr (Finset.mem_image_of_mem S (by
        fin_cases i
        · exact absurd rfl hi0
        · exact absurd rfl hi1
        · exact hd2F
        · exact hd3F
        · exact hd4F))) hzD'
    rcases hcov with ((hF | hc0) | hc1) | he0
    · exact Or.inr hF
    · right
      refine convexHull_tri_subset
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd0F)))
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hy0F))) hc0
    · left
      have hc1' : S z ∈ convexHull ℝ (({d1, y0, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
        rw [finset3_image_eq]
        change S z ∈ convexHull ℝ ({S y0, S d1, S d2} : Set (ℝ × ℝ)) at hc1
        rwa [Set.insert_comm (S y0) (S d1)] at hc1
      have hzO : z ∉ O0 := by
        simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hzy0, fun h => hznD (h ▸ ccwCycle_mem cycD 2)⟩
      exact hex_lift_hp hy0F hd2F (hO0_sel1.2.2.2.2 z hzy0 (fun h => hznD (h ▸ ccwCycle_mem cycD 2)) hzO hc1').2.1
    · exact False.elim (hy0_empty z hz ((inClosedTri_iff_mem_convexHull _ _ _ _).mpr he0))
  have hcomb := combination_lemma_core hPoly h25 hQ_sub (Or.inl hQ_card) hM0_sub hQ_hp hH_cov (fun z hz => by
    have hzA : z ∈ interiorPoints S := (Finset.mem_sdiff.mp hz).1
    have hznM0 : z ∉ M0 := (Finset.mem_sdiff.mp hz).2
    have hzM' : z ∈ M' := Finset.mem_erase.mpr
      ⟨fun h => hznM0 (h ▸ Finset.mem_singleton_self _),
       Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hzA).2 (Finset.sdiff_subset hd)⟩⟩
    have hzB : S z ∈ convexHull ℝ (B.image S : Set (ℝ × ℝ)) := mem_convexHull_hullVertices S hPoly.s_inj z
    rw [hFeq]
    by_cases hHne : H.Nonempty
    · obtain ⟨l, r, hlD, hrD, _, hed', hH_neg, _, _, h_edges, _, _⟩ := h25.certified_structure.2 hHne
      have hed := hed' hD3
      obtain ⟨hl1, hr1⟩ := h1_not_lr l r hHne hed hH_neg
      have hlF : l ∈ F := by rw [← hFeq]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hlD, by simp [Q, hl1]⟩)
      have hrF : r ∈ F := by rw [← hFeq]; exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hrD, by simp [Q, hr1]⟩)
      rcases convexHull_B_subset_convD_union_lrH hPoly h25 hD3 hlD hrD h_edges hzB with hzD | hzH
      · rcases h_convD_cov z hzM' hzD with hhp | hconv
        · exact Or.inl hhp
        · exact Or.inr (convexHull_mono Set.subset_union_left hconv)
      · right
        refine convexHull_min (fun p hp => ?_) (convex_convexHull ℝ _) hzH
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨x, hx, rfl⟩
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | rfl | hxH
        · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hlF)))
        · exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hrF)))
        · by_cases hxM0 : x ∈ M0
          · have hx_y0 : x = y0 := Finset.mem_singleton.mp hxM0
            exact subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S (hx_y0 ▸ hy0F))))
          · obtain ⟨a, b, haF, hbF, _, hin⟩ := hH_cov x (Finset.mem_sdiff.mpr ⟨hxH, hxM0⟩)
            rw [hFeq] at haF hbF
            have hwt := hin (w F) ⟨F, fun t ht => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with rfl | rfl <;> assumption, Finset.disjoint_empty_right _, rfl⟩
            exact convexHull_tri_subset
              (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton _)))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S haF))))
              (subset_convexHull ℝ _ (Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hbF))))
              hwt.to_convexHull
    · have hH_emp : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      have hBD : B = D := by dsimp [D, B, H]; rw [show certifiedVertices S w = ∅ from hH_emp, Finset.sdiff_empty]
      rw [hBD] at hzB
      rcases h_convD_cov z hzM' hzB with hhp | hconv
      · exact Or.inl hhp
      · exact Or.inr (convexHull_mono Set.subset_union_left hconv))
  have hM'_sdiff : M \ M0 = M' := by dsimp [M', M0]; rw [← Finset.sdiff_singleton_eq_erase]
  have h_no_hp : ∀ z ∈ M', ¬ ∃ Hp : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet F ∅ w) (S z) Hp := by
    intro z hz hhp
    have hM'4 : (M \ M0).card = 4 := by rwa [hM'_sdiff]
    have hbad := hcomb.2.2.1 hQ_card hM'4 z (by rwa [hM'_sdiff])
    rw [hFeq] at hbad; exact hbad hhp
  have h_no_tri12 : ∀ z ∈ M', ¬ InClosedTri (S y0) (S d1) (S d2) (S z) := by
    intro z hz hcl
    have hznD : z ∉ D := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hz).2).2
    have hzy0 : z ≠ y0 := (Finset.mem_erase.mp hz).1
    have hzO : z ∉ O0 := by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hzy0, fun h => hznD (h ▸ ccwCycle_mem cycD 2)⟩
    have hconv : S z ∈ convexHull ℝ (({d1, y0, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
      rw [finset3_image_eq]
      have hset : ({S y0, S d1, S d2} : Set (ℝ × ℝ)) = {S d1, S y0, S d2} := Set.insert_comm _ _ _
      rw [← hset]; exact (inClosedTri_iff_mem_convexHull _ _ _ _).mp hcl
    exact h_no_hp z hz (hex_lift_hp hy0F hd2F
      (hO0_sel1.2.2.2.2 z hzy0 (fun h => hznD (h ▸ ccwCycle_mem cycD 2)) hzO hconv).2.1)
  refine ⟨h1_not_lr, fun z hz hcross => ?_, hy0_empty, h_no_tri12, fun z hz hzD => ?_⟩
  · have hznD : z ∉ D := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hz).2).2
    have hzy0 : z ≠ y0 := (Finset.mem_erase.mp hz).1
    have hzO : z ∉ O0 := by
      simp only [O0, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hznD (h ▸ ccwCycle_mem cycD 4), hzy0, fun h => hznD (h ▸ ccwCycle_mem cycD 2)⟩
    exact h_no_hp z hz (hex_lift_hp hy0F hd2F
      (goodAnchorPair_universal_crossing hPoly h25 hO0_sel1.1 hzO hcross).1)
  · rcases h_convD_cov z hz hzD with hhp | hconv
    · exact False.elim (h_no_hp z hz hhp)
    · exact hconv

private lemma localization_symm {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card = 5)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y1 : Fin n}
    (hy1M : y1 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy1_ex : InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 1, cycD.toFun 2) ≠ (l, r)))
    (hy1_empty : ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y1) (S z))
    (hO1_sel1 :
      let O1 := ({cycD.toFun 0, y1, cycD.toFun 3} : Finset (Fin n))
      let v1 := w (Finset.univ \ O1)
      GoodAnchorPair P S w O1 (cycD.toFun 0) y1 ∧
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) v1 ∧
      SegmentsCross v1 (S (cycD.toFun 1)) (S (cycD.toFun 0)) (S y1) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, y1} ∅ w) (S (cycD.toFun 1)) Hp) ∧
      (∀ z : Fin n, z ≠ cycD.toFun 0 → z ≠ y1 → z ∉ O1 →
        S z ∈ convexHull ℝ (({cycD.toFun 1, cycD.toFun 0, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
        SegmentsCross v1 (S z) (S (cycD.toFun 0)) (S y1) ∧
        (∃ Hp, IsHalfPlaneTest P (WitnessSet {cycD.toFun 0, y1} ∅ w) (S z) Hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v1))) :
    ∀ z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1,
      ¬ InClosedTri (S (cycD.toFun 2)) (S (cycD.toFun 1)) (S y1) (S z) ∧
      ¬ InClosedTri (S y1) (S (cycD.toFun 1)) (S (cycD.toFun 0)) (S z) := by
  let P' := reflPt '' P
  let S' := reflPt ∘ S
  let w' := reflPt ∘ w
  have hPoly' := reflPt_shattered hPoly
  have h25' := reflPt_sec2to5 hPoly h25
  have hD_eq' : hullVertices S' \ certifiedVertices S' w' = hullVertices S \ certifiedVertices S w := by
    simp [S', w', reflPt_hullVertices, reflPt_certifiedVertices]
  let cycR : CCWCycle S' (hullVertices S' \ certifiedVertices S' w') 2 :=
    ccwCycle_cast hD_eq'.symm (ccwCycle_rev cycD 2)
  have hr0 : cycR.toFun 0 = cycD.toFun 2 := rfl
  have hr1 : cycR.toFun 1 = cycD.toFun 1 := rfl
  have hr2 : cycR.toFun 2 = cycD.toFun 0 := rfl
  have hr3 : cycR.toFun 3 = cycD.toFun 4 := rfl
  have hr4 : cycR.toFun 4 = cycD.toFun 3 := rfl
  have hO_eq : ({cycR.toFun 4, y1, cycR.toFun 2} : Finset (Fin n)) = {cycD.toFun 0, y1, cycD.toFun 3} := by
    rw [hr4, hr2]; ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hW_eq : ({y1, cycR.toFun 2} : Finset (Fin n)) = {cycD.toFun 0, y1} := by
    rw [hr2]; exact Finset.pair_comm _ _
  have h_loc := localization hPoly' h25' (by rwa [hD_eq']) (by rwa [hD_eq']) cycR
    (fun y hy => by
      have hy' : y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w) := by rwa [← hD_eq']
      rcases h_adj y hy' with ⟨hin, hnot⟩ | ⟨hin, hnot⟩
      · right; rw [hr1, hr2]
        refine ⟨?_, fun l r hH' hed hHn heq => ?_⟩
        · dsimp only [S', w', Function.comp_apply]; rw [hD_eq', reflPt_inIntTri]; exact hin.symm23
        · have heq' : (cycD.toFun 0, cycD.toFun 1) = (r, l) :=
            Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
          exact hnot r l (by simpa [S', w', reflPt_certifiedVertices] using hH')
            ((reflPt_isCCWEdge S _ l r).mp (hD_eq' ▸ hed))
            (fun h hh => by
              have hh' : h ∈ certifiedVertices S' w' := by simpa [S', w', reflPt_certifiedVertices] using hh
              have ho := hHn h hh'; dsimp [S'] at ho; rw [reflPt_orient2D] at ho; unfold orient2D at ho ⊢; linarith)
            heq'
      · left; rw [hr0, hr1]
        refine ⟨?_, fun l r hH' hed hHn heq => ?_⟩
        · dsimp only [S', w', Function.comp_apply]; rw [hD_eq', reflPt_inIntTri]; exact hin.symm23
        · have heq' : (cycD.toFun 1, cycD.toFun 2) = (r, l) :=
            Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
          exact hnot r l (by simpa [S', w', reflPt_certifiedVertices] using hH')
            ((reflPt_isCCWEdge S _ l r).mp (hD_eq' ▸ hed))
            (fun h hh => by
              have hh' : h ∈ certifiedVertices S' w' := by simpa [S', w', reflPt_certifiedVertices] using hh
              have ho := hHn h hh'; dsimp [S'] at ho; rw [reflPt_orient2D] at ho; unfold orient2D at ho ⊢; linarith)
            heq')
    (by rwa [hD_eq'])
    (by
      rw [hr0, hr1]
      refine ⟨by dsimp only [S', w', Function.comp_apply]; rw [hD_eq', reflPt_inIntTri]; exact hy1_ex.1.symm23,
        fun l r hH' hed hHn heq => hy1_ex.2 r l (by simpa [S', w', reflPt_certifiedVertices] using hH')
          ((reflPt_isCCWEdge S _ l r).mp (hD_eq' ▸ hed))
          (fun h hh => by
            have hh' : h ∈ certifiedVertices S' w' := by simpa [S', w', reflPt_certifiedVertices] using hh
            have ho := hHn h hh'; dsimp [S'] at ho; rw [reflPt_orient2D] at ho; unfold orient2D at ho ⊢; linarith)
          (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))⟩)
    (fun z hz hcl => by
      rw [hr0, hr1] at hcl
      have hz' : z ∈ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y1 := by rwa [← hD_eq']
      apply hy1_empty z hz'
      rw [inClosedTri_iff_mem_convexHull] at hcl ⊢
      have pull_mem : ∀ {T : Set (ℝ × ℝ)}, reflPt (S z) ∈ convexHull ℝ (reflPt '' T) →
          S z ∈ convexHull ℝ T := fun {T} hzT => (reflPt_mem_convexHull T (S z)).mp hzT
      refine pull_mem ?_
      rw [reflPt_image_tri_swap12]; exact hcl)
    (by
      rw [hO_eq, hW_eq, hr1, hr2]
      refine ⟨goodAnchorPair_symm (reflPt_goodAnchorPair.mpr hO1_sel1.1),
        ?_,
        (reflPt_segmentsCross _ _ _ _).mpr hO1_sel1.2.2.1.symm34,
        ?_, fun z hzy1 hz0 hzO hc => ?_⟩
      · rw [reflPt_hullVertices]; exact (reflPt_isBackVertexOf S _ _ _).mpr hO1_sel1.2.1
      · obtain ⟨Hp, hHp⟩ := hO1_sel1.2.2.2.1
        refine ⟨reflHP Hp, ?_⟩
        rw [reflPt_witnessSet]
        exact reflPt_isHalfPlaneTest hHp
      · have hconv : S z ∈ convexHull ℝ (({cycD.toFun 1, cycD.toFun 0, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
          have him : (({cycD.toFun 1, cycD.toFun 0, y1} : Finset (Fin n)).image S' : Set (ℝ × ℝ)) =
              reflPt '' (({cycD.toFun 1, cycD.toFun 0, y1} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by
            ext p; simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image, S', Function.comp_apply]
            constructor
            · rintro ⟨q, hq, rfl⟩; exact ⟨S q, ⟨q, hq, rfl⟩, rfl⟩
            · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩; exact ⟨q, hq, rfl⟩
          rw [him] at hc
          exact (reflPt_mem_convexHull _ _).mp hc
        have hzrec := hO1_sel1.2.2.2.2 z hz0 hzy1 hzO hconv
        refine ⟨(reflPt_segmentsCross _ _ _ _).mpr hzrec.1.symm34, ?_, fun hzB => ?_⟩
        · obtain ⟨Hp, hHp⟩ := hzrec.2.1
          refine ⟨reflHP Hp, ?_⟩
          rw [reflPt_witnessSet]
          exact reflPt_isHalfPlaneTest hHp
        · rw [reflPt_hullVertices] at hzB ⊢
          exact (reflPt_isBackVertexOf S (hullVertices S) _ _).mpr (hzrec.2.2 hzB))
  intro z hz
  have hz' : z ∈ (Finset.univ \ (hullVertices S' \ certifiedVertices S' w')).erase y1 := by rwa [hD_eq']
  have hc1 := h_loc.2.2.1 z hz'
  have hc2 := h_loc.2.2.2.1 z hz'
  rw [hr0, hr1] at hc1
  rw [hr1, hr2] at hc2
  have pull_mem : ∀ {T : Set (ℝ × ℝ)}, reflPt (S z) ∈ convexHull ℝ (reflPt '' T) →
      S z ∈ convexHull ℝ T := fun {T} hzT => (reflPt_mem_convexHull T (S z)).mp hzT
  refine ⟨fun hcl => hc1 ?_, fun hcl => hc2 ?_⟩
  · rw [inClosedTri_iff_mem_convexHull] at hcl ⊢
    rw [show ({S' (cycD.toFun 2), S' (cycD.toFun 1), S' y1} : Set (ℝ × ℝ)) =
        reflPt '' ({S (cycD.toFun 2), S (cycD.toFun 1), S y1} : Set (ℝ × ℝ)) by
      ext p; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, S', Function.comp_apply]
      constructor
      · rintro (rfl | rfl | rfl) <;> [exact ⟨_, Or.inl rfl, rfl⟩; exact ⟨_, Or.inr (Or.inl rfl), rfl⟩; exact ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto]
    exact (reflPt_mem_convexHull _ _).mpr hcl
  · rw [inClosedTri_iff_mem_convexHull] at hcl ⊢
    rw [show ({S' y1, S' (cycD.toFun 1), S' (cycD.toFun 0)} : Set (ℝ × ℝ)) =
        reflPt '' ({S y1, S (cycD.toFun 1), S (cycD.toFun 0)} : Set (ℝ × ℝ)) by
      ext p; simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, S', Function.comp_apply]
      constructor
      · rintro (rfl | rfl | rfl) <;> [exact ⟨_, Or.inl rfl, rfl⟩; exact ⟨_, Or.inr (Or.inl rfl), rfl⟩; exact ⟨_, Or.inr (Or.inr rfl), rfl⟩]
      · rintro ⟨q, rfl | rfl | rfl, rfl⟩ <;> tauto]
    exact (reflPt_mem_convexHull _ _).mpr hcl

private lemma prop88_goodAnchorPair_of_see {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {O_miss : Finset (Fin n)} {oa ob : Fin n}
    (hao : oa ∈ O_miss) (hbo : ob ∈ O_miss) (hne : oa ≠ ob)
    (hsee : Sees P (w (Finset.univ \ O_miss)) (w Finset.univ))
    (hss : OnSameSide (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) (S ob))
    (hnc : orient2D (w (Finset.univ \ O_miss)) (S oa) (S ob) ≠ 0) :
    GoodAnchorPair P S w O_miss oa ob := by
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  refine ⟨hao, hbo, hne, ?_⟩
  have hqa : orient2D v q (S oa) ≠ 0 := fun h => by
    unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  rcases lt_or_gt_of_ne hnc with hneg | hpos <;> rcases lt_or_gt_of_ne hqa with hqn | hqp
  · left; exact ⟨⟨hss, mul_pos_of_neg_of_neg hqn hneg⟩, Or.inl hsee⟩
  · right
    have hpos' : 0 < orient2D v (S ob) (S oa) := by unfold orient2D at hneg ⊢; linarith
    have hqb_pos : 0 < orient2D v q (S ob) := by unfold OnSameSide at hss; nlinarith
    exact ⟨⟨hss.symm, mul_pos hqb_pos hpos'⟩, Or.inl hsee⟩
  · right
    have hqb : orient2D v q (S ob) < 0 := by unfold OnSameSide at hss; nlinarith
    have hneg' : orient2D v (S ob) (S oa) < 0 := by unfold orient2D at hpos ⊢; linarith
    exact ⟨⟨hss.symm, mul_pos_of_neg_of_neg hqb hneg'⟩, Or.inl hsee⟩
  · left; exact ⟨⟨hss, mul_pos hqp hpos⟩, Or.inl hsee⟩

private lemma prop88_goodAnchorPair_of_cone_ends {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    {O_miss : Finset (Fin n)} {oa ob : Fin n}
    (hao : oa ∈ O_miss) (hbo : ob ∈ O_miss) (hne : oa ≠ ob)
    (hss : OnSameSide (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) (S ob))
    (ho : 0 < orient2D (w (Finset.univ \ O_miss)) (S oa) (S ob))
    (he1 : 0 < orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) →
      ∃ e1 : Fin n, e1 ∉ O_miss ∧
        0 < orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S e1) ∧
        0 < orient2D (w (Finset.univ \ O_miss)) (S e1) (S oa))
    (he2 : orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S oa) < 0 →
      ∃ e2 : Fin n, e2 ∉ O_miss ∧
        orient2D (w (Finset.univ \ O_miss)) (w Finset.univ) (S e2) < 0 ∧
        0 < orient2D (w (Finset.univ \ O_miss)) (S ob) (S e2)) :
    GoodAnchorPair P S w O_miss oa ob := by
  let v := w (Finset.univ \ O_miss)
  let q := w Finset.univ
  refine ⟨hao, hbo, hne, ?_⟩
  have hqa : orient2D v q (S oa) ≠ 0 := fun h => by
    unfold OnSameSide at hss; rw [h, zero_mul] at hss; linarith
  rcases lt_or_gt_of_ne hqa with hqn | hqp
  · have hqb : orient2D v q (S ob) < 0 := by unfold OnSameSide at hss; nlinarith
    obtain ⟨e2, he2O, he2q, he2o⟩ := he2 hqn
    right
    refine ⟨⟨hss.symm, mul_pos_of_neg_of_neg hqb (by unfold orient2D at ho ⊢; linarith)⟩, ?_⟩
    right
    refine ⟨e2, he2O, ⟨by unfold OnSameSide; exact mul_pos_of_neg_of_neg he2q hqb, ?_⟩⟩
    exact mul_pos_of_neg_of_neg he2q (by unfold orient2D at he2o ⊢; linarith)
  · obtain ⟨e1, he1O, he1q, he1o⟩ := he1 hqp
    left
    refine ⟨⟨hss, mul_pos hqp ho⟩, Or.inr ⟨e1, he1O, ⟨by unfold OnSameSide; exact mul_pos he1q hqp, ?_⟩⟩⟩
    exact mul_pos he1q he1o

private lemma fgp_gap_123_local {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    {Ov : Finset (Fin n)} {y0 y0' yj : Fin n}
    (hOv : Ov = {cycD.toFun 4, y0, y0'})
    (hy0_nD : y0 ∉ hullVertices S \ certifiedVertices S w)
    (hy0'_nD : y0' ∉ hullVertices S \ certifiedVertices S w)
    (hyj_nD : yj ∉ hullVertices S \ certifiedVertices S w)
    (hyj_O : yj ∈ Ov)
    (hsee : Sees P (w (Finset.univ \ Ov)) (w Finset.univ))
    (hyj_v : InIntTri (w (Finset.univ \ Ov)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S yj))
    (hd1_nO : cycD.toFun 1 ∉ Ov) (hd2_nO : cycD.toFun 2 ∉ Ov)
    (hss_j4 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S yj) (S (cycD.toFun 4)))
    (hvj1 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 1)))
    (hvj2 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 2)))
    (hvj3 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 3)))
    (hv14 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 1)) (S (cycD.toFun 4)))
    (hv24 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 2)) (S (cycD.toFun 4)))
    (hv34 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 3)) (S (cycD.toFun 4)))
    (hvj4 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 4))) :
    False := by
  have hd4_O : cycD.toFun 4 ∈ Ov := by rw [hOv]; exact Finset.mem_insert_self _ _
  have hgap_v : GoodAnchorPair P S w Ov yj (cycD.toFun 4) :=
    prop88_goodAnchorPair_of_see hyj_O hd4_O (fun h => hyj_nD (h.symm ▸ ccwCycle_mem cycD 4))
      hsee hss_j4 (ne_of_gt hvj4)
  have hd3_nO : cycD.toFun 3 ∉ Ov := by
    rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cycD.inj.ne (by decide), fun h => hy0_nD (h ▸ ccwCycle_mem cycD 3),
      fun h => hy0'_nD (h ▸ ccwCycle_mem cycD 3)⟩
  have hcr1 := segmentsCross_inIntTri_right hyj_v hvj1 hv14 hvj4
    (cycD.ccw_tri 0 1 4 (by decide) (by decide)) (by rw [orient2D_self_left])
  have hcr2 := segmentsCross_inIntTri_right hyj_v hvj2 hv24 hvj4
    (cycD.ccw_tri 0 2 4 (by decide) (by decide))
    (le_of_lt (cycD.ccw_tri 1 2 4 (by decide) (by decide)))
  have hcr3 := segmentsCross_inIntTri_right hyj_v hvj3 hv34 hvj4
    (cycD.ccw_tri 0 3 4 (by decide) (by decide))
    (le_of_lt (cycD.ccw_tri 1 3 4 (by decide) (by decide)))
  obtain ⟨Hp1, hHp1⟩ := (goodAnchorPair_universal_crossing hPoly h25 hgap_v hd1_nO hcr1).1
  obtain ⟨Hp2, hHp2⟩ := (goodAnchorPair_universal_crossing hPoly h25 hgap_v hd2_nO hcr2).1
  obtain ⟨Hp3, hHp3⟩ := (goodAnchorPair_universal_crossing hPoly h25 hgap_v hd3_nO hcr3).1
  let p3 : Fin 3 → Fin n := fun i => match i with
    | ⟨0, _⟩ => cycD.toFun 1
    | ⟨1, _⟩ => cycD.toFun 2
    | ⟨2, _⟩ => cycD.toFun 3
  let H3 : Fin 3 → OpenHalfPlane := fun i => match i with
    | ⟨0, _⟩ => Hp1
    | ⟨1, _⟩ => Hp2
    | ⟨2, _⟩ => Hp3
  refine no_three_halfplanes_on_witnessSet hPoly h25 (Finset.disjoint_empty_right {yj, cycD.toFun 4}) p3
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (cycD.inj.ne (by decide) hij))
    (fun i => ⟨fun hi => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        fin_cases i <;> rcases hi with h | h <;>
          first | exact hyj_nD (h ▸ ccwCycle_mem cycD _) | exact cycD.inj.ne (by decide) h,
      Finset.notMem_empty _⟩)
    H3 (fun i => by fin_cases i; exact hHp1; exact hHp2; exact hHp3)

private lemma fgp_gap_0_local {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5' : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 y0' yi yj : Fin n} (hy01 : y0 ≠ y0')
    (hyij : (yi = y0 ∧ yj = y0') ∨ (yi = y0' ∧ yj = y0))
    (hy0_nD : y0 ∉ hullVertices S \ certifiedVertices S w)
    (hy0'_nD : y0' ∉ hullVertices S \ certifiedVertices S w)
    (hyiM : yi ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hyjM : yj ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0_no01 : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))
    (hy0'_quad : ∀ z ∈ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0).erase y0',
      S z ∉ convexHull ℝ ({S (cycD.toFun 0), S (cycD.toFun 1), S y0, S y0'} : Set (ℝ × ℝ)))
    (hyj_inst :
      IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ {cycD.toFun 4, yj, cycD.toFun 2})) ∧
      (∃ Hp, IsHalfPlaneTest P (WitnessSet {yj, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) Hp) ∧
      (∀ z : Fin n, z ≠ yj → z ≠ cycD.toFun 2 → z ∉ ({cycD.toFun 4, yj, cycD.toFun 2} : Finset (Fin n)) →
        S z ∈ convexHull ℝ (({cycD.toFun 1, yj, cycD.toFun 2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
        ∃ Hp, IsHalfPlaneTest P (WitnessSet {yj, cycD.toFun 2} ∅ w) (S z) Hp))
    {Ov : Finset (Fin n)} (hOv : Ov = {cycD.toFun 4, y0, y0'})
    (hyi_O : yi ∈ Ov) (hd0_nO : cycD.toFun 0 ∉ Ov)
    (hsee : Sees P (w (Finset.univ \ Ov)) (w Finset.univ))
    (hyi_v : InIntTri (w (Finset.univ \ Ov)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S yi))
    (hd0_yi : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 0)) (S yi))
    (hss_0i : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 0)) (S yi))
    (hvq_ne : ∀ x : Fin n, orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S x) ≠ 0)
    (hss_40 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 4)) (S (cycD.toFun 0)))
    (hv40 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 4)) (S (cycD.toFun 0))) :
    False := by
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
  let B := hullVertices S; let H := certifiedVertices S w
  let D := B \ H; let M := Finset.univ \ D
  have hB : D ⊆ B := Finset.sdiff_subset
  have hyi_nD : yi ∉ D := (Finset.mem_sdiff.mp hyiM).2
  have hyj_nD : yj ∉ D := (Finset.mem_sdiff.mp hyjM).2
  have hyij_ne : yi ≠ yj := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hy01; exact hy01.symm
  have hd01 : d0 ≠ d1 := cycD.inj.ne (by decide)
  have hd02 : d0 ≠ d2 := cycD.inj.ne (by decide)
  have hd03 : d0 ≠ d3 := cycD.inj.ne (by decide)
  have hd04 : d0 ≠ d4 := cycD.inj.ne (by decide)
  have hd12 : d1 ≠ d2 := cycD.inj.ne (by decide)
  have hd13 : d1 ≠ d3 := cycD.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cycD.inj.ne (by decide)
  have hd4_O : d4 ∈ Ov := by rw [hOv]; exact Finset.mem_insert_self _ _
  have hv4i : 0 < orient2D (w (Finset.univ \ Ov)) (S d4) (S yi) := by
    have hid := orient2D_angle_trans_id (w (Finset.univ \ Ov)) (w Finset.univ) (S d4) (S d0) (S yi)
    unfold OnSameSide at hss_40 hss_0i
    rcases lt_or_gt_of_ne (hvq_ne d0) with hdn | hdp
    · have h4n : orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S d4) < 0 := by nlinarith
      have hin : orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S yi) < 0 := by nlinarith
      nlinarith [mul_neg_of_neg_of_pos h4n hd0_yi, mul_neg_of_neg_of_pos hin hv40]
    · have h4p : 0 < orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S d4) := by nlinarith
      have hip : 0 < orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S yi) := by nlinarith
      nlinarith [mul_pos h4p hd0_yi, mul_pos hip hv40]
  have hgap_v : GoodAnchorPair P S w Ov d4 yi :=
    prop88_goodAnchorPair_of_see hd4_O hyi_O (fun h => hyi_nD (h ▸ ccwCycle_mem cycD 4))
      hsee (hss_40.trans hss_0i) (ne_of_gt hv4i)
  have hd0_cr : SegmentsCross (w (Finset.univ \ Ov)) (S d0) (S d4) (S yi) :=
    segmentsCross_inIntTri_left hyi_v hv40 hd0_yi hv4i (by dsimp [d0]; rw [orient2D_self_right])
      (by dsimp [d0, d1, d4]; rw [orient2D_cycle, orient2D_cycle]; exact cycD.ccw_tri 0 1 4 (by decide) (by decide))
  obtain ⟨hhp0, hback0⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap_v hd0_nO hd0_cr
  have hcap0 : ∀ z : Fin n, z ≠ d4 → z ≠ yi → z ∉ Ov →
      S z ∈ convexHull ℝ ({S d0, S d4, S yi} : Set (ℝ × ℝ)) →
      ∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, yi} ∅ w) (S z) Hp := by
    intro z hzd4 hzyi hzO hc
    have hc' : S z ∈ convexHull ℝ (({d0, d4, yi} : Finset (Fin n)).image S : Set (ℝ × ℝ)) := by rwa [finset3_image_eq]
    refine (cap_crossing_of_vertices_cross hPoly h25 hgap_v {d0, d4, yi} (fun g hg => ?_)
      hzO hzd4 hzyi hc').2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · exact Or.inr (Or.inr hd0_cr)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  let Q : Finset (Fin n) := {d0, d1}
  let F : Finset (Fin n) := (D \ Q) ∪ {yi, yj}
  have hBackQ : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ c ∈ O ∩ D, ¬ IsCCWEdge S B a c) ∧
      IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · refine ⟨Ov, hd0_nO, ?_, hback0 (hB (ccwCycle_mem cycD 0))⟩
      intro a ha c hc hed
      have haD := (Finset.mem_inter.mp ha).2; have hcD := (Finset.mem_inter.mp hc).2
      have ha4 : a = d4 := by
        have hm := (Finset.mem_inter.mp ha).1; rw [hOv] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl; rfl; exact False.elim (hy0_nD haD); exact False.elim (hy0'_nD haD)
      have hc4 : c = d4 := by
        have hm := (Finset.mem_inter.mp hc).1; rw [hOv] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl; rfl; exact False.elim (hy0_nD hcD); exact False.elim (hy0'_nD hcD)
      exact hed.2.2.1 (ha4.trans hc4.symm)
    · refine ⟨{d4, yj, d2}, by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd14, fun h => hyj_nD (h ▸ ccwCycle_mem cycD 1), hd12⟩,
        pentagon_Ostar_nadj h25 hD5 cycD hyj_nD 4 2 (by decide) (by decide), hyj_inst.1⟩
  have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, hd02.symm, hd12.symm]⟩)
  have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd03.symm, hd13.symm]⟩)
  have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd04.symm, hd14.symm]⟩)
  have hyiF : yi ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hyjF : yj ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hQ_disj : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q :=
    adj_pair_H_disj hPoly h25 hD5 cycD h_adj (fun hHne l r hed hHn => hy0_no01 l r hHne hed hHn)
      (fun h2Q => False.elim (by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at h2Q
        rcases h2Q with h | h <;> [exact hd02.symm h; exact hd12.symm h]))
      hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d1]))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5' Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
    (Finset.card_pair hd01) yi yj hyiM hyjM hyij_ne hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hex_lift_hp hd4F hyiF hhp0
      · exact hex_lift_hp hyjF hd2F hyj_inst.2.1)
    hQ_disj (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hnyij : z ≠ yi ∧ z ≠ yj := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm; exact hm
  have hny00' : z ≠ y0 ∧ z ≠ y0' := by
    rcases hyij with ⟨hyi0, hyj0'⟩ | ⟨hyi0', hyj0⟩
    · exact ⟨hyi0 ▸ hnyij.1, hyj0' ▸ hnyij.2⟩
    · exact ⟨hyj0 ▸ hnyij.2, hyi0' ▸ hnyij.1⟩
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
  have hcov := convD_cover_case3b_same_edge pD cycD.ccw (S yi) (S yj) (F.image S : Set (ℝ × ℝ))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyiF))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyjF))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F))
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
  rcases hcov with ((hF | hc0) | hc1) | hquad
  · exact Or.inr hF
  · left
    have hset : ({pD 4, pD 0, S yi} : Set (ℝ × ℝ)) = {S d0, S d4, S yi} := by
      change {S d4, S d0, S yi} = {S d0, S d4, S yi}; exact Set.insert_comm _ _ _
    rw [hset] at hc0
    have hzO : z ∉ Ov := by
      rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 4), hny00'.1, hny00'.2⟩
    exact hex_lift_hp hd4F hyiF (hcap0 z (fun h => hzD (h ▸ ccwCycle_mem cycD 4)) hnyij.1 hzO hc0)
  · left
    have hset : ({S yj, pD 1, pD 2} : Set (ℝ × ℝ)) = {S d1, S yj, S d2} := by
      change {S yj, S d1, S d2} = {S d1, S yj, S d2}; exact Set.insert_comm _ _ _
    rw [hset, ← finset3_image_eq] at hc1
    have hzO : z ∉ ({d4, yj, d2} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 4), hnyij.2, fun h => hzD (h ▸ ccwCycle_mem cycD 2)⟩
    exact hex_lift_hp hyjF hd2F (hyj_inst.2.2 z hnyij.2 (fun h => hzD (h ▸ ccwCycle_mem cycD 2)) hzO hc1)
  · exfalso
    have hset : ({pD 0, pD 1, S yi, S yj} : Set (ℝ × ℝ)) = {S d0, S d1, S y0, S y0'} := by
      rcases hyij with ⟨hyi0, hyj0'⟩ | ⟨hyi0', hyj0⟩
      · rw [hyi0, hyj0']
      · rw [hyi0', hyj0]
        exact congrArg (insert (S d0)) (congrArg (insert (S d1)) (Set.pair_comm (S y0') (S y0)))
    rw [hset] at hquad
    exact hy0'_quad z (Finset.mem_erase.mpr ⟨hny00'.2, Finset.mem_erase.mpr ⟨hny00'.1, hzM⟩⟩) hquad

private lemma fgp_gap_40_b3_local {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5' : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 y0' yi yj : Fin n} (hy01 : y0 ≠ y0')
    (hyij : (yi = y0 ∧ yj = y0') ∨ (yi = y0' ∧ yj = y0))
    (hy0_nD : y0 ∉ hullVertices S \ certifiedVertices S w)
    (hy0'_nD : y0' ∉ hullVertices S \ certifiedVertices S w)
    (hyiM : yi ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hyjM : yj ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0_no01 : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))
    (hy0'_quad : ∀ z ∈ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0).erase y0',
      S z ∉ convexHull ℝ ({S (cycD.toFun 0), S (cycD.toFun 1), S y0, S y0'} : Set (ℝ × ℝ)))
    {Ov : Finset (Fin n)} (hOv : Ov = {cycD.toFun 3, y0, y0'})
    (hyi_O : yi ∈ Ov) (hd0_nO : cycD.toFun 0 ∉ Ov)
    (hsee : Sees P (w (Finset.univ \ Ov)) (w Finset.univ))
    (hyi_v : InIntTri (w (Finset.univ \ Ov)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S yi))
    (hd0_yi : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 0)) (S yi))
    (hss_0i : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 0)) (S yi))
    (hvq_ne : ∀ x : Fin n, orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S x) ≠ 0)
    (hss_34 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 3)) (S (cycD.toFun 4)))
    (hss_40 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 4)) (S (cycD.toFun 0)))
    (hv34 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 3)) (S (cycD.toFun 4)))
    (hv40 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 4)) (S (cycD.toFun 0)))
    (hv30 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 3)) (S (cycD.toFun 0))) :
    False := by
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
  let B := hullVertices S; let H := certifiedVertices S w
  let D := B \ H; let M := Finset.univ \ D
  have hB : D ⊆ B := Finset.sdiff_subset
  have hyi_nD : yi ∉ D := (Finset.mem_sdiff.mp hyiM).2
  have hyij_ne : yi ≠ yj := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hy01; exact hy01.symm
  have hd01 : d0 ≠ d1 := cycD.inj.ne (by decide)
  have hd02 : d0 ≠ d2 := cycD.inj.ne (by decide)
  have hd03 : d0 ≠ d3 := cycD.inj.ne (by decide)
  have hd04 : d0 ≠ d4 := cycD.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cycD.inj.ne (by decide)
  have hd24 : d2 ≠ d4 := cycD.inj.ne (by decide)
  have hd34 : d3 ≠ d4 := cycD.inj.ne (by decide)
  have hd3_O : d3 ∈ Ov := by rw [hOv]; exact Finset.mem_insert_self _ _
  have ots : ∀ a c e : Fin n, OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S a) (S c) →
      OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S c) (S e) →
      0 < orient2D (w (Finset.univ \ Ov)) (S a) (S c) →
      0 < orient2D (w (Finset.univ \ Ov)) (S c) (S e) →
      0 < orient2D (w (Finset.univ \ Ov)) (S a) (S e) := fun a c e hs1 hs2 hac hce => by
    have hid := orient2D_angle_trans_id (w (Finset.univ \ Ov)) (w Finset.univ) (S a) (S c) (S e)
    unfold OnSameSide at hs1 hs2
    rcases lt_or_gt_of_ne (hvq_ne c) with hcn | hcp
    · have han : orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S a) < 0 := by nlinarith
      have hen : orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S e) < 0 := by nlinarith
      nlinarith [mul_neg_of_neg_of_pos han hce, mul_neg_of_neg_of_pos hen hac]
    · have hap : 0 < orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S a) := by nlinarith
      have hep : 0 < orient2D (w (Finset.univ \ Ov)) (w Finset.univ) (S e) := by nlinarith
      nlinarith [mul_pos hap hce, mul_pos hep hac]
  have hv3i : 0 < orient2D (w (Finset.univ \ Ov)) (S d3) (S yi) :=
    ots d3 d0 yi (hss_34.trans hss_40) hss_0i hv30 hd0_yi
  have hv4i : 0 < orient2D (w (Finset.univ \ Ov)) (S d4) (S yi) :=
    ots d4 d0 yi hss_40 hss_0i hv40 hd0_yi
  have hgap_v : GoodAnchorPair P S w Ov d3 yi :=
    prop88_goodAnchorPair_of_see hd3_O hyi_O (fun h => hyi_nD (h ▸ ccwCycle_mem cycD 3))
      hsee (hss_34.trans (hss_40.trans hss_0i)) (ne_of_gt hv3i)
  have hd4_cr : SegmentsCross (w (Finset.univ \ Ov)) (S d4) (S d3) (S yi) :=
    segmentsCross_inIntTri_left hyi_v hv34 hv4i hv3i
      (le_of_lt (by have h := cycD.ccw_tri 0 3 4 (by decide) (by decide); unfold orient2D at h ⊢; linarith))
      (by have h := cycD.ccw_tri 1 3 4 (by decide) (by decide); unfold orient2D at h ⊢; linarith)
  have hd0_cr : SegmentsCross (w (Finset.univ \ Ov)) (S d0) (S d3) (S yi) :=
    segmentsCross_inIntTri_left hyi_v hv30 hd0_yi hv3i
      (by dsimp [d0]; rw [orient2D_self_right])
      (by have h := cycD.ccw_tri 0 1 3 (by decide) (by decide); unfold orient2D at h ⊢; linarith)
  have hd4_nO : d4 ∉ Ov := by
    rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hd34.symm, fun h => hy0_nD (h ▸ ccwCycle_mem cycD 4), fun h => hy0'_nD (h ▸ ccwCycle_mem cycD 4)⟩
  obtain ⟨hhp4, hback4⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap_v hd4_nO hd4_cr
  obtain ⟨hhp0, hback0⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap_v hd0_nO hd0_cr
  let Q : Finset (Fin n) := {d4, d0}
  let F : Finset (Fin n) := (D \ Q) ∪ {yi, yj}
  have hd1F : d1 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 1, by simp [Q, hd14, hd01.symm]⟩)
  have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, hd24, hd02.symm]⟩)
  have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd34, hd03.symm]⟩)
  have hyiF : yi ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hBackQ : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ c ∈ O ∩ D, ¬ IsCCWEdge S B a c) ∧
      IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    refine ⟨Ov, ?_, ?_, ?_⟩
    · rcases hp with rfl | rfl <;> [exact hd4_nO; exact hd0_nO]
    · intro a ha c hc hed
      have haD := (Finset.mem_inter.mp ha).2; have hcD := (Finset.mem_inter.mp hc).2
      have ha3 : a = d3 := by
        have hm := (Finset.mem_inter.mp ha).1; rw [hOv] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl; rfl; exact False.elim (hy0_nD haD); exact False.elim (hy0'_nD haD)
      have hc3 : c = d3 := by
        have hm := (Finset.mem_inter.mp hc).1; rw [hOv] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl; rfl; exact False.elim (hy0_nD hcD); exact False.elim (hy0'_nD hcD)
      exact hed.2.2.1 (ha3.trans hc3.symm)
    · rcases hp with rfl | rfl
      · exact hback4 (hB (ccwCycle_mem cycD 4))
      · exact hback0 (hB (ccwCycle_mem cycD 0))
  have hQ_disj : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q :=
    adj_pair_H_disj hPoly h25 hD5 cycD h_adj (fun hHne l r hed hHn => hy0_no01 l r hHne hed hHn)
      (fun h2Q => False.elim (by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at h2Q
        rcases h2Q with h | h <;> [exact hd24 h; exact hd02.symm h]))
      hBackQ (Or.inr (Or.inr rfl))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5' Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
    (Finset.card_pair hd04.symm) yi yj hyiM hyjM hyij_ne hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> [exact hex_lift_hp hd3F hyiF hhp4; exact hex_lift_hp hd3F hyiF hhp0])
    hQ_disj (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hny00' : z ≠ y0 ∧ z ≠ y0' := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    rcases hyij with ⟨hyi0, hyj0'⟩ | ⟨hyi0', hyj0⟩
    · exact ⟨hyi0 ▸ hm.1, hyj0' ▸ hm.2⟩
    · exact ⟨hyj0 ▸ hm.2, hyi0' ▸ hm.1⟩
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S yi) (S z) hzD'
  fin_cases i
  · exfalso
    have hsub : convexHull ℝ ({pD 0, pD 1, S yi} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ({S d0, S d1, S y0, S y0'} : Set (ℝ × ℝ)) :=
      convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d0]))
        (subset_convexHull ℝ _ (by simp [pD, d1]))
        (subset_convexHull ℝ _ (by rcases hyij with ⟨hyi0, _⟩ | ⟨hyi0', _⟩ <;> [rw [hyi0]; rw [hyi0']] <;> simp))
    exact hy0'_quad z (Finset.mem_erase.mpr ⟨hny00'.2, Finset.mem_erase.mpr ⟨hny00'.1, hzM⟩⟩) (hsub hi)
  · right
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd1F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyiF))) hi
  · right
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyiF))) hi
  · left
    have hsub : convexHull ℝ ({pD 3, pD 4, S yi} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({d3, d4, d0, yi} : Finset (Fin n)).image S : Set (ℝ × ℝ)) :=
      convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d3]))
        (subset_convexHull ℝ _ (by simp [pD, d4])) (subset_convexHull ℝ _ (by simp))
    have hzO : z ∉ Ov := by
      rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 3), hny00'.1, hny00'.2⟩
    exact hex_lift_hp hd3F hyiF (cap_crossing_of_vertices_cross hPoly h25 hgap_v {d3, d4, d0, yi}
      (fun g hg => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hd4_cr)
        · exact Or.inr (Or.inr hd0_cr)
        · exact Or.inr (Or.inl rfl))
      hzO (fun h => hzD (h ▸ ccwCycle_mem cycD 3))
      (by rcases hyij with ⟨hyi0, _⟩ | ⟨hyi0', _⟩ <;> [rw [hyi0]; rw [hyi0']] <;> first | exact hny00'.1 | exact hny00'.2) (hsub hi)).2.1
  · left
    have hsub : convexHull ℝ ({pD 4, pD 0, S yi} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({d3, d4, d0, yi} : Finset (Fin n)).image S : Set (ℝ × ℝ)) :=
      convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d4]))
        (subset_convexHull ℝ _ (by simp [pD, d0])) (subset_convexHull ℝ _ (by simp))
    have hzO : z ∉ Ov := by
      rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 3), hny00'.1, hny00'.2⟩
    exact hex_lift_hp hd3F hyiF (cap_crossing_of_vertices_cross hPoly h25 hgap_v {d3, d4, d0, yi}
      (fun g hg => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hd4_cr)
        · exact Or.inr (Or.inr hd0_cr)
        · exact Or.inr (Or.inl rfl))
      hzO (fun h => hzD (h ▸ ccwCycle_mem cycD 3))
      (by rcases hyij with ⟨hyi0, _⟩ | ⟨hyi0', _⟩ <;> [rw [hyi0]; rw [hyi0']] <;> first | exact hny00'.1 | exact hny00'.2) (hsub hi)).2.1

private lemma fgp_gap_12_b3_local {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5' : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 y0' yi yj : Fin n} (hy01 : y0 ≠ y0')
    (hyij : (yi = y0 ∧ yj = y0') ∨ (yi = y0' ∧ yj = y0))
    (hy0_nD : y0 ∉ hullVertices S \ certifiedVertices S w)
    (hy0'_nD : y0' ∉ hullVertices S \ certifiedVertices S w)
    (hyiM : yi ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hyjM : yj ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0_no01 : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))
    (h1_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ cycD.toFun 1 ∧ r ≠ cycD.toFun 1)
    (hy0'_quad : ∀ z ∈ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0).erase y0',
      S z ∉ convexHull ℝ ({S (cycD.toFun 0), S (cycD.toFun 1), S y0, S y0'} : Set (ℝ × ℝ)))
    {Ov : Finset (Fin n)} (hOv : Ov = {cycD.toFun 3, y0, y0'})
    (hyj_O : yj ∈ Ov) (hd1_nO : cycD.toFun 1 ∉ Ov) (hd2_nO : cycD.toFun 2 ∉ Ov)
    (hsee : Sees P (w (Finset.univ \ Ov)) (w Finset.univ))
    (hyj_v : InIntTri (w (Finset.univ \ Ov)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S yj))
    (hyj_d1 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 1)))
    (hss_j1 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S yj) (S (cycD.toFun 1)))
    (hss_12 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 1)) (S (cycD.toFun 2)))
    (hss_23 : OnSameSide (w (Finset.univ \ Ov)) (w Finset.univ) (S (cycD.toFun 2)) (S (cycD.toFun 3)))
    (hvj2 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 2)))
    (hv13 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 1)) (S (cycD.toFun 3)))
    (hv23 : 0 < orient2D (w (Finset.univ \ Ov)) (S (cycD.toFun 2)) (S (cycD.toFun 3)))
    (hvj3 : 0 < orient2D (w (Finset.univ \ Ov)) (S yj) (S (cycD.toFun 3))) :
    False := by
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
  let B := hullVertices S; let H := certifiedVertices S w
  let D := B \ H; let M := Finset.univ \ D
  have hB : D ⊆ B := Finset.sdiff_subset
  have hyj_nD : yj ∉ D := (Finset.mem_sdiff.mp hyjM).2
  have hyij_ne : yi ≠ yj := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hy01; exact hy01.symm
  have hd01 : d0 ≠ d1 := cycD.inj.ne (by decide)
  have hd02 : d0 ≠ d2 := cycD.inj.ne (by decide)
  have hd12 : d1 ≠ d2 := cycD.inj.ne (by decide)
  have hd13 : d1 ≠ d3 := cycD.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cycD.inj.ne (by decide)
  have hd23 : d2 ≠ d3 := cycD.inj.ne (by decide)
  have hd24 : d2 ≠ d4 := cycD.inj.ne (by decide)
  have hd3_O : d3 ∈ Ov := by rw [hOv]; exact Finset.mem_insert_self _ _
  have hgap_v : GoodAnchorPair P S w Ov yj d3 :=
    prop88_goodAnchorPair_of_see hyj_O hd3_O (fun h => hyj_nD (h.symm ▸ ccwCycle_mem cycD 3))
      hsee (hss_j1.trans (hss_12.trans hss_23)) (ne_of_gt hvj3)
  have hd1_cr : SegmentsCross (w (Finset.univ \ Ov)) (S d1) (S yj) (S d3) :=
    segmentsCross_inIntTri_right hyj_v hyj_d1 hv13 hvj3
      (cycD.ccw_tri 0 1 3 (by decide) (by decide)) (by dsimp [d1]; rw [orient2D_self_left])
  have hd2_cr : SegmentsCross (w (Finset.univ \ Ov)) (S d2) (S yj) (S d3) :=
    segmentsCross_inIntTri_right hyj_v hvj2 hv23 hvj3
      (cycD.ccw_tri 0 2 3 (by decide) (by decide)) (le_of_lt (cycD.ccw_tri 1 2 3 (by decide) (by decide)))
  obtain ⟨hhp1, hback1⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap_v hd1_nO hd1_cr
  obtain ⟨hhp2, hback2⟩ := goodAnchorPair_universal_crossing hPoly h25 hgap_v hd2_nO hd2_cr
  let Q : Finset (Fin n) := {d1, d2}
  let F : Finset (Fin n) := (D \ Q) ∪ {yi, yj}
  have hd0F : d0 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 0, by simp [Q, hd01, hd02]⟩)
  have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd13.symm, hd23.symm]⟩)
  have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd14.symm, hd24.symm]⟩)
  have hyjF : yj ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hBackQ : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
      (∀ a ∈ O ∩ D, ∀ c ∈ O ∩ D, ¬ IsCCWEdge S B a c) ∧
      IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
    refine ⟨Ov, ?_, ?_, ?_⟩
    · rcases hp with rfl | rfl <;> [exact hd1_nO; exact hd2_nO]
    · intro a ha c hc hed
      have haD := (Finset.mem_inter.mp ha).2; have hcD := (Finset.mem_inter.mp hc).2
      have ha3 : a = d3 := by
        have hm := (Finset.mem_inter.mp ha).1; rw [hOv] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl; rfl; exact False.elim (hy0_nD haD); exact False.elim (hy0'_nD haD)
      have hc3 : c = d3 := by
        have hm := (Finset.mem_inter.mp hc).1; rw [hOv] at hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl; rfl; exact False.elim (hy0_nD hcD); exact False.elim (hy0'_nD hcD)
      exact hed.2.2.1 (ha3.trans hc3.symm)
    · rcases hp with rfl | rfl
      · exact hback1 (hB (ccwCycle_mem cycD 1))
      · exact hback2 (hB (ccwCycle_mem cycD 2))
  have hQ_disj : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
      (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q :=
    adj_pair_H_disj hPoly h25 hD5 cycD h_adj (fun hHne l r hed hHn => hy0_no01 l r hHne hed hHn)
      (fun _ hHne l r hed hHn heq => (h1_not_lr l r hHne hed hHn).1 (congrArg Prod.fst heq).symm)
      hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d1, d2]))
  refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5' Q
    (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
    (Finset.card_pair hd12) yi yj hyiM hyjM hyij_ne hBackQ
    (fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> [exact hex_lift_hp hyjF hd3F hhp1; exact hex_lift_hp hyjF hd3F hhp2])
    hQ_disj (fun z hz hzD_conv => ?_)
  have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
  have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
  have hny00' : z ≠ y0 ∧ z ≠ y0' := by
    have hm := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    rcases hyij with ⟨hyi0, hyj0'⟩ | ⟨hyi0', hyj0⟩
    · exact ⟨hyi0 ▸ hm.1, hyj0' ▸ hm.2⟩
    · exact ⟨hyj0 ▸ hm.2, hyi0' ▸ hm.1⟩
  let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
  have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by rw [range_cyc_local S cycD]; exact hzD_conv
  obtain ⟨i, hi⟩ := convexHull_ray_exit_polygon_cover pD cycD.ccw (S yj) (S z) hzD'
  fin_cases i
  · exfalso
    have hsub : convexHull ℝ ({pD 0, pD 1, S yj} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ ({S d0, S d1, S y0, S y0'} : Set (ℝ × ℝ)) :=
      convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d0]))
        (subset_convexHull ℝ _ (by simp [pD, d1]))
        (subset_convexHull ℝ _ (by rcases hyij with ⟨_, hyj0'⟩ | ⟨_, hyj0⟩ <;> [rw [hyj0']; rw [hyj0]] <;> simp))
    exact hy0'_quad z (Finset.mem_erase.mpr ⟨hny00'.2, Finset.mem_erase.mpr ⟨hny00'.1, hzM⟩⟩) (hsub hi)
  · left
    have hsub : convexHull ℝ ({pD 1, pD 2, S yj} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({d1, d2, yj, d3} : Finset (Fin n)).image S : Set (ℝ × ℝ)) :=
      convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d1]))
        (subset_convexHull ℝ _ (by simp [pD, d2])) (subset_convexHull ℝ _ (by simp))
    have hzO : z ∉ Ov := by
      rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 3), hny00'.1, hny00'.2⟩
    exact hex_lift_hp hyjF hd3F (cap_crossing_of_vertices_cross hPoly h25 hgap_v {d1, d2, yj, d3}
      (fun g hg => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr hd1_cr)
        · exact Or.inr (Or.inr hd2_cr)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl))
      hzO (by rcases hyij with ⟨_, hyj0'⟩ | ⟨_, hyj0⟩ <;> [rw [hyj0']; rw [hyj0]] <;> first | exact hny00'.2 | exact hny00'.1)
      (fun h => hzD (h ▸ ccwCycle_mem cycD 3)) (hsub hi)).2.1
  · left
    have hsub : convexHull ℝ ({pD 2, pD 3, S yj} : Set (ℝ × ℝ)) ⊆
        convexHull ℝ (({d1, d2, yj, d3} : Finset (Fin n)).image S : Set (ℝ × ℝ)) :=
      convexHull_tri_subset (subset_convexHull ℝ _ (by simp [pD, d2]))
        (subset_convexHull ℝ _ (by simp [pD, d3])) (subset_convexHull ℝ _ (by simp))
    have hzO : z ∉ Ov := by
      rw [hOv]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 3), hny00'.1, hny00'.2⟩
    exact hex_lift_hp hyjF hd3F (cap_crossing_of_vertices_cross hPoly h25 hgap_v {d1, d2, yj, d3}
      (fun g hg => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr hd1_cr)
        · exact Or.inr (Or.inr hd2_cr)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl))
      hzO (by rcases hyij with ⟨_, hyj0'⟩ | ⟨_, hyj0⟩ <;> [rw [hyj0']; rw [hyj0]] <;> first | exact hny00'.2 | exact hny00'.1)
      (fun h => hzD (h ▸ ccwCycle_mem cycD 3)) (hsub hi)).2.1
  · right
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyjF))) hi
  · right
    exact convexHull_tri_subset
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd0F)))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyjF))) hi

private lemma fgp_noalt_4gon_local {n : ℕ} {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)}
    (cycD : CCWCycle S D 2) (v q : ℝ × ℝ) (hvq_ne : ∀ x : Fin n, orient2D v q (S x) ≠ 0)
    (i0 i1 i2 i3 : Fin 5) (hi01 : i0 < i1) (hi12 : i1 < i2) (hi23 : i2 < i3) :
    ¬ (OnSameSide v q (S (cycD.toFun i0)) (S (cycD.toFun i2)) ∧
       OnSameSide v q (S (cycD.toFun i1)) (S (cycD.toFun i3)) ∧
       ¬ OnSameSide v q (S (cycD.toFun i0)) (S (cycD.toFun i1))) := by
  rintro ⟨hs02, hs13, hn01⟩
  have h4g := convex_fourgon_no_alternating_line (S (cycD.toFun i0)) (S (cycD.toFun i1))
    (S (cycD.toFun i2)) (S (cycD.toFun i3)) v q
    (cycD.ccw_tri i1 i2 i3 hi12 hi23)
    (by have h := cycD.ccw_tri i0 i2 i3 (lt_trans hi01 hi12) hi23; unfold orient2D at h ⊢; linarith)
    (by have h := cycD.ccw_tri i0 i1 i3 hi01 (lt_trans hi12 hi23); unfold orient2D at h ⊢; linarith)
    (cycD.ccw_tri i0 i1 i2 hi01 hi12)
  unfold OnSameSide at hs02 hs13 hn01
  have hn01' : orient2D v q (S (cycD.toFun i0)) * orient2D v q (S (cycD.toFun i1)) < 0 :=
    lt_of_le_of_ne (not_lt.mp hn01) (mul_ne_zero (hvq_ne (cycD.toFun i0)) (hvq_ne (cycD.toFun i1)))
  rcases lt_or_gt_of_ne (hvq_ne (cycD.toFun i0)) with h0n | h0p
  · have h2n : orient2D v q (S (cycD.toFun i2)) < 0 := by
      rcases mul_pos_iff.mp hs02 with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (not_lt.mpr h0n.le h)
      · exact h
    have h1p : 0 < orient2D v q (S (cycD.toFun i1)) := by
      rcases mul_neg_iff.mp hn01' with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (not_lt.mpr h0n.le h)
      · exact h
    have h3p : 0 < orient2D v q (S (cycD.toFun i3)) := by
      rcases mul_pos_iff.mp hs13 with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (not_lt.mpr h1p.le h)
    exact h4g.2 ⟨h0n, h1p, h2n, h3p⟩
  · have h2p : 0 < orient2D v q (S (cycD.toFun i2)) := by
      rcases mul_pos_iff.mp hs02 with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (not_lt.mpr h0p.le h)
    have h1n : orient2D v q (S (cycD.toFun i1)) < 0 := by
      rcases mul_neg_iff.mp hn01' with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim (not_lt.mpr h0p.le h)
    have h3n : orient2D v q (S (cycD.toFun i3)) < 0 := by
      rcases mul_pos_iff.mp hs13 with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (not_lt.mpr h1n.le h)
      · exact h
    exact h4g.1 ⟨h0p, h1n, h2p, h3n⟩

private lemma fgp_not_all_nf_b3_local {n : ℕ}
    {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)} (cycD : CCWCycle S D 2)
    (v q : ℝ × ℝ) (yj : Fin n)
    (hvq_ne : ∀ x : Fin n, orient2D v q (S x) ≠ 0)
    (h_v01 : 0 < orient2D v (S (cycD.toFun 0)) (S (cycD.toFun 1)))
    (h_opp_01 : ¬ OnSameSide v q (S (cycD.toFun 0)) (S (cycD.toFun 1)))
    (hss_j1 : OnSameSide v q (S yj) (S (cycD.toFun 1)))
    (hyj_d1 : 0 < orient2D v (S yj) (S (cycD.toFun 1)))
    (orient_trans_sameSide : ∀ a c e : ℝ × ℝ,
      orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
      OnSameSide v q a c → OnSameSide v q c e →
      0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e)
    (orient_sameSide_between : ∀ a c e : ℝ × ℝ,
      orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
      OnSameSide v q a e →
      0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e →
      OnSameSide v q a c ∧ OnSameSide v q c e)
    (orient_oppSide_force : ∀ a c e : ℝ × ℝ,
      orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
      ¬ OnSameSide v q a c →
      0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e →
      OnSameSide v q c e)
    (h_gap_40_b3 : OnSameSide v q (S (cycD.toFun 3)) (S (cycD.toFun 4)) →
      OnSameSide v q (S (cycD.toFun 4)) (S (cycD.toFun 0)) →
      0 < orient2D v (S (cycD.toFun 3)) (S (cycD.toFun 4)) →
      0 < orient2D v (S (cycD.toFun 4)) (S (cycD.toFun 0)) →
      0 < orient2D v (S (cycD.toFun 3)) (S (cycD.toFun 0)) → False)
    (h_gap_12_b3 : OnSameSide v q (S (cycD.toFun 1)) (S (cycD.toFun 2)) →
      OnSameSide v q (S (cycD.toFun 2)) (S (cycD.toFun 3)) →
      0 < orient2D v (S yj) (S (cycD.toFun 2)) →
      0 < orient2D v (S (cycD.toFun 1)) (S (cycD.toFun 3)) →
      0 < orient2D v (S (cycD.toFun 2)) (S (cycD.toFun 3)) →
      0 < orient2D v (S yj) (S (cycD.toFun 3)) → False)
    (e_start e_end : Fin 5) {L : ℕ} (hL_cases : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4)
    (he_end_eq : e_end = e_start + finNat (2 + 3) L)
    (h_face_lt : ∀ m : Fin 5, (m - e_start).val < L → orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v < 0)
    (h_ang : ∀ a c : Fin 5, (a - e_end).val < (c - e_end).val → (c - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)))
    (h0_nf' : ¬ (0 - e_start).val < L)
    (hb_nf3 : ¬ (orient2D (S (cycD.toFun (3 - 1))) (S (cycD.toFun 3)) v < 0 ∧
      orient2D (S (cycD.toFun 3)) (S (cycD.toFun (3 + 1))) v < 0)) :
    False := by
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
  have h_case40 :
      (3 - e_end).val < (4 - e_end).val → (4 - e_end).val < (0 - e_end).val →
      (0 - e_end).val < (1 - e_end).val → (1 - e_end).val ≤ (e_start - e_end).val → False := by
    intro h34 h40 h01' h1s
    have hv34 := h_ang 3 4 h34 (le_trans (le_trans (le_of_lt h40) (le_of_lt h01')) h1s)
    have hv40 := h_ang 4 0 h40 (le_trans (le_of_lt h01') h1s)
    have hv30 := h_ang 3 0 (lt_trans h34 h40) (le_trans (le_of_lt h01') h1s)
    have hv41 := h_ang 4 1 (lt_trans h40 h01') h1s
    have hv31 := h_ang 3 1 (lt_trans (lt_trans h34 h40) h01') h1s
    have hss_40 : OnSameSide v q (S d4) (S d0) := by
      by_contra hn
      have h41 : OnSameSide v q (S d4) (S d1) := by
        unfold OnSameSide at hn h_opp_01 ⊢
        have h1 := lt_of_le_of_ne (not_lt.mp hn) (mul_ne_zero (hvq_ne d4) (hvq_ne d0))
        have h2 := lt_of_le_of_ne (not_lt.mp h_opp_01) (mul_ne_zero (hvq_ne d0) (hvq_ne d1))
        nlinarith only [h1, h2, mul_self_pos.mpr (hvq_ne d0)]
      exact h_opp_01 (orient_sameSide_between (S d4) (S d0) (S d1) (hvq_ne d4) (hvq_ne d0) (hvq_ne d1)
        h41 hv40 h_v01 hv41).2
    have hss_34 : OnSameSide v q (S d3) (S d4) := by
      by_contra hn
      have h31 : OnSameSide v q (S d3) (S d1) := by
        have h30n : orient2D v q (S d3) * orient2D v q (S d0) < 0 := by
          unfold OnSameSide at hn hss_40
          have h1 := lt_of_le_of_ne (not_lt.mp hn) (mul_ne_zero (hvq_ne d3) (hvq_ne d4))
          nlinarith only [h1, hss_40, mul_self_pos.mpr (hvq_ne d4)]
        have h01n := lt_of_le_of_ne (not_lt.mp h_opp_01) (mul_ne_zero (hvq_ne d0) (hvq_ne d1))
        unfold OnSameSide; nlinarith only [h30n, h01n, mul_self_pos.mpr (hvq_ne d0)]
      exact h_opp_01 (orient_sameSide_between (S d3) (S d0) (S d1) (hvq_ne d3) (hvq_ne d0) (hvq_ne d1)
        h31 hv30 h_v01 hv31).2
    exact h_gap_40_b3 hss_34 hss_40 hv34 hv40 hv30
  have h_case12 :
      (0 - e_end).val < (1 - e_end).val → (1 - e_end).val < (2 - e_end).val →
      (2 - e_end).val < (3 - e_end).val → (3 - e_end).val ≤ (e_start - e_end).val → False := by
    intro h01' h12 h23 h3s
    have hv12 := h_ang 1 2 h12 (le_trans (le_of_lt h23) h3s)
    have hv23 := h_ang 2 3 h23 h3s
    have hv02 := h_ang 0 2 (lt_trans h01' h12) (le_trans (le_of_lt h23) h3s)
    have hv03 := h_ang 0 3 (lt_trans (lt_trans h01' h12) h23) h3s
    have hv13 := h_ang 1 3 (lt_trans h12 h23) h3s
    have hss_12 := orient_oppSide_force (S d0) (S d1) (S d2) (hvq_ne d0) (hvq_ne d1) (hvq_ne d2)
      h_opp_01 h_v01 hv12 hv02
    have hss_23 := hss_12.symm.trans
      (orient_oppSide_force (S d0) (S d1) (S d3) (hvq_ne d0) (hvq_ne d1) (hvq_ne d3)
        h_opp_01 h_v01 hv13 hv03)
    have hvj2 := orient_trans_sameSide (S yj) (S d1) (S d2) (hvq_ne yj) (hvq_ne d1) (hvq_ne d2)
      hss_j1 hss_12 hyj_d1 hv12
    have hvj3 := orient_trans_sameSide (S yj) (S d1) (S d3) (hvq_ne yj) (hvq_ne d1) (hvq_ne d3)
      hss_j1 (hss_12.trans hss_23) hyj_d1 hv13
    exact h_gap_12_b3 hss_12 hss_23 hvj2 hv13 hv23 hvj3
  have h_b3_contra : (2 - e_start).val < L → (3 - e_start).val < L → False := fun h2 h3 =>
    hb_nf3 ⟨by rw [show (3 - 1 : Fin 5) = 2 by decide]; exact h_face_lt 2 h2,
      by rw [show (3 + 1 : Fin 5) = 4 by decide]; exact h_face_lt 3 h3⟩
  fin_cases e_start <;> rcases hL_cases with rfl | rfl | rfl | rfl
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact h_case40 (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_case40 (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_b3_contra (by decide) (by decide)
  · exact h_b3_contra (by decide) (by decide)
  · exact h_case40 (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_b3_contra (by decide) (by decide)
  · exact h_b3_contra (by decide) (by decide)
  · exact False.elim (h0_nf' (by decide))
  · exact h_case12 (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_case12 (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact h_case12 (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))

private lemma fgp_not_all_nf_b4_local {n : ℕ}
    {S : Fin n → ℝ × ℝ} {D : Finset (Fin n)} (cycD : CCWCycle S D 2)
    (v q : ℝ × ℝ) (yj : Fin n)
    (hvq_ne : ∀ x : Fin n, orient2D v q (S x) ≠ 0)
    (h_v01 : 0 < orient2D v (S (cycD.toFun 0)) (S (cycD.toFun 1)))
    (h_opp_01 : ¬ OnSameSide v q (S (cycD.toFun 0)) (S (cycD.toFun 1)))
    (hss_j1 : OnSameSide v q (S yj) (S (cycD.toFun 1)))
    (hyj_d1 : 0 < orient2D v (S yj) (S (cycD.toFun 1)))
    (orient_trans_sameSide : ∀ a c e : ℝ × ℝ,
      orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
      OnSameSide v q a c → OnSameSide v q c e →
      0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e)
    (orient_sameSide_between : ∀ a c e : ℝ × ℝ,
      orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
      OnSameSide v q a e →
      0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e →
      OnSameSide v q a c ∧ OnSameSide v q c e)
    (orient_oppSide_force : ∀ a c e : ℝ × ℝ,
      orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
      ¬ OnSameSide v q a c →
      0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e →
      OnSameSide v q c e)
    (h_gap_0 : OnSameSide v q (S (cycD.toFun 4)) (S (cycD.toFun 0)) →
      0 < orient2D v (S (cycD.toFun 4)) (S (cycD.toFun 0)) → False)
    (h_gap_123 : OnSameSide v q (S yj) (S (cycD.toFun 4)) →
      0 < orient2D v (S yj) (S (cycD.toFun 1)) → 0 < orient2D v (S yj) (S (cycD.toFun 2)) →
      0 < orient2D v (S yj) (S (cycD.toFun 3)) →
      0 < orient2D v (S (cycD.toFun 1)) (S (cycD.toFun 4)) →
      0 < orient2D v (S (cycD.toFun 2)) (S (cycD.toFun 4)) →
      0 < orient2D v (S (cycD.toFun 3)) (S (cycD.toFun 4)) →
      0 < orient2D v (S yj) (S (cycD.toFun 4)) → False)
    (e_start e_end : Fin 5) {L : ℕ} (hL_cases : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4)
    (he_end_eq : e_end = e_start + finNat (2 + 3) L)
    (h_face_lt : ∀ m : Fin 5, (m - e_start).val < L → orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v < 0)
    (h_ang : ∀ a c : Fin 5, (a - e_end).val < (c - e_end).val → (c - e_end).val ≤ (e_start - e_end).val →
      0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c)))
    (h0_nf' : ¬ (0 - e_start).val < L)
    (hb_nf4 : ¬ (orient2D (S (cycD.toFun (4 - 1))) (S (cycD.toFun 4)) v < 0 ∧
      orient2D (S (cycD.toFun 4)) (S (cycD.toFun (4 + 1))) v < 0)) :
    False := by
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
  have h_401_case :
      (∀ a c : Fin 5, (a - e_end).val < (c - e_end).val → (c - e_end).val ≤ (e_start - e_end).val →
        0 < orient2D v (S (cycD.toFun a)) (S (cycD.toFun c))) →
      (4 - e_end).val < (0 - e_end).val → (0 - e_end).val < (1 - e_end).val →
      (1 - e_end).val ≤ (e_start - e_end).val → False := by
    intro hang h40 h01' h1s
    have hv40 := hang 4 0 h40 (le_trans (le_of_lt h01') h1s)
    have hv41 := hang 4 1 (lt_trans h40 h01') h1s
    have hss_40 : OnSameSide v q (S d4) (S d0) := by
      by_contra hn
      have h41 : OnSameSide v q (S d4) (S d1) := by
        unfold OnSameSide at hn h_opp_01 ⊢
        have h1 := lt_of_le_of_ne (not_lt.mp hn) (mul_ne_zero (hvq_ne d4) (hvq_ne d0))
        have h2 := lt_of_le_of_ne (not_lt.mp h_opp_01) (mul_ne_zero (hvq_ne d0) (hvq_ne d1))
        nlinarith only [h1, h2, mul_self_pos.mpr (hvq_ne d0)]
      exact h_opp_01 (orient_sameSide_between (S d4) (S d0) (S d1) (hvq_ne d4) (hvq_ne d0) (hvq_ne d1)
        h41 hv40 h_v01 hv41).2
    exact h_gap_0 hss_40 hv40
  have h_b4_contra : (3 - e_start).val < L → (4 - e_start).val < L → False := fun h3 h4 =>
    hb_nf4 ⟨by rw [show (4 - 1 : Fin 5) = 3 by decide]; exact h_face_lt 3 h3,
      by rw [show (4 + 1 : Fin 5) = 0 by decide]; exact h_face_lt 4 h4⟩
  fin_cases e_start <;> rcases hL_cases with rfl | rfl | rfl | rfl
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact h_401_case h_ang (by rw [he_end_eq]; decide)
      (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_401_case h_ang (by rw [he_end_eq]; decide)
      (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_401_case h_ang (by rw [he_end_eq]; decide)
      (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_b4_contra (by decide) (by decide)
  · exact h_401_case h_ang (by rw [he_end_eq]; decide)
      (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_401_case h_ang (by rw [he_end_eq]; decide)
      (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_b4_contra (by decide) (by decide)
  · exact h_b4_contra (by decide) (by decide)
  · exact h_401_case h_ang (by rw [he_end_eq]; decide)
      (by rw [he_end_eq]; decide) (by rw [he_end_eq]; decide)
  · exact h_b4_contra (by decide) (by decide)
  · exact h_b4_contra (by decide) (by decide)
  · exact h_b4_contra (by decide) (by decide)
  · rw [he_end_eq] at h_ang
    have hv12 := h_ang 1 2 (by decide) (by decide)
    have hv13 := h_ang 1 3 (by decide) (by decide)
    have hv14 := h_ang 1 4 (by decide) (by decide)
    have hv24 := h_ang 2 4 (by decide) (by decide)
    have hv34 := h_ang 3 4 (by decide) (by decide)
    have hv02 := h_ang 0 2 (by decide) (by decide)
    have hv03 := h_ang 0 3 (by decide) (by decide)
    have hv04 := h_ang 0 4 (by decide) (by decide)
    have hss_12 := orient_oppSide_force (S d0) (S d1) (S d2) (hvq_ne d0) (hvq_ne d1) (hvq_ne d2)
      h_opp_01 h_v01 hv12 hv02
    have hss_13 := orient_oppSide_force (S d0) (S d1) (S d3) (hvq_ne d0) (hvq_ne d1) (hvq_ne d3)
      h_opp_01 h_v01 hv13 hv03
    have hss_14 := orient_oppSide_force (S d0) (S d1) (S d4) (hvq_ne d0) (hvq_ne d1) (hvq_ne d4)
      h_opp_01 h_v01 hv14 hv04
    have hvj2 := orient_trans_sameSide (S yj) (S d1) (S d2) (hvq_ne yj) (hvq_ne d1) (hvq_ne d2)
      hss_j1 hss_12 hyj_d1 hv12
    have hvj3 := orient_trans_sameSide (S yj) (S d1) (S d3) (hvq_ne yj) (hvq_ne d1) (hvq_ne d3)
      hss_j1 hss_13 hyj_d1 hv13
    have hvj4 := orient_trans_sameSide (S yj) (S d1) (S d4) (hvq_ne yj) (hvq_ne d1) (hvq_ne d4)
      hss_j1 hss_14 hyj_d1 hv14
    exact h_gap_123 (hss_j1.trans hss_14) hyj_d1 hvj2 hvj3 hv14 hv24 hv34 hvj4
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))
  · exact False.elim (h0_nf' (by decide))

private lemma fgp_res_pair_local {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5' : 5 ≤ (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 y0' : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0'M : y0' ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y0')
    (hy0_ex :
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0) ∧
      (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
        InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r)))
    (hy0'_ex :
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0') ∧
      (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
        InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0')) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r)))
    (hy0'_quad : ∀ z ∈ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0).erase y0',
      S z ∉ convexHull ℝ ({S (cycD.toFun 0), S (cycD.toFun 1), S y0, S y0'} : Set (ℝ × ℝ)))
    (h_both_1 : ∀ (ya : Fin n), (ya = y0 ∨ ya = y0') →
       IsBackVertexOf S (hullVertices S) (cycD.toFun 1) (w (Finset.univ \ {cycD.toFun 4, ya, cycD.toFun 2})) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {ya, cycD.toFun 2} ∅ w) (S (cycD.toFun 1)) Hp) ∧
       (∀ z : Fin n, z ≠ ya → z ≠ cycD.toFun 2 → z ∉ ({cycD.toFun 4, ya, cycD.toFun 2} : Finset (Fin n)) →
         S z ∈ convexHull ℝ (({cycD.toFun 1, ya, cycD.toFun 2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
         ∃ Hp, IsHalfPlaneTest P (WitnessSet {ya, cycD.toFun 2} ∅ w) (S z) Hp))
    (h1_not_lr : ∀ l r : Fin n, (certifiedVertices S w).Nonempty →
      IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
      (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
      l ≠ cycD.toFun 1 ∧ r ≠ cycD.toFun 1)
    {b : Fin n} (hb34 : b ∈ ({cycD.toFun 3, cycD.toFun 4} : Finset (Fin n)))
    (hd0_nO : cycD.toFun 0 ∉ ({b, y0, y0'} : Finset (Fin n)))
    (hd1_nO : cycD.toFun 1 ∉ ({b, y0, y0'} : Finset (Fin n)))
    (hd2_nO : cycD.toFun 2 ∉ ({b, y0, y0'} : Finset (Fin n)))
    (h01_nf : 0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (Finset.univ \ {b, y0, y0'})))
    (hy0_v : InIntTri (w (Finset.univ \ {b, y0, y0'})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0))
    (hy0'_v : InIntTri (w (Finset.univ \ {b, y0, y0'})) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0'))
    (hvq_ne : ∀ x : Fin n, orient2D (w (Finset.univ \ {b, y0, y0'})) (w Finset.univ) (S x) ≠ 0)
    (h_v01 : 0 < orient2D (w (Finset.univ \ {b, y0, y0'})) (S (cycD.toFun 0)) (S (cycD.toFun 1)))
    (hv_noncol : ∀ i j : Fin 5, i ≠ j →
      orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) (w (Finset.univ \ {b, y0, y0'})) ≠ 0)
    (hb_nf : ¬ IsFrontVertexOf S (hullVertices S \ certifiedVertices S w) b (w (Finset.univ \ {b, y0, y0'})))
    {yi yj : Fin n} (hyij : (yi = y0 ∧ yj = y0') ∨ (yi = y0' ∧ yj = y0))
    (hy_pos : 0 < orient2D (w (Finset.univ \ {b, y0, y0'})) (S yi) (S yj)) :
    OnSameSide (w (Finset.univ \ {b, y0, y0'})) (w Finset.univ) (S y0) (S y0') ∧
    GoodAnchorPair P S w {b, y0, y0'} y0 y0' := by
  let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
  let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
  let D := hullVertices S \ certifiedVertices S w
  let M := Finset.univ \ D
  let Ov : Finset (Fin n) := {b, y0, y0'}
  let v := w (Finset.univ \ Ov)
  let q := w Finset.univ
  have hy0_O : y0 ∈ Ov := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hy0'_O : y0' ∈ Ov := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hy0_nD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy0'_nD : y0' ∉ D := (Finset.mem_sdiff.mp hy0'M).2
  have hyiM : yi ∈ M := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hyjM : yj ∈ M := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hyi_nD : yi ∉ D := (Finset.mem_sdiff.mp hyiM).2
  have hyj_nD : yj ∉ D := (Finset.mem_sdiff.mp hyjM).2
  have hyi_v : InIntTri v (S d0) (S d1) (S yi) := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hyj_v : InIntTri v (S d0) (S d1) (S yj) := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have hyi_O : yi ∈ Ov := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Ov]
  have hyj_O : yj ∈ Ov := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Ov]
  have hyij_ne : yi ≠ yj := by rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hy01; exact hy01.symm
  have hv_0i := ((inIntTri_iff_orient_pos h01_nf).mp hyi_v.cycle).2.2
  have hv_i1 := ((inIntTri_iff_orient_pos h01_nf).mp hyi_v.cycle).2.1
  have hv_0j := ((inIntTri_iff_orient_pos h01_nf).mp hyj_v.cycle).2.2
  have hv_j1 := ((inIntTri_iff_orient_pos h01_nf).mp hyj_v.cycle).2.1
  have hd0_yi : 0 < orient2D v (S d0) (S yi) := by unfold orient2D at hv_0i ⊢; linarith
  have hyi_d1 : 0 < orient2D v (S yi) (S d1) := by unfold orient2D at hv_i1 ⊢; linarith
  have hd0_yj : 0 < orient2D v (S d0) (S yj) := by unfold orient2D at hv_0j ⊢; linarith
  have hyj_d1 : 0 < orient2D v (S yj) (S d1) := by unfold orient2D at hv_j1 ⊢; linarith
  have h_wrap : GoodAnchorPair P S w Ov yi yj → OnSameSide v q (S y0) (S y0') ∧ GoodAnchorPair P S w Ov y0 y0' := by
    intro hgap
    rcases hyij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨by rcases hgap.2.2.2 with ⟨⟨hss, _⟩, _⟩ | ⟨⟨hss, _⟩, _⟩; exact hss; exact hss.symm, hgap⟩
    · refine ⟨?_, goodAnchorPair_symm hgap⟩
      rcases hgap.2.2.2 with ⟨⟨hss, _⟩, _⟩ | ⟨⟨hss, _⟩, _⟩
      · exact hss.symm
      · exact hss
  by_cases hsee : Sees P v q
  · by_cases hss : OnSameSide v q (S yi) (S yj)
    · exact h_wrap (prop88_goodAnchorPair_of_see hyi_O hyj_O hyij_ne hsee hss (ne_of_gt hy_pos))
    · exfalso
      have h_opp_ij : orient2D v q (S yi) * orient2D v q (S yj) < 0 :=
        lt_of_le_of_ne (not_lt.mp hss) (mul_ne_zero (hvq_ne yi) (hvq_ne yj))
      have hss_0i : OnSameSide v q (S d0) (S yi) := by
        by_contra hnot
        have h_opp_0i : orient2D v q (S d0) * orient2D v q (S yi) < 0 :=
          lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero (hvq_ne d0) (hvq_ne yi))
        have hss_0j : OnSameSide v q (S d0) (S yj) := by
          unfold OnSameSide at *; nlinarith only [h_opp_0i, h_opp_ij, mul_self_pos.mpr (hvq_ne yi)]
        have hid := orient2D_angle_trans_id v q (S d0) (S yi) (S yj)
        rcases lt_or_gt_of_ne (hvq_ne d0) with hdn | hdp
        · have hjp : orient2D v q (S yj) < 0 := by unfold OnSameSide at hss_0j; nlinarith
          have hip : 0 < orient2D v q (S yi) := by nlinarith
          have : orient2D v q (S d0) * orient2D v (S yi) (S yj) < 0 := mul_neg_of_neg_of_pos hdn hy_pos
          have : orient2D v q (S yj) * orient2D v (S d0) (S yi) < 0 := mul_neg_of_neg_of_pos hjp hd0_yi
          have : 0 ≤ orient2D v q (S yi) * orient2D v (S d0) (S yj) := le_of_lt (mul_pos hip hd0_yj)
          linarith
        · have hjp : 0 < orient2D v q (S yj) := by unfold OnSameSide at hss_0j; nlinarith
          have hin : orient2D v q (S yi) < 0 := by nlinarith
          have : 0 < orient2D v q (S d0) * orient2D v (S yi) (S yj) := mul_pos hdp hy_pos
          have : 0 < orient2D v q (S yj) * orient2D v (S d0) (S yi) := mul_pos hjp hd0_yi
          have : orient2D v q (S yi) * orient2D v (S d0) (S yj) ≤ 0 := le_of_lt (mul_neg_of_neg_of_pos hin hd0_yj)
          linarith
      have hss_j1 : OnSameSide v q (S yj) (S d1) := by
        by_contra hnot
        have h_opp_j1 : orient2D v q (S yj) * orient2D v q (S d1) < 0 :=
          lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero (hvq_ne yj) (hvq_ne d1))
        have hss_i1 : OnSameSide v q (S yi) (S d1) := by
          unfold OnSameSide at *; nlinarith only [h_opp_ij, h_opp_j1, mul_self_pos.mpr (hvq_ne yj)]
        have hid := orient2D_angle_trans_id v q (S yi) (S yj) (S d1)
        rcases lt_or_gt_of_ne (hvq_ne yi) with hin | hip
        · have h1n : orient2D v q (S d1) < 0 := by unfold OnSameSide at hss_i1; nlinarith
          have hjp : 0 < orient2D v q (S yj) := by nlinarith
          have : orient2D v q (S yi) * orient2D v (S yj) (S d1) < 0 := mul_neg_of_neg_of_pos hin hyj_d1
          have : orient2D v q (S d1) * orient2D v (S yi) (S yj) < 0 := mul_neg_of_neg_of_pos h1n hy_pos
          have : 0 ≤ orient2D v q (S yj) * orient2D v (S yi) (S d1) := le_of_lt (mul_pos hjp hyi_d1)
          linarith
        · have h1p : 0 < orient2D v q (S d1) := by unfold OnSameSide at hss_i1; nlinarith
          have hjn : orient2D v q (S yj) < 0 := by nlinarith
          have : 0 < orient2D v q (S yi) * orient2D v (S yj) (S d1) := mul_pos hip hyj_d1
          have : 0 < orient2D v q (S d1) * orient2D v (S yi) (S yj) := mul_pos h1p hy_pos
          have : orient2D v q (S yj) * orient2D v (S yi) (S d1) ≤ 0 := le_of_lt (mul_neg_of_neg_of_pos hjn hyi_d1)
          linarith
      have h_chain_pos : ∀ {a c e : ℝ × ℝ}, OnSameSide v q a e →
          0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e → OnSameSide v q a c ∧ OnSameSide v q c e := by
        intro a c e hss_ae hac hce hae
        have hid := orient2D_angle_trans_id v q a c e
        have hne_a : orient2D v q a ≠ 0 := fun h => by unfold OnSameSide at hss_ae; rw [h, zero_mul] at hss_ae; linarith
        rcases lt_or_gt_of_ne hne_a with han | hap
        · have hen : orient2D v q e < 0 := by unfold OnSameSide at hss_ae; nlinarith
          have hcn : orient2D v q c < 0 := by nlinarith [mul_neg_of_neg_of_pos han hce, mul_neg_of_neg_of_pos hen hac]
          exact ⟨by unfold OnSameSide; exact mul_pos_of_neg_of_neg han hcn, by unfold OnSameSide; exact mul_pos_of_neg_of_neg hcn hen⟩
        · have hep : 0 < orient2D v q e := by unfold OnSameSide at hss_ae; nlinarith
          have hcp : 0 < orient2D v q c := by nlinarith [mul_pos hap hce, mul_pos hep hac]
          exact ⟨by unfold OnSameSide; exact mul_pos hap hcp, by unfold OnSameSide; exact mul_pos hcp hep⟩
      have orient_trans_sameSide : ∀ a c e : ℝ × ℝ,
          orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
          OnSameSide v q a c → OnSameSide v q c e →
          0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e := by
        intro a c e ha hc he hs1 hs2 hac hce
        have hid := orient2D_angle_trans_id v q a c e
        unfold OnSameSide at hs1 hs2
        rcases lt_or_gt_of_ne hc with hcn | hcp
        · have han : orient2D v q a < 0 := by nlinarith
          have hen : orient2D v q e < 0 := by nlinarith
          nlinarith [mul_neg_of_neg_of_pos han hce, mul_neg_of_neg_of_pos hen hac]
        · have hap : 0 < orient2D v q a := by nlinarith
          have hep : 0 < orient2D v q e := by nlinarith
          nlinarith [mul_pos hap hce, mul_pos hep hac]
      have orient_sameSide_between : ∀ a c e : ℝ × ℝ,
          orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
          OnSameSide v q a e →
          0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e →
          OnSameSide v q a c ∧ OnSameSide v q c e :=
        fun a c e _ _ _ hsae hac hce hae => h_chain_pos hsae hac hce hae
      have orient_oppSide_force : ∀ a c e : ℝ × ℝ,
          orient2D v q a ≠ 0 → orient2D v q c ≠ 0 → orient2D v q e ≠ 0 →
          ¬ OnSameSide v q a c →
          0 < orient2D v a c → 0 < orient2D v c e → 0 < orient2D v a e →
          OnSameSide v q c e := by
        intro a c e ha hc he hnot hac hce hae
        by_cases hsae : OnSameSide v q a e
        · exact False.elim (hnot (orient_sameSide_between a c e ha hc he hsae hac hce hae).1)
        · unfold OnSameSide at hnot hsae ⊢
          have h1 : orient2D v q a * orient2D v q c < 0 := lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero ha hc)
          have h2 : orient2D v q a * orient2D v q e < 0 := lt_of_le_of_ne (not_lt.mp hsae) (mul_ne_zero ha he)
          nlinarith only [h1, h2, mul_self_pos.mpr ha]
      have h_opp_01 : ¬ OnSameSide v q (S d0) (S d1) := fun h =>
        hss (hss_0i.symm.trans (h.trans hss_j1.symm))
      have h_gap_0 : b = d4 → OnSameSide v q (S d4) (S d0) → 0 < orient2D v (S d4) (S d0) → False :=
        fun hb_eq hss_40 hv40 =>
          fgp_gap_0_local hPoly h25 hD5 hM5' cycD h_adj hy01 hyij hy0_nD hy0'_nD hyiM hyjM
            hy0_ex.2.2 hy0'_quad
            (h_both_1 yj (by rcases hyij with ⟨_, hyj0'⟩ | ⟨_, hyj0⟩; exact Or.inr hyj0'; exact Or.inl hyj0))
            (by dsimp only [Ov, d4]; rw [hb_eq]) hyi_O hd0_nO hsee hyi_v hd0_yi hss_0i hvq_ne hss_40 hv40
      have h_gap_123 : b = d4 → OnSameSide v q (S yj) (S d4) →
          0 < orient2D v (S yj) (S d1) → 0 < orient2D v (S yj) (S d2) → 0 < orient2D v (S yj) (S d3) →
          0 < orient2D v (S d1) (S d4) → 0 < orient2D v (S d2) (S d4) → 0 < orient2D v (S d3) (S d4) →
          0 < orient2D v (S yj) (S d4) → False :=
        fun hb_eq hss_j4 hvj1 hvj2 hvj3 hv14 hv24 hv34 hvj4 =>
          fgp_gap_123_local hPoly h25 cycD (by dsimp only [Ov, d4]; rw [hb_eq]) hy0_nD hy0'_nD hyj_nD hyj_O
            hsee hyj_v hd1_nO hd2_nO hss_j4 hvj1 hvj2 hvj3 hv14 hv24 hv34 hvj4
      have h_gap_40_b3 : b = d3 → OnSameSide v q (S d3) (S d4) → OnSameSide v q (S d4) (S d0) →
          0 < orient2D v (S d3) (S d4) → 0 < orient2D v (S d4) (S d0) →
          0 < orient2D v (S d3) (S d0) → False :=
        fun hb_eq hss_34 hss_40 hv34 hv40 hv30 =>
          fgp_gap_40_b3_local hPoly h25 hD5 hM5' cycD h_adj hy01 hyij hy0_nD hy0'_nD hyiM hyjM
            hy0_ex.2.2 hy0'_quad (by dsimp only [Ov, d3]; rw [hb_eq]) hyi_O hd0_nO hsee hyi_v hd0_yi hss_0i
            hvq_ne hss_34 hss_40 hv34 hv40 hv30
      have h_gap_12_b3 : b = d3 → OnSameSide v q (S d1) (S d2) → OnSameSide v q (S d2) (S d3) →
          0 < orient2D v (S yj) (S d2) → 0 < orient2D v (S d1) (S d3) →
          0 < orient2D v (S d2) (S d3) → 0 < orient2D v (S yj) (S d3) → False :=
        fun hb_eq hss_12 hss_23 hvj2 hv13 hv23 hvj3 =>
          fgp_gap_12_b3_local hPoly h25 hD5 hM5' cycD h_adj hy01 hyij hy0_nD hy0'_nD hyiM hyjM
            hy0_ex.2.2 h1_not_lr hy0'_quad (by dsimp only [Ov, d3]; rw [hb_eq]) hyj_O hd1_nO hd2_nO hsee
            hyj_v hyj_d1 hss_j1 hss_12 hss_23 hvj2 hv13 hv23 hvj3
      by_cases h_all_nf : ∀ m : Fin 5, 0 < orient2D (S (cycD.toFun m)) (S (cycD.toFun (m + 1))) v
      · have hnf12 : 0 < orient2D v (S d1) (S d2) := by
          have h := h_all_nf 1; rw [show (1 + 1 : Fin 5) = 2 by decide] at h; unfold orient2D at h ⊢; linarith
        have hnf23 : 0 < orient2D v (S d2) (S d3) := by
          have h := h_all_nf 2; rw [show (2 + 1 : Fin 5) = 3 by decide] at h; unfold orient2D at h ⊢; linarith
        have hnf34 : 0 < orient2D v (S d3) (S d4) := by
          have h := h_all_nf 3; rw [show (3 + 1 : Fin 5) = 4 by decide] at h; unfold orient2D at h ⊢; linarith
        have hnf40 : 0 < orient2D v (S d4) (S d0) := by
          have h := h_all_nf 4; rw [show (4 + 1 : Fin 5) = 0 by decide] at h; unfold orient2D at h ⊢; linarith
        have h_noalt_4gon := fgp_noalt_4gon_local cycD v q hvq_ne
        have h_opp_ss : ∀ a c e : Fin n,
            ¬ OnSameSide v q (S a) (S c) → ¬ OnSameSide v q (S a) (S e) → OnSameSide v q (S c) (S e) := by
          intro a c e hn1 hn2
          unfold OnSameSide at hn1 hn2 ⊢
          have h1 := lt_of_le_of_ne (not_lt.mp hn1) (mul_ne_zero (hvq_ne a) (hvq_ne c))
          have h2 := lt_of_le_of_ne (not_lt.mp hn2) (mul_ne_zero (hvq_ne a) (hvq_ne e))
          nlinarith only [h1, h2, mul_self_pos.mpr (hvq_ne a)]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb34
        rcases hb34 with hb3 | hb4
        · by_cases hss_30 : OnSameSide v q (S d3) (S d0)
          · have hss_40 : OnSameSide v q (S d4) (S d0) := by
              by_contra hnot
              have hss_14 := h_opp_ss d0 d1 d4 h_opp_01 (fun h => hnot h.symm)
              exact h_noalt_4gon 0 1 3 4 (by decide) (by decide) (by decide) ⟨hss_30.symm, hss_14, h_opp_01⟩
            have hss_34 := hss_30.trans hss_40.symm
            have hv30 := orient_trans_sameSide (S d3) (S d4) (S d0) (hvq_ne d3) (hvq_ne d4) (hvq_ne d0)
              hss_34 hss_40 hnf34 hnf40
            exact h_gap_40_b3 hb3 hss_34 hss_40 hnf34 hnf40 hv30
          · have hss_13 := h_opp_ss d0 d1 d3 h_opp_01 (fun h => hss_30 h.symm)
            have hss_12 : OnSameSide v q (S d1) (S d2) := by
              by_contra hnot
              have hss_02 : OnSameSide v q (S d0) (S d2) := by
                unfold OnSameSide at h_opp_01 hnot ⊢
                have h1 := lt_of_le_of_ne (not_lt.mp h_opp_01) (mul_ne_zero (hvq_ne d0) (hvq_ne d1))
                have h2 := lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero (hvq_ne d1) (hvq_ne d2))
                nlinarith only [h1, h2, mul_self_pos.mpr (hvq_ne d1)]
              exact h_noalt_4gon 0 1 2 3 (by decide) (by decide) (by decide) ⟨hss_02, hss_13, h_opp_01⟩
            have hss_23 := hss_12.symm.trans hss_13
            have hvj2 := orient_trans_sameSide (S yj) (S d1) (S d2) (hvq_ne yj) (hvq_ne d1) (hvq_ne d2)
              hss_j1 hss_12 hyj_d1 hnf12
            have hv13 := orient_trans_sameSide (S d1) (S d2) (S d3) (hvq_ne d1) (hvq_ne d2) (hvq_ne d3)
              hss_12 hss_23 hnf12 hnf23
            have hvj3 := orient_trans_sameSide (S yj) (S d1) (S d3) (hvq_ne yj) (hvq_ne d1) (hvq_ne d3)
              hss_j1 hss_13 hyj_d1 hv13
            exact h_gap_12_b3 hb3 hss_12 hss_23 hvj2 hv13 hnf23 hvj3
        · by_cases hss_40 : OnSameSide v q (S d4) (S d0)
          · exact h_gap_0 hb4 hss_40 hnf40
          · have hss_14 := h_opp_ss d0 d1 d4 h_opp_01 (fun h => hss_40 h.symm)
            have hss_12 : OnSameSide v q (S d1) (S d2) := by
              by_contra hnot
              have hss_02 : OnSameSide v q (S d0) (S d2) := by
                unfold OnSameSide at h_opp_01 hnot ⊢
                have h1 := lt_of_le_of_ne (not_lt.mp h_opp_01) (mul_ne_zero (hvq_ne d0) (hvq_ne d1))
                have h2 := lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero (hvq_ne d1) (hvq_ne d2))
                nlinarith only [h1, h2, mul_self_pos.mpr (hvq_ne d1)]
              exact h_noalt_4gon 0 1 2 4 (by decide) (by decide) (by decide) ⟨hss_02, hss_14, h_opp_01⟩
            have hss_13 : OnSameSide v q (S d1) (S d3) := by
              by_contra hnot
              have hss_03 : OnSameSide v q (S d0) (S d3) := by
                unfold OnSameSide at h_opp_01 hnot ⊢
                have h1 := lt_of_le_of_ne (not_lt.mp h_opp_01) (mul_ne_zero (hvq_ne d0) (hvq_ne d1))
                have h2 := lt_of_le_of_ne (not_lt.mp hnot) (mul_ne_zero (hvq_ne d1) (hvq_ne d3))
                nlinarith only [h1, h2, mul_self_pos.mpr (hvq_ne d1)]
              exact h_noalt_4gon 0 1 3 4 (by decide) (by decide) (by decide) ⟨hss_03, hss_14, h_opp_01⟩
            have hss_23 := hss_12.symm.trans hss_13
            have hss_34 := hss_13.symm.trans hss_14
            have hvj2 := orient_trans_sameSide (S yj) (S d1) (S d2) (hvq_ne yj) (hvq_ne d1) (hvq_ne d2)
              hss_j1 hss_12 hyj_d1 hnf12
            have hv24 := orient_trans_sameSide (S d2) (S d3) (S d4) (hvq_ne d2) (hvq_ne d3) (hvq_ne d4)
              hss_23 hss_34 hnf23 hnf34
            have hv14 := orient_trans_sameSide (S d1) (S d2) (S d4) (hvq_ne d1) (hvq_ne d2) (hvq_ne d4)
              hss_12 (hss_23.trans hss_34) hnf12 hv24
            have hvj3 := orient_trans_sameSide (S yj) (S d2) (S d3) (hvq_ne yj) (hvq_ne d2) (hvq_ne d3)
              (hss_j1.trans hss_12) hss_23 hvj2 hnf23
            have hvj4 := orient_trans_sameSide (S yj) (S d1) (S d4) (hvq_ne yj) (hvq_ne d1) (hvq_ne d4)
              hss_j1 hss_14 hyj_d1 hv14
            exact h_gap_123 hb4 (hss_j1.trans hss_14) hyj_d1 hvj2 hvj3 hv14 hv24 hnf34 hvj4
      · push Not at h_all_nf
        obtain ⟨j0, hj0⟩ := h_all_nf
        have hj0_lt : orient2D (S (cycD.toFun j0)) (S (cycD.toFun (j0 + 1))) v < 0 :=
          lt_of_le_of_ne hj0 (hv_noncol j0 (j0 + 1) (fin_add_one_ne_self j0))
        obtain ⟨e_start, e_end, L, hL1, hL_le, he_end_eq, h_face_lt, _, _, _, _, h_ang⟩ :=
          facing_arc_complement_order cycD v hv_noncol ⟨j0, hj0_lt⟩
        have hL_cases : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 := by omega
        have h0_nf' : ¬ (0 - e_start).val < L := fun h => by
          have hf := h_face_lt 0 h; change orient2D (S d0) (S d1) v < 0 at hf; linarith
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb34
        rcases hb34 with hb3 | hb4
        · have hb_nf3 : ¬ IsFrontVertexOf S D d3 v := by
            dsimp only [D, v, Ov, d3]; rw [← hb3]; exact hb_nf
          rw [isFrontVertexOf_iff_ccwCycle cycD 3 v] at hb_nf3
          exact fgp_not_all_nf_b3_local cycD v q yj hvq_ne h_v01 h_opp_01 hss_j1 hyj_d1
            orient_trans_sameSide orient_sameSide_between orient_oppSide_force
            (h_gap_40_b3 hb3) (h_gap_12_b3 hb3) e_start e_end hL_cases he_end_eq h_face_lt
            (fun a c h1 h2 => (h_ang a c h1 h2).2) h0_nf' hb_nf3
        · have hb_nf4 : ¬ IsFrontVertexOf S D d4 v := by
            dsimp only [D, v, Ov, d4]; rw [← hb4]; exact hb_nf
          rw [isFrontVertexOf_iff_ccwCycle cycD 4 v] at hb_nf4
          exact fgp_not_all_nf_b4_local cycD v q yj hvq_ne h_v01 h_opp_01 hss_j1 hyj_d1
            orient_trans_sameSide orient_sameSide_between orient_oppSide_force
            (h_gap_0 hb4) (h_gap_123 hb4) e_start e_end hL_cases he_end_eq h_face_lt
            (fun a c h1 h2 => (h_ang a c h1 h2).2) h0_nf' hb_nf4
  · have h01_ss := seen_same_side_of_misses_q hPoly hsee d0 d1
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hd0_nO⟩) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hd1_nO⟩)
    change OnSameSide v q (S d0) (S d1) at h01_ss
    have h_pos_y : ∀ y : Fin n, InIntTri v (S d0) (S d1) (S y) →
        OnSameSide v q (S d0) (S y) ∧ OnSameSide v q (S y) (S d1) := by
      rintro y ⟨μ₁, μ₂, μ₃, _, hm2, hm3, hs, hy1, hy2⟩
      have hid := orient2D_convex_comb3 v q v (S d0) (S d1) (S y) μ₁ μ₂ μ₃ hs hy1 hy2
      rw [orient2D_self_outer, mul_zero, zero_add] at hid
      rcases lt_or_gt_of_ne (hvq_ne d0) with hd0n | hd0p
      · have hd1n : orient2D v q (S d1) < 0 := by
          rcases mul_pos_iff.mp h01_ss with ⟨h, _⟩ | ⟨_, h⟩
          · exact False.elim (not_lt.mpr hd0n.le h)
          · exact h
        have hyn : orient2D v q (S y) < 0 := by rw [hid]; exact add_neg (mul_neg_of_pos_of_neg hm2 hd0n) (mul_neg_of_pos_of_neg hm3 hd1n)
        exact ⟨by unfold OnSameSide; exact mul_pos_of_neg_of_neg hd0n hyn, by unfold OnSameSide; exact mul_pos_of_neg_of_neg hyn hd1n⟩
      · have hd1p : 0 < orient2D v q (S d1) := by
          rcases mul_pos_iff.mp h01_ss with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · exact False.elim (not_lt.mpr hd0p.le h)
        have hyp : 0 < orient2D v q (S y) := by rw [hid]; exact add_pos (mul_pos hm2 hd0p) (mul_pos hm3 hd1p)
        exact ⟨by unfold OnSameSide; exact mul_pos hd0p hyp, by unfold OnSameSide; exact mul_pos hyp hd1p⟩
    have h0i_ss : OnSameSide v q (S d0) (S yi) := (h_pos_y yi hyi_v).1
    have hj1_ss : OnSameSide v q (S yj) (S d1) := (h_pos_y yj hyj_v).2
    have hij_ss : OnSameSide v q (S yi) (S yj) := h0i_ss.symm.trans (h_pos_y yj hyj_v).1
    exact h_wrap (prop88_goodAnchorPair_of_cone_ends hyi_O hyj_O hyij_ne hij_ss hy_pos
      (fun hqi => ⟨d0, hd0_nO,
        (mul_pos_iff.mp h0i_ss).elim (fun h => h.1) (fun h => False.elim (not_lt.mpr hqi.le h.2)),
        hd0_yi⟩)
      (fun hqi => ⟨d1, hd1_nO,
        (mul_pos_iff.mp (hij_ss.trans hj1_ss)).elim
          (fun h => False.elim (not_lt.mpr hqi.le h.1)) (fun h => h.2),
        hyj_d1⟩))

/-- **Proposition 8.8 (`forced-good-pair`, `upper_9.tex` lines 1027–1035)**:
    When `|S| = 10`, `|D| = 5`, `{e(y) : y ∈ M} ⊆ {01, 12}`, and `|e⁻¹(01)| ≥ 2` with the two
    minimal points `y0, y0'` on `01`, `O*(y0)` and `O*(y0')` make the same selection in `{0, 1}`.
    When both select `1`, then for both `b ∈ {3, 4}`, `{y0, y0'}` is a `GoodAnchorPair` from
    `w(S \ {b, y0, y0'})` (both lie on one open side of `vq` and condition (iv) of Lemma 5.1 holds),
    and every `z ∉ {b, y0, y0'}` with `v z` crossing `y0 y0'` has a half-plane test on `W({y0, y0'})`. -/
theorem forced_good_pair {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w)
    (hD5 : (hullVertices S \ certifiedVertices S w).card = 5)
    (hM5 : (Finset.univ \ (hullVertices S \ certifiedVertices S w)).card = 5)
    (cycD : CCWCycle S (hullVertices S \ certifiedVertices S w) 2)
    (h_adj : ∀ y ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w),
      (0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
          InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 0, cycD.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cycD.toFun 1)) (S (cycD.toFun 2)) (w (hullVertices S \ certifiedVertices S w)) ∧
        InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cycD.toFun 1, cycD.toFun 2} ∅ w,
          InIntTri x (S (cycD.toFun 1)) (S (cycD.toFun 2)) (S y)) ∧
        (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
          IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
          (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
          (cycD.toFun 1, cycD.toFun 2) ≠ (l, r))))
    {y0 y0' : Fin n}
    (hy0M : y0 ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy0'M : y0' ∈ Finset.univ \ (hullVertices S \ certifiedVertices S w))
    (hy01 : y0 ≠ y0')
    (hy0_ex : 0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0) ∧
      (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
        InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0)) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r)))
    (hy0'_ex : 0 < orient2D (S (cycD.toFun 0)) (S (cycD.toFun 1)) (w (hullVertices S \ certifiedVertices S w)) ∧
      InIntTri (w (hullVertices S \ certifiedVertices S w)) (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0') ∧
      (∀ x ∈ WitnessSet {cycD.toFun 0, cycD.toFun 1} ∅ w,
        InIntTri x (S (cycD.toFun 0)) (S (cycD.toFun 1)) (S y0')) ∧
      (∀ l r : Fin n, (certifiedVertices S w).Nonempty →
        IsCCWEdge S (hullVertices S \ certifiedVertices S w) l r →
        (∀ h ∈ certifiedVertices S w, orient2D (S l) (S r) (S h) < 0) →
        (cycD.toFun 0, cycD.toFun 1) ≠ (l, r)))
    (hy0'_quad : ∀ z ∈ ((Finset.univ \ (hullVertices S \ certifiedVertices S w)).erase y0).erase y0',
      S z ∉ convexHull ℝ ({S (cycD.toFun 0), S (cycD.toFun 1), S y0, S y0'} : Set (ℝ × ℝ))) :
    let d0 := cycD.toFun 0; let d1 := cycD.toFun 1; let d2 := cycD.toFun 2
    let d3 := cycD.toFun 3; let d4 := cycD.toFun 4
    (∀ (sel0 sel1 : Fin n), (sel0 = d0 ∧ sel1 = d1) ∨ (sel0 = d1 ∧ sel1 = d0) →
      let ya := if sel0 = d0 then y0 else y0'
      let yb := if sel0 = d0 then y0' else y0
      let Oa : Finset (Fin n) := {d4, ya, d2}
      let Ob : Finset (Fin n) := {d4, yb, d2}
      (IsBackVertexOf S (hullVertices S) d0 (w (Finset.univ \ Oa)) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, ya} ∅ w) (S d0) Hp) ∧
       (∀ z : Fin n, z ≠ d4 → z ≠ ya → z ∉ Oa →
         S z ∈ convexHull ℝ (({d0, d4, ya} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
         ∃ Hp, IsHalfPlaneTest P (WitnessSet {d4, ya} ∅ w) (S z) Hp)) →
      (IsBackVertexOf S (hullVertices S) d1 (w (Finset.univ \ Ob)) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {yb, d2} ∅ w) (S d1) Hp) ∧
       (∀ z : Fin n, z ≠ yb → z ≠ d2 → z ∉ Ob →
         S z ∈ convexHull ℝ (({d1, yb, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
         ∃ Hp, IsHalfPlaneTest P (WitnessSet {yb, d2} ∅ w) (S z) Hp)) →
      False) ∧
    ((∀ (ya : Fin n), (ya = y0 ∨ ya = y0') →
       IsBackVertexOf S (hullVertices S) d1 (w (Finset.univ \ {d4, ya, d2})) ∧
       (∃ Hp, IsHalfPlaneTest P (WitnessSet {ya, d2} ∅ w) (S d1) Hp) ∧
       (∀ z : Fin n, z ≠ ya → z ≠ d2 → z ∉ ({d4, ya, d2} : Finset (Fin n)) →
         S z ∈ convexHull ℝ (({d1, ya, d2} : Finset (Fin n)).image S : Set (ℝ × ℝ)) →
         ∃ Hp, IsHalfPlaneTest P (WitnessSet {ya, d2} ∅ w) (S z) Hp)) →
     ∀ b ∈ ({d3, d4} : Finset (Fin n)),
      let Ov : Finset (Fin n) := {b, y0, y0'}
      let v := w (Finset.univ \ Ov)
      let q := w Finset.univ
      OnSameSide v q (S y0) (S y0') ∧
      GoodAnchorPair P S w Ov y0 y0' ∧
      (∀ z : Fin n, z ∉ Ov → SegmentsCross v (S z) (S y0) (S y0') →
        (∃ Hp, IsHalfPlaneTest P (WitnessSet {y0, y0'} ∅ w) (S z) Hp) ∧
        (z ∈ hullVertices S → IsBackVertexOf S (hullVertices S) z v))) := by
  intro d0 d1 d2 d3 d4
  let B := hullVertices S
  let H := certifiedVertices S w
  let D := B \ H
  let M := Finset.univ \ D
  have hD3 : 3 ≤ D.card := by dsimp [D, B, H] at hD5 ⊢; omega
  have hD5' : 5 ≤ D.card := le_of_eq hD5.symm
  have hM5' : 5 ≤ M.card := le_of_eq hM5.symm
  have hy0_nD : y0 ∉ D := (Finset.mem_sdiff.mp hy0M).2
  have hy0'_nD : y0' ∉ D := (Finset.mem_sdiff.mp hy0'M).2
  have hB : D ⊆ B := Finset.sdiff_subset
  have hd01 : d0 ≠ d1 := cycD.inj.ne (by decide)
  have hd02 : d0 ≠ d2 := cycD.inj.ne (by decide)
  have hd03 : d0 ≠ d3 := cycD.inj.ne (by decide)
  have hd04 : d0 ≠ d4 := cycD.inj.ne (by decide)
  have hd12 : d1 ≠ d2 := cycD.inj.ne (by decide)
  have hd13 : d1 ≠ d3 := cycD.inj.ne (by decide)
  have hd14 : d1 ≠ d4 := cycD.inj.ne (by decide)
  have hd23 : d2 ≠ d3 := cycD.inj.ne (by decide)
  have hd24 : d2 ≠ d4 := cycD.inj.ne (by decide)
  have hd34 : d3 ≠ d4 := cycD.inj.ne (by decide)
  have h1_not_lr_of_back : ∀ {ya : Fin n}, ya ∈ M →
      IsBackVertexOf S B d1 (w (Finset.univ \ {d4, ya, d2})) →
      ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ≠ d1 ∧ r ≠ d1 := by
    intro ya hyaM hback l r hHne hed hHneg
    have hya_nD : ya ∉ D := (Finset.mem_sdiff.mp hyaM).2
    have hOa_nadj : ∀ a ∈ ({d4, ya, d2} : Finset (Fin n)) ∩ D,
        ∀ b ∈ ({d4, ya, d2} : Finset (Fin n)) ∩ D, ¬ IsCCWEdge S B a b :=
      pentagon_Ostar_nadj h25 hD5 cycD hya_nD 4 2 (by decide) (by decide)
    have hd1_nOa : d1 ∉ ({d4, ya, d2} : Finset (Fin n)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd14, fun h => hya_nD (h ▸ ccwCycle_mem cycD 1), hd12⟩
    rw [isCCWEdge_iff_ccwCycle cycD] at hed
    rcases hed with ⟨il, rfl, rfl⟩
    fin_cases il
    · exact False.elim (hy0_ex.2.2.2 _ _ hHne (ccwCycle_isCCWEdge cycD 0) hHneg rfl)
    · exfalso
      have h12 : (1 + 1 : Fin 5) = 2 := by decide
      have hH_01 : ∀ h ∈ H, InIntTri (w D) (S d0) (S d1) (S h) := by
        intro h hh
        have hhM : h ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hd => (Finset.mem_sdiff.mp hd).2 hh⟩
        rcases h_adj h hhM with ⟨_, hin, _, _⟩ | ⟨_, _, _, hnot⟩
        · exact hin
        · exact False.elim (hnot _ _ hHne (by rw [← h12]; exact ccwCycle_isCCWEdge cycD 1) (by simpa [h12] using hHneg) rfl)
      have hed12 : IsCCWEdge S D d1 d2 := by simpa only [d1, d2, ← h12] using ccwCycle_isCCWEdge cycD 1
      have hep := (h25.endpoint_back_criterion hHne hD5' d1 d2 d1 d2
        (ccwCycle_mem cycD 1) (ccwCycle_mem cycD 2) hd12 hed12
        (fun h hh => by have := hHneg h hh; simp only [d1, d2, ← h12]; exact this) (Or.inl ⟨rfl, rfl⟩)
        ⟨{d4, ya, d2}, hd1_nOa, hOa_nadj, hback⟩).1
      obtain ⟨h0, hh0⟩ := hHne
      rcases hep h0 hh0 _ _ (ccwCycle_isCCWEdge cycD 0) (hH_01 h0 hh0) with e | e
      · exact cycD.inj.ne (by decide : (0 : Fin 5) ≠ 2) e
      · exact cycD.inj.ne (by decide : (1 : Fin 5) ≠ 2) e
    · exact ⟨cycD.inj.ne (by decide : (2 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1)⟩
    · exact ⟨cycD.inj.ne (by decide : (3 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1)⟩
    · exact ⟨cycD.inj.ne (by decide : (4 : Fin 5) ≠ 1), cycD.inj.ne (by decide : (0 : Fin 5) ≠ 1)⟩
  constructor
  · intro sel0 sel1 _ ya yb Oa Ob h0 h1
    have hyaM : ya ∈ M := by dsimp [ya]; split_ifs <;> assumption
    have hybM : yb ∈ M := by dsimp [yb]; split_ifs <;> assumption
    have hyab : ya ≠ yb := by dsimp [ya, yb]; split_ifs <;> [exact hy01; exact hy01.symm]
    have hya_nD : ya ∉ D := (Finset.mem_sdiff.mp hyaM).2
    have hyb_nD : yb ∉ D := (Finset.mem_sdiff.mp hybM).2
    let Q : Finset (Fin n) := {d0, d1}
    let F : Finset (Fin n) := (D \ Q) ∪ {ya, yb}
    have hBackQ : ∀ p ∈ Q, ∃ O : Finset (Fin n), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ IsCCWEdge S B a b) ∧
        IsBackVertexOf S B p (w (Finset.univ \ O)) := fun p hp => by
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact ⟨Oa, by simp only [Oa, Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd04, fun h => hya_nD (h ▸ ccwCycle_mem cycD 0), hd02⟩,
          pentagon_Ostar_nadj h25 hD5 cycD hya_nD 4 2 (by decide) (by decide), h0.1⟩
      · exact ⟨Ob, by simp only [Ob, Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hd14, fun h => hyb_nD (h ▸ ccwCycle_mem cycD 1), hd12⟩,
          pentagon_Ostar_nadj h25 hD5 cycD hyb_nD 4 2 (by decide) (by decide), h1.1⟩
    have hd2F : d2 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 2, by simp [Q, hd02.symm, hd12.symm]⟩)
    have hd3F : d3 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 3, by simp [Q, hd03.symm, hd13.symm]⟩)
    have hd4F : d4 ∈ F := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ccwCycle_mem cycD 4, by simp [Q, hd04.symm, hd14.symm]⟩)
    have hyaF : ya ∈ F := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hybF : yb ∈ F := Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hQ_disj : ∀ l r : Fin n, H.Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) → l ∉ Q ∧ r ∉ Q :=
      adj_pair_H_disj hPoly h25 hD5 cycD h_adj
        (fun hHne l r hed hHn => hy0_ex.2.2.2 l r hHne hed hHn)
        (fun h2Q => False.elim (by
          simp only [Q, Finset.mem_insert, Finset.mem_singleton] at h2Q
          rcases h2Q with h | h <;> [exact hd02.symm h; exact hd12.symm h]))
        hBackQ (Or.inl (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [d0, d1]))
    refine pentagon_Q2_M02_absurd hPoly h25 hD5 hM5' Q
      (fun x hx => by simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> exact ccwCycle_mem cycD _)
      (Finset.card_pair hd01) ya yb hyaM hybM hyab hBackQ
      (fun p hp => by
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hex_lift_hp hd4F hyaF h0.2.1
        · exact hex_lift_hp hybF hd2F h1.2.1)
      hQ_disj (fun z hz hzD_conv => ?_)
    have hznB : z ∉ hullVertices S := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
    have hzD : z ∉ D := fun hd => hznB (Finset.sdiff_subset hd)
    have hzM : z ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzD⟩
    have hnyab : z ≠ ya ∧ z ≠ yb := by
      have hm := (Finset.mem_sdiff.mp hz).2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
      exact hm
    have hny00' : z ≠ y0 ∧ z ≠ y0' := by
      dsimp [ya, yb] at hnyab
      split_ifs at hnyab
      · exact hnyab
      · exact ⟨hnyab.2, hnyab.1⟩
    let pD : Fin 5 → ℝ × ℝ := fun i => S (cycD.toFun i)
    have hzD' : S z ∈ convexHull ℝ (Set.range pD) := by
      have hr : Set.range pD = (D.image S : Set (ℝ × ℝ)) := by
        ext p; simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image, pD]
        constructor
        · rintro ⟨i, rfl⟩; exact ⟨cycD.toFun i, ccwCycle_mem cycD i, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ D := hx; dsimp [D] at hx'; rw [← cycD.image_eq] at hx'
          rcases Finset.mem_image.mp hx' with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
      rwa [hr]
    have hcov := convD_cover_case3b_same_edge pD cycD.ccw (S ya) (S yb) (F.image S : Set (ℝ × ℝ))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hyaF))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hybF))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd2F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd3F))
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S hd4F)) hzD'
    rcases hcov with ((hF | hc0) | hc1) | hquad
    · exact Or.inr hF
    · left
      have hset : ({pD 4, pD 0, S ya} : Set (ℝ × ℝ)) = {S d0, S d4, S ya} := by
        change {S d4, S d0, S ya} = {S d0, S d4, S ya}; exact Set.insert_comm _ _ _
      rw [hset, ← finset3_image_eq] at hc0
      have hzO : z ∉ Oa := by
        simp only [Oa, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 4), hnyab.1, fun h => hzD (h ▸ ccwCycle_mem cycD 2)⟩
      exact hex_lift_hp hd4F hyaF (h0.2.2 z (fun h => hzD (h ▸ ccwCycle_mem cycD 4)) hnyab.1 hzO hc0)
    · left
      have hset : ({S yb, pD 1, pD 2} : Set (ℝ × ℝ)) = {S d1, S yb, S d2} := by
        change {S yb, S d1, S d2} = {S d1, S yb, S d2}; exact Set.insert_comm _ _ _
      rw [hset, ← finset3_image_eq] at hc1
      have hzO : z ∉ Ob := by
        simp only [Ob, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hzD (h ▸ ccwCycle_mem cycD 4), hnyab.2, fun h => hzD (h ▸ ccwCycle_mem cycD 2)⟩
      exact hex_lift_hp hybF hd2F (h1.2.2 z hnyab.2 (fun h => hzD (h ▸ ccwCycle_mem cycD 2)) hzO hc1)
    · exfalso
      have hq' : S z ∈ convexHull ℝ ({S d0, S d1, S y0, S y0'} : Set (ℝ × ℝ)) := by
        have hset : ({pD 0, pD 1, S ya, S yb} : Set (ℝ × ℝ)) = {S d0, S d1, S y0, S y0'} := by
          dsimp [pD, ya, yb]
          split_ifs
          · rfl
          · exact congrArg (insert (S d0)) (congrArg (insert (S d1)) (Set.pair_comm (S y0') (S y0)))
        rwa [← hset]
      exact hy0'_quad z (Finset.mem_erase.mpr ⟨hny00'.2, Finset.mem_erase.mpr ⟨hny00'.1, hzM⟩⟩) hq'
  · intro h_both_1 b hb34
    have h1_back_y0 : IsBackVertexOf S B d1 (w (Finset.univ \ {d4, y0, d2})) := (h_both_1 y0 (Or.inl rfl)).1
    let Ov : Finset (Fin n) := {b, y0, y0'}
    let v := w (Finset.univ \ Ov)
    let q := w Finset.univ
    have hy0_O : y0 ∈ Ov := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hy0'_O : y0' ∈ Ov := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have h1_not_lr := h1_not_lr_of_back hy0M h1_back_y0
    have hb34' : b = d3 ∨ b = d4 := by simpa using hb34
    have hd0_nO : d0 ∉ Ov := by
      simp only [Ov, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by rcases hb34' with rfl | rfl <;> [exact hd03; exact hd04],
        fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0), fun h => hy0'_nD (h ▸ ccwCycle_mem cycD 0)⟩
    have hd1_nO : d1 ∉ Ov := by
      simp only [Ov, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by rcases hb34' with rfl | rfl <;> [exact hd13; exact hd14],
        fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1), fun h => hy0'_nD (h ▸ ccwCycle_mem cycD 1)⟩
    have hd2_nO : d2 ∉ Ov := by
      simp only [Ov, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by rcases hb34' with rfl | rfl <;> [exact hd23; exact hd24],
        fun h => hy0_nD (h ▸ ccwCycle_mem cycD 2), fun h => hy0'_nD (h ▸ ccwCycle_mem cycD 2)⟩
    have h01_nf : 0 < orient2D (S d0) (S d1) v := by
      have he_B : IsCCWEdge S B d0 d1 :=
        isCCWEdge_B_of_D_ne_lr h25 hD3 (ccwCycle_isCCWEdge cycD 0) (fun l r hH' _ _ _ hed hHn heq =>
          hy0_ex.2.2.2 l r hH' hed hHn heq)
      have hccw := orient2D_pos_of_isCCWEdge_B hPoly he_B (z := y0)
        (fun h => hy0_nD (h ▸ ccwCycle_mem cycD 0)) (fun h => hy0_nD (h ▸ ccwCycle_mem cycD 1))
      have hv_W01 : v ∈ WitnessSet {d0, d1} ∅ w := ⟨Finset.univ \ Ov, fun x hx =>
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl; exact hd0_nO; exact hd1_nO⟩, Finset.disjoint_empty_right _, rfl⟩
      rcases hy0_ex.2.2.1 v hv_W01 with ⟨μ₁, _, _, hm1, _, _, hsum, heq1, heq2⟩
      have hid := orient2D_convex_comb3 (S d0) (S d1) v (S d0) (S d1) (S y0) μ₁ _ _ hsum heq1 heq2
      rw [orient2D_self_outer, orient2D_self_right, mul_zero, mul_zero, add_zero, add_zero] at hid
      nlinarith
    have hy0_v : InIntTri v (S d0) (S d1) (S y0) := by
      refine hy0_ex.2.2.1 v ⟨Finset.univ \ Ov, fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exact hd0_nO; exact hd1_nO⟩,
        Finset.disjoint_empty_right _, rfl⟩
    have hy0'_v : InIntTri v (S d0) (S d1) (S y0') := by
      refine hy0'_ex.2.2.1 v ⟨Finset.univ \ Ov, fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exact hd0_nO; exact hd1_nO⟩,
        Finset.disjoint_empty_right _, rfl⟩
    have hv_ne_q : v ≠ q := by
      intro h
      have hs : Sees P v (S y0) := by rw [h]; exact (hPoly.shatters Finset.univ y0).mpr (Finset.mem_univ _)
      exact (Finset.mem_sdiff.mp ((hPoly.shatters (Finset.univ \ Ov) y0).mp hs)).2 hy0_O
    have hvq_ne : ∀ x : Fin n, orient2D v q (S x) ≠ 0 := fun x =>
      hPoly.no_three_collinear _ _ _
        (Or.inr (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.w_inj.ne (fun h => hv_ne_q (congrArg w h))) (hPoly.s_ne_w _ _).symm (hPoly.s_ne_w _ _).symm
    have h_v01 : 0 < orient2D v (S d0) (S d1) := by unfold orient2D at h01_nf ⊢; linarith
    have hv_noncol : ∀ i j : Fin 5, i ≠ j → orient2D (S (cycD.toFun i)) (S (cycD.toFun j)) v ≠ 0 :=
      fun i j hij => hPoly.no_three_collinear _ _ _
        (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inr (Set.mem_range_self _))
        (hPoly.s_inj.ne (cycD.inj.ne hij)) (hPoly.s_ne_w _ _) (hPoly.s_ne_w _ _)
    have hb_nf : ¬ IsFrontVertexOf S D b v := by
      have hbD : b ∈ D := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb34
        rcases hb34 with rfl | rfl <;> exact ccwCycle_mem cycD _
      exact no_odd_front hPoly h25 (Subset.rfl) hD3 hbD
        (fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _))
        (fun x hxD hadj => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hxO => by
          simp only [Ov, Finset.mem_insert, Finset.mem_singleton] at hxO
          rcases hxO with rfl | rfl | rfl
          · rcases hadj with e | e <;> exact e.2.2.1 rfl
          · exact hy0_nD hxD
          · exact hy0'_nD hxD⟩)
    have h_res_pair : ∀ (yi yj : Fin n),
        (yi = y0 ∧ yj = y0') ∨ (yi = y0' ∧ yj = y0) →
        0 < orient2D v (S yi) (S yj) →
        OnSameSide v q (S y0) (S y0') ∧ GoodAnchorPair P S w Ov y0 y0' :=
      fun _ _ hyij hy_pos =>
        fgp_res_pair_local hPoly h25 hD5 hM5' cycD h_adj hy0M hy0'M hy01 hy0_ex.2 hy0'_ex.2 hy0'_quad
          h_both_1 h1_not_lr hb34 hd0_nO hd1_nO hd2_nO h01_nf hy0_v hy0'_v hvq_ne h_v01 hv_noncol hb_nf
          hyij hy_pos
    have hy00'_ne : orient2D v (S y0) (S y0') ≠ 0 :=
      hPoly.no_three_collinear _ _ _
        (Or.inr (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
        (hPoly.s_ne_w _ _).symm (hPoly.s_inj.ne hy01) (hPoly.s_ne_w _ _).symm
    obtain ⟨hss_fin, hgap_fin⟩ : OnSameSide v q (S y0) (S y0') ∧ GoodAnchorPair P S w Ov y0 y0' := by
      rcases lt_or_gt_of_ne hy00'_ne with hneg | hpos
      · exact h_res_pair y0' y0 (Or.inr ⟨rfl, rfl⟩) (by unfold orient2D at hneg ⊢; linarith)
      · exact h_res_pair y0 y0' (Or.inl ⟨rfl, rfl⟩) hpos
    exact ⟨hss_fin, hgap_fin, fun z hzO hcross =>
      goodAnchorPair_universal_crossing hPoly h25 hgap_fin hzO hcross⟩


/-! ## Part 5: Section 11 Visibility Bridge and No-10-Point Shattered Polygon -/

/-- **Lemma 11.1 (`two-sided`, `upper_9.tex` lines 1492–1498)**:
    Two-sided visibility separation over `ShatteredSimplePolygon`. -/
theorem two_sided_visibility_separation {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin n} {F' : Finset (Fin n)} (hd_not : d ∉ F')
    {T_x : Finset (Fin n)} (hF'_Tx : F' ⊆ T_x) (hd_Tx : d ∉ T_x)
    {u v : Fin n} (hu : u ∈ F') (hv : v ∈ F')
    (hsep : orient2D (S d) (w T_x) (S u) * orient2D (S d) (w T_x) (S v) < 0) :
    ((∀ y ∈ WitnessSet (insert d F') ∅ w, 0 < orient2D (S d) (w T_x) y) ∨
     (∀ y ∈ WitnessSet (insert d F') ∅ w, orient2D (S d) (w T_x) y < 0)) ∧
    w T_x ∉ convexHull ℝ (WitnessSet (insert d F') ∅ w) :=
  Sec11Bridge.two_sided_visibility_separation hP hd_not hF'_Tx hd_Tx hu hv hsep

/-- **Lemma 11.3 (`adjacent-ear-empty`, `upper_9.tex` lines 1529–1546)**:
    Unconditional ear emptiness `△(0, 1, 2) ∩ M = ∅`, `w_D ∈ H^+(0, 2)`, `M ⊆ int △(w_D, 0, 2)`,
    and extraction of the five open convex wedges `W_i ⊆ U(y_i; 0, 2)` on `WitnessSet {0, 2} ∅ w`. -/
theorem adjacent_ear_empty_and_chord_wedges {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    (D M : Finset (Fin n)) (hD_eq : D = Finset.univ.image d) (hM_disj : Disjoint D M)
    (y0 y1 : Fin n) (hy0M : y0 ∈ M) (hy1M : y1 ∈ M) (hy01 : y0 ≠ y1)
    (hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y))
    (hM_12 : ∀ y ∈ M, 0 < orient2D (S (d 1)) (S (d 2)) (S y))
    (hwD_01 : 0 < orient2D (S (d 0)) (S (d 1)) (w D))
    (hwD_12 : 0 < orient2D (S (d 1)) (S (d 2)) (w D))
    (hM_exit : ∀ y ∈ M, InIntTri (w D) (S (d 0)) (S (d 1)) (S y) ∨
                        InIntTri (w D) (S (d 1)) (S (d 2)) (S y))
    (hy0_loc : ∀ z ∈ M.erase y0,
      ¬ InClosedTri (S (d 0)) (S (d 1)) (S y0) (S z) ∧
      ¬ InClosedTri (S y0) (S (d 1)) (S (d 2)) (S z))
    (hy1_loc : ∀ z ∈ M.erase y1,
      ¬ InClosedTri (S (d 2)) (S (d 1)) (S y1) (S z) ∧
      ¬ InClosedTri (S y1) (S (d 1)) (S (d 0)) (S z)) :
    (∀ y ∈ M, ¬ InClosedTri (S (d 0)) (S (d 1)) (S (d 2)) (S y) ∧
              0 < orient2D (S (d 0)) (S (d 2)) (S y)) ∧
    0 < orient2D (S (d 0)) (S (d 2)) (w D) ∧
    (∀ y ∈ M, InIntTri (w D) (S (d 0)) (S (d 2)) (S y)) ∧
    (∀ x ∈ WitnessSet {d 0, d 2} ∅ w,
      (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos x ∧
      ∀ y ∈ M, x ∈ Sec11Bridge.UCone (S y) (S (d 0)) (S (d 2))) ∧
    (∀ y ∈ M, ∃ W_y : OpenWedge, W_y.y = S y ∧
      (∀ z : ℝ × ℝ, W_y.MemOpen z →
        z ∈ Sec11Bridge.UCone (S y) (S (d 0)) (S (d 2)) ∧
        (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 2} ∅ w) (S y) W_y) :=
  Sec11Bridge.adjacent_ear_empty_and_chord_wedges hP hd_inj hv D M hD_eq hM_disj
    y0 y1 hy0M hy1M hy01 hM_01 hM_12 hwD_01 hwD_12 hM_exit hy0_loc hy1_loc

private lemma exists_memNeg_in_R11111_local
    (W : Fin 5 → OpenWedge) (H : OpenHalfPlane)
    (z : ℝ × ℝ) (hz_open : ∀ i : Fin 5, (W i).MemOpen z) (hz_not : ¬ H.MemPos z) :
    ∃ z' : ℝ × ℝ, H.MemNeg z' ∧ ∀ i : Fin 5, (W i).MemOpen z' := by
  have hz_le : H.n.1 * z.1 + H.n.2 * z.2 + H.c ≤ 0 := not_lt.mp hz_not
  have hcont : ∀ i : Fin 5, Continuous (fun p : ℝ × ℝ =>
      min ((W i).u₁.1 * (p.1 - (W i).y.1) + (W i).u₁.2 * (p.2 - (W i).y.2))
          ((W i).u₂.1 * (p.1 - (W i).y.1) + (W i).u₂.2 * (p.2 - (W i).y.2))) := by
    intro i; continuity
  have hopen : IsOpen {p : ℝ × ℝ | ∀ i : Fin 5, (W i).MemOpen p} := by
    have : {p : ℝ × ℝ | ∀ i : Fin 5, (W i).MemOpen p} =
        ⋂ i : Fin 5, {p : ℝ × ℝ | 0 < min ((W i).u₁.1 * (p.1 - (W i).y.1) + (W i).u₁.2 * (p.2 - (W i).y.2))
                                          ((W i).u₂.1 * (p.1 - (W i).y.1) + (W i).u₂.2 * (p.2 - (W i).y.2))} := by
      ext p; simp [OpenWedge.MemOpen]
    rw [this]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hcont i))
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen z hz_open
  let denom : ℝ := |H.n.1| + |H.n.2| + 1
  have hdenom_pos : 0 < denom := by
    have h1 : 0 ≤ |H.n.1| := abs_nonneg _
    have h2 : 0 ≤ |H.n.2| := abs_nonneg _
    dsimp [denom]; linarith
  let δ : ℝ := ε / (2 * denom)
  have hδ_pos : 0 < δ := div_pos hε (by linarith)
  let z' : ℝ × ℝ := (z.1 - δ * H.n.1, z.2 - δ * H.n.2)
  have hz'_mem : z' ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Prod.dist_eq]; simp only [Real.dist_eq, z']
    have h1 : |(z.1 - δ * H.n.1) - z.1| < ε := by
      have heq : (z.1 - δ * H.n.1) - z.1 = -(δ * H.n.1) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hδ_pos]
      have hle : |H.n.1| ≤ denom := by have := abs_nonneg H.n.2; dsimp [denom]; linarith
      calc δ * |H.n.1| ≤ δ * denom := mul_le_mul_of_nonneg_left hle (le_of_lt hδ_pos)
        _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hdenom_pos]
        _ < ε := by linarith
    have h2 : |(z.2 - δ * H.n.2) - z.2| < ε := by
      have heq : (z.2 - δ * H.n.2) - z.2 = -(δ * H.n.2) := by ring
      rw [heq, abs_neg, abs_mul, abs_of_pos hδ_pos]
      have hle : |H.n.2| ≤ denom := by have := abs_nonneg H.n.1; dsimp [denom]; linarith
      calc δ * |H.n.2| ≤ δ * denom := mul_le_mul_of_nonneg_left hle (le_of_lt hδ_pos)
        _ = ε / 2 := by dsimp [δ]; field_simp [ne_of_gt hdenom_pos]
        _ < ε := by linarith
    exact max_lt h1 h2
  refine ⟨z', ?_, hball hz'_mem⟩
  dsimp [OpenHalfPlane.MemNeg, z']
  have hs : 0 < H.n.1 ^ 2 + H.n.2 ^ 2 := by
    rcases H.hn with h1 | h2
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
  have heq : H.n.1 * (z.1 - δ * H.n.1) + H.n.2 * (z.2 - δ * H.n.2) + H.c =
      (H.n.1 * z.1 + H.n.2 * z.2 + H.c) - δ * (H.n.1 ^ 2 + H.n.2 ^ 2) := by ring
  rw [heq]; nlinarith

private theorem pentagon_wedges_no_ten_shattered_planar_regime2_local
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    (v : Fin 5 → ℝ × ℝ) (hv : StrictConvexCCWPentagon v)
    (W : Fin 5 → OpenWedge)
    (xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ)
    (hxk_mask : ∀ k m, RealizesWedgeMask W m (xk k m))
    (h_nonfront3 : ∀ m, (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 m) ∨
                        (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 m))
    (h_nonfront4 : ∀ m, (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 m) ∨
                        (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 m))
    (h_xor3 : (pentagonEdgeHalfPlane v hv 2).MemPos (xk 3 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 3).MemPos (xk 3 (fun _ => true)))
    (h_xor4 : (pentagonEdgeHalfPlane v hv 3).MemPos (xk 4 (fun _ => true)) ↔
              ¬ (pentagonEdgeHalfPlane v hv 4).MemPos (xk 4 (fun _ => true)))
    (h_regime2 :
      (∀ k m, (pentagonDiag02HalfPlane v hv).MemPos (xk k m)) ∧
      (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → (pentagonDiag02HalfPlane v hv).MemPos z) ∧
      ((pentagonEdgeHalfPlane v hv 0).MemPos (xk 1 (fun _ => true)) ↔
        ¬ (pentagonEdgeHalfPlane v hv 1).MemPos (xk 1 (fun _ => true))))
    (h_case :
      (∃ rstar : Fin 5, rstar ≠ 0 ∧ rstar ≠ 1 ∧
        (∀ k m, ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos (xk k m)) ∧
        (∀ z, (∀ i : Fin 5, (W i).MemOpen z) → ¬ (pentagonEdgeHalfPlane v hv rstar).MemPos z)) ∨
      (∀ i r : Fin 5, (pentagonEdgeHalfPlane v hv r).MemPos (W i).y)) :
    False := by
  let H := pentagonEdgeHalfPlane v hv
  let R11111 : ℝ × ℝ → Prop := fun z => ∀ i : Fin 5, (W i).MemOpen z
  have hxk_R11111 : ∀ k, R11111 (xk k (fun _ => true)) := fun k i => by
    simpa using hxk_mask k (fun _ => true) i
  have h_inc := fun z => pentagon_halfplane_inclusions_planar v hv z
  have thm_v_sep : ∀ (r : Fin 5) (fam : (Fin 5 → Bool) → ℝ × ℝ),
      (∀ m, RealizesWedgeMask W m (fam m)) →
      (∀ m, (H r).MemPos (fam m)) → ∀ z, R11111 z → (H r).MemPos z := fun r fam hfam_mask hfam z hz =>
    thm1_part2_general_halfplane h_thm1 W (H r) (fun m => ⟨fam m, hfam m, hfam_mask m⟩) z hz
  rcases h_regime2 with ⟨h02_xk, h02_R, h_xor1⟩
  rcases h_case with ⟨rstar, hr0, hr1, hr_xk, hr_R⟩ | h_apices
  · fin_cases rstar
    · exact hr0 rfl
    · exact hr1 rfl
    · have hx3_in_H3 : ∀ m, (H 3).MemPos (xk 3 m) := fun m => (h_nonfront3 m).resolve_left (hr_xk 3 m)
      have hR_H3 := thm_v_sep 3 (xk 3) (hxk_mask 3) hx3_in_H3
      have h4_3 := hR_H3 (xk 4 (fun _ => true)) (hxk_R11111 4)
      have hn4 := h_xor4.mp h4_3
      exact (h_inc (xk 4 (fun _ => true))).2.2.2.2.2.2
        (h02_R _ (hxk_R11111 4)) (hr_R _ (hxk_R11111 4)) hn4 |>.2 h4_3
    · have hx3_in_H2 : ∀ m, (H 2).MemPos (xk 3 m) := fun m => (h_nonfront3 m).resolve_right (hr_xk 3 m)
      have hx4_in_H4 : ∀ m, (H 4).MemPos (xk 4 m) := fun m => (h_nonfront4 m).resolve_left (hr_xk 4 m)
      have hR_H2 := thm_v_sep 2 (xk 3) (hxk_mask 3) hx3_in_H2
      have hR_H4 := thm_v_sep 4 (xk 4) (hxk_mask 4) hx4_in_H4
      have hn3_1 := hr_R (xk 1 (fun _ => true)) (hxk_R11111 1)
      have h1_in_H1 : (H 1).MemPos (xk 1 (fun _ => true)) := by
        by_contra hn1
        exact ((h_inc _).2.2.2.2.1 (h02_R _ (hxk_R11111 1)) hn1 hn3_1).1 (hR_H2 _ (hxk_R11111 1))
      have h1_in_H0 : (H 0).MemPos (xk 1 (fun _ => true)) := by
        by_contra hn0
        exact ((h_inc _).2.2.2.2.2.1 (h02_R _ (hxk_R11111 1)) hn0 hn3_1).2 (hR_H4 _ (hxk_R11111 1))
      exact (h_xor1.mp h1_in_H0) h1_in_H1
    · have hx4_in_H3 : ∀ m, (H 3).MemPos (xk 4 m) := fun m => (h_nonfront4 m).resolve_right (hr_xk 4 m)
      have hR_H3 := thm_v_sep 3 (xk 4) (hxk_mask 4) hx4_in_H3
      have h3_3 := hR_H3 (xk 3 (fun _ => true)) (hxk_R11111 3)
      have hn2 : ¬ (H 2).MemPos (xk 3 (fun _ => true)) := fun h2 => (h_xor3.mp h2) h3_3
      exact ((h_inc _).2.2.2.2.2.2 (h02_R _ (hxk_R11111 3)) hn2 (hr_R _ (hxk_R11111 3))).2 h3_3
  · have thm_L_obs : ∀ (a b : Fin 5) (fam : (Fin 5 → Bool) → ℝ × ℝ),
        (∀ m, RealizesWedgeMask W m (fam m)) →
        (∀ m, (H a).MemPos (fam m) ∨ (H b).MemPos (fam m)) →
        ∀ za zb, R11111 za → R11111 zb → ¬ (H a).MemPos za → ¬ (H b).MemPos zb → False := by
      intro a b fam hfam_mask hfam za zb hza hzb hna hnb
      obtain ⟨za', hza'_neg, hza'_open⟩ := exists_memNeg_in_R11111_local W (H a) za hza hna
      obtain ⟨zb', hzb'_neg, hzb'_open⟩ := exists_memNeg_in_R11111_local W (H b) zb hzb hnb
      exact five_wedges_two_halfplanes_general h_thm1 h_caseA_orig (H a) (H b) W
        (fun i => ⟨h_apices i a, h_apices i b⟩)
        ⟨za', hza'_neg, hza'_open⟩ ⟨zb', hzb'_neg, hzb'_open⟩
        (fun m => ⟨fam m, hfam m, hfam_mask m⟩)
    have hx3_24 : ∀ m, (H 2).MemPos (xk 3 m) ∨ (H 4).MemPos (xk 3 m) := by
      intro m
      by_cases h2 : (H 2).MemPos (xk 3 m)
      · exact Or.inl h2
      · right; by_contra h4
        exact h2 ((h_nonfront3 m).resolve_right ((h_inc _).2.2.2.2.2.2 (h02_xk 3 m) h2 h4).2)
    by_cases h3_2 : (H 2).MemPos (xk 3 (fun _ => true))
    · have hn3 := h_xor3.mp h3_2
      have hx3_13 : ∀ m, (H 1).MemPos (xk 3 m) ∨ (H 3).MemPos (xk 3 m) := by
        intro m
        by_cases h1 : (H 1).MemPos (xk 3 m)
        · exact Or.inl h1
        · right; by_contra h3
          have := (h_inc (xk 3 m)).2.2.2.2.1 (h02_xk 3 m) h1 h3
          rcases h_nonfront3 m with h2 | h3'
          · exact this.1 h2
          · exact h3 h3'
      have hx4_03 : ∀ m, (H 0).MemPos (xk 4 m) ∨ (H 3).MemPos (xk 4 m) := by
        intro m
        by_cases h0 : (H 0).MemPos (xk 4 m)
        · exact Or.inl h0
        · right; by_contra h3
          have := (h_inc (xk 4 m)).2.2.2.2.2.1 (h02_xk 4 m) h0 h3
          rcases h_nonfront4 m with h3' | h4
          · exact h3 h3'
          · exact this.2 h4
      by_cases h1_0 : (H 0).MemPos (xk 1 (fun _ => true))
      · exact thm_L_obs 1 3 (xk 3) (hxk_mask 3) hx3_13
          (xk 1 (fun _ => true)) (xk 3 (fun _ => true)) (hxk_R11111 1) (hxk_R11111 3) (h_xor1.mp h1_0) hn3
      · exact thm_L_obs 0 3 (xk 4) (hxk_mask 4) hx4_03
          (xk 1 (fun _ => true)) (xk 3 (fun _ => true)) (hxk_R11111 1) (hxk_R11111 3) h1_0 hn3
    · have hn4_3 : ¬ (H 3).MemPos (xk 4 (fun _ => true)) → False := fun hn3_4 =>
        thm_L_obs 2 3 (xk 3) (hxk_mask 3) h_nonfront3
          (xk 3 (fun _ => true)) (xk 4 (fun _ => true)) (hxk_R11111 3) (hxk_R11111 4) h3_2 hn3_4
      have h4_3 : (H 3).MemPos (xk 4 (fun _ => true)) := by by_contra h; exact hn4_3 h
      exact thm_L_obs 2 4 (xk 3) (hxk_mask 3) hx3_24
        (xk 3 (fun _ => true)) (xk 4 (fun _ => true)) (hxk_R11111 3) (hxk_R11111 4) h3_2 (h_xor4.mp h4_3)

private lemma strictConvexCCWPentagon_shift1_local {v : Fin 5 → ℝ × ℝ} (hv : StrictConvexCCWPentagon v) :
    StrictConvexCCWPentagon (fun i => v (i + 1)) := by
  intro i j k hij hjk
  by_cases hk4 : k = 4
  · subst hk4
    have h0i : (0 : Fin 5) < i + 1 := by omega
    have hij' : i + 1 < j + 1 := by omega
    change 0 < orient2D (v (i + 1)) (v (j + 1)) (v 0)
    rw [orient2D_cycle]
    exact hv 0 (i + 1) (j + 1) h0i hij'
  · exact hv (i + 1) (j + 1) (k + 1) (by omega) (by omega)

private lemma finset_M_enum_local {M : Finset (Fin 10)} (hM_card : M.card = 5) :
    ∃ m_enum : Fin 5 → Fin 10, Function.Injective m_enum ∧ Finset.univ.image m_enum = M := by
  let e := M.equivFin
  refine ⟨fun i => (e.symm (i.cast hM_card.symm)).1, ?_, ?_⟩
  · intro i j hij
    have h2 : i.cast hM_card.symm = j.cast hM_card.symm := e.symm.injective (Subtype.ext hij)
    exact Fin.ext (by simpa using congrArg Fin.val h2)
  · ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]; constructor
    · rintro ⟨i, rfl⟩; exact (e.symm _).2
    · intro hx; refine ⟨(e ⟨x, hx⟩).cast hM_card, ?_⟩; simp

private lemma hullVertices_nonneg_edge_local {n : ℕ} {P : Set (ℝ × ℝ)} {S : Fin n → ℝ × ℝ}
    {w : Finset (Fin n) → ℝ × ℝ} (hP : ShatteredSimplePolygon P S w)
    {d : Fin 5 → Fin n} (hd_inj : Function.Injective d)
    (hv : StrictConvexCCWPentagon (S ∘ d))
    {D H : Finset (Fin n)} (hDB : D = hullVertices S \ H) (hD_eq : D = Finset.univ.image d)
    (i : Fin 5) (hH_edge : ∀ h ∈ H, 0 < orient2D (S (d i)) (S (d (i + 1))) (S h)) :
    ∀ x ∈ Finset.univ \ D, 0 < orient2D (S (d i)) (S (d (i + 1))) (S x) := by
  have hB_nn : ∀ b ∈ hullVertices S, 0 ≤ orient2D (S (d i)) (S (d (i + 1))) (S b) := by
    intro b hb
    by_cases hbH : b ∈ H
    · exact le_of_lt (hH_edge b hbH)
    · have hbD : b ∈ D := hDB ▸ Finset.mem_sdiff.mpr ⟨hb, hbH⟩
      rw [hD_eq] at hbD
      rcases Finset.mem_image.mp hbD with ⟨j, _, rfl⟩
      by_cases hji : j = i
      · subst hji; rw [orient2D_self_outer]
      · by_cases hji1 : j = i + 1
        · subst hji1; rw [orient2D_self_right]
        · exact le_of_lt (hv.toPoly i j hji hji1)
  have hpos := Sec11Bridge.orient2D_pos_of_hullVertices hP (hd_inj.ne ((by decide : ∀ x : Fin 5, x ≠ x + 1) i)) hB_nn
  intro x hx
  have hxD : x ∉ D := (Finset.mem_sdiff.mp hx).2
  have hxi : x ≠ d i := fun h => hxD (h ▸ hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ i))
  have hxi1 : x ≠ d (i + 1) := fun h => hxD (h ▸ hD_eq ▸ Finset.mem_image_of_mem d (Finset.mem_univ (i + 1)))
  exact hpos x hxi hxi1

private lemma localized_pentagon_regime1_local
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (d : Fin 5 → Fin 10) (hd_inj : Function.Injective d) (hv : StrictConvexCCWPentagon (S ∘ d))
    (hDB : Finset.univ.image d = hullVertices S \ certifiedVertices S w)
    (h_exit01 : ∀ y ∈ Finset.univ \ Finset.univ.image d,
      0 < orient2D (S (d 0)) (S (d 1)) (w (Finset.univ.image d)) ∧
      InIntTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y))
    (h_H_arc : (certifiedVertices S w).Nonempty →
      ∃ rstar : Fin 5, rstar ≠ 0 ∧
        (∀ h ∈ certifiedVertices S w, orient2D (S (d rstar)) (S (d (rstar + 1))) (S h) < 0) ∧
        (∀ i : Fin 5, i ≠ rstar → ∀ h ∈ certifiedVertices S w,
          0 < orient2D (S (d i)) (S (d (i + 1))) (S h))) :
    False := by
  let D : Finset (Fin 10) := Finset.univ.image d
  let M : Finset (Fin 10) := Finset.univ \ D
  let B := hullVertices S
  let H := certifiedVertices S w
  have hD_B : D ⊆ B := by dsimp [D, B]; rw [hDB]; exact Finset.sdiff_subset
  have hD_card : D.card = 5 := by rw [Finset.card_image_of_injective Finset.univ hd_inj, Finset.card_fin]
  have hM_card : M.card = 5 := by dsimp [M]; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hD_card]
  have hM_ne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hM_disj : Disjoint D M := Finset.disjoint_left.mpr fun _ hx hm => (Finset.mem_sdiff.mp hm).2 hx
  have hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y) := by
    by_cases hHne : H.Nonempty
    · obtain ⟨rstar, hr0, _, hH_pos⟩ := h_H_arc hHne
      exact hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl 0 (hH_pos 0 hr0.symm)
    · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      exact hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl 0 (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
  obtain ⟨hW_sub, hM_wedges⟩ := Sec11Bridge.exit01_chord_wedges hP hd_inj hv D M rfl hM_disj hM_ne hM_01
    (fun y hy => (h_exit01 y hy).2)
  obtain ⟨m_enum, hm_inj, hm_img⟩ := finset_M_enum_local hM_card
  have hm_mem : ∀ i : Fin 5, m_enum i ∈ M := fun i => hm_img ▸ Finset.mem_image_of_mem m_enum (Finset.mem_univ i)
  have h_wedges_ex : ∀ i : Fin 5, ∃ W_i : OpenWedge, W_i.y = S (m_enum i) ∧
      (∀ z : ℝ × ℝ, W_i.MemOpen z →
        z ∈ Sec11Bridge.UCone (S (m_enum i)) (S (d 0)) (S (d 1)) ∧
        (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 1} ∅ w) (S (m_enum i)) W_i :=
    fun i => hM_wedges (m_enum i) (hm_mem i)
  choose W hWy hW_U hW_test using h_wedges_ex
  let M_mask : (Fin 5 → Bool) → Finset (Fin 10) := fun mask =>
    (Finset.univ.filter (fun i : Fin 5 => mask i = true)).image m_enum
  have h_d_not_M : ∀ (k : Fin 5) (mask : Fin 5 → Bool), d k ∉ M_mask mask := by
    intro k mask hmem
    rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
    exact Finset.disjoint_left.mp hM_disj (Finset.mem_image_of_mem d (Finset.mem_univ k)) (hi ▸ hm_mem i)
  let xk_T : Fin 5 → (Fin 5 → Bool) → Finset (Fin 10) := fun k mask =>
    if k = 2 ∨ k = 3 ∨ k = 4 then (D.erase (d k)) ∪ M_mask mask else (D.erase (d 3)) ∪ M_mask mask
  let xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ := fun k mask => w (xk_T k mask)
  have hxk_in_W01 : ∀ k mask, xk k mask ∈ WitnessSet {d 0, d 1} ∅ w := by
    intro k mask; refine ⟨xk_T k mask, ?_, Finset.disjoint_empty_right _, rfl⟩
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; dsimp [xk_T]; split_ifs with hk
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · rcases hx with rfl | rfl <;> rcases hk with rfl | rfl | rfl <;> exact hd_inj.ne (by decide)
      · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · rcases hx with rfl | rfl <;> exact hd_inj.ne (by decide)
      · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
  have h_realizes : ∀ T : Finset (Fin 10), ∀ mask : Fin 5 → Bool,
      w T ∈ WitnessSet {d 0, d 1} ∅ w →
      (∀ i : Fin 5, m_enum i ∈ T ↔ mask i = true) →
      RealizesWedgeMask W mask (w T) := by
    intro T mask hwT him i
    have htest := hW_test i (w T) hwT
    have hsees := (hP.shatters T (m_enum i)).trans (him i)
    cases hmi : mask i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases htest.1 with ho | he
      · exfalso; have := hsees.mp (htest.2.mpr ho); simp [hmi] at this
      · exact he
    · simp only [↓reduceIte]; exact htest.2.mp (hsees.mpr hmi)
  have hxk_mask : ∀ k mask, RealizesWedgeMask W mask (xk k mask) := by
    intro k mask; refine h_realizes (xk_T k mask) mask (hxk_in_W01 k mask) (fun i => ?_)
    dsimp [xk_T, M_mask]; split_ifs <;>
    · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, hiD⟩ | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
  let pm : (Fin 5 → Bool) → ℝ × ℝ := fun mask => w (D ∪ M_mask mask)
  have hpm_mask : ∀ mask, RealizesWedgeMask W mask (pm mask) := by
    intro mask
    refine h_realizes (D ∪ M_mask mask) mask ⟨D ∪ M_mask mask, ?_, Finset.disjoint_empty_right _, rfl⟩ (fun i => ?_)
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_union_left _ (Finset.mem_image_of_mem d (Finset.mem_univ _))
    · dsimp [M_mask]; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hiD | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
  have hR_in_conv : ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) → z ∈ convexHull ℝ (WitnessSet D ∅ w) := by
    intro z hz
    have hcz := thm1_part2_convexHull_containment h_thm1 W pm hpm_mask z hz
    refine convexHull_mono ?_ hcz
    rintro _ ⟨mask, rfl⟩; exact ⟨D ∪ M_mask mask, Finset.subset_union_left, Finset.disjoint_empty_right _, rfl⟩
  have hk_nonfront : ∀ (k : Fin 5) (hk : k = 2 ∨ k = 3 ∨ k = 4) (mask : Fin 5 → Bool),
      (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k mask) ∨
      (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k mask) := fun k hk mask =>
    Sec11Bridge.pentagon_cells_nonfront hP hd_inj hv hD_B k
      (fun h => Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
        (Finset.mem_image_of_mem d (Finset.mem_univ k)) h)
      (by dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left)
      (by dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k mask])
  have hk_xor : ∀ (k : Fin 5) (hk : k = 2 ∨ k = 3 ∨ k = 4),
      (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k (fun _ => true)) ↔
      ¬ (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k (fun _ => true)) := fun k hk =>
    Sec11Bridge.pentagon_cells_xor_of_convexHull hP hd_inj hv hD_B k
      (fun h => Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
        (Finset.mem_image_of_mem d (Finset.mem_univ k)) h)
      (by dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left)
      (by dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k _])
      (hR_in_conv _ (fun i => by simpa using hxk_mask k (fun _ => true) i))
  refine pentagon_wedges_no_ten_shattered_planar h_thm1 h_caseA_orig false (S ∘ d) hv W xk hxk_mask
    (hk_nonfront 3 (Or.inr (Or.inl rfl))) (hk_nonfront 4 (Or.inr (Or.inr rfl))) (hk_nonfront 2 (Or.inl rfl))
    (hk_xor 3 (Or.inr (Or.inl rfl))) (hk_xor 4 (Or.inr (Or.inr rfl)))
    (by rw [if_pos rfl]; exact ⟨fun k mask => (hW_sub _ (hxk_in_W01 k mask)).1,
          fun z hz => (hW_U 0 z (hz 0)).2, hk_xor 2 (Or.inl rfl)⟩) ?_
  by_cases hHne : H.Nonempty
  · obtain ⟨rstar, hr0, hr_out, _⟩ := h_H_arc hHne
    obtain ⟨h_in_H, hhH⟩ := hHne
    have hhM : h_in_H ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hhD => by
      dsimp [D] at hhD; rw [hDB] at hhD; exact (Finset.mem_sdiff.mp hhD).2 hhH⟩
    have hh_01 : 0 < orient2D (S (d 0)) (S (d 1)) (S h_in_H) := hM_01 h_in_H hhM
    left
    refine ⟨rstar, hr0, fun h => False.elim (by cases h), ?_, ?_⟩
    · intro k mask
      have hneg := (Sec11Bridge.pentagon_cells_certified_cone_H0 hv rstar hr0 (hr_out h_in_H hhH) hh_01 _
        ((hW_sub _ (hxk_in_W01 k mask)).2 h_in_H hhM)).2
      dsimp [pentagonEdgeHalfPlane] at hneg ⊢; rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
    · intro z hz
      obtain ⟨i_h, _, hi_eq⟩ := Finset.mem_image.mp (hm_img.symm ▸ hhM)
      have hzU : z ∈ Sec11Bridge.UCone (S h_in_H) (S (d 0)) (S (d 1)) := by rw [← hi_eq]; exact (hW_U i_h z (hz i_h)).1
      have hneg := (Sec11Bridge.pentagon_cells_certified_cone_H0 hv rstar hr0 (hr_out h_in_H hhH) hh_01 _ hzU).2
      dsimp [pentagonEdgeHalfPlane] at hneg ⊢; rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
  · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
    right
    intro i r; rw [hWy i]
    have hall_r := hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl r
      (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
    dsimp [pentagonEdgeHalfPlane]; rw [edgeHalfPlane_memPos_iff]; exact hall_r (m_enum i) (hm_mem i)

private lemma localized_pentagon_regime2_local
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    (d : Fin 5 → Fin 10) (hd_inj : Function.Injective d) (hv : StrictConvexCCWPentagon (S ∘ d))
    (hDB : Finset.univ.image d = hullVertices S \ certifiedVertices S w)
    (hM_exit : ∀ y ∈ Finset.univ \ Finset.univ.image d,
      InIntTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y) ∨
      InIntTri (w (Finset.univ.image d)) (S (d 1)) (S (d 2)) (S y))
    (h_H_arc2 : (certifiedVertices S w).Nonempty → ∃ rstar : Fin 5, rstar ≠ 0 ∧ rstar ≠ 1 ∧
      (∀ h ∈ certifiedVertices S w, orient2D (S (d rstar)) (S (d (rstar + 1))) (S h) < 0) ∧
      (∀ i : Fin 5, i ≠ rstar → ∀ h ∈ certifiedVertices S w,
        0 < orient2D (S (d i)) (S (d (i + 1))) (S h)))
    {y0 y1 : Fin 10}
    (hy0M : y0 ∈ Finset.univ \ Finset.univ.image d) (hy1M : y1 ∈ Finset.univ \ Finset.univ.image d) (hy01 : y0 ≠ y1)
    (hy0_ex : InIntTri (w (Finset.univ.image d)) (S (d 0)) (S (d 1)) (S y0))
    (hy1_ex : InIntTri (w (Finset.univ.image d)) (S (d 1)) (S (d 2)) (S y1))
    (hy0_loc : ∀ z ∈ (Finset.univ \ Finset.univ.image d).erase y0,
      ¬ InClosedTri (S (d 0)) (S (d 1)) (S y0) (S z) ∧ ¬ InClosedTri (S y0) (S (d 1)) (S (d 2)) (S z))
    (hy1_loc : ∀ z ∈ (Finset.univ \ Finset.univ.image d).erase y1,
      ¬ InClosedTri (S (d 2)) (S (d 1)) (S y1) (S z) ∧ ¬ InClosedTri (S y1) (S (d 1)) (S (d 0)) (S z)) :
    False := by
  let D : Finset (Fin 10) := Finset.univ.image d
  let M : Finset (Fin 10) := Finset.univ \ D
  let B := hullVertices S
  let H := certifiedVertices S w
  have hD_B : D ⊆ B := by dsimp [D, B]; rw [hDB]; exact Finset.sdiff_subset
  have hD_card : D.card = 5 := by rw [Finset.card_image_of_injective Finset.univ hd_inj, Finset.card_fin]
  have hM_card : M.card = 5 := by dsimp [M]; rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hD_card]
  have hM_disj : Disjoint D M := Finset.disjoint_left.mpr fun _ hx hm => (Finset.mem_sdiff.mp hm).2 hx
  have hM_01 : ∀ y ∈ M, 0 < orient2D (S (d 0)) (S (d 1)) (S y) := by
    by_cases hHne : H.Nonempty
    · obtain ⟨rstar, hr0, _, _, hH_pos⟩ := h_H_arc2 hHne
      exact hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl 0 (hH_pos 0 hr0.symm)
    · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      exact hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl 0 (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
  have hM_12 : ∀ y ∈ M, 0 < orient2D (S (d 1)) (S (d 2)) (S y) := by
    by_cases hHne : H.Nonempty
    · obtain ⟨rstar, _, hr1, _, hH_pos⟩ := h_H_arc2 hHne
      exact hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl 1 (hH_pos 1 hr1.symm)
    · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
      exact hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl 1 (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
  have hwD_01 : 0 < orient2D (S (d 0)) (S (d 1)) (w D) := by
    rcases hy0_ex with ⟨μ₁, _, _, hμ1, _, _, hs, hx1, hx2⟩
    have hid : orient2D (S (d 0)) (S (d 1)) (S y0) = μ₁ * orient2D (S (d 0)) (S (d 1)) (w D) := by
      unfold orient2D; rw [hx1, hx2]; linear_combination ((S (d 0)).2 * (S (d 1)).1 - (S (d 0)).1 * (S (d 1)).2) * hs
    have hpos := hM_01 y0 hy0M; nlinarith
  have hwD_12 : 0 < orient2D (S (d 1)) (S (d 2)) (w D) := by
    rcases hy1_ex with ⟨μ₁, _, _, hμ1, _, _, hs, hx1, hx2⟩
    have hid : orient2D (S (d 1)) (S (d 2)) (S y1) = μ₁ * orient2D (S (d 1)) (S (d 2)) (w D) := by
      unfold orient2D; rw [hx1, hx2]; linear_combination ((S (d 1)).2 * (S (d 2)).1 - (S (d 1)).1 * (S (d 2)).2) * hs
    have hpos := hM_12 y1 hy1M; nlinarith
  obtain ⟨hM_02_pos, _, _, hW_sub, hM_wedges⟩ :=
    adjacent_ear_empty_and_chord_wedges hP hd_inj hv D M rfl hM_disj
      y0 y1 hy0M hy1M hy01 hM_01 hM_12 hwD_01 hwD_12 hM_exit hy0_loc hy1_loc
  obtain ⟨m_enum, hm_inj, hm_img⟩ := finset_M_enum_local hM_card
  have hm_mem : ∀ i : Fin 5, m_enum i ∈ M := fun i => hm_img ▸ Finset.mem_image_of_mem m_enum (Finset.mem_univ i)
  have h_wedges_ex : ∀ i : Fin 5, ∃ W_i : OpenWedge, W_i.y = S (m_enum i) ∧
      (∀ z : ℝ × ℝ, W_i.MemOpen z →
        z ∈ Sec11Bridge.UCone (S (m_enum i)) (S (d 0)) (S (d 2)) ∧
        (pentagonDiag02HalfPlane (S ∘ d) hv).MemPos z) ∧
      IsWedgeTest P (WitnessSet {d 0, d 2} ∅ w) (S (m_enum i)) W_i :=
    fun i => hM_wedges (m_enum i) (hm_mem i)
  choose W hWy hW_U hW_test using h_wedges_ex
  let M_mask : (Fin 5 → Bool) → Finset (Fin 10) := fun mask =>
    (Finset.univ.filter (fun i : Fin 5 => mask i = true)).image m_enum
  have h_d_not_M : ∀ (k : Fin 5) (mask : Fin 5 → Bool), d k ∉ M_mask mask := by
    intro k mask hmem; rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
    exact Finset.disjoint_left.mp hM_disj (Finset.mem_image_of_mem d (Finset.mem_univ k)) (hi ▸ hm_mem i)
  let xk_T : Fin 5 → (Fin 5 → Bool) → Finset (Fin 10) := fun k mask =>
    if k = 1 ∨ k = 3 ∨ k = 4 then (D.erase (d k)) ∪ M_mask mask else (D.erase (d 3)) ∪ M_mask mask
  let xk : Fin 5 → (Fin 5 → Bool) → ℝ × ℝ := fun k mask => w (xk_T k mask)
  have hxk_in_W02 : ∀ k mask, xk k mask ∈ WitnessSet {d 0, d 2} ∅ w := by
    intro k mask; refine ⟨xk_T k mask, ?_, Finset.disjoint_empty_right _, rfl⟩
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; dsimp [xk_T]; split_ifs with hk
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · rcases hx with rfl | rfl <;> rcases hk with rfl | rfl | rfl <;> exact hd_inj.ne (by decide)
      · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
    · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · rcases hx with rfl | rfl <;> exact hd_inj.ne (by decide)
      · rcases hx with rfl | rfl <;> exact Finset.mem_image_of_mem d (Finset.mem_univ _)
  have h_realizes : ∀ T : Finset (Fin 10), ∀ mask : Fin 5 → Bool,
      w T ∈ WitnessSet {d 0, d 2} ∅ w →
      (∀ i : Fin 5, m_enum i ∈ T ↔ mask i = true) →
      RealizesWedgeMask W mask (w T) := by
    intro T mask hwT him i
    have htest := hW_test i (w T) hwT
    have hsees := (hP.shatters T (m_enum i)).trans (him i)
    cases hmi : mask i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases htest.1 with ho | he
      · exfalso; have := hsees.mp (htest.2.mpr ho); simp [hmi] at this
      · exact he
    · simp only [↓reduceIte]; exact htest.2.mp (hsees.mpr hmi)
  have hxk_mask : ∀ k mask, RealizesWedgeMask W mask (xk k mask) := by
    intro k mask; refine h_realizes (xk_T k mask) mask (hxk_in_W02 k mask) (fun i => ?_)
    dsimp [xk_T, M_mask]; split_ifs <;>
    · simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, hiD⟩ | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
  let pm : (Fin 5 → Bool) → ℝ × ℝ := fun mask => w (D ∪ M_mask mask)
  have hpm_mask : ∀ mask, RealizesWedgeMask W mask (pm mask) := by
    intro mask
    refine h_realizes (D ∪ M_mask mask) mask ⟨D ∪ M_mask mask, ?_, Finset.disjoint_empty_right _, rfl⟩ (fun i => ?_)
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_union_left _ (Finset.mem_image_of_mem d (Finset.mem_univ _))
    · dsimp [M_mask]; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hiD | ⟨j, hj, hji⟩)
        · exact False.elim (Finset.disjoint_left.mp hM_disj hiD (hm_mem i))
        · rwa [← hm_inj hji]
      · intro hmi; right; exact ⟨i, hmi, rfl⟩
  have hR_in_conv : ∀ z : ℝ × ℝ, (∀ i : Fin 5, (W i).MemOpen z) → z ∈ convexHull ℝ (WitnessSet D ∅ w) := by
    intro z hz
    have hcz := thm1_part2_convexHull_containment h_thm1 W pm hpm_mask z hz
    refine convexHull_mono ?_ hcz
    rintro _ ⟨mask, rfl⟩; exact ⟨D ∪ M_mask mask, Finset.subset_union_left, Finset.disjoint_empty_right _, rfl⟩
  have hk_nonfront : ∀ (k : Fin 5) (hk : k = 1 ∨ k = 3 ∨ k = 4) (mask : Fin 5 → Bool),
      (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k mask) ∨
      (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k mask) := fun k hk mask =>
    Sec11Bridge.pentagon_cells_nonfront hP hd_inj hv hD_B k
      (fun h => Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
        (Finset.mem_image_of_mem d (Finset.mem_univ k)) h)
      (by dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left)
      (by dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k mask])
  have hk_xor : ∀ (k : Fin 5) (hk : k = 1 ∨ k = 3 ∨ k = 4),
      (pentagonEdgeHalfPlane (S ∘ d) hv (k - 1)).MemPos (xk k (fun _ => true)) ↔
      ¬ (pentagonEdgeHalfPlane (S ∘ d) hv k).MemPos (xk k (fun _ => true)) := fun k hk =>
    Sec11Bridge.pentagon_cells_xor_of_convexHull hP hd_inj hv hD_B k
      (fun h => Finset.disjoint_left.mp (by rw [hDB]; exact Finset.sdiff_disjoint)
        (Finset.mem_image_of_mem d (Finset.mem_univ k)) h)
      (by dsimp [xk_T]; rw [if_pos hk]; exact Finset.subset_union_left)
      (by dsimp [xk_T]; rw [if_pos hk]; simp [h_d_not_M k _])
      (hR_in_conv _ (fun i => by simpa using hxk_mask k (fun _ => true) i))
  have h_xor1 : (pentagonEdgeHalfPlane (S ∘ d) hv 0).MemPos (xk 1 (fun _ => true)) ↔
      ¬ (pentagonEdgeHalfPlane (S ∘ d) hv 1).MemPos (xk 1 (fun _ => true)) :=
    Sec11Bridge.pentagon_cells_xor1_H02 hP hd_inj hv
      (by dsimp [xk_T]; exact Finset.subset_union_left) (by dsimp [xk_T]; simp [h_d_not_M 1 _])
      (hW_sub _ (hxk_in_W02 1 _)).1 (hR_in_conv _ (fun i => by simpa using hxk_mask 1 (fun _ => true) i))
  refine pentagon_wedges_no_ten_shattered_planar_regime2_local h_thm1 h_caseA_orig (S ∘ d) hv W xk hxk_mask
    (hk_nonfront 3 (Or.inr (Or.inl rfl))) (hk_nonfront 4 (Or.inr (Or.inr rfl)))
    (hk_xor 3 (Or.inr (Or.inl rfl))) (hk_xor 4 (Or.inr (Or.inr rfl)))
    ⟨fun k mask => (hW_sub _ (hxk_in_W02 k mask)).1, fun z hz => (hW_U 0 z (hz 0)).2, h_xor1⟩ ?_
  by_cases hHne : H.Nonempty
  · obtain ⟨rstar, hr0, hr1, hr_out, _⟩ := h_H_arc2 hHne
    obtain ⟨h_in_H, hhH⟩ := hHne
    have hhM : h_in_H ∈ M := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hhD => by
      dsimp [D] at hhD; rw [hDB] at hhD; exact (Finset.mem_sdiff.mp hhD).2 hhH⟩
    have hh_02 : 0 < orient2D (S (d 0)) (S (d 2)) (S h_in_H) := (hM_02_pos h_in_H hhM).2
    left
    refine ⟨rstar, hr0, hr1, ?_, ?_⟩
    · intro k mask
      have hneg := (Sec11Bridge.pentagon_cells_certified_cone_H02 hv rstar hr0 hr1 (hr_out h_in_H hhH) hh_02 _
        ((hW_sub _ (hxk_in_W02 k mask)).2 h_in_H hhM)).2
      dsimp [pentagonEdgeHalfPlane] at hneg ⊢; rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
    · intro z hz
      obtain ⟨i_h, _, hi_eq⟩ := Finset.mem_image.mp (hm_img.symm ▸ hhM)
      have hzU : z ∈ Sec11Bridge.UCone (S h_in_H) (S (d 0)) (S (d 2)) := by rw [← hi_eq]; exact (hW_U i_h z (hz i_h)).1
      have hneg := (Sec11Bridge.pentagon_cells_certified_cone_H02 hv rstar hr0 hr1 (hr_out h_in_H hhH) hh_02 _ hzU).2
      dsimp [pentagonEdgeHalfPlane] at hneg ⊢; rw [edgeHalfPlane_memPos_iff]; rw [edgeHalfPlane_memNeg_iff] at hneg; linarith
  · have hH_empty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
    right
    intro i r; rw [hWy i]
    have hall_r := hullVertices_nonneg_edge_local hP hd_inj hv hDB rfl r
      (fun h hh => by change h ∈ H at hh; rw [hH_empty] at hh; simp at hh)
    dsimp [pentagonEdgeHalfPlane]; rw [edgeHalfPlane_memPos_iff]; exact hall_r (m_enum i) (hm_mem i)

/-- **Main Theorem (`no-five-M`, `upper_9.tex` Theorem 11.4)**:
    Given the V-epigraph bitmask bound (`h_thm1`) and Case A planar wedge theorem (`h_caseA_orig`),
    no simple polygon `P ⊂ ℝ²` can contain a shattered `10`-point set `S` with valid Section 2–5
    visibility interface (`hPoly`, `h25`). -/
theorem no_ten_point_shattered_polygon
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ q : ℝ × ℝ, RealizesVMask f m q))
    (h_caseA_orig :
      (∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p)) →
      ∀ W : Fin 5 → OpenWedge,
        (∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0) →
        (∀ i : Fin 5, (W i).MemOpen (0, 0)) →
        ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p))
    {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (h25 : Sec2To5Interface P S w) :
    False := by
  let H := certifiedVertices S w
  let D := hullVertices S \ H
  let M := Finset.univ \ D
  obtain ⟨hD5, hM5⟩ := ten_points_D5_M5 hPoly h25
  obtain ⟨cycD⟩ := exists_ccwCycle S D
    (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _)) (Or.inl (Set.mem_range_self _))
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Finset.sdiff_subset) hD5
  obtain ⟨il, h_adj⟩ := pentagon_exits_adjacent_pair hPoly h25 hD5 (le_of_eq hM5.symm) cycD
  let cyc0 : CCWCycle S D 2 := ccwCycle_shift cycD il
  have h_adj0 : ∀ y ∈ M,
      (0 < orient2D (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (w D) ∧
        InIntTri (w D) (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y) ∧
        (∀ x ∈ WitnessSet {cyc0.toFun 0, cyc0.toFun 1} ∅ w,
          InIntTri x (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y)) ∧
        (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
          (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
          (cyc0.toFun 0, cyc0.toFun 1) ≠ (l, r))) ∨
      (0 < orient2D (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (w D) ∧
        InIntTri (w D) (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (S y) ∧
        (∀ x ∈ WitnessSet {cyc0.toFun 1, cyc0.toFun 2} ∅ w,
          InIntTri x (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (S y)) ∧
        (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
          (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
          (cyc0.toFun 1, cyc0.toFun 2) ≠ (l, r))) := by
    intro y hy
    rcases h_adj y hy with h | h
    · left; dsimp [cyc0, ccwCycle_shift, D, H]; simpa using h
    · right; have he2 : il + 2 = il + 1 + 1 := by abel
      dsimp [cyc0, ccwCycle_shift, D, H] at *; simpa [he2] using h
  have hDB : Finset.univ.image cyc0.toFun = hullVertices S \ certifiedVertices S w := cyc0.image_eq
  have hD3 : 3 ≤ D.card := by dsimp [D, H] at hD5 ⊢; omega
  have h_H_arc_all : H.Nonempty → ∃ rstar : Fin 5,
      (∀ h ∈ H, orient2D (S (cyc0.toFun rstar)) (S (cyc0.toFun (rstar + 1))) (S h) < 0) ∧
      (∀ i : Fin 5, i ≠ rstar → ∀ h ∈ H,
        0 < orient2D (S (cyc0.toFun i)) (S (cyc0.toFun (i + 1))) (S h)) := by
    intro hHne
    obtain ⟨l, r, hlD, hrD, hlr, hed', hH_neg, _, _, h_edges, _, _⟩ := h25.certified_structure.2 hHne
    have hed := hed' hD3
    obtain ⟨rstar, hl_eq, hr_eq⟩ := (isCCWEdge_iff_ccwCycle cyc0 _ _).mp hed
    refine ⟨rstar, ?_, ?_⟩
    · intro h hh; simpa [hl_eq, hr_eq] using hH_neg h hh
    · intro i hi h hh
      have he_B := isCCWEdge_B_of_D_ne_lr h25 hD3 (ccwCycle_isCCWEdge cyc0 i)
        (fun l' r' hH' _ _ _ hed' hHn' heq => by
          have huniq := certified_edge_unique_of_neg hPoly h25 hH' hD3 hed' hHn'
            hed hlD hrD hlr h_edges
          have hl'_eq : cyc0.toFun i = cyc0.toFun rstar := by
            rw [← hl_eq, ← huniq.1]; exact congrArg Prod.fst heq
          exact hi (cyc0.inj hl'_eq))
      exact orient2D_pos_of_isCCWEdge_B hPoly he_B
        (fun e => (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 i)).2 (e ▸ hh))
        (fun e => (Finset.mem_sdiff.mp (ccwCycle_mem cyc0 (i + 1))).2 (e ▸ hh))
  by_cases h_has01 : ∃ y ∈ M,
      0 < orient2D (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (w D) ∧
      InIntTri (w D) (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y) ∧
      (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
        (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
        (cyc0.toFun 0, cyc0.toFun 1) ≠ (l, r))
  · obtain ⟨y_w0, hyw0M, hnf01, hyw0_ex, hnot_lr01⟩ := h_has01
    by_cases h_has12 : ∃ y ∈ M,
        0 < orient2D (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (w D) ∧
        InIntTri (w D) (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (S y) ∧
        (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
          (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
          (cyc0.toFun 1, cyc0.toFun 2) ≠ (l, r))
    · obtain ⟨y_w1, hyw1M, hnf12, hyw1_ex, hnot_lr12⟩ := h_has12
      obtain ⟨y0, hy0M, hy0_ex, hy0_W, hy0_not_lr, hy0_empty⟩ :=
        minimal_on_exit_edge hPoly h25 cyc0 0 hnf01 ⟨y_w0, hyw0M, hyw0_ex⟩
      obtain ⟨y1, hy1M, hy1_ex, hy1_W, hy1_not_lr, hy1_empty⟩ :=
        minimal_on_exit_edge hPoly h25 cyc0 1 hnf12 ⟨y_w1, hyw1M, hyw1_ex⟩
      have hy01 : y0 ≠ y1 := by
        intro h; subst h
        obtain ⟨u, v, _, _, _, _, _, h_uniq⟩ := h25.exit_edge_lemma hD3 y0 hy0M
        have e0 := h_uniq _ _ (ccwCycle_isCCWEdge cyc0 0) hnf01 hy0_ex.to_convexHull
        have e1 := h_uniq _ _ (ccwCycle_isCCWEdge cyc0 1) hnf12 hy1_ex.to_convexHull
        exact cyc0.inj.ne (by decide : (0 : Fin 5) ≠ 1) (e0.1.trans e1.1.symm)
      have h_adj_loc : ∀ y ∈ Finset.univ \ D,
          (InIntTri (w D) (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y) ∧
            (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
              (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
              (cyc0.toFun 0, cyc0.toFun 1) ≠ (l, r))) ∨
          (InIntTri (w D) (S (cyc0.toFun 1)) (S (cyc0.toFun 2)) (S y) ∧
            (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
              (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
              (cyc0.toFun 1, cyc0.toFun 2) ≠ (l, r))) := fun y hy => by
        rcases h_adj0 y hy with ⟨_, hin, _, hnot⟩ | ⟨_, hin, _, hnot⟩
        · exact Or.inl ⟨hin, hnot⟩
        · exact Or.inr ⟨hin, hnot⟩
      have h_red := adjacent_reduction hPoly h25 hD5 (le_of_eq hM5.symm) cyc0 h_adj0
        hy0M hy1M ⟨hnf01, hy0_ex, hy0_W, hy0_not_lr⟩ ⟨hnf12, hy1_ex, hy1_W, hy1_not_lr⟩
        hy0_empty hy1_empty
      have h_loc0 := localization hPoly h25 hD5 hM5 cyc0 h_adj_loc hy0M ⟨hy0_ex, hy0_not_lr⟩
        hy0_empty h_red.2.1
      have h_loc1 := localization_symm hPoly h25 hD5 hM5 cyc0 h_adj_loc hy1M ⟨hy1_ex, hy1_not_lr⟩
        hy1_empty h_red.2.2.1
      refine localized_pentagon_regime2_local h_thm1 h_caseA_orig hPoly cyc0.toFun cyc0.inj cyc0.ccw_tri hDB
        (fun y hy => by
          rw [show Finset.univ.image cyc0.toFun = D from hDB] at hy ⊢
          rcases h_adj0 y hy with ⟨_, hin, _⟩ | ⟨_, hin, _⟩ <;> [exact Or.inl hin; exact Or.inr hin])
        (fun hHne => by
          obtain ⟨rstar, hr_neg, hr_pos⟩ := h_H_arc_all hHne
          obtain ⟨l, r, hlD, hrD, hlr, hed', hH_neg, _, _, h_edges, _, _⟩ := h25.certified_structure.2 hHne
          have hed := hed' hD3
          have hr0 : rstar ≠ 0 := fun h0 => by
            subst h0; exact hnot_lr01 _ _ hHne (ccwCycle_isCCWEdge cyc0 0) hr_neg rfl
          have hr1 : rstar ≠ 1 := fun h1 => by
            subst h1; exact hnot_lr12 _ _ hHne (ccwCycle_isCCWEdge cyc0 1) hr_neg rfl
          exact ⟨rstar, hr0, hr1, hr_neg, hr_pos⟩)
        (by rwa [hDB]) (by rwa [hDB]) hy01
        (by rwa [hDB]) (by rwa [hDB])
        (fun z hz => ⟨by rw [hDB] at hz; exact hy0_empty z hz, by rw [hDB] at hz; exact h_loc0.2.2.2.1 z hz⟩)
        (fun z hz => by rw [hDB] at hz; exact h_loc1 z hz)
    · have h_exit01 : ∀ y ∈ Finset.univ \ Finset.univ.image cyc0.toFun,
          0 < orient2D (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (w (Finset.univ.image cyc0.toFun)) ∧
          InIntTri (w (Finset.univ.image cyc0.toFun)) (S (cyc0.toFun 0)) (S (cyc0.toFun 1)) (S y) := by
        intro y hy
        rw [hDB] at hy ⊢
        rcases h_adj0 y hy with ⟨hnf, hin, _⟩ | ⟨hnf, hin, _, hnot⟩
        · exact ⟨hnf, hin⟩
        · exact False.elim (h_has12 ⟨y, hy, hnf, hin, hnot⟩)
      refine localized_pentagon_regime1_local h_thm1 h_caseA_orig hPoly cyc0.toFun cyc0.inj cyc0.ccw_tri hDB
        h_exit01 (fun hHne => by
          obtain ⟨rstar, hr_neg, hr_pos⟩ := h_H_arc_all hHne
          have hr0 : rstar ≠ 0 := fun h0 => by
            subst h0; exact hnot_lr01 _ _ hHne (ccwCycle_isCCWEdge cyc0 0) hr_neg rfl
          exact ⟨rstar, hr0, hr_neg, hr_pos⟩)
  · let d' : Fin 5 → Fin 10 := fun i => cyc0.toFun (i + 1)
    have hd'_inj : Function.Injective d' := cyc0.inj.comp (add_left_injective (1 : Fin 5))
    have hv' : StrictConvexCCWPentagon (S ∘ d') := strictConvexCCWPentagon_shift1_local cyc0.ccw_tri
    have hD'_eq : Finset.univ.image d' = D := by
      dsimp [D, H]; rw [← hDB]; ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, d']
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i + 1, hi⟩
      · rintro ⟨i, hi⟩; exact ⟨i - 1, by simpa using hi⟩
    have hDB' : Finset.univ.image d' = hullVertices S \ certifiedVertices S w := hD'_eq
    have h_exit01' : ∀ y ∈ Finset.univ \ Finset.univ.image d',
        0 < orient2D (S (d' 0)) (S (d' 1)) (w (Finset.univ.image d')) ∧
        InIntTri (w (Finset.univ.image d')) (S (d' 0)) (S (d' 1)) (S y) := by
      intro y hy
      rw [hD'_eq] at hy ⊢
      rcases h_adj0 y hy with ⟨hnf, hin, _, hnot⟩ | ⟨hnf, hin, _⟩
      · exact False.elim (h_has01 ⟨y, hy, hnf, hin, hnot⟩)
      · exact ⟨by simpa [d'] using hnf, by simpa [d'] using hin⟩
    refine localized_pentagon_regime1_local h_thm1 h_caseA_orig hPoly d' hd'_inj hv' hDB' h_exit01' ?_
    intro hHne
    obtain ⟨rstar, hr_neg, hr_pos⟩ := h_H_arc_all hHne
    obtain ⟨y0, hy0M⟩ := Finset.card_pos.mp (by dsimp [M, D, H] at hM5 ⊢; omega : 0 < M.card)
    have hy0_12 :
        (∀ l r : Fin 10, H.Nonempty → IsCCWEdge S D l r →
          (∀ h ∈ H, orient2D (S l) (S r) (S h) < 0) →
          (cyc0.toFun 1, cyc0.toFun 2) ≠ (l, r)) := by
      rcases h_adj0 y0 hy0M with ⟨hnf, hin, _, hnot⟩ | ⟨_, _, _, hnot⟩
      · exact False.elim (h_has01 ⟨y0, hy0M, hnf, hin, hnot⟩)
      · exact hnot
    have hr1 : rstar ≠ 1 := fun h1 => by
      subst h1; exact hy0_12 _ _ hHne (ccwCycle_isCCWEdge cyc0 1) hr_neg rfl
    refine ⟨rstar - 1, fun h0 => hr1 (sub_eq_zero.mp h0), fun h hh => ?_, fun i hi h hh => ?_⟩
    · simpa [d', sub_add_cancel] using hr_neg h hh
    · have hi1 : i + 1 ≠ rstar := fun heq => hi (eq_sub_of_add_eq heq)
      simpa [d', add_assoc] using hr_pos (i + 1) hi1 h hh

