import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.Sec5HalfPlane
import RootTask.ArrangementBounds
import RootTask.ChirotopeSoundness
import RootTask.CertifiedAndHalfPlaneSoundness

open scoped Classical BigOperators
open Finset
open PolygonCore ChirotopeSoundness CertifiedAndHalfPlaneSoundness

noncomputable section

namespace VCDim6

/-!
# Theorem 2.3: Global Half-Plane Upgrade, Intrinsic Polarization, and `(C4)` Bound

Formalizes **Theorem 2.3(1)–(4)** of `ideation_FINAL_SOLUTION.md` (`vc_dim_6_simplified.tex`
Lemma 2.6) directly from `HalfPlaneChirotopeConfig`, `half_plane_chirotope_clauses_C9`,
`Sec5HP.half_plane_lemma_orient`, `ArrangementBounds.three_halfplanes_not_all_8`, and
`non_certified_obstruction_clause_C4` — 100% computer-free and certificate-free.
-/

/-- **Intrinsic Polarization (`σ_p`)**:
    For each `p ∈ S`, `intrinsicPol S w p` represents `sgn orient(p, w_★, w_{¬p}) ∈ {true, false}`
    (`true = +1`, `false = -1`), where `w_★ = w Finset.univ` and `w_{¬p} = w (Finset.univ.erase p)`. -/
def intrinsicPol {n : ℕ} (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ) (p : Fin n) : Bool :=
  orientSign (S p) (w Finset.univ) (w (Finset.univ.erase p))

/-- Target `p` fires Lemma 4.4 with `w_1 = w_★ = w Finset.univ` across an ordered pair `(g, c)`
    via witness `Tv`. -/
def FiresOrdered {n : ℕ} (P : Set (ℝ × ℝ)) (S : Fin n → ℝ × ℝ) (w : Finset (Fin n) → ℝ × ℝ)
    (Tv : Finset (Fin n)) (g p c : Fin n) : Prop :=
  HalfPlaneChirotopeConfig P S w Tv Finset.univ g p c

/-- 2D Grassmann–Plücker four-ray identity around common origin `o`:
    `orient2D o x₁ x₄ * orient2D o x₂ x₃ = orient2D o x₁ x₃ * orient2D o x₂ x₄ - orient2D o x₁ x₂ * orient2D o x₃ x₄`. -/
lemma plucker_around_origin (o x₁ x₂ x₃ x₄ : ℝ × ℝ) :
    orient2D o x₁ x₄ * orient2D o x₂ x₃ =
      orient2D o x₁ x₃ * orient2D o x₂ x₄ - orient2D o x₁ x₂ * orient2D o x₃ x₄ := by
  unfold orient2D; ring

/-- **Theorem 2.3(1) & (2) (`fires_intrinsic_pol_and_signs`)**:
    Whenever `FiresOrdered P S w Tv g p c` holds on `ShatteredSimplePolygon P S w`:
    1. `orientSign (w Tv) (w Finset.univ) (S p) = intrinsicPol S w p` (`σ = σ_p`);
    2. `orientSign (S g) (S p) (S c) = intrinsicPol S w p`;
    3. Every `Tx` seeing `{g, c, p}` satisfies `orientSign (S p) (w Tx) (S g) = intrinsicPol S w p`;
    4. Every `Ty` seeing `{g, c}` and missing `p` satisfies
       `orientSign (S p) (w Finset.univ) (w Ty) = intrinsicPol S w p` and
       `orientSign (w Ty) (w Finset.univ) (S p) = !(intrinsicPol S w p)`. -/
theorem fires_intrinsic_pol_and_signs {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin n)} {g p c : Fin n}
    (hf : FiresOrdered P S w Tv g p c) :
    let σp := intrinsicPol S w p
    orientSign (w Tv) (w Finset.univ) (S p) = σp ∧
    orientSign (S g) (S p) (S c) = σp ∧
    (∀ {Tx : Finset (Fin n)}, {g, c} ⊆ Tx → p ∈ Tx →
      orientSign (S p) (w Tx) (S g) = σp) ∧
    (∀ {Ty : Finset (Fin n)}, {g, c} ⊆ Ty → p ∉ Ty →
      orientSign (S p) (w Finset.univ) (w Ty) = σp ∧
      orientSign (w Ty) (w Finset.univ) (S p) = !σp) := by
  intro σp
  obtain ⟨_, _, hc9_c, hc9_s⟩ := half_plane_chirotope_clauses_C9 hP hf
  have hgp : g ≠ p := fun h => hf.ha_not_v (h ▸ hf.hp_v)
  have hcp : c ≠ p := fun h => hf.hc_not_v (h ▸ hf.hp_v)
  have hgc : g ≠ c := by
    intro h
    have hc := hf.h_cross_ac
    rw [h] at hc
    have h0 : ∀ z, orient2D (S c) (S c) z = 0 := fun z => by unfold orient2D; ring
    simp [oppSideBool, orientSign, h0] at hc
  have huniv_gc : {g, c} ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have herase_gc : {g, c} ⊆ (Finset.univ.erase p : Finset (Fin n)) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hgp, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hcp, Finset.mem_univ _⟩
  have hσ_eq : orientSign (w Tv) (w Finset.univ) (S p) = σp :=
    (hc9_s huniv_gc (Finset.mem_univ p) herase_gc (Finset.notMem_erase p _)).symm
  -- Prove `orientSign (S g) (S p) (S c) = σp` via Grassmann-Plucker / crossing on `(w Tv, S p, S g, S c)`
  have hgpc : orientSign (S g) (S p) (S c) = σp := by
    have hvgp : orientSign (w Tv) (S g) (S p) = σp := hf.h_vap.trans hσ_eq
    have hvpc : orientSign (w Tv) (S p) (S c) = σp := hf.h_vpc.trans hσ_eq
    have hcross := (oppSideBool_iff_mul_neg
      (orient_S_S_w_ne hP hgc Tv) (orient_S_S_S_ne hP hgc hcp hgp)).mp hf.h_cross_ac
    -- Identity: `orient(g, c, v) + orient(c, p, v) + orient(p, g, v)` doesn't apply; instead use
    -- `orient(v, g, c) = ...`? Wait: `orient2D g c p - orient2D g c v = orient2D v g p + orient2D v p c`!
    have raff : orient2D (S g) (S c) (S p) - orient2D (S g) (S c) (w Tv) =
        -(orient2D (w Tv) (S g) (S p) + orient2D (w Tv) (S p) (S c)) := by
      unfold orient2D; ring
    have hvgp_ne := orient_w_S_S_ne hP Tv hgp
    have hvpc_ne := orient_w_S_S_ne hP Tv hcp.symm
    have hgpc_ne := orient_S_S_S_ne hP hgp hcp.symm hgc
    have hgcp_ne := orient_S_S_S_ne hP hgc hcp hgp
    rw [orientSign_swap23 hgcp_ne]
    -- Need `!orientSign (S g) (S c) (S p) = σp`
    cases hσ : σp
    · rw [hσ] at hvgp hvpc
      have h1 : orient2D (w Tv) (S g) (S p) < 0 := (orientSign_eq_false_iff_of_ne_zero hvgp_ne).mp hvgp
      have h2 : orient2D (w Tv) (S p) (S c) < 0 := (orientSign_eq_false_iff_of_ne_zero hvpc_ne).mp hvpc
      have hpos : 0 < orient2D (S g) (S c) (S p) := by nlinarith
      simp [(orientSign_eq_true_iff _ _ _).mpr hpos]
    · rw [hσ] at hvgp hvpc
      have h1 : 0 < orient2D (w Tv) (S g) (S p) := (orientSign_eq_true_iff _ _ _).mp hvgp
      have h2 : 0 < orient2D (w Tv) (S p) (S c) := (orientSign_eq_true_iff _ _ _).mp hvpc
      have hneg : orient2D (S g) (S c) (S p) < 0 := by nlinarith
      simp [(orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)]
  refine ⟨hσ_eq, hgpc, ?_, ?_⟩
  · intro Tx hgc_Tx hp_Tx
    exact (hc9_c hgc_Tx hp_Tx).1.trans hσ_eq
  · intro Ty hgc_Ty hp_not_Ty
    have hs := (hc9_s huniv_gc (Finset.mem_univ p) hgc_Ty hp_not_Ty).trans hσ_eq
    have hTy_ne : Finset.univ ≠ Ty := fun he => hp_not_Ty (he ▸ Finset.mem_univ p)
    have hrev : orientSign (w Ty) (w Finset.univ) (S p) = !σp := by
      have h1 : orientSign (w Ty) (w Finset.univ) (S p) = !orientSign (w Finset.univ) (w Ty) (S p) :=
        orientSign_swap12 (orient_w_w_S_ne hP hTy_ne p)
      have h2 : orientSign (w Finset.univ) (w Ty) (S p) = orientSign (S p) (w Finset.univ) (w Ty) :=
        orientSign_cycle _ _ _
      rw [h1, h2, hs]
    exact ⟨hs, hrev⟩

/-- **Theorem 2.3(3) (`fires_unmarked_c_sign`)**:
    If `3 ≤ n`, `p ∈ D = hullVertices S \ certifiedSet P S w`, and `FiresOrdered P S w Tv g p c`,
    then every `Ty` seeing `{g, c}` and missing `p` satisfies
    `orientSign (S p) (S c) (w Ty) = intrinsicPol S w p`. -/
theorem fires_unmarked_c_sign {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w) (hn : 3 ≤ n)
    {Tv Ty : Finset (Fin n)} {g p c : Fin n}
    (hf : FiresOrdered P S w Tv g p c)
    (hpD : p ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w)
    (hgc_Ty : {g, c} ⊆ Ty) (hp_not_Ty : p ∉ Ty) :
    orientSign (S p) (S c) (w Ty) = intrinsicPol S w p := by
  let σp := intrinsicPol S w p
  obtain ⟨hσ_eq, hgpc, _, _⟩ := fires_intrinsic_pol_and_signs hP hf
  obtain ⟨_, hc9_b, _, _⟩ := half_plane_chirotope_clauses_C9 hP hf
  have hgp : g ≠ p := fun h => hf.ha_not_v (h ▸ hf.hp_v)
  have hcp : c ≠ p := fun h => hf.hc_not_v (h ▸ hf.hp_v)
  have hgc : g ≠ c := by
    intro h; have hc := hf.h_cross_ac; rw [h] at hc
    have h0 : ∀ z, orient2D (S c) (S c) z = 0 := fun z => by unfold orient2D; ring
    simp [oppSideBool, orientSign, h0] at hc
  have hg_Ty : g ∈ Ty := hgc_Ty (by simp)
  have hc_Ty : c ∈ Ty := hgc_Ty (by simp)
  have hTv_ne_Ty : Tv ≠ Ty := fun he => hf.ha_not_v (he ▸ hg_Ty)
  have hvpy_not : orientSign (w Tv) (S p) (w Ty) = !σp := by
    rw [(hc9_b hgc_Ty).1, hσ_eq]
  -- Suppose for contradiction `orientSign (S p) (S c) (w Ty) ≠ σp`, i.e., `= !σp`
  by_contra hne
  have hpcy_not : orientSign (S p) (S c) (w Ty) = !σp := by
    cases h1 : orientSign (S p) (S c) (w Ty) <;> cases h2 : σp <;> simp_all
  -- Plucker identity around `S p` on `(S g, w Tv, S c, w Ty)`:
  have hpl := plucker_around_origin (S p) (S g) (w Tv) (S c) (w Ty)
  have hpvc_ne : orient2D (S p) (w Tv) (S c) ≠ 0 := orient_S_w_S_ne hP hcp.symm Tv
  have hpgc_ne : orient2D (S p) (S g) (S c) ≠ 0 := orient_S_S_S_ne hP hgp.symm hgc hcp.symm
  have hpvy_ne : orient2D (S p) (w Tv) (w Ty) ≠ 0 := orient_S_w_w_ne hP p hTv_ne_Ty
  have hpgv_ne : orient2D (S p) (S g) (w Tv) ≠ 0 := orient_S_S_w_ne hP hgp.symm Tv
  have hpcy_ne : orient2D (S p) (S c) (w Ty) ≠ 0 := orient_S_S_w_ne hP hcp.symm Ty
  have hvpc_s : orientSign (w Tv) (S p) (S c) = σp := hf.h_vpc.trans hσ_eq
  have hvgp_s : orientSign (w Tv) (S g) (S p) = σp := hf.h_vap.trans hσ_eq
  have hpvc_s : orientSign (S p) (w Tv) (S c) = !σp := by
    rw [orientSign_swap12 (orient_w_S_S_ne hP Tv hcp.symm), hvpc_s]
  have hpgc_s : orientSign (S p) (S g) (S c) = !σp := by
    rw [orientSign_swap12 (orient_S_S_S_ne hP hgp hcp.symm hgc), hgpc]
  have hpvy_s : orientSign (S p) (w Tv) (w Ty) = σp := by
    rw [orientSign_swap12 (orient_w_S_w_ne hP hTv_ne_Ty p), hvpy_not, Bool.not_not]
  have hpgv_s : orientSign (S p) (S g) (w Tv) = !σp := by
    have hcyc : orientSign (S p) (S g) (w Tv) = orientSign (w Tv) (S p) (S g) := orientSign_cycle _ _ _
    rw [hcyc, orientSign_swap23 (orient_w_S_S_ne hP Tv hgp), hvgp_s]
  have htri_side : inOpenTriSideBool σp (S p) (w Ty) (S c) (S g) = true := by
    unfold inOpenTriSideBool
    have hycp_s : orientSign (w Ty) (S c) (S p) = σp := by
      have : orientSign (w Ty) (S c) (S p) = !orientSign (S p) (S c) (w Ty) := by
        rw [orientSign_cycle2 (S c) (S p) (w Ty), orientSign_swap12 hpcy_ne]
      rw [this, hpcy_not, Bool.not_not]
    have hcgp_s : orientSign (S c) (S g) (S p) = σp := by
      rw [orientSign_cycle2 (S g) (S p) (S c), hgpc]
    have hgyp_s : orientSign (S g) (w Ty) (S p) = σp := by
      rw [orientSign_cycle (S p) (S g) (w Ty)]
      cases hσ : σp
      · rw [hσ] at hpvc_s hpgc_s hpvy_s hpgv_s hpcy_not
        simp only [Bool.not_false] at hpvc_s hpgc_s hpgv_s hpcy_not
        have a1 := (orientSign_eq_true_iff _ _ _).mp hpvc_s
        have a2 := (orientSign_eq_true_iff _ _ _).mp hpgc_s
        have a3 := (orientSign_eq_false_iff_of_ne_zero hpvy_ne).mp hpvy_s
        have a4 := (orientSign_eq_true_iff _ _ _).mp hpgv_s
        have a5 := (orientSign_eq_true_iff _ _ _).mp hpcy_not
        have hneg : orient2D (S p) (S g) (w Ty) < 0 := by nlinarith
        exact (orientSign_eq_false_iff _ _ _).mpr (le_of_lt hneg)
      · rw [hσ] at hpvc_s hpgc_s hpvy_s hpgv_s hpcy_not
        simp only [Bool.not_true] at hpvc_s hpgc_s hpgv_s hpcy_not
        have a1 := (orientSign_eq_false_iff_of_ne_zero hpvc_ne).mp hpvc_s
        have a2 := (orientSign_eq_false_iff_of_ne_zero hpgc_ne).mp hpgc_s
        have a3 := (orientSign_eq_true_iff _ _ _).mp hpvy_s
        have a4 := (orientSign_eq_false_iff_of_ne_zero hpgv_ne).mp hpgv_s
        have a5 := (orientSign_eq_false_iff_of_ne_zero hpcy_ne).mp hpcy_not
        have hpos : 0 < orient2D (S p) (S g) (w Ty) := by nlinarith
        exact (orientSign_eq_true_iff _ _ _).mpr hpos
    simp [hycp_s, hcgp_s, hgyp_s]
  have htri : inOpenTriBool (S p) (w Ty) (S c) (S g) = true := by
    unfold inOpenTriBool; cases hs : σp <;> rw [hs] at htri_side <;> simp [htri_side]
  have hfalse := non_certified_obstruction_clause_C4 hP hn hpD hp_not_Ty hc_Ty hg_Ty hgc.symm
  rw [hfalse] at htri
  exact Bool.noConfusion htri

/-- Extracts an `OpenHalfPlane` test on `WitnessSet {a, b} ∅ w` from any `FiresOrdered P S w Tv g p c`
    with `{g, c} = {a, b}`. -/
theorem fires_half_plane_test {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {Tv : Finset (Fin n)} {g p c a b : Fin n}
    (hf : FiresOrdered P S w Tv g p c)
    (hpair : ({g, c} : Finset (Fin n)) = {a, b}) :
    ∃ H : OpenHalfPlane, IsHalfPlaneTest P (WitnessSet {a, b} ∅ w) (S p) H := by
  have hTvq : Tv ≠ Finset.univ := fun he => hf.ha_not_v (he ▸ Finset.mem_univ g)
  have hgp : g ≠ p := fun h => hf.ha_not_v (h ▸ hf.hp_v)
  have hcp : c ≠ p := fun h => hf.hc_not_v (h ▸ hf.hp_v)
  have hgc : g ≠ c := by
    intro h; have hc := hf.h_cross_ac; rw [h] at hc
    have h0 : ∀ z, orient2D (S c) (S c) z = 0 := fun z => by unfold orient2D; ring
    simp [oppSideBool, orientSign, h0] at hc
  have hvqp_ne := orient_w_w_S_ne hP hTvq p
  have hvqg_ne := orient_w_w_S_ne hP hTvq g
  have hvqc_ne := orient_w_w_S_ne hP hTvq c
  have hvgp_ne := orient_w_S_S_ne hP Tv hgp
  have hvpc_ne := orient_w_S_S_ne hP Tv hcp.symm
  have hsame_gp : Sec5HP.SameSideOfLine (w Tv) (w Finset.univ) (S g) (S p) :=
    mul_pos_of_orientSign_eq hvqg_ne hvqp_ne hf.h_vqa rfl
  have hsame_cp : Sec5HP.SameSideOfLine (w Tv) (w Finset.univ) (S c) (S p) :=
    mul_pos_of_orientSign_eq hvqc_ne hvqp_ne hf.h_vqc rfl
  have htheta_gp := mul_pos_of_orientSign_eq hvgp_ne hvqp_ne hf.h_vap rfl
  have htheta_pc := mul_pos_of_orientSign_eq hvpc_ne hvqp_ne hf.h_vpc rfl
  have hcross : Sec5HP.SegmentsCross (w Tv) (S p) (S g) (S c) := by
    refine ⟨?_, (oppSideBool_iff_mul_neg (orient_S_S_w_ne hP hgc Tv)
      (orient_S_S_S_ne hP hgc hcp hgp)).mp hf.h_cross_ac⟩
    have hvpg_opp : orientSign (w Tv) (S p) (S g) = !orientSign (w Tv) (w Finset.univ) (S p) := by
      rw [orientSign_swap23 hvgp_ne, hf.h_vap]
    exact mul_neg_of_orientSign_opp (orient_w_S_S_ne hP Tv hgp.symm) hvpc_ne hvpg_opp
      (by rw [Bool.not_not]; exact hf.h_vpc)
  have hiv : Sees P (w Tv) (w Finset.univ) ∨
      ∃ ie : Fin n, Sees P (w Tv) (S ie) ∧ Sees P (w Finset.univ) (S ie) ∧
        Sec5HP.SameSideOfLine (w Tv) (w Finset.univ) (S ie) (S g) ∧
        0 < orient2D (w Tv) (S ie) (S g) * orient2D (w Tv) (w Finset.univ) (S p) := by
    rcases hf.h_cond_iv with hvq | ⟨s₁, s₂, hs1v, hs1q, hs2v, hs2q, hopp⟩ | ⟨ie, hev, heq_in, hvqe, hveg⟩
    · exact Or.inl hvq
    · exact Or.inl (vis_chord_sees_of_oppSide hP hTvq hs1v hs1q hs2v hs2q hopp)
    · right
      have heg : ie ≠ g := fun h => hf.ha_not_v (h ▸ hev)
      exact ⟨ie, (hP.shatters Tv ie).mpr hev, (hP.shatters Finset.univ ie).mpr heq_in,
        mul_pos_of_orientSign_eq (orient_w_w_S_ne hP hTvq ie) hvqg_ne hvqe hf.h_vqa,
        mul_pos_of_orientSign_eq (orient_w_S_S_ne hP Tv heg) hvqp_ne hveg rfl⟩
  obtain ⟨H, hH_test, _, _, _, _, _, _⟩ := Sec5HP.half_plane_lemma_orient hP Tv Finset.univ g p c
    ((hP.shatters Tv p).mpr hf.hp_v)
    (fun hs => hf.ha_not_v ((hP.shatters Tv g).mp hs))
    (fun hs => hf.hc_not_v ((hP.shatters Tv c).mp hs))
    ((hP.shatters Finset.univ g).mpr hf.ha_q)
    ((hP.shatters Finset.univ p).mpr hf.hp_q)
    ((hP.shatters Finset.univ c).mpr hf.hc_q)
    hsame_gp hsame_cp htheta_gp htheta_pc hcross hiv
  rw [hpair] at hH_test
  exact ⟨H, hH_test⟩

/-- **Theorem 2.3(4) (`chord_capacity_le_two`)**:
    For every unordered pair `{a, b}`, at most **two** distinct targets `p₀, p₁, p₂ ∈ S \ {a, b}`
    can admit `OpenHalfPlane` tests on `WitnessSet {a, b} ∅ w` (in particular, at most two targets
    can fire Lemma 4.4 across `{a, b}`). -/
theorem chord_capacity_le_two {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {a b p₀ p₁ p₂ : Fin n}
    (hp01 : p₀ ≠ p₁) (hp02 : p₀ ≠ p₂) (hp12 : p₁ ≠ p₂)
    (hp0_ab : p₀ ∉ ({a, b} : Finset (Fin n)))
    (hp1_ab : p₁ ∉ ({a, b} : Finset (Fin n)))
    (hp2_ab : p₂ ∉ ({a, b} : Finset (Fin n)))
    {H₀ H₁ H₂ : OpenHalfPlane}
    (ht0 : IsHalfPlaneTest P (WitnessSet {a, b} ∅ w) (S p₀) H₀)
    (ht1 : IsHalfPlaneTest P (WitnessSet {a, b} ∅ w) (S p₁) H₁)
    (ht2 : IsHalfPlaneTest P (WitnessSet {a, b} ∅ w) (S p₂) H₂) : False := by
  let H : Fin 3 → OpenHalfPlane := ![H₀, H₁, H₂]
  apply ArrangementBounds.three_halfplanes_not_all_8 H
  intro m
  let Tm : Finset (Fin n) :=
    {a, b} ∪ (if m 0 then {p₀} else ∅) ∪ (if m 1 then {p₁} else ∅) ∪ (if m 2 then {p₂} else ∅)
  have hmem_ite : ∀ {b₀ : Bool} {x y : Fin n},
      x ∈ (if b₀ then ({y} : Finset (Fin n)) else ∅) ↔ b₀ = true ∧ x = y := by
    intro b₀ x y; cases b₀ <;> simp
  have hab_sub : ({a, b} : Finset (Fin n)) ⊆ Tm :=
    Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hw_mem : w Tm ∈ WitnessSet {a, b} ∅ w :=
    ⟨Tm, hab_sub, Finset.disjoint_empty_right Tm, rfl⟩
  refine ⟨w Tm, fun i => ?_⟩
  fin_cases i
  · change if m 0 = true then H₀.MemPos (w Tm) else H₀.MemNeg (w Tm)
    have hmem_iff : p₀ ∈ Tm ↔ m 0 = true := by
      simp only [Tm, Finset.mem_union, hmem_ite, hp0_ab, false_or, and_true,
        hp01, hp02, and_false, or_false]
    obtain ⟨hside, hsees⟩ := ht0 (w Tm) hw_mem
    cases hm : m 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hside with hpos | hneg
      · exact False.elim (Bool.noConfusion (hm ▸ hmem_iff.mp ((hP.shatters Tm p₀).mp (hsees.mpr hpos))))
      · exact hneg
    · simp only [↓reduceIte]
      exact hsees.mp ((hP.shatters Tm p₀).mpr (hmem_iff.mpr hm))
  · change if m 1 = true then H₁.MemPos (w Tm) else H₁.MemNeg (w Tm)
    have hmem_iff : p₁ ∈ Tm ↔ m 1 = true := by
      simp only [Tm, Finset.mem_union, hmem_ite, hp1_ab, false_or, and_true,
        hp01.symm, hp12, and_false, or_false]
    obtain ⟨hside, hsees⟩ := ht1 (w Tm) hw_mem
    cases hm : m 1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hside with hpos | hneg
      · exact False.elim (Bool.noConfusion (hm ▸ hmem_iff.mp ((hP.shatters Tm p₁).mp (hsees.mpr hpos))))
      · exact hneg
    · simp only [↓reduceIte]
      exact hsees.mp ((hP.shatters Tm p₁).mpr (hmem_iff.mpr hm))
  · change if m 2 = true then H₂.MemPos (w Tm) else H₂.MemNeg (w Tm)
    have hmem_iff : p₂ ∈ Tm ↔ m 2 = true := by
      simp only [Tm, Finset.mem_union, hmem_ite, hp2_ab, false_or, and_true,
        hp02.symm, hp12.symm, and_false, or_false]
    obtain ⟨hside, hsees⟩ := ht2 (w Tm) hw_mem
    cases hm : m 2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rcases hside with hpos | hneg
      · exact False.elim (Bool.noConfusion (hm ▸ hmem_iff.mp ((hP.shatters Tm p₂).mp (hsees.mpr hpos))))
      · exact hneg
    · simp only [↓reduceIte]
      exact hsees.mp ((hP.shatters Tm p₂).mpr (hmem_iff.mpr hm))

end VCDim6

end
