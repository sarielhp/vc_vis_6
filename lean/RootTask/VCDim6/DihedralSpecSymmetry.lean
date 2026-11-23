import Mathlib
import RootTask.VCDim6.CoreClauseSoundness
import RootTask.VCDim6.SymmetryAndMonotonicity

open scoped Classical BigOperators
open Finset
open PolygonCore NewEnclosure ChirotopeSoundness CertifiedAndHalfPlaneSoundness
open VCDimSixMasterBridge VCDim6.FastTrieRUP

noncomputable section

namespace VCDim6

/-!
# Dihedral Action on `ValidCanonicalInstance` (`DihedralSpecSymmetry.lean`)

Provides the four elementary symmetry generators on `ValidCanonicalInstance P S w spec` (`Fin 7`):
1. `ValidCanonicalInstance.withMasks`: replaces `spec.masks` (independent of `ValidCanonicalInstance`).
2. `ValidCanonicalInstance.swapAdjA`: swaps adjacent interior points `n_d + h_sz + k` and
   `n_d + h_sz + k + 1` in `A = interiorPoints S` and their exit-edge entries in `spec.edges`.
3. `ValidCanonicalInstance.stepRotD` / `rotateD`: cyclically shifts `D = hullVertices S \ H`
   (`0 .. n_d - 1`) while fixing `H` and `A`, shifting `spec.lr_l` and `spec.edges` by `+1 mod n_d`.
4. `ValidCanonicalInstance.reflD`: applies horizontal reflection `reflX` + dihedral involution on
   `lr_l = (if h_sz = 0 then none else some 0)`, reversing the pocket exit-edge block `0 .. h_sz - 1`
   and mapping every exit edge `u ↦ (n_d - u) % n_d`.
-/

/-! ## 1. Mask Replacement & Basic `listGetOpt` / Triangle Helpers -/

def withMasksSpec (spec : CaseSpec) (masks' : List ℕ) : CaseSpec :=
  { spec with masks := masks' }

theorem ValidCanonicalInstance.withMasks {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec) (masks' : List ℕ) :
    ValidCanonicalInstance P S w (withMasksSpec spec masks') :=
  ⟨hV.hP, hV.h_nd_ge2, hV.h_tot_le7, hV.h_bsz_ge3,
   hV.hD_mem, hV.hH_mem, hV.h_cb, hV.h_pocket, hV.h_edges⟩

lemma listGetOpt_eq_getElem? {α : Type*} : ∀ (l : List α) (i : ℕ), listGetOpt l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => listGetOpt_eq_getElem? xs k

private lemma erase_image_perm_fix {σ : Equiv.Perm (Fin 7)} {h : Fin 7} :
    (Finset.univ.erase h).image σ = Finset.univ.erase (σ h) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨j, hjh, rfl⟩
    exact σ.injective.ne hjh
  · intro hx
    exact ⟨σ.symm x, fun e => hx (by rw [← e, σ.apply_symm_apply]), σ.apply_symm_apply x⟩

private lemma zWitness_relabelW (σ : Equiv.Perm (Fin 7))
    (w : Finset (Fin 7) → ℝ × ℝ) (h : Fin 7) :
    PolygonCore.zWitness (relabelW σ w) h = PolygonCore.zWitness w (σ h) := by
  dsimp [PolygonCore.zWitness, relabelW]
  rw [erase_image_perm_fix]

private lemma inOpenTriBool_swap_endpoints {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hP : ShatteredSimplePolygon P S w)
    {y a b : Fin 7} (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b)
    (Tw : Finset (Fin 7))
    (h : inOpenTriBool (S y) (w Tw) (S a) (S b) = true) :
    inOpenTriBool (S y) (w Tw) (S b) (S a) = true := by
  have htri : InOpenTri (w Tw) (S a) (S b) (S y) :=
    (inOpenTriBool_S_w_S_S hP hya hyb hab Tw).mp h
  exact (inOpenTriBool_S_w_S_S hP hyb hya hab.symm Tw).mpr (inOpenTri_perm_23 htri)

private lemma inOpenTriBool_reflX {p a b c : ℝ × ℝ}
    (h1 : orient2D a b p ≠ 0) (h2 : orient2D b c p ≠ 0) (h3 : orient2D c a p ≠ 0)
    (h : inOpenTriBool p a b c = true) :
    inOpenTriBool (reflX p) (reflX a) (reflX b) (reflX c) = true := by
  unfold inOpenTriBool inOpenTriSideBool at h ⊢
  rw [orientSign_reflX h1, orientSign_reflX h2, orientSign_reflX h3]
  rcases Bool.or_eq_true_iff.mp h with ht | hf
  · apply Bool.or_eq_true_iff.mpr; right
    simp only [Bool.and_eq_true, beq_iff_eq] at ht ⊢
    rcases ht with ⟨⟨e1, e2⟩, e3⟩
    exact ⟨⟨by rw [e1]; rfl, by rw [e2]; rfl⟩, by rw [e3]; rfl⟩
  · apply Bool.or_eq_true_iff.mpr; left
    simp only [Bool.and_eq_true, beq_iff_eq] at hf ⊢
    rcases hf with ⟨⟨e1, e2⟩, e3⟩
    exact ⟨⟨by rw [e1]; rfl, by rw [e2]; rfl⟩, by rw [e3]; rfl⟩

/-! ## 2. Cyclic Shift & Reversal of `CyclicSubsetBoundary` -/

private lemma cyclicOrder_add_const {N : ℕ} (sh i j k : Fin N)
    (h : PolygonCore.CyclicOrder i j k) :
    PolygonCore.CyclicOrder (i + sh) (j + sh) (k + sh) := by
  unfold PolygonCore.CyclicOrder at h ⊢
  simp only [Fin.lt_def, Fin.val_add_eq_ite] at h ⊢
  have := i.isLt; have := j.isLt; have := k.isLt; have := sh.isLt
  split_ifs <;> omega

private lemma cyclicOrder_sub_rev {N : ℕ} (c i j k : Fin N)
    (h : PolygonCore.CyclicOrder i j k) :
    PolygonCore.CyclicOrder (c - k) (c - j) (c - i) := by
  unfold PolygonCore.CyclicOrder at h ⊢
  have hsub : ∀ x : Fin N, (c - x).val = if x.val ≤ c.val then c.val - x.val else c.val + N - x.val := by
    intro x
    have := c.isLt; have := x.isLt
    change ((N - x.val) + c.val) % N = _
    split_ifs with hle
    · have heq : (N - x.val) + c.val = N + (c.val - x.val) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · have heq : (N - x.val) + c.val = c.val + N - x.val := by omega
      rw [heq, Nat.mod_eq_of_lt (by omega)]
  simp only [Fin.lt_def, hsub] at h ⊢
  have := i.isLt; have := j.isLt; have := k.isLt; have := c.isLt
  split_ifs <;> omega

private lemma strictConvexCCWPoly_of_hcyc {m : ℕ} {p : Fin (m + 3) → ℝ × ℝ}
    (hcyc : ∀ i j k : Fin (m + 3), PolygonCore.CyclicOrder i j k → 0 < orient2D (p i) (p j) (p k)) :
    StrictConvexCCWPoly p := by
  intro i j hji hj1
  have h1_eq : (1 : Fin (m + 3)) = ⟨1 % (m + 3), Nat.mod_lt 1 (by omega)⟩ := by
    ext; change 1 % (m + 3) = 1 % (m + 3); rfl
  rw [h1_eq] at hj1
  have hc := PolygonCore.cyclicOrder_succ (by omega : 3 ≤ m + 3) hji hj1
  rw [← h1_eq] at hc
  exact hcyc i (i + 1) j hc

private lemma relabelShiftCB_hcyc {S : Fin 7 → ℝ × ℝ} (σ : Equiv.Perm (Fin 7))
    (cb : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S))
    (sh : Fin (cb.m + 3)) :
    ∀ i j k : Fin (cb.m + 3), PolygonCore.CyclicOrder i j k →
      0 < orient2D (relabelS σ S (σ.symm (cb.p_idx (i + sh))))
                   (relabelS σ S (σ.symm (cb.p_idx (j + sh))))
                   (relabelS σ S (σ.symm (cb.p_idx (k + sh)))) := by
  intro i j k h
  simp only [relabelS, Function.comp_apply, σ.apply_symm_apply]
  exact cb.hcyc (i + sh) (j + sh) (k + sh) (cyclicOrder_add_const sh i j k h)

private def relabelShiftCB {S : Fin 7 → ℝ × ℝ} (σ : Equiv.Perm (Fin 7))
    (cb : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S))
    (sh : Fin (cb.m + 3)) :
    PolygonCore.CyclicSubsetBoundary (relabelS σ S) (PolygonCore.hullVertices (relabelS σ S)) where
  m := cb.m
  p_idx := fun idx => σ.symm (cb.p_idx (idx + sh))
  hp_idx_inj := fun _ _ hij => add_right_cancel (cb.hp_idx_inj (σ.symm.injective hij))
  hp_idx_img := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_hullVertices_relabel]
    have himg := Finset.ext_iff.mp cb.hp_idx_img (σ x)
    rw [← himg]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i + sh, (σ.apply_symm_apply _).symm⟩
    · rintro ⟨j, hj⟩
      refine ⟨j - sh, ?_⟩
      rw [sub_add_cancel, hj, σ.symm_apply_apply]
  hstrict := strictConvexCCWPoly_of_hcyc (relabelShiftCB_hcyc σ cb sh)
  hcyc := relabelShiftCB_hcyc σ cb sh

private lemma reflRevCB_hcyc {S : Fin 7 → ℝ × ℝ} (σ : Equiv.Perm (Fin 7))
    (cb : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S))
    (c : Fin (cb.m + 3)) :
    ∀ i j k : Fin (cb.m + 3), PolygonCore.CyclicOrder i j k →
      0 < orient2D ((reflX ∘ relabelS σ S) (σ.symm (cb.p_idx (c - i))))
                   ((reflX ∘ relabelS σ S) (σ.symm (cb.p_idx (c - j))))
                   ((reflX ∘ relabelS σ S) (σ.symm (cb.p_idx (c - k)))) := by
  intro i j k h
  simp only [Function.comp_apply, relabelS, σ.apply_symm_apply, orient2D_reflX]
  have hpos := cb.hcyc (c - k) (c - j) (c - i) (cyclicOrder_sub_rev c i j k h)
  have hid : -orient2D (S (cb.p_idx (c - i))) (S (cb.p_idx (c - j))) (S (cb.p_idx (c - k))) =
      orient2D (S (cb.p_idx (c - k))) (S (cb.p_idx (c - j))) (S (cb.p_idx (c - i))) := by
    unfold orient2D; ring
  linarith

private def reflRevCB {S : Fin 7 → ℝ × ℝ} (σ : Equiv.Perm (Fin 7))
    (cb : PolygonCore.CyclicSubsetBoundary S (PolygonCore.hullVertices S))
    (c : Fin (cb.m + 3)) :
    PolygonCore.CyclicSubsetBoundary (reflX ∘ relabelS σ S)
      (PolygonCore.hullVertices (reflX ∘ relabelS σ S)) where
  m := cb.m
  p_idx := fun idx => σ.symm (cb.p_idx (c - idx))
  hp_idx_inj := fun i j hij => by
    have h1 : c - i = c - j := cb.hp_idx_inj (σ.symm.injective hij)
    have h2 : c - (c - i) = c - (c - j) := congrArg (fun z => c - z) h1
    simpa using h2
  hp_idx_img := by
    rw [hullVertices_reflX]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_hullVertices_relabel]
    have himg := Finset.ext_iff.mp cb.hp_idx_img (σ x)
    rw [← himg]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨c - i, (σ.apply_symm_apply _).symm⟩
    · rintro ⟨j, hj⟩
      refine ⟨c - j, ?_⟩
      have hc : c - (c - j) = j := by abel
      rw [hc, hj, σ.symm_apply_apply]
  hstrict := strictConvexCCWPoly_of_hcyc (reflRevCB_hcyc σ cb c)
  hcyc := reflRevCB_hcyc σ cb c

/-! ## 3. Generator 1: Swapping Adjacent Interior Points (`swapAdjA`) -/

def swapNatPair (a b x : ℕ) : ℕ :=
  if x = a then b else if x = b then a else x

def swapEdgesAt (n_d pos : ℕ) (edges : List (Option ℕ)) : List (Option ℕ) :=
  (List.range (7 - n_d)).map fun i =>
    match listGetOpt edges (swapNatPair pos (pos + 1) i) with
    | some v => v
    | none => none

@[reducible] def swapAdjASpec (spec : CaseSpec) (k : ℕ) : CaseSpec :=
  { spec with edges := swapEdgesAt spec.n_d (spec.h_sz + k) spec.edges }

theorem ValidCanonicalInstance.swapAdjA {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec)
    (k : ℕ) (hk : spec.n_d + spec.h_sz + k + 1 < 7) :
    ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
      ValidCanonicalInstance P S' w' (swapAdjASpec spec k) := by
  have hnd2 := hV.h_nd_ge2
  have htot := hV.h_tot_le7
  have hbsz3 := hV.h_bsz_ge3
  let a₁ : Fin 7 := ⟨spec.n_d + spec.h_sz + k, by omega⟩
  let a₂ : Fin 7 := ⟨spec.n_d + spec.h_sz + k + 1, by omega⟩
  let σ : Equiv.Perm (Fin 7) := Equiv.swap a₁ a₂
  have hfix : ∀ x : Fin 7, x.val < spec.n_d + spec.h_sz → σ x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne
      (fun e => by have := congrArg Fin.val e; dsimp [a₁] at this; omega)
      (fun e => by have := congrArg Fin.val e; dsimp [a₂] at this; omega)
  have hfix_symm : ∀ x : Fin 7, x.val < spec.n_d + spec.h_sz → σ.symm x = x := by
    intro x hx; change σ x = x; exact hfix x hx
  have hlt_iff : ∀ (m : ℕ), m ≤ spec.n_d + spec.h_sz → ∀ x : Fin 7, (σ x).val < m ↔ x.val < m := by
    intro m hm x
    constructor
    · intro hs
      have hxs : σ (σ x) = σ x := hfix (σ x) (by omega)
      have hself : σ (σ x) = x := Equiv.swap_apply_self a₁ a₂ x
      rw [hself] at hxs
      rw [hxs]; exact hs
    · intro hx
      rw [hfix x (by omega)]; exact hx
  refine ⟨relabelS σ S, relabelW σ w, {
    hP := shattered_relabel hV.hP σ
    h_nd_ge2 := hV.h_nd_ge2
    h_tot_le7 := hV.h_tot_le7
    h_bsz_ge3 := hV.h_bsz_ge3
    hD_mem := fun x => by
      dsimp only [swapAdjASpec]
      rw [Finset.mem_sdiff, mem_hullVertices_relabel, mem_certifiedSet_relabel,
          ← Finset.mem_sdiff, hV.hD_mem, hlt_iff spec.n_d (by omega)]
    hH_mem := fun x => by
      dsimp only [swapAdjASpec]
      rw [mem_certifiedSet_relabel, hV.hH_mem]
      have h1 := hlt_iff spec.n_d (by omega) x
      have h2 := hlt_iff (spec.n_d + spec.h_sz) le_rfl x
      omega
    h_cb := ?_
    h_pocket := ?_
    h_edges := ?_
  }⟩
  · obtain ⟨cb, hlen, hget⟩ := hV.h_cb
    have hbccw_eq : buildBccw (swapAdjASpec spec k) = buildBccw spec := rfl
    refine ⟨relabelShiftCB σ cb 0, by rw [hbccw_eq]; exact hlen, fun idx => ?_⟩
    change Fin (cb.m + 3) at idx
    rw [hbccw_eq]
    have hg0 := hget idx
    have hb_lt : ∀ v ∈ buildBccw spec, v < spec.n_d + spec.h_sz := by
      have haux : ∀ d rem, d + rem = spec.n_d →
          ∀ v ∈ buildBccwAux spec.n_d spec.h_sz spec.lr_l d rem, v < spec.n_d + spec.h_sz := by
        intro d rem hd v hv
        induction rem generalizing d with
        | zero => simp [buildBccwAux] at hv
        | succ r ih =>
          unfold buildBccwAux at hv
          split_ifs at hv
          · rcases List.mem_cons.mp hv with rfl | hmem
            · omega
            · rcases List.mem_append.mp hmem with hrng | htl
              · have hbr : ∀ st c, st + c ≤ spec.n_d + spec.h_sz → ∀ u ∈ buildRange st c, u < spec.n_d + spec.h_sz := by
                  intro st c hsc u hu
                  induction c generalizing st with
                  | zero => simp [buildRange] at hu
                  | succ c' ihc =>
                    rcases List.mem_cons.mp hu with rfl | hrest
                    · omega
                    · exact ihc (st + 1) (by omega) hrest
                exact hbr spec.n_d spec.h_sz le_rfl v hrng
              · exact ih (d + 1) (by omega) htl
          · rcases List.mem_cons.mp hv with rfl | htl
            · omega
            · exact ih (d + 1) (by omega) htl
      exact haux 0 spec.n_d (by omega)
    have hmem : (cb.p_idx idx).val ∈ buildBccw spec := by
      rw [listGetOpt_eq_getElem?] at hg0
      exact List.mem_of_getElem? hg0
    have hidx_lt : (cb.p_idx idx).val < spec.n_d + spec.h_sz := hb_lt _ hmem
    dsimp [relabelShiftCB]
    rw [add_zero, hfix_symm _ hidx_lt]
    exact hg0
  · dsimp only [swapAdjASpec]
    intro hh_pos
    have hfix_mk : ∀ (v : ℕ) (hv : v < 7), v < spec.n_d + spec.h_sz → σ ⟨v, hv⟩ = ⟨v, hv⟩ :=
      fun v hv h => hfix ⟨v, hv⟩ h
    obtain ⟨l, hl, hlr_eq, hp1, hp2, hp3⟩ := hV.h_pocket hh_pos
    refine ⟨l, hl, hlr_eq, ?_, ?_, ?_⟩
    · intro hi hhi Tw hsub
      have hfl_fix : σ ⟨l, by omega⟩ = ⟨l, by omega⟩ := hfix_mk _ _ (by omega)
      have hfr_fix : σ ⟨if l + 1 < spec.n_d then l + 1 else 0, nextMod_lt_seven (by omega)⟩ =
          ⟨if l + 1 < spec.n_d then l + 1 else 0, nextMod_lt_seven (by omega)⟩ :=
        hfix_mk _ _ (by split_ifs <;> omega)
      have hh_fix : σ ⟨spec.n_d + hi, by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := hfix_mk _ _ (by omega)
      have hsub' : ({⟨l, by omega⟩, ⟨if l + 1 < spec.n_d then l + 1 else 0, nextMod_lt_seven (by omega)⟩} : Finset (Fin 7)) ⊆
          Tw.image σ := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz2
        · rw [← hfl_fix]; exact Finset.mem_image_of_mem σ (hsub (by simp))
        · rw [Finset.mem_singleton.mp hz2, ← hfr_fix]
          exact Finset.mem_image_of_mem σ (hsub (by simp))
      simp only [relabelS, relabelW, Function.comp_apply, hh_fix, hfl_fix, hfr_fix]
      exact hp1 hi hhi (Tw.image σ) hsub'
    · intro hh_gt1 hi hhi
      obtain ⟨hne1, hne2, hne3, htri⟩ := hp2 hh_gt1 hi hhi
      refine ⟨hne1, hne2, hne3, fun Tw hsub => ?_⟩
      let hm := if hi == 0 then l else (spec.n_d + hi) - 1
      let hp := if hi + 1 == spec.h_sz then (if l + 1 < spec.n_d then l + 1 else 0) else (spec.n_d + hi) + 1
      have hhm_lt : hm < spec.n_d + spec.h_sz := by
        dsimp [hm]; by_cases h0 : hi = 0 <;> simp [h0] <;> omega
      have hhp_lt : hp < spec.n_d + spec.h_sz := by
        dsimp [hp]; by_cases h0 : hi + 1 = spec.h_sz <;> simp [h0]
        · split_ifs <;> omega
        · omega
      have hhm_fix : σ ⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩ = ⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩ :=
        hfix_mk _ _ hhm_lt
      have hhp_fix : σ ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩ = ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩ :=
        hfix_mk _ _ hhp_lt
      have hh_fix : σ ⟨spec.n_d + hi, by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := hfix_mk _ _ (by omega)
      have hsub' : ({⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩, ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩} : Finset (Fin 7)) ⊆
          Tw.image σ := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz2
        · rw [← hhm_fix]; exact Finset.mem_image_of_mem σ (hsub (by simp [hm]))
        · rw [Finset.mem_singleton.mp hz2, ← hhp_fix]
          exact Finset.mem_image_of_mem σ (hsub (by simp [hp]))
      have ht0 := htri (Tw.image σ) hsub'
      simp only [relabelS, relabelW, Function.comp_apply, hh_fix]
      change inOpenTriBool (S ⟨spec.n_d + hi, _⟩) (w (Tw.image σ))
        (S (σ ⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩))
        (S (σ ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩)) = true
      rw [hhm_fix, hhp_fix]
      exact ht0
    · intro hi hhi target ht
      have hh_fix : σ ⟨spec.n_d + hi, by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := hfix_mk _ _ (by omega)
      obtain ⟨hsL, hsR⟩ := hp3 hi hhi target ht
      refine ⟨fun hL => ?_, fun hR => ?_⟩
      · have ht_fix : σ ⟨target, ht⟩ = ⟨target, ht⟩ := hfix_mk _ _ (by omega)
        rw [zWitness_relabelW, hh_fix]
        simp only [relabelS, Function.comp_apply, hh_fix, ht_fix]
        exact hsL hL
      · have ht_fix : σ ⟨target, ht⟩ = ⟨target, ht⟩ := hfix_mk _ _ (by
          rcases hR with h1 | rfl
          · omega
          · split_ifs <;> omega)
        rw [zWitness_relabelW, hh_fix]
        simp only [relabelS, Function.comp_apply, hh_fix, ht_fix]
        exact hsR hR
  · dsimp only [swapAdjASpec]
    intro hnd3 eIdx u_y he_lt hed huy_lt
    have hfix_mk : ∀ (v : ℕ) (hv : v < 7), v < spec.n_d + spec.h_sz → σ ⟨v, hv⟩ = ⟨v, hv⟩ :=
      fun v hv h => hfix ⟨v, hv⟩ h
    dsimp only [swapEdgesAt] at hed ⊢
    rw [listGetOpt_eq_getElem?, List.getElem?_map, List.getElem?_range he_lt] at hed
    dsimp only [Option.map] at hed
    injection hed with hmatch
    let srcIdx := swapNatPair (spec.h_sz + k) (spec.h_sz + k + 1) eIdx
    have hsrc_lt : srcIdx < 7 - spec.n_d := by
      dsimp [srcIdx, swapNatPair]; split_ifs <;> omega
    have hed_src : listGetOpt spec.edges srcIdx = some (some u_y) := by
      cases hg : listGetOpt spec.edges srcIdx with
      | none => rw [hg] at hmatch; nomatch hmatch
      | some v => rw [hg] at hmatch; exact congrArg some hmatch
    have hsigma_e : σ ⟨spec.n_d + eIdx, by omega⟩ = ⟨spec.n_d + srcIdx, by omega⟩ := by
      by_cases he1 : eIdx = spec.h_sz + k
      · have h1 : (⟨spec.n_d + eIdx, by omega⟩ : Fin 7) = a₁ := by ext; dsimp [a₁]; omega
        have hs : srcIdx = spec.h_sz + k + 1 := by dsimp [srcIdx, swapNatPair]; rw [if_pos he1]
        have h2 : (⟨spec.n_d + srcIdx, by omega⟩ : Fin 7) = a₂ := by ext; dsimp [a₂]; omega
        rw [h1, h2]; exact Equiv.swap_apply_left a₁ a₂
      · by_cases he2 : eIdx = spec.h_sz + k + 1
        · have h1 : (⟨spec.n_d + eIdx, by omega⟩ : Fin 7) = a₂ := by ext; dsimp [a₂]; omega
          have hs : srcIdx = spec.h_sz + k := by
            dsimp [srcIdx, swapNatPair]; rw [if_neg he1, if_pos he2]
          have h2 : (⟨spec.n_d + srcIdx, by omega⟩ : Fin 7) = a₁ := by ext; dsimp [a₁]; omega
          rw [h1, h2]; exact Equiv.swap_apply_right a₁ a₂
        · have hs : srcIdx = eIdx := by
            dsimp [srcIdx, swapNatPair]; rw [if_neg he1, if_neg he2]
          have h2 : (⟨spec.n_d + srcIdx, by omega⟩ : Fin 7) = ⟨spec.n_d + eIdx, by omega⟩ := by
            ext; dsimp; omega
          rw [h2]
          exact Equiv.swap_apply_of_ne_of_ne
            (fun e => he1 (by have := congrArg Fin.val e; dsimp [a₁] at this; omega))
            (fun e => he2 (by have := congrArg Fin.val e; dsimp [a₂] at this; omega))
    have hfu_fix : σ ⟨u_y, by omega⟩ = ⟨u_y, by omega⟩ := hfix_mk _ _ (by omega)
    have hfv_fix : σ ⟨if u_y + 1 < spec.n_d then u_y + 1 else 0, nextMod_lt_seven (by omega)⟩ =
        ⟨if u_y + 1 < spec.n_d then u_y + 1 else 0, nextMod_lt_seven (by omega)⟩ :=
      hfix_mk _ _ (by split_ifs <;> omega)
    intro Tw hfu hfv
    have hfu' : (⟨u_y, by omega⟩ : Fin 7) ∈ Tw.image σ := by
      rw [← hfu_fix]; exact Finset.mem_image_of_mem σ hfu
    have hfv' : (⟨if u_y + 1 < spec.n_d then u_y + 1 else 0, nextMod_lt_seven (by omega)⟩ : Fin 7) ∈ Tw.image σ := by
      rw [← hfv_fix]; exact Finset.mem_image_of_mem σ hfv
    simp only [relabelS, relabelW, Function.comp_apply, hsigma_e, hfu_fix, hfv_fix]
    exact hV.h_edges hnd3 srcIdx u_y hsrc_lt hed_src huy_lt (Tw.image σ) hfu' hfv'

/-! ## 4. Generator 2: Cyclic Rotation of `D` (`stepRotD` & `rotateD`) -/

def nextD (n_d u : ℕ) : ℕ :=
  if u + 1 < n_d then u + 1 else 0

def prevD (n_d u : ℕ) : ℕ :=
  if u = 0 then n_d - 1 else u - 1

private lemma prevD_nextD {n_d u : ℕ} (hu : u < n_d) : prevD n_d (nextD n_d u) = u := by
  by_cases h1 : u + 1 < n_d
  · simp [nextD, prevD, h1]
  · simp [nextD, prevD, h1]; omega

private lemma nextD_prevD {n_d u : ℕ} (h2 : 2 ≤ n_d) (hu : u < n_d) : nextD n_d (prevD n_d u) = u := by
  by_cases h0 : u = 0
  · subst h0; simp [prevD, nextD, show ¬ (n_d - 1 + 1 < n_d) by omega]
  · simp [prevD, nextD, h0, show u - 1 + 1 < n_d by omega]; omega

private def rotPerm1 (n_d : ℕ) (h2 : 2 ≤ n_d) (h7 : n_d ≤ 7) : Equiv.Perm (Fin 7) where
  toFun x := if x.val < n_d then ⟨prevD n_d x.val, by dsimp [prevD]; split_ifs <;> omega⟩ else x
  invFun x := if x.val < n_d then ⟨nextD n_d x.val, by dsimp [nextD]; split_ifs <;> omega⟩ else x
  left_inv x := by
    by_cases hx : x.val < n_d
    · have hp : prevD n_d x.val < n_d := by dsimp [prevD]; split_ifs <;> omega
      simp [hx, hp, nextD_prevD h2 hx]
    · simp [hx]
  right_inv x := by
    by_cases hx : x.val < n_d
    · have hn : nextD n_d x.val < n_d := by dsimp [nextD]; split_ifs <;> omega
      simp [hx, hn, prevD_nextD hx]
    · simp [hx]

@[reducible] def rotSpec1 (spec : CaseSpec) : CaseSpec :=
  { spec with
    lr_l := spec.lr_l.map (nextD spec.n_d)
    edges := spec.edges.map (Option.map (nextD spec.n_d)) }

def rotateSpec : ℕ → CaseSpec → CaseSpec
  | 0, spec => spec
  | s + 1, spec => rotateSpec s (rotSpec1 spec)

private def checkRotBccwOne (n_d h_sz : ℕ) (lr_l : Option ℕ) : Bool :=
  let s1 : CaseSpec := { n_d := n_d, h_sz := h_sz, lr_l := lr_l, edges := [], masks := [] }
  let s2 := rotSpec1 s1
  let b1 := buildBccw s1
  let b2 := buildBccw s2
  let N := n_d + h_sz
  let sh := if h_sz > 0 && lr_l == some (n_d - 1) then (N - (h_sz + 1)) % N else (N - 1) % N
  (b1.length == N) && (b2.length == N) &&
  (List.range N).all fun idx =>
    match listGetOpt b2 idx, listGetOpt b1 ((idx + sh) % N) with
    | some v2, some v1 =>
      (v2 < 7) && ((if v2 < n_d then prevD n_d v2 else v2) == v1)
    | _, _ => false

private def checkRotBccwAll : Bool :=
  (List.range 8).all fun n_d =>
    if n_d < 2 then true else
    (List.range (8 - n_d)).all fun h_sz =>
      if n_d + h_sz < 3 then true else
      if h_sz == 0 then checkRotBccwOne n_d 0 none
      else (List.range n_d).all fun l => checkRotBccwOne n_d h_sz (some l)

private lemma checkRotBccwAll_ok : checkRotBccwAll = true := by decide

private lemma checkRotBccwOne_of_valid {n_d h_sz : ℕ} {lr_l : Option ℕ}
    (h2 : 2 ≤ n_d) (htot : n_d + h_sz ≤ 7) (hb3 : 3 ≤ n_d + h_sz)
    (hlr : (h_sz = 0 ∧ lr_l = none) ∨ (h_sz > 0 ∧ ∃ l < n_d, lr_l = some l)) :
    checkRotBccwOne n_d h_sz lr_l = true := by
  have hall := List.all_eq_true.mp checkRotBccwAll_ok n_d (List.mem_range.mpr (by omega))
  simp only [show ¬ (n_d < 2) by omega, ↓reduceIte] at hall
  have hh := List.all_eq_true.mp hall h_sz (List.mem_range.mpr (by omega))
  simp only [show ¬ (n_d + h_sz < 3) by omega, ↓reduceIte] at hh
  rcases hlr with ⟨rfl, rfl⟩ | ⟨hpos, l, hl, rfl⟩
  · simpa using hh
  · simp only [show (h_sz == 0) = false from beq_false_of_ne (by omega)] at hh
    exact List.all_eq_true.mp hh l (List.mem_range.mpr hl)

def EdgesBounded (spec : CaseSpec) : Prop :=
  ∀ eIdx u, listGetOpt spec.edges eIdx = some (some u) → u < spec.n_d

theorem ValidCanonicalInstance.stepRotD {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec)
    (hlr_wf : spec.h_sz = 0 → spec.lr_l = none)
    (hed_wf : EdgesBounded spec) :
    ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
      ValidCanonicalInstance P S' w' (rotSpec1 spec) ∧
      ((rotSpec1 spec).h_sz = 0 → (rotSpec1 spec).lr_l = none) ∧
      EdgesBounded (rotSpec1 spec) := by
  have hnd2 := hV.h_nd_ge2
  have htot := hV.h_tot_le7
  have hbsz3 := hV.h_bsz_ge3
  have hnd7 : spec.n_d ≤ 7 := by omega
  let σ := rotPerm1 spec.n_d hV.h_nd_ge2 hnd7
  have hσ_lt : ∀ x : Fin 7, (σ x).val < spec.n_d ↔ x.val < spec.n_d := by
    intro x; dsimp [σ, rotPerm1]
    split_ifs with hx
    · simp [hx]; dsimp [prevD]; split_ifs <;> omega
    · simp [hx]
  have hσ_fix : ∀ x : Fin 7, spec.n_d ≤ x.val → σ x = x := by
    intro x hx; dsimp [σ, rotPerm1]; rw [if_neg (by omega)]
  have hσ_next : ∀ (u : ℕ) (hu : u < spec.n_d),
      σ ⟨nextD spec.n_d u, by dsimp [nextD]; split_ifs <;> omega⟩ = ⟨u, by omega⟩ := by
    intro u hu
    have hn_lt : nextD spec.n_d u < spec.n_d := by dsimp [nextD]; split_ifs <;> omega
    dsimp [σ, rotPerm1]
    rw [if_pos hn_lt]
    ext; exact prevD_nextD hu
  refine ⟨relabelS σ S, relabelW σ w, {
    hP := shattered_relabel hV.hP σ
    h_nd_ge2 := hV.h_nd_ge2
    h_tot_le7 := hV.h_tot_le7
    h_bsz_ge3 := hV.h_bsz_ge3
    hD_mem := fun x => by
      dsimp only [rotSpec1]
      rw [Finset.mem_sdiff, mem_hullVertices_relabel, mem_certifiedSet_relabel,
          ← Finset.mem_sdiff, hV.hD_mem, hσ_lt]
    hH_mem := fun x => by
      dsimp only [rotSpec1]
      rw [mem_certifiedSet_relabel, hV.hH_mem]
      by_cases hx : x.val < spec.n_d
      · have hs : (σ x).val < spec.n_d := (hσ_lt x).mpr hx
        omega
      · rw [hσ_fix x (by omega)]
    h_cb := ?_
    h_pocket := ?_
    h_edges := ?_
  }, fun hh0 => by dsimp [rotSpec1] at hh0 ⊢; rw [hlr_wf hh0]; rfl, ?_⟩
  · obtain ⟨cb, hlen, hget⟩ := hV.h_cb
    have hlr_disj : (spec.h_sz = 0 ∧ spec.lr_l = none) ∨
        (spec.h_sz > 0 ∧ ∃ l < spec.n_d, spec.lr_l = some l) := by
      by_cases hh0 : spec.h_sz = 0
      · exact Or.inl ⟨hh0, hlr_wf hh0⟩
      · obtain ⟨l, hl, hlr_eq, _⟩ := hV.h_pocket (by omega)
        exact Or.inr ⟨by omega, l, hl, hlr_eq⟩
    have hchk := checkRotBccwOne_of_valid hV.h_nd_ge2 hV.h_tot_le7 hV.h_bsz_ge3 hlr_disj
    unfold checkRotBccwOne at hchk
    dsimp only at hchk
    rcases (Bool.and_eq_true _ _).mp hchk with ⟨hh12, hall_idx⟩
    rcases (Bool.and_eq_true _ _).mp hh12 with ⟨hlen1_b, hlen2_b⟩
    have hlen1 := beq_iff_eq.mp hlen1_b
    have hlen2 := beq_iff_eq.mp hlen2_b
    have hbccw1 : buildBccw { n_d := spec.n_d, h_sz := spec.h_sz, lr_l := spec.lr_l, edges := [], masks := [] } =
        buildBccw spec := rfl
    have hbccw2 : buildBccw (rotSpec1 { n_d := spec.n_d, h_sz := spec.h_sz, lr_l := spec.lr_l, edges := [], masks := [] }) =
        buildBccw (rotSpec1 spec) := rfl
    rw [hbccw1] at hlen1 hall_idx
    rw [hbccw2] at hlen2 hall_idx
    let N := spec.n_d + spec.h_sz
    have hN_eq : N = cb.m + 3 := hlen1.symm.trans hlen
    let sh_nat := if spec.h_sz > 0 && spec.lr_l == some (spec.n_d - 1) then
        (N - (spec.h_sz + 1)) % N else (N - 1) % N
    have hsh_lt : sh_nat < cb.m + 3 := by
      rw [← hN_eq]; dsimp [sh_nat]; split_ifs <;> exact Nat.mod_lt _ (by have := hV.h_bsz_ge3; omega)
    let sh : Fin (cb.m + 3) := ⟨sh_nat, hsh_lt⟩
    refine ⟨relabelShiftCB σ cb sh, hlen2.trans hN_eq, fun idx => ?_⟩
    change Fin (cb.m + 3) at idx
    have hidx_N : idx.val < N := by rw [hN_eq]; exact idx.isLt
    have hi_chk := List.all_eq_true.mp hall_idx idx.val (List.mem_range.mpr hidx_N)
    change (match listGetOpt (buildBccw (rotSpec1 spec)) idx.val,
        listGetOpt (buildBccw spec) ((idx.val + sh_nat) % N) with
      | some v2, some v1 => (v2 < 7) && ((if v2 < spec.n_d then prevD spec.n_d v2 else v2) == v1)
      | _, _ => false) = true at hi_chk
    have hadd_mod : (idx + sh).val = (idx.val + sh_nat) % N := by
      haveI : NeZero (cb.m + 3) := ⟨by omega⟩
      rw [Fin.add_def, hN_eq]
    have hg1 := hget (idx + sh)
    rw [hadd_mod] at hg1
    rw [hg1] at hi_chk
    cases hg2 : listGetOpt (buildBccw (rotSpec1 spec)) idx.val with
    | none => rw [hg2] at hi_chk; exact Bool.noConfusion hi_chk
    | some v2 =>
      rw [hg2] at hi_chk
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi_chk
      rcases hi_chk with ⟨hv2_7, hv_eq⟩
      have hσ_v2 : σ ⟨v2, hv2_7⟩ = cb.p_idx (idx + sh) := by
        ext
        dsimp [σ, rotPerm1]
        split_ifs with hv2_nd
        · simpa [hv2_nd] using hv_eq
        · simpa [hv2_nd] using hv_eq
      dsimp [relabelShiftCB]
      rw [← hσ_v2, σ.symm_apply_apply]
  · dsimp only [rotSpec1]
    intro hh_pos
    have hσ_fix_mk : ∀ (v : ℕ) (hv : v < 7), spec.n_d ≤ v → σ ⟨v, hv⟩ = ⟨v, hv⟩ :=
      fun v hv h => hσ_fix ⟨v, hv⟩ h
    obtain ⟨l, hl, hlr_eq, hp1, hp2, hp3⟩ := hV.h_pocket hh_pos
    let l' := nextD spec.n_d l
    have hl' : l' < spec.n_d := by dsimp [l', nextD]; split_ifs <;> omega
    have hlr'_eq : Option.map (nextD spec.n_d) spec.lr_l = some l' := by
      rw [hlr_eq]; rfl
    let r := nextD spec.n_d l
    let r' := nextD spec.n_d l'
    have hfl_eq : σ ⟨l', by omega⟩ = ⟨l, by omega⟩ := hσ_next l hl
    have hfr_eq : σ ⟨r', by dsimp [r', nextD]; split_ifs <;> omega⟩ =
        ⟨r, by dsimp [r, nextD]; split_ifs <;> omega⟩ := hσ_next l' hl'
    refine ⟨l', hl', hlr'_eq, ?_, ?_, ?_⟩
    · intro hi hhi Tw hsub
      have hh_fix : σ ⟨spec.n_d + hi, by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := hσ_fix_mk _ _ (by omega)
      have hsub' : ({⟨l, by omega⟩, ⟨r, nextMod_lt_seven (by omega)⟩} : Finset (Fin 7)) ⊆ Tw.image σ := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz2
        · rw [← hfl_eq]; exact Finset.mem_image_of_mem σ (hsub (by simp))
        · rw [Finset.mem_singleton.mp hz2, ← hfr_eq]
          exact Finset.mem_image_of_mem σ (hsub (by simp [r', nextD]))
      have ht0 := hp1 hi hhi (Tw.image σ) hsub'
      simp only [relabelS, relabelW, Function.comp_apply, hh_fix, hfl_eq]
      have hr'_eq : (⟨if l' + 1 < spec.n_d then l' + 1 else 0, nextMod_lt_seven (by omega)⟩ : Fin 7) =
          ⟨r', by dsimp [r', nextD]; split_ifs <;> omega⟩ := rfl
      rw [hr'_eq, hfr_eq]
      exact ht0
    · intro hh_gt1 hi hhi
      obtain ⟨hne1, hne2, hne3, htri⟩ := hp2 hh_gt1 hi hhi
      let hm := if hi == 0 then l else (spec.n_d + hi) - 1
      let hp := if hi + 1 == spec.h_sz then r else (spec.n_d + hi) + 1
      let hm' := if hi == 0 then l' else (spec.n_d + hi) - 1
      let hp' := if hi + 1 == spec.h_sz then r' else (spec.n_d + hi) + 1
      have hhm_map : σ ⟨hm', hm_lt_seven hV.h_tot_le7 hl' hhi⟩ = ⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩ := by
        by_cases h0 : hi = 0
        · subst h0; simpa [hm', hm] using hfl_eq
        · have hb : (hi == 0) = false := beq_false_of_ne h0
          simpa [hm', hm, hb] using hσ_fix_mk ((spec.n_d + hi) - 1) (by omega) (by omega)
      have hhp_map : σ ⟨hp', hp_lt_seven hV.h_tot_le7 hhi⟩ = ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩ := by
        by_cases h0 : hi + 1 = spec.h_sz
        · have hb : (hi + 1 == spec.h_sz) = true := beq_iff_eq.mpr h0
          simpa [hp', hp, hb] using hfr_eq
        · have hb : (hi + 1 == spec.h_sz) = false := beq_false_of_ne h0
          simpa [hp', hp, hb] using hσ_fix_mk ((spec.n_d + hi) + 1) (by omega) (by omega)
      have hh_fix : σ ⟨spec.n_d + hi, by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := hσ_fix_mk _ _ (by omega)
      have hne1' : (⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩ : Fin 7) ≠ ⟨spec.n_d + hi, by omega⟩ := by
        simpa [hm] using hne1
      have hne2' : (⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩ : Fin 7) ≠ ⟨spec.n_d + hi, by omega⟩ := by
        simpa [hp, r, nextD] using hne2
      have hne3' : (⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩ : Fin 7) ≠ ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩ := by
        simpa [hm, hp, r, nextD] using hne3
      refine ⟨fun e => hne1' (by rw [← hhm_map, ← hh_fix]; exact congrArg σ (by simpa [hm'] using e)),
              fun e => hne2' (by rw [← hhp_map, ← hh_fix]; exact congrArg σ (by simpa [hp', r', nextD] using e)),
              fun e => hne3' (by rw [← hhm_map, ← hhp_map]; exact congrArg σ (by simpa [hm', hp', r', nextD] using e)),
              fun Tw hsub => ?_⟩
      have hsub' : ({⟨hm, hm_lt_seven hV.h_tot_le7 hl hhi⟩, ⟨hp, hp_lt_seven hV.h_tot_le7 hhi⟩} : Finset (Fin 7)) ⊆
          Tw.image σ := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz2
        · rw [← hhm_map]; exact Finset.mem_image_of_mem σ (hsub (by simp [hm']))
        · rw [Finset.mem_singleton.mp hz2, ← hhp_map]
          exact Finset.mem_image_of_mem σ (hsub (by
            apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]; ext; rfl))
      have ht0 := htri (Tw.image σ) (by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz2
        · exact hsub' (by simp [hm])
        · rw [Finset.mem_singleton.mp hz2]
          exact hsub' (by apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]; ext; rfl))
      simp only [relabelS, relabelW, Function.comp_apply, hh_fix]
      change inOpenTriBool (S ⟨spec.n_d + hi, _⟩) (w (Tw.image σ))
        (S (σ ⟨hm', hm_lt_seven hV.h_tot_le7 hl' hhi⟩))
        (S (σ ⟨hp', hp_lt_seven hV.h_tot_le7 hhi⟩)) = true
      rw [hhm_map, hhp_map]
      exact ht0
    · intro hi hhi target ht
      have hh_fix : σ ⟨spec.n_d + hi, by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := hσ_fix_mk _ _ (by omega)
      refine ⟨fun hL => ?_, fun hR => ?_⟩
      · rcases hL with hmid | rfl
        · have ht_fix : σ ⟨target, ht⟩ = ⟨target, ht⟩ := hσ_fix_mk _ _ hmid.1
          rw [zWitness_relabelW, hh_fix]
          simp only [relabelS, Function.comp_apply, hh_fix, ht_fix]
          exact (hp3 hi hhi target ht).1 (Or.inl hmid)
        · rw [zWitness_relabelW, hh_fix]
          simp only [relabelS, Function.comp_apply, hh_fix, hfl_eq]
          exact (hp3 hi hhi l (by omega)).1 (Or.inr rfl)
      · rcases hR with hmid | rfl
        · have ht_fix : σ ⟨target, ht⟩ = ⟨target, ht⟩ := hσ_fix_mk _ _ (by omega)
          rw [zWitness_relabelW, hh_fix]
          simp only [relabelS, Function.comp_apply, hh_fix, ht_fix]
          exact (hp3 hi hhi target ht).2 (Or.inl hmid)
        · rw [zWitness_relabelW, hh_fix]
          have hr'_fin : (⟨if l' + 1 < spec.n_d then l' + 1 else 0, ht⟩ : Fin 7) =
              ⟨r', by dsimp [r', nextD]; split_ifs <;> omega⟩ := by ext; rfl
          simp only [relabelS, Function.comp_apply, hh_fix]
          rw [hr'_fin, hfr_eq]
          exact (hp3 hi hhi r (by dsimp [r, nextD]; split_ifs <;> omega)).2 (Or.inr rfl)
  · dsimp only [rotSpec1]
    intro hnd3 eIdx u' he_lt hed hu'_lt
    have hσ_fix_mk : ∀ (v : ℕ) (hv : v < 7), spec.n_d ≤ v → σ ⟨v, hv⟩ = ⟨v, hv⟩ :=
      fun v hv h => hσ_fix ⟨v, hv⟩ h
    try dsimp only
    rw [listGetOpt_eq_getElem?, List.getElem?_map] at hed
    cases hg : spec.edges[eIdx]? with
    | none => rw [hg] at hed; nomatch hed
    | some opt_u =>
      rw [hg] at hed; dsimp only [Option.map] at hed
      injection hed with hopt
      cases opt_u with
      | none => nomatch hopt
      | some u =>
        injection hopt with hu'_eq
        have hed0 : listGetOpt spec.edges eIdx = some (some u) := by
          rwa [listGetOpt_eq_getElem?]
        have hu_lt : u < spec.n_d := hed_wf eIdx u hed0
        have hfu_map : σ ⟨u', by omega⟩ = ⟨u, by omega⟩ := by
          have := hσ_next u hu_lt
          simpa [hu'_eq] using this
        have hfv_map : σ ⟨nextD spec.n_d u', nextMod_lt_seven (by omega)⟩ =
            ⟨nextD spec.n_d u, nextMod_lt_seven (by omega)⟩ := by
          have := hσ_next u' hu'_lt
          simpa [← hu'_eq] using this
        have he_fix : σ ⟨spec.n_d + eIdx, by omega⟩ = ⟨spec.n_d + eIdx, by omega⟩ := hσ_fix_mk _ _ (by omega)
        intro Tw hfu hfv
        have hfu0 : (⟨u, by omega⟩ : Fin 7) ∈ Tw.image σ := by
          rw [← hfu_map]; exact Finset.mem_image_of_mem σ hfu
        have hfv0 : (⟨nextD spec.n_d u, nextMod_lt_seven (by omega)⟩ : Fin 7) ∈ Tw.image σ := by
          rw [← hfv_map]; exact Finset.mem_image_of_mem σ hfv
        simp only [relabelS, relabelW, Function.comp_apply, he_fix, hfu_map]
        have hfv_fin : (⟨if u' + 1 < spec.n_d then u' + 1 else 0, nextMod_lt_seven (by omega)⟩ : Fin 7) =
            ⟨nextD spec.n_d u', nextMod_lt_seven (by omega)⟩ := rfl
        rw [hfv_fin, hfv_map]
        exact hV.h_edges hnd3 eIdx u he_lt hed0 hu_lt (Tw.image σ) hfu0 hfv0
  · dsimp only [rotSpec1]
    intro eIdx u' hed
    rw [listGetOpt_eq_getElem?, List.getElem?_map] at hed
    cases hg : spec.edges[eIdx]? with
    | none => rw [hg] at hed; nomatch hed
    | some opt_u =>
      rw [hg] at hed; dsimp only [Option.map] at hed
      injection hed with hopt
      cases opt_u with
      | none => nomatch hopt
      | some u =>
        injection hopt with hu'_eq
        subst hu'_eq
        have := hV.h_nd_ge2
        dsimp [nextD]; split_ifs <;> omega

theorem ValidCanonicalInstance.rotateD {P : Set (ℝ × ℝ)} :
    ∀ (steps : ℕ) {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec},
      ValidCanonicalInstance P S w spec →
      (spec.h_sz = 0 → spec.lr_l = none) →
      EdgesBounded spec →
      ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
        ValidCanonicalInstance P S' w' (rotateSpec steps spec)
  | 0, S, w, _, hV, _, _ => ⟨S, w, hV⟩
  | s + 1, _, _, _, hV, hlr_wf, hed_wf => by
    obtain ⟨S₁, w₁, hV₁, hlr₁, hed₁⟩ := hV.stepRotD hlr_wf hed_wf
    exact ValidCanonicalInstance.rotateD s hV₁ hlr₁ hed₁

def applySwapsASpec : List ℕ → CaseSpec → CaseSpec
  | [], spec => spec
  | k :: ks, spec => applySwapsASpec ks (swapAdjASpec spec k)

theorem ValidCanonicalInstance.applySwapsA {P : Set (ℝ × ℝ)} :
    ∀ (swaps : List ℕ) {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec},
      ValidCanonicalInstance P S w spec →
      (∀ k ∈ swaps, spec.n_d + spec.h_sz + k + 1 < 7) →
      ∃ (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
        ValidCanonicalInstance P S' w' (applySwapsASpec swaps spec)
  | [], S, w, _, hV, _ => ⟨S, w, hV⟩
  | k :: ks, _, _, spec, hV, hks => by
    have hk : spec.n_d + spec.h_sz + k + 1 < 7 := hks k (List.mem_cons_self)
    obtain ⟨S₁, w₁, hV₁⟩ := hV.swapAdjA k hk
    exact ValidCanonicalInstance.applySwapsA ks hV₁ (fun j hj => hks j (List.mem_cons_of_mem k hj))

/-! ## 5. Generator 3: Dihedral Reflection on `lr_l = none` (`h_sz = 0`) or `some 0` (`h_sz > 0`) -/

def reflIdxFun (n_d h_sz x : ℕ) : ℕ :=
  if x < n_d then
    if x = 0 then 1 else if x = 1 then 0 else n_d + 1 - x
  else if x < n_d + h_sz then
    n_d + (h_sz - 1 - (x - n_d))
  else
    x

private lemma reflIdxFun_lt7 {n_d h_sz x : ℕ} (h2 : 2 ≤ n_d) (htot : n_d + h_sz ≤ 7) (hx : x < 7) :
    reflIdxFun n_d h_sz x < 7 := by
  dsimp [reflIdxFun]; split_ifs <;> omega

private lemma reflIdxFun_invol {n_d h_sz x : ℕ} (h2 : 2 ≤ n_d) (_htot : n_d + h_sz ≤ 7) (hx : x < 7) :
    reflIdxFun n_d h_sz (reflIdxFun n_d h_sz x) = x := by
  by_cases hx1 : x < n_d
  · by_cases h0 : x = 0
    · simp [reflIdxFun, h0, show 0 < n_d by omega, show 1 < n_d by omega]
    · by_cases h1 : x = 1
      · simp [reflIdxFun, h1, show 1 < n_d by omega, show 0 < n_d by omega]
      · have hlt : n_d + 1 - x < n_d := by omega
        have hne0 : n_d + 1 - x ≠ 0 := by omega
        have hne1 : n_d + 1 - x ≠ 1 := by omega
        simp [reflIdxFun, hx1, h0, h1, hlt, hne0, hne1]; omega
  · by_cases hx2 : x < n_d + h_sz
    · have hge : ¬ (n_d + (h_sz - 1 - (x - n_d)) < n_d) := by omega
      have hlt : n_d + (h_sz - 1 - (x - n_d)) < n_d + h_sz := by omega
      simp [reflIdxFun, hx1, hx2, hge, hlt]; omega
    · simp [reflIdxFun, hx1, hx2]

private def reflPerm (n_d h_sz : ℕ) (h2 : 2 ≤ n_d) (htot : n_d + h_sz ≤ 7) : Equiv.Perm (Fin 7) where
  toFun x := ⟨reflIdxFun n_d h_sz x.val, reflIdxFun_lt7 h2 htot x.isLt⟩
  invFun x := ⟨reflIdxFun n_d h_sz x.val, reflIdxFun_lt7 h2 htot x.isLt⟩
  left_inv x := by ext; exact reflIdxFun_invol h2 htot x.isLt
  right_inv x := by ext; exact reflIdxFun_invol h2 htot x.isLt

def reflEdgeIdx (h_sz i : ℕ) : ℕ :=
  if i < h_sz then h_sz - 1 - i else i

def reflEdges (n_d h_sz : ℕ) (edges : List (Option ℕ)) : List (Option ℕ) :=
  (List.range (7 - n_d)).map fun i =>
    match listGetOpt edges (reflEdgeIdx h_sz i) with
    | some (some u) => some ((n_d - u) % n_d)
    | _ => none

@[reducible] def reflSpec (spec : CaseSpec) : CaseSpec :=
  { spec with edges := reflEdges spec.n_d spec.h_sz spec.edges }

private def checkReflBccwOne (n_d h_sz : ℕ) : Bool :=
  let lr0 := if h_sz = 0 then none else some 0
  let s1 : CaseSpec := { n_d := n_d, h_sz := h_sz, lr_l := lr0, edges := [], masks := [] }
  let b := buildBccw s1
  let N := n_d + h_sz
  let c := (h_sz + 1) % N
  (b.length == N) &&
  (List.range N).all fun idx =>
    let ridx := (c + N - idx) % N
    match listGetOpt b idx, listGetOpt b ridx with
    | some v, some vr => (v < 7) && (reflIdxFun n_d h_sz v == vr)
    | _, _ => false

private def checkReflBccwAll : Bool :=
  (List.range 8).all fun n_d =>
    if n_d < 2 then true else
    (List.range (8 - n_d)).all fun h_sz =>
      if n_d + h_sz < 3 then true else checkReflBccwOne n_d h_sz

private lemma checkReflBccwAll_ok : checkReflBccwAll = true := by decide

private lemma checkReflBccwOne_of_valid {n_d h_sz : ℕ}
    (h2 : 2 ≤ n_d) (htot : n_d + h_sz ≤ 7) (hb3 : 3 ≤ n_d + h_sz) :
    checkReflBccwOne n_d h_sz = true := by
  have hall := List.all_eq_true.mp checkReflBccwAll_ok n_d (List.mem_range.mpr (by omega))
  simp only [show ¬ (n_d < 2) by omega, ↓reduceIte] at hall
  have hh := List.all_eq_true.mp hall h_sz (List.mem_range.mpr (by omega))
  simpa [show ¬ (n_d + h_sz < 3) by omega] using hh

theorem ValidCanonicalInstance.reflD {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ}
    {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec)
    (hlr0 : spec.lr_l = (if spec.h_sz = 0 then none else some 0))
    (hed_wf : EdgesBounded spec) :
    ∃ (P' : Set (ℝ × ℝ)) (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
      ValidCanonicalInstance P' S' w' (reflSpec spec) ∧
      ((reflSpec spec).h_sz = 0 → (reflSpec spec).lr_l = none) ∧
      EdgesBounded (reflSpec spec) := by
  have hnd2 := hV.h_nd_ge2
  have htot := hV.h_tot_le7
  have hbsz3 := hV.h_bsz_ge3
  let σ := reflPerm spec.n_d spec.h_sz hnd2 htot
  let P' := reflX '' P
  let S₁ := relabelS σ S
  let w₁ := relabelW σ w
  let S' := reflX ∘ S₁
  let w' := reflX ∘ w₁
  have hP₁ : ShatteredSimplePolygon P S₁ w₁ := shattered_relabel hV.hP σ
  have hP' : ShatteredSimplePolygon P' S' w' := shattered_reflX hP₁
  have hσ_D : ∀ x : Fin 7, (σ x).val < spec.n_d ↔ x.val < spec.n_d := by
    intro x; change reflIdxFun spec.n_d spec.h_sz x.val < spec.n_d ↔ x.val < spec.n_d
    dsimp [reflIdxFun]; split_ifs <;> omega
  have hσ_H : ∀ x : Fin 7,
      (spec.n_d ≤ (σ x).val ∧ (σ x).val < spec.n_d + spec.h_sz) ↔
      (spec.n_d ≤ x.val ∧ x.val < spec.n_d + spec.h_sz) := by
    intro x
    change (spec.n_d ≤ reflIdxFun spec.n_d spec.h_sz x.val ∧
            reflIdxFun spec.n_d spec.h_sz x.val < spec.n_d + spec.h_sz) ↔ _
    dsimp [reflIdxFun]; split_ifs <;> omega
  refine ⟨P', S', w', {
    hP := hP'
    h_nd_ge2 := hV.h_nd_ge2
    h_tot_le7 := hV.h_tot_le7
    h_bsz_ge3 := hV.h_bsz_ge3
    hD_mem := fun x => by
      dsimp only [P', S', w', reflSpec]
      rw [hullVertices_reflX, certifiedSet_reflX]
      dsimp [S₁, w₁]
      rw [Finset.mem_sdiff, mem_hullVertices_relabel, mem_certifiedSet_relabel,
          ← Finset.mem_sdiff, hV.hD_mem, hσ_D]
    hH_mem := fun x => by
      dsimp only [P', S', w', reflSpec]
      rw [certifiedSet_reflX]
      dsimp [S₁, w₁]
      rw [mem_certifiedSet_relabel, hV.hH_mem, hσ_H]
    h_cb := ?_
    h_pocket := ?_
    h_edges := ?_
  }, fun hh0 => by dsimp only [reflSpec] at hh0 ⊢; rw [hlr0, if_pos hh0], ?_⟩
  · obtain ⟨cb, hlen, hget⟩ := hV.h_cb
    have hchk := checkReflBccwOne_of_valid hnd2 htot hbsz3
    unfold checkReflBccwOne at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨hlen0, hall_idx⟩
    let sp0 : CaseSpec := { n_d := spec.n_d, h_sz := spec.h_sz, lr_l := if spec.h_sz = 0 then none else some 0, edges := [], masks := [] }
    have hbccw0 : buildBccw sp0 = buildBccw spec := by
      unfold buildBccw; dsimp [sp0]; rw [hlr0.symm]
    have hbccw_refl : buildBccw (reflSpec spec) = buildBccw spec := rfl
    change (buildBccw sp0).length = spec.n_d + spec.h_sz at hlen0
    rw [hbccw0] at hlen0
    let N := spec.n_d + spec.h_sz
    have hN_eq : N = cb.m + 3 := hlen0.symm.trans hlen
    let c_nat := (spec.h_sz + 1) % N
    have hc_lt : c_nat < cb.m + 3 := by
      rw [← hN_eq]; exact Nat.mod_lt _ (by have := hV.h_bsz_ge3; omega)
    let c : Fin (cb.m + 3) := ⟨c_nat, hc_lt⟩
    refine ⟨reflRevCB σ cb c, hbccw_refl ▸ hlen, fun idx => ?_⟩
    change Fin (cb.m + 3) at idx
    rw [hbccw_refl]
    have hidx_N : idx.val < N := by rw [hN_eq]; exact idx.isLt
    have hi_chk := List.all_eq_true.mp hall_idx idx.val (List.mem_range.mpr hidx_N)
    change (match listGetOpt (buildBccw sp0) idx.val,
        listGetOpt (buildBccw sp0) ((c_nat + N - idx.val) % N) with
      | some v, some vr => (v < 7) && (reflIdxFun spec.n_d spec.h_sz v == vr)
      | _, _ => false) = true at hi_chk
    rw [hbccw0] at hi_chk
    have hsub_mod : (c - idx).val = (c_nat + N - idx.val) % N := by
      let iv : ℕ := idx.val
      have hiv : iv < N := hidx_N
      change ((cb.m + 3 - iv) + c_nat) % (cb.m + 3) = (c_nat + N - iv) % N
      rw [← hN_eq]
      congr 2; omega
    have hg_rev := hget (c - idx)
    rw [hsub_mod] at hg_rev
    rw [hg_rev] at hi_chk
    cases hg_cur : listGetOpt (buildBccw spec) idx.val with
    | none => rw [hg_cur] at hi_chk; exact Bool.noConfusion hi_chk
    | some v =>
      rw [hg_cur] at hi_chk
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hi_chk
      rcases hi_chk with ⟨hv_7, hv_eq⟩
      have hσ_v : σ ⟨v, hv_7⟩ = cb.p_idx (c - idx) := by
        ext; exact hv_eq
      dsimp [reflRevCB]
      rw [← hσ_v, σ.symm_apply_apply]
  · dsimp only [reflSpec]
    intro hh_pos
    obtain ⟨l, hl, hlr_eq, hp1, hp2, hp3⟩ := hV.h_pocket hh_pos
    have hl0 : l = 0 := by
      rw [hlr0, if_neg (by omega)] at hlr_eq
      exact Option.some.inj hlr_eq.symm
    subst hl0
    have hr1 : (if 0 + 1 < spec.n_d then 0 + 1 else 0) = 1 := if_pos (by omega)
    have hlr'_eq : spec.lr_l = some 0 := by
      rw [hlr0, if_neg (by omega)]
    have hfl_ne_fr : (0 : Fin 7) ≠ (1 : Fin 7) := by decide
    have hσ_fl : σ 0 = 1 := by
      ext; change reflIdxFun spec.n_d spec.h_sz 0 = 1
      dsimp [reflIdxFun]; rw [if_pos (by omega)]
    have hσ_fr : σ 1 = 0 := by
      ext; change reflIdxFun spec.n_d spec.h_sz 1 = 0
      dsimp [reflIdxFun]; rw [if_pos (by omega)]
    refine ⟨0, by omega, hlr'_eq, ?_, ?_, ?_⟩
    · intro hi' hhi' Tw hsub
      let hi := spec.h_sz - 1 - hi'
      have hhi : hi < spec.h_sz := by omega
      have hσ_h : σ ⟨spec.n_d + hi', by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := by
        ext; change reflIdxFun spec.n_d spec.h_sz (spec.n_d + hi') = spec.n_d + hi
        dsimp [reflIdxFun]; split_ifs <;> omega
      have hsub' : ({(0 : Fin 7), (1 : Fin 7)} : Finset (Fin 7)) ⊆ Tw.image σ := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz2
        · rw [← hσ_fr]
          exact Finset.mem_image_of_mem σ (hsub (by
            apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]; ext; simp [hr1]))
        · rw [Finset.mem_singleton.mp hz2, ← hσ_fl]
          exact Finset.mem_image_of_mem σ (hsub (by simp))
      have ht0 : inOpenTriBool (S ⟨spec.n_d + hi, by omega⟩) (w (Tw.image σ)) (S 0) (S 1) = true := by
        have := hp1 hi hhi (Tw.image σ) (by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz2
          · exact hsub' (by simp)
          · rw [Finset.mem_singleton.mp hz2]
            exact hsub' (by apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]; ext; simp [hr1]))
        simpa [hr1] using this
      have ht_sw : inOpenTriBool (S ⟨spec.n_d + hi, by omega⟩) (w (Tw.image σ)) (S 1) (S 0) = true :=
        inOpenTriBool_swap_endpoints hV.hP
          (fun e => by have := congrArg Fin.val e; simp at this; omega)
          (fun e => by have := congrArg Fin.val e; simp at this; omega)
          hfl_ne_fr (Tw.image σ) ht0
      have ht_refl : inOpenTriBool
          (reflX (S ⟨spec.n_d + hi, by omega⟩))
          (reflX (w (Tw.image σ)))
          (reflX (S 1)) (reflX (S 0)) = true :=
        inOpenTriBool_reflX
          (orient_w_S_S_ne hV.hP _ (fun e => by have := congrArg Fin.val e; simp at this; omega))
          (orient_S_S_S_ne hV.hP hfl_ne_fr.symm
            (fun e => by have := congrArg Fin.val e; simp at this; omega)
            (fun e => by have := congrArg Fin.val e; simp at this; omega))
          (orient_S_w_S_ne hV.hP (fun e => by have := congrArg Fin.val e; simp at this; omega) _)
          ht_sw
      have h0_eq : (⟨0, by omega⟩ : Fin 7) = 0 := rfl
      have h1_eq : (⟨if 0 + 1 < spec.n_d then 0 + 1 else 0, nextMod_lt_seven (by omega)⟩ : Fin 7) = 1 := by
        ext; simp [hr1]
      rw [h0_eq, h1_eq]
      simpa [S', w', S₁, w₁, relabelS, relabelW, hσ_h, hσ_fl, hσ_fr] using ht_refl
    · intro hh_gt1 hi' hhi'
      let hi := spec.h_sz - 1 - hi'
      have hhi : hi < spec.h_sz := by omega
      obtain ⟨hne1, hne2, hne3, htri⟩ := hp2 hh_gt1 hi hhi
      let hm := if hi == 0 then 0 else (spec.n_d + hi) - 1
      let hp := if hi + 1 == spec.h_sz then 1 else (spec.n_d + hi) + 1
      let hm' := if hi' == 0 then 0 else (spec.n_d + hi') - 1
      let hp' := if hi' + 1 == spec.h_sz then 1 else (spec.n_d + hi') + 1
      have hhp_lt : hp < 7 := by dsimp [hp]; by_cases h0 : hi + 1 = spec.h_sz <;> simp [h0] <;> omega
      have hhp'_lt : hp' < 7 := by dsimp [hp']; by_cases h0 : hi' + 1 = spec.h_sz <;> simp [h0] <;> omega
      have hσ_h : σ ⟨spec.n_d + hi', by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := by
        ext; change reflIdxFun spec.n_d spec.h_sz (spec.n_d + hi') = spec.n_d + hi
        dsimp [reflIdxFun]; split_ifs <;> omega
      have hσ_hm' : σ ⟨hm', hm_lt_seven hV.h_tot_le7 (by omega) hhi'⟩ = ⟨hp, hhp_lt⟩ := by
        ext
        change reflIdxFun spec.n_d spec.h_sz hm' = hp
        dsimp [reflIdxFun, hm', hp]
        by_cases h0 : hi' = 0
        · subst h0
          have hhi_end : hi + 1 = spec.h_sz := by omega
          simp [hhi_end, show 0 < spec.n_d by omega]
        · have hhi_not_end : hi + 1 ≠ spec.h_sz := by omega
          simp only [beq_false_of_ne h0, beq_false_of_ne hhi_not_end, ↓reduceIte, Bool.false_eq_true]
          split_ifs <;> omega
      have hσ_hp' : σ ⟨hp', hhp'_lt⟩ = ⟨hm, hm_lt_seven hV.h_tot_le7 (by omega) hhi⟩ := by
        ext
        change reflIdxFun spec.n_d spec.h_sz hp' = hm
        dsimp [reflIdxFun, hp', hm]
        by_cases h0 : hi' + 1 = spec.h_sz
        · have hhi0 : hi = 0 := by omega
          simp [h0, hhi0, show 1 < spec.n_d by omega]
        · have hhi_ne0 : hi ≠ 0 := by omega
          simp only [beq_false_of_ne h0, beq_false_of_ne hhi_ne0, ↓reduceIte, Bool.false_eq_true]
          split_ifs <;> omega
      let fhm : Fin 7 := ⟨hm, hm_lt_seven hV.h_tot_le7 (by omega) hhi⟩
      let fhp : Fin 7 := ⟨hp, hhp_lt⟩
      have hne1' : fhm ≠ ⟨spec.n_d + hi, by omega⟩ := by simpa [fhm, hm] using hne1
      have hne2' : fhp ≠ ⟨spec.n_d + hi, by omega⟩ := by simpa [fhp, hp, hr1] using hne2
      have hne3' : fhm ≠ fhp := by simpa [fhm, fhp, hm, hp, hr1] using hne3
      refine ⟨?_, ?_, ?_, fun Tw hsub => ?_⟩
      · intro e
        have := congrArg σ e
        rw [hσ_hm', hσ_h] at this
        exact hne2' this
      · intro e
        have := congrArg σ e
        rw [show (⟨if hi' + 1 == spec.h_sz then if 0 + 1 < spec.n_d then 0 + 1 else 0 else (spec.n_d + hi') + 1,
            hp_lt_seven hV.h_tot_le7 hhi'⟩ : Fin 7) = ⟨hp', hhp'_lt⟩ by ext; simp [hp', hr1]] at this
        rw [hσ_hp', hσ_h] at this
        exact hne1' this
      · intro e
        have := congrArg σ e
        rw [show (⟨if hi' + 1 == spec.h_sz then if 0 + 1 < spec.n_d then 0 + 1 else 0 else (spec.n_d + hi') + 1,
            hp_lt_seven hV.h_tot_le7 hhi'⟩ : Fin 7) = ⟨hp', hhp'_lt⟩ by ext; simp [hp', hr1]] at this
        rw [hσ_hm', hσ_hp'] at this
        exact hne3' this.symm
      · have hsub' : ({fhm, fhp} : Finset (Fin 7)) ⊆ Tw.image σ := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz2
          · dsimp only [fhm]; rw [← hσ_hp']
            exact Finset.mem_image_of_mem σ (hsub (by
              apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]; ext; simp [hp', hr1]))
          · rw [Finset.mem_singleton.mp hz2]
            dsimp only [fhp]; rw [← hσ_hm']
            exact Finset.mem_image_of_mem σ (hsub (by
              rw [Finset.mem_insert]; left; ext; rfl))
        have ht0 : inOpenTriBool (S ⟨spec.n_d + hi, by omega⟩) (w (Tw.image σ)) (S fhm) (S fhp) = true := by
          have := htri (Tw.image σ) (by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz2
            · exact hsub' (by rw [Finset.mem_insert]; left; ext; rfl)
            · rw [Finset.mem_singleton.mp hz2]
              exact hsub' (by apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]; ext; simp [fhp, hp, hr1]))
          simpa [fhm, fhp, hm, hp, hr1] using this
        have ht_sw : inOpenTriBool (S ⟨spec.n_d + hi, by omega⟩) (w (Tw.image σ)) (S fhp) (S fhm) = true :=
          inOpenTriBool_swap_endpoints hV.hP hne1'.symm hne2'.symm hne3' (Tw.image σ) ht0
        have ht_refl : inOpenTriBool
            (reflX (S ⟨spec.n_d + hi, by omega⟩))
            (reflX (w (Tw.image σ)))
            (reflX (S fhp)) (reflX (S fhm)) = true :=
          inOpenTriBool_reflX
            (orient_w_S_S_ne hV.hP _ hne2')
            (orient_S_S_S_ne hV.hP hne3'.symm hne1' hne2')
            (orient_S_w_S_ne hV.hP hne1' _)
            ht_sw
        have hhm'_eq : (⟨if hi' == 0 then 0 else (spec.n_d + hi') - 1,
            hm_lt_seven hV.h_tot_le7 (by omega) hhi'⟩ : Fin 7) =
            ⟨hm', hm_lt_seven hV.h_tot_le7 (by omega) hhi'⟩ := by ext; rfl
        have hhp'_eq : (⟨if hi' + 1 == spec.h_sz then if 0 + 1 < spec.n_d then 0 + 1 else 0 else (spec.n_d + hi') + 1,
            hp_lt_seven hV.h_tot_le7 hhi'⟩ : Fin 7) =
            ⟨hp', hhp'_lt⟩ := by
          ext; simp [hp', hr1]
        try dsimp only
        rw [hhm'_eq, hhp'_eq]
        simp only [S', w', S₁, w₁, Function.comp_apply, relabelS, relabelW, hσ_h, hσ_hm', hσ_hp']
        exact ht_refl
    · intro hi' hhi' target' ht'
      let hi := spec.h_sz - 1 - hi'
      have hhi : hi < spec.h_sz := by omega
      have hσ_h : σ ⟨spec.n_d + hi', by omega⟩ = ⟨spec.n_d + hi, by omega⟩ := by
        ext; change reflIdxFun spec.n_d spec.h_sz (spec.n_d + hi') = spec.n_d + hi
        dsimp [reflIdxFun]; split_ifs <;> omega
      have hzh_eq : PolygonCore.zWitness w' ⟨spec.n_d + hi', by omega⟩ =
          reflX (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩) := by
        change reflX (PolygonCore.zWitness w₁ ⟨spec.n_d + hi', by omega⟩) = _
        rw [zWitness_relabelW, hσ_h]
      let ft : Fin 7 := σ ⟨target', ht'⟩
      refine ⟨fun hL => ?_, fun hR => ?_⟩
      · have hft_R : (spec.n_d + hi < ft.val ∧ ft.val < spec.n_d + spec.h_sz) ∨ ft.val = 1 := by
          change (spec.n_d + hi < reflIdxFun spec.n_d spec.h_sz target' ∧
                  reflIdxFun spec.n_d spec.h_sz target' < spec.n_d + spec.h_sz) ∨
                 reflIdxFun spec.n_d spec.h_sz target' = 1
          dsimp [reflIdxFun]; split_ifs <;> omega
        have h_ne : ft ≠ ⟨spec.n_d + hi, by omega⟩ := by
          intro e
          have hev : ft.val = spec.n_d + hi := congrArg Fin.val e
          rcases hft_R with h1 | h2 <;> omega
        have hor0 : orientSign (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩)
            (S ⟨spec.n_d + hi, by omega⟩) (S ft) = false := by
          have := (hp3 hi hhi ft.val ft.isLt).2
          rw [hr1] at this
          exact this hft_R
        have hnz : orient2D (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩)
            (S ⟨spec.n_d + hi, by omega⟩) (S ft) ≠ 0 :=
          orient_w_S_S_ne hV.hP (Finset.univ.erase _) h_ne.symm
        rw [hzh_eq]
        change orientSign (reflX (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩))
            (reflX (S (σ ⟨spec.n_d + hi', by omega⟩))) (reflX (S ft)) = true
        rw [hσ_h, orientSign_reflX hnz, hor0]
        rfl
      · have hR' : (spec.n_d + hi' < target' ∧ target' < spec.n_d + spec.h_sz) ∨ target' = 1 := by
          simpa [hr1] using hR
        have hft_L : (spec.n_d ≤ ft.val ∧ ft.val < spec.n_d + hi) ∨ ft.val = 0 := by
          change (spec.n_d ≤ reflIdxFun spec.n_d spec.h_sz target' ∧
                  reflIdxFun spec.n_d spec.h_sz target' < spec.n_d + hi) ∨
                 reflIdxFun spec.n_d spec.h_sz target' = 0
          dsimp [reflIdxFun]; split_ifs <;> omega
        have h_ne : ft ≠ ⟨spec.n_d + hi, by omega⟩ := by
          intro e
          have hev : ft.val = spec.n_d + hi := congrArg Fin.val e
          rcases hft_L with h1 | h2 <;> omega
        have hor0 : orientSign (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩)
            (S ⟨spec.n_d + hi, by omega⟩) (S ft) = true :=
          (hp3 hi hhi ft.val ft.isLt).1 hft_L
        have hnz : orient2D (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩)
            (S ⟨spec.n_d + hi, by omega⟩) (S ft) ≠ 0 :=
          orient_w_S_S_ne hV.hP (Finset.univ.erase _) h_ne.symm
        rw [hzh_eq]
        change orientSign (reflX (PolygonCore.zWitness w ⟨spec.n_d + hi, by omega⟩))
            (reflX (S (σ ⟨spec.n_d + hi', by omega⟩))) (reflX (S ft)) = false
        rw [hσ_h, orientSign_reflX hnz, hor0]
        rfl
  · dsimp only [reflSpec]
    intro hnd3 eIdx' u' he'_lt hed hu'_lt
    dsimp only [reflEdges] at hed ⊢
    rw [listGetOpt_eq_getElem?, List.getElem?_map, List.getElem?_range he'_lt] at hed
    dsimp only [Option.map] at hed
    injection hed with hmatch
    let eIdx := reflEdgeIdx spec.h_sz eIdx'
    have he_lt : eIdx < 7 - spec.n_d := by
      dsimp [eIdx, reflEdgeIdx]; split_ifs <;> omega
    cases hg : listGetOpt spec.edges eIdx with
    | none => rw [hg] at hmatch; nomatch hmatch
    | some opt_u =>
      rw [hg] at hmatch
      cases opt_u with
      | none => nomatch hmatch
      | some u =>
        injection hmatch with hu'_eq
        have hu_lt : u < spec.n_d := hed_wf eIdx u hg
        let v := nextD spec.n_d u
        let v' := nextD spec.n_d u'
        have hv_lt : v < spec.n_d := by dsimp [v, nextD]; split_ifs <;> omega
        have hv'_lt : v' < spec.n_d := by dsimp [v', nextD]; split_ifs <;> omega
        have hu'_cases : (u = 0 ∧ u' = 0) ∨ (u ≠ 0 ∧ u' = spec.n_d - u) := by
          rw [← hu'_eq]
          by_cases hu0 : u = 0
          · subst hu0; left; simp
          · right; exact ⟨hu0, Nat.mod_eq_of_lt (by omega)⟩
        have hσ_u' : σ ⟨u', by omega⟩ = ⟨v, by omega⟩ := by
          ext
          change reflIdxFun spec.n_d spec.h_sz u' = v
          dsimp only [reflIdxFun, v, nextD]
          rw [if_pos hu'_lt]
          rcases hu'_cases with ⟨hu0, hu'0⟩ | ⟨hu0, hu'0⟩
          · rw [hu'0]; split_ifs <;> omega
          · rw [hu'0]; split_ifs <;> omega
        have hσ_v' : σ ⟨v', by omega⟩ = ⟨u, by omega⟩ := by
          ext
          change reflIdxFun spec.n_d spec.h_sz v' = u
          have hv'_def : v' = if u' + 1 < spec.n_d then u' + 1 else 0 := rfl
          rcases hu'_cases with ⟨hu0, hu'0⟩ | ⟨hu0, hu'0⟩
          · have hv'1 : v' = 1 := by rw [hv'_def, hu'0, if_pos (by omega)]
            rw [hv'1, hu0]
            dsimp [reflIdxFun]; rw [if_pos (by omega)]
          · by_cases hu1 : u = 1
            · have hv'0 : v' = 0 := by rw [hv'_def, hu'0, hu1, if_neg (by omega)]
              rw [hv'0, hu1]
              dsimp [reflIdxFun]; rw [if_pos (by omega)]
            · have hv's : v' = spec.n_d - u + 1 := by rw [hv'_def, hu'0, if_pos (by omega)]
              rw [hv's]
              dsimp [reflIdxFun]; split_ifs <;> omega
        have hσ_e : σ ⟨spec.n_d + eIdx', by omega⟩ = ⟨spec.n_d + eIdx, by omega⟩ := by
          ext
          change reflIdxFun spec.n_d spec.h_sz (spec.n_d + eIdx') = spec.n_d + eIdx
          dsimp [reflIdxFun, eIdx, reflEdgeIdx]
          split_ifs <;> omega
        let fu : Fin 7 := ⟨u, by omega⟩
        let fv : Fin 7 := ⟨v, by omega⟩
        let fy : Fin 7 := ⟨spec.n_d + eIdx, by omega⟩
        have hyu : fy ≠ fu := fun e => by have := congrArg Fin.val e; dsimp [fy, fu] at this; omega
        have hyv : fy ≠ fv := fun e => by have := congrArg Fin.val e; dsimp [fy, fv] at this; omega
        have huv : fu ≠ fv := fun e => by
          have := congrArg Fin.val e; dsimp [fu, fv, v, nextD] at this; split_ifs at this <;> omega
        intro Tw hfu' hfv'
        have hfu_in : fu ∈ Tw.image σ := by
          dsimp only [fu]; rw [← hσ_v']; exact Finset.mem_image_of_mem σ hfv'
        have hfv_in : fv ∈ Tw.image σ := by
          dsimp only [fv]; rw [← hσ_u']; exact Finset.mem_image_of_mem σ hfu'
        have ht0 : inOpenTriBool (S fy) (w (Tw.image σ)) (S fu) (S fv) = true :=
          hV.h_edges hnd3 eIdx u he_lt hg hu_lt (Tw.image σ) hfu_in hfv_in
        have ht_sw : inOpenTriBool (S fy) (w (Tw.image σ)) (S fv) (S fu) = true :=
          inOpenTriBool_swap_endpoints hV.hP hyu hyv huv (Tw.image σ) ht0
        have ht_refl : inOpenTriBool
            (reflX (S fy)) (reflX (w (Tw.image σ))) (reflX (S fv)) (reflX (S fu)) = true :=
          inOpenTriBool_reflX
            (orient_w_S_S_ne hV.hP _ hyv.symm)
            (orient_S_S_S_ne hV.hP huv.symm hyu.symm hyv.symm)
            (orient_S_w_S_ne hV.hP hyu.symm _)
            ht_sw
        have hfv'_fin : (⟨if u' + 1 < spec.n_d then u' + 1 else 0, nextMod_lt_seven (by omega)⟩ : Fin 7) =
            ⟨v', by omega⟩ := by ext; rfl
        simp only [S', w', S₁, w₁, Function.comp_apply, relabelS, relabelW, hσ_e, hσ_u']
        rw [hfv'_fin, hσ_v']
        exact ht_refl
  · dsimp only [reflSpec, EdgesBounded]
    intro eIdx' u' hed
    dsimp only [reflEdges] at hed
    rw [listGetOpt_eq_getElem?, List.getElem?_map] at hed
    cases hr : (List.range (7 - spec.n_d))[eIdx']? with
    | none => rw [hr] at hed; nomatch hed
    | some idx =>
      rw [hr] at hed; dsimp only [Option.map] at hed
      injection hed with hm
      cases hg : listGetOpt spec.edges (reflEdgeIdx spec.h_sz idx) with
      | none => rw [hg] at hm; nomatch hm
      | some opt_u =>
        rw [hg] at hm
        cases opt_u with
        | none => nomatch hm
        | some u =>
          injection hm with hu'_eq
          subst hu'_eq
          exact Nat.mod_lt _ (by have := hV.h_nd_ge2; omega)

/-! ## 6. Combined Dihedral Normalization Action (`applyDihedralNorm`) -/

def dihedralNormSpec (doRefl : Bool) (rotSteps : ℕ) (swaps : List ℕ)
    (masks' : List ℕ) (spec : CaseSpec) : CaseSpec :=
  let s1 := if doRefl then reflSpec spec else spec
  let s2 := rotateSpec rotSteps s1
  let s3 := applySwapsASpec swaps s2
  withMasksSpec s3 masks'

theorem ValidCanonicalInstance.applyDihedralNorm {P : Set (ℝ × ℝ)}
    {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ} {spec : CaseSpec}
    (hV : ValidCanonicalInstance P S w spec)
    (hlr0 : spec.lr_l = (if spec.h_sz = 0 then none else some 0))
    (hed_wf : EdgesBounded spec)
    (doRefl : Bool) (rotSteps : ℕ) (swaps : List ℕ) (masks' : List ℕ)
    (hswaps : ∀ k ∈ swaps, spec.n_d + spec.h_sz + k + 1 < 7) :
    ∃ (P' : Set (ℝ × ℝ)) (S' : Fin 7 → ℝ × ℝ) (w' : Finset (Fin 7) → ℝ × ℝ),
      ValidCanonicalInstance P' S' w' (dihedralNormSpec doRefl rotSteps swaps masks' spec) := by
  have h1 : ∃ (P₁ : Set (ℝ × ℝ)) (S₁ : Fin 7 → ℝ × ℝ) (w₁ : Finset (Fin 7) → ℝ × ℝ),
      let s1 := if doRefl then reflSpec spec else spec
      ValidCanonicalInstance P₁ S₁ w₁ s1 ∧
      (s1.h_sz = 0 → s1.lr_l = none) ∧
      EdgesBounded s1 ∧
      s1.n_d = spec.n_d ∧ s1.h_sz = spec.h_sz := by
    cases doRefl
    · refine ⟨P, S, w, hV, ?_, hed_wf, rfl, rfl⟩
      change spec.h_sz = 0 → spec.lr_l = none
      intro hh0; rw [hlr0, if_pos hh0]
    · obtain ⟨P₁, S₁, w₁, hV₁, hlr₁, hed₁⟩ := hV.reflD hlr0 hed_wf
      exact ⟨P₁, S₁, w₁, hV₁, hlr₁, hed₁, rfl, rfl⟩
  rcases h1 with ⟨P₁, S₁, w₁, hV₁, hlr₁, hed₁, hnd1, hh1⟩
  let s1 := if doRefl then reflSpec spec else spec
  have hrot_dims : ∀ r (sp : CaseSpec),
      (rotateSpec r sp).n_d = sp.n_d ∧ (rotateSpec r sp).h_sz = sp.h_sz := by
    intro r
    induction r with
    | zero => intro sp; exact ⟨rfl, rfl⟩
    | succ r' ih => intro sp; exact ih (rotSpec1 sp)
  obtain ⟨S₂, w₂, hV₂⟩ := hV₁.rotateD rotSteps hlr₁ hed₁
  have hdims2 := hrot_dims rotSteps s1
  have hsw2 : ∀ k ∈ swaps, (rotateSpec rotSteps s1).n_d + (rotateSpec rotSteps s1).h_sz + k + 1 < 7 := by
    rw [hdims2.1, hdims2.2, hnd1, hh1]; exact hswaps
  obtain ⟨S₃, w₃, hV₃⟩ := hV₂.applySwapsA swaps hsw2
  exact ⟨P₁, S₃, w₃, hV₃.withMasks masks'⟩

end VCDim6

end
