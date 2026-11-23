import Mathlib
import RootTask.Defs
import RootTask.Sec9Perturb
import RootTask.Sec9Dual
import RootTask.Sec9Sweep
import RootTask.Sec9Leaves

open scoped Classical BigOperators
open Finset

noncomputable section

namespace Sec9

/-! ## Part 2: Hull Block Decomposition & Realization Helper -/

def blockVal {f : Fin 5 → VFunc} (H : HullData f) (r : Fin H.h) : ℕ :=
  (Finset.univ.filter (fun k : Fin (H.h - 1) =>
    k.val < r.val ∧
    (H.q ⟨k.val, by have := H.hh_ge; omega⟩).1 ≠
    (H.q ⟨k.val + 1, by have := H.hh_ge; omega⟩).1)).card

lemma blockVal_zero {f : Fin 5 → VFunc} (H : HullData f) :
    blockVal H ⟨0, by have := H.hh_ge; omega⟩ = 0 := by
  unfold blockVal
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k _ hk
  dsimp at hk
  omega

lemma blockVal_last {f : Fin 5 → VFunc} (H : HullData f) :
    blockVal H ⟨H.h - 1, by have := H.hh_ge; omega⟩ = H.n - 1 := by
  have h1 : Finset.univ.filter (fun k : Fin (H.h - 1) =>
      k.val < H.h - 1 ∧
      (H.q ⟨k.val, by have := H.hh_ge; omega⟩).1 ≠
      (H.q ⟨k.val + 1, by have := H.hh_ge; omega⟩).1) =
      Finset.univ.filter (fun k : Fin (H.h - 1) =>
        (H.q ⟨k.val, by have := H.hh_ge; omega⟩).1 ≠
        (H.q ⟨k.val + 1, by have := H.hh_ge; omega⟩).1) := by
    apply Finset.ext; intro k; simp
  unfold blockVal HullData.n
  rw [h1]; omega

lemma blockVal_mono {f : Fin 5 → VFunc} (H : HullData f) : Monotone (blockVal H) := by
  intro a b hab
  refine Finset.card_le_card (fun k hk => ?_)
  have hk' := (Finset.mem_filter.mp hk).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hk'.1 hab, hk'.2⟩

lemma blockVal_step {f : Fin 5 → VFunc} (H : HullData f) (r : Fin (H.h - 1)) :
    blockVal H ⟨r.val + 1, by have := H.hh_ge; omega⟩ =
      blockVal H ⟨r.val, by have := H.hh_ge; omega⟩ +
      if (H.q ⟨r.val, by have := H.hh_ge; omega⟩).1 ≠
         (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩).1 then 1 else 0 := by
  let S0 := Finset.univ.filter (fun k : Fin (H.h - 1) =>
    k.val < r.val ∧
    (H.q ⟨k.val, by have := H.hh_ge; omega⟩).1 ≠
    (H.q ⟨k.val + 1, by have := H.hh_ge; omega⟩).1)
  let S1 := Finset.univ.filter (fun k : Fin (H.h - 1) =>
    k.val < r.val + 1 ∧
    (H.q ⟨k.val, by have := H.hh_ge; omega⟩).1 ≠
    (H.q ⟨k.val + 1, by have := H.hh_ge; omega⟩).1)
  change S1.card = S0.card + _
  by_cases hne : (H.q ⟨r.val, by have := H.hh_ge; omega⟩).1 ≠
      (H.q ⟨r.val + 1, by have := H.hh_ge; omega⟩).1
  · rw [if_pos hne]
    have hnot : r ∉ S0 := fun h => by have := (Finset.mem_filter.mp h).2.1; omega
    have heq : S1 = insert r S0 := by
      apply Finset.ext; intro k
      simp only [S1, S0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hk1, hk2⟩
        by_cases hkr : k = r
        · left; exact hkr
        · right; refine ⟨?_, hk2⟩
          have : k.val ≠ r.val := fun h => hkr (Fin.ext h)
          omega
      · rintro (rfl | ⟨hk1, hk2⟩)
        · exact ⟨by omega, hne⟩
        · exact ⟨by omega, hk2⟩
    rw [heq, Finset.card_insert_of_notMem hnot]
  · rw [if_neg hne]
    have heq : S1 = S0 := by
      apply Finset.ext; intro k
      simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hk1, hk2⟩
        refine ⟨?_, hk2⟩
        by_contra hge
        have hkr : k = r := Fin.ext (by omega)
        subst hkr; exact hne hk2
      · intro ⟨hk1, hk2⟩
        exact ⟨by omega, hk2⟩
    rw [heq]; omega

lemma blockVal_lt_n {f : Fin 5 → VFunc} (H : HullData f) (r : Fin H.h) :
    blockVal H r < H.n := by
  have hn : 1 ≤ H.n := by unfold HullData.n; omega
  have hle : blockVal H r ≤ blockVal H ⟨H.h - 1, by have := H.hh_ge; omega⟩ :=
    blockVal_mono H (by change r.val ≤ H.h - 1; have := r.isLt; omega)
  rw [blockVal_last H] at hle
  omega

lemma blockVal_surj {f : Fin 5 → VFunc} (H : HullData f) (j : Fin H.n) :
    ∃ r : Fin H.h, blockVal H r = j.val := by
  let S := Finset.univ.filter (fun r : Fin H.h => j.val ≤ blockVal H r)
  have hSne : S.Nonempty := by
    refine ⟨⟨H.h - 1, by have := H.hh_ge; omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [blockVal_last H]; have := j.isLt; omega
  let r := S.min' hSne
  have hr_ge : j.val ≤ blockVal H r := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
  by_cases hr0 : r.val = 0
  · have hreq : r = ⟨0, by have := H.hh_ge; omega⟩ := Fin.ext hr0
    rw [hreq, blockVal_zero] at hr_ge
    refine ⟨⟨0, by have := H.hh_ge; omega⟩, ?_⟩
    rw [blockVal_zero]; omega
  · have hr_lt := r.isLt
    let rp : Fin (H.h - 1) := ⟨r.val - 1, by omega⟩
    have hrp_not : (⟨rp.val, by have := H.hh_ge; omega⟩ : Fin H.h) ∉ S := by
      intro hmem
      have hle := Finset.min'_le S _ hmem
      change r.val ≤ rp.val at hle
      dsimp [rp] at hle; omega
    have hrp_lt : blockVal H ⟨rp.val, by have := H.hh_ge; omega⟩ < j.val := by
      by_contra hge
      exact hrp_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp hge⟩)
    have hstep := blockVal_step H rp
    have hreq : (⟨rp.val + 1, by have := H.hh_ge; omega⟩ : Fin H.h) = r := by
      ext; dsimp [rp]; omega
    rw [hreq] at hstep
    refine ⟨r, ?_⟩
    by_cases hif : (H.q ⟨rp.val, by have := H.hh_ge; omega⟩).1 ≠ (H.q r).1
    · rw [if_pos hif] at hstep; omega
    · rw [if_neg hif] at hstep; omega

lemma blockVal_eq_same_color {f : Fin 5 → VFunc} (H : HullData f) {r₁ r₂ : Fin H.h}
    (h12 : r₁ ≤ r₂) (heq : blockVal H r₁ = blockVal H r₂) :
    (H.q r₁).1 = (H.q r₂).1 := by
  have hh5 := H.hh_ge
  have hr2 := r₂.isLt
  have h12' : r₁.val ≤ r₂.val := h12
  have hno : ∀ k : ℕ, (hk : r₁.val ≤ k ∧ k < r₂.val) →
      (H.q ⟨k, by omega⟩).1 = (H.q ⟨k + 1, by omega⟩).1 := by
    intro k hk
    by_contra hne
    let k' : Fin (H.h - 1) := ⟨k, by omega⟩
    let S1 := Finset.univ.filter (fun m : Fin (H.h - 1) =>
      m.val < r₁.val ∧ (H.q ⟨m.val, by omega⟩).1 ≠ (H.q ⟨m.val + 1, by omega⟩).1)
    let S2 := Finset.univ.filter (fun m : Fin (H.h - 1) =>
      m.val < r₂.val ∧ (H.q ⟨m.val, by omega⟩).1 ≠ (H.q ⟨m.val + 1, by omega⟩).1)
    have hsub : S1 ⊂ S2 := Finset.ssubset_iff_subset_ne.mpr ⟨fun m hm => by
      have hm' := (Finset.mem_filter.mp hm).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le hm'.1 h12, hm'.2⟩, by
      intro heqS
      have hk2 : k' ∈ S2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.2, hne⟩
      rw [← heqS] at hk2
      have hk1 := (Finset.mem_filter.mp hk2).2.1
      dsimp [k'] at hk1; omega⟩
    have hlt := Finset.card_lt_card hsub
    change blockVal H r₁ < blockVal H r₂ at hlt
    omega
  have h_ind : ∀ d : ℕ, (hd : r₁.val + d ≤ r₂.val) →
      (H.q r₁).1 = (H.q ⟨r₁.val + d, by omega⟩).1 := by
    intro d; induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [ih (by omega)]
      exact hno (r₁.val + d) ⟨by omega, by omega⟩
  have hres := h_ind (r₂.val - r₁.val) (by change r₁.val ≤ r₂.val at h12; omega)
  have hreq : (⟨r₁.val + (r₂.val - r₁.val), by omega⟩ : Fin H.h) = r₂ := by
    ext; dsimp; change r₁.val ≤ r₂.val at h12; omega
  rwa [hreq] at hres

def kbar {f : Fin 5 → VFunc} (H : HullData f) (j : Fin H.n) : Fin 5 :=
  (H.q (Classical.choose (blockVal_surj H j))).1

lemma kbar_at_blockVal {f : Fin 5 → VFunc} (H : HullData f) (r : Fin H.h) :
    (H.q r).1 = kbar H ⟨blockVal H r, blockVal_lt_n H r⟩ := by
  let j : Fin H.n := ⟨blockVal H r, blockVal_lt_n H r⟩
  let r' := Classical.choose (blockVal_surj H j)
  have hr' : blockVal H r' = j.val := Classical.choose_spec (blockVal_surj H j)
  rcases le_total r r' with h1 | h2
  · exact blockVal_eq_same_color H h1 hr'.symm
  · exact (blockVal_eq_same_color H h2 hr').symm

lemma kbar_adj_ne {f : Fin 5 → VFunc} (H : HullData f) (j : Fin (H.n - 1)) :
    kbar H ⟨j.val, by have := j.isLt; omega⟩ ≠
    kbar H ⟨j.val + 1, by have := j.isLt; omega⟩ := by
  have hh5 := H.hh_ge
  let S := Finset.univ.filter (fun r : Fin H.h => blockVal H r = j.val)
  have hSne : S.Nonempty := by
    obtain ⟨r0, hr0⟩ := blockVal_surj H ⟨j.val, by have := j.isLt; omega⟩
    exact ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0⟩⟩
  let r0 := S.max' hSne
  have hr0_eq : blockVal H r0 = j.val := (Finset.mem_filter.mp (Finset.max'_mem S hSne)).2
  have hr0_lt : r0.val + 1 < H.h := by
    have hr0_le := r0.isLt
    by_contra hge
    have hlast : r0 = ⟨H.h - 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hlast, blockVal_last] at hr0_eq
    have := j.isLt; omega
  let r1 : Fin H.h := ⟨r0.val + 1, hr0_lt⟩
  have hr1_gt : j.val < blockVal H r1 := by
    by_contra hle
    have hmono : blockVal H r0 ≤ blockVal H r1 := blockVal_mono H (by change r0.val ≤ r0.val + 1; omega)
    have hr1_eq : blockVal H r1 = j.val := by omega
    have hle_max := Finset.le_max' S r1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1_eq⟩)
    change r1.val ≤ r0.val at hle_max
    dsimp [r1] at hle_max; omega
  have hstep := blockVal_step H ⟨r0.val, by omega⟩
  change blockVal H r1 = blockVal H r0 + _ at hstep
  have hne_q : (H.q ⟨r0.val, by omega⟩).1 ≠ (H.q ⟨r0.val + 1, by omega⟩).1 := by
    by_contra heq
    rw [if_neg (not_not.mpr heq)] at hstep; omega
  have hc0 : (H.q ⟨r0.val, by omega⟩).1 = kbar H ⟨j.val, by have := j.isLt; omega⟩ := by
    have := kbar_at_blockVal H r0
    have hfeq : (⟨blockVal H r0, blockVal_lt_n H r0⟩ : Fin H.n) = ⟨j.val, by have := j.isLt; omega⟩ :=
      Fin.ext hr0_eq
    rw [hfeq] at this; exact this
  have hr1_val : blockVal H r1 = j.val + 1 := by
    rw [if_pos hne_q] at hstep; omega
  have hc1 : (H.q r1).1 = kbar H ⟨j.val + 1, by have := j.isLt; omega⟩ := by
    have := kbar_at_blockVal H r1
    have hfeq : (⟨blockVal H r1, blockVal_lt_n H r1⟩ : Fin H.n) = ⟨j.val + 1, by have := j.isLt; omega⟩ :=
      Fin.ext hr1_val
    rw [hfeq] at this; exact this
  rw [← hc0, ← hc1]; exact hne_q

lemma kbar_surj {f : Fin 5 → VFunc} (H : HullData f) : Function.Surjective (kbar H) := by
  intro i
  obtain ⟨b, hb⟩ := H.h_colors_H i
  obtain ⟨r, hr⟩ := H.hq_surj (i, b) hb
  refine ⟨⟨blockVal H r, blockVal_lt_n H r⟩, ?_⟩
  rw [← kbar_at_blockVal H r, hr]

lemma hull_n_ge_5 {f : Fin 5 → VFunc} (H : HullData f) : 5 ≤ H.n := by
  have := Fintype.card_le_of_surjective (kbar H) (kbar_surj H)
  simpa using this

lemma hull_n_le_h {f : Fin 5 → VFunc} (H : HullData f) : H.n ≤ H.h := by
  have hh5 := H.hh_ge
  unfold HullData.n
  calc 1 + (Finset.univ.filter (fun r : Fin (H.h - 1) =>
        (H.q ⟨r.val, by omega⟩).1 ≠ (H.q ⟨r.val + 1, by omega⟩).1)).card
      ≤ 1 + (Finset.univ : Finset (Fin (H.h - 1))).card := by gcongr; exact Finset.filter_subset _ _
    _ = 1 + (H.h - 1) := by simp
    _ = H.h := by omega

/-- Universal realization constraint on `H`: for any nonempty `S : Finset (Fin 5)` realized by
    `DualRealizes G.f S s t`, there exist `0 ≤ a ≤ b < H.n` such that every block color
    `kbar H j` (`a ≤ j ≤ b`) is in `S`, and every color `c ∈ S` not in `{kbar H j | a ≤ j ≤ b}`
    must have an interior point `p_c ∈ R_int G.f` whose fixed slab `r_c` satisfies
    `a ≤ min (blockVal H r_c) (H.n - 2) + 1` and `min (blockVal H r_c) (H.n - 2) ≤ b`. -/
def fixedSlabIdx {f : Fin 5 → VFunc} (H : HullData f) (p : Fin 5 × Bool)
    (hp : p ∈ R_int f) : ℕ :=
  min (blockVal H ⟨(Classical.choose (H.h_subenv p hp)).val, by have := H.hh_ge; omega⟩) (H.n - 2)

lemma dualRealizes_hull_slab_spec {f : Fin 5 → VFunc} (H : HullData f)
    (h_dual : ∀ S : Finset (Fin 5), ∃ s t : ℝ, DualRealizes f S s t)
    (S : Finset (Fin 5)) (hSne : S.Nonempty) :
    ∃ a b : ℕ, a ≤ b ∧ b < H.n ∧
      (∀ j : Fin H.n, a ≤ j.val → j.val ≤ b → kbar H j ∈ S) ∧
      (∀ c ∈ S, (∃ j : Fin H.n, a ≤ j.val ∧ j.val ≤ b ∧ kbar H j = c) ∨
        (∃ (p : Fin 5 × Bool) (hp : p ∈ R_int f),
          p.1 = c ∧ a ≤ fixedSlabIdx H p hp + 1 ∧ fixedSlabIdx H p hp ≤ b)) := by
  have hh5 := H.hh_ge
  have hn5 : 5 ≤ H.n := hull_n_ge_5 H
  obtain ⟨s, t, _, hS⟩ := h_dual S
  let U_H := Finset.univ.filter (fun r : Fin H.h =>
    s * (dualPt f (H.q r)).1 + t < (dualPt f (H.q r)).2)
  have hUH_ne : U_H.Nonempty := by
    obtain ⟨i₀, hi₀⟩ := hSne
    obtain ⟨b₀, hb₀⟩ := (hS i₀).mp hi₀
    by_cases hH : (i₀, b₀) ∈ H_top f
    · obtain ⟨r, hr⟩ := H.hq_surj (i₀, b₀) hH
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr ▸ hb₀⟩⟩
    · have hp : (i₀, b₀) ∈ R_int f := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hH⟩
      obtain ⟨r, hu1, hu2, _⟩ := H.h_subenv (i₀, b₀) hp
      rcases H.h_lift s t (i₀, b₀) r hp hu1 hu2 hb₀ with h | h
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      · exact ⟨⟨r.val + 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  let r_min := U_H.min' hUH_ne
  let r_max := U_H.max' hUH_ne
  have hr_min_U : r_min ∈ U_H := Finset.min'_mem U_H hUH_ne
  have hr_max_U : r_max ∈ U_H := Finset.max'_mem U_H hUH_ne
  have hmin_le_max : r_min ≤ r_max := Finset.min'_le U_H r_max hr_max_U
  have h_interval : ∀ r : Fin H.h, r ∈ U_H ↔ r_min ≤ r ∧ r ≤ r_max := by
    intro r; constructor
    · intro hr; exact ⟨Finset.min'_le U_H r hr, Finset.le_max' U_H r hr⟩
    · rintro ⟨h1, h2⟩
      by_cases h_eq1 : r = r_min
      · rwa [h_eq1]
      · by_cases h_eq2 : r = r_max
        · rwa [h_eq2]
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.h_contiguity s t r_min r r_max
            (lt_of_le_of_ne h1 (Ne.symm h_eq1)) (lt_of_le_of_ne h2 h_eq2)
            (Finset.mem_filter.mp hr_min_U).2 (Finset.mem_filter.mp hr_max_U).2⟩
  let a := blockVal H r_min
  let b := blockVal H r_max
  have hab : a ≤ b := blockVal_mono H hmin_le_max
  have hb_lt : b < H.n := blockVal_lt_n H r_max
  refine ⟨a, b, hab, hb_lt, ?_, ?_⟩
  · intro j haj hjb
    have hj_mem : ∃ r : Fin H.h, r_min ≤ r ∧ r ≤ r_max ∧ blockVal H r = j.val := by
      let S_j := Finset.univ.filter (fun r : Fin H.h => blockVal H r = j.val)
      have hS_j : S_j.Nonempty := by
        obtain ⟨r0, hr0⟩ := blockVal_surj H j
        exact ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr0⟩⟩
      let r_hi := S_j.max' hS_j
      have hr_hi_eq : blockVal H r_hi = j.val := (Finset.mem_filter.mp (Finset.max'_mem S_j hS_j)).2
      rcases le_total r_min r_hi with h1 | h1
      · refine ⟨min r_hi r_max, le_min h1 hmin_le_max, min_le_right _ _, ?_⟩
        rcases le_total r_hi r_max with h2 | h2
        · rwa [min_eq_left h2]
        · rw [min_eq_right h2]
          have h_le2 : blockVal H r_max ≤ j.val := by rw [← hr_hi_eq]; exact blockVal_mono H h2
          dsimp [b] at hjb; omega
      · have h_le : blockVal H r_hi ≤ blockVal H r_min := blockVal_mono H h1
        have ha_eq : a = j.val := by dsimp [a]; omega
        exact ⟨r_min, le_rfl, hmin_le_max, ha_eq⟩
    obtain ⟨r, hr1, hr2, hr_val⟩ := hj_mem
    have hr_U : r ∈ U_H := (h_interval r).mpr ⟨hr1, hr2⟩
    have hr_lt := (Finset.mem_filter.mp hr_U).2
    have h_col : (H.q r).1 ∈ S := (hS (H.q r).1).mpr ⟨(H.q r).2, hr_lt⟩
    have hkeq := kbar_at_blockVal H r
    have hfeq : (⟨blockVal H r, blockVal_lt_n H r⟩ : Fin H.n) = j := Fin.ext hr_val
    rw [hfeq] at hkeq
    rwa [← hkeq]
  · intro c hcS
    by_cases hex : ∃ j : Fin H.n, a ≤ j.val ∧ j.val ≤ b ∧ kbar H j = c
    · exact Or.inl hex
    · right
      obtain ⟨b₀, hb₀⟩ := (hS c).mp hcS
      have hp : (c, b₀) ∈ R_int f := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hH => ?_⟩
        obtain ⟨r, hr⟩ := H.hq_surj (c, b₀) hH
        have hr_U : r ∈ U_H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr ▸ hb₀⟩
        obtain ⟨hr1, hr2⟩ := (h_interval r).mp hr_U
        have haj : a ≤ blockVal H r := blockVal_mono H hr1
        have hjb : blockVal H r ≤ b := blockVal_mono H hr2
        have hkeq := kbar_at_blockVal H r
        rw [hr] at hkeq
        exact hex ⟨⟨blockVal H r, blockVal_lt_n H r⟩, haj, hjb, hkeq.symm⟩
      refine ⟨(c, b₀), hp, rfl, ?_⟩
      let r_c := Classical.choose (H.h_subenv (c, b₀) hp)
      have hr_c := Classical.choose_spec (H.h_subenv (c, b₀) hp)
      have h_lift := H.h_lift s t (c, b₀) r_c hp hr_c.1 hr_c.2.1 hb₀
      have hr_U : (⟨r_c.val, by omega⟩ : Fin H.h) ∈ U_H ∨
          (⟨r_c.val + 1, by omega⟩ : Fin H.h) ∈ U_H := by
        rcases h_lift with h | h
        · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      have hstep := blockVal_step H r_c
      dsimp [fixedSlabIdx]
      change a ≤ min (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) + 1 ∧
        min (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) ≤ b
      rcases hr_U with hr_in | hr_in
      · obtain ⟨hr1, hr2⟩ := (h_interval _).mp hr_in
        have ha_le : a ≤ blockVal H ⟨r_c.val, by omega⟩ := blockVal_mono H hr1
        have hb_ge : blockVal H ⟨r_c.val, by omega⟩ ≤ b := blockVal_mono H hr2
        have hlt_n := blockVal_lt_n H ⟨r_c.val, by omega⟩
        omega
      · obtain ⟨hr1, hr2⟩ := (h_interval _).mp hr_in
        have ha_le : a ≤ blockVal H ⟨r_c.val + 1, by omega⟩ := blockVal_mono H hr1
        have hb_ge : blockVal H ⟨r_c.val + 1, by omega⟩ ≤ b := blockVal_mono H hr2
        have hstep_le : blockVal H ⟨r_c.val + 1, by omega⟩ ≤ blockVal H ⟨r_c.val, by omega⟩ + 1 := by
          split_ifs at hstep <;> omega
        have h_n1 : H.n - 1 ≤ (H.n - 2) + 1 := by omega
        -- Wait: if `r_c` has `blockVal = H.n - 1` and `(q r_c).1 = (q (r_c+1)).1`, then `b = H.n - 1 ≥ H.n - 2`!
        have hb_ge' : min (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) ≤ b := by
          rcases le_or_gt (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) with hle | hgt
          · have : blockVal H ⟨r_c.val, by omega⟩ ≤ blockVal H ⟨r_c.val + 1, by omega⟩ :=
              blockVal_mono H (by change r_c.val ≤ r_c.val + 1; omega)
            omega
          · have hlt_n := blockVal_lt_n H ⟨r_c.val, by omega⟩
            have hlt_n1 := blockVal_lt_n H ⟨r_c.val + 1, by omega⟩
            have h_eq : blockVal H ⟨r_c.val, by omega⟩ = H.n - 1 := by omega
            have h_le2 : blockVal H ⟨r_c.val, by omega⟩ ≤ blockVal H ⟨r_c.val + 1, by omega⟩ :=
              blockVal_mono H (by change r_c.val ≤ r_c.val + 1; omega)
            omega
        have ha_le' : a ≤ min (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) + 1 := by
          rcases le_or_gt (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) with hle | hgt
          · omega
          · have ha_lt := blockVal_lt_n H r_min
            dsimp [a] at *; omega
        exact ⟨ha_le', hb_ge'⟩

/-! ## Part 3: Right-Slope Permutation `σ`, Outer Witnesses, Certificates, `H.n ≤ 7` -/

lemma permInvCount5_symm (σ : Equiv.Perm (Fin 5)) :
    permInvCount5 σ = permInvCount5 σ.symm := by
  unfold permInvCount5
  refine Finset.card_bij (fun p _ => (σ p.2, σ p.1)) ?_ ?_ ?_
  · intro ⟨a, b⟩ hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ _, hp.2.2, ?_⟩
    simpa using hp.2.1
  · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
    have h1 := σ.injective (congrArg Prod.fst heq)
    have h2 := σ.injective (congrArg Prod.snd heq)
    exact Prod.ext h2 h1
  · intro ⟨x, y⟩ hxy
    rw [Finset.mem_filter] at hxy
    refine ⟨(σ.symm y, σ.symm x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.2.2, ?_⟩, ?_⟩
    · simpa using hxy.2.1
    · ext <;> simp

lemma P_inv_card (G : GenericVSystem) : (P_inv G.f).card = T3bar G - T1 G := by
  let S3 := E_G3 G
  let S1 := pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1)
  let S2 := P_inv G.f
  have hconc_part : ∀ p ∈ pair5, (G.f p.1).c < (G.f p.2).c ∨ (G.f p.2).c < (G.f p.1).c := by
    intro ⟨i, j⟩ hp
    have hij : i < j := (Finset.mem_filter.mp hp).2
    have hne : (G.f i).c ≠ (G.f j).c := fun h => by
      have := G.slopes_inj (a₁ := (i, true)) (a₂ := (j, true)) h
      exact (ne_of_lt hij) (congrArg Prod.fst this)
    exact lt_or_gt_of_ne hne
  have hpart : ∀ p ∈ pair5, p ∈ S3 ∨ p ∈ S1 ∨ p ∈ S2 := by
    intro ⟨i, j⟩ hp
    have hij : i < j := (Finset.mem_filter.mp hp).2
    rcases hconc_part (i, j) hp with hc | hi
    · rcases (Z_set_conc_spec G hij hc).1 with h1 | h3
      · right; left; exact Finset.mem_filter.mpr ⟨hp, hc, h1⟩
      · left; exact Finset.mem_filter.mpr ⟨hp, h3⟩
    · right; right; exact Finset.mem_filter.mpr ⟨hp, hi⟩
  have h12 : Disjoint S3 S1 := by
    rw [Finset.disjoint_left]; intro p h3 h1
    have := (Finset.mem_filter.mp h3).2
    have := (Finset.mem_filter.mp h1).2.2
    omega
  have h13 : Disjoint (S3 ∪ S1) S2 := by
    rw [Finset.disjoint_left]; intro p h31 h2
    have hij : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
    have hi : (G.f p.2).c < (G.f p.1).c := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h31 with h3 | h1
    · have h3' := (Finset.mem_filter.mp h3).2
      have h2' := (Z_set_inv_spec G hij hi).1
      omega
    · have h1' := (Finset.mem_filter.mp h1).2.1
      linarith
  have hpair_eq : pair5 = S3 ∪ S1 ∪ S2 := by
    apply Finset.ext; intro p; constructor
    · intro hp; rcases hpart p hp with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
      · exact Finset.mem_union_right _ h
    · intro hp; rcases Finset.mem_union.mp hp with h | h
      · rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  have hcard_total : 10 = S3.card + S1.card + S2.card := by
    calc 10 = pair5.card := pair5_card.symm
      _ = (S3 ∪ S1 ∪ S2).card := by rw [hpair_eq]
      _ = S3.card + S1.card + S2.card := by
          rw [Finset.card_union_of_disjoint h13, Finset.card_union_of_disjoint h12]
  dsimp [S3, S1, S2] at hcard_total
  change 10 = T3 G + T1 G + (P_inv G.f).card at hcard_total
  dsimp [T3bar]; omega

def cPerm (G : GenericVSystem) : Equiv.Perm (Fin 5) :=
  let cSet : Finset ℝ := Finset.univ.image (fun i : Fin 5 => (G.f i).c)
  have hc_inj : Function.Injective (fun i : Fin 5 => (G.f i).c) := fun i j h =>
    congrArg Prod.fst (G.slopes_inj (a₁ := (i, true)) (a₂ := (j, true)) h)
  have hc_card : cSet.card = 5 := by rw [Finset.card_image_of_injective _ hc_inj, Finset.card_fin]
  let cEmb : Fin 5 ↪o ℝ := cSet.orderEmbOfFin hc_card
  let fn : Fin 5 → Fin 5 := fun r =>
    Classical.choose (Finset.mem_image.mp (Finset.orderEmbOfFin_mem cSet hc_card r))
  have hfn_spec : ∀ r : Fin 5, (G.f (fn r)).c = cEmb r := fun r =>
    (Classical.choose_spec (Finset.mem_image.mp (Finset.orderEmbOfFin_mem cSet hc_card r))).2
  have hfn_inj : Function.Injective fn := fun r₁ r₂ heq =>
    cEmb.injective (by rw [← hfn_spec r₁, ← hfn_spec r₂, heq])
  Equiv.ofBijective fn ((Fintype.bijective_iff_injective_and_card fn).mpr ⟨hfn_inj, rfl⟩)

lemma cPerm_strictMono (G : GenericVSystem) :
    StrictMono (fun r : Fin 5 => (G.f (cPerm G r)).c) := by
  let cSet : Finset ℝ := Finset.univ.image (fun i : Fin 5 => (G.f i).c)
  have hc_inj : Function.Injective (fun i : Fin 5 => (G.f i).c) := fun i j h =>
    congrArg Prod.fst (G.slopes_inj (a₁ := (i, true)) (a₂ := (j, true)) h)
  have hc_card : cSet.card = 5 := by rw [Finset.card_image_of_injective _ hc_inj, Finset.card_fin]
  let cEmb : Fin 5 ↪o ℝ := cSet.orderEmbOfFin hc_card
  have hspec : ∀ r : Fin 5, (G.f (cPerm G r)).c = cEmb r := fun r =>
    (Classical.choose_spec (Finset.mem_image.mp (Finset.orderEmbOfFin_mem cSet hc_card r))).2
  intro r s hrs
  dsimp only
  rw [hspec r, hspec s]
  exact cEmb.strictMono hrs

lemma cPerm_lt_iff (G : GenericVSystem) (r s : Fin 5) :
    r < s ↔ (G.f (cPerm G r)).c < (G.f (cPerm G s)).c :=
  (cPerm_strictMono G).lt_iff_lt.symm

lemma cPerm_invCount_eq (G : GenericVSystem) :
    permInvCount5 (cPerm G) = T3bar G - T1 G := by
  rw [permInvCount5_symm, ← P_inv_card G]
  unfold permInvCount5 P_inv pair5
  congr 1
  apply Finset.ext; rintro ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hprod : (i, j) ∈ (Finset.univ : Finset (Fin 5)).product Finset.univ :=
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  have heq : (cPerm G).symm j < (cPerm G).symm i ↔ (G.f j).c < (G.f i).c := by
    have := cPerm_lt_iff G ((cPerm G).symm j) ((cPerm G).symm i)
    simpa using this
  tauto

lemma kink_not_mem_X_cross (G : GenericVSystem) (m : Fin 5) : kink G.f m ∉ X_cross G.f := by
  intro hx
  rcases Finset.mem_biUnion.mp hx with ⟨⟨i, j⟩, hp, hz⟩
  have hij : i < j := (Finset.mem_filter.mp hp).2
  exact G.gpb_kink i j m hij ((mem_Z_set G hij (kink G.f m)).mp hz)

lemma exists_tau_minus (G : GenericVSystem) :
    ∃ τm : ℝ, τm ∉ X_cross G.f ∧ (∀ i : Fin 5, τm < kink G.f i) ∧
      (∀ i j : Fin 5, i < j → (G.f j).eval τm < (G.f i).eval τm) := by
  let S : Finset ℝ := X_cross G.f ∪ Finset.univ.image (kink G.f) ∪
    pair5.image (fun p => ((G.f p.2).b - (G.f p.1).b) / ((G.f p.1).a - (G.f p.2).a))
  have hSne : S.Nonempty := ⟨kink G.f 0, Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩))⟩
  let τm := S.min' hSne - 1
  have hlt : ∀ z ∈ S, τm < z := fun z hz => by
    have := Finset.min'_le S z hz; dsimp [τm]; linarith
  refine ⟨τm, ?_, ?_, ?_⟩
  · intro hx; exact lt_irrefl _ (hlt τm (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  · intro i; exact hlt _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  · intro i j hij
    have hi_le : τm ≤ kink G.f i := le_of_lt (hlt _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))))
    have hj_le : τm ≤ kink G.f j := le_of_lt (hlt _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))))
    rw [VFunc.eval_left (G.f i) (G.ac i) hi_le, VFunc.eval_left (G.f j) (G.ac j) hj_le]
    have hmem : ((G.f j).b - (G.f i).b) / ((G.f i).a - (G.f j).a) ∈ S :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
    have htm_lt := hlt _ hmem
    have hha : (G.f i).a < (G.f j).a := G.a_mono hij
    have hneg : (G.f i).a - (G.f j).a < 0 := sub_neg.mpr hha
    have hmul : (G.f j).b - (G.f i).b < τm * ((G.f i).a - (G.f j).a) :=
      (lt_div_iff_of_neg hneg).mp htm_lt
    linarith

lemma exists_tau_plus (G : GenericVSystem) :
    ∃ τp : ℝ, τp ∉ X_cross G.f ∧ (∀ i : Fin 5, kink G.f i < τp) ∧
      (∀ r s : Fin 5, r < s → (G.f (cPerm G r)).eval τp < (G.f (cPerm G s)).eval τp) := by
  let S : Finset ℝ := X_cross G.f ∪ Finset.univ.image (kink G.f) ∪
    pair5.image (fun p => ((G.f (cPerm G p.1)).d - (G.f (cPerm G p.2)).d) /
      ((G.f (cPerm G p.2)).c - (G.f (cPerm G p.1)).c))
  have hSne : S.Nonempty := ⟨kink G.f 0, Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩))⟩
  let τp := S.max' hSne + 1
  have hgt : ∀ z ∈ S, z < τp := fun z hz => by
    have := Finset.le_max' S z hz; dsimp [τp]; linarith
  refine ⟨τp, ?_, ?_, ?_⟩
  · intro hx; exact lt_irrefl _ (hgt τp (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  · intro i; exact hgt _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
  · intro r s hrs
    have hr_le : kink G.f (cPerm G r) ≤ τp := le_of_lt (hgt _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨cPerm G r, Finset.mem_univ _, rfl⟩))))
    have hs_le : kink G.f (cPerm G s) ≤ τp := le_of_lt (hgt _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨cPerm G s, Finset.mem_univ _, rfl⟩))))
    rw [VFunc.eval_right (G.f (cPerm G r)) (G.ac (cPerm G r)) hr_le,
        VFunc.eval_right (G.f (cPerm G s)) (G.ac (cPerm G s)) hs_le]
    have hmem : ((G.f (cPerm G r)).d - (G.f (cPerm G s)).d) /
        ((G.f (cPerm G s)).c - (G.f (cPerm G r)).c) ∈ S :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(r, s),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs⟩, rfl⟩)
    have htp_gt := hgt _ hmem
    have hhc : (G.f (cPerm G r)).c < (G.f (cPerm G s)).c := cPerm_strictMono G hrs
    have hpos : 0 < (G.f (cPerm G s)).c - (G.f (cPerm G r)).c := sub_pos.mpr hhc
    have hmul : (G.f (cPerm G r)).d - (G.f (cPerm G s)).d <
        τp * ((G.f (cPerm G s)).c - (G.f (cPerm G r)).c) :=
      (div_lt_iff₀ hpos).mp htp_gt
    linarith

def E3_bool (G : GenericVSystem) (i j : Fin 5) : Bool :=
  decide (i ≠ j ∧ (Z_set G.f (min i j) (max i j)).card = 3)

lemma E3_bool_symm (G : GenericVSystem) (i j : Fin 5) :
    E3_bool G i j = E3_bool G j i := by
  unfold E3_bool
  simp only [min_comm, max_comm, ne_comm]

lemma E3_bool_conc (G : GenericVSystem) {i j : Fin 5} (hE : E3_bool G i j = true) :
    i ≠ j ∧
    ((i < j ∧ (G.f i).c < (G.f j).c ∧ kink G.f i < kink G.f j ∧
      (G.f i).eval (kink G.f i) < (G.f j).eval (kink G.f i) ∧
      (G.f j).eval (kink G.f j) < (G.f i).eval (kink G.f j)) ∨
     (j < i ∧ (G.f j).c < (G.f i).c ∧ kink G.f j < kink G.f i ∧
      (G.f j).eval (kink G.f j) < (G.f i).eval (kink G.f j) ∧
      (G.f i).eval (kink G.f i) < (G.f j).eval (kink G.f i))) := by
  unfold E3_bool at hE
  rw [decide_eq_true_eq] at hE
  refine ⟨hE.1, ?_⟩
  rcases lt_or_gt_of_ne hE.1 with hij | hji
  · left
    have hcard : (Z_set G.f i j).card = 3 := by
      simpa [min_eq_left (le_of_lt hij), max_eq_right (le_of_lt hij)] using hE.2
    have hconc : (G.f i).c < (G.f j).c := by
      by_contra hnot
      have hne : (G.f j).c ≠ (G.f i).c := fun h =>
        (ne_of_lt hij) (congrArg Prod.fst (G.slopes_inj (a₁ := (i, true)) (a₂ := (j, true)) h.symm))
      have hinv : (G.f j).c < (G.f i).c := lt_of_le_of_ne (not_lt.mp hnot) hne
      have := (Z_set_inv_spec G hij hinv).1
      omega
    exact ⟨hij, hconc, (Z_set_conc_spec G hij hconc).2.mp hcard⟩
  · right
    have hcard : (Z_set G.f j i).card = 3 := by
      simpa [min_eq_right (le_of_lt hji), max_eq_left (le_of_lt hji)] using hE.2
    have hconc : (G.f j).c < (G.f i).c := by
      by_contra hnot
      have hne : (G.f i).c ≠ (G.f j).c := fun h =>
        (ne_of_lt hji) (congrArg Prod.fst (G.slopes_inj (a₁ := (j, true)) (a₂ := (i, true)) h.symm))
      have hinv : (G.f i).c < (G.f j).c := lt_of_le_of_ne (not_lt.mp hnot) hne
      have := (Z_set_inv_spec G hji hinv).1
      omega
    exact ⟨hji, hconc, (Z_set_conc_spec G hji hconc).2.mp hcard⟩

def dL_nat (G : GenericVSystem) : ℕ :=
  if E3_bool G 0 4 && E3_bool G 1 4 && E3_bool G 2 4 then 1 else 0

def dR_nat (G : GenericVSystem) : ℕ :=
  if E3_bool G (cPerm G 0) (cPerm G 2) &&
     E3_bool G (cPerm G 0) (cPerm G 3) &&
     E3_bool G (cPerm G 0) (cPerm G 4) then 1 else 0

lemma sigma_first_ne_4 {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H) :
    cPerm G 0 ≠ 4 := by
  intro h0
  have hinv4 : 4 ≤ permInvCount5 (cPerm G) := v_sigma1_ne_5_and_top2_ne_45.1 (cPerm G) h0
  rw [cPerm_invCount_eq G] at hinv4
  have hsymm4 : (cPerm G).symm 4 = 0 := by rw [← h0]; simp
  have hsymm0_ne : (cPerm G).symm 0 ≠ 0 := by
    intro heq
    have : (cPerm G) ((cPerm G).symm 0) = (cPerm G) 0 := congrArg (cPerm G) heq
    simp [h0] at this
  have h0_lt : (0 : Fin 5) < (cPerm G).symm 0 :=
    lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hsymm0_ne)
  have hinv_c : (G.f 4).c < (G.f 0).c := by
    have := cPerm_lt_iff G 0 ((cPerm G).symm 0) |>.mp h0_lt
    simpa [h0] using this
  have h_kink0 : (G.f 0).eval (kink G.f 0) < (G.f 4).eval (kink G.f 0) :=
    (Z_set_inv_spec G (by decide : (0 : Fin 5) < 4) hinv_c).2
  obtain ⟨τm, hτmX, hτm_k, hτm_ord⟩ := exists_tau_minus G
  obtain ⟨τp, hτpX, hτp_k, hτp_ord⟩ := exists_tau_plus G
  have h12 : τm < kink G.f 0 := hτm_k 0
  have h23 : kink G.f 0 < τp := hτp_k 0
  have hΦm : Φ G.f {4} τm := by
    intro u hu v hv
    rw [Finset.mem_singleton.mp hu]
    have hv4 : v < 4 := lt_of_le_of_ne (Fin.le_last v) (fun h => hv (Finset.mem_singleton.mpr h))
    exact hτm_ord v 4 hv4
  have hnΦ : ¬ Φ G.f {4} (kink G.f 0) := by
    intro hΦ
    have := hΦ 4 (Finset.mem_singleton_self _) 0 (by decide)
    linarith
  have hΦp : Φ G.f {4} τp := by
    intro u hu v hv
    rw [Finset.mem_singleton.mp hu]
    have hvne : (cPerm G).symm v ≠ 0 := by
      intro heq
      apply hv; rw [Finset.mem_singleton, ← h0, ← heq]; simp
    have h0r : (0 : Fin 5) < (cPerm G).symm v :=
      lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hvne)
    have := hτp_ord 0 ((cPerm G).symm v) h0r
    simpa [h0] using this
  have hΔ := W.h_split_cert {4} τm (kink G.f 0) τp (Or.inl (Finset.card_singleton 4))
    h12 h23 hτmX (kink_not_mem_X_cross G 0) hτpX hΦm hnΦ hΦp
  simp only [Finset.card_singleton, ↓reduceIte] at hΔ
  have hn5 := hull_n_ge_5 H
  have hcons := W.h_cons
  omega

lemma sigma_top2_ne_34 {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H) :
    ({cPerm G 0, cPerm G 1} : Finset (Fin 5)) ≠ {3, 4} := by
  intro heq
  have hinv6 : 6 ≤ permInvCount5 (cPerm G) := v_sigma1_ne_5_and_top2_ne_45.2.2 (cPerm G) heq
  rw [cPerm_invCount_eq G] at hinv6
  have hn5 := hull_n_ge_5 H
  have hcons := W.h_cons
  omega

lemma left_cert_witness (G : GenericVSystem) (hdL : dL_nat G = 1) :
    ∃ (M : Finset (Fin 5)) (τ₁ τ₂ τ₃ : ℝ),
      (M = {4} ∨ M = {3, 4}) ∧ (M.card = 1 ∨ M.card = 2) ∧
      τ₁ < τ₂ ∧ τ₂ < τ₃ ∧
      τ₁ ∉ X_cross G.f ∧ τ₂ ∉ X_cross G.f ∧ τ₃ ∉ X_cross G.f ∧
      Φ G.f M τ₁ ∧ ¬ Φ G.f M τ₂ ∧ Φ G.f M τ₃ := by
  have hE : E3_bool G 0 4 = true ∧ E3_bool G 1 4 = true ∧ E3_bool G 2 4 = true := by
    unfold dL_nat at hdL
    split_ifs at hdL with h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hc0 : kink G.f 0 < kink G.f 4 ∧ (G.f 0).eval (kink G.f 0) < (G.f 4).eval (kink G.f 0) ∧
      (G.f 4).eval (kink G.f 4) < (G.f 0).eval (kink G.f 4) := by
    rcases (E3_bool_conc G hE.1).2 with ⟨_, _, h⟩ | ⟨h40, _⟩
    · exact h
    · exact absurd h40 (by decide)
  have hc1 : (G.f 4).eval (kink G.f 4) < (G.f 1).eval (kink G.f 4) := by
    rcases (E3_bool_conc G hE.2.1).2 with ⟨_, _, _, _, h⟩ | ⟨h41, _⟩
    · exact h
    · exact absurd h41 (by decide)
  have hc2 : (G.f 4).eval (kink G.f 4) < (G.f 2).eval (kink G.f 4) := by
    rcases (E3_bool_conc G hE.2.2).2 with ⟨_, _, _, _, h⟩ | ⟨h42, _⟩
    · exact h
    · exact absurd h42 (by decide)
  obtain ⟨τm, hτmX, hτm_k, hτm_ord⟩ := exists_tau_minus G
  rcases lt_or_gt_of_ne (G.gpa_vals 4 3 (by decide)) with h43 | h34
  · refine ⟨{4}, τm, kink G.f 0, kink G.f 4, Or.inl rfl, Or.inl (by decide),
      hτm_k 0, hc0.1, hτmX, kink_not_mem_X_cross G 0, kink_not_mem_X_cross G 4, ?_, ?_, ?_⟩
    · intro u hu v hv
      rw [Finset.mem_singleton.mp hu]
      exact hτm_ord v 4 (lt_of_le_of_ne (Fin.le_last v) (fun h => hv (Finset.mem_singleton.mpr h)))
    · intro hΦ
      have := hΦ 4 (Finset.mem_singleton_self _) 0 (by decide)
      linarith [hc0.2.1]
    · intro u hu v hv
      rw [Finset.mem_singleton.mp hu]
      fin_cases v
      · exact hc0.2.2
      · exact hc1
      · exact hc2
      · exact h43
      · exact absurd (Finset.mem_singleton_self 4) hv
  · refine ⟨{3, 4}, τm, kink G.f 0, kink G.f 4, Or.inr rfl, Or.inr (by decide),
      hτm_k 0, hc0.1, hτmX, kink_not_mem_X_cross G 0, kink_not_mem_X_cross G 4, ?_, ?_, ?_⟩
    · intro u hu v hv
      have hu34 : u = 3 ∨ u = 4 := by simpa using hu
      have hv012 : v = 0 ∨ v = 1 ∨ v = 2 := by
        fin_cases v <;> simp at hv ⊢
      rcases hu34 with rfl | rfl <;> rcases hv012 with rfl | rfl | rfl <;>
        exact hτm_ord _ _ (by decide)
    · intro hΦ
      have := hΦ 4 (by decide) 0 (by decide)
      linarith [hc0.2.1]
    · intro u hu v hv
      have hu34 : u = 3 ∨ u = 4 := by simpa using hu
      have hv012 : v = 0 ∨ v = 1 ∨ v = 2 := by
        fin_cases v <;> simp at hv ⊢
      have huv : (G.f u).eval (kink G.f 4) ≤ (G.f 4).eval (kink G.f 4) := by
        rcases hu34 with rfl | rfl <;> linarith
      rcases hv012 with rfl | rfl | rfl
      · linarith [hc0.2.2]
      · linarith [hc1]
      · linarith [hc2]

lemma right_cert_witness (G : GenericVSystem) (hdR : dR_nat G = 1) :
    ∃ (M : Finset (Fin 5)) (τ₁ τ₂ τ₃ : ℝ),
      (M = {cPerm G 0} ∨ M = {cPerm G 0, cPerm G 1}) ∧ (M.card = 1 ∨ M.card = 2) ∧
      τ₁ < τ₂ ∧ τ₂ < τ₃ ∧
      τ₁ ∉ X_cross G.f ∧ τ₂ ∉ X_cross G.f ∧ τ₃ ∉ X_cross G.f ∧
      Φ G.f M τ₁ ∧ ¬ Φ G.f M τ₂ ∧ Φ G.f M τ₃ := by
  let s0 := cPerm G 0
  let s1 := cPerm G 1
  let s2 := cPerm G 2
  let s3 := cPerm G 3
  let s4 := cPerm G 4
  have hE : E3_bool G s0 s2 = true ∧ E3_bool G s0 s3 = true ∧ E3_bool G s0 s4 = true := by
    unfold dR_nat at hdR
    split_ifs at hdR with h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hE_conc : ∀ r : Fin 5, (0 : Fin 5) < r → E3_bool G s0 (cPerm G r) = true →
      kink G.f s0 < kink G.f (cPerm G r) ∧
      (G.f s0).eval (kink G.f s0) < (G.f (cPerm G r)).eval (kink G.f s0) ∧
      (G.f (cPerm G r)).eval (kink G.f (cPerm G r)) < (G.f s0).eval (kink G.f (cPerm G r)) := by
    intro r h0r hEr
    rcases (E3_bool_conc G hEr).2 with ⟨_, _, h⟩ | ⟨_, hc, _⟩
    · exact h
    · exact absurd hc (not_lt.mpr (le_of_lt (cPerm_strictMono G h0r)))
  have hc2 := hE_conc 2 (by decide) hE.1
  have hc3 := hE_conc 3 (by decide) hE.2.1
  have hc4 := hE_conc 4 (by decide) hE.2.2
  obtain ⟨τp, hτpX, hτp_k, hτp_ord⟩ := exists_tau_plus G
  have hs01 : s0 ≠ s1 := (cPerm G).injective.ne (by decide)
  rcases lt_or_gt_of_ne (G.gpa_vals s0 s1 hs01) with h01 | h10
  · refine ⟨{s0}, kink G.f s0, kink G.f s4, τp, Or.inl rfl, Or.inl (Finset.card_singleton s0),
      hc4.1, hτp_k s4, kink_not_mem_X_cross G s0, kink_not_mem_X_cross G s4, hτpX, ?_, ?_, ?_⟩
    · intro u hu v hv
      rw [Finset.mem_singleton.mp hu]
      have hv_ne : v ≠ s0 := fun h => hv (Finset.mem_singleton.mpr h)
      have hsym : (cPerm G).symm v ≠ 0 := fun h => hv_ne (by simpa [s0] using congrArg (cPerm G) h)
      generalize hr : (cPerm G).symm v = idx
      fin_cases idx
      · exact absurd hr hsym
      · have hveq : v = s1 := by simpa [s1] using congrArg (cPerm G) hr
        rwa [hveq]
      · have hveq : v = s2 := by simpa [s2] using congrArg (cPerm G) hr
        rw [hveq]; exact hc2.2.1
      · have hveq : v = s3 := by simpa [s3] using congrArg (cPerm G) hr
        rw [hveq]; exact hc3.2.1
      · have hveq : v = s4 := by simpa [s4] using congrArg (cPerm G) hr
        rw [hveq]; exact hc4.2.1
    · intro hΦ
      have hs40 : s4 ≠ s0 := (cPerm G).injective.ne (by decide)
      have := hΦ s0 (Finset.mem_singleton_self _) s4 (by simp [hs40])
      linarith [hc4.2.2]
    · intro u hu v hv
      rw [Finset.mem_singleton.mp hu]
      have hv_ne : v ≠ s0 := fun h => hv (Finset.mem_singleton.mpr h)
      have hsym : (cPerm G).symm v ≠ 0 := fun h => hv_ne (by simpa [s0] using congrArg (cPerm G) h)
      have h0r : (0 : Fin 5) < (cPerm G).symm v :=
        lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hsym)
      have := hτp_ord 0 ((cPerm G).symm v) h0r
      simpa [s0] using this
  · refine ⟨{s0, s1}, kink G.f s0, kink G.f s4, τp, Or.inr rfl, Or.inr (Finset.card_pair hs01),
      hc4.1, hτp_k s4, kink_not_mem_X_cross G s0, kink_not_mem_X_cross G s4, hτpX, ?_, ?_, ?_⟩
    · intro u hu v hv
      have hu01 : u = s0 ∨ u = s1 := by simpa using hu
      have huv : (G.f u).eval (kink G.f s0) ≤ (G.f s0).eval (kink G.f s0) := by
        rcases hu01 with rfl | rfl <;> linarith
      have hv0 : v ≠ s0 := fun h => hv (by simp [h])
      have hv1 : v ≠ s1 := fun h => hv (by simp [h])
      have hsym0 : (cPerm G).symm v ≠ 0 := fun h => hv0 (by simpa [s0] using congrArg (cPerm G) h)
      have hsym1 : (cPerm G).symm v ≠ 1 := fun h => hv1 (by simpa [s1] using congrArg (cPerm G) h)
      generalize hr : (cPerm G).symm v = idx
      fin_cases idx
      · exact absurd hr hsym0
      · exact absurd hr hsym1
      · have hveq : v = s2 := by simpa [s2] using congrArg (cPerm G) hr
        rw [hveq]; linarith [hc2.2.1]
      · have hveq : v = s3 := by simpa [s3] using congrArg (cPerm G) hr
        rw [hveq]; linarith [hc3.2.1]
      · have hveq : v = s4 := by simpa [s4] using congrArg (cPerm G) hr
        rw [hveq]; linarith [hc4.2.1]
    · intro hΦ
      have hs40 : s4 ≠ s0 := (cPerm G).injective.ne (by decide)
      have hs41 : s4 ≠ s1 := (cPerm G).injective.ne (by decide)
      have := hΦ s0 (by simp) s4 (by simp [hs40, hs41])
      linarith [hc4.2.2]
    · intro u hu v hv
      have hu01 : u = s0 ∨ u = s1 := by simpa using hu
      have hv0 : v ≠ s0 := fun h => hv (by simp [h])
      have hv1 : v ≠ s1 := fun h => hv (by simp [h])
      have hsym0 : (cPerm G).symm v ≠ 0 := fun h => hv0 (by simpa [s0] using congrArg (cPerm G) h)
      have hsym1 : (cPerm G).symm v ≠ 1 := fun h => hv1 (by simpa [s1] using congrArg (cPerm G) h)
      have h_ge2 : (1 : Fin 5) < (cPerm G).symm v := by
        generalize hr : (cPerm G).symm v = idx
        fin_cases idx
        · exact absurd hr hsym0
        · exact absurd hr hsym1
        all_goals decide
      rcases hu01 with rfl | rfl
      · have := hτp_ord 0 ((cPerm G).symm v) (lt_trans (by decide : (0 : Fin 5) < 1) h_ge2)
        simpa [s0] using this
      · have := hτp_ord 1 ((cPerm G).symm v) h_ge2
        simpa [s1] using this

lemma left_right_cert_to_delta {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H) :
    dL_nat G + dR_nat G ≤ W.Δ1 + W.Δ2 := by
  have hdL_le : dL_nat G ≤ 1 := by unfold dL_nat; split_ifs <;> omega
  have hdR_le : dR_nat G ≤ 1 := by unfold dR_nat; split_ifs <;> omega
  by_cases hL : dL_nat G = 1
  · by_cases hR : dR_nat G = 1
    · obtain ⟨ML, τ1, τ2, τ3, hML_eq, hMLc, h12, h23, hX1, hX2, hX3, hP1, hP2, hP3⟩ :=
        left_cert_witness G hL
      obtain ⟨MR, τ1', τ2', τ3', hMR_eq, hMRc, h12', h23', hX1', hX2', hX3', hP1', hP2', hP3'⟩ :=
        right_cert_witness G hR
      have hne : ML ≠ MR := by
        intro heq
        have hs0 := sigma_first_ne_4 W
        have hs01 := sigma_top2_ne_34 W
        rcases hML_eq with rfl | rfl <;> rcases hMR_eq with rfl | rfl
        · exact hs0 (Finset.singleton_injective heq).symm
        · have hc := congrArg Finset.card heq
          have hs01_ne : cPerm G 0 ≠ cPerm G 1 := (cPerm G).injective.ne (by decide)
          rw [Finset.card_singleton, Finset.card_pair hs01_ne] at hc; omega
        · have hc := congrArg Finset.card heq
          rw [Finset.card_pair (by decide : (3 : Fin 5) ≠ 4), Finset.card_singleton] at hc; omega
        · exact hs01 heq.symm
      have h2 := W.h_two_split_cert ML MR τ1 τ2 τ3 τ1' τ2' τ3'
        hMLc hMRc hne h12 h23 hX1 hX2 hX3 hP1 hP2 hP3 h12' h23' hX1' hX2' hX3' hP1' hP2' hP3'
      omega
    · obtain ⟨ML, τ1, τ2, τ3, _, hMLc, h12, h23, hX1, hX2, hX3, hP1, hP2, hP3⟩ :=
        left_cert_witness G hL
      have h1 := W.h_split_cert ML τ1 τ2 τ3 hMLc h12 h23 hX1 hX2 hX3 hP1 hP2 hP3
      have hR0 : dR_nat G = 0 := by omega
      rcases hMLc with hc | hc <;> rw [hc] at h1 <;> simp at h1 <;> omega
  · have hL0 : dL_nat G = 0 := by omega
    by_cases hR : dR_nat G = 1
    · obtain ⟨MR, τ1', τ2', τ3', _, hMRc, h12', h23', hX1', hX2', hX3', hP1', hP2', hP3'⟩ :=
        right_cert_witness G hR
      have h1 := W.h_split_cert MR τ1' τ2' τ3' hMRc h12' h23' hX1' hX2' hX3' hP1' hP2' hP3'
      rcases hMRc with hc | hc <;> rw [hc] at h1 <;> simp at h1 <;> omega
    · omega

private def pack5 (b0 b1 b2 b3 b4 : Bool) : Nat :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
  (if b3 then 8 else 0) + (if b4 then 16 else 0)

private lemma pack5_spec (b0 b1 b2 b3 b4 : Bool) :
    pack5 b0 b1 b2 b3 b4 < 32 ∧
    Nat.beq ((pack5 b0 b1 b2 b3 b4 >>> 0) &&& 1) 1 = b0 ∧
    Nat.beq ((pack5 b0 b1 b2 b3 b4 >>> 1) &&& 1) 1 = b1 ∧
    Nat.beq ((pack5 b0 b1 b2 b3 b4 >>> 2) &&& 1) 1 = b2 ∧
    Nat.beq ((pack5 b0 b1 b2 b3 b4 >>> 3) &&& 1) 1 = b3 ∧
    Nat.beq ((pack5 b0 b1 b2 b3 b4 >>> 4) &&& 1) 1 = b4 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private def checkHiLoBit : Bool :=
  (List.range 32).all fun hi =>
    (List.range 32).all fun lo =>
      let gMask := (hi <<< 5) ||| lo
      (List.range 10).all fun k =>
        let bit := Nat.beq ((gMask >>> k) &&& 1) 1
        if Nat.blt k 5 then bit == Nat.beq ((lo >>> k) &&& 1) 1
        else bit == Nat.beq ((hi >>> (k - 5)) &&& 1) 1

private lemma hi_lo_bit_spec : checkHiLoBit = true := by decide +kernel

private lemma perm_mem_perms5_aux :
    (List.range 5).all (fun s0 =>
      (List.range 5).all fun s1 =>
        (List.range 5).all fun s2 =>
          (List.range 5).all fun s3 =>
            (List.range 5).all fun s4 =>
              if Nat.beq s0 s1 || Nat.beq s0 s2 || Nat.beq s0 s3 || Nat.beq s0 s4 ||
                 Nat.beq s1 s2 || Nat.beq s1 s3 || Nat.beq s1 s4 ||
                 Nat.beq s2 s3 || Nat.beq s2 s4 || Nat.beq s3 s4 then true
              else perms5.contains (s0, s1, s2, s3, s4)) = true := by
  decide +kernel

private lemma perm_mem_perms5 (s0 s1 s2 s3 s4 : Fin 5)
    (h01 : s0 ≠ s1) (h02 : s0 ≠ s2) (h03 : s0 ≠ s3) (h04 : s0 ≠ s4)
    (h12 : s1 ≠ s2) (h13 : s1 ≠ s3) (h14 : s1 ≠ s4)
    (h23 : s2 ≠ s3) (h24 : s2 ≠ s4) (h34 : s3 ≠ s4) :
    (s0.val, s1.val, s2.val, s3.val, s4.val) ∈ perms5 := by
  have hm := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp perm_mem_perms5_aux
      s0.val (List.mem_range.mpr s0.isLt))
      s1.val (List.mem_range.mpr s1.isLt))
      s2.val (List.mem_range.mpr s2.isLt))
      s3.val (List.mem_range.mpr s3.isLt))
      s4.val (List.mem_range.mpr s4.isLt)
  have hbeq : ∀ a b : Fin 5, a ≠ b → Nat.beq a.val b.val = false := fun a b hab =>
    Bool.eq_false_iff.mpr fun h => hab (Fin.ext (Nat.beq_eq.mp h))
  have hcond : (Nat.beq s0.val s1.val || Nat.beq s0.val s2.val || Nat.beq s0.val s3.val ||
      Nat.beq s0.val s4.val || Nat.beq s1.val s2.val || Nat.beq s1.val s3.val ||
      Nat.beq s1.val s4.val || Nat.beq s2.val s3.val || Nat.beq s2.val s4.val ||
      Nat.beq s3.val s4.val) = false := by
    simp [hbeq _ _ h01, hbeq _ _ h02, hbeq _ _ h03, hbeq _ _ h04,
          hbeq _ _ h12, hbeq _ _ h13, hbeq _ _ h14,
          hbeq _ _ h23, hbeq _ _ h24, hbeq _ _ h34]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem] at hm
  exact of_decide_eq_true hm

lemma left_right_lower_bound {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H) :
    2 ≤ T3bar G + T1 G + dL_nat G + dR_nat G := by
  let lo := pack5 (E3_bool G 0 1) (E3_bool G 0 2) (E3_bool G 0 3) (E3_bool G 0 4) (E3_bool G 1 2)
  let hi := pack5 (E3_bool G 1 3) (E3_bool G 1 4) (E3_bool G 2 3) (E3_bool G 2 4) (E3_bool G 3 4)
  have hlo := pack5_spec (E3_bool G 0 1) (E3_bool G 0 2) (E3_bool G 0 3) (E3_bool G 0 4) (E3_bool G 1 2)
  have hhi := pack5_spec (E3_bool G 1 3) (E3_bool G 1 4) (E3_bool G 2 3) (E3_bool G 2 4) (E3_bool G 3 4)
  let gMask := (hi <<< 5) ||| lo
  have hbit_eq : ∀ i j : Fin 5, i < j →
      Nat.beq ((gMask >>> pairBitIdx i.val j.val) &&& 1) 1 = E3_bool G i j := by
    have hhl := List.all_eq_true.mp hi_lo_bit_spec hi (List.mem_range.mpr hhi.1)
    have hhl2 := List.all_eq_true.mp hhl lo (List.mem_range.mpr hlo.1)
    intro i j hij
    have hk : ∀ k < 10, Nat.beq ((gMask >>> k) &&& 1) 1 =
        if k < 5 then Nat.beq ((lo >>> k) &&& 1) 1 else Nat.beq ((hi >>> (k - 5)) &&& 1) 1 := by
      intro k hk10
      have hk' := List.all_eq_true.mp hhl2 k (List.mem_range.mpr hk10)
      by_cases hk5 : k < 5
      · simp only [Nat.blt_eq, hk5, ↓reduceIte, beq_iff_eq] at hk' ⊢; exact hk'
      · simp only [Nat.blt_eq, hk5, ↓reduceIte, beq_iff_eq] at hk' ⊢; exact hk'
    have hk_lo : ∀ k < 5, Nat.beq ((gMask >>> k) &&& 1) 1 = Nat.beq ((lo >>> k) &&& 1) 1 :=
      fun k hk5 => by simpa [hk5] using hk k (by omega)
    have hk_hi : ∀ k, 5 ≤ k → k < 10 →
        Nat.beq ((gMask >>> k) &&& 1) 1 = Nat.beq ((hi >>> (k - 5)) &&& 1) 1 :=
      fun k hk5 hk10 => by
        have hnot : ¬ (k < 5) := by omega
        simpa [hnot] using hk k hk10
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | (rw [hk_lo _ (by decide)];
         first | exact hlo.2.1 | exact hlo.2.2.1 | exact hlo.2.2.2.1 | exact hlo.2.2.2.2.1 | exact hlo.2.2.2.2.2)
      | (rw [hk_hi _ (by decide) (by decide)];
         first | exact hhi.2.1 | exact hhi.2.2.1 | exact hhi.2.2.2.1 | exact hhi.2.2.2.2.1 | exact hhi.2.2.2.2.2)
  let σ := cPerm G
  have h_all_true := v_left_right_cert_bound
  unfold checkLeftRightCertBound at h_all_true
  have h1 := List.all_eq_true.mp h_all_true hi (List.mem_range.mpr hhi.1)
  have h2 := List.all_eq_true.mp h1 lo (List.mem_range.mpr hlo.1)
  have hperm_mem : ((σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val, (σ 4).val) ∈ perms5 :=
    perm_mem_perms5 (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
      (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) (σ.injective.ne (by decide))
  have h3 := List.all_eq_true.mp h2 _ hperm_mem
  dsimp only at h3
  have hs0_ne4 : σ 0 ≠ 4 := sigma_first_ne_4 W
  have hs01_ne34 : ({σ 0, σ 1} : Finset (Fin 5)) ≠ {3, 4} := sigma_top2_ne_34 W
  have hskip : (Nat.beq (σ 0).val 4 ||
      ((Nat.beq (σ 0).val 3 && Nat.beq (σ 1).val 4) ||
       (Nat.beq (σ 0).val 4 && Nat.beq (σ 1).val 3))) = false := by
    by_contra htrue
    have htrue' : _ = true := Bool.eq_true_of_not_eq_false htrue
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at htrue'
    rcases htrue' with h4 | (⟨h3', h4'⟩ | ⟨h4', h3'⟩)
    · exact hs0_ne4 (Fin.ext h4)
    · apply hs01_ne34
      have h0 : σ 0 = 3 := Fin.ext h3'
      have h1 : σ 1 = 4 := Fin.ext h4'
      rw [h0, h1]
    · apply hs01_ne34
      have h0 : σ 0 = 4 := Fin.ext h4'
      have h1 : σ 1 = 3 := Fin.ext h3'
      rw [h0, h1, Finset.pair_comm]
  rw [hskip] at h3
  simp only [Bool.false_eq_true, ↓reduceIte] at h3
  let invAt : Nat → Nat := fun x =>
    if Nat.beq x (σ 0).val then 0
    else if Nat.beq x (σ 1).val then 1
    else if Nat.beq x (σ 2).val then 2
    else if Nat.beq x (σ 3).val then 3
    else 4
  have hinvAt : ∀ x : Fin 5, invAt x.val = (σ.symm x).val := by
    intro x
    generalize hr : σ.symm x = idx
    fin_cases idx
    · have hx : x = σ 0 := by have := congrArg σ hr; simpa using this
      rw [hx]; dsimp [invAt]; simp
    · have hx : x = σ 1 := by have := congrArg σ hr; simpa using this
      have h01 : (σ 1).val ≠ (σ 0).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      rw [hx]; dsimp [invAt]; simp [Nat.beq_eq, h01]
    · have hx : x = σ 2 := by have := congrArg σ hr; simpa using this
      have h02 : (σ 2).val ≠ (σ 0).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      have h12 : (σ 2).val ≠ (σ 1).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      rw [hx]; dsimp [invAt]; simp [Nat.beq_eq, h02, h12]
    · have hx : x = σ 3 := by have := congrArg σ hr; simpa using this
      have h03 : (σ 3).val ≠ (σ 0).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      have h13 : (σ 3).val ≠ (σ 1).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      have h23 : (σ 3).val ≠ (σ 2).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      rw [hx]; dsimp [invAt]; simp [Nat.beq_eq, h03, h13, h23]
    · have hx : x = σ 4 := by have := congrArg σ hr; simpa using this
      have h04 : (σ 4).val ≠ (σ 0).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      have h14 : (σ 4).val ≠ (σ 1).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      have h24 : (σ 4).val ≠ (σ 2).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      have h34 : (σ 4).val ≠ (σ 3).val := Fin.val_ne_of_ne (σ.injective.ne (by decide))
      rw [hx]; dsimp [invAt]; simp [Nat.beq_eq, h04, h14, h24, h34]
  let pairs : List (Nat × Nat) :=
    [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
  have hinvOk : (pairs.all fun (i, j) =>
      if Nat.blt (invAt j) (invAt i) then !(Nat.beq ((gMask >>> pairBitIdx i j) &&& 1) 1) else true) = true := by
    rw [List.all_eq_true]
    rintro ⟨i, j⟩ hp
    have hij_lt : ∃ i' j' : Fin 5, i' < j' ∧ i = i'.val ∧ j = j'.val := by
      simp only [pairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, 1, by decide, rfl, rfl⟩
      · exact ⟨0, 2, by decide, rfl, rfl⟩
      · exact ⟨0, 3, by decide, rfl, rfl⟩
      · exact ⟨0, 4, by decide, rfl, rfl⟩
      · exact ⟨1, 2, by decide, rfl, rfl⟩
      · exact ⟨1, 3, by decide, rfl, rfl⟩
      · exact ⟨1, 4, by decide, rfl, rfl⟩
      · exact ⟨2, 3, by decide, rfl, rfl⟩
      · exact ⟨2, 4, by decide, rfl, rfl⟩
      · exact ⟨3, 4, by decide, rfl, rfl⟩
    obtain ⟨i', j', hij', rfl, rfl⟩ := hij_lt
    dsimp only
    rw [hinvAt i', hinvAt j', hbit_eq i' j' hij']
    split_ifs with hblt
    · simp only [Bool.not_eq_true']
      rw [Nat.blt_eq] at hblt
      have hc : (G.f j').c < (G.f i').c := by
        simpa [σ] using (cPerm_lt_iff G (σ.symm j') (σ.symm i')).mp hblt
      by_contra hE_true
      have hE' := Bool.eq_true_of_not_eq_false hE_true
      rcases (E3_bool_conc G hE').2 with ⟨_, hci, _⟩ | ⟨hji, _⟩
      · linarith
      · exact absurd hij' (not_lt.mpr (le_of_lt hji))
    · rfl
  change (if !(pairs.all _) then true else _) = true at h3
  rw [hinvOk] at h3
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.ble_eq] at h3
  have hE_symm : ∀ a b : Fin 5, a ≠ b →
      Nat.beq ((gMask >>> pairBitIdx a.val b.val) &&& 1) 1 = E3_bool G a b := by
    intro a b hab_ne
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact hbit_eq a b hab
    · exact absurd rfl hab_ne
    · have hp_comm : pairBitIdx a.val b.val = pairBitIdx b.val a.val := by
        fin_cases a <;> fin_cases b <;> decide
      rw [hp_comm, hbit_eq b a hba, E3_bool_symm]
  let pairList : List (Fin 5 × Fin 5) :=
    [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
  have hpair_nodup : pairList.Nodup := by decide
  have hpair_mem : ∀ p : Fin 5 × Fin 5, p ∈ pairList ↔ p ∈ pair5 := by decide
  have hpair_map : pairs = pairList.map (fun p => (p.1.val, p.2.val)) := rfl
  have hT3bar_eq : (pairs.filter fun (i, j) =>
      !(Nat.beq ((gMask >>> pairBitIdx i j) &&& 1) 1)).length = T3bar G := by
    rw [hpair_map, List.filter_map, List.length_map]
    dsimp only [Function.comp_def]
    have h_filt : pairList.filter (fun p : Fin 5 × Fin 5 =>
        !(Nat.beq ((gMask >>> pairBitIdx p.1.val p.2.val) &&& 1) 1)) =
        pairList.filter (fun p : Fin 5 × Fin 5 => !(E3_bool G p.1 p.2)) := by
      apply List.filter_congr; intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp ((hpair_mem p).mp hp)).2
      rw [hbit_eq p.1 p.2 hlt]
    rw [h_filt, ← List.toFinset_card_of_nodup (hpair_nodup.filter _)]
    have h_fs : (pairList.filter (fun p => !(E3_bool G p.1 p.2))).toFinset = pair5 \ E_G3 G := by
      apply Finset.ext; intro p
      rw [List.mem_toFinset, List.mem_filter, hpair_mem, Finset.mem_sdiff]
      constructor
      · rintro ⟨hp, hnot⟩
        have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        refine ⟨hp, fun h => ?_⟩
        have hcard : (Z_set G.f p.1 p.2).card = 3 := (Finset.mem_filter.mp h).2
        have hE : E3_bool G p.1 p.2 = true := by
          simp [E3_bool, ne_of_lt hlt, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt), hcard]
        rw [hE] at hnot; simp at hnot
      · rintro ⟨hp, hnot⟩
        have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
        refine ⟨hp, ?_⟩
        by_contra hE
        have hE' : E3_bool G p.1 p.2 = true := Bool.eq_true_of_not_eq_false (by simpa using hE)
        have hcard : (Z_set G.f p.1 p.2).card = 3 := by
          simpa [E3_bool, ne_of_lt hlt, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)] using hE'
        exact hnot (Finset.mem_filter.mpr ⟨hp, hcard⟩)
    rw [h_fs]
    unfold E_G3
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), pair5_card]
    rfl
  have hT1_eq : (pairs.filter fun (i, j) =>
      Nat.blt (invAt i) (invAt j) && !(Nat.beq ((gMask >>> pairBitIdx i j) &&& 1) 1)).length = T1 G := by
    rw [hpair_map, List.filter_map, List.length_map]
    dsimp only [Function.comp_def]
    have h_filt : pairList.filter (fun p : Fin 5 × Fin 5 =>
        Nat.blt (invAt p.1.val) (invAt p.2.val) &&
        !(Nat.beq ((gMask >>> pairBitIdx p.1.val p.2.val) &&& 1) 1)) =
        pairList.filter (fun p : Fin 5 × Fin 5 =>
          decide ((G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1)) := by
      apply List.filter_congr; intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp ((hpair_mem p).mp hp)).2
      simp only [hinvAt p.1, hinvAt p.2, hbit_eq p.1 p.2 hlt]
      have hc_iff : σ.symm p.1 < σ.symm p.2 ↔ (G.f p.1).c < (G.f p.2).c := by
        simpa [σ] using cPerm_lt_iff G (σ.symm p.1) (σ.symm p.2)
      by_cases hc : (G.f p.1).c < (G.f p.2).c
      · have hblt : Nat.blt (σ.symm p.1).val (σ.symm p.2).val = true :=
          Nat.blt_eq.mpr (Fin.lt_def.mp (hc_iff.mpr hc))
        rcases (Z_set_conc_spec G hlt hc).1 with h1 | h3
        · have hE : E3_bool G p.1 p.2 = false := by
            simp [E3_bool, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt), h1]
          simp [hblt, hc, h1, hE]
        · have hE : E3_bool G p.1 p.2 = true := by
            simp [E3_bool, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt), ne_of_lt hlt, h3]
          simp [hblt, hc, h3, hE]
      · have hblt : Nat.blt (σ.symm p.1).val (σ.symm p.2).val = false :=
          Bool.eq_false_iff.mpr fun h => hc (hc_iff.mp (Fin.lt_def.mp (Nat.blt_eq.mp h)))
        simp [hblt, hc]
    rw [h_filt, ← List.toFinset_card_of_nodup (hpair_nodup.filter _)]
    have h_fs : (pairList.filter (fun p : Fin 5 × Fin 5 =>
        decide ((G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1))).toFinset =
        pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1) := by
      apply Finset.ext; intro p
      rw [List.mem_toFinset, List.mem_filter, hpair_mem, Finset.mem_filter, decide_eq_true_eq]
    rw [h_fs]; rfl
  have hdL_eq : (if Nat.beq ((gMask >>> pairBitIdx 0 4) &&& 1) 1 &&
      Nat.beq ((gMask >>> pairBitIdx 1 4) &&& 1) 1 &&
      Nat.beq ((gMask >>> pairBitIdx 2 4) &&& 1) 1 then 1 else 0) = dL_nat G := by
    have h04 : Nat.beq ((gMask >>> pairBitIdx 0 4) &&& 1) 1 = E3_bool G 0 4 := hbit_eq 0 4 (by decide)
    have h14 : Nat.beq ((gMask >>> pairBitIdx 1 4) &&& 1) 1 = E3_bool G 1 4 := hbit_eq 1 4 (by decide)
    have h24 : Nat.beq ((gMask >>> pairBitIdx 2 4) &&& 1) 1 = E3_bool G 2 4 := hbit_eq 2 4 (by decide)
    rw [h04, h14, h24]; rfl
  have hdR_eq : (if Nat.beq ((gMask >>> pairBitIdx (σ 0).val (σ 2).val) &&& 1) 1 &&
      Nat.beq ((gMask >>> pairBitIdx (σ 0).val (σ 3).val) &&& 1) 1 &&
      Nat.beq ((gMask >>> pairBitIdx (σ 0).val (σ 4).val) &&& 1) 1 then 1 else 0) = dR_nat G := by
    rw [hE_symm (σ 0) (σ 2) (σ.injective.ne (by decide)),
        hE_symm (σ 0) (σ 3) (σ.injective.ne (by decide)),
        hE_symm (σ 0) (σ 4) (σ.injective.ne (by decide))]; rfl
  change 2 ≤ (pairs.filter _).length + (pairs.filter _).length + _ + _ at h3
  rw [hT3bar_eq, hT1_eq, hdL_eq, hdR_eq] at h3
  exact h3

lemma hull_n_le_7 {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H) :
    H.n ≤ 7 := by
  have h2 := left_right_lower_bound W
  have hΔ := left_right_cert_to_delta W
  have hcons := W.h_cons
  omega

/-! ## Part 4: Elimination of `n = 7` -/

private lemma perm_invCount_zero_eq_refl (σ : Equiv.Perm (Fin 5))
    (h0 : permInvCount5 σ = 0) : σ = Equiv.refl _ := by
  have hmono : ∀ a b : Fin 5, a < b → σ a < σ b := by
    intro a b hab
    by_contra hle
    have hlt : σ b < σ a := lt_of_le_of_ne (not_lt.mp hle) (σ.injective.ne (ne_of_gt hab))
    have hmem : (a, b) ∈ (Finset.univ.product Finset.univ).filter
        (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ σ p.2 < σ p.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hlt⟩
    have hpos := Finset.card_pos.mpr ⟨(a, b), hmem⟩
    change 0 < permInvCount5 σ at hpos; omega
  have h01 : (σ 0).val < (σ 1).val := hmono 0 1 (by decide)
  have h12 : (σ 1).val < (σ 2).val := hmono 1 2 (by decide)
  have h23 : (σ 2).val < (σ 3).val := hmono 2 3 (by decide)
  have h34 : (σ 3).val < (σ 4).val := hmono 3 4 (by decide)
  have h4 : (σ 4).val < 5 := (σ 4).isLt
  ext i; fin_cases i <;> dsimp <;> omega

private lemma finset_card_two_sub_eq {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    {T : Finset α} (hT : T.card = 2) (ha : a ∈ T) (hb : b ∈ T) : T = {a, b} := by
  symm
  exact Finset.eq_of_subset_of_card_le
    (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
    (by rw [Finset.card_pair hab, hT])

private lemma list_getLast!_spec : ∀ (L : List Nat), L ≠ [] → L.Pairwise (· < ·) →
    L.getLast! ∈ L ∧ ∀ x ∈ L, x ≤ L.getLast!
  | [], h, _ => absurd rfl h
  | [a], _, _ => ⟨List.mem_singleton.mpr rfl, fun x hx => by rw [List.mem_singleton.mp hx]; rfl⟩
  | a :: b :: t, _, hP => by
    have hne : b :: t ≠ [] := List.cons_ne_nil _ _
    have ih := list_getLast!_spec (b :: t) hne (List.pairwise_cons.mp hP).2
    have hlast : (a :: b :: t).getLast! = (b :: t).getLast! := rfl
    rw [hlast]
    refine ⟨List.mem_cons_of_mem a ih.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_trans (le_of_lt ((List.pairwise_cons.mp hP).1 b (List.mem_cons_self ..)))
        (ih.2 b (List.mem_cons_self ..))
    · exact ih.2 x hx'

private lemma list_head!_spec : ∀ (L : List Nat), L ≠ [] → L.Pairwise (· < ·) →
    L.head! ∈ L ∧ ∀ x ∈ L, L.head! ≤ x
  | [], h, _ => absurd rfl h
  | a :: t, _, hP => ⟨List.mem_cons_self .., fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.mp hP).1 x hx')⟩

lemma elim_n7 {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H)
    (hn7 : H.n = 7) : False := by
  have hΔ := left_right_cert_to_delta W
  have hT1_le := T1_le_T3bar G
  have hcons := W.h_cons
  have h_sum2 : T3bar G + T1 G + W.Δ1 + W.Δ2 + W.Δ3 = 2 := by omega
  have h_bound : T3bar G ≤ 2 := by omega
  interval_cases hT3 : T3bar G
  · -- Case `T3bar G = 0`: `σ = 1`, `E_G3 G = pair5`, `H.h = 7`, contradiction with `v_n7_T3bar0_diagonals_lt_5`.
    have hT1_0 : T1 G = 0 := by omega
    have hinv0 : permInvCount5 (cPerm G) = 0 := by rw [cPerm_invCount_eq G]; omega
    have hσ_id : cPerm G = Equiv.refl _ := perm_invCount_zero_eq_refl (cPerm G) hinv0
    have hc_mono : StrictMono (fun i : Fin 5 => (G.f i).c) := by
      have := cPerm_strictMono G; simpa [hσ_id] using this
    have hEG3_all : ∀ i j : Fin 5, i < j → E3_bool G i j = true := by
      intro i j hij
      have hT3_le : T3 G ≤ 10 := (Finset.card_filter_le _ _).trans_eq pair5_card
      have hcard3 : (E_G3 G).card = 10 := by dsimp [T3bar, T3] at hT3 hT3_le; omega
      have h_eq : E_G3 G = pair5 :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [pair5_card, hcard3])
      have hmem : (i, j) ∈ E_G3 G := by
        rw [h_eq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
      have hc := (Finset.mem_filter.mp hmem).2
      simp [E3_bool, ne_of_lt hij, min_eq_left (le_of_lt hij), max_eq_right (le_of_lt hij), hc]
    have h4a_lt_0c : (G.f 4).a < (G.f 0).c := by
      rcases (E3_bool_conc G (hEG3_all 0 4 (by decide))).2 with ⟨_, _, hk, h0k, h4k⟩ | ⟨h40, _⟩
      · have he0 : (G.f 0).eval (kink G.f 0) = (G.f 0).c * kink G.f 0 + (G.f 0).d :=
          VFunc.eval_right (G.f 0) (G.ac 0) le_rfl
        have hf0_k4 := VFunc.eval_right (G.f 0) (G.ac 0) (le_of_lt hk)
        have he4 : (G.f 4).eval (kink G.f 4) = (G.f 4).a * kink G.f 4 + (G.f 4).b :=
          VFunc.eval_left (G.f 4) (G.ac 4) le_rfl
        have hf4_k0 := VFunc.eval_left (G.f 4) (G.ac 4) (le_of_lt hk)
        have hlt1 : (G.f 0).c * kink G.f 0 + (G.f 0).d < (G.f 4).a * kink G.f 0 + (G.f 4).b := by linarith
        have hlt2 : (G.f 4).a * kink G.f 4 + (G.f 4).b < (G.f 0).c * kink G.f 4 + (G.f 0).d := by linarith
        nlinarith
      · exact absurd h40 (by decide)
    -- Define the 10-point sorted order `khat : Fin 10 → Fin 5 × Bool`
    let khat : Fin 10 → Fin 5 × Bool := fun idx =>
      if h : idx.val < 5 then (⟨idx.val, h⟩, false) else (⟨idx.val - 5, by omega⟩, true)
    let khatInv : Fin 5 × Bool → Fin 10 := fun p =>
      if p.2 then ⟨p.1.val + 5, by omega⟩ else ⟨p.1.val, by omega⟩
    have hkhat_left : ∀ p : Fin 5 × Bool, khat (khatInv p) = p := by
      rintro ⟨c, b⟩; fin_cases c <;> cases b <;> rfl
    have hkhat_right : ∀ idx : Fin 10, khatInv (khat idx) = idx := by
      intro idx; fin_cases idx <;> rfl
    have hkhat_mono : StrictMono (fun idx : Fin 10 => (dualPt G.f (khat idx)).1) := by
      intro i j hij
      dsimp [khat]
      split_ifs with hi hj hj
      · exact G.a_mono (by change i.val < j.val; exact hij)
      · exact lt_of_le_of_lt (G.a_mono.monotone (Fin.mk_le_mk.mpr (by omega : i.val ≤ 4)))
          (lt_of_lt_of_le h4a_lt_0c (hc_mono.monotone (Fin.mk_le_mk.mpr (by omega : 0 ≤ j.val - 5))))
      · exfalso; omega
      · exact hc_mono (by change i.val - 5 < j.val - 5; omega)
    let hullIdx : Fin H.h → Fin 10 := fun r => khatInv (H.q r)
    have hhullIdx_mono : StrictMono hullIdx := by
      intro r₁ r₂ hr
      have h1 := H.hq_mono hr
      by_contra hle
      rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hgt
      · have hq : H.q r₁ = H.q r₂ := by
          rw [← hkhat_left (H.q r₁), ← hkhat_left (H.q r₂)]
          exact congrArg khat heq.symm
        exact ne_of_lt hr (H.hq_inj hq)
      · have h2 := hkhat_mono hgt
        dsimp [hullIdx] at h2
        rw [hkhat_left, hkhat_left] at h2
        linarith
    -- Show `H.h = 7`: if `H.h ≥ 8`, some adjacent pair in `H.q` has same color, forcing 4 points in `R_int`.
    have hh_eq7 : H.h = 7 := by
      have hh_ge7 : 7 ≤ H.h := by rw [← hn7]; exact hull_n_le_h H
      by_contra hne7
      have hh_ge8 : 8 ≤ H.h := by omega
      have hex_same : ∃ r : Fin (H.h - 1),
          (H.q ⟨r.val, by omega⟩).1 = (H.q ⟨r.val + 1, by omega⟩).1 := by
        by_contra hnone
        push Not at hnone
        have h_all : Finset.univ.filter (fun r : Fin (H.h - 1) =>
            (H.q ⟨r.val, by omega⟩).1 ≠ (H.q ⟨r.val + 1, by omega⟩).1) = Finset.univ := by
          apply Finset.ext; intro r; simp [hnone r]
        have hn_eq : H.n = H.h := by
          unfold HullData.n; rw [h_all, Finset.card_univ, Fintype.card_fin]; omega
        omega
      obtain ⟨r, hr_col⟩ := hex_same
      let idx1 := hullIdx ⟨r.val, by omega⟩
      let idx2 := hullIdx ⟨r.val + 1, by omega⟩
      have h12 : idx1 < idx2 := hhullIdx_mono (by change r.val < r.val + 1; omega)
      have hq1 : H.q ⟨r.val, by omega⟩ = khat idx1 := (hkhat_left _).symm
      have hq2 : H.q ⟨r.val + 1, by omega⟩ = khat idx2 := (hkhat_left _).symm
      have h_diff5 : idx2.val = idx1.val + 5 := by
        dsimp [idx1, idx2, hullIdx, khatInv]
        have hqne : H.q ⟨r.val, by omega⟩ ≠ H.q ⟨r.val + 1, by omega⟩ :=
          H.hq_inj.ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
        cases hb1 : (H.q ⟨r.val, by omega⟩).2 <;> cases hb2 : (H.q ⟨r.val + 1, by omega⟩).2
        · exfalso; exact hqne (Prod.ext hr_col (hb1.trans hb2.symm))
        · dsimp; rw [hr_col]
        · exfalso
          have h12' : idx1.val < idx2.val := h12
          dsimp [idx1, idx2, hullIdx, khatInv] at h12'
          simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte, hr_col] at h12'
          omega
        · exfalso; exact hqne (Prod.ext hr_col (hb1.trans hb2.symm))
      let mid : Finset (Fin 10) := Finset.univ.filter (fun idx : Fin 10 => idx1 < idx ∧ idx < idx2)
      have hmid_card : mid.card = 4 := by
        have h_bij : mid = ({⟨idx1.val + 1, by omega⟩, ⟨idx1.val + 2, by omega⟩,
            ⟨idx1.val + 3, by omega⟩, ⟨idx1.val + 4, by omega⟩} : Finset (Fin 10)) := by
          apply Finset.ext; intro x
          simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.ext_iff, Fin.lt_def]
          omega
        rw [h_bij]
        rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
            Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
            Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
            Finset.card_singleton]
      have h_disj : Disjoint (Finset.univ.image hullIdx) mid := by
        rw [Finset.disjoint_left]
        intro idx h1 h2
        rcases Finset.mem_image.mp h1 with ⟨s, _, rfl⟩
        have hm := (Finset.mem_filter.mp h2).2
        rcases le_or_gt s.val r.val with hs | hs
        · have : hullIdx s ≤ idx1 := hhullIdx_mono.monotone (by change s.val ≤ r.val; exact hs)
          exact absurd (lt_of_lt_of_le hm.1 this) (lt_irrefl _)
        · have : idx2 ≤ hullIdx s := hhullIdx_mono.monotone (by change r.val + 1 ≤ s.val; omega)
          exact absurd (lt_of_le_of_lt this hm.2) (lt_irrefl _)
      have h_union_le : (Finset.univ.image hullIdx).card + mid.card ≤ (Finset.univ : Finset (Fin 10)).card := by
        rw [← Finset.card_union_of_disjoint h_disj]
        exact Finset.card_le_univ _
      rw [Finset.card_image_of_injective _ hhullIdx_mono.injective, Finset.card_univ, Fintype.card_fin,
          Finset.card_univ, Fintype.card_fin, hmid_card] at h_union_le
      omega
    -- Now `H.h = 7`, `hullIdx 0 = 0`, `hullIdx 6 = 9`, leaving 3 deleted positions `i1 < i2 < i3` in `1..8`.
    have h0_eq : hullIdx ⟨0, by omega⟩ = 0 := by
      have hmin := H.hq_min (khat 0)
      have h_eq : H.q ⟨0, by omega⟩ = khat 0 := by
        by_contra hne
        have hlt := hkhat_mono (show (0 : Fin 10) < hullIdx ⟨0, by omega⟩ from
          lt_of_le_of_ne (Fin.zero_le _) (fun h => hne (by simpa [hullIdx, hkhat_left] using congrArg khat h.symm)))
        dsimp [hullIdx] at hlt; rw [hkhat_left] at hlt; linarith
      dsimp [hullIdx]; rw [h_eq]; exact hkhat_right 0
    have h6_eq : hullIdx ⟨H.h - 1, by omega⟩ = 9 := by
      have hmax := H.hq_max (khat 9)
      have h_eq : H.q ⟨H.h - 1, by omega⟩ = khat 9 := by
        by_contra hne
        have hlt := hkhat_mono (show hullIdx ⟨H.h - 1, by omega⟩ < (9 : Fin 10) from
          lt_of_le_of_ne (Fin.le_last _) (fun h => hne (by simpa [hullIdx, hkhat_left] using congrArg khat h)))
        dsimp [hullIdx] at hlt; rw [hkhat_left] at hlt; linarith
      dsimp [hullIdx]; rw [h_eq]; exact hkhat_right 9
    let hullFinSet : Finset (Fin 10) := Finset.univ.image hullIdx
    let remFinSet : Finset (Fin 10) := Finset.univ \ hullFinSet
    have hrem_card : remFinSet.card = 3 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_image_of_injective _ hhullIdx_mono.injective, Finset.card_univ, Fintype.card_fin, hh_eq7]
    let remEmb : Fin 3 ↪o Fin 10 := remFinSet.orderEmbOfFin hrem_card
    let i1 : ℕ := (remEmb 0).val
    let i2 : ℕ := (remEmb 1).val
    let i3 : ℕ := (remEmb 2).val
    have hi_ord : i1 < i2 ∧ i2 < i3 := ⟨remEmb.strictMono (by decide), remEmb.strictMono (by decide)⟩
    have hi_bounds : ∀ t : Fin 3, 1 ≤ (remEmb t).val ∧ (remEmb t).val ≤ 8 := by
      intro t
      have ht_mem : remEmb t ∈ remFinSet := Finset.orderEmbOfFin_mem remFinSet hrem_card t
      have ht_not : remEmb t ∉ hullFinSet := (Finset.mem_sdiff.mp ht_mem).2
      have hne0 : remEmb t ≠ 0 := fun h => ht_not (h ▸ h0_eq ▸ Finset.mem_image_of_mem hullIdx (Finset.mem_univ _))
      have hne9 : remEmb t ≠ 9 := fun h => ht_not (h ▸ h6_eq ▸ Finset.mem_image_of_mem hullIdx (Finset.mem_univ _))
      have hlt10 := (remEmb t).isLt
      have hv0 : (remEmb t).val ≠ 0 := fun h => hne0 (Fin.ext h)
      have hv9 : (remEmb t).val ≠ 9 := fun h => hne9 (Fin.ext h)
      omega
    have h_chk := v_n7_T3bar0_diagonals_lt_5
    unfold checkN7T3bar0Diagonals at h_chk
    have hi1_mem : i1 ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by
      have := (hi_bounds 0).1; have := (hi_bounds 0).2
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    have hi2_mem : i2 ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by
      have := (hi_bounds 1).1; have := (hi_bounds 1).2
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    have hi3_mem : i3 ∈ [1, 2, 3, 4, 5, 6, 7, 8] := by
      have := (hi_bounds 2).1; have := (hi_bounds 2).2
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    have h_body := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h_chk i1 hi1_mem) i2 hi2_mem) i3 hi3_mem
    have hcond : (!(decide (i1 < i2) && decide (i2 < i3))) = false := by simp [hi_ord.1, hi_ord.2]
    rw [hcond] at h_body
    simp only [Bool.false_eq_true, ↓reduceIte] at h_body
    let khatArr : Array (Fin 5) := #[0, 1, 2, 3, 4, 0, 1, 2, 3, 4]
    have hkhatArr_eq : ∀ p : Fin 10, khatArr[p.val]! = (khat p).1 := by
      intro p; fin_cases p <;> rfl
    let remList : List Nat := [i1, i2, i3]
    let hullList : List Nat := (List.range 10).filter (fun p => !(remList.contains p))
    have hhullList_mem : ∀ p : Fin 10, p.val ∈ hullList ↔ p ∈ hullFinSet := by
      intro p
      simp only [hullList, List.mem_filter, List.mem_range, p.isLt, true_and, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not, remList, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro hnot
        by_contra hnotH
        have hp_rem : p ∈ remFinSet := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotH⟩
        have hrange : p ∈ Set.range remEmb := by
          simpa [remEmb, Finset.range_orderEmbOfFin] using hp_rem
        rcases hrange with ⟨t, rfl⟩
        fin_cases t <;> apply hnot <;> simp [i1, i2, i3]
      · intro hpH h_in
        have hp_not_rem : p ∉ remFinSet := fun h => (Finset.mem_sdiff.mp h).2 hpH
        rcases h_in with h | h | h
        · have : p = remEmb 0 := Fin.ext h
          exact hp_not_rem (this ▸ Finset.orderEmbOfFin_mem remFinSet hrem_card 0)
        · have : p = remEmb 1 := Fin.ext h
          exact hp_not_rem (this ▸ Finset.orderEmbOfFin_mem remFinSet hrem_card 1)
        · have : p = remEmb 2 := Fin.ext h
          exact hp_not_rem (this ▸ Finset.orderEmbOfFin_mem remFinSet hrem_card 2)
    have hhullList_eq : hullList = (List.finRange H.h).map (fun r => (hullIdx r).val) := by
      -- Both are strictly increasing lists of ℕ with the exact same elements!
      have h_sorted1 : hullList.Pairwise (· < ·) :=
        List.Pairwise.filter _ List.pairwise_lt_range
      have h_sorted2 : ((List.finRange H.h).map (fun r => (hullIdx r).val)).Pairwise (· < ·) :=
        List.Pairwise.map _ (fun a b hab => hhullIdx_mono hab)
          (List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by simp [hij]))
      refine List.Perm.eq_of_pairwise
        (fun a b _ _ hab hba => absurd (lt_trans hab hba) (lt_irrefl _)) h_sorted1 h_sorted2 ?_
      refine List.perm_of_nodup_nodup_toFinset_eq (h_sorted1.imp ne_of_lt) (h_sorted2.imp ne_of_lt) ?_
      apply Finset.ext; intro n
      simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
      constructor
      · intro hn
        have hn10 : n < 10 := (List.mem_range.mp (List.mem_filter.mp hn).1)
        have hm := (hhullList_mem ⟨n, hn10⟩).mp hn
        rcases Finset.mem_image.mp hm with ⟨r, _, hr⟩
        exact ⟨r, congrArg Fin.val hr⟩
      · rintro ⟨r, rfl⟩
        exact (hhullList_mem (hullIdx r)).mpr (Finset.mem_image_of_mem hullIdx (Finset.mem_univ r))
    have hadj_distinct : (hullList.zip hullList.tail).all (fun (a, b) => khatArr[a]! != khatArr[b]!) = true := by
      rw [hhullList_eq, List.all_eq_true]
      rintro ⟨a, b⟩ hab
      -- Check directly via `blockVal` / `H.n = 7 = H.h`: adjacent hull points have distinct colors!
      have h_q_adj : ∀ r : Fin (H.h - 1),
          (H.q ⟨r.val, by omega⟩).1 ≠ (H.q ⟨r.val + 1, by omega⟩).1 := by
        by_contra hnot
        push Not at hnot
        rcases hnot with ⟨r, hr⟩
        have hsub : Finset.univ.filter (fun k : Fin (H.h - 1) =>
            (H.q ⟨k.val, by omega⟩).1 ≠ (H.q ⟨k.val + 1, by omega⟩).1) ⊆ Finset.univ.erase r := by
          intro k hk
          exact Finset.mem_erase.mpr ⟨fun h => by subst h; exact (Finset.mem_filter.mp hk).2 hr, Finset.mem_univ _⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin] at hc
        unfold HullData.n at hn7; omega
      have ha_mem : ∃ r : Fin (H.h - 1),
          a = (hullIdx ⟨r.val, by omega⟩).val ∧ b = (hullIdx ⟨r.val + 1, by omega⟩).val := by
        have h_len : ((List.finRange H.h).map (fun r => (hullIdx r).val)).length = H.h := by simp
        obtain ⟨k, hk_zip, hpair⟩ := List.mem_iff_getElem.mp hab
        have hk : k < H.h - 1 := by
          simp only [List.length_zip, List.length_map, List.length_finRange, List.length_tail] at hk_zip
          omega
        have hget := List.getElem_zip (l := (List.finRange H.h).map (fun r => (hullIdx r).val))
          (l' := ((List.finRange H.h).map (fun r => (hullIdx r).val)).tail) (i := k) (h := hk_zip)
        have h1 : k < H.h := by omega
        have h2 : k + 1 < H.h := by omega
        rw [hget] at hpair
        simp only [List.getElem_tail, List.getElem_map, List.getElem_finRange, Fin.cast_mk] at hpair
        exact ⟨⟨k, hk⟩, congrArg Prod.fst hpair |>.symm, congrArg Prod.snd hpair |>.symm⟩
      obtain ⟨r, rfl, rfl⟩ := ha_mem
      dsimp only
      rw [hkhatArr_eq (hullIdx ⟨r.val, by omega⟩), hkhatArr_eq (hullIdx ⟨r.val + 1, by omega⟩)]
      dsimp [hullIdx]
      rw [hkhat_left, hkhat_left]
      exact bne_iff_ne.mpr (h_q_adj r)
    change (if !((hullList.zip hullList.tail).all (fun x => khatArr[x.1]! != khatArr[x.2]!)) then true
      else _) = true at h_body
    rw [hadj_distinct] at h_body
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h_body
    -- Now `h_body` says NOT all 5 diagonals are contained in `a2 ++ b2`. We prove every diagonal IS in `a2 ++ b2`!
    let a2 : List (Finset (Fin 5)) :=
      (hullList.zip hullList.tail).map fun (a, b) => ({khatArr[a]!, khatArr[b]!} : Finset (Fin 5))
    let b2 : List (Finset (Fin 5)) :=
      remList.flatMap fun r =>
        let leftH := (hullList.filter (fun p => p < r)).getLast!
        let rightH := (hullList.filter (fun p => r < p)).head!
        ([{khatArr[r]!, khatArr[leftH]!}, {khatArr[r]!, khatArr[rightH]!}] : List (Finset (Fin 5)))
    have hdiag_mem : ∀ d : Finset (Fin 5), d.card = 2 → d ∈ a2 ++ b2 := by
      intro d hd_card
      have hd_ne : d.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, b, hab, hb_lt, h_in_d, h_rest⟩ := dualRealizes_hull_slab_spec H G.dual d hd_ne
      -- Since `H.h = 7 = H.n`, `blockVal H r = r.val` for all `r`!
      have h_q_adj : ∀ r : Fin (H.h - 1),
          (H.q ⟨r.val, by omega⟩).1 ≠ (H.q ⟨r.val + 1, by omega⟩).1 := by
        by_contra hnot; push Not at hnot; rcases hnot with ⟨r, hr⟩
        have hsub : Finset.univ.filter (fun k : Fin (H.h - 1) =>
            (H.q ⟨k.val, by omega⟩).1 ≠ (H.q ⟨k.val + 1, by omega⟩).1) ⊆ Finset.univ.erase r := by
          intro k hk; exact Finset.mem_erase.mpr ⟨fun h => by subst h; exact (Finset.mem_filter.mp hk).2 hr, Finset.mem_univ _⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin] at hc
        unfold HullData.n at hn7; omega
      have hbv_eq : ∀ r : Fin H.h, blockVal H r = r.val := by
        intro r
        have hfilt : Finset.univ.filter (fun k : Fin (H.h - 1) => k.val < r.val ∧
            (H.q ⟨k.val, by omega⟩).1 ≠ (H.q ⟨k.val + 1, by omega⟩).1) =
            Finset.univ.filter (fun k : Fin (H.h - 1) => k.val < r.val) := by
          apply Finset.ext; intro k; simp [h_q_adj k]
        unfold blockVal; rw [hfilt]
        have himg : Finset.univ.filter (fun k : Fin (H.h - 1) => k.val < r.val) =
            (Finset.range r.val).attach.image (fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; have := r.isLt; omega⟩) := by
          apply Finset.ext; intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach, true_and]
          constructor
          · intro hk; exact ⟨⟨k.val, Finset.mem_range.mpr hk⟩, Fin.ext rfl⟩
          · rintro ⟨⟨x, hx⟩, rfl⟩; exact Finset.mem_range.mp hx
        rw [himg, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (congrArg Fin.val h)),
            Finset.card_attach, Finset.card_range]
      have hkbar_eq : ∀ j : Fin H.n, kbar H j = (H.q ⟨j.val, by omega⟩).1 := by
        intro j
        have hbv := hbv_eq ⟨j.val, by omega⟩
        have hk := kbar_at_blockVal H ⟨j.val, by omega⟩
        have hfeq : (⟨blockVal H ⟨j.val, by omega⟩, blockVal_lt_n H ⟨j.val, by omega⟩⟩ : Fin H.n) = j := Fin.ext hbv
        rw [hfeq] at hk; exact hk.symm
      by_cases hab_lt : a < b
      · -- `a < b`: `(a, a+1)` gives two distinct colors in `d`, hence `d = {kbar a, kbar (a+1)} ∈ a2`!
        have ha1_lt : a + 1 < H.n := by omega
        let c1 := kbar H ⟨a, by omega⟩
        let c2 := kbar H ⟨a + 1, by omega⟩
        have hc12 : c1 ≠ c2 := kbar_adj_ne H ⟨a, by omega⟩
        have hc1_d : c1 ∈ d := h_in_d ⟨a, by omega⟩ (by change a ≤ a; omega) (by change a ≤ b; omega)
        have hc2_d : c2 ∈ d := h_in_d ⟨a + 1, by omega⟩ (by change a ≤ a + 1; omega) (by change a + 1 ≤ b; omega)
        have hd_eq : d = {c1, c2} := finset_card_two_sub_eq hc12 hd_card hc1_d hc2_d
        rw [List.mem_append]; left
        simp only [a2, List.mem_map]
        refine ⟨((hullIdx ⟨a, by omega⟩).val, (hullIdx ⟨a + 1, by omega⟩).val), ?_, ?_⟩
        · rw [hhullList_eq]
          refine List.mem_iff_getElem.mpr ⟨a, ?_, ?_⟩
          · simp only [List.length_zip, List.length_map, List.length_finRange, List.length_tail]; omega
          · rw [List.getElem_zip]
            simp only [List.getElem_tail, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
        · have h1 : khatArr[(hullIdx ⟨a, by omega⟩).val]! = c1 := by
            rw [hkhatArr_eq]; dsimp [hullIdx, c1]; rw [hkhat_left, hkbar_eq]
          have h2 : khatArr[(hullIdx ⟨a + 1, by omega⟩).val]! = c2 := by
            rw [hkhatArr_eq]; dsimp [hullIdx, c2]; rw [hkhat_left, hkbar_eq]
          rw [h1, h2, hd_eq]
      · -- `a = b`: `kbar a ∈ d` (`1` color), so the other color `c_R ∈ d \ {kbar a}` is in `R_int G.f`!
        have hab_eq : a = b := by omega
        let cH := kbar H ⟨a, by omega⟩
        have hcH_d : cH ∈ d := h_in_d ⟨a, by omega⟩ le_rfl (by omega)
        have hex_other : ∃ cR ∈ d, cR ≠ cH := by
          by_contra hnone; push Not at hnone
          have hsub : d ⊆ {cH} := fun x hx => Finset.mem_singleton.mpr (hnone x hx)
          have := Finset.card_le_card hsub; rw [Finset.card_singleton] at this; omega
        obtain ⟨cR, hcR_d, hcR_ne⟩ := hex_other
        have hd_eq : d = {cR, cH} := finset_card_two_sub_eq hcR_ne hd_card hcR_d hcH_d
        rcases h_rest cR hcR_d with ⟨j, hj1, hj2, hjc⟩ | ⟨p, hp, rfl, hsl1, hsl2⟩
        · exfalso; apply hcR_ne
          have hja : j = ⟨a, by omega⟩ := Fin.ext (by change j.val = a; omega)
          rw [hja] at hjc; exact hjc.symm
        · -- `p ∈ R_int G.f` and `fixedSlabIdx H p hp` satisfies `a ≤ r_c + 1 ∧ r_c ≤ a`!
          let r_c := Classical.choose (H.h_subenv p hp)
          have hr_c := Classical.choose_spec (H.h_subenv p hp)
          have hsl_eq : fixedSlabIdx H p hp = r_c.val := by
            unfold fixedSlabIdx
            change min (blockVal H ⟨r_c.val, by omega⟩) (H.n - 2) = r_c.val
            rw [hbv_eq ⟨r_c.val, by omega⟩]
            have hrc_lt : r_c.val < H.h - 1 := r_c.isLt
            dsimp [r_c] at hrc_lt ⊢
            omega
          rw [hsl_eq] at hsl1 hsl2
          have ha_case : a = r_c.val ∨ a = r_c.val + 1 := by omega
          let p_idx := khatInv p
          have hp_rem : p_idx ∈ remFinSet := by
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hpH => ?_⟩
            rcases Finset.mem_image.mp hpH with ⟨s, _, hs⟩
            have hqs : H.q s = p := by
              rw [← hkhat_left (H.q s), show khatInv (H.q s) = p_idx from hs, hkhat_left]
            exact (Finset.mem_sdiff.mp hp).2 (hqs ▸ H.hq_mem s)
          have hp_mem_remList : p_idx.val ∈ remList := by
            have hrange : p_idx ∈ Set.range remEmb := by simpa [remEmb, Finset.range_orderEmbOfFin] using hp_rem
            rcases hrange with ⟨t, ht⟩
            fin_cases t <;> simp [remList, i1, i2, i3, ← ht]
          have hp_between : (hullIdx ⟨r_c.val, by omega⟩).val < p_idx.val ∧
              p_idx.val < (hullIdx ⟨r_c.val + 1, by omega⟩).val := by
            constructor
            · by_contra hle
              rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hgt
              · have hne : p_idx ≠ hullIdx ⟨r_c.val, by omega⟩ := fun h =>
                  (Finset.mem_sdiff.mp hp_rem).2 (h ▸ Finset.mem_image_of_mem hullIdx (Finset.mem_univ _))
                exact hne (Fin.ext heq)
              · have := hkhat_mono (show p_idx < hullIdx ⟨r_c.val, by omega⟩ from hgt)
                dsimp [p_idx, hullIdx] at this; rw [hkhat_left, hkhat_left] at this; linarith [hr_c.1]
            · by_contra hle
              rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hgt
              · have hne : p_idx ≠ hullIdx ⟨r_c.val + 1, by omega⟩ := fun h =>
                  (Finset.mem_sdiff.mp hp_rem).2 (h ▸ Finset.mem_image_of_mem hullIdx (Finset.mem_univ _))
                exact hne (Fin.ext heq.symm)
              · have := hkhat_mono (show hullIdx ⟨r_c.val + 1, by omega⟩ < p_idx from hgt)
                dsimp [p_idx, hullIdx] at this; rw [hkhat_left, hkhat_left] at this; linarith [hr_c.2.1]
          have hleft_eq : (hullList.filter (fun q => q < p_idx.val)).getLast! =
              (hullIdx ⟨r_c.val, by omega⟩).val := by
            let L := hullList.filter (fun q => q < p_idx.val)
            have hL_ne : L ≠ [] := by
              intro hnil
              have hmem : (hullIdx ⟨r_c.val, by omega⟩).val ∈ L :=
                List.mem_filter.mpr ⟨(hhullList_mem _).mpr (Finset.mem_image_of_mem hullIdx (Finset.mem_univ _)),
                  decide_eq_true hp_between.1⟩
              rw [hnil] at hmem; simp at hmem
            have hL_sorted : L.Pairwise (· < ·) :=
              (List.Pairwise.filter _ List.pairwise_lt_range).filter _
            obtain ⟨hlast_mem, hlast_max⟩ := list_getLast!_spec L hL_ne hL_sorted
            have hlast_H : L.getLast! ∈ hullList := (List.mem_filter.mp hlast_mem).1
            have hlast_lt : L.getLast! < p_idx.val := of_decide_eq_true (List.mem_filter.mp hlast_mem).2
            have hmem : (hullIdx ⟨r_c.val, by omega⟩).val ∈ L :=
              List.mem_filter.mpr ⟨(hhullList_mem _).mpr (Finset.mem_image_of_mem hullIdx (Finset.mem_univ _)),
                decide_eq_true hp_between.1⟩
            have hle1 : (hullIdx ⟨r_c.val, by omega⟩).val ≤ L.getLast! := hlast_max _ hmem
            have hlt_10 : L.getLast! < 10 := List.mem_range.mp (List.mem_filter.mp hlast_H).1
            rcases Finset.mem_image.mp ((hhullList_mem ⟨L.getLast!, hlt_10⟩).mp hlast_H) with ⟨s, _, hs⟩
            have hs_val : (hullIdx s).val = L.getLast! := congrArg Fin.val hs
            by_contra hne
            have hs_gt : r_c.val < s.val := by
              by_contra hle; rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
              · apply hne; rw [← hs_val]; exact congrArg (fun x => (hullIdx x).val) (Fin.ext heq)
              · have := hhullIdx_mono (show s < ⟨r_c.val, by omega⟩ from hlt)
                have : (hullIdx s).val < (hullIdx ⟨r_c.val, by omega⟩).val := this
                omega
            have hs_ge : r_c.val + 1 ≤ s.val := hs_gt
            have : (hullIdx ⟨r_c.val + 1, by omega⟩).val ≤ (hullIdx s).val :=
              hhullIdx_mono.monotone (by change r_c.val + 1 ≤ s.val; exact hs_ge)
            omega
          have hright_eq : (hullList.filter (fun q => p_idx.val < q)).head! =
              (hullIdx ⟨r_c.val + 1, by omega⟩).val := by
            let R := hullList.filter (fun q => p_idx.val < q)
            have hR_ne : R ≠ [] := by
              intro hnil
              have hmem : (hullIdx ⟨r_c.val + 1, by omega⟩).val ∈ R :=
                List.mem_filter.mpr ⟨(hhullList_mem _).mpr (Finset.mem_image_of_mem hullIdx (Finset.mem_univ _)),
                  decide_eq_true hp_between.2⟩
              rw [hnil] at hmem; simp at hmem
            have hR_sorted : R.Pairwise (· < ·) :=
              (List.Pairwise.filter _ List.pairwise_lt_range).filter _
            obtain ⟨hhead_mem, hhead_min⟩ := list_head!_spec R hR_ne hR_sorted
            have hhead_H : R.head! ∈ hullList := (List.mem_filter.mp hhead_mem).1
            have hhead_gt : p_idx.val < R.head! := of_decide_eq_true (List.mem_filter.mp hhead_mem).2
            have hmem : (hullIdx ⟨r_c.val + 1, by omega⟩).val ∈ R :=
              List.mem_filter.mpr ⟨(hhullList_mem _).mpr (Finset.mem_image_of_mem hullIdx (Finset.mem_univ _)),
                decide_eq_true hp_between.2⟩
            have hle1 : R.head! ≤ (hullIdx ⟨r_c.val + 1, by omega⟩).val := hhead_min _ hmem
            have hlt_10 : R.head! < 10 := List.mem_range.mp (List.mem_filter.mp hhead_H).1
            rcases Finset.mem_image.mp ((hhullList_mem ⟨R.head!, hlt_10⟩).mp hhead_H) with ⟨s, _, hs⟩
            have hs_val : (hullIdx s).val = R.head! := congrArg Fin.val hs
            by_contra hne
            have hs_lt : s.val < r_c.val + 1 := by
              by_contra hle; rcases eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
              · apply hne; rw [← hs_val]; exact congrArg (fun x => (hullIdx x).val) (Fin.ext heq.symm)
              · have := hhullIdx_mono (show ⟨r_c.val + 1, by omega⟩ < s from hlt)
                have : (hullIdx ⟨r_c.val + 1, by omega⟩).val < (hullIdx s).val := this
                omega
            have hs_le : s.val ≤ r_c.val := by omega
            have : (hullIdx s).val ≤ (hullIdx ⟨r_c.val, by omega⟩).val :=
              hhullIdx_mono.monotone (by change s.val ≤ r_c.val; exact hs_le)
            omega
          rw [List.mem_append]; right
          simp only [b2, List.mem_flatMap]
          refine ⟨p_idx.val, hp_mem_remList, ?_⟩
          rw [hleft_eq, hright_eq]
          have hp_arr : khatArr[p_idx.val]! = p.1 := by
            rw [hkhatArr_eq]; dsimp [p_idx]; rw [hkhat_left]
          have hl_arr : khatArr[(hullIdx ⟨r_c.val, by omega⟩).val]! = kbar H ⟨r_c.val, by omega⟩ := by
            rw [hkhatArr_eq]; dsimp [hullIdx]; rw [hkhat_left, hkbar_eq]
          have hr_arr : khatArr[(hullIdx ⟨r_c.val + 1, by omega⟩).val]! = kbar H ⟨r_c.val + 1, by omega⟩ := by
            rw [hkhatArr_eq]; dsimp [hullIdx]; rw [hkhat_left, hkbar_eq]
          rw [hp_arr, hl_arr, hr_arr]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rcases ha_case with ha0 | ha1
          · left; rw [hd_eq]; dsimp [cH]; exact congrArg (fun x => ({p.1, x} : Finset (Fin 5))) (congrArg (kbar H) (Fin.ext ha0))
          · right; rw [hd_eq]; dsimp [cH]; exact congrArg (fun x => ({p.1, x} : Finset (Fin 5))) (congrArg (kbar H) (Fin.ext ha1))
    have h_all_diags : ([({0, 2} : Finset (Fin 5)), {0, 3}, {1, 3}, {1, 4}, {2, 4}] : List (Finset (Fin 5))).all
        (fun d => (a2 ++ b2).contains d) = true := by
      rw [List.all_eq_true]
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      have h2 : d.card = 2 := by
        rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [List.contains_eq_mem] using hdiag_mem d h2
    rw [h_all_diags] at h_body
    simp at h_body
  · -- Case `T3bar G = 1`: `W.Δ1 + W.Δ2 = 0` or `T1 G = 0`.
    have hinv_le1 : permInvCount5 (cPerm G) ≤ 1 := by rw [cPerm_invCount_eq G]; omega
    by_cases hT1_0 : T1 G = 0
    · -- Subcase `T3bar = 1, T1 = 0`: `permInvCount5 = 1`, so `dL = 1` AND `dR = 1`, giving `dL + dR = 2 > W.Δ1 + W.Δ2`.
      have hinv1 : permInvCount5 (cPerm G) = 1 := by rw [cPerm_invCount_eq G]; omega
      have hinv_symm1 : permInvCount5 (cPerm G).symm = 1 := by rw [← permInvCount5_symm, hinv1]
      have hL : ∀ i : Fin 5, i.val < 3 → (cPerm G).symm i < (cPerm G).symm 4 := by
        intro i hi
        by_contra hle
        have hlt : (cPerm G).symm 4 < (cPerm G).symm i :=
          lt_of_le_of_ne (not_lt.mp hle) ((cPerm G).symm.injective.ne (Fin.ne_of_val_ne (by change (4 : ℕ) ≠ i.val; omega)))
        let S := (Finset.univ.product Finset.univ).filter
          (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ (cPerm G).symm p.2 < (cPerm G).symm p.1)
        have hm1 : (i, (4 : Fin 5)) ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change i.val < 4; omega, hlt⟩
        have hne3 : (i, (3 : Fin 5)) ≠ (i, (4 : Fin 5)) := fun h => by
          have := congrArg (fun p : Fin 5 × Fin 5 => p.2.val) h; dsimp at this; omega
        have hne34 : ((3 : Fin 5), (4 : Fin 5)) ≠ (i, (4 : Fin 5)) := by
          intro h; have := congrArg (fun p => p.1.val) h; dsimp at this; omega
        rcases lt_or_gt_of_ne ((cPerm G).symm.injective.ne (Fin.ne_of_val_ne (show i.val ≠ (3 : Fin 5).val by omega))) with h_i3 | h_3i
        · rcases lt_or_gt_of_ne ((cPerm G).symm.injective.ne (by decide : (3 : Fin 5) ≠ 4)) with h_34 | h_43
          · exact absurd (lt_trans h_i3 h_34) (not_lt.mpr (le_of_lt hlt))
          · have hm2 : ((3 : Fin 5), (4 : Fin 5)) ∈ S :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, h_43⟩
            have h2 := Finset.one_lt_card.mpr ⟨(3, 4), hm2, (i, 4), hm1, hne34⟩
            change 1 < permInvCount5 (cPerm G).symm at h2; omega
        · have hm2 : (i, (3 : Fin 5)) ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change i.val < 3; omega, h_3i⟩
          have h2 := Finset.one_lt_card.mpr ⟨(i, 3), hm2, (i, 4), hm1, hne3⟩
          change 1 < permInvCount5 (cPerm G).symm at h2; omega
      have hR : ∀ r : Fin 5, 2 ≤ r.val → cPerm G 0 < cPerm G r := by
        intro r hr
        by_contra hle
        have hlt : cPerm G r < cPerm G 0 :=
          lt_of_le_of_ne (not_lt.mp hle) ((cPerm G).injective.ne (Fin.ne_of_val_ne (by change r.val ≠ 0; omega)))
        let S := (Finset.univ.product Finset.univ).filter
          (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ cPerm G p.2 < cPerm G p.1)
        have hm1 : ((0 : Fin 5), r) ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change 0 < r.val; omega, hlt⟩
        have hne01 : ((0 : Fin 5), (1 : Fin 5)) ≠ ((0 : Fin 5), r) := by
          intro h; have := congrArg (fun p => p.2.val) h; dsimp at this; omega
        have hne1r : ((1 : Fin 5), r) ≠ ((0 : Fin 5), r) := fun h => by
          have := congrArg (fun p : Fin 5 × Fin 5 => p.1.val) h; dsimp at this; omega
        rcases lt_or_gt_of_ne ((cPerm G).injective.ne (by decide : (0 : Fin 5) ≠ 1)) with h_01 | h_10
        · rcases lt_or_gt_of_ne ((cPerm G).injective.ne (Fin.ne_of_val_ne (show (1 : Fin 5).val ≠ r.val by omega))) with h_1r | h_r1
          · exact absurd (lt_trans h_01 h_1r) (not_lt.mpr (le_of_lt hlt))
          · have hm2 : ((1 : Fin 5), r) ∈ S :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change 1 < r.val; omega, h_r1⟩
            have h2 := Finset.one_lt_card.mpr ⟨(1, r), hm2, (0, r), hm1, hne1r⟩
            change 1 < permInvCount5 (cPerm G) at h2; omega
        · have hm2 : ((0 : Fin 5), (1 : Fin 5)) ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, h_10⟩
          have h2 := Finset.one_lt_card.mpr ⟨(0, 1), hm2, (0, r), hm1, hne01⟩
          change 1 < permInvCount5 (cPerm G) at h2; omega
      have hEL : ∀ i : Fin 5, i.val < 3 → E3_bool G i 4 = true := by
        intro i hi
        have hi4 : i < 4 := by change i.val < 4; omega
        have hconc : (G.f i).c < (G.f 4).c := by
          have := cPerm_lt_iff G ((cPerm G).symm i) ((cPerm G).symm 4)
          simpa using this.mp (hL i hi)
        rcases (Z_set_conc_spec G hi4 hconc).1 with h1 | h3
        · exfalso
          have hmem : (i, 4) ∈ pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi4⟩, hconc, h1⟩
          have hpos := Finset.card_pos.mpr ⟨(i, 4), hmem⟩
          change 0 < T1 G at hpos; omega
        · simp [E3_bool, ne_of_lt hi4, min_eq_left (le_of_lt hi4), max_eq_right (le_of_lt hi4), h3]
      have hER : ∀ r : Fin 5, 2 ≤ r.val → E3_bool G (cPerm G 0) (cPerm G r) = true := by
        intro r hr
        have h0r : (0 : Fin 5) < r := by change 0 < r.val; omega
        have hs_lt : cPerm G 0 < cPerm G r := hR r hr
        have hconc : (G.f (cPerm G 0)).c < (G.f (cPerm G r)).c := cPerm_strictMono G h0r
        rcases (Z_set_conc_spec G hs_lt hconc).1 with h1 | h3
        · exfalso
          have hmem : (cPerm G 0, cPerm G r) ∈ pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs_lt⟩, hconc, h1⟩
          have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
          change 0 < T1 G at hpos; omega
        · simp [E3_bool, ne_of_lt hs_lt, min_eq_left (le_of_lt hs_lt), max_eq_right (le_of_lt hs_lt), h3]
      have hdL1 : dL_nat G = 1 := by
        unfold dL_nat; rw [if_pos (by simp [hEL 0 (by decide), hEL 1 (by decide), hEL 2 (by decide)])]
      have hdR1 : dR_nat G = 1 := by
        unfold dR_nat; rw [if_pos (by simp [hER 2 (by decide), hER 3 (by decide), hER 4 (by decide)])]
      omega
    · -- Subcase `T3bar = 1, T1 = 1`: `permInvCount5 = 0`, `σ = 1`, unique non-edge is `(0, 4)`, contradiction with `n7_T3bar1_T11_has_split_mask`!
      have hT1_1 : T1 G = 1 := by omega
      have hΔ0 : W.Δ1 = 0 ∧ W.Δ2 = 0 := by omega
      have hdL0 : dL_nat G = 0 := by omega
      have hdR0 : dR_nat G = 0 := by omega
      have hinv0 : permInvCount5 (cPerm G) = 0 := by rw [cPerm_invCount_eq G]; omega
      have hσ_id : cPerm G = Equiv.refl _ := perm_invCount_zero_eq_refl (cPerm G) hinv0
      have hc_mono : StrictMono (fun i : Fin 5 => (G.f i).c) := by
        have := cPerm_strictMono G; simpa [hσ_id] using this
      let S1 := pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1)
      have hS1_card : S1.card = 1 := hT1_1
      have h04_S1 : (0, 4) ∈ S1 := by
        -- Since `dL_nat G = 0`, some `(r, 4)` (`r ≤ 2`) has `E3_bool G r 4 = false`, so `(r, 4) ∈ S1`.
        -- Since `dR_nat G = 0` (`σ = 1`), some `(0, s)` (`s ≥ 2`) has `E3_bool G 0 s = false`, so `(0, s) ∈ S1`.
        -- Since `S1.card = 1`, `(r, 4) = (0, s)`, hence `(0, 4) ∈ S1`!
        have hexL : ∃ r : Fin 5, r.val < 3 ∧ E3_bool G r 4 = false := by
          by_contra hnone; push Not at hnone
          have hE : E3_bool G 0 4 = true ∧ E3_bool G 1 4 = true ∧ E3_bool G 2 4 = true :=
            ⟨Bool.eq_true_of_not_eq_false (hnone 0 (by decide)),
             Bool.eq_true_of_not_eq_false (hnone 1 (by decide)),
             Bool.eq_true_of_not_eq_false (hnone 2 (by decide))⟩
          have hdL1 : dL_nat G = 1 := by unfold dL_nat; rw [if_pos (by simp [hE])]
          omega
        have hexR : ∃ s : Fin 5, 2 ≤ s.val ∧ E3_bool G 0 s = false := by
          by_contra hnone; push Not at hnone
          have hE : E3_bool G (cPerm G 0) (cPerm G 2) = true ∧
              E3_bool G (cPerm G 0) (cPerm G 3) = true ∧
              E3_bool G (cPerm G 0) (cPerm G 4) = true := by
            simp only [hσ_id, Equiv.refl_apply]
            exact ⟨Bool.eq_true_of_not_eq_false (hnone 2 (by decide)),
                   Bool.eq_true_of_not_eq_false (hnone 3 (by decide)),
                   Bool.eq_true_of_not_eq_false (hnone 4 (by decide))⟩
          have hdR1 : dR_nat G = 1 := by unfold dR_nat; rw [if_pos (by simp [hE])]
          omega
        obtain ⟨r, hr, hrE⟩ := hexL
        obtain ⟨s, hs, hsE⟩ := hexR
        have hr4_S1 : (r, 4) ∈ S1 := by
          have hr4 : r < 4 := by change r.val < 4; omega
          have hconc := hc_mono hr4
          rcases (Z_set_conc_spec G hr4 hconc).1 with h1 | h3
          · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr4⟩, hconc, h1⟩
          · exfalso; simp [E3_bool, ne_of_lt hr4, min_eq_left (le_of_lt hr4), max_eq_right (le_of_lt hr4), h3] at hrE
        have h0s_S1 : (0, s) ∈ S1 := by
          have h0s : (0 : Fin 5) < s := by change 0 < s.val; omega
          have hconc := hc_mono h0s
          rcases (Z_set_conc_spec G h0s hconc).1 with h1 | h3
          · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0s⟩, hconc, h1⟩
          · exfalso; simp [E3_bool, ne_of_lt h0s, min_eq_left (le_of_lt h0s), max_eq_right (le_of_lt h0s), h3] at hsE
        obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hS1_card
        rw [hp] at hr4_S1 h0s_S1
        have heq1 := Finset.mem_singleton.mp hr4_S1
        have heq2 := Finset.mem_singleton.mp h0s_S1
        have hrs : r = 0 ∧ s = 4 := by
          have := heq1.trans heq2.symm
          exact ⟨congrArg Prod.fst this, (congrArg Prod.snd this).symm⟩
        rw [← hp, hrs.1] at hr4_S1
        exact hr4_S1
      have hS1_eq : S1 = {(0, 4)} := Finset.eq_of_subset_of_card_le
        (fun p hp => by
          obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hS1_card
          rw [hq] at hp h04_S1; exact Finset.mem_singleton.mpr ((Finset.mem_singleton.mp hp).trans (Finset.mem_singleton.mp h04_S1).symm))
        (by rw [Finset.card_singleton, hS1_card])
      have hE_other : ∀ i j : Fin 5, i < j → (i, j) ≠ (0, 4) → E3_bool G i j = true := by
        intro i j hij hne
        have hconc := hc_mono hij
        rcases (Z_set_conc_spec G hij hconc).1 with h1 | h3
        · exfalso
          have hmem : (i, j) ∈ S1 := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hconc, h1⟩
          rw [hS1_eq, Finset.mem_singleton] at hmem
          exact hne hmem
        · simp [E3_bool, ne_of_lt hij, min_eq_left (le_of_lt hij), max_eq_right (le_of_lt hij), h3]
      have h01 := (E3_bool_conc G (hE_other 0 1 (by decide) (by decide))).2.resolve_right (by rintro ⟨h, _⟩; exact absurd h (by decide))
      have h02 := (E3_bool_conc G (hE_other 0 2 (by decide) (by decide))).2.resolve_right (by rintro ⟨h, _⟩; exact absurd h (by decide))
      have h03 := (E3_bool_conc G (hE_other 0 3 (by decide) (by decide))).2.resolve_right (by rintro ⟨h, _⟩; exact absurd h (by decide))
      have h14 := (E3_bool_conc G (hE_other 1 4 (by decide) (by decide))).2.resolve_right (by rintro ⟨h, _⟩; exact absurd h (by decide))
      have h24 := (E3_bool_conc G (hE_other 2 4 (by decide) (by decide))).2.resolve_right (by rintro ⟨h, _⟩; exact absurd h (by decide))
      have h34 := (E3_bool_conc G (hE_other 3 4 (by decide) (by decide))).2.resolve_right (by rintro ⟨h, _⟩; exact absurd h (by decide))
      obtain ⟨τm, hτmX, hτm_k, hτm_ord⟩ := exists_tau_minus G
      obtain ⟨τp, hτpX, hτp_k, hτp_ord⟩ := exists_tau_plus G
      have htm : (G.f 4).eval τm < (G.f 3).eval τm ∧ (G.f 3).eval τm < (G.f 2).eval τm ∧
          (G.f 2).eval τm < (G.f 1).eval τm ∧ (G.f 1).eval τm < (G.f 0).eval τm :=
        ⟨hτm_ord 3 4 (by decide), hτm_ord 2 3 (by decide), hτm_ord 1 2 (by decide), hτm_ord 0 1 (by decide)⟩
      have htp : (G.f 0).eval τp < (G.f 1).eval τp ∧ (G.f 1).eval τp < (G.f 2).eval τp ∧
          (G.f 2).eval τp < (G.f 3).eval τp ∧ (G.f 3).eval τp < (G.f 4).eval τp :=
        ⟨by simpa [hσ_id] using hτp_ord 0 1 (by decide),
         by simpa [hσ_id] using hτp_ord 1 2 (by decide),
         by simpa [hσ_id] using hτp_ord 2 3 (by decide),
         by simpa [hσ_id] using hτp_ord 3 4 (by decide)⟩
      have hx0 : (G.f 0).eval (kink G.f 0) < (G.f 1).eval (kink G.f 0) ∧
          (G.f 0).eval (kink G.f 0) < (G.f 2).eval (kink G.f 0) ∧
          (G.f 0).eval (kink G.f 0) < (G.f 3).eval (kink G.f 0) ∧
          (G.f 0).eval (kink G.f 0) ≠ (G.f 4).eval (kink G.f 0) :=
        ⟨h01.2.2.2.1, h02.2.2.2.1, h03.2.2.2.1, G.gpa_vals 0 4 (by decide)⟩
      have hx1 : (G.f 1).eval (kink G.f 1) < (G.f 0).eval (kink G.f 1) ∧
          (G.f 1).eval (kink G.f 1) < (G.f 4).eval (kink G.f 1) :=
        ⟨h01.2.2.2.2, h14.2.2.2.1⟩
      have hx4 : (G.f 4).eval (kink G.f 4) < (G.f 1).eval (kink G.f 4) ∧
          (G.f 4).eval (kink G.f 4) < (G.f 2).eval (kink G.f 4) ∧
          (G.f 4).eval (kink G.f 4) < (G.f 3).eval (kink G.f 4) ∧
          (G.f 0).eval (kink G.f 4) ≠ (G.f 4).eval (kink G.f 4) :=
        ⟨h14.2.2.2.2, h24.2.2.2.2, h34.2.2.2.2, (G.gpa_vals 4 0 (by decide)).symm⟩
      rcases n7_T3bar1_T11_has_split_mask
          ((G.f 0).eval τm) ((G.f 1).eval τm) ((G.f 2).eval τm) ((G.f 3).eval τm) ((G.f 4).eval τm)
          ((G.f 0).eval (kink G.f 0)) ((G.f 1).eval (kink G.f 0)) ((G.f 2).eval (kink G.f 0)) ((G.f 3).eval (kink G.f 0)) ((G.f 4).eval (kink G.f 0))
          ((G.f 0).eval (kink G.f 1)) ((G.f 1).eval (kink G.f 1)) ((G.f 2).eval (kink G.f 1)) ((G.f 3).eval (kink G.f 1)) ((G.f 4).eval (kink G.f 1))
          ((G.f 0).eval (kink G.f 4)) ((G.f 1).eval (kink G.f 4)) ((G.f 2).eval (kink G.f 4)) ((G.f 3).eval (kink G.f 4)) ((G.f 4).eval (kink G.f 4))
          ((G.f 0).eval τp) ((G.f 1).eval τp) ((G.f 2).eval τp) ((G.f 3).eval τp) ((G.f 4).eval τp)
          htm htp hx0 hx1 hx4 with ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩
      · simp only [lt_min_iff] at hA hC
        have hΦ1 : Φ G.f {4} τm := by
          intro u hu v hv; rw [Finset.mem_singleton.mp hu]
          fin_cases v
          · exact hA.1.1
          · exact hA.1.2
          · exact hA.2.1
          · exact hA.2.2
          · exact absurd (Finset.mem_singleton_self 4) hv
        have hnΦ : ¬ Φ G.f {4} (kink G.f 1) := fun h => by
          have := h 4 (Finset.mem_singleton_self _) 1 (by decide); linarith
        have hΦ3 : Φ G.f {4} (kink G.f 4) := by
          intro u hu v hv; rw [Finset.mem_singleton.mp hu]
          fin_cases v
          · exact hC.1.1
          · exact hC.1.2
          · exact hC.2.1
          · exact hC.2.2
          · exact absurd (Finset.mem_singleton_self 4) hv
        have h1 := W.h_split_cert {4} τm (kink G.f 1) (kink G.f 4) (Or.inl rfl)
          (hτm_k 1) h14.2.2.1 hτmX (kink_not_mem_X_cross G 1) (kink_not_mem_X_cross G 4) hΦ1 hnΦ hΦ3
        simp only [Finset.card_singleton, ↓reduceIte] at h1; omega
      · simp only [lt_min_iff] at hA hC
        have hΦ1 : Φ G.f {0} (kink G.f 0) := by
          intro u hu v hv; rw [Finset.mem_singleton.mp hu]
          fin_cases v
          · exact absurd (Finset.mem_singleton_self 0) hv
          · exact hA.1.1
          · exact hA.1.2
          · exact hA.2.1
          · exact hA.2.2
        have hnΦ : ¬ Φ G.f {0} (kink G.f 1) := fun h => by
          have := h 0 (Finset.mem_singleton_self _) 1 (by decide); linarith
        have hΦ3 : Φ G.f {0} τp := by
          intro u hu v hv; rw [Finset.mem_singleton.mp hu]
          fin_cases v
          · exact absurd (Finset.mem_singleton_self 0) hv
          · exact hC.1.1
          · exact hC.1.2
          · exact hC.2.1
          · exact hC.2.2
        have h1 := W.h_split_cert {0} (kink G.f 0) (kink G.f 1) τp (Or.inl rfl)
          h01.2.2.1 (hτp_k 1) (kink_not_mem_X_cross G 0) (kink_not_mem_X_cross G 1) hτpX hΦ1 hnΦ hΦ3
        simp only [Finset.card_singleton, ↓reduceIte] at h1; omega
      · simp only [max_lt_iff, lt_min_iff] at hA hC
        have hΦ1 : Φ G.f {0, 4} (kink G.f 0) := by
          intro u hu v hv
          have hu' : u = 0 ∨ u = 4 := by simpa using hu
          have hv' : v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> simp at hv ⊢
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl | rfl
          · exact hA.1.1
          · exact hA.2.1.1
          · exact hA.2.2.1
          · exact hA.1.2
          · exact hA.2.1.2
          · exact hA.2.2.2
        have hnΦ : ¬ Φ G.f {0, 4} (kink G.f 1) := fun h => by
          have := h 0 (by simp) 1 (by decide); linarith
        have hΦ3 : Φ G.f {0, 4} (kink G.f 4) := by
          intro u hu v hv
          have hu' : u = 0 ∨ u = 4 := by simpa using hu
          have hv' : v = 1 ∨ v = 2 ∨ v = 3 := by fin_cases v <;> simp at hv ⊢
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl | rfl
          · exact hC.1.1
          · exact hC.2.1.1
          · exact hC.2.2.1
          · exact hC.1.2
          · exact hC.2.1.2
          · exact hC.2.2.2
        have h1 := W.h_split_cert {0, 4} (kink G.f 0) (kink G.f 1) (kink G.f 4) (Or.inr (by decide))
          h01.2.2.1 h14.2.2.1 (kink_not_mem_X_cross G 0) (kink_not_mem_X_cross G 1) (kink_not_mem_X_cross G 4)
          hΦ1 hnΦ hΦ3
        rw [if_neg (by decide : ({0, 4} : Finset (Fin 5)).card ≠ 1)] at h1
        omega
  · -- Case `T3bar G = 2`: `T1 = 0`, `permInvCount5 σ = 2`, `dL = dR = 0`, contradiction with `n7_perm_inv_1_or_2_has_certificate`.
    have hT1_0 : T1 G = 0 := by omega
    have hd0 : dL_nat G = 0 ∧ dR_nat G = 0 := by omega
    have hinv2 : permInvCount5 (cPerm G) = 2 := by rw [cPerm_invCount_eq G]; omega
    have hinv_symm2 : ((Finset.univ.product Finset.univ).filter
        (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ (cPerm G).symm p.2 < (cPerm G).symm p.1)).card ∈ ({1, 2} : Set ℕ) := by
      have h_eq : permInvCount5 (cPerm G).symm = ((Finset.univ.product Finset.univ).filter
          (fun p : Fin 5 × Fin 5 => p.1 < p.2 ∧ (cPerm G).symm p.2 < (cPerm G).symm p.1)).card := rfl
      rw [← h_eq, ← permInvCount5_symm, hinv2]; simp
    rcases n7_perm_inv_1_or_2_has_certificate (cPerm G) hinv_symm2 with hL | hR
    · have hE : ∀ i : Fin 5, i.val < 3 → E3_bool G i 4 = true := by
        intro i hi
        have hi4 : i < 4 := by change i.val < 4; omega
        have hconc : (G.f i).c < (G.f 4).c := by
          have := cPerm_lt_iff G ((cPerm G).symm i) ((cPerm G).symm 4)
          simpa using this.mp (hL i hi)
        rcases (Z_set_conc_spec G hi4 hconc).1 with h1 | h3
        · exfalso
          have hmem : (i, 4) ∈ pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi4⟩, hconc, h1⟩
          have hpos := Finset.card_pos.mpr ⟨(i, 4), hmem⟩
          change 0 < T1 G at hpos; omega
        · simp [E3_bool, ne_of_lt hi4, min_eq_left (le_of_lt hi4), max_eq_right (le_of_lt hi4), h3]
      have hdL1 : dL_nat G = 1 := by
        unfold dL_nat; rw [if_pos (by simp [hE 0 (by decide), hE 1 (by decide), hE 2 (by decide)])]
      omega
    · have hE : ∀ r : Fin 5, 2 ≤ r.val → E3_bool G (cPerm G 0) (cPerm G r) = true := by
        intro r hr
        have h0r : (0 : Fin 5) < r := by change 0 < r.val; omega
        have hs_lt : cPerm G 0 < cPerm G r := hR r hr
        have hconc : (G.f (cPerm G 0)).c < (G.f (cPerm G r)).c := cPerm_strictMono G h0r
        rcases (Z_set_conc_spec G hs_lt hconc).1 with h1 | h3
        · exfalso
          have hmem : (cPerm G 0, cPerm G r) ∈ pair5.filter (fun p => (G.f p.1).c < (G.f p.2).c ∧ (Z_set G.f p.1 p.2).card = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs_lt⟩, hconc, h1⟩
          have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
          change 0 < T1 G at hpos; omega
        · simp [E3_bool, ne_of_lt hs_lt, min_eq_left (le_of_lt hs_lt), max_eq_right (le_of_lt hs_lt), h3]
      have hdR1 : dR_nat G = 1 := by
        unfold dR_nat; rw [if_pos (by simp [hE 2 (by decide), hE 3 (by decide), hE 4 (by decide)])]
      omega

/-! ## Part 5: Elimination of `n = 5` and `n = 6` via `v_n5_n6_island_rule_elimination` -/

private def maskToFinset5 (m : Nat) : Finset (Fin 5) :=
  Finset.univ.filter (fun c : Fin 5 => bitSet m c.val)

private lemma maskToFinset5_nonempty (m : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 31) :
    (maskToFinset5 m).Nonempty := by
  have hdec : (List.range 32).all (fun x =>
      if Nat.ble 1 x && Nat.ble x 31 then (maskToFinset5 x).Nonempty else true) = true := by decide
  have hm := List.all_eq_true.mp hdec m (List.mem_range.mpr (by omega))
  simpa [Nat.ble_eq, hm1, hm2] using hm

private def packBase4 (s0 s1 s2 s3 s4 : Fin 4) : Nat :=
  s0.val + 4 * s1.val + 16 * s2.val + 64 * s3.val + 256 * s4.val

private lemma packBase4_aux :
    (List.range 4).all (fun s0 =>
      (List.range 4).all fun s1 =>
        (List.range 4).all fun s2 =>
          (List.range 4).all fun s3 =>
            (List.range 4).all fun s4 =>
              let code := s0 + 4 * s1 + 16 * s2 + 64 * s3 + 256 * s4
              Nat.blt (code / 32) 32 && Nat.blt (code % 32) 32 &&
              Nat.beq (((code / 32) <<< 5) ||| (code % 32)) code &&
              Nat.beq ((code >>> 0) &&& 3) s0 &&
              Nat.beq ((code >>> 2) &&& 3) s1 &&
              Nat.beq ((code >>> 4) &&& 3) s2 &&
              Nat.beq ((code >>> 6) &&& 3) s3 &&
              Nat.beq ((code >>> 8) &&& 3) s4) = true := by
  decide +kernel

private lemma packBase4_spec (s0 s1 s2 s3 s4 : Fin 4) :
    let code := packBase4 s0 s1 s2 s3 s4
    code / 32 < 32 ∧ code % 32 < 32 ∧ (((code / 32) <<< 5) ||| (code % 32)) = code ∧
    ((code >>> 0) &&& 3) = s0.val ∧
    ((code >>> 2) &&& 3) = s1.val ∧
    ((code >>> 4) &&& 3) = s2.val ∧
    ((code >>> 6) &&& 3) = s3.val ∧
    ((code >>> 8) &&& 3) = s4.val := by
  have hm := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp packBase4_aux
      s0.val (List.mem_range.mpr s0.isLt))
      s1.val (List.mem_range.mpr s1.isLt))
      s2.val (List.mem_range.mpr s2.isLt))
      s3.val (List.mem_range.mpr s3.isLt))
      s4.val (List.mem_range.mpr s4.isLt)
  dsimp only [packBase4] at hm ⊢
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
  exact ⟨hm.1.1.1.1.1.1.1, hm.1.1.1.1.1.1.2, hm.1.1.1.1.1.2, hm.1.1.1.1.2,
    hm.1.1.1.2, hm.1.1.2, hm.1.2, hm.2⟩

private lemma ivals5_mem (a b : Nat) (hab : a ≤ b) (hb : b < 5) :
    (a, b) ∈ ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)] : List (Nat × Nat)) := by
  have ha : a < 5 := by omega
  interval_cases a <;> interval_cases b <;> first | omega | decide

private lemma n5_mask_counterexample (s0 s1 s2 s3 s4 : Fin 4) :
    ∃ tMask : Nat, 1 ≤ tMask ∧ tMask ≤ 31 ∧
      ∀ a b : Nat, a ≤ b → b < 5 →
        ((List.range (b + 1 - a)).all fun d => bitSet tMask (a + d)) = true →
        ([0, 1, 2, 3, 4].all fun c =>
          if !(bitSet tMask c) then true
          else if Nat.ble a c && Nat.ble c b then true
          else let j := (packBase4 s0 s1 s2 s3 s4 >>> (2 * c)) &&& 3
               Nat.ble a (j + 1) && Nat.ble j b) = false := by
  have hcode := packBase4_spec s0 s1 s2 s3 s4
  dsimp only at hcode
  set code := packBase4 s0 s1 s2 s3 s4
  have h_chk := v_n5_n6_island_rule_elimination.1
  unfold checkN5Elim at h_chk
  have h1 := List.all_eq_true.mp h_chk (code / 32) (List.mem_range.mpr hcode.1)
  have h2 := List.all_eq_true.mp h1 (code % 32) (List.mem_range.mpr hcode.2.1)
  dsimp only at h2
  rw [hcode.2.2.1] at h2
  rw [Bool.not_eq_true', List.all_eq_false] at h2
  rcases h2 with ⟨tMask, htMask_mem, htMask_false⟩
  have htMask_bounds : 1 ≤ tMask ∧ tMask ≤ 31 := by
    simp only [List.mem_cons, List.mem_map, List.mem_range] at htMask_mem
    rcases htMask_mem with rfl | ⟨x, hx, rfl⟩ <;> omega
  refine ⟨tMask, htMask_bounds.1, htMask_bounds.2, fun a b hab hb hbase => ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hreal
  have hmem := ivals5_mem a b hab hb
  have hany : ([(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)] : List (Nat × Nat)).any (fun p =>
      let baseOk := (List.range (p.2 + 1 - p.1)).all fun d => bitSet tMask (p.1 + d)
      if !baseOk then false
      else [0, 1, 2, 3, 4].all fun c =>
        if !(bitSet tMask c) then true
        else if Nat.ble p.1 c && Nat.ble c p.2 then true
        else let j := (code >>> (2 * c)) &&& 3; Nat.ble p.1 (j + 1) && Nat.ble j p.2) = true := by
    refine List.any_eq_true.mpr ⟨(a, b), hmem, ?_⟩
    change (if !(List.all (List.range (b + 1 - a)) fun d => bitSet tMask (a + d)) then false
      else [0, 1, 2, 3, 4].all fun c =>
        if !(bitSet tMask c) then true
        else if Nat.ble a c && Nat.ble c b then true
        else let j := (code >>> (2 * c)) &&& 3; Nat.ble a (j + 1) && Nat.ble j b) = true
    rw [hbase]
    exact hreal
  exact absurd hany htMask_false

lemma elim_n5 {G : GenericVSystem} {H : HullData G.f} (hn5 : H.n = 5) : False := by
  let k5 : Fin 5 → Fin 5 := fun j => kbar H ⟨j.val, by omega⟩
  have hk5_surj : Function.Surjective k5 := by
    intro c; obtain ⟨j, hj⟩ := kbar_surj H c
    exact ⟨⟨j.val, by omega⟩, by simpa [k5] using hj⟩
  let π : Equiv.Perm (Fin 5) := Equiv.ofBijective k5 ((Fintype.bijective_iff_surjective_and_card k5).mpr ⟨hk5_surj, rfl⟩)
  let slab5 (c : Fin 5) : Fin 4 :=
    if h : ∃ (p : Fin 5 × Bool), p ∈ R_int G.f ∧ p.1 = π c then
      ⟨fixedSlabIdx H (Classical.choose h) (Classical.choose_spec h).1, by
        have hle : fixedSlabIdx H (Classical.choose h) (Classical.choose_spec h).1 ≤ H.n - 2 := min_le_right _ _
        omega⟩
    else 0
  have hcode := packBase4_spec (slab5 0) (slab5 1) (slab5 2) (slab5 3) (slab5 4)
  dsimp only at hcode
  obtain ⟨tMask, ht1, ht2, ht_bad⟩ :=
    n5_mask_counterexample (slab5 0) (slab5 1) (slab5 2) (slab5 3) (slab5 4)
  let S : Finset (Fin 5) := (maskToFinset5 tMask).image π
  have hSne : S.Nonempty := (maskToFinset5_nonempty tMask ht1 ht2).image π
  obtain ⟨a, b, hab, hb_lt, h_in_S, h_rest⟩ := dualRealizes_hull_slab_spec H G.dual S hSne
  have h_real_true : [0, 1, 2, 3, 4].all (fun c =>
      if !(bitSet tMask c) then true
      else if Nat.ble a c && Nat.ble c b then true
      else let j := (packBase4 (slab5 0) (slab5 1) (slab5 2) (slab5 3) (slab5 4) >>> (2 * c)) &&& 3
           Nat.ble a (j + 1) && Nat.ble j b) = true := by
    rw [List.all_eq_true]; intro c hc
    by_cases hc_bit : bitSet tMask c = true
    · simp only [hc_bit, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hc5 : c < 5 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; omega
      let c' : Fin 5 := ⟨c, hc5⟩
      have hc'_S : π c' ∈ S := Finset.mem_image_of_mem π (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_bit⟩)
      by_cases h_in_ab : a ≤ c ∧ c ≤ b
      · simp [Nat.ble_eq, h_in_ab.1, h_in_ab.2]
      · have hnot_ble : (Nat.ble a c && Nat.ble c b) = false := by
          by_contra h; exact h_in_ab (by simp [Nat.ble_eq] at h; exact h)
        simp only [hnot_ble, Bool.false_eq_true, ↓reduceIte]
        rcases h_rest (π c') hc'_S with ⟨j, hj1, hj2, hjc⟩ | ⟨p, hp, hpc, hsl1, hsl2⟩
        · exfalso; apply h_in_ab
          have hjeq : j.val = c := by
            have h1 : π ⟨j.val, by omega⟩ = kbar H j := rfl
            have h2 : π c' = π ⟨j.val, by omega⟩ := by rw [← hjc, h1]
            exact congrArg Fin.val (π.injective h2) |>.symm
          omega
        · have hex : ∃ (p : Fin 5 × Bool), p ∈ R_int G.f ∧ p.1 = π c' := ⟨p, hp, hpc⟩
          have hp_eq : p = Classical.choose hex :=
            H.h_R_inj p hp (Classical.choose hex) (Classical.choose_spec hex).1
              (by rw [hpc, (Classical.choose_spec hex).2])
          have hslab_val : (slab5 c').val = fixedSlabIdx H p hp := by
            dsimp [slab5]; rw [dif_pos hex]; dsimp; congr 1; exact hp_eq.symm
          have hbit_slab : (packBase4 (slab5 0) (slab5 1) (slab5 2) (slab5 3) (slab5 4) >>> (2 * c)) &&& 3 = (slab5 c').val := by
            have hc_cases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
            rcases hc_cases with rfl | rfl | rfl | rfl | rfl
            · exact hcode.2.2.2.1
            · exact hcode.2.2.2.2.1
            · exact hcode.2.2.2.2.2.1
            · exact hcode.2.2.2.2.2.2.1
            · exact hcode.2.2.2.2.2.2.2
          rw [hbit_slab, hslab_val]
          simp [Nat.ble_eq, hsl1, hsl2]
    · simp [hc_bit]
  have hbase : (List.range (b + 1 - a)).all (fun d => bitSet tMask (a + d)) = true := by
    rw [List.all_eq_true]; intro d hd
    have hd_lt := List.mem_range.mp hd
    have had_S : π ⟨a + d, by omega⟩ ∈ S := h_in_S ⟨a + d, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    rcases Finset.mem_image.mp had_S with ⟨c', hc', hpi⟩
    have hc'_eq : c' = ⟨a + d, by omega⟩ := π.injective hpi
    have hmem_f := (Finset.mem_filter.mp hc').2
    rw [hc'_eq] at hmem_f
    exact hmem_f
  have hfalse := ht_bad a b hab (by omega) hbase
  exact absurd h_real_true (Bool.eq_false_iff.mp hfalse)

private def words6List : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [ (0, 1, 0, 2, 3, 4), (0, 1, 2, 0, 3, 4), (0, 1, 2, 3, 0, 4),
    (1, 0, 2, 0, 3, 4), (1, 0, 2, 3, 0, 4), (1, 0, 2, 3, 4, 0),
    (1, 2, 0, 3, 0, 4), (1, 2, 0, 3, 4, 0), (1, 2, 3, 0, 4, 0) ]

private lemma ivals6_mem (a b : Nat) (hab : a ≤ b) (hb : b < 6) :
    (a, b) ∈ ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),
      (2,2),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5),(4,4),(4,5),(5,5)] : List (Nat × Nat)) := by
  have ha : a < 6 := by omega
  interval_cases a <;> interval_cases b <;> first | omega | decide

private lemma n6_mask_counterexample
    (w6 : Nat × Nat × Nat × Nat × Nat × Nat) (hw6 : w6 ∈ words6List)
    (s1 s2 s3 s4 : Fin 5) :
    ∃ tMask : Nat, 1 ≤ tMask ∧ tMask ≤ 31 ∧
      let code := s1.val + 5 * s2.val + 25 * s3.val + 125 * s4.val
      let kAt (idx : Nat) : Nat :=
        if Nat.beq idx 0 then w6.1
        else if Nat.beq idx 1 then w6.2.1
        else if Nat.beq idx 2 then w6.2.2.1
        else if Nat.beq idx 3 then w6.2.2.2.1
        else if Nat.beq idx 4 then w6.2.2.2.2.1
        else w6.2.2.2.2.2
      ∀ a b : Nat, a ≤ b → b < 6 →
        (((List.range (b + 1 - a)).map (fun d => a + d)).all (fun idx => bitSet tMask (kAt idx))) = true →
        ([0, 1, 2, 3, 4].all fun c =>
          if !(bitSet tMask c) then true
          else if ((List.range (b + 1 - a)).map (fun d => a + d)).any (fun idx => Nat.beq (kAt idx) c) then true
          else if Nat.beq c 0 then false
          else
            let j := if Nat.beq c 1 then code % 5
              else if Nat.beq c 2 then (code / 5) % 5
              else if Nat.beq c 3 then (code / 25) % 5
              else (code / 125) % 5
            Nat.ble a (j + 1) && Nat.ble j b) = false := by
  rcases w6 with ⟨c0, c1, c2, c3, c4, c5⟩
  set code := s1.val + 5 * s2.val + 25 * s3.val + 125 * s4.val
  have hcode_lt : code < 625 := by have := s1.isLt; have := s2.isLt; have := s3.isLt; have := s4.isLt; omega
  have hhi_lt : code / 25 < 25 := by omega
  have hlo_lt : code % 25 < 25 := by omega
  have hcode_pack : (code / 25) * 25 + (code % 25) = code := by omega
  have h_chk := v_n5_n6_island_rule_elimination.2
  unfold checkN6Elim at h_chk
  have h1 := List.all_eq_true.mp h_chk (c0, c1, c2, c3, c4, c5) hw6
  have h2 := List.all_eq_true.mp h1 (code / 25) (List.mem_range.mpr hhi_lt)
  have h3 := List.all_eq_true.mp h2 (code % 25) (List.mem_range.mpr hlo_lt)
  dsimp only at h3
  rw [hcode_pack] at h3
  rw [Bool.not_eq_true', List.all_eq_false] at h3
  rcases h3 with ⟨tMask, htMask_mem, htMask_false⟩
  have htMask_bounds : 1 ≤ tMask ∧ tMask ≤ 31 := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_range] at htMask_mem
    rcases htMask_mem with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨x, hx, rfl⟩ <;> omega
  refine ⟨tMask, htMask_bounds.1, htMask_bounds.2, fun a b hab hb hbase => ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hreal
  have hmem := ivals6_mem a b hab hb
  have hany : ([(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),
      (2,2),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5),(4,4),(4,5),(5,5)] : List (Nat × Nat)).any (fun p =>
      let indices := (List.range (p.2 + 1 - p.1)).map (fun d => p.1 + d)
      let kAt (idx : Nat) : Nat :=
        if Nat.beq idx 0 then c0 else if Nat.beq idx 1 then c1 else if Nat.beq idx 2 then c2
        else if Nat.beq idx 3 then c3 else if Nat.beq idx 4 then c4 else c5
      let baseOk := indices.all (fun idx => bitSet tMask (kAt idx))
      if !baseOk then false
      else [0, 1, 2, 3, 4].all fun c =>
        if !(bitSet tMask c) then true
        else if indices.any (fun idx => Nat.beq (kAt idx) c) then true
        else if Nat.beq c 0 then false
        else
          let j := if Nat.beq c 1 then code % 5
            else if Nat.beq c 2 then (code / 5) % 5
            else if Nat.beq c 3 then (code / 25) % 5
            else (code / 125) % 5
          Nat.ble p.1 (j + 1) && Nat.ble j p.2) = true := by
    refine List.any_eq_true.mpr ⟨(a, b), hmem, ?_⟩
    change (if !(((List.range (b + 1 - a)).map (fun d => a + d)).all fun idx => bitSet tMask (
        if Nat.beq idx 0 then c0 else if Nat.beq idx 1 then c1 else if Nat.beq idx 2 then c2
        else if Nat.beq idx 3 then c3 else if Nat.beq idx 4 then c4 else c5)) then false
      else [0, 1, 2, 3, 4].all fun c =>
        if !(bitSet tMask c) then true
        else if ((List.range (b + 1 - a)).map (fun d => a + d)).any (fun idx => Nat.beq (
          if Nat.beq idx 0 then c0 else if Nat.beq idx 1 then c1 else if Nat.beq idx 2 then c2
          else if Nat.beq idx 3 then c3 else if Nat.beq idx 4 then c4 else c5) c) then true
        else if Nat.beq c 0 then false
        else
          let j := if Nat.beq c 1 then code % 5
            else if Nat.beq c 2 then (code / 5) % 5
            else if Nat.beq c 3 then (code / 25) % 5
            else (code / 125) % 5
          Nat.ble a (j + 1) && Nat.ble j b) = true
    rw [hbase]
    exact hreal
  exact absurd hany htMask_false

lemma elim_n6 {G : GenericVSystem} {H : HullData G.f} (W : SweepData G H)
    (hn6 : H.n = 6) : False := by
  have hh5 := H.hh_ge
  let k6 : Fin 6 → Fin 5 := fun j => kbar H ⟨j.val, by omega⟩
  have hk6_surj : Function.Surjective k6 := by
    intro c; obtain ⟨j, hj⟩ := kbar_surj H c
    exact ⟨⟨j.val, by omega⟩, by simpa [k6] using hj⟩
  have hnot_inj : ¬ Function.Injective k6 := by
    intro hinj
    have := Fintype.card_le_of_injective k6 hinj
    simp at this
  have hex_rep : ∃ i₁ i₂ : Fin 6, i₁ < i₂ ∧ k6 i₁ = k6 i₂ := by
    by_contra hnone; push Not at hnone
    apply hnot_inj; intro x y hxy
    rcases lt_trichotomy x y with h | rfl | h
    · exact absurd hxy (hnone x y h)
    · rfl
    · exact absurd hxy.symm (hnone y x h)
  obtain ⟨i₁, i₂, hi12, hki_eq⟩ := hex_rep
  have hi12_gap : i₁.val + 2 ≤ i₂.val := by
    by_contra hlt
    have hadj : i₂.val = i₁.val + 1 := by change i₁.val < i₂.val at hi12; omega
    have hne := kbar_adj_ne H ⟨i₁.val, by omega⟩
    apply hne
    have h1 : kbar H ⟨i₁.val, by omega⟩ = k6 i₁ := rfl
    have h2 : kbar H ⟨i₁.val + 1, by omega⟩ = k6 i₂ := by
      dsimp [k6]; congr 1; ext; dsimp; exact hadj.symm
    rw [h1, h2, hki_eq]
  let X : Fin 5 := k6 i₁
  -- Both copies of `X` are in `H_top`, so `X` has NO interior copy in `R_int G.f`!
  have hX_no_R : ¬ ∃ p ∈ R_int G.f, p.1 = X := by
    rintro ⟨p, hp, hpX⟩
    obtain ⟨r₁, hr₁⟩ := blockVal_surj H ⟨i₁.val, by omega⟩
    obtain ⟨r₂, hr₂⟩ := blockVal_surj H ⟨i₂.val, by omega⟩
    have hr12 : r₁ < r₂ := by
      by_contra hle
      have : blockVal H r₂ ≤ blockVal H r₁ := blockVal_mono H (not_lt.mp hle)
      dsimp at hr₁ hr₂; omega
    have hq1 : (H.q r₁).1 = X := by
      have := kbar_at_blockVal H r₁
      have heq : (⟨blockVal H r₁, blockVal_lt_n H r₁⟩ : Fin H.n) = ⟨i₁.val, by omega⟩ := Fin.ext hr₁
      rw [heq] at this; exact this
    have hq2 : (H.q r₂).1 = X := by
      have := kbar_at_blockVal H r₂
      have heq : (⟨blockVal H r₂, blockVal_lt_n H r₂⟩ : Fin H.n) = ⟨i₂.val, by omega⟩ := Fin.ext hr₂
      rw [heq] at this
      change (H.q r₂).1 = k6 i₂ at this
      rw [← hki_eq] at this; exact this
    have hq_ne : H.q r₁ ≠ H.q r₂ := H.hq_inj.ne (ne_of_lt hr12)
    have hsub : ({(X, false), (X, true)} : Finset (Fin 5 × Bool)) ⊆ H_top G.f := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · cases hb1 : (H.q r₁).2
        · rw [← hq1, ← hb1]; exact H.hq_mem r₁
        · have hb2 : (H.q r₂).2 = false := by
            by_contra ht
            have ht' : (H.q r₂).2 = true := Bool.eq_true_of_not_eq_false ht
            exact hq_ne (Prod.ext (hq1.trans hq2.symm) (hb1.trans ht'.symm))
          rw [← hq2, ← hb2]; exact H.hq_mem r₂
      · rw [Finset.mem_singleton.mp hw]
        cases hb1 : (H.q r₁).2
        · have hb2 : (H.q r₂).2 = true := by
            by_contra hf
            have hf' : (H.q r₂).2 = false := Bool.eq_false_of_not_eq_true hf
            exact hq_ne (Prod.ext (hq1.trans hq2.symm) (hb1.trans hf'.symm))
          rw [← hq2, ← hb2]; exact H.hq_mem r₂
        · rw [← hq1, ← hb1]; exact H.hq_mem r₁
    have hp_mem : p ∈ ({(X, false), (X, true)} : Finset (Fin 5 × Bool)) := by
      rcases p with ⟨c, b⟩; cases b <;> simp_all
    exact (Finset.mem_sdiff.mp hp).2 (hsub hp_mem)
  -- Case `(i₁, i₂) = (0, 5)` -> `X = 0 = cPerm G 4`, contradicting `v_sigma1_ne_5_and_top2_ne_45`.
  by_cases h05 : i₁.val = 0 ∧ i₂.val = 5
  · have hq0_eq : H.q ⟨0, by omega⟩ = (0, false) := by
      by_contra hne
      have hlt_0 : (dualPt G.f (0, false)).1 < (dualPt G.f (H.q ⟨0, by omega⟩)).1 := by
        cases hb : (H.q ⟨0, by omega⟩).2
        · have hc : (H.q ⟨0, by omega⟩).1 ≠ 0 := fun h => hne (Prod.ext h hb)
          have hpos : (0 : Fin 5) < (H.q ⟨0, by omega⟩).1 := lt_of_le_of_ne (Fin.zero_le _) hc.symm
          simpa [dualPt, hb] using G.a_mono hpos
        · have h1 := G.a_mono.monotone (Fin.zero_le (H.q ⟨0, by omega⟩).1)
          have h2 := G.ac (H.q ⟨0, by omega⟩).1
          simp only [dualPt, hb, ↓reduceIte, Bool.false_eq_true]; linarith
      have := H.hq_min (0, false)
      linarith
    have hq_last_eq : H.q ⟨H.h - 1, by omega⟩ = (cPerm G 4, true) := by
      by_contra hne
      have hlt_last : (dualPt G.f (H.q ⟨H.h - 1, by omega⟩)).1 < (dualPt G.f (cPerm G 4, true)).1 := by
        cases hb : (H.q ⟨H.h - 1, by omega⟩).2
        · have h1 := G.ac (H.q ⟨H.h - 1, by omega⟩).1
          have h2 := cPerm_strictMono G |>.monotone (Fin.le_last ((cPerm G).symm (H.q ⟨H.h - 1, by omega⟩).1))
          simp only [dualPt, hb, ↓reduceIte, Bool.false_eq_true] at *
          linarith [show (G.f (H.q ⟨H.h - 1, by omega⟩).1).c ≤ (G.f (cPerm G 4)).c by simpa using h2]
        · have hc : (cPerm G).symm (H.q ⟨H.h - 1, by omega⟩).1 < 4 :=
            lt_of_le_of_ne (Fin.le_last _) (fun h => hne (Prod.ext (by rw [← h]; simp) hb))
          simpa [dualPt, hb] using cPerm_strictMono G hc
      have := H.hq_max (cPerm G 4, true)
      linarith
    have hX0 : X = 0 := by
      have := kbar_at_blockVal H ⟨0, by omega⟩
      have hbv0 : blockVal H ⟨0, by omega⟩ = 0 := blockVal_zero H
      have hi1_0 : i₁ = 0 := Fin.ext h05.1
      have hfeq : (⟨blockVal H ⟨0, by omega⟩, blockVal_lt_n H ⟨0, by omega⟩⟩ : Fin H.n) = ⟨0, by omega⟩ :=
        Fin.ext hbv0
      rw [hfeq] at this
      dsimp [X, k6]; rw [hi1_0]; change kbar H ⟨0, by omega⟩ = 0; rw [← this, hq0_eq]
    have hXs4 : X = cPerm G 4 := by
      have := kbar_at_blockVal H ⟨H.h - 1, by omega⟩
      have hbvl : blockVal H ⟨H.h - 1, by omega⟩ = 5 := by rw [blockVal_last H, hn6]
      have hi2_5 : i₂ = 5 := Fin.ext h05.2
      dsimp [X]; rw [hki_eq]; dsimp [k6]; rw [hi2_5]
      have hfeq : (⟨blockVal H ⟨H.h - 1, by omega⟩, blockVal_lt_n H ⟨H.h - 1, by omega⟩⟩ : Fin H.n) = ⟨5, by omega⟩ :=
        Fin.ext hbvl
      rw [hfeq] at this
      change kbar H ⟨5, by omega⟩ = cPerm G 4
      rw [← this, hq_last_eq]
    have hsym : (cPerm G).symm 0 = 4 := by
      rw [show (0 : Fin 5) = cPerm G 4 from hX0.symm.trans hXs4]; simp
    have hinv4 : 4 ≤ permInvCount5 (cPerm G) := v_sigma1_ne_5_and_top2_ne_45.2.1 (cPerm G) hsym
    rw [cPerm_invCount_eq G] at hinv4
    have hcons := W.h_cons
    omega
  · -- Remaining 9 pairs `(i₁, i₂)`: `k6` is injective on `Finset.univ.erase i₂`, giving `π : Equiv.Perm (Fin 5)`!
    let S_no2 : Finset (Fin 6) := Finset.univ.erase i₂
    have himg_eq : S_no2.image k6 = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr; intro c
      obtain ⟨j, hj⟩ := hk6_surj c
      by_cases hj2 : j = i₂
      · subst hj2; exact Finset.mem_image.mpr ⟨i₁, Finset.mem_erase.mpr ⟨ne_of_lt hi12, Finset.mem_univ _⟩, hki_eq.trans hj⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj2, Finset.mem_univ _⟩, hj⟩
    have hinjOn : Set.InjOn k6 S_no2 := by
      apply Finset.injOn_of_card_image_eq
      simp [S_no2, himg_eq, Finset.card_erase_of_mem]
    let otherFin : Finset (Fin 6) := S_no2.erase i₁
    have hother_card : otherFin.card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_lt hi12, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    let otherEmb : Fin 4 ↪o Fin 6 := otherFin.orderEmbOfFin hother_card
    let piFun : Fin 5 → Fin 5 := fun c =>
      if h : c = 0 then X else k6 (otherEmb ⟨c.val - 1, by have := c.isLt; have : c.val ≠ 0 := fun h0 => h (Fin.ext h0); omega⟩)
    have hpi_inj : Function.Injective piFun := by
      intro c₁ c₂ heq
      dsimp [piFun] at heq
      split_ifs at heq with h1 h2 h2
      · rw [h1, h2]
      · exfalso
        have hc2_lt : c₂.val - 1 < 4 := by have := c₂.isLt; have : c₂.val ≠ 0 := fun h0 => h2 (Fin.ext h0); omega
        have hmem1 : i₁ ∈ S_no2 := Finset.mem_erase.mpr ⟨ne_of_lt hi12, Finset.mem_univ _⟩
        have hmem2 : otherEmb ⟨c₂.val - 1, hc2_lt⟩ ∈ S_no2 :=
          Finset.erase_subset _ _ (Finset.orderEmbOfFin_mem otherFin hother_card ⟨c₂.val - 1, hc2_lt⟩)
        have h_eq := hinjOn hmem1 hmem2 heq
        have h_not : otherEmb ⟨c₂.val - 1, hc2_lt⟩ ≠ i₁ :=
          (Finset.mem_erase.mp (Finset.orderEmbOfFin_mem otherFin hother_card ⟨c₂.val - 1, hc2_lt⟩)).1
        exact h_not h_eq.symm
      · exfalso
        have hc1_lt : c₁.val - 1 < 4 := by have := c₁.isLt; have : c₁.val ≠ 0 := fun h0 => h1 (Fin.ext h0); omega
        have hmem1 : i₁ ∈ S_no2 := Finset.mem_erase.mpr ⟨ne_of_lt hi12, Finset.mem_univ _⟩
        have hmem2 : otherEmb ⟨c₁.val - 1, hc1_lt⟩ ∈ S_no2 :=
          Finset.erase_subset _ _ (Finset.orderEmbOfFin_mem otherFin hother_card ⟨c₁.val - 1, hc1_lt⟩)
        have h_eq := hinjOn hmem2 hmem1 heq
        have h_not : otherEmb ⟨c₁.val - 1, hc1_lt⟩ ≠ i₁ :=
          (Finset.mem_erase.mp (Finset.orderEmbOfFin_mem otherFin hother_card ⟨c₁.val - 1, hc1_lt⟩)).1
        exact h_not h_eq
      · have hc1_lt : c₁.val - 1 < 4 := by have := c₁.isLt; have : c₁.val ≠ 0 := fun h0 => h1 (Fin.ext h0); omega
        have hc2_lt : c₂.val - 1 < 4 := by have := c₂.isLt; have : c₂.val ≠ 0 := fun h0 => h2 (Fin.ext h0); omega
        have hm1 : otherEmb ⟨c₁.val - 1, hc1_lt⟩ ∈ S_no2 :=
          Finset.erase_subset _ _ (Finset.orderEmbOfFin_mem otherFin hother_card ⟨c₁.val - 1, hc1_lt⟩)
        have hm2 : otherEmb ⟨c₂.val - 1, hc2_lt⟩ ∈ S_no2 :=
          Finset.erase_subset _ _ (Finset.orderEmbOfFin_mem otherFin hother_card ⟨c₂.val - 1, hc2_lt⟩)
        have h_eq := otherEmb.injective (hinjOn hm1 hm2 heq)
        have hv1 : c₁.val ≠ 0 := fun h0 => h1 (Fin.ext h0)
        have hv2 : c₂.val ≠ 0 := fun h0 => h2 (Fin.ext h0)
        have hveq : c₁.val - 1 = c₂.val - 1 := congrArg Fin.val h_eq
        exact Fin.ext (by omega)
    let π : Equiv.Perm (Fin 5) := Equiv.ofBijective piFun ((Fintype.bijective_iff_injective_and_card piFun).mpr ⟨hpi_inj, rfl⟩)
    have hπ0 : π 0 = X := rfl
    have hπ_other : ∀ r : Fin 4, π ⟨r.val + 1, by omega⟩ = k6 (otherEmb r) := fun r => by
      dsimp [π, Equiv.ofBijective, piFun]
      try simp [Fin.ext_iff]
    let slab4 (c : Fin 5) : Fin 5 :=
      if h : ∃ (p : Fin 5 × Bool), p ∈ R_int G.f ∧ p.1 = π c then
        ⟨fixedSlabIdx H (Classical.choose h) (Classical.choose_spec h).1, by
          have hle : fixedSlabIdx H (Classical.choose h) (Classical.choose_spec h).1 ≤ H.n - 2 := min_le_right _ _
          omega⟩
      else 0
    let code := (slab4 1).val + 5 * (slab4 2).val + 25 * (slab4 3).val + 125 * (slab4 4).val
    have hdiv1 : code % 5 = (slab4 1).val := by
      have h1 := (slab4 1).isLt; dsimp [code]; omega
    have hdiv2 : (code / 5) % 5 = (slab4 2).val := by
      have h1 := (slab4 1).isLt; have h2 := (slab4 2).isLt; dsimp [code]; omega
    have hdiv3 : (code / 25) % 5 = (slab4 3).val := by
      have h1 := (slab4 1).isLt; have h2 := (slab4 2).isLt; have h3 := (slab4 3).isLt; dsimp [code]; omega
    have hdiv4 : (code / 125) % 5 = (slab4 4).val := by
      have h1 := (slab4 1).isLt; have h2 := (slab4 2).isLt; have h3 := (slab4 3).isLt; have h4 := (slab4 4).isLt
      dsimp [code]; omega
    let w6 : Nat × Nat × Nat × Nat × Nat × Nat :=
      ((π.symm (k6 0)).val, (π.symm (k6 1)).val, (π.symm (k6 2)).val,
       (π.symm (k6 3)).val, (π.symm (k6 4)).val, (π.symm (k6 5)).val)
    let rankOtherB (a b j : Fin 6) : Nat :=
      if j == a || j == b then 0
      else ((List.finRange 6).filter (fun u => decide (u < j) && (u != a) && (u != b))).length + 1
    have hw6_val : ∀ j : Fin 6, (π.symm (k6 j)).val = rankOtherB i₁ i₂ j := by
      intro j
      dsimp [rankOtherB]
      split_ifs with hj12
      · have hj12' : j = i₁ ∨ j = i₂ := by simpa using hj12
        have hkj : k6 j = X := by rcases hj12' with rfl | rfl; rfl; exact hki_eq.symm
        rw [hkj, ← hπ0]; simp
      · have hj12' : j ≠ i₁ ∧ j ≠ i₂ := by simpa using hj12
        have hj_other : j ∈ otherFin := Finset.mem_erase.mpr ⟨hj12'.1, Finset.mem_erase.mpr ⟨hj12'.2, Finset.mem_univ _⟩⟩
        have hrange : j ∈ Set.range otherEmb := by simpa [otherEmb, Finset.range_orderEmbOfFin] using hj_other
        rcases hrange with ⟨r, hr⟩
        have hkj : k6 j = π ⟨r.val + 1, by omega⟩ := by rw [← hr, hπ_other r]
        rw [hkj]; simp only [Equiv.symm_apply_apply]
        have hcard_list : ((List.finRange 6).filter (fun u => decide (u < j) && (u != i₁) && (u != i₂))).length =
            (Finset.univ.filter (fun u : Fin 6 => u < j ∧ u ≠ i₁ ∧ u ≠ i₂)).card := by
          rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 6).filter _)]
          congr 1; apply Finset.ext; intro u
          simp [Bool.and_eq_true, and_assoc]
        rw [hcard_list]
        have hbij : Finset.univ.filter (fun u : Fin 6 => u < j ∧ u ≠ i₁ ∧ u ≠ i₂) =
            (Finset.univ.filter (fun s : Fin 4 => s < r)).image otherEmb := by
          apply Finset.ext; intro u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro ⟨hu1, hu2, hu3⟩
            have hu_other : u ∈ otherFin := Finset.mem_erase.mpr ⟨hu2, Finset.mem_erase.mpr ⟨hu3, Finset.mem_univ _⟩⟩
            obtain ⟨s, hs⟩ := show u ∈ Set.range otherEmb by simpa [otherEmb, Finset.range_orderEmbOfFin] using hu_other
            refine ⟨s, ?_, hs⟩
            rw [← hs, ← hr] at hu1
            exact (otherEmb.lt_iff_lt).mp hu1
          · rintro ⟨s, hs, rfl⟩
            have hs_mem := Finset.orderEmbOfFin_mem otherFin hother_card s
            exact ⟨by rw [← hr]; exact otherEmb.strictMono hs,
              (Finset.mem_erase.mp hs_mem).1, (Finset.mem_erase.mp (Finset.mem_erase.mp hs_mem).2).1⟩
        rw [hbij, Finset.card_image_of_injective _ otherEmb.injective]
        have hcard_r : (Finset.univ.filter (fun s : Fin 4 => s < r)).card = r.val := by
          have himg : Finset.univ.filter (fun s : Fin 4 => s < r) =
              (Finset.range r.val).attach.image (fun x => ⟨x.1, by have := Finset.mem_range.mp x.2; omega⟩) := by
            apply Finset.ext; intro s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach, true_and]
            constructor
            · intro hs; exact ⟨⟨s.val, Finset.mem_range.mpr hs⟩, Fin.ext rfl⟩
            · rintro ⟨⟨x, hx⟩, rfl⟩; exact Finset.mem_range.mp hx
          rw [himg, Finset.card_image_of_injective _ (fun x y h => Subtype.ext (congrArg Fin.val h)),
              Finset.card_attach, Finset.card_range]
        rw [hcard_r]
    have hw6_mem : w6 ∈ words6List := by
      have hdec : (List.finRange 6).all (fun a => (List.finRange 6).all (fun b =>
          if Nat.ble (a.val + 2) b.val && !(Nat.beq a.val 0 && Nat.beq b.val 5) then
            words6List.contains (rankOtherB a b 0, rankOtherB a b 1, rankOtherB a b 2,
              rankOtherB a b 3, rankOtherB a b 4, rankOtherB a b 5)
          else true)) = true := by decide
      have hm := List.all_eq_true.mp (List.all_eq_true.mp hdec i₁ (List.mem_finRange _)) i₂ (List.mem_finRange _)
      have hcond : (Nat.ble (i₁.val + 2) i₂.val && !(Nat.beq i₁.val 0 && Nat.beq i₂.val 5)) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true']
        refine ⟨hi12_gap, Bool.eq_false_iff.mpr fun h => h05 ?_⟩
        simp only [Bool.and_eq_true] at h
        exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩
      rw [if_pos hcond, List.contains_eq_mem] at hm
      simpa [w6, hw6_val 0, hw6_val 1, hw6_val 2, hw6_val 3, hw6_val 4, hw6_val 5] using hm
    obtain ⟨tMask, ht1, ht2, ht_bad⟩ :=
      n6_mask_counterexample w6 hw6_mem (slab4 1) (slab4 2) (slab4 3) (slab4 4)
    let S : Finset (Fin 5) := (maskToFinset5 tMask).image π
    have hSne : S.Nonempty := (maskToFinset5_nonempty tMask ht1 ht2).image π
    obtain ⟨a, b, hab, hb_lt, h_in_S, h_rest⟩ := dualRealizes_hull_slab_spec H G.dual S hSne
    let kAt (idx : Nat) : Nat :=
      if Nat.beq idx 0 then w6.1
      else if Nat.beq idx 1 then w6.2.1
      else if Nat.beq idx 2 then w6.2.2.1
      else if Nat.beq idx 3 then w6.2.2.2.1
      else if Nat.beq idx 4 then w6.2.2.2.2.1
      else w6.2.2.2.2.2
    have hkAt_eq : ∀ idx : Fin 6, kAt idx.val = (π.symm (k6 idx)).val := by
      intro idx; fin_cases idx <;> rfl
    have hbase : ((List.range (b + 1 - a)).map (fun d => a + d)).all
        (fun idx => bitSet tMask (kAt idx)) = true := by
      rw [List.all_eq_true]; intro idx hidx
      rcases List.mem_map.mp hidx with ⟨d, hd, rfl⟩
      have hd_lt := List.mem_range.mp hd
      have hidx6 : a + d < 6 := by omega
      have hmem_S : k6 ⟨a + d, hidx6⟩ ∈ S := h_in_S ⟨a + d, by omega⟩ (by dsimp; omega) (by dsimp; omega)
      rcases Finset.mem_image.mp hmem_S with ⟨c', hc', hpi⟩
      have hce : c' = π.symm (k6 ⟨a + d, hidx6⟩) := by rw [← hpi]; simp
      rw [hkAt_eq ⟨a + d, hidx6⟩, ← hce]
      exact (Finset.mem_filter.mp hc').2
    have h_real_true : [0, 1, 2, 3, 4].all (fun c =>
        if !(bitSet tMask c) then true
        else if ((List.range (b + 1 - a)).map (fun d => a + d)).any (fun idx => Nat.beq (kAt idx) c) then true
        else if Nat.beq c 0 then false
        else
          let j := if Nat.beq c 1 then code % 5
            else if Nat.beq c 2 then (code / 5) % 5
            else if Nat.beq c 3 then (code / 25) % 5
            else (code / 125) % 5
          Nat.ble a (j + 1) && Nat.ble j b) = true := by
      rw [List.all_eq_true]; intro c hc
      by_cases hc_bit : bitSet tMask c = true
      · simp only [hc_bit, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hc5 : c < 5 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; omega
        let c' : Fin 5 := ⟨c, hc5⟩
        have hc'_S : π c' ∈ S := Finset.mem_image_of_mem π (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_bit⟩)
        by_cases h_any : (((List.range (b + 1 - a)).map (fun d => a + d)).any (fun idx => Nat.beq (kAt idx) c)) = true
        · simp [h_any]
        · have h_any_false : (((List.range (b + 1 - a)).map (fun d => a + d)).any (fun idx => Nat.beq (kAt idx) c)) = false :=
            Bool.eq_false_of_not_eq_true h_any
          simp only [h_any_false, Bool.false_eq_true, ↓reduceIte]
          rcases h_rest (π c') hc'_S with ⟨j, hj1, hj2, hjc⟩ | ⟨p, hp, hpc, hsl1, hsl2⟩
          · exfalso; apply h_any
            rw [List.any_eq_true]
            refine ⟨j.val, List.mem_map.mpr ⟨j.val - a, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
            rw [hkAt_eq ⟨j.val, by omega⟩]
            have hkeq : k6 ⟨j.val, by omega⟩ = π c' := by simpa [k6] using hjc
            rw [hkeq]; simp [c']
          · have hc_ne0 : c ≠ 0 := by
              intro hc0
              have hc'0 : c' = 0 := Fin.ext hc0
              rw [hc'0, hπ0] at hpc
              exact hX_no_R ⟨p, hp, hpc⟩
            have hbeq0 : Nat.beq c 0 = false :=
              Bool.eq_false_iff.mpr (fun h => hc_ne0 (Nat.eq_of_beq_eq_true h))
            simp only [hbeq0, Bool.false_eq_true, ↓reduceIte]
            have hex : ∃ (p : Fin 5 × Bool), p ∈ R_int G.f ∧ p.1 = π c' := ⟨p, hp, hpc⟩
            have hp_eq : p = Classical.choose hex :=
              H.h_R_inj p hp (Classical.choose hex) (Classical.choose_spec hex).1
                (by rw [hpc, (Classical.choose_spec hex).2])
            have hslab_val : (slab4 c').val = fixedSlabIdx H p hp := by
              dsimp [slab4]; rw [dif_pos hex]; dsimp; congr 1; exact hp_eq.symm
            have hj_eq : (if Nat.beq c 1 then code % 5
                else if Nat.beq c 2 then (code / 5) % 5
                else if Nat.beq c 3 then (code / 25) % 5
                else (code / 125) % 5) = (slab4 c').val := by
              have hc_cases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
              rcases hc_cases with rfl | rfl | rfl | rfl | rfl
              · exact absurd rfl hc_ne0
              · simpa [c'] using hdiv1
              · simpa [c'] using hdiv2
              · simpa [c'] using hdiv3
              · simpa [c'] using hdiv4
            rw [hj_eq, hslab_val]
            simp [Nat.ble_eq, hsl1, hsl2]
      · simp [hc_bit]
    have hfalse := ht_bad a b hab (by omega) hbase
    exact absurd h_real_true (Bool.eq_false_iff.mp hfalse)

lemma v_epigraph_contradiction (G : GenericVSystem) : False := by
  obtain ⟨H⟩ := build_hullData G.f G.slopes_inj G.noncol G.dual
  obtain ⟨W⟩ := build_sweepData G H
  have hn_ge5 : 5 ≤ H.n := hull_n_ge_5 H
  have hn_le7 : H.n ≤ 7 := hull_n_le_7 W
  interval_cases hn : H.n
  · exact elim_n5 hn
  · exact elim_n6 W hn
  · exact elim_n7 W hn

theorem five_v_epigraphs_not_all_32_masks_proved (f₀ : Fin 5 → VFunc) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f₀ m p) := by
  intro hall
  obtain ⟨f, h_ac, h_mono, h_inj, h_noncol, h_dual, h_realizes, h_kinks, h_vals, h_disj, h_gpb_kink⟩ :=
    exists_generic_v_system f₀ hall
  exact v_epigraph_contradiction ⟨f, h_ac, h_mono, h_inj, h_noncol, h_dual, h_realizes, h_kinks, h_vals, h_disj, h_gpb_kink⟩

end Sec9

end



