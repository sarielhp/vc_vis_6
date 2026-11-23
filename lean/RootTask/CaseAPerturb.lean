import RootTask.CaseAChart

open Finset
open Classical

noncomputable section

namespace CaseA

/-- Normalized dual configuration of five origin-containing wedges with apices in `Q₃`. -/
structure DualConfig where
  p1 : Fin 5 → ℝ × ℝ
  p2 : Fin 5 → ℝ × ℝ
  h_det : ∀ i : Fin 5, 0 < det2 (p1 i) (p2 i)
  h_apex : ∀ i : Fin 5,
    InQ3 (((p2 i).2 - (p1 i).2) / det2 (p1 i) (p2 i),
          ((p1 i).1 - (p2 i).1) / det2 (p1 i) (p2 i))

/-- Enumeration `q_0, ..., q_9` of the `10` dual branch vectors. -/
def DualConfig.vec (P : DualConfig) (a : Fin 10) : ℝ × ℝ :=
  if a.val % 2 = 0 then P.p1 ⟨a.val / 2, by omega⟩
  else P.p2 ⟨a.val / 2, by omega⟩

/-- Wedge color index `⌊a / 2⌋ ∈ Fin 5` of `P.vec a`. -/
def vecColor (a : Fin 10) : Fin 5 :=
  ⟨a.val / 2, by omega⟩

/-- Unique primal apex `y_i ∈ Q₃` solving `dot2 (p_{i,1}) y_i = dot2 (p_{i,2}) y_i = 1`. -/
def DualConfig.apex (P : DualConfig) (i : Fin 5) : ℝ × ℝ :=
  (((P.p2 i).2 - (P.p1 i).2) / det2 (P.p1 i) (P.p2 i),
   ((P.p1 i).1 - (P.p2 i).1) / det2 (P.p1 i) (P.p2 i))

/-- Dual open-wedge membership `max_s ⟨p_{i,s}, z⟩ < 1`. -/
def DualConfig.MemOpen (P : DualConfig) (i : Fin 5) (z : ℝ × ℝ) : Prop :=
  dot2 (P.p1 i) z < 1 ∧ dot2 (P.p2 i) z < 1

/-- Dual strict-exterior membership `max_s ⟨p_{i,s}, z⟩ > 1`. -/
def DualConfig.MemExt (P : DualConfig) (i : Fin 5) (z : ℝ × ℝ) : Prop :=
  1 < dot2 (P.p1 i) z ∨ 1 < dot2 (P.p2 i) z

/-- Realization of a Boolean mask `m : Fin 5 → Bool` by `z ∈ ℝ²` in dual gauge form. -/
def RealizesDualMask (P : DualConfig) (m : Fin 5 → Bool) (z : ℝ × ℝ) : Prop :=
  ∀ i : Fin 5, if m i then P.MemOpen i z else P.MemExt i z

/-- Coordinate-swapped dual configuration reversing branch order to preserve `det2 > 0`. -/
def DualConfig.swap (P : DualConfig) : DualConfig where
  p1 := fun i => swap2 (P.p2 i)
  p2 := fun i => swap2 (P.p1 i)
  h_det := fun i => by
    rw [det2_swap2, det2_antisymm, neg_neg]
    exact P.h_det i
  h_apex := fun i => by
    have hdet_eq : det2 (swap2 (P.p2 i)) (swap2 (P.p1 i)) = det2 (P.p1 i) (P.p2 i) := by
      rw [det2_swap2, det2_antisymm, neg_neg]
    rw [hdet_eq]
    have hq3 := P.h_apex i
    dsimp [swap2, InQ3] at hq3 ⊢
    exact ⟨hq3.2, hq3.1⟩

/-- Full general-position predicate (GP1)--(GP4) on the `10` dual vectors `P.vec`. -/
def IsGenPos (P : DualConfig) : Prop :=
  (∀ a : Fin 10, (P.vec a).1 ≠ 0 ∧ (P.vec a).2 ≠ 0) ∧
  (∀ a b : Fin 10, a ≠ b → (P.vec a).1 ≠ (P.vec b).1 ∧ (P.vec a).2 ≠ (P.vec b).2) ∧
  (∀ a b : Fin 10, a ≠ b → det2 (P.vec a) (P.vec b) ≠ 0) ∧
  (∀ a b c : Fin 10, a ≠ b → det2 (P.vec a - P.vec b) (P.vec c) ≠ 0) ∧
  (∀ a b c d : Fin 10, a < b → c < d → (a, b) ≠ (c, d) →
    det2 (P.vec a - P.vec b) (P.vec c - P.vec d) ≠ 0)

/-- Internal mirror of `VFunc` inside `namespace CaseA`. -/
structure VFuncData where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  hle : a ≤ c

/-- Evaluation of `VFuncData` at `x ∈ ℝ`. -/
def VFuncData.eval (f : VFuncData) (x : ℝ) : ℝ :=
  max (f.a * x + f.b) (f.c * x + f.d)

/-- Realization of a Boolean mask `m` by `p ∈ ℝ²` for `f : Fin 5 → VFuncData`. -/
def RealizesVDataMask (f : Fin 5 → VFuncData) (m : Fin 5 → Bool) (p : ℝ × ℝ) : Prop :=
  ∀ i : Fin 5, if m i then (f i).eval p.1 < p.2 else p.2 < (f i).eval p.1

/-- Apex gauge equations and difference-normal determinant identity for `DualConfig`. -/
theorem DualConfig.apex_spec (P : DualConfig) (i : Fin 5) :
    InQ3 (P.apex i) ∧
    dot2 (P.p1 i) (P.apex i) = 1 ∧
    dot2 (P.p2 i) (P.apex i) = 1 ∧
    (∀ v : ℝ × ℝ, dot2 (P.p2 i - P.p1 i) v = det2 (P.p1 i) (P.p2 i) * det2 (P.apex i) v) := by
  have hne : det2 (P.p1 i) (P.p2 i) ≠ 0 := ne_of_gt (P.h_det i)
  refine ⟨P.h_apex i, ?_, ?_, ?_⟩
  · unfold dot2 DualConfig.apex
    dsimp
    have h1 : (P.p1 i).1 * (((P.p2 i).2 - (P.p1 i).2) / det2 (P.p1 i) (P.p2 i)) +
        (P.p1 i).2 * (((P.p1 i).1 - (P.p2 i).1) / det2 (P.p1 i) (P.p2 i)) =
        det2 (P.p1 i) (P.p2 i) / det2 (P.p1 i) (P.p2 i) := by
      unfold det2; ring
    rw [h1, div_self hne]
  · unfold dot2 DualConfig.apex
    dsimp
    have h1 : (P.p2 i).1 * (((P.p2 i).2 - (P.p1 i).2) / det2 (P.p1 i) (P.p2 i)) +
        (P.p2 i).2 * (((P.p1 i).1 - (P.p2 i).1) / det2 (P.p1 i) (P.p2 i)) =
        det2 (P.p1 i) (P.p2 i) / det2 (P.p1 i) (P.p2 i) := by
      unfold det2; ring
    rw [h1, div_self hne]
  · intro v
    unfold dot2 DualConfig.apex
    dsimp
    have h1 : det2 (P.p1 i) (P.p2 i) *
        ((((P.p2 i).2 - (P.p1 i).2) / det2 (P.p1 i) (P.p2 i)) * v.2 -
         (((P.p1 i).1 - (P.p2 i).1) / det2 (P.p1 i) (P.p2 i)) * v.1) =
        (((P.p2 i).2 - (P.p1 i).2) * v.2 - ((P.p1 i).1 - (P.p2 i).1) * v.1) *
        (det2 (P.p1 i) (P.p2 i) / det2 (P.p1 i) (P.p2 i)) := by ring
    rw [div_self hne] at h1
    unfold det2 at h1 ⊢
    dsimp at h1 ⊢
    linear_combination -h1

theorem DualConfig.vec_even (P : DualConfig) (i : Fin 5) :
    P.vec ⟨2 * i.val, by omega⟩ = P.p1 i := by
  unfold DualConfig.vec
  simp

theorem DualConfig.vec_odd (P : DualConfig) (i : Fin 5) :
    P.vec ⟨2 * i.val + 1, by omega⟩ = P.p2 i := by
  unfold DualConfig.vec
  have hmod : (2 * i.val + 1) % 2 = 1 := by omega
  have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
  simp [hmod, hdiv]

/-- Every dual branch vector `P.vec a` lies in `Ω` since `⟨p_{i,s}, y_i⟩ = 1` with `y_i ∈ Q₃`. -/
theorem DualConfig.vec_inOmega (P : DualConfig) (a : Fin 10) : InOmega (P.vec a) := by
  unfold DualConfig.vec
  split_ifs with h
  · let i : Fin 5 := ⟨a.val / 2, by omega⟩
    obtain ⟨⟨hy1, hy2⟩, hd1, _, _⟩ := P.apex_spec i
    by_contra hnot
    rcases not_or.mp hnot with ⟨h1, h2⟩
    have hge1 : 0 ≤ (P.p1 i).1 := not_lt.mp h1
    have hge2 : 0 ≤ (P.p1 i).2 := not_lt.mp h2
    unfold dot2 at hd1
    nlinarith
  · let i : Fin 5 := ⟨a.val / 2, by omega⟩
    obtain ⟨⟨hy1, hy2⟩, _, hd2, _⟩ := P.apex_spec i
    by_contra hnot
    rcases not_or.mp hnot with ⟨h1, h2⟩
    have hge1 : 0 ≤ (P.p2 i).1 := not_lt.mp h1
    have hge2 : 0 ≤ (P.p2 i).2 := not_lt.mp h2
    unfold dot2 at hd2
    nlinarith

/-- Primal-to-dual normalization from five origin-containing wedges with apices in `Q₃`. -/
theorem DualConfig.ofPrimal_spec
    (y u₁ u₂ : Fin 5 → ℝ × ℝ)
    (h_nondeg : ∀ i : Fin 5, 0 < det2 (u₁ i) (u₂ i))
    (h_apex : ∀ i : Fin 5, InQ3 (y i))
    (h_orig : ∀ i : Fin 5, 0 < -dot2 (u₁ i) (y i) ∧ 0 < -dot2 (u₂ i) (y i)) :
    ∃ P : DualConfig,
      (∀ i : Fin 5, P.apex i = y i) ∧
      (∀ (i : Fin 5) (z : ℝ × ℝ),
        (P.MemOpen i z ↔
          0 < (u₁ i).1 * (z.1 - (y i).1) + (u₁ i).2 * (z.2 - (y i).2) ∧
          0 < (u₂ i).1 * (z.1 - (y i).1) + (u₂ i).2 * (z.2 - (y i).2)) ∧
        (P.MemExt i z ↔
          (u₁ i).1 * (z.1 - (y i).1) + (u₁ i).2 * (z.2 - (y i).2) < 0 ∨
          (u₂ i).1 * (z.1 - (y i).1) + (u₂ i).2 * (z.2 - (y i).2) < 0)) := by
  let c₁ : Fin 5 → ℝ := fun i => -dot2 (u₁ i) (y i)
  let c₂ : Fin 5 → ℝ := fun i => -dot2 (u₂ i) (y i)
  let q₁ : Fin 5 → ℝ × ℝ := fun i => (-1 / c₁ i) • u₁ i
  let q₂ : Fin 5 → ℝ × ℝ := fun i => (-1 / c₂ i) • u₂ i
  have hc1 : ∀ i, 0 < c₁ i := fun i => (h_orig i).1
  have hc2 : ∀ i, 0 < c₂ i := fun i => (h_orig i).2
  have hdet_q_eq : ∀ i, det2 (q₁ i) (q₂ i) = (1 / (c₁ i * c₂ i)) * det2 (u₁ i) (u₂ i) := by
    intro i
    dsimp [q₁, q₂]; simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hdet_q : ∀ i, 0 < det2 (q₁ i) (q₂ i) := fun i => by
    rw [hdet_q_eq i]
    exact mul_pos (div_pos one_pos (mul_pos (hc1 i) (hc2 i))) (h_nondeg i)
  have hapex_eq : ∀ i,
      (((q₂ i).2 - (q₁ i).2) / det2 (q₁ i) (q₂ i),
       ((q₁ i).1 - (q₂ i).1) / det2 (q₁ i) (q₂ i)) = y i := by
    intro i
    have hc1_ne : c₁ i ≠ 0 := ne_of_gt (hc1 i)
    have hc2_ne : c₂ i ≠ 0 := ne_of_gt (hc2 i)
    have hqd_ne : det2 (q₁ i) (q₂ i) ≠ 0 := ne_of_gt (hdet_q i)
    have hcc_ne : c₁ i * c₂ i ≠ 0 := mul_ne_zero hc1_ne hc2_ne
    ext
    · apply mul_right_cancel₀ hqd_ne
      rw [div_mul_cancel₀ _ hqd_ne, hdet_q_eq i]
      apply mul_right_cancel₀ hcc_ne
      have lhs_eq : ((q₂ i).2 - (q₁ i).2) * (c₁ i * c₂ i) =
          -(u₂ i).2 * c₁ i * (c₂ i / c₂ i) + (u₁ i).2 * c₂ i * (c₁ i / c₁ i) := by
        dsimp [q₁, q₂]; ring
      have rhs_eq : (y i).1 * (1 / (c₁ i * c₂ i) * det2 (u₁ i) (u₂ i)) * (c₁ i * c₂ i) =
          (y i).1 * det2 (u₁ i) (u₂ i) * ((c₁ i * c₂ i) / (c₁ i * c₂ i)) := by ring
      rw [lhs_eq, rhs_eq, div_self hc1_ne, div_self hc2_ne, div_self hcc_ne]
      simp only [c₁, c₂, dot2, det2]; ring
    · apply mul_right_cancel₀ hqd_ne
      rw [div_mul_cancel₀ _ hqd_ne, hdet_q_eq i]
      apply mul_right_cancel₀ hcc_ne
      have lhs_eq : ((q₁ i).1 - (q₂ i).1) * (c₁ i * c₂ i) =
          -(u₁ i).1 * c₂ i * (c₁ i / c₁ i) + (u₂ i).1 * c₁ i * (c₂ i / c₂ i) := by
        dsimp [q₁, q₂]; ring
      have rhs_eq : (y i).2 * (1 / (c₁ i * c₂ i) * det2 (u₁ i) (u₂ i)) * (c₁ i * c₂ i) =
          (y i).2 * det2 (u₁ i) (u₂ i) * ((c₁ i * c₂ i) / (c₁ i * c₂ i)) := by ring
      rw [lhs_eq, rhs_eq, div_self hc1_ne, div_self hc2_ne, div_self hcc_ne]
      simp only [c₁, c₂, dot2, det2]; ring
  refine ⟨{ p1 := q₁, p2 := q₂, h_det := hdet_q,
            h_apex := fun i => by rw [hapex_eq i]; exact h_apex i },
          hapex_eq, fun i z => ?_⟩
  have hid1 : (u₁ i).1 * (z.1 - (y i).1) + (u₁ i).2 * (z.2 - (y i).2) =
      c₁ i * (1 - dot2 (q₁ i) z) := by
    have hc1_ne : c₁ i ≠ 0 := ne_of_gt (hc1 i)
    have hinv : c₁ i * (-1 / c₁ i) = -1 := by linear_combination div_mul_cancel₀ (-1 : ℝ) hc1_ne
    have hmul : c₁ i * dot2 (q₁ i) z = -dot2 (u₁ i) z := by
      dsimp [q₁]; rw [dot2_smul_left]; linear_combination dot2 (u₁ i) z * hinv
    have hsub : c₁ i * (1 - dot2 (q₁ i) z) = c₁ i - c₁ i * dot2 (q₁ i) z := by ring
    rw [hsub, hmul]
    dsimp [c₁, dot2]; ring
  have hid2 : (u₂ i).1 * (z.1 - (y i).1) + (u₂ i).2 * (z.2 - (y i).2) =
      c₂ i * (1 - dot2 (q₂ i) z) := by
    have hc2_ne : c₂ i ≠ 0 := ne_of_gt (hc2 i)
    have hinv : c₂ i * (-1 / c₂ i) = -1 := by linear_combination div_mul_cancel₀ (-1 : ℝ) hc2_ne
    have hmul : c₂ i * dot2 (q₂ i) z = -dot2 (u₂ i) z := by
      dsimp [q₂]; rw [dot2_smul_left]; linear_combination dot2 (u₂ i) z * hinv
    have hsub : c₂ i * (1 - dot2 (q₂ i) z) = c₂ i - c₂ i * dot2 (q₂ i) z := by ring
    rw [hsub, hmul]
    dsimp [c₂, dot2]; ring
  have h1 := hc1 i
  have h2 := hc2 i
  unfold DualConfig.MemOpen DualConfig.MemExt
  dsimp
  rw [hid1, hid2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨ha, hb⟩; exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨by nlinarith, by nlinarith⟩
  · rintro (ha | hb)
    · left; nlinarith
    · right; nlinarith
  · rintro (ha | hb)
    · left; nlinarith
    · right; nlinarith

/-- Swap involution properties for `DualConfig.swap`. -/
theorem DualConfig.swap_spec (P : DualConfig) :
    (∀ i : Fin 5, P.swap.apex i = swap2 (P.apex i)) ∧
    (IsGenPos P.swap ↔ IsGenPos P) ∧
    (∀ (m : Fin 5 → Bool) (z : ℝ × ℝ),
      RealizesDualMask P.swap m (swap2 z) ↔ RealizesDualMask P m z) := by
  have hapex : ∀ i : Fin 5, P.swap.apex i = swap2 (P.apex i) := by
    intro i
    have hdet_eq : det2 (swap2 (P.p2 i)) (swap2 (P.p1 i)) = det2 (P.p1 i) (P.p2 i) := by
      rw [det2_swap2, det2_antisymm, neg_neg]
    unfold DualConfig.apex DualConfig.swap; dsimp; rw [hdet_eq]; rfl
  have hmask : ∀ (P' : DualConfig) (m : Fin 5 → Bool) (z : ℝ × ℝ),
      RealizesDualMask P'.swap m (swap2 z) ↔ RealizesDualMask P' m z := by
    intro P' m z
    unfold RealizesDualMask DualConfig.MemOpen DualConfig.MemExt DualConfig.swap
    refine forall_congr' fun i => ?_
    dsimp
    rw [dot2_swap2, dot2_swap2, and_comm, or_comm]
  have hperm : ∃ e : Equiv.Perm (Fin 10), ∀ (P' : DualConfig) (a : Fin 10),
      P'.swap.vec a = swap2 (P'.vec (e a)) := by
    refine ⟨{ toFun := fun a => ⟨2 * (a.val / 2) + (1 - a.val % 2), by omega⟩
              invFun := fun a => ⟨2 * (a.val / 2) + (1 - a.val % 2), by omega⟩
              left_inv := fun a => by ext; dsimp; omega
              right_inv := fun a => by ext; dsimp; omega }, fun P' a => ?_⟩
    fin_cases a <;> rfl
  have hgp_imp : ∀ P' : DualConfig, IsGenPos P' → IsGenPos P'.swap := by
    intro P' ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨e, he⟩ := hperm
    have hsub_swap : ∀ u v : ℝ × ℝ, swap2 u - swap2 v = swap2 (u - v) := by
      intro u v; ext <;> rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a; rw [he P' a]; exact ⟨(h1 (e a)).2, (h1 (e a)).1⟩
    · intro a b hab
      rw [he P' a, he P' b]
      have heb : e a ≠ e b := fun h => hab (e.injective h)
      exact ⟨(h2 (e a) (e b) heb).2, (h2 (e a) (e b) heb).1⟩
    · intro a b hab
      rw [he P' a, he P' b, det2_swap2, neg_ne_zero]
      exact h3 (e a) (e b) (fun h => hab (e.injective h))
    · intro a b c hab
      rw [he P' a, he P' b, he P' c, hsub_swap, det2_swap2, neg_ne_zero]
      exact h4 (e a) (e b) (e c) (fun h => hab (e.injective h))
    · intro a b c d hab hcd hne
      rw [he P' a, he P' b, he P' c, he P' d, hsub_swap, hsub_swap, det2_swap2, neg_ne_zero]
      have hea_ne : e a ≠ e b := fun h => ne_of_lt hab (e.injective h)
      have hec_ne : e c ≠ e d := fun h => ne_of_lt hcd (e.injective h)
      rcases lt_or_gt_of_ne hea_ne with h1_lt | h1_gt <;>
      rcases lt_or_gt_of_ne hec_ne with h2_lt | h2_gt
      · exact h5 (e a) (e b) (e c) (e d) h1_lt h2_lt (by
          intro hp
          exact hne (Prod.ext (e.injective (congrArg Prod.fst hp)) (e.injective (congrArg Prod.snd hp))))
      · have hneg : det2 (P'.vec (e a) - P'.vec (e b)) (P'.vec (e c) - P'.vec (e d)) =
            -det2 (P'.vec (e a) - P'.vec (e b)) (P'.vec (e d) - P'.vec (e c)) := by
          simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
        rw [hneg, neg_ne_zero]
        exact h5 (e a) (e b) (e d) (e c) h1_lt h2_gt (by
          intro hp
          have hac : e a = e d := congrArg Prod.fst hp
          have hbd : e b = e c := congrArg Prod.snd hp
          have ha_eq : a = d := e.injective hac
          have hb_eq : b = c := e.injective hbd
          subst ha_eq hb_eq
          -- Note e flips pairs within the same color block `2k, 2k+1`, check impossibility:
          omega)
      · have hneg : det2 (P'.vec (e a) - P'.vec (e b)) (P'.vec (e c) - P'.vec (e d)) =
            -det2 (P'.vec (e b) - P'.vec (e a)) (P'.vec (e c) - P'.vec (e d)) := by
          simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
        rw [hneg, neg_ne_zero]
        exact h5 (e b) (e a) (e c) (e d) h1_gt h2_lt (by
          intro hp
          have hbc : e b = e c := congrArg Prod.fst hp
          have had : e a = e d := congrArg Prod.snd hp
          have hb_eq : b = c := e.injective hbc
          have ha_eq : a = d := e.injective had
          subst hb_eq ha_eq
          omega)
      · have heq_sign : det2 (P'.vec (e a) - P'.vec (e b)) (P'.vec (e c) - P'.vec (e d)) =
            det2 (P'.vec (e b) - P'.vec (e a)) (P'.vec (e d) - P'.vec (e c)) := by
          simp only [det2, Prod.fst_sub, Prod.snd_sub]; ring
        rw [heq_sign]
        exact h5 (e b) (e a) (e d) (e c) h1_gt h2_gt (by
          intro hp
          have hbd : e b = e d := congrArg Prod.fst hp
          have hac : e a = e c := congrArg Prod.snd hp
          exact hne (Prod.ext (e.injective hac) (e.injective hbd)))
  have hswap_invol : P.swap.swap = P := by
    cases P
    simp [DualConfig.swap, swap2]
  refine ⟨hapex, ⟨fun h => hswap_invol ▸ hgp_imp P.swap h, hgp_imp P⟩, hmask P⟩

/-- Every open square `(x₀.1 - δ, x₀.1 + δ) × (x₀.2 - δ, x₀.2 + δ)` in `ℝ²` (`δ > 0`) contains
a point avoiding any finite list of nondegenerate affine lines `α x₁ + β x₂ + γ = 0`. -/
theorem exists_not_on_lines_in_square (x₀ : ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ)
    (lines : List (ℝ × ℝ × ℝ))
    (hnondeg : ∀ ℓ ∈ lines, ℓ.1 ≠ 0 ∨ ℓ.2.1 ≠ 0) :
    ∃ x : ℝ × ℝ, |x.1 - x₀.1| < δ ∧ |x.2 - x₀.2| < δ ∧
      ∀ ℓ ∈ lines, ℓ.1 * x.1 + ℓ.2.1 * x.2 + ℓ.2.2 ≠ 0 := by
  classical
  let badX1 : Finset ℝ := (lines.toFinset.filter (fun ℓ => ℓ.2.1 = 0)).image
    (fun ℓ => -ℓ.2.2 / ℓ.1)
  have h_inf1 : (Set.Ioo (x₀.1 - δ) (x₀.1 + δ)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨x₁, hx₁_mem, hx₁_not⟩ := h_inf1.exists_notMem_finset badX1
  let badX2 : Finset ℝ := (lines.toFinset.filter (fun ℓ => ℓ.2.1 ≠ 0)).image
    (fun ℓ => -(ℓ.1 * x₁ + ℓ.2.2) / ℓ.2.1)
  have h_inf2 : (Set.Ioo (x₀.2 - δ) (x₀.2 + δ)).Infinite :=
    Set.Ioo_infinite (by linarith)
  obtain ⟨x₂, hx₂_mem, hx₂_not⟩ := h_inf2.exists_notMem_finset badX2
  rw [Set.mem_Ioo] at hx₁_mem hx₂_mem
  refine ⟨(x₁, x₂), abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩,
    abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩, ?_⟩
  intro ℓ hℓ heq
  by_cases hβ : ℓ.2.1 = 0
  · have hα : ℓ.1 ≠ 0 := (hnondeg ℓ hℓ).resolve_right (not_not.mpr hβ)
    have hx₁_eq : x₁ = -ℓ.2.2 / ℓ.1 := by
      rw [eq_div_iff hα]; linear_combination heq - x₂ * hβ
    apply hx₁_not
    rw [hx₁_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hℓ, hβ⟩)
  · have hx₂_eq : x₂ = -(ℓ.1 * x₁ + ℓ.2.2) / ℓ.2.1 := by
      rw [eq_div_iff hβ]; linear_combination heq
    apply hx₂_not
    rw [hx₂_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hℓ, hβ⟩)

private lemma open_stability_shattered (P₀ : DualConfig)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P₀ m z) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q : Fin 10 → ℝ × ℝ,
        (∀ a : Fin 10, |(q a).1 - (P₀.vec a).1| < δ ∧ |(q a).2 - (P₀.vec a).2| < δ) →
        ∃ P : DualConfig,
          (∀ a : Fin 10, P.vec a = q a) ∧
          (∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) := by
  classical
  let zWit : (Fin 5 → Bool) → ℝ × ℝ := fun m => Classical.choose (h_shat m)
  have hzWit_spec : ∀ m, InOmega (zWit m) ∧ RealizesDualMask P₀ m (zWit m) :=
    fun m => Classical.choose_spec (h_shat m)
  let U : Set (Fin 10 → ℝ × ℝ) :=
    (⋂ i : Fin 5, {q | 0 < det2 (q ⟨2 * i.val, by omega⟩) (q ⟨2 * i.val + 1, by omega⟩)}) ∩
    (⋂ i : Fin 5, {q | (q ⟨2 * i.val + 1, by omega⟩).2 - (q ⟨2 * i.val, by omega⟩).2 < 0 ∧
                       (q ⟨2 * i.val, by omega⟩).1 - (q ⟨2 * i.val + 1, by omega⟩).1 < 0}) ∩
    (⋂ m : Fin 5 → Bool, ⋂ i : Fin 5,
      {q | if m i then
             dot2 (q ⟨2 * i.val, by omega⟩) (zWit m) < 1 ∧
             dot2 (q ⟨2 * i.val + 1, by omega⟩) (zWit m) < 1
           else
             1 < dot2 (q ⟨2 * i.val, by omega⟩) (zWit m) ∨
             1 < dot2 (q ⟨2 * i.val + 1, by omega⟩) (zWit m)})
  have hc_coord : ∀ a : Fin 10, Continuous (fun q : Fin 10 → ℝ × ℝ => q a) :=
    fun a => continuous_apply a
  have hc_fst : ∀ a : Fin 10, Continuous (fun q : Fin 10 → ℝ × ℝ => (q a).1) :=
    fun a => continuous_fst.comp (hc_coord a)
  have hc_snd : ∀ a : Fin 10, Continuous (fun q : Fin 10 → ℝ × ℝ => (q a).2) :=
    fun a => continuous_snd.comp (hc_coord a)
  have hc_det : ∀ a b : Fin 10, Continuous (fun q : Fin 10 → ℝ × ℝ => det2 (q a) (q b)) :=
    fun a b => ((hc_fst a).mul (hc_snd b)).sub ((hc_snd a).mul (hc_fst b))
  have hc_dot : ∀ a : Fin 10, ∀ z : ℝ × ℝ,
      Continuous (fun q : Fin 10 → ℝ × ℝ => dot2 (q a) z) :=
    fun a z => ((hc_fst a).mul continuous_const).add ((hc_snd a).mul continuous_const)
  have hU_open : IsOpen U := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hc_det _ _)
    · refine isOpen_iInter_of_finite fun i => IsOpen.and
        (isOpen_lt ((hc_snd _).sub (hc_snd _)) continuous_const)
        (isOpen_lt ((hc_fst _).sub (hc_fst _)) continuous_const)
    · refine isOpen_iInter_of_finite fun m => isOpen_iInter_of_finite fun i => ?_
      by_cases hmi : m i
      · simp only [hmi, ↓reduceIte]
        exact IsOpen.and (isOpen_lt (hc_dot _ _) continuous_const)
          (isOpen_lt (hc_dot _ _) continuous_const)
      · simp only [hmi, Bool.false_eq_true, ↓reduceIte]
        exact IsOpen.union (isOpen_lt continuous_const (hc_dot _ _))
          (isOpen_lt continuous_const (hc_dot _ _))
  have hP0_mem : P₀.vec ∈ U := by
    simp only [U, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, fun m i => ?_⟩
    · rw [P₀.vec_even i, P₀.vec_odd i]; exact P₀.h_det i
    · rw [P₀.vec_even i, P₀.vec_odd i]
      have hdet := P₀.h_det i
      obtain ⟨ha1, ha2⟩ := P₀.h_apex i
      refine ⟨?_, ?_⟩
      · by_contra hle
        have hge : 0 ≤ (P₀.p2 i).2 - (P₀.p1 i).2 := not_lt.mp hle
        exact absurd (div_nonneg hge (le_of_lt hdet)) (not_le.mpr ha1)
      · by_contra hle
        have hge : 0 ≤ (P₀.p1 i).1 - (P₀.p2 i).1 := not_lt.mp hle
        exact absurd (div_nonneg hge (le_of_lt hdet)) (not_le.mpr ha2)
    · have hreal := (hzWit_spec m).2 i
      rw [P₀.vec_even i, P₀.vec_odd i]
      by_cases hmi : m i
      · simp only [hmi, ↓reduceIte] at hreal ⊢; exact hreal
      · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hreal ⊢; exact hreal
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU_open P₀.vec hP0_mem
  refine ⟨δ, hδ, fun q hq => ?_⟩
  have hq_ball : q ∈ Metric.ball P₀.vec δ := by
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    intro a
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    exact hq a
  have hqU := hball hq_ball
  simp only [U, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hqU
  refine ⟨{
    p1 := fun i => q ⟨2 * i.val, by omega⟩
    p2 := fun i => q ⟨2 * i.val + 1, by omega⟩
    h_det := hqU.1.1
    h_apex := fun i => ⟨div_neg_of_neg_of_pos (hqU.1.2 i).1 (hqU.1.1 i),
                        div_neg_of_neg_of_pos (hqU.1.2 i).2 (hqU.1.1 i)⟩
  }, ?_, ?_⟩
  · intro a
    unfold DualConfig.vec
    dsimp
    split_ifs with h
    · congr 1; ext; dsimp; omega
    · congr 1; ext; dsimp; omega
  · intro m
    refine ⟨zWit m, (hzWit_spec m).1, fun i => ?_⟩
    have hm := hqU.2 m i
    dsimp [DualConfig.MemOpen, DualConfig.MemExt] at hm ⊢
    by_cases hmi : m i
    · simp only [hmi, ↓reduceIte] at hm ⊢; exact hm
    · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm ⊢; exact hm

private def IsGenPosPrefix (q : Fin 10 → ℝ × ℝ) (n : ℕ) : Prop :=
  (∀ a : Fin 10, a.val < n → (q a).1 ≠ 0 ∧ (q a).2 ≠ 0) ∧
  (∀ a b : Fin 10, a.val < n → b.val < n → a ≠ b → (q a).1 ≠ (q b).1 ∧ (q a).2 ≠ (q b).2) ∧
  (∀ a b : Fin 10, a.val < n → b.val < n → a ≠ b → det2 (q a) (q b) ≠ 0) ∧
  (∀ a b c : Fin 10, a.val < n → b.val < n → c.val < n → a ≠ b →
    det2 (q a - q b) (q c) ≠ 0) ∧
  (∀ a b c d : Fin 10, a.val < n → b.val < n → c.val < n → d.val < n →
    a < b → c < d → (a, b) ≠ (c, d) → det2 (q a - q b) (q c - q d) ≠ 0)

private lemma genPos_step (q₀ : Fin 10 → ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ n : ℕ, n ≤ 10 →
      ∃ q : Fin 10 → ℝ × ℝ,
        (∀ a : Fin 10, |(q a).1 - (q₀ a).1| < δ ∧ |(q a).2 - (q₀ a).2| < δ) ∧
        IsGenPosPrefix q n
  | 0, _ => by
    refine ⟨q₀, fun a => by simp [hδ], ?_⟩
    refine ⟨fun a ha => by omega, fun a b ha => by omega, fun a b ha => by omega,
            fun a b c ha => by omega, fun a b c d ha => by omega⟩
  | n + 1, hn => by
    obtain ⟨q, hbox, hpre⟩ := genPos_step q₀ hδ n (by omega)
    let k : Fin 10 := ⟨n, hn⟩
    let prevS : Finset (Fin 10) := Finset.univ.filter fun a : Fin 10 => a.val < n
    let prev : List (Fin 10) := prevS.toList
    have hprev_iff : ∀ a : Fin 10, a ∈ prev ↔ a.val < n := fun a => by
      simp [prev, prevS]
    let pairsNeS : Finset (Fin 10 × Fin 10) := (prevS ×ˢ prevS).filter fun p => p.1 ≠ p.2
    let pairsLtS : Finset (Fin 10 × Fin 10) := (prevS ×ˢ prevS).filter fun p => p.1 < p.2
    let pairsAll : List (Fin 10 × Fin 10) := (prevS ×ˢ prevS).toList
    let pairsNe : List (Fin 10 × Fin 10) := pairsNeS.toList
    let triplesLt : List ((Fin 10 × Fin 10) × Fin 10) := (pairsLtS ×ˢ prevS).toList
    let lines1 : List (ℝ × ℝ × ℝ) := [(1, 0, 0), (0, 1, 0)]
    let lines2 : List (ℝ × ℝ × ℝ) := prev.map fun a => (1, 0, -(q a).1)
    let lines3 : List (ℝ × ℝ × ℝ) := prev.map fun a => (0, 1, -(q a).2)
    let lines4 : List (ℝ × ℝ × ℝ) := prev.map fun a => (-(q a).2, (q a).1, 0)
    let lines5 : List (ℝ × ℝ × ℝ) :=
      pairsNe.map fun p => (-(q p.1 - q p.2).2, (q p.1 - q p.2).1, 0)
    let lines6 : List (ℝ × ℝ × ℝ) :=
      pairsAll.map fun p =>
        ((q p.2).2, -(q p.2).1, (q p.1).2 * (q p.2).1 - (q p.1).1 * (q p.2).2)
    let lines7 : List (ℝ × ℝ × ℝ) :=
      triplesLt.map fun t =>
        ((q t.1.2 - q t.1.1).2, (q t.1.1 - q t.1.2).1, det2 (q t.2) (q t.1.1 - q t.1.2))
    let lines8 : List (ℝ × ℝ × ℝ) :=
      pairsNe.map fun p => (-(q p.2 - q p.1).2, (q p.2 - q p.1).1, det2 (q p.1) (q p.2))
    let lines : List (ℝ × ℝ × ℝ) :=
      lines1 ++ lines2 ++ lines3 ++ lines4 ++ lines5 ++ lines6 ++ lines7 ++ lines8
    have hnondeg : ∀ ℓ ∈ lines, ℓ.1 ≠ 0 ∨ ℓ.2.1 ≠ 0 := by
      intro ℓ hℓ
      simp only [lines, List.mem_append] at hℓ
      rcases hℓ with (((((((h | h) | h) | h) | h) | h) | h) | h)
      · simp only [lines1, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> [left; right] <;> norm_num
      · rcases List.mem_map.mp h with ⟨a, _, rfl⟩; left; norm_num
      · rcases List.mem_map.mp h with ⟨a, _, rfl⟩; right; norm_num
      · rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
        right; exact (hpre.1 a ((hprev_iff a).mp ha)).1
      · rcases List.mem_map.mp h with ⟨p, hp, rfl⟩
        simp only [pairsNe, pairsNeS, Finset.mem_toList, Finset.mem_filter,
          Finset.mem_product, Finset.mem_univ, true_and, prevS] at hp
        right
        have hne_x := (hpre.2.1 p.1 p.2 hp.1.1 hp.1.2 hp.2).1
        dsimp; exact sub_ne_zero.mpr hne_x
      · rcases List.mem_map.mp h with ⟨p, hp, rfl⟩
        simp only [pairsAll, Finset.mem_toList, Finset.mem_product, Finset.mem_filter,
          Finset.mem_univ, true_and, prevS] at hp
        left; exact (hpre.1 p.2 hp.2).2
      · rcases List.mem_map.mp h with ⟨t, ht, rfl⟩
        simp only [triplesLt, pairsLtS, Finset.mem_toList, Finset.mem_product, Finset.mem_filter,
          Finset.mem_univ, true_and, prevS] at ht
        right
        have hne_x := (hpre.2.1 t.1.1 t.1.2 ht.1.1.1 ht.1.1.2 (ne_of_lt ht.1.2)).1
        dsimp; exact sub_ne_zero.mpr hne_x
      · rcases List.mem_map.mp h with ⟨p, hp, rfl⟩
        simp only [pairsNe, pairsNeS, Finset.mem_toList, Finset.mem_filter,
          Finset.mem_product, Finset.mem_univ, true_and, prevS] at hp
        right
        have hne_x := (hpre.2.1 p.2 p.1 hp.1.2 hp.1.1 hp.2.symm).1
        dsimp; exact sub_ne_zero.mpr hne_x
    obtain ⟨x, hx1, hx2, hx_avoid⟩ := exists_not_on_lines_in_square (q₀ k) hδ lines hnondeg
    let q' : Fin 10 → ℝ × ℝ := Function.update q k x
    have hq'_lt : ∀ a : Fin 10, a.val < n → q' a = q a := fun a ha =>
      Function.update_of_ne (fun h => by subst h; dsimp [k] at ha; omega) _ _
    have hq'_k : q' k = x := Function.update_self k x q
    have hmem_lines : ∀ (part : List (ℝ × ℝ × ℝ)) (ℓ : ℝ × ℝ × ℝ),
        (part = lines1 ∨ part = lines2 ∨ part = lines3 ∨ part = lines4 ∨
         part = lines5 ∨ part = lines6 ∨ part = lines7 ∨ part = lines8) →
        ℓ ∈ part → ℓ.1 * x.1 + ℓ.2.1 * x.2 + ℓ.2.2 ≠ 0 := by
      intro part ℓ hp hℓ
      apply hx_avoid ℓ
      simp only [lines, List.mem_append]
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto
    refine ⟨q', fun a => ?_, ?_⟩
    · by_cases ha : a = k
      · subst ha; rw [hq'_k]; exact ⟨hx1, hx2⟩
      · dsimp [q']; rw [Function.update_of_ne ha]; exact hbox a
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
        · rw [hq'_lt a ha_lt]; exact hpre.1 a ha_lt
        · have hak : a = k := Fin.ext ha_eq
          subst hak; rw [hq'_k]
          have h1 := hmem_lines lines1 (1, 0, 0) (Or.inl rfl) (by simp [lines1])
          have h2 := hmem_lines lines1 (0, 1, 0) (Or.inl rfl) (by simp [lines1])
          exact ⟨fun h => h1 (by linear_combination h), fun h => h2 (by linear_combination h)⟩
      · intro a b ha hb hab
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb_lt | hb_eq
        · rw [hq'_lt a ha_lt, hq'_lt b hb_lt]; exact hpre.2.1 a b ha_lt hb_lt hab
        · have hbk : b = k := Fin.ext hb_eq
          subst hbk; rw [hq'_lt a ha_lt, hq'_k]
          have h1 := hmem_lines lines2 (1, 0, -(q a).1) (Or.inr (Or.inl rfl))
            (List.mem_map.mpr ⟨a, (hprev_iff a).mpr ha_lt, rfl⟩)
          have h2 := hmem_lines lines3 (0, 1, -(q a).2) (Or.inr (Or.inr (Or.inl rfl)))
            (List.mem_map.mpr ⟨a, (hprev_iff a).mpr ha_lt, rfl⟩)
          exact ⟨fun heq => h1 (by linear_combination -heq),
                 fun heq => h2 (by linear_combination -heq)⟩
        · have hak : a = k := Fin.ext ha_eq
          subst hak; rw [hq'_k, hq'_lt b hb_lt]
          have h1 := hmem_lines lines2 (1, 0, -(q b).1) (Or.inr (Or.inl rfl))
            (List.mem_map.mpr ⟨b, (hprev_iff b).mpr hb_lt, rfl⟩)
          have h2 := hmem_lines lines3 (0, 1, -(q b).2) (Or.inr (Or.inr (Or.inl rfl)))
            (List.mem_map.mpr ⟨b, (hprev_iff b).mpr hb_lt, rfl⟩)
          exact ⟨fun heq => h1 (by linear_combination heq),
                 fun heq => h2 (by linear_combination heq)⟩
        · exfalso; exact hab (Fin.ext (by omega))
      · intro a b ha hb hab
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb_lt | hb_eq
        · rw [hq'_lt a ha_lt, hq'_lt b hb_lt]; exact hpre.2.2.1 a b ha_lt hb_lt hab
        · have hbk : b = k := Fin.ext hb_eq
          subst hbk; rw [hq'_lt a ha_lt, hq'_k]
          have h4 := hmem_lines lines4 (-(q a).2, (q a).1, 0) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (List.mem_map.mpr ⟨a, (hprev_iff a).mpr ha_lt, rfl⟩)
          dsimp [det2] at h4 ⊢; exact fun heq => h4 (by linear_combination heq)
        · have hak : a = k := Fin.ext ha_eq
          subst hak; rw [hq'_k, hq'_lt b hb_lt]
          have h4 := hmem_lines lines4 (-(q b).2, (q b).1, 0) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (List.mem_map.mpr ⟨b, (hprev_iff b).mpr hb_lt, rfl⟩)
          dsimp [det2] at h4 ⊢; exact fun heq => h4 (by linear_combination -heq)
        · exfalso; exact hab (Fin.ext (by omega))
      · intro a b c ha hb hc hab
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb_lt | hb_eq <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc_lt | hc_eq
        · rw [hq'_lt a ha_lt, hq'_lt b hb_lt, hq'_lt c hc_lt]
          exact hpre.2.2.2.1 a b c ha_lt hb_lt hc_lt hab
        · have hck : c = k := Fin.ext hc_eq
          subst hck; rw [hq'_lt a ha_lt, hq'_lt b hb_lt, hq'_k]
          have hp_mem : (a, b) ∈ pairsNe := by
            simp [pairsNe, pairsNeS, prevS, ha_lt, hb_lt, hab]
          have h5 := hmem_lines lines5 (-(q a - q b).2, (q a - q b).1, 0)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            (List.mem_map.mpr ⟨(a, b), hp_mem, rfl⟩)
          dsimp [det2] at h5 ⊢; exact fun heq => h5 (by linear_combination heq)
        · have hbk : b = k := Fin.ext hb_eq
          subst hbk; rw [hq'_lt a ha_lt, hq'_k, hq'_lt c hc_lt]
          have hp_mem : (a, c) ∈ pairsAll := by
            simp [pairsAll, prevS, ha_lt, hc_lt]
          have h6 := hmem_lines lines6
            ((q c).2, -(q c).1, (q a).2 * (q c).1 - (q a).1 * (q c).2)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
            (List.mem_map.mpr ⟨(a, c), hp_mem, rfl⟩)
          dsimp [det2] at h6 ⊢; exact fun heq => h6 (by linear_combination -heq)
        · have hbk : b = k := Fin.ext hb_eq
          have hck : c = k := Fin.ext hc_eq
          subst hbk hck; rw [hq'_lt a ha_lt, hq'_k]
          have h4 := hmem_lines lines4 (-(q a).2, (q a).1, 0)
            (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (List.mem_map.mpr ⟨a, (hprev_iff a).mpr ha_lt, rfl⟩)
          dsimp [det2] at h4 ⊢; exact fun heq => h4 (by linear_combination heq)
        · have hak : a = k := Fin.ext ha_eq
          subst hak; rw [hq'_k, hq'_lt b hb_lt, hq'_lt c hc_lt]
          have hp_mem : (b, c) ∈ pairsAll := by
            simp [pairsAll, prevS, hb_lt, hc_lt]
          have h6 := hmem_lines lines6
            ((q c).2, -(q c).1, (q b).2 * (q c).1 - (q b).1 * (q c).2)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
            (List.mem_map.mpr ⟨(b, c), hp_mem, rfl⟩)
          dsimp [det2] at h6 ⊢; exact fun heq => h6 (by linear_combination heq)
        · have hak : a = k := Fin.ext ha_eq
          have hck : c = k := Fin.ext hc_eq
          subst hak hck; rw [hq'_lt b hb_lt, hq'_k]
          have h4 := hmem_lines lines4 (-(q b).2, (q b).1, 0)
            (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (List.mem_map.mpr ⟨b, (hprev_iff b).mpr hb_lt, rfl⟩)
          dsimp [det2] at h4 ⊢; exact fun heq => h4 (by linear_combination -heq)
        · exfalso; exact hab (Fin.ext (by omega))
        · exfalso; exact hab (Fin.ext (by omega))
      · intro a b c d ha hb hc hd hab hcd hpair
        have ha_lt : a.val < n := by omega
        have hc_lt : c.val < n := by omega
        rw [hq'_lt a ha_lt, hq'_lt c hc_lt]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb_lt | hb_eq <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd_lt | hd_eq
        · rw [hq'_lt b hb_lt, hq'_lt d hd_lt]
          exact hpre.2.2.2.2 a b c d ha_lt hb_lt hc_lt hd_lt hab hcd hpair
        · have hdk : d = k := Fin.ext hd_eq
          subst hdk; rw [hq'_lt b hb_lt, hq'_k]
          have ht_mem : ((a, b), c) ∈ triplesLt := by
            simp [triplesLt, pairsLtS, prevS, ha_lt, hb_lt, hc_lt, hab]
          have h7 := hmem_lines lines7
            ((q b - q a).2, (q a - q b).1, det2 (q c) (q a - q b))
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
            (List.mem_map.mpr ⟨((a, b), c), ht_mem, rfl⟩)
          dsimp [det2] at h7 ⊢; exact fun heq => h7 (by linear_combination -heq)
        · have hbk : b = k := Fin.ext hb_eq
          subst hbk; rw [hq'_k, hq'_lt d hd_lt]
          have ht_mem : ((c, d), a) ∈ triplesLt := by
            simp [triplesLt, pairsLtS, prevS, hc_lt, hd_lt, ha_lt, hcd]
          have h7 := hmem_lines lines7
            ((q d - q c).2, (q c - q d).1, det2 (q a) (q c - q d))
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
            (List.mem_map.mpr ⟨((c, d), a), ht_mem, rfl⟩)
          dsimp [det2] at h7 ⊢; exact fun heq => h7 (by linear_combination heq)
        · have hbk : b = k := Fin.ext hb_eq
          have hdk : d = k := Fin.ext hd_eq
          subst hbk hdk; rw [hq'_k]
          have hac : a ≠ c := fun h => hpair (by subst h; rfl)
          have hp_mem : (a, c) ∈ pairsNe := by
            simp [pairsNe, pairsNeS, prevS, ha_lt, hc_lt, hac]
          have h8 := hmem_lines lines8
            (-(q c - q a).2, (q c - q a).1, det2 (q a) (q c))
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
            (List.mem_map.mpr ⟨(a, c), hp_mem, rfl⟩)
          dsimp [det2] at h8 ⊢; exact fun heq => h8 (by linear_combination heq)

/-- Sequential general-position perturbation preserving all `32` strict masks in `Ω`. -/
theorem exists_genPos_shattering (P₀ : DualConfig)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P₀ m z) :
    ∃ P : DualConfig, IsGenPos P ∧
      ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z := by
  obtain ⟨δ, hδ, hstab⟩ := open_stability_shattered P₀ h_shat
  obtain ⟨q, hbox, hgp_pre⟩ := genPos_step P₀.vec hδ 10 le_rfl
  obtain ⟨P, hvec, hshat_P⟩ := hstab q hbox
  refine ⟨P, ?_, hshat_P⟩
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b hab => ?_,
          fun a b c hab => ?_, fun a b c d hab hcd hpair => ?_⟩
  · rw [hvec a]; exact hgp_pre.1 a a.isLt
  · rw [hvec a, hvec b]; exact hgp_pre.2.1 a b a.isLt b.isLt hab
  · rw [hvec a, hvec b]; exact hgp_pre.2.2.1 a b a.isLt b.isLt hab
  · rw [hvec a, hvec b, hvec c]; exact hgp_pre.2.2.2.1 a b c a.isLt b.isLt c.isLt hab
  · rw [hvec a, hvec b, hvec c, hvec d]
    exact hgp_pre.2.2.2.2 a b c d a.isLt b.isLt c.isLt d.isLt hab hcd hpair

/-- Wedge support function `F_i(t) = max(⟨p_{i,1}, γ(t)⟩, ⟨p_{i,2}, γ(t)⟩)`. -/
def supportF (P : DualConfig) (i : Fin 5) (t : ℝ) : ℝ :=
  max (dot2 (P.p1 i) (gamma t)) (dot2 (P.p2 i) (gamma t))

/-- Top support envelope `F_{(5)}(t) = max_{i ∈ Fin 5} F_i(t)`. -/
def topEnv (P : DualConfig) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 5 => supportF P i t)

theorem le_topEnv (P : DualConfig) (i : Fin 5) (t : ℝ) :
    supportF P i t ≤ topEnv P t :=
  Finset.le_sup' (fun j : Fin 5 => supportF P j t) (Finset.mem_univ i)

theorem dot2_vec_le_topEnv (P : DualConfig) (a : Fin 10) (t : ℝ) :
    dot2 (P.vec a) (gamma t) ≤ topEnv P t := by
  let i : Fin 5 := ⟨a.val / 2, by omega⟩
  refine le_trans ?_ (le_topEnv P i t)
  unfold DualConfig.vec supportF
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Tilting lemma: if `v_* ≠ 0` has `⟨q_a, v_*⟩ ≤ 0` for all `10` vectors of a generic `DualConfig`,
tilting slightly produces `e_y ≠ 0` with `⟨q_a, e_y⟩ < 0` for all `a ∈ Fin 10`. -/
theorem tilt_strict_neg (P : DualConfig) (hgp : IsGenPos P) {v : ℝ × ℝ}
    (hv : v ≠ (0, 0)) (hle : ∀ a : Fin 10, dot2 (P.vec a) v ≤ 0) :
    ∃ e_y : ℝ × ℝ, e_y ≠ (0, 0) ∧ ∀ a : Fin 10, dot2 (P.vec a) e_y < 0 := by
  classical
  by_cases hex : ∃ a₀ : Fin 10, dot2 (P.vec a₀) v = 0
  · rcases hex with ⟨a₀, ha₀⟩
    have h_other_neg : ∀ a : Fin 10, a ≠ a₀ → dot2 (P.vec a) v < 0 := by
      intro a hne
      rcases lt_or_eq_of_le (hle a) with hlt | heq
      · exact hlt
      · exfalso
        apply hgp.2.2.1 a a₀ hne
        unfold dot2 at heq ha₀
        unfold det2
        by_cases hv1 : v.1 = 0
        · have hv2 : v.2 ≠ 0 := fun h => hv (Prod.ext hv1 h)
          rw [hv1, mul_zero, zero_add] at heq ha₀
          have hqa2 : (P.vec a).2 = 0 := (mul_eq_zero.mp heq).resolve_right hv2
          have hqa02 : (P.vec a₀).2 = 0 := (mul_eq_zero.mp ha₀).resolve_right hv2
          rw [hqa2, hqa02]; ring
        · have h1 : v.1 * ((P.vec a).1 * (P.vec a₀).2 - (P.vec a).2 * (P.vec a₀).1) =
              (P.vec a₀).2 * ((P.vec a).1 * v.1 + (P.vec a).2 * v.2) -
              (P.vec a).2 * ((P.vec a₀).1 * v.1 + (P.vec a₀).2 * v.2) := by ring
          rw [heq, ha₀] at h1
          simp at h1
          exact h1.resolve_left hv1
    have hqa0_pos : 0 < dot2 (P.vec a₀) (P.vec a₀) := by
      have hnz := (hgp.1 a₀).1
      unfold dot2
      have : 0 < (P.vec a₀).1 ^ 2 := sq_pos_of_ne_zero hnz
      nlinarith
    let S : Finset (Fin 10) := Finset.univ.erase a₀
    have hS_ne : S.Nonempty := ⟨if a₀.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
      simp only [S, Finset.mem_erase, Finset.mem_univ, and_true]
      split_ifs with h <;> intro heq <;> { have := congrArg Fin.val heq; dsimp at this; omega }⟩
    let ε : ℝ := (1 / 2) * S.inf' hS_ne
      (fun a => (-dot2 (P.vec a) v) / (1 + |dot2 (P.vec a) (P.vec a₀)|))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      refine mul_pos (by norm_num) ((Finset.lt_inf'_iff hS_ne).mpr fun a ha => ?_)
      have hne : a ≠ a₀ := (Finset.mem_erase.mp ha).1
      exact div_pos (by linarith [h_other_neg a hne]) (by positivity)
    let e_y : ℝ × ℝ := (v.1 - ε * (P.vec a₀).1, v.2 - ε * (P.vec a₀).2)
    have hey_dot : ∀ b : Fin 10, dot2 (P.vec b) e_y =
        dot2 (P.vec b) v - ε * dot2 (P.vec b) (P.vec a₀) := by
      intro b; simp only [e_y, dot2]; ring
    have ha0_neg : dot2 (P.vec a₀) e_y < 0 := by
      rw [hey_dot a₀, ha₀]; nlinarith
    have hey_nz : e_y ≠ (0, 0) := by
      intro hz; rw [hz] at ha0_neg; simp [dot2] at ha0_neg
    refine ⟨e_y, hey_nz, fun a => ?_⟩
    by_cases ha : a = a₀
    · subst ha; exact ha0_neg
    · rw [hey_dot a]
      have hmem : a ∈ S := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
      have hle_inf : ε ≤
          (1 / 2) * ((-dot2 (P.vec a) v) / (1 + |dot2 (P.vec a) (P.vec a₀)|)) := by
        dsimp [ε]
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hmem) (by norm_num)
      have hden_pos : 0 < 1 + |dot2 (P.vec a) (P.vec a₀)| := by positivity
      have hbound : ε * (1 + |dot2 (P.vec a) (P.vec a₀)|) ≤ (1 / 2) * (-dot2 (P.vec a) v) := by
        have hm := mul_le_mul_of_nonneg_right hle_inf (le_of_lt hden_pos)
        have hne_d : 1 + |dot2 (P.vec a) (P.vec a₀)| ≠ 0 := ne_of_gt hden_pos
        calc ε * (1 + |dot2 (P.vec a) (P.vec a₀)|)
            ≤ (1 / 2) * ((-dot2 (P.vec a) v) / (1 + |dot2 (P.vec a) (P.vec a₀)|)) * (1 + |dot2 (P.vec a) (P.vec a₀)|) := hm
          _ = (1 / 2) * (-dot2 (P.vec a) v) := by rw [mul_assoc, div_mul_cancel₀ _ hne_d]
      have habs : -|dot2 (P.vec a) (P.vec a₀)| ≤ dot2 (P.vec a) (P.vec a₀) := neg_abs_le _
      have hneg_a := h_other_neg a ha
      nlinarith
  · refine ⟨v, hv, fun a => lt_of_le_of_ne (hle a) (fun h => hex ⟨a, h⟩)⟩

private def mkVFuncData (α₁ β₁ α₂ β₂ : ℝ) : VFuncData :=
  if h : α₁ ≤ α₂ then ⟨α₁, β₁, α₂, β₂, h⟩
  else ⟨α₂, β₂, α₁, β₁, le_of_not_ge h⟩

private theorem mkVFuncData_eval (α₁ β₁ α₂ β₂ x : ℝ) :
    (mkVFuncData α₁ β₁ α₂ β₂).eval x = max (α₁ * x + β₁) (α₂ * x + β₂) := by
  unfold mkVFuncData VFuncData.eval
  split_ifs
  · rfl
  · exact max_comm _ _

/-- Elimination of the unbounded regime: if no `5`-tuple of V-functions shatters `ℝ²`, then every
generic `DualConfig` shattering `Ω` satisfies `topEnv P t > 0` for all `t ∈ [0, 3]`. -/
theorem topEnv_pos_of_shattering
    (h_no_vshat : ∀ f : Fin 5 → VFuncData,
      ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVDataMask f m p))
    (P : DualConfig) (hgp : IsGenPos P)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t := by
  intro t ht0 ht3
  by_contra hle0
  replace hle0 : topEnv P t ≤ 0 := not_lt.mp hle0
  have hv_nz : gamma t ≠ (0, 0) := gamma_ne_zero ht0 ht3
  have hvec_le : ∀ a : Fin 10, dot2 (P.vec a) (gamma t) ≤ 0 :=
    fun a => le_trans (dot2_vec_le_topEnv P a t) hle0
  obtain ⟨ey, hey_nz, hey_neg⟩ := tilt_strict_neg P hgp hv_nz hvec_le
  let ex : ℝ × ℝ := (ey.2, -ey.1)
  let ν : ℝ := ey.1 ^ 2 + ey.2 ^ 2
  have hν_pos : 0 < ν := by
    by_contra h0
    have h1 : ey.1 = 0 := by dsimp [ν] at h0; nlinarith
    have h2 : ey.2 = 0 := by dsimp [ν] at h0; nlinarith
    exact hey_nz (Prod.ext h1 h2)
  have hν_ne : ν ≠ 0 := ne_of_gt hν_pos
  have hp1_neg : ∀ i : Fin 5, dot2 (P.p1 i) ey < 0 := by
    intro i; rw [← P.vec_even i]; exact hey_neg _
  have hp2_neg : ∀ i : Fin 5, dot2 (P.p2 i) ey < 0 := by
    intro i; rw [← P.vec_odd i]; exact hey_neg _
  let γ₁ : Fin 5 → ℝ := fun i => -dot2 (P.p1 i) ey
  let γ₂ : Fin 5 → ℝ := fun i => -dot2 (P.p2 i) ey
  let f : Fin 5 → VFuncData := fun i =>
    mkVFuncData (dot2 (P.p1 i) ex / γ₁ i) (-1 / γ₁ i)
                (dot2 (P.p2 i) ex / γ₂ i) (-1 / γ₂ i)
  apply h_no_vshat f
  intro m
  obtain ⟨z, _, hzm⟩ := h_shat m
  let X : ℝ := dot2 z ex / ν
  let Y : ℝ := dot2 z ey / ν
  refine ⟨(X, Y), fun i => ?_⟩
  have hγ1_pos : 0 < γ₁ i := neg_pos.mpr (hp1_neg i)
  have hγ2_pos : 0 < γ₂ i := neg_pos.mpr (hp2_neg i)
  have hγ1_ne : γ₁ i ≠ 0 := ne_of_gt hγ1_pos
  have hγ2_ne : γ₂ i ≠ 0 := ne_of_gt hγ2_pos
  have hid : ∀ q : ℝ × ℝ, dot2 q z = dot2 q ex * X + dot2 q ey * Y := by
    intro q
    apply mul_right_cancel₀ hν_ne
    simp only [X, Y, ex, ν, dot2, add_mul, mul_assoc, div_mul_cancel₀ _ hν_ne]
    ring
  have hrel1 : 1 - dot2 (P.p1 i) z =
      γ₁ i * (Y - (dot2 (P.p1 i) ex / γ₁ i * X + (-1 / γ₁ i))) := by
    rw [hid (P.p1 i)]
    have h1 : γ₁ i * (dot2 (P.p1 i) ex / γ₁ i * X) = dot2 (P.p1 i) ex * X := by
      rw [← mul_assoc, mul_div_cancel₀ _ hγ1_ne]
    have h2 : γ₁ i * (-1 / γ₁ i) = -1 := mul_div_cancel₀ _ hγ1_ne
    dsimp [γ₁] at h1 h2 ⊢
    linarith
  have hrel2 : 1 - dot2 (P.p2 i) z =
      γ₂ i * (Y - (dot2 (P.p2 i) ex / γ₂ i * X + (-1 / γ₂ i))) := by
    rw [hid (P.p2 i)]
    have h1 : γ₂ i * (dot2 (P.p2 i) ex / γ₂ i * X) = dot2 (P.p2 i) ex * X := by
      rw [← mul_assoc, mul_div_cancel₀ _ hγ2_ne]
    have h2 : γ₂ i * (-1 / γ₂ i) = -1 := mul_div_cancel₀ _ hγ2_ne
    dsimp [γ₂] at h1 h2 ⊢
    linarith
  have hev : (f i).eval X = max (dot2 (P.p1 i) ex / γ₁ i * X + (-1 / γ₁ i))
                                (dot2 (P.p2 i) ex / γ₂ i * X + (-1 / γ₂ i)) :=
    mkVFuncData_eval _ _ _ _ _
  have hm_i := hzm i
  by_cases hmi : m i
  · simp only [hmi, ↓reduceIte] at hm_i ⊢
    rw [hev, max_lt_iff]
    obtain ⟨ho1, ho2⟩ := hm_i
    exact ⟨by nlinarith [hrel1], by nlinarith [hrel2]⟩
  · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm_i ⊢
    rw [hev, lt_max_iff]
    rcases hm_i with he1 | he2
    · left; nlinarith [hrel1]
    · right; nlinarith [hrel2]

end CaseA
end
