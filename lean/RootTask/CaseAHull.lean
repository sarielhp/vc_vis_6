import RootTask.CaseAPerturb

open Finset
open Classical
set_option maxRecDepth 4000

noncomputable section

namespace CaseA

/-- Explicit candidate grid on `(0, 3)` containing all piecewise-linear pairwise tie roots. -/
def candTieGrid (P : DualConfig) : Finset ℝ :=
  ({1, 2} : Finset ℝ) ∪
  (Finset.univ : Finset (Fin 10 × Fin 10)).biUnion fun p =>
    let w := P.vec p.1 - P.vec p.2
    {w.2 / (w.1 + w.2), (2 * w.1 - w.2) / (w.1 - w.2), (2 * w.1 + 3 * w.2) / (w.1 + w.2)}

/-- Finite set of top-envelope transition points `ξ ∈ (0, 3)` where two distinct vectors tie
for `topEnv P ξ`. -/
def topTiePts (P : DualConfig) : Finset ℝ :=
  (candTieGrid P).filter fun t =>
    0 < t ∧ t < 3 ∧ ∃ a b : Fin 10, a ≠ b ∧
      dot2 (P.vec a) (gamma t) = topEnv P t ∧
      dot2 (P.vec b) (gamma t) = topEnv P t

/-- Sorted seam list `0 = ξ_0 < ξ_1 < ... < ξ_{h-1} < ξ_h = 3`. -/
def hullSeamList (P : DualConfig) : List ℝ :=
  [0] ++ (topTiePts P).sort (· ≤ ·) ++ [3]

/-- Midpoint of the `r`-th exposure interval `(ξ_r, ξ_{r+1})`. -/
def hullMidpoint (P : DualConfig) (r : Fin ((topTiePts P).card + 1)) : ℝ :=
  ((hullSeamList P).getD r.val 0 + (hullSeamList P).getD (r.val + 1) 3) / 2

/-- Unique maximizing vector index `a ∈ Fin 10` on the `r`-th exposure interval. -/
def hullIdx (P : DualConfig) (r : Fin ((topTiePts P).card + 1)) : Fin 10 :=
  if h : ∃ a : Fin 10, dot2 (P.vec a) (gamma (hullMidpoint P r)) = topEnv P (hullMidpoint P r)
  then Classical.choose h
  else ⟨0, by omega⟩

/-- Ordered exposed dual hull vertices `H_Ω = (q_1, ..., q_h)`. -/
def hullVerts (P : DualConfig) (r : Fin ((topTiePts P).card + 1)) : ℝ × ℝ :=
  P.vec (hullIdx P r)

/-- Hull color word `κ = (κ_1, ..., κ_h) ∈ (Fin 5)^h`. -/
def hullColors (P : DualConfig) (r : Fin ((topTiePts P).card + 1)) : Fin 5 :=
  vecColor (hullIdx P r)

/-- Run-length compression collapsing adjacent equal colors in a color word. -/
def compressAdj : List (Fin 5) → List (Fin 5)
  | [] => []
  | [c] => [c]
  | c₁ :: c₂ :: rest =>
      if c₁ = c₂ then compressAdj (c₂ :: rest)
      else c₁ :: compressAdj (c₂ :: rest)

/-- Compressed hull block color sequence `κ̄ = (κ̄_1, ..., κ̄_{n_Ω})`. -/
def compressedColors (P : DualConfig) : List (Fin 5) :=
  compressAdj (List.ofFn (hullColors P))

/-- Number `n_Ω` of maximal monochromatic contiguous hull blocks along `H_Ω`. -/
def hullBlockCount (P : DualConfig) : ℕ :=
  (compressedColors P).length

/-- Adjacent-block pure hull `2`-subsets `𝒜_2(κ) = {{κ̄_k, κ̄_{k+1}} : 1 ≤ k ≤ n_Ω - 1}`. -/
def pureHullPairs (P : DualConfig) : Finset (Finset (Fin 5)) :=
  let cs := compressedColors P
  ((List.range (cs.length - 1)).map fun k =>
    ({cs.getD k 0, cs.getD (k + 1) 0} : Finset (Fin 5))).toFinset

private lemma det2_eq_zero_of_dot2_zero {u v : ℝ × ℝ} {t : ℝ}
    (ht0 : 0 < t) (ht3 : t < 3) (hu : dot2 u (gamma t) = 0) (hv : dot2 v (gamma t) = 0) :
    det2 u v = 0 := by
  have hg := gamma_ne_zero (le_of_lt ht0) (le_of_lt ht3)
  have h1 : det2 u v * (gamma t).1 = 0 := by
    have : det2 u v * (gamma t).1 = v.2 * dot2 u (gamma t) - u.2 * dot2 v (gamma t) := by
      simp only [det2, dot2]; ring
    rw [this, hu, hv]; ring
  have h2 : det2 u v * (gamma t).2 = 0 := by
    have : det2 u v * (gamma t).2 = u.1 * dot2 v (gamma t) - v.1 * dot2 u (gamma t) := by
      simp only [det2, dot2]; ring
    rw [this, hu, hv]; ring
  by_contra hne
  exact hg (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))

private lemma ray_tie_in_candTieGrid (P : DualConfig) (hgp : IsGenPos P)
    {t : ℝ} (_ht0 : 0 < t) (_ht3 : t < 3) {a b : Fin 10} (hab : a ≠ b)
    (heq : dot2 (P.vec a) (gamma t) = dot2 (P.vec b) (gamma t)) :
    t ∈ candTieGrid P := by
  have hdot_w : dot2 (P.vec a - P.vec b) (gamma t) = 0 := by
    simp only [dot2, Prod.fst_sub, Prod.snd_sub] at *; linarith
  have hw1 : (P.vec a - P.vec b).1 ≠ 0 := sub_ne_zero.mpr (hgp.2.1 a b hab).1
  have hw2 : (P.vec a - P.vec b).2 ≠ 0 := sub_ne_zero.mpr (hgp.2.1 a b hab).2
  set w := P.vec a - P.vec b
  have ht_eq : t = w.2 / (w.1 + w.2) ∨ t = (2 * w.1 - w.2) / (w.1 - w.2) ∨
      t = (2 * w.1 + 3 * w.2) / (w.1 + w.2) := by
    unfold gamma dot2 at hdot_w
    split_ifs at hdot_w with h1 h2
    · left
      have hne : w.1 + w.2 ≠ 0 := by
        intro hsum
        have : w.2 = 0 := by
          dsimp at hdot_w
          linear_combination t * hsum + hdot_w
        exact hw2 this
      exact eq_div_of_mul_eq hne (by dsimp at hdot_w; linear_combination -hdot_w)
    · right; left
      dsimp only at hdot_w
      have hne : w.1 - w.2 ≠ 0 := by
        intro hdiff
        have : -w.1 = 0 := by linear_combination (1 - t) * hdiff + hdot_w
        exact hw1 (by linarith)
      exact eq_div_of_mul_eq hne (by linear_combination hdot_w)
    · right; right
      dsimp only at hdot_w
      have hne : w.1 + w.2 ≠ 0 := by
        intro hsum
        have : w.1 = 0 := by linear_combination (3 - t) * hsum + hdot_w
        exact hw1 this
      exact eq_div_of_mul_eq hne (by linear_combination hdot_w)
  simp only [candTieGrid, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  right
  refine ⟨(a, b), ?_⟩
  simpa [w] using ht_eq

/-- Ray genericity on `[0, 3]`: pairwise ties and zeros are isolated and mutually disjoint,
and `topTiePts P` captures all top-envelope ties on `(0, 3)`. -/
theorem ray_ties_zeros_disjoint (P : DualConfig) (hgp : IsGenPos P) :
    (∀ t : ℝ, t ∈ topTiePts P ↔
      0 < t ∧ t < 3 ∧ ∃ a b : Fin 10, a ≠ b ∧
        dot2 (P.vec a) (gamma t) = topEnv P t ∧
        dot2 (P.vec b) (gamma t) = topEnv P t) ∧
    (∀ t ∈ ({0, 1, 2, 3} : Finset ℝ), ∀ a b : Fin 10,
      dot2 (P.vec a) (gamma t) ≠ 0 ∧
      (a ≠ b → dot2 (P.vec a) (gamma t) ≠ dot2 (P.vec b) (gamma t))) ∧
    (∀ t : ℝ, 0 < t → t < 3 → ∀ a b c : Fin 10, a ≠ b →
      ¬ (dot2 (P.vec a) (gamma t) = dot2 (P.vec b) (gamma t) ∧
         dot2 (P.vec c) (gamma t) = 0)) ∧
    (∀ t : ℝ, 0 < t → t < 3 → ∀ a b c d : Fin 10, a < b → c < d → (a, b) ≠ (c, d) →
      ¬ (dot2 (P.vec a) (gamma t) = dot2 (P.vec b) (gamma t) ∧
         dot2 (P.vec c) (gamma t) = dot2 (P.vec d) (gamma t))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    simp only [topTiePts, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro ⟨ht0, ht3, a, b, hab, ha, hb⟩
      exact ⟨ray_tie_in_candTieGrid P hgp ht0 ht3 hab (ha.trans hb.symm),
        ht0, ht3, a, b, hab, ha, hb⟩
  · intro t ht a b
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · simp only [gamma_zero, dot2, mul_zero, zero_add, mul_one]
      exact ⟨(hgp.1 a).2, fun hab => (hgp.2.1 a b hab).2⟩
    · simp only [gamma_one, dot2, mul_neg, mul_one, mul_zero, add_zero, neg_ne_zero]
      exact ⟨(hgp.1 a).1, fun hab h => (hgp.2.1 a b hab).1 (by linarith)⟩
    · simp only [gamma_two, dot2, mul_zero, zero_add, mul_neg, mul_one, neg_ne_zero]
      exact ⟨(hgp.1 a).2, fun hab h => (hgp.2.1 a b hab).2 (by linarith)⟩
    · simp only [gamma_three, dot2, mul_one, mul_zero, add_zero]
      exact ⟨(hgp.1 a).1, fun hab => (hgp.2.1 a b hab).1⟩
  · intro t ht0 ht3 a b c hab ⟨heq, hzc⟩
    have hzd : dot2 (P.vec a - P.vec b) (gamma t) = 0 := by
      simp only [dot2, Prod.fst_sub, Prod.snd_sub] at *; linarith
    exact hgp.2.2.2.1 a b c hab (det2_eq_zero_of_dot2_zero ht0 ht3 hzd hzc)
  · intro t ht0 ht3 a b c d hab hcd hpair ⟨h1, h2⟩
    have hz1 : dot2 (P.vec a - P.vec b) (gamma t) = 0 := by
      simp only [dot2, Prod.fst_sub, Prod.snd_sub] at *; linarith
    have hz2 : dot2 (P.vec c - P.vec d) (gamma t) = 0 := by
      simp only [dot2, Prod.fst_sub, Prod.snd_sub] at *; linarith
    exact hgp.2.2.2.2 a b c d hab hcd hpair (det2_eq_zero_of_dot2_zero ht0 ht3 hz1 hz2)

private lemma hullSeamList_pairwise (P : DualConfig) :
    (hullSeamList P).Pairwise (· < ·) := by
  let s : List ℝ := (topTiePts P).sort (· ≤ ·)
  have hs_sorted : s.Pairwise (· < ·) := (topTiePts P).sortedLT_sort.pairwise
  have hs_mem : ∀ x ∈ s, 0 < x ∧ x < 3 := by
    intro x hx
    have hx' : x ∈ topTiePts P := (Finset.mem_sort _).mp hx
    simp only [topTiePts, Finset.mem_filter] at hx'
    exact ⟨hx'.2.1, hx'.2.2.1⟩
  unfold hullSeamList
  change ([0] ++ s ++ [3]).Pairwise (· < ·)
  rw [List.singleton_append, List.cons_append, List.pairwise_cons]
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hs_mem x hx).1
    · norm_num
  · rw [List.pairwise_append]
    refine ⟨hs_sorted, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
    rw [List.mem_singleton] at hy; subst hy
    exact (hs_mem x hx).2

private lemma hullSeamList_length (P : DualConfig) :
    (hullSeamList P).length = (topTiePts P).card + 2 := by
  unfold hullSeamList
  simp [Finset.length_sort]

private lemma hullSeamList_zero (P : DualConfig) :
    (hullSeamList P)[0]'(by rw [hullSeamList_length]; omega) = 0 := by
  simp [hullSeamList]

private lemma hullSeamList_last (P : DualConfig) :
    (hullSeamList P)[(topTiePts P).card + 1]'(by rw [hullSeamList_length]; omega) = 3 := by
  unfold hullSeamList
  simp [List.getElem_append_right]

private lemma hullMidpoint_spec (P : DualConfig) (r : Fin ((topTiePts P).card + 1)) :
    let L := hullSeamList P
    have hr0 : r.val < L.length := by rw [hullSeamList_length]; omega
    have hr1 : r.val + 1 < L.length := by rw [hullSeamList_length]; omega
    L[r.val]'hr0 < hullMidpoint P r ∧ hullMidpoint P r < L[r.val + 1]'hr1 ∧
    0 ≤ L[r.val]'hr0 ∧ L[r.val + 1]'hr1 ≤ 3 ∧
    0 < hullMidpoint P r ∧ hullMidpoint P r < 3 ∧
    (∀ t : ℝ, L[r.val]'hr0 < t → t < L[r.val + 1]'hr1 → t ∉ topTiePts P) := by
  have hpw := hullSeamList_pairwise P
  have hlen := hullSeamList_length P
  have hr0 : r.val < (hullSeamList P).length := by rw [hlen]; omega
  have hr1 : r.val + 1 < (hullSeamList P).length := by rw [hlen]; omega
  have hget0 : (hullSeamList P).getD r.val 0 = (hullSeamList P)[r.val] := by
    simp [List.getD_eq_getElem?_getD, hr0]
  have hget1 : (hullSeamList P).getD (r.val + 1) 3 = (hullSeamList P)[r.val + 1] := by
    simp [List.getD_eq_getElem?_getD, hr1]
  have hlt_adj : (hullSeamList P)[r.val] < (hullSeamList P)[r.val + 1] :=
    List.pairwise_iff_getElem.mp hpw r.val (r.val + 1) hr0 hr1 (by omega)
  have hge0 : 0 ≤ (hullSeamList P)[r.val] := by
    rcases Nat.eq_zero_or_pos r.val with hz | hp
    · have : (hullSeamList P)[r.val] = 0 := by simp [hz, hullSeamList]
      exact le_of_eq this.symm
    · have h0lt := List.pairwise_iff_getElem.mp hpw 0 r.val (by omega) hr0 hp
      rw [hullSeamList_zero] at h0lt
      exact le_of_lt h0lt
  have hle3 : (hullSeamList P)[r.val + 1] ≤ 3 := by
    by_cases hlast : r.val + 1 = (topTiePts P).card + 1
    · have hlast' : (hullSeamList P)[r.val + 1] = 3 := by
        have := hullSeamList_last P
        simpa [hlast] using this
      exact le_of_eq hlast'
    · have hlt_last := List.pairwise_iff_getElem.mp hpw (r.val + 1) ((topTiePts P).card + 1)
        hr1 (by rw [hlen]; omega) (by omega)
      rw [hullSeamList_last] at hlt_last
      exact le_of_lt hlt_last
  have hmid : hullMidpoint P r = ((hullSeamList P)[r.val] + (hullSeamList P)[r.val + 1]) / 2 := by
    unfold hullMidpoint; rw [hget0, hget1]
  have hmid_lo : (hullSeamList P)[r.val] < hullMidpoint P r := by
    rw [hmid]; exact left_lt_add_div_two.mpr hlt_adj
  have hmid_hi : hullMidpoint P r < (hullSeamList P)[r.val + 1] := by
    rw [hmid]; exact add_div_two_lt_right.mpr hlt_adj
  refine ⟨hmid_lo, hmid_hi, hge0, hle3, lt_of_le_of_lt hge0 hmid_lo, lt_of_lt_of_le hmid_hi hle3,
      fun t ht1 ht2 hmem => ?_⟩
  have hmem_seam : t ∈ hullSeamList P := by
    unfold hullSeamList
    simp only [List.mem_append, List.mem_singleton, Finset.mem_sort]
    exact Or.inl (Or.inr hmem)
  obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem_seam
  rcases lt_trichotomy k r.val with hkr | rfl | hkr
  · have hlt := List.pairwise_iff_getElem.mp hpw k r.val hk hr0 hkr
    rw [hkeq] at hlt
    exact (lt_asymm hlt ht1).elim
  · rw [hkeq] at ht1
    exact lt_irrefl _ ht1
  · have hge : r.val + 1 ≤ k := hkr
    rcases eq_or_lt_of_le hge with rfl | hgt
    · rw [hkeq] at ht2
      exact lt_irrefl _ ht2
    · have hlt := List.pairwise_iff_getElem.mp hpw (r.val + 1) k hr1 hk hgt
      rw [hkeq] at hlt
      exact (lt_asymm hlt ht2).elim

private lemma dot2_vec_continuous (P : DualConfig) (a : Fin 10) :
    Continuous (fun t : ℝ => dot2 (P.vec a) (gamma t)) := by
  unfold dot2
  exact (continuous_const.mul gamma_continuous.fst).add (continuous_const.mul gamma_continuous.snd)

private lemma exists_vec_eq_topEnv (P : DualConfig) (t : ℝ) :
    ∃ a : Fin 10, dot2 (P.vec a) (gamma t) = topEnv P t := by
  unfold topEnv
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : Fin 5 => supportF P i t)
  unfold supportF at hi
  rcases max_choice (dot2 (P.p1 i) (gamma t)) (dot2 (P.p2 i) (gamma t)) with hm | hm
  · exact ⟨⟨2 * i.val, by omega⟩, by rw [P.vec_even i, ← hm]; exact hi.symm⟩
  · exact ⟨⟨2 * i.val + 1, by omega⟩, by rw [P.vec_odd i, ← hm]; exact hi.symm⟩

private lemma hullIdx_dot_eq_topEnv_on_interval (P : DualConfig) (hgp : IsGenPos P)
    (r : Fin ((topTiePts P).card + 1)) :
    let L := hullSeamList P
    have hr0 : r.val < L.length := by rw [hullSeamList_length]; omega
    have hr1 : r.val + 1 < L.length := by rw [hullSeamList_length]; omega
    (∀ t : ℝ, L[r.val]'hr0 < t → t < L[r.val + 1]'hr1 →
      ∀ b : Fin 10, b ≠ hullIdx P r →
        dot2 (P.vec b) (gamma t) < dot2 (hullVerts P r) (gamma t)) ∧
    (∀ t : ℝ, L[r.val]'hr0 ≤ t → t ≤ L[r.val + 1]'hr1 →
      dot2 (hullVerts P r) (gamma t) = topEnv P t) := by
  have hm := hullMidpoint_spec P r
  set L := hullSeamList P
  have hr0 : r.val < L.length := by rw [hullSeamList_length]; omega
  have hr1 : r.val + 1 < L.length := by rw [hullSeamList_length]; omega
  have hex := exists_vec_eq_topEnv P (hullMidpoint P r)
  have hmid_eq : dot2 (hullVerts P r) (gamma (hullMidpoint P r)) = topEnv P (hullMidpoint P r) := by
    unfold hullVerts hullIdx
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hm_not : hullMidpoint P r ∉ topTiePts P := hm.2.2.2.2.2.2 _ hm.1 hm.2.1
  have hstrict : ∀ t : ℝ, L[r.val] < t → t < L[r.val + 1] →
      ∀ b : Fin 10, b ≠ hullIdx P r →
        dot2 (P.vec b) (gamma t) < dot2 (hullVerts P r) (gamma t) := by
    intro t ht_lo ht_hi b hne
    by_contra hge
    replace hge : dot2 (hullVerts P r) (gamma t) ≤ dot2 (P.vec b) (gamma t) := not_lt.mp hge
    let g : ℝ → ℝ := fun u =>
      (Finset.univ.erase (hullIdx P r)).sup'
        ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
        (fun c : Fin 10 => dot2 (P.vec c) (gamma u)) -
      dot2 (hullVerts P r) (gamma u)
    have hg_cont : Continuous g := by
      refine Continuous.sub ?_ (dot2_vec_continuous P (hullIdx P r))
      exact Continuous.finset_sup'_apply _ fun c _ => dot2_vec_continuous P c
    have hg_mid : g (hullMidpoint P r) < 0 := by
      dsimp [g]
      rw [sub_neg, Finset.sup'_lt_iff]
      intro c hc
      have hc_ne : c ≠ hullIdx P r := (Finset.mem_erase.mp hc).1
      have hle := le_trans (dot2_vec_le_topEnv P c (hullMidpoint P r)) hmid_eq.symm.le
      refine lt_of_le_of_ne hle fun heq => hm_not ?_
      exact (ray_ties_zeros_disjoint P hgp).1 (hullMidpoint P r) |>.mpr
        ⟨hm.2.2.2.2.1, hm.2.2.2.2.2.1, c, hullIdx P r, hc_ne, heq.trans hmid_eq, hmid_eq⟩
    have hg_t : 0 ≤ g t := by
      dsimp [g]
      have hle_sup : dot2 (P.vec b) (gamma t) ≤
          (Finset.univ.erase (hullIdx P r)).sup'
            ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
            (fun c : Fin 10 => dot2 (P.vec c) (gamma t)) :=
        Finset.le_sup' (fun c : Fin 10 => dot2 (P.vec c) (gamma t))
          (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩)
      linarith
    rcases le_or_gt t (hullMidpoint P r) with htm | hmt
    · obtain ⟨s, hs_mem, hs0⟩ :=
        intermediate_value_Icc' htm hg_cont.continuousOn ⟨le_of_lt hg_mid, hg_t⟩
      have hs_not := hm.2.2.2.2.2.2 s (lt_of_lt_of_le ht_lo hs_mem.1) (lt_of_le_of_lt hs_mem.2 hm.2.1)
      have hs0' : (Finset.univ.erase (hullIdx P r)).sup' _
          (fun c : Fin 10 => dot2 (P.vec c) (gamma s)) =
          dot2 (hullVerts P r) (gamma s) := sub_eq_zero.mp hs0
      obtain ⟨c, hc_mem, hc_eq⟩ := Finset.exists_mem_eq_sup'
        ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
        (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
      have hc_ne : c ≠ hullIdx P r := (Finset.mem_erase.mp hc_mem).1
      have htop_s : dot2 (hullVerts P r) (gamma s) = topEnv P s := by
        refine le_antisymm (dot2_vec_le_topEnv P (hullIdx P r) s) ?_
        obtain ⟨d, hd⟩ := exists_vec_eq_topEnv P s
        rw [← hd]
        by_cases hdc : d = hullIdx P r
        · rw [hdc]; rfl
        · rw [← hs0']
          exact Finset.le_sup' (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
            (Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩)
      exact hs_not ((ray_ties_zeros_disjoint P hgp).1 s |>.mpr
        ⟨lt_of_le_of_lt hm.2.2.1 (lt_of_lt_of_le ht_lo hs_mem.1),
         lt_of_lt_of_le (lt_of_le_of_lt hs_mem.2 hm.2.1) hm.2.2.2.1,
         c, hullIdx P r, hc_ne, hc_eq.symm.trans (hs0'.trans htop_s), htop_s⟩)
    · obtain ⟨s, hs_mem, hs0⟩ :=
        intermediate_value_Icc (le_of_lt hmt) hg_cont.continuousOn ⟨le_of_lt hg_mid, hg_t⟩
      have hs_not := hm.2.2.2.2.2.2 s (lt_of_lt_of_le hm.1 hs_mem.1) (lt_of_le_of_lt hs_mem.2 ht_hi)
      have hs0' : (Finset.univ.erase (hullIdx P r)).sup' _
          (fun c : Fin 10 => dot2 (P.vec c) (gamma s)) =
          dot2 (hullVerts P r) (gamma s) := sub_eq_zero.mp hs0
      obtain ⟨c, hc_mem, hc_eq⟩ := Finset.exists_mem_eq_sup'
        ⟨b, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ b⟩⟩
        (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
      have hc_ne : c ≠ hullIdx P r := (Finset.mem_erase.mp hc_mem).1
      have htop_s : dot2 (hullVerts P r) (gamma s) = topEnv P s := by
        refine le_antisymm (dot2_vec_le_topEnv P (hullIdx P r) s) ?_
        obtain ⟨d, hd⟩ := exists_vec_eq_topEnv P s
        rw [← hd]
        by_cases hdc : d = hullIdx P r
        · rw [hdc]; rfl
        · rw [← hs0']
          exact Finset.le_sup' (fun c : Fin 10 => dot2 (P.vec c) (gamma s))
            (Finset.mem_erase.mpr ⟨hdc, Finset.mem_univ d⟩)
      exact hs_not ((ray_ties_zeros_disjoint P hgp).1 s |>.mpr
        ⟨lt_of_le_of_lt hm.2.2.1 (lt_of_lt_of_le hm.1 hs_mem.1),
         lt_of_lt_of_le (lt_of_le_of_lt hs_mem.2 ht_hi) hm.2.2.2.1,
         c, hullIdx P r, hc_ne, hc_eq.symm.trans (hs0'.trans htop_s), htop_s⟩)
  refine ⟨hstrict, fun t ht_lo ht_hi => ?_⟩
  refine le_antisymm (dot2_vec_le_topEnv P (hullIdx P r) t) ?_
  obtain ⟨b, hb⟩ := exists_vec_eq_topEnv P t
  rw [← hb]
  by_cases hbr : b = hullIdx P r
  · rw [hbr]; rfl
  · by_contra hlt
    replace hlt : dot2 (hullVerts P r) (gamma t) < dot2 (P.vec b) (gamma t) := not_le.mp hlt
    have hopen : IsOpen {u : ℝ | dot2 (hullVerts P r) (gamma u) < dot2 (P.vec b) (gamma u)} :=
      isOpen_lt (dot2_vec_continuous P (hullIdx P r)) (dot2_vec_continuous P b)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen t hlt
    rcases eq_or_lt_of_le ht_lo with rfl | ht_lo'
    · let u := min (hullMidpoint P r) (L[r.val] + δ / 2)
      have hu_lo : L[r.val] < u := lt_min hm.1 (by linarith)
      have hu_hi : u < L[r.val + 1] := lt_of_le_of_lt (min_le_left _ _) hm.2.1
      have hu_ball : u ∈ Metric.ball L[r.val] δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        have : u ≤ L[r.val] + δ / 2 := min_le_right _ _
        linarith
      have hu_lt := Set.mem_setOf.mp (hball hu_ball)
      linarith [hstrict u hu_lo hu_hi b hbr]
    · rcases eq_or_lt_of_le ht_hi with rfl | ht_hi'
      · let u := max (hullMidpoint P r) (L[r.val + 1] - δ / 2)
        have hu_lo : L[r.val] < u := lt_of_lt_of_le hm.1 (le_max_left _ _)
        have hu_hi : u < L[r.val + 1] := max_lt hm.2.1 (by linarith)
        have hu_ball : u ∈ Metric.ball L[r.val + 1] δ := by
          rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
          have : L[r.val + 1] - δ / 2 ≤ u := le_max_right _ _
          linarith
        have hu_lt := Set.mem_setOf.mp (hball hu_ball)
        linarith [hstrict u hu_lo hu_hi b hbr]
      · linarith [hstrict t ht_lo' ht_hi' b hbr]

private lemma span_lt_two_of_inOmega
    {q : ℝ × ℝ} (hq : InOmega q) {a b : ℝ}
    (ha0 : 0 < a) (hab : a < b) (hb3 : b < 3)
    (hpa : 0 < dot2 q (gamma a)) (hpb : 0 < dot2 q (gamma b)) :
    b - a < 2 :=
  (omega_pos_span (le_of_lt ha0) hab (le_of_lt hb3) hpa hpb (Or.inl hq)).1

private lemma caseA_hull_approval_contiguity_le
    (w1 wj w2 : ℝ × ℝ) (t1 tj t2 t ρ : ℝ)
    (hw1 : InOmega w1) (hw2 : InOmega w2)
    (h01 : 0 < t1) (h1j : t1 < tj) (hj2 : tj < t2) (h23 : t2 < 3)
    (ht0 : 0 < t) (ht3 : t < 3) (hρ : 0 < ρ)
    (h1_pos : 0 < dot2 w1 (gamma t1))
    (h2_pos : 0 < dot2 w2 (gamma t2))
    (h1_dom : dot2 wj (gamma t1) < dot2 w1 (gamma t1))
    (hj_dom1 : dot2 w1 (gamma tj) < dot2 wj (gamma tj))
    (hj_dom2 : dot2 w2 (gamma tj) < dot2 wj (gamma tj))
    (h2_dom : dot2 wj (gamma t2) < dot2 w2 (gamma t2))
    (ht_w1 : ρ ≤ dot2 w1 (gamma t))
    (ht_w2 : ρ ≤ dot2 w2 (gamma t)) :
    ρ < dot2 wj (gamma t) := by
  by_cases hteq : t = tj
  · subst hteq; linarith
  · rcases lt_or_gt_of_ne hteq with hlt | hgt
    · have hspan : t2 - t < 2 :=
        span_lt_two_of_inOmega hw2 ht0 (lt_trans hlt hj2) h23 (lt_of_lt_of_le hρ ht_w2) h2_pos
      have hd_outer : 0 < det2 (gamma t) (gamma t2) :=
        (gamma_det2_sign (le_of_lt ht0) (lt_trans hlt hj2) (le_of_lt h23)).1.mpr hspan
      have hd_right : 0 < det2 (gamma tj) (gamma t2) :=
        (gamma_det2_sign (le_of_lt (lt_trans h01 h1j)) hj2 (le_of_lt h23)).1.mpr (by linarith)
      have hd_left : 0 < det2 (gamma t) (gamma tj) :=
        (gamma_det2_sign (le_of_lt ht0) hlt (le_of_lt (lt_trans hj2 h23))).1.mpr (by linarith)
      have hcramer :
          det2 (gamma t) (gamma t2) * (dot2 wj (gamma tj) - dot2 w2 (gamma tj)) =
          det2 (gamma tj) (gamma t2) * (dot2 wj (gamma t) - dot2 w2 (gamma t)) +
          det2 (gamma t) (gamma tj) * (dot2 wj (gamma t2) - dot2 w2 (gamma t2)) := by
        unfold det2 dot2; ring
      have hpos_lhs : 0 < det2 (gamma t) (gamma t2) * (dot2 wj (gamma tj) - dot2 w2 (gamma tj)) :=
        mul_pos hd_outer (by linarith)
      have hneg_rhs : det2 (gamma t) (gamma tj) * (dot2 wj (gamma t2) - dot2 w2 (gamma t2)) < 0 :=
        mul_neg_of_pos_of_neg hd_left (by linarith)
      have hpos_mid : 0 < det2 (gamma tj) (gamma t2) * (dot2 wj (gamma t) - dot2 w2 (gamma t)) := by
        linarith
      have hdiff_pos : 0 < dot2 wj (gamma t) - dot2 w2 (gamma t) := by
        by_contra hle
        have : det2 (gamma tj) (gamma t2) * (dot2 wj (gamma t) - dot2 w2 (gamma t)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd_right) (not_lt.mp hle)
        linarith
      linarith
    · have hspan : t - t1 < 2 :=
        span_lt_two_of_inOmega hw1 h01 (lt_trans h1j hgt) ht3 h1_pos (lt_of_lt_of_le hρ ht_w1)
      have hd_outer : 0 < det2 (gamma t1) (gamma t) :=
        (gamma_det2_sign (le_of_lt h01) (lt_trans h1j hgt) (le_of_lt ht3)).1.mpr hspan
      have hd_left : 0 < det2 (gamma t1) (gamma tj) :=
        (gamma_det2_sign (le_of_lt h01) h1j (le_of_lt (lt_trans hj2 h23))).1.mpr (by linarith)
      have hd_right : 0 < det2 (gamma tj) (gamma t) :=
        (gamma_det2_sign (le_of_lt (lt_trans h01 h1j)) hgt (le_of_lt ht3)).1.mpr (by linarith)
      have hcramer :
          det2 (gamma t1) (gamma t) * (dot2 wj (gamma tj) - dot2 w1 (gamma tj)) =
          det2 (gamma tj) (gamma t) * (dot2 wj (gamma t1) - dot2 w1 (gamma t1)) +
          det2 (gamma t1) (gamma tj) * (dot2 wj (gamma t) - dot2 w1 (gamma t)) := by
        unfold det2 dot2; ring
      have hpos_lhs : 0 < det2 (gamma t1) (gamma t) * (dot2 wj (gamma tj) - dot2 w1 (gamma tj)) :=
        mul_pos hd_outer (by linarith)
      have hneg_rhs : det2 (gamma tj) (gamma t) * (dot2 wj (gamma t1) - dot2 w1 (gamma t1)) < 0 :=
        mul_neg_of_pos_of_neg hd_right (by linarith)
      have hpos_mid : 0 < det2 (gamma t1) (gamma tj) * (dot2 wj (gamma t) - dot2 w1 (gamma t)) := by
        linarith
      have hdiff_pos : 0 < dot2 wj (gamma t) - dot2 w1 (gamma t) := by
        by_contra hle
        have : det2 (gamma t1) (gamma tj) * (dot2 wj (gamma t) - dot2 w1 (gamma t)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd_left) (not_lt.mp hle)
        linarith
      linarith

private lemma hullIdx_adj_ne (P : DualConfig) (hgp : IsGenPos P)
    (r : Fin ((topTiePts P).card + 1)) (hr : r.val + 1 < (topTiePts P).card + 1) :
    hullIdx P r ≠ hullIdx P ⟨r.val + 1, hr⟩ := by
  intro heq
  let r' : Fin ((topTiePts P).card + 1) := ⟨r.val + 1, hr⟩
  have hlen := hullSeamList_length P
  have hr1_lt : r.val + 1 < (hullSeamList P).length := by rw [hlen]; omega
  set ξ : ℝ := (hullSeamList P)[r.val + 1]'hr1_lt
  have hξ_mem : ξ ∈ topTiePts P := by
    have hs_mem : ξ ∈ (hullSeamList P) := List.getElem_mem hr1_lt
    unfold hullSeamList at hs_mem
    simp only [List.mem_append, List.mem_singleton, Finset.mem_sort] at hs_mem
    rcases hs_mem with h | h
    · rcases h with h0 | h
      · exfalso
        have hlt0 := List.pairwise_iff_getElem.mp (hullSeamList_pairwise P) 0 (r.val + 1)
          (by rw [hlen]; omega) hr1_lt (by omega)
        rw [hullSeamList_zero] at hlt0
        change 0 < ξ at hlt0
        linarith
      · exact h
    · exfalso
      have hlt3 := List.pairwise_iff_getElem.mp (hullSeamList_pairwise P) (r.val + 1)
        ((topTiePts P).card + 1) hr1_lt (by rw [hlen]; omega) (by omega)
      rw [hullSeamList_last] at hlt3
      change ξ < 3 at hlt3
      linarith
  obtain ⟨hξ0, hξ3, a, b, hab, ha, hb⟩ := (ray_ties_zeros_disjoint P hgp).1 ξ |>.mp hξ_mem
  have hne12 : ξ ≠ 1 ∧ ξ ≠ 2 := by
    have hrd := (ray_ties_zeros_disjoint P hgp).2.1
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · exact (hrd 1 (by simp) a b).2 hab (by rw [← h1, ha, hb])
    · exact (hrd 2 (by simp) a b).2 hab (by rw [← h2, ha, hb])
  obtain ⟨d, hd_ne, hd_eq⟩ : ∃ d : Fin 10, d ≠ hullIdx P r ∧ dot2 (P.vec d) (gamma ξ) = topEnv P ξ := by
    by_cases had : a = hullIdx P r
    · exact ⟨b, fun h => hab (had.trans h.symm), hb⟩
    · exact ⟨a, had, ha⟩
  have hr_spec := hullIdx_dot_eq_topEnv_on_interval P hgp r
  have hr'_spec := hullIdx_dot_eq_topEnv_on_interval P hgp r'
  have hm_r := hullMidpoint_spec P r
  have hm_r' := hullMidpoint_spec P r'
  have hdot_c : dot2 (hullVerts P r) (gamma ξ) = topEnv P ξ :=
    hr_spec.2 ξ (le_of_lt (List.pairwise_iff_getElem.mp (hullSeamList_pairwise P) r.val (r.val + 1)
      (by rw [hlen]; omega) hr1_lt (by omega))) le_rfl
  have hleft_lt : dot2 (P.vec d) (gamma (hullMidpoint P r)) <
      dot2 (hullVerts P r) (gamma (hullMidpoint P r)) :=
    hr_spec.1 (hullMidpoint P r) hm_r.1 hm_r.2.1 d hd_ne
  have hright_lt : dot2 (P.vec d) (gamma (hullMidpoint P r')) <
      dot2 (hullVerts P r) (gamma (hullMidpoint P r')) := by
    have := hr'_spec.1 (hullMidpoint P r') hm_r'.1 hm_r'.2.1 d (by rw [← heq]; exact hd_ne)
    simpa [hullVerts, heq] using this
  let w := P.vec d - hullVerts P r
  have hwc : dot2 w (gamma ξ) = 0 := by
    unfold hullVerts at hdot_c
    unfold dot2 at hdot_c hd_eq
    dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
    linarith [hdot_c, hd_eq]
  have hwl : dot2 w (gamma (hullMidpoint P r)) < 0 := by
    unfold hullVerts dot2 at hleft_lt
    dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
    linarith
  have hwr : dot2 w (gamma (hullMidpoint P r')) < 0 := by
    unfold hullVerts dot2 at hright_lt
    dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
    linarith
  have h_lin : ∀ t₁ t₂ : ℝ,
      ((t₁ ≤ 1 ∧ ξ ≤ 1 ∧ t₂ ≤ 1) ∨
       (1 < t₁ ∧ t₁ ≤ 2 ∧ 1 < ξ ∧ ξ ≤ 2 ∧ 1 < t₂ ∧ t₂ ≤ 2) ∨
       (2 < t₁ ∧ 2 < ξ ∧ 2 < t₂)) →
      t₁ < ξ → ξ < t₂ → dot2 w (gamma t₁) < 0 → dot2 w (gamma t₂) < 0 → False := by
    intro t₁ t₂ hseg ht1 hξt2 hlt1 hlt2
    rcases hseg with ⟨h1a, h1b, h1c⟩ | ⟨h2a1, h2a2, h2b1, h2b2, h2c1, h2c2⟩ | ⟨h3a, h3b, h3c⟩
    · unfold gamma dot2 at hwc hlt1 hlt2
      rw [if_pos h1b] at hwc
      rw [if_pos h1a] at hlt1
      rw [if_pos h1c] at hlt2
      dsimp at hwc hlt1 hlt2
      nlinarith
    · unfold gamma dot2 at hwc hlt1 hlt2
      rw [if_neg (by linarith), if_pos h2b2] at hwc
      rw [if_neg (by linarith), if_pos h2a2] at hlt1
      rw [if_neg (by linarith), if_pos h2c2] at hlt2
      dsimp at hwc hlt1 hlt2
      nlinarith
    · unfold gamma dot2 at hwc hlt1 hlt2
      rw [if_neg (by linarith), if_neg (by linarith)] at hwc
      rw [if_neg (by linarith), if_neg (by linarith)] at hlt1
      rw [if_neg (by linarith), if_neg (by linarith)] at hlt2
      dsimp at hwc hlt1 hlt2
      nlinarith
  rcases lt_or_gt_of_ne hne12.1 with hξ1 | h1ξ
  · let t₁ := max (hullMidpoint P r) 0
    let t₂ := min (hullMidpoint P r') 1
    have ht1_lt : t₁ < ξ := max_lt hm_r.2.1 hξ0
    have ht2_gt : ξ < t₂ := lt_min hm_r'.1 hξ1
    have hdot1 : dot2 w (gamma t₁) < 0 := by
      dsimp only [t₁]
      rw [max_eq_left (le_of_lt hm_r.2.2.2.2.1)]
      exact hwl
    have hdot2 : dot2 w (gamma t₂) < 0 := by
      dsimp only [t₂]
      by_cases hle : hullMidpoint P r' ≤ 1
      · rw [min_eq_left hle]; exact hwr
      · rw [min_eq_right (le_of_lt (not_le.mp hle))]
        have h1_lt_r' : 1 < hullMidpoint P r' := not_le.mp hle
        have hξ_eq_r' : (hullSeamList P)[r'.val]'(by rw [hullSeamList_length]; omega) = ξ := rfl
        have := hr'_spec.1 1 (hξ_eq_r' ▸ hξ1) (lt_trans h1_lt_r' hm_r'.2.1) d (by rw [← heq]; exact hd_ne)
        unfold hullVerts at this
        rw [← heq] at this
        unfold dot2 at this
        dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
        linarith
    exact h_lin t₁ t₂ (Or.inl ⟨by linarith, le_of_lt hξ1, min_le_right _ _⟩) ht1_lt ht2_gt hdot1 hdot2
  · rcases lt_or_gt_of_ne hne12.2 with hξ2 | h2ξ
    · let t₁ := max (hullMidpoint P r) ((1 + ξ) / 2)
      let t₂ := min (hullMidpoint P r') 2
      have ht1_gt1 : 1 < t₁ := lt_max_of_lt_right (by linarith)
      have ht1_lt : t₁ < ξ := max_lt hm_r.2.1 (by linarith)
      have ht2_gt : ξ < t₂ := lt_min hm_r'.1 hξ2
      have hdot1 : dot2 w (gamma t₁) < 0 := by
        dsimp only [t₁]
        by_cases hle : hullMidpoint P r ≤ (1 + ξ) / 2
        · rw [max_eq_right hle]
          have := hr_spec.1 ((1 + ξ) / 2) (lt_of_lt_of_le hm_r.1 hle) (by linarith) d hd_ne
          unfold hullVerts dot2 at this
          dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
          linarith
        · rw [max_eq_left (le_of_lt (not_le.mp hle))]
          exact hwl
      have hdot2 : dot2 w (gamma t₂) < 0 := by
        dsimp only [t₂]
        by_cases hle : hullMidpoint P r' ≤ 2
        · rw [min_eq_left hle]; exact hwr
        · rw [min_eq_right (le_of_lt (not_le.mp hle))]
          have hlt_2 : 2 < hullMidpoint P r' := not_le.mp hle
          have hξ_eq_r' : (hullSeamList P)[r'.val]'(by rw [hullSeamList_length]; omega) = ξ := rfl
          have := hr'_spec.1 2 (hξ_eq_r' ▸ hξ2) (lt_trans hlt_2 hm_r'.2.1) d (by rw [← heq]; exact hd_ne)
          unfold hullVerts at this
          rw [← heq] at this
          unfold dot2 at this
          dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
          linarith
      exact h_lin t₁ t₂ (Or.inr (Or.inl ⟨ht1_gt1, by linarith, h1ξ, le_of_lt hξ2, by linarith, min_le_right _ _⟩))
        ht1_lt ht2_gt hdot1 hdot2
    · let t₁ := max (hullMidpoint P r) ((2 + ξ) / 2)
      let t₂ := hullMidpoint P r'
      have ht1_gt2 : 2 < t₁ := lt_max_of_lt_right (by linarith)
      have ht1_lt : t₁ < ξ := max_lt hm_r.2.1 (by linarith)
      have hdot1 : dot2 w (gamma t₁) < 0 := by
        dsimp only [t₁]
        by_cases hle : hullMidpoint P r ≤ (2 + ξ) / 2
        · rw [max_eq_right hle]
          have := hr_spec.1 ((2 + ξ) / 2) (lt_of_lt_of_le hm_r.1 hle) (by linarith) d hd_ne
          unfold hullVerts dot2 at this
          dsimp only [w, hullVerts, dot2, Prod.fst_sub, Prod.snd_sub]
          linarith
        · rw [max_eq_left (le_of_lt (not_le.mp hle))]
          exact hwl
      have hξ_r'_lt : ξ < hullMidpoint P r' := hm_r'.1
      exact h_lin t₁ t₂ (Or.inr (Or.inr ⟨ht1_gt2, h2ξ, by linarith⟩)) ht1_lt hξ_r'_lt hdot1 hwr

private lemma hullVerts_strictMono (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t) :
    StrictMono (fun r : Fin ((topTiePts P).card + 1) => rayParam (hullVerts P r)) := by
  refine Fin.strictMono_iff_lt_succ.mpr fun r => ?_
  let r0 : Fin ((topTiePts P).card + 1) := r.castSucc
  let r' : Fin ((topTiePts P).card + 1) := r.succ
  have hne := hullIdx_adj_ne P hgp r0 (by dsimp [r0]; omega)
  have hlen := hullSeamList_length P
  have hr1_lt : r0.val + 1 < (hullSeamList P).length := by rw [hlen]; dsimp [r0]; omega
  set ξ : ℝ := (hullSeamList P)[r0.val + 1]'hr1_lt
  have hm_r := hullMidpoint_spec P r0
  have hm_r' := hullMidpoint_spec P r'
  have hξ0 : 0 ≤ ξ := le_trans hm_r.2.2.1 (le_of_lt (lt_trans hm_r.1 hm_r.2.1))
  have hξ3 : ξ ≤ 3 := le_trans (le_of_lt (lt_trans hm_r'.1 hm_r'.2.1)) hm_r'.2.2.2.1
  have hr_spec := hullIdx_dot_eq_topEnv_on_interval P hgp r0
  have hr'_spec := hullIdx_dot_eq_topEnv_on_interval P hgp r'
  have hξ_r : dot2 (hullVerts P r0) (gamma ξ) = topEnv P ξ :=
    hr_spec.2 ξ (le_of_lt (lt_trans hm_r.1 hm_r.2.1)) le_rfl
  have hξ_r' : dot2 (hullVerts P r') (gamma ξ) = topEnv P ξ :=
    hr'_spec.2 ξ le_rfl (le_of_lt (lt_trans hm_r'.1 hm_r'.2.1))
  have hpos_ξ : 0 < dot2 (hullVerts P r0) (gamma ξ) := by rw [hξ_r]; exact htop hξ0 hξ3
  have hbeat : dot2 (hullVerts P r0) (gamma (hullMidpoint P r')) <
      dot2 (hullVerts P r') (gamma (hullMidpoint P r')) :=
    hr'_spec.1 (hullMidpoint P r') hm_r'.1 hm_r'.2.1 (hullIdx P r0) hne
  have hpos_r' : 0 < dot2 (hullVerts P r') (gamma (hullMidpoint P r')) := by
    rw [hr'_spec.2 _ (le_of_lt hm_r'.1) (le_of_lt hm_r'.2.1)]
    exact htop (le_of_lt hm_r'.2.2.2.2.1) (le_of_lt hm_r'.2.2.2.2.2.1)
  exact (rayParam_lt_of_pos_tie (P.vec_inOmega _) (P.vec_inOmega _)
    hξ0 hξ3 (le_of_lt hm_r'.2.2.2.2.1) (le_of_lt hm_r'.2.2.2.2.2.1)
    (hξ_r.trans hξ_r'.symm) hpos_ξ (Or.inl ⟨hm_r'.1, hbeat, hpos_r'⟩)).2

private lemma hullVerts_contig_le (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (z : ℝ × ℝ) (hz : InOmega z)
    (r₁ r₂ r₃ : Fin ((topTiePts P).card + 1))
    (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (hd1 : 1 ≤ dot2 (hullVerts P r₁) z) (hd3 : 1 ≤ dot2 (hullVerts P r₃) z) :
    1 < dot2 (hullVerts P r₂) z := by
  have hm1 := hullMidpoint_spec P r₁
  have hm2 := hullMidpoint_spec P r₂
  have hm3 := hullMidpoint_spec P r₃
  have hs1 := hullIdx_dot_eq_topEnv_on_interval P hgp r₁
  have hs2 := hullIdx_dot_eq_topEnv_on_interval P hgp r₂
  have hs3 := hullIdx_dot_eq_topEnv_on_interval P hgp r₃
  have hlen := hullSeamList_length P
  have h1j : hullMidpoint P r₁ < hullMidpoint P r₂ := by
    have hle : r₁.val + 1 ≤ r₂.val := h12
    have h_le_seam : (hullSeamList P)[r₁.val + 1]'(by rw [hlen]; omega) ≤
        (hullSeamList P)[r₂.val]'(by rw [hlen]; omega) := by
      rcases eq_or_lt_of_le hle with heq | hlt
      · simp [heq]
      · exact le_of_lt (List.pairwise_iff_getElem.mp (hullSeamList_pairwise P) _ _
          (by rw [hlen]; omega) (by rw [hlen]; omega) hlt)
    linarith [hm1.2.1, hm2.1]
  have hj2 : hullMidpoint P r₂ < hullMidpoint P r₃ := by
    have hle : r₂.val + 1 ≤ r₃.val := h23
    have h_le_seam : (hullSeamList P)[r₂.val + 1]'(by rw [hlen]; omega) ≤
        (hullSeamList P)[r₃.val]'(by rw [hlen]; omega) := by
      rcases eq_or_lt_of_le hle with heq | hlt
      · simp [heq]
      · exact le_of_lt (List.pairwise_iff_getElem.mp (hullSeamList_pairwise P) _ _
          (by rw [hlen]; omega) (by rw [hlen]; omega) hlt)
    linarith [hm2.2.1, hm3.1]
  have hnorm_z := inOmega_norm_pos hz
  have hrec_z := gamma_rayParam_smul hz
  have htz := rayParam_mem_Ioo hz
  let ρ := 1 / (|z.1| + |z.2|)
  have hρ_pos : 0 < ρ := div_pos one_pos hnorm_z
  have h_le_scale : ∀ w : ℝ × ℝ, 1 ≤ dot2 w z → ρ ≤ dot2 w (gamma (rayParam z)) := by
    intro w hw
    rw [← hrec_z, dot2_smul_right] at hw
    dsimp [ρ]
    exact (div_le_iff₀' hnorm_z).mpr hw
  have h_lt_scale : ∀ w : ℝ × ℝ, ρ < dot2 w (gamma (rayParam z)) → 1 < dot2 w z := by
    intro w hw
    rw [← hrec_z, dot2_smul_right]
    dsimp [ρ] at hw
    exact (div_lt_iff₀' hnorm_z).mp hw
  have h1_pos : 0 < dot2 (hullVerts P r₁) (gamma (hullMidpoint P r₁)) := by
    rw [hs1.2 _ (le_of_lt hm1.1) (le_of_lt hm1.2.1)]
    exact htop (le_of_lt hm1.2.2.2.2.1) (le_of_lt hm1.2.2.2.2.2.1)
  have h2_pos : 0 < dot2 (hullVerts P r₃) (gamma (hullMidpoint P r₃)) := by
    rw [hs3.2 _ (le_of_lt hm3.1) (le_of_lt hm3.2.1)]
    exact htop (le_of_lt hm3.2.2.2.2.1) (le_of_lt hm3.2.2.2.2.2.1)
  have hmono := hullVerts_strictMono P hgp htop
  have hinj : Function.Injective (hullIdx P) := by
    intro a b hab
    exact hmono.injective (by simp [hullVerts, hab])
  have hne12 : hullIdx P r₁ ≠ hullIdx P r₂ := hinj.ne h12.ne
  have hne23 : hullIdx P r₂ ≠ hullIdx P r₃ := hinj.ne h23.ne
  exact h_lt_scale _ (caseA_hull_approval_contiguity_le
    (hullVerts P r₁) (hullVerts P r₂) (hullVerts P r₃)
    (hullMidpoint P r₁) (hullMidpoint P r₂) (hullMidpoint P r₃) (rayParam z) ρ
    (P.vec_inOmega _) (P.vec_inOmega _)
    hm1.2.2.2.2.1 h1j hj2 hm3.2.2.2.2.2.1
    htz.1 htz.2 hρ_pos
    h1_pos h2_pos
    (hs1.1 _ hm1.1 hm1.2.1 _ hne12.symm)
    (hs2.1 _ hm2.1 hm2.2.1 _ hne12)
    (hs2.1 _ hm2.1 hm2.2.1 _ hne23.symm)
    (hs3.1 _ hm3.1 hm3.2.1 _ hne23)
    (h_le_scale _ hd1) (h_le_scale _ hd3))

/-- Exposed hull distinctness, ray parameter monotonicity, and approval contiguity. -/
theorem hullVerts_spec (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t) :
    let h := (topTiePts P).card + 1
    1 ≤ (topTiePts P).card ∧ h ≤ 10 ∧
    Function.Injective (hullIdx P) ∧
    StrictMono (fun r : Fin h => rayParam (hullVerts P r)) ∧
    rayParam (hullVerts P ⟨0, by omega⟩) < 1 ∧
    2 < rayParam (hullVerts P ⟨h - 1, by omega⟩) ∧
    (∀ (z : ℝ × ℝ), InOmega z →
      ∀ r₁ r₂ r₃ : Fin h, r₁ < r₂ → r₂ < r₃ →
        1 < dot2 (hullVerts P r₁) z → 1 < dot2 (hullVerts P r₃) z →
        1 < dot2 (hullVerts P r₂) z) := by
  intro h
  have hmono := hullVerts_strictMono P hgp htop
  have hinj : Function.Injective (hullIdx P) := by
    intro r₁ r₂ heq
    have hray : rayParam (hullVerts P r₁) = rayParam (hullVerts P r₂) := by
      simp [hullVerts, heq]
    exact hmono.injective hray
  have hle10 : h ≤ 10 := by
    have := Fintype.card_le_of_injective (hullIdx P) hinj
    simpa only [Fintype.card_fin] using this
  have h0_lt1 : rayParam (hullVerts P ⟨0, by omega⟩) < 1 := by
    let r0 : Fin h := ⟨0, by omega⟩
    have h0_spec := hullIdx_dot_eq_topEnv_on_interval P hgp r0
    have h0_le : (hullSeamList P)[0]'(by rw [hullSeamList_length]; omega) ≤ 0 := by
      rw [hullSeamList_zero]
    have h0_pos : 0 < (hullVerts P r0).2 := by
      have hdot0 : dot2 (hullVerts P r0) (gamma 0) = topEnv P 0 :=
        h0_spec.2 0 h0_le (le_trans (le_of_lt (hullMidpoint_spec P r0).1) (le_of_lt (hullMidpoint_spec P r0).2.1))
      rw [gamma_zero] at hdot0
      simp only [dot2, mul_zero, zero_add, mul_one] at hdot0
      rw [hdot0]
      exact htop le_rfl (by norm_num)
    have h0_x_neg : (hullVerts P r0).1 < 0 := by
      rcases P.vec_inOmega (hullIdx P r0) with hx | hy
      · exact hx
      · change (hullVerts P r0).2 < 0 at hy; linarith
    have hnorm := inOmega_norm_pos (P.vec_inOmega (hullIdx P r0))
    change 0 < |(hullVerts P r0).1| + |(hullVerts P r0).2| at hnorm
    change rayParam (hullVerts P r0) < 1
    unfold rayParam
    rw [if_pos (le_of_lt h0_pos), abs_of_neg h0_x_neg, abs_of_pos h0_pos]
    have hnorm' : 0 < -(hullVerts P r0).1 + (hullVerts P r0).2 := by
      rw [← abs_of_neg h0_x_neg, ← abs_of_pos h0_pos]; exact hnorm
    exact (div_lt_one hnorm').mpr (by linarith)
  have hlast_gt2 : 2 < rayParam (hullVerts P ⟨h - 1, by omega⟩) := by
    let rL : Fin h := ⟨h - 1, by omega⟩
    have hL_spec := hullIdx_dot_eq_topEnv_on_interval P hgp rL
    have hL_pos : 0 < (hullVerts P rL).1 := by
      have h3_eq : (hullSeamList P)[rL.val + 1]'(by rw [hullSeamList_length]; omega) = 3 := by
        have := hullSeamList_last P
        simpa [rL, h] using this
      have hdot3 : dot2 (hullVerts P rL) (gamma 3) = topEnv P 3 :=
        hL_spec.2 3 (by rw [← h3_eq]; exact le_of_lt (lt_trans (hullMidpoint_spec P rL).1 (hullMidpoint_spec P rL).2.1))
          (by rw [h3_eq])
      rw [gamma_three] at hdot3
      simp only [dot2, mul_one, mul_zero, add_zero] at hdot3
      rw [hdot3]
      exact htop (by norm_num) le_rfl
    have hL_y_neg : (hullVerts P rL).2 < 0 := by
      rcases P.vec_inOmega (hullIdx P rL) with hx | hy
      · change (hullVerts P rL).1 < 0 at hx; linarith
      · exact hy
    have hnorm := inOmega_norm_pos (P.vec_inOmega (hullIdx P rL))
    change 0 < |(hullVerts P rL).1| + |(hullVerts P rL).2| at hnorm
    unfold rayParam
    rw [if_neg (not_le.mpr hL_y_neg)]
    have hpos_div : 0 < (hullVerts P rL).1 / (|(hullVerts P rL).1| + |(hullVerts P rL).2|) :=
      div_pos hL_pos hnorm
    linarith
  have hcard1 : 1 ≤ (topTiePts P).card := by
    by_contra h0
    have hc0 : (topTiePts P).card = 0 := by omega
    have hr_eq : (⟨0, by omega⟩ : Fin h) = ⟨h - 1, by omega⟩ := by ext; dsimp [h]; omega
    rw [← hr_eq] at hlast_gt2
    linarith
  refine ⟨hcard1, hle10, hinj, hmono, h0_lt1, hlast_gt2, ?_⟩
  intro z hz r₁ r₂ r₃ h12 h23 hd1 hd3
  exact hullVerts_contig_le P hgp htop z hz r₁ r₂ r₃ h12 h23 (le_of_lt hd1) (le_of_lt hd3)

private lemma det2_pos_of_rayParam_lt {u v : ℝ × ℝ} (hu : InOmega u) (hv : InOmega v)
    (hlt : rayParam u < rayParam v) (hspan : rayParam v - rayParam u < 2) :
    0 < det2 u v := by
  have hnu := inOmega_norm_pos hu
  have hnv := inOmega_norm_pos hv
  have htu := rayParam_mem_Ioo hu
  have htv := rayParam_mem_Ioo hv
  have hdet_g : 0 < det2 (gamma (rayParam u)) (gamma (rayParam v)) :=
    (gamma_det2_sign (le_of_lt htu.1) hlt (le_of_lt htv.2)).1.mpr hspan
  rw [← gamma_rayParam_smul hu, ← gamma_rayParam_smul hv, det2_smul_left, det2_smul_right]
  exact mul_pos hnu (mul_pos hnv hdet_g)

/-- Interior-sector and case-free outer-flap domination for non-hull vectors `R_Ω`. -/
theorem hull_domination (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (a : Fin 10) (ha_not : ∀ r, hullIdx P r ≠ a) :
    let h := (topTiePts P).card + 1
    (rayParam (P.vec a) < rayParam (hullVerts P ⟨0, by omega⟩) ∧
      ∀ z : ℝ × ℝ, InOmega z → 1 ≤ dot2 (P.vec a) z →
        1 < dot2 (hullVerts P ⟨0, by omega⟩) z) ∨
    (rayParam (hullVerts P ⟨h - 1, by omega⟩) < rayParam (P.vec a) ∧
      ∀ z : ℝ × ℝ, InOmega z → 1 ≤ dot2 (P.vec a) z →
        1 < dot2 (hullVerts P ⟨h - 1, by omega⟩) z) ∨
    (∃ r : Fin h, ∃ hr : r.val + 1 < h,
      rayParam (hullVerts P r) < rayParam (P.vec a) ∧
      rayParam (P.vec a) < rayParam (hullVerts P ⟨r.val + 1, hr⟩) ∧
      ∀ z : ℝ × ℝ, InOmega z → 1 ≤ dot2 (P.vec a) z →
        1 < dot2 (hullVerts P r) z ∨ 1 < dot2 (hullVerts P ⟨r.val + 1, hr⟩) z) := by
  intro h
  have hspec := hullVerts_spec P hgp htop
  have ha_om : InOmega (P.vec a) := P.vec_inOmega a
  have hta := rayParam_mem_Ioo ha_om
  have hne_ray : ∀ r : Fin h, rayParam (P.vec a) ≠ rayParam (hullVerts P r) := by
    intro r heq
    have hdet0 : det2 (P.vec a) (hullVerts P r) = 0 := by
      have h1 := gamma_rayParam_smul ha_om
      have h2 := gamma_rayParam_smul (P.vec_inOmega (hullIdx P r))
      dsimp only [hullVerts] at heq ⊢
      rw [← h1, ← h2, heq, det2_smul_left, det2_smul_right, det2_self]
      ring
    exact hgp.2.2.1 a (hullIdx P r) (ha_not r).symm hdet0
  by_cases hleft : rayParam (P.vec a) < rayParam (hullVerts P ⟨0, by omega⟩)
  · left
    refine ⟨hleft, fun z hz hzu => ?_⟩
    let w := hullVerts P ⟨0, by omega⟩
    let u := P.vec a
    have hw_om : InOmega w := P.vec_inOmega _
    have hw_lt1 : rayParam w < 1 := hspec.2.2.2.2.1
    have hu_lt1 : rayParam u < 1 := lt_trans hleft hw_lt1
    have hu_signs : u.1 < 0 ∧ 0 < u.2 := by
      have hrec := gamma_rayParam_smul ha_om
      have hnu := inOmega_norm_pos ha_om
      have hg : gamma (rayParam u) = (-rayParam u, 1 - rayParam u) := by
        unfold gamma; rw [if_pos (le_of_lt hu_lt1)]
      dsimp only [u]
      rw [← hrec]
      change (((|(P.vec a).1| + |(P.vec a).2|) • gamma (rayParam u)).1 < 0) ∧
             (0 < ((|(P.vec a).1| + |(P.vec a).2|) • gamma (rayParam u)).2)
      rw [hg]
      exact ⟨by dsimp; nlinarith [hta.1], by dsimp; nlinarith [hu_lt1]⟩
    have hw_signs : w.1 < 0 ∧ 0 < w.2 := by
      have hrec := gamma_rayParam_smul hw_om
      have hnw := inOmega_norm_pos hw_om
      have htw := rayParam_mem_Ioo hw_om
      have hg : gamma (rayParam w) = (-rayParam w, 1 - rayParam w) := by
        unfold gamma; rw [if_pos (le_of_lt hw_lt1)]
      rw [← hrec, hg]
      exact ⟨by dsimp; nlinarith [htw.1], by dsimp; nlinarith [hw_lt1]⟩
    have hu_lt_w2 : u.2 < w.2 := by
      have h0_spec := hullIdx_dot_eq_topEnv_on_interval P hgp ⟨0, by omega⟩
      have h0_le : (hullSeamList P)[0]'(by rw [hullSeamList_length]; omega) ≤ 0 := by
        rw [hullSeamList_zero]
      have hw_top : dot2 w (gamma 0) = topEnv P 0 :=
        h0_spec.2 0 h0_le (le_trans (le_of_lt (hullMidpoint_spec P ⟨0, by omega⟩).1)
          (le_of_lt (hullMidpoint_spec P ⟨0, by omega⟩).2.1))
      have hle : dot2 u (gamma 0) ≤ dot2 w (gamma 0) := by
        rw [hw_top]; exact dot2_vec_le_topEnv P a 0
      have hne : dot2 u (gamma 0) ≠ dot2 w (gamma 0) :=
        ((ray_ties_zeros_disjoint P hgp).2.1 0 (by simp) a (hullIdx P ⟨0, by omega⟩)).2
          (ha_not ⟨0, by omega⟩).symm
      rw [gamma_zero] at hle hne
      simp only [dot2, mul_zero, zero_add, mul_one] at hle hne
      exact lt_of_le_of_ne hle hne
    have hdet_uw : 0 < det2 u w :=
      det2_pos_of_rayParam_lt ha_om hw_om hleft (by linarith [hta.1, hw_lt1])
    have hz1_le : z.1 ≤ 0 := by
      by_contra hz1_pos
      replace hz1_pos : 0 < z.1 := not_le.mp hz1_pos
      have hz2_neg : z.2 < 0 := by
        rcases hz with h1 | h2
        · linarith
        · exact h2
      have hdot_neg : dot2 u z < 0 := by
        unfold dot2; nlinarith [hu_signs.1, hu_signs.2]
      linarith
    have hid : w.2 * dot2 u z = u.2 * dot2 w z + det2 u w * z.1 := by
      unfold dot2 det2; ring
    have hdet_z1 : det2 u w * z.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdet_uw) hz1_le
    nlinarith [hw_signs.2, hu_signs.2]
  · by_cases hright : rayParam (hullVerts P ⟨h - 1, by omega⟩) < rayParam (P.vec a)
    · right; left
      refine ⟨hright, fun z hz hzu => ?_⟩
      let w := hullVerts P ⟨h - 1, by omega⟩
      let u := P.vec a
      have hw_om : InOmega w := P.vec_inOmega _
      have hw_gt2 : 2 < rayParam w := hspec.2.2.2.2.2.1
      have hu_gt2 : 2 < rayParam u := lt_trans hw_gt2 hright
      have hu_signs : 0 < u.1 ∧ u.2 < 0 := by
        have hrec := gamma_rayParam_smul ha_om
        have hnu := inOmega_norm_pos ha_om
        have hg : gamma (rayParam u) = (rayParam u - 2, rayParam u - 3) := by
          unfold gamma; rw [if_neg (by linarith), if_neg (by linarith)]
        dsimp only [u]
        rw [← hrec]
        change (0 < ((|(P.vec a).1| + |(P.vec a).2|) • gamma (rayParam u)).1) ∧
               (((|(P.vec a).1| + |(P.vec a).2|) • gamma (rayParam u)).2 < 0)
        rw [hg]
        exact ⟨by dsimp; nlinarith [hu_gt2], by dsimp; nlinarith [hta.2]⟩
      have hw_signs : 0 < w.1 ∧ w.2 < 0 := by
        have hrec := gamma_rayParam_smul hw_om
        have hnw := inOmega_norm_pos hw_om
        have htw := rayParam_mem_Ioo hw_om
        have hg : gamma (rayParam w) = (rayParam w - 2, rayParam w - 3) := by
          unfold gamma; rw [if_neg (by linarith), if_neg (by linarith)]
        rw [← hrec, hg]
        exact ⟨by dsimp; nlinarith [hw_gt2], by dsimp; nlinarith [htw.2]⟩
      have hu_lt_w1 : u.1 < w.1 := by
        let rL : Fin h := ⟨h - 1, by omega⟩
        have hL_spec := hullIdx_dot_eq_topEnv_on_interval P hgp rL
        have h3_eq : (hullSeamList P)[rL.val + 1]'(by rw [hullSeamList_length]; omega) = 3 := by
          have := hullSeamList_last P
          simpa [rL, h] using this
        have hw_top : dot2 w (gamma 3) = topEnv P 3 :=
          hL_spec.2 3 (by rw [← h3_eq]; exact le_of_lt (lt_trans (hullMidpoint_spec P rL).1 (hullMidpoint_spec P rL).2.1))
            (by rw [h3_eq])
        have hle : dot2 u (gamma 3) ≤ dot2 w (gamma 3) := by
          rw [hw_top]; exact dot2_vec_le_topEnv P a 3
        have hne : dot2 u (gamma 3) ≠ dot2 w (gamma 3) :=
          ((ray_ties_zeros_disjoint P hgp).2.1 3 (by simp) a (hullIdx P rL)).2
            (ha_not rL).symm
        rw [gamma_three] at hle hne
        simp only [dot2, mul_one, mul_zero, add_zero] at hle hne
        exact lt_of_le_of_ne hle hne
      have hdet_wu : 0 < det2 w u :=
        det2_pos_of_rayParam_lt hw_om ha_om hright (by linarith [hw_gt2, hta.2])
      have hz2_le : z.2 ≤ 0 := by
        by_contra hz2_pos
        replace hz2_pos : 0 < z.2 := not_le.mp hz2_pos
        have hz1_neg : z.1 < 0 := by
          rcases hz with h1 | h2
          · exact h1
          · linarith
        have hdot_neg : dot2 u z < 0 := by
          unfold dot2; nlinarith [hu_signs.1, hu_signs.2]
        linarith
      have hid : w.1 * dot2 u z = u.1 * dot2 w z + det2 w u * z.2 := by
        unfold dot2 det2; ring
      have hdet_z2 : det2 w u * z.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdet_wu) hz2_le
      nlinarith [hw_signs.1, hu_signs.1]
    · right; right
      have h0_lt : rayParam (hullVerts P ⟨0, by omega⟩) < rayParam (P.vec a) :=
        lt_of_le_of_ne (not_lt.mp hleft) (hne_ray ⟨0, by omega⟩).symm
      have hlast_gt : rayParam (P.vec a) < rayParam (hullVerts P ⟨h - 1, by omega⟩) :=
        lt_of_le_of_ne (not_lt.mp hright) (hne_ray ⟨h - 1, by omega⟩)
      obtain ⟨r, hr_ne_last, hr_lt, hr'_gt⟩ : ∃ r : Fin h, ∃ hr : r.val + 1 < h,
          rayParam (hullVerts P r) < rayParam (P.vec a) ∧
          rayParam (P.vec a) < rayParam (hullVerts P ⟨r.val + 1, hr⟩) := by
        let S_lt : Finset (Fin h) :=
          Finset.univ.filter fun r : Fin h => rayParam (hullVerts P r) < rayParam (P.vec a)
        have hS_ne : S_lt.Nonempty := ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0_lt⟩⟩
        let r : Fin h := S_lt.max' hS_ne
        have hr_mem : r ∈ S_lt := Finset.max'_mem S_lt hS_ne
        have hr_lt : rayParam (hullVerts P r) < rayParam (P.vec a) := (Finset.mem_filter.mp hr_mem).2
        have hr_ne_last : r.val + 1 < h := by
          by_contra hge
          have hr_lt_h : r.val < h := r.isLt
          have h_pos : 0 < h := by omega
          have h_eq : r = ⟨h - 1, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [h_eq] at hr_lt
          linarith
        let r' : Fin h := ⟨r.val + 1, hr_ne_last⟩
        have hr'_gt : rayParam (P.vec a) < rayParam (hullVerts P r') := by
          have hr'_not : r' ∉ S_lt := by
            intro hm
            have hle := Finset.le_max' S_lt r' hm
            change r.val + 1 ≤ r.val at hle
            omega
          rw [Finset.mem_filter] at hr'_not
          have hge : rayParam (P.vec a) ≤ rayParam (hullVerts P r') := by
            by_contra hlt'
            exact hr'_not ⟨Finset.mem_univ _, not_le.mp hlt'⟩
          exact lt_of_le_of_ne hge (hne_ray r')
        exact ⟨r, hr_ne_last, hr_lt, hr'_gt⟩
      let r' : Fin h := ⟨r.val + 1, hr_ne_last⟩
      refine ⟨r, hr_ne_last, hr_lt, hr'_gt, fun z hz hzu => ?_⟩
      let w₁ := hullVerts P r
      let w₂ := hullVerts P r'
      let u := P.vec a
      have hlen := hullSeamList_length P
      have hr1_lt : r.val + 1 < (hullSeamList P).length := by rw [hlen]; omega
      let ξ : ℝ := (hullSeamList P)[r.val + 1]'hr1_lt
      have hm_r := hullMidpoint_spec P r
      have hm_r' := hullMidpoint_spec P r'
      have hξ0 : 0 < ξ := lt_of_le_of_lt hm_r.2.2.1 (lt_trans hm_r.1 hm_r.2.1)
      have hξ3 : ξ < 3 := lt_of_lt_of_le (lt_trans hm_r'.1 hm_r'.2.1) hm_r'.2.2.2.1
      have hξ_om : InOmega (gamma ξ) := gamma_inOmega hξ0 hξ3
      have hξ_w1 : dot2 w₁ (gamma ξ) = topEnv P ξ :=
        (hullIdx_dot_eq_topEnv_on_interval P hgp r).2 ξ
          (le_of_lt (lt_trans hm_r.1 hm_r.2.1)) le_rfl
      have hξ_w2 : dot2 w₂ (gamma ξ) = topEnv P ξ :=
        (hullIdx_dot_eq_topEnv_on_interval P hgp r').2 ξ
          le_rfl (le_of_lt (lt_trans hm_r'.1 hm_r'.2.1))
      have htop_ξ : 0 < topEnv P ξ := htop (le_of_lt hξ0) (le_of_lt hξ3)
      have hξ_u_lt : dot2 u (gamma ξ) < topEnv P ξ := by
        refine lt_of_le_of_ne (dot2_vec_le_topEnv P a ξ) fun heq => ?_
        have hidx_ne : hullIdx P r ≠ hullIdx P r' := hspec.2.2.1.ne (Fin.ne_of_val_ne (by dsimp [r']; omega))
        have hu_ne1 : a ≠ hullIdx P r := (ha_not r).symm
        have hu_ne2 : a ≠ hullIdx P r' := (ha_not r').symm
        rcases lt_or_gt_of_ne hidx_ne with h12 | h21 <;> rcases lt_or_gt_of_ne hu_ne1 with hau | uha
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 ξ hξ0 hξ3 a (hullIdx P r) (hullIdx P r) (hullIdx P r')
            hau h12 (by intro hp; exact hu_ne1 (congrArg Prod.fst hp)) ⟨heq.trans hξ_w1.symm, hξ_w1.trans hξ_w2.symm⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 ξ hξ0 hξ3 (hullIdx P r) a (hullIdx P r) (hullIdx P r')
            uha h12 (by intro hp; exact hu_ne2 (congrArg Prod.snd hp)) ⟨hξ_w1.trans heq.symm, hξ_w1.trans hξ_w2.symm⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 ξ hξ0 hξ3 a (hullIdx P r) (hullIdx P r') (hullIdx P r)
            hau h21 (by intro hp; exact hu_ne2 (congrArg Prod.fst hp)) ⟨heq.trans hξ_w1.symm, hξ_w2.trans hξ_w1.symm⟩
        · exact (ray_ties_zeros_disjoint P hgp).2.2.2 ξ hξ0 hξ3 (hullIdx P r) a (hullIdx P r') (hullIdx P r)
            uha h21 (by intro hp; exact hu_ne1 (congrArg Prod.snd hp)) ⟨hξ_w1.trans heq.symm, hξ_w2.trans hξ_w1.symm⟩
      have hw1_om : InOmega w₁ := P.vec_inOmega _
      have hw2_om : InOmega w₂ := P.vec_inOmega _
      have hw1_ray_lt_w2 : rayParam w₁ < rayParam w₂ :=
        hspec.2.2.2.1 (show r.val < r'.val by dsimp [r']; omega)
      have hspan_w12 : rayParam w₂ - rayParam w₁ < 2 := by
        have hpos1 : 0 < dot2 (gamma ξ) (gamma (rayParam w₁)) := by
          rw [← gamma_rayParam_smul hw1_om, dot2_smul_left] at hξ_w1
          have : 0 < (|w₁.1| + |w₁.2|) * dot2 (gamma (rayParam w₁)) (gamma ξ) := by
            rw [hξ_w1]; exact htop_ξ
          rw [dot2_comm]
          exact pos_of_mul_pos_right this (le_of_lt (inOmega_norm_pos hw1_om))
        have hpos2 : 0 < dot2 (gamma ξ) (gamma (rayParam w₂)) := by
          rw [← gamma_rayParam_smul hw2_om, dot2_smul_left] at hξ_w2
          have : 0 < (|w₂.1| + |w₂.2|) * dot2 (gamma (rayParam w₂)) (gamma ξ) := by
            rw [hξ_w2]; exact htop_ξ
          rw [dot2_comm]
          exact pos_of_mul_pos_right this (le_of_lt (inOmega_norm_pos hw2_om))
        exact (omega_pos_span (le_of_lt (rayParam_mem_Ioo hw1_om).1) hw1_ray_lt_w2
          (le_of_lt (rayParam_mem_Ioo hw2_om).2) hpos1 hpos2 (Or.inl hξ_om)).1
      have hdet_12 : 0 < det2 w₁ w₂ := det2_pos_of_rayParam_lt hw1_om hw2_om hw1_ray_lt_w2 hspan_w12
      have hdet_1u : 0 < det2 w₁ u := det2_pos_of_rayParam_lt hw1_om ha_om hr_lt (by linarith)
      have hdet_u2 : 0 < det2 u w₂ := det2_pos_of_rayParam_lt ha_om hw2_om hr'_gt (by linarith)
      have hcr_ξ : det2 w₁ w₂ * dot2 u (gamma ξ) =
          det2 u w₂ * dot2 w₁ (gamma ξ) + det2 w₁ u * dot2 w₂ (gamma ξ) := by
        simp only [det2, dot2]; ring
      rw [hξ_w1, hξ_w2] at hcr_ξ
      have hsum_lt : det2 u w₂ + det2 w₁ u < det2 w₁ w₂ := by nlinarith
      have hcr_z : det2 w₁ w₂ * dot2 u z = det2 u w₂ * dot2 w₁ z + det2 w₁ u * dot2 w₂ z := by
        simp only [det2, dot2]; ring
      by_contra hnot
      push Not at hnot
      nlinarith

private lemma compressAdj_mem_iff :
    ∀ (l : List (Fin 5)) (c : Fin 5), c ∈ compressAdj l ↔ c ∈ l
  | [], _ => by simp [compressAdj]
  | [x], c => by simp [compressAdj]
  | x :: y :: rest, c => by
    simp only [compressAdj]
    split_ifs with hxy
    · rw [compressAdj_mem_iff (y :: rest) c]
      subst hxy
      simp
    · simp only [List.mem_cons]
      rw [compressAdj_mem_iff (y :: rest) c]
      simp

private lemma compressAdj_length_le :
    ∀ l : List (Fin 5), (compressAdj l).length ≤ l.length
  | [] => by simp [compressAdj]
  | [x] => by simp [compressAdj]
  | x :: y :: rest => by
    simp only [compressAdj]
    split_ifs
    · exact (compressAdj_length_le (y :: rest)).trans (by simp)
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (compressAdj_length_le (y :: rest))

/-- Every color `i ∈ Fin 5` appears on `H_Ω`, so `5 ≤ n_Ω ≤ 10` and non-hull vectors have
pairwise distinct colors. -/
theorem hull_five_colors (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    Function.Surjective (hullColors P) ∧
    5 ≤ hullBlockCount P ∧ hullBlockCount P ≤ 10 ∧
    (∀ a b : Fin 10, (∀ r, hullIdx P r ≠ a) → (∀ r, hullIdx P r ≠ b) →
      vecColor a = vecColor b → a = b) := by
  have hsurj : Function.Surjective (hullColors P) := by
    intro i
    obtain ⟨z, hz_om, hz_mask⟩ := h_shat (fun j => !decide (j = i))
    have hmem_ext : P.MemExt i z := by
      have hi := hz_mask i
      simpa using hi
    have hmem_open : ∀ j : Fin 5, j ≠ i → P.MemOpen j z := by
      intro j hj
      have hjj := hz_mask j
      simpa [hj] using hjj
    have hnot_other : ∀ r : Fin ((topTiePts P).card + 1), 1 < dot2 (hullVerts P r) z →
        hullColors P r = i := by
      intro r hdr
      by_contra hne
      have ho := hmem_open (hullColors P r) hne
      unfold hullVerts at hdr
      have hvc : (hullIdx P r).val / 2 = (hullColors P r).val := rfl
      unfold DualConfig.vec at hdr
      split_ifs at hdr with hev
      · have heq_i : (⟨(hullIdx P r).val / 2, by omega⟩ : Fin 5) = hullColors P r := Fin.ext hvc
        rw [heq_i] at hdr
        linarith [ho.1]
      · have heq_i : (⟨(hullIdx P r).val / 2, by omega⟩ : Fin 5) = hullColors P r := Fin.ext hvc
        rw [heq_i] at hdr
        linarith [ho.2]
    obtain ⟨a, ha_col, ha_dot⟩ : ∃ a : Fin 10, vecColor a = i ∧ 1 < dot2 (P.vec a) z := by
      rcases hmem_ext with h1 | h2
      · refine ⟨⟨2 * i.val, by omega⟩, ?_, ?_⟩
        · ext; dsimp [vecColor]; omega
        · rw [P.vec_even i]; exact h1
      · refine ⟨⟨2 * i.val + 1, by omega⟩, ?_, ?_⟩
        · ext; dsimp [vecColor]; omega
        · rw [P.vec_odd i]; exact h2
    by_cases hex : ∃ r, hullIdx P r = a
    · obtain ⟨r, hr⟩ := hex
      exact ⟨r, by unfold hullColors; rw [hr, ha_col]⟩
    · push Not at hex
      rcases hull_domination P hgp htop a hex with ⟨_, hdom⟩ | ⟨_, hdom⟩ | ⟨r, hr, _, _, hdom⟩
      · exact ⟨⟨0, by omega⟩, hnot_other _ (hdom z hz_om (le_of_lt ha_dot))⟩
      · exact ⟨⟨(topTiePts P).card, by omega⟩, hnot_other _ (hdom z hz_om (le_of_lt ha_dot))⟩
      · rcases hdom z hz_om (le_of_lt ha_dot) with hd1 | hd2
        · exact ⟨r, hnot_other _ hd1⟩
        · exact ⟨⟨r.val + 1, hr⟩, hnot_other _ hd2⟩
  have h5_le : 5 ≤ hullBlockCount P := by
    unfold hullBlockCount compressedColors
    have hsub : (Finset.univ : Finset (Fin 5)) ⊆ (compressAdj (List.ofFn (hullColors P))).toFinset := by
      intro i _
      rw [List.mem_toFinset, compressAdj_mem_iff, List.mem_ofFn]
      exact hsurj i
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    exact le_trans hcard (List.toFinset_card_le _)
  have h_le10 : hullBlockCount P ≤ 10 := by
    unfold hullBlockCount compressedColors
    have hlen1 := compressAdj_length_le (List.ofFn (hullColors P))
    rw [List.length_ofFn] at hlen1
    exact le_trans hlen1 (hullVerts_spec P hgp htop).2.1
  refine ⟨hsurj, h5_le, h_le10, fun a b ha hb hcol => ?_⟩
  obtain ⟨r, hr⟩ := hsurj (vecColor a)
  unfold hullColors at hr
  have har : hullIdx P r ≠ a := ha r
  have hbr : hullIdx P r ≠ b := hb r
  have hc1 : a.val / 2 = (hullIdx P r).val / 2 := by
    have := congrArg Fin.val hr; dsimp [vecColor] at this; exact this.symm
  have hc2 : b.val / 2 = (hullIdx P r).val / 2 := by
    have := congrArg Fin.val (hcol.symm.trans hr.symm); dsimp [vecColor] at this; exact this
  have hne1 : a.val ≠ (hullIdx P r).val := fun h => har (Fin.ext h.symm)
  have hne2 : b.val ≠ (hullIdx P r).val := fun h => hbr (Fin.ext h.symm)
  ext; omega

private lemma compressAdj_head? (x : Fin 5) (xs : List (Fin 5)) :
    (compressAdj (x :: xs)).head? = some x := by
  induction xs generalizing x with
  | nil => rfl
  | cons y rest ih =>
    simp only [compressAdj]
    split_ifs with hxy
    · rw [hxy]; exact ih y
    · rfl

private lemma compressAdj_adj_pair :
    ∀ (l : List (Fin 5)) (k : ℕ) (hk : k + 1 < (compressAdj l).length),
      ∃ m : ℕ, ∃ hm : m + 1 < l.length,
        (compressAdj l)[k]'(Nat.lt_of_succ_lt hk) = l[m]'(Nat.lt_of_succ_lt hm) ∧
        (compressAdj l)[k + 1]'hk = l[m + 1]'hm ∧
        l[m]'(Nat.lt_of_succ_lt hm) ≠ l[m + 1]'hm
  | [], _, hk => by simp [compressAdj] at hk
  | [_], _, hk => by simp [compressAdj] at hk
  | x :: y :: rest, k, hk => by
    simp only [compressAdj] at hk ⊢
    split_ifs with hxy
    · obtain ⟨m, hm, h1, h2, hne⟩ := compressAdj_adj_pair (y :: rest) k (by simpa [hxy] using hk)
      refine ⟨m + 1, by simpa using hm, ?_, ?_, hne⟩
      · simpa [hxy] using h1
      · simpa [hxy] using h2
    · cases k with
      | zero =>
        refine ⟨0, by simp, rfl, ?_, hxy⟩
        have hhd := compressAdj_head? y rest
        have heq0 : ∀ (xs : List (Fin 5)) (hxs : xs.head? = some y) (hl : 0 < xs.length),
            xs[0]'hl = y := by
          intro xs hxs hl
          cases xs with
          | nil => simp at hl
          | cons z zs => simp at hxs; exact hxs
        simpa [hxy] using heq0 (compressAdj (y :: rest)) hhd (by
          cases h : compressAdj (y :: rest) with
          | nil => simp [h] at hhd
          | cons _ _ => simp)
      | succ k' =>
        have hk' : k' + 1 < (compressAdj (y :: rest)).length := by
          simpa [hxy] using hk
        obtain ⟨m, hm, h1, h2, hne⟩ := compressAdj_adj_pair (y :: rest) k' hk'
        refine ⟨m + 1, by simpa using hm, ?_, ?_, hne⟩
        · simpa [hxy] using h1
        · simpa [hxy] using h2

private lemma adj_pair_in_compressAdj :
    ∀ (l : List (Fin 5)) (m : ℕ) (hm : m + 1 < l.length),
      l[m]'(Nat.lt_of_succ_lt hm) ≠ l[m + 1]'hm →
      ∃ k : ℕ, ∃ hk : k + 1 < (compressAdj l).length,
        (compressAdj l)[k]'(Nat.lt_of_succ_lt hk) = l[m]'(Nat.lt_of_succ_lt hm) ∧
        (compressAdj l)[k + 1]'hk = l[m + 1]'hm
  | [], _, hm, _ => by simp at hm
  | [_], _, hm, _ => by simp at hm
  | x :: y :: rest, m, hm, hne => by
    simp only [compressAdj]
    split_ifs with hxy
    · cases m with
      | zero => exact absurd hxy hne
      | succ m' =>
        obtain ⟨k, hk, h1, h2⟩ := adj_pair_in_compressAdj (y :: rest) m' (by simpa using hm) hne
        exact ⟨k, hk, h1, h2⟩
    · cases m with
      | zero =>
        have hhd := compressAdj_head? y rest
        have hlen_pos : 0 < (compressAdj (y :: rest)).length := by
          cases h : compressAdj (y :: rest) with
          | nil => simp [h] at hhd
          | cons _ _ => simp
        refine ⟨0, by simp [hlen_pos], rfl, ?_⟩
        have heq0 : ∀ (xs : List (Fin 5)) (hxs : xs.head? = some y) (hl : 0 < xs.length),
            xs[0]'hl = y := by
          intro xs hxs hl
          cases xs with
          | nil => simp at hl
          | cons z zs => simp at hxs; exact hxs
        simpa [hxy] using heq0 (compressAdj (y :: rest)) hhd hlen_pos
      | succ m' =>
        obtain ⟨k, hk, h1, h2⟩ := adj_pair_in_compressAdj (y :: rest) m' (by simpa using hm) hne
        exact ⟨k + 1, by simp; exact hk, h1, h2⟩

private lemma const_on_range
    {h : ℕ} (c : Fin h → Fin 5) (r₁ r₂ : Fin h)
    (S : Finset (Fin 5)) (hS2 : S.card = 2)
    (himg : (Finset.univ.filter (fun r : Fin h => r₁ ≤ r ∧ r ≤ r₂)).image c = S)
    (hno : ∀ k : ℕ, ∀ hk : k + 1 < h, r₁.val ≤ k → k + 1 ≤ r₂.val →
      ({c ⟨k, by omega⟩, c ⟨k + 1, hk⟩} : Finset (Fin 5)) ≠ S) :
    ∀ n : ℕ, ∀ hn : n < h, r₁.val ≤ n → n ≤ r₂.val → c ⟨n, hn⟩ = c r₁ := by
  intro n
  induction n with
  | zero =>
    intro hn hr1 _
    have hr1_eq : r₁ = ⟨0, hn⟩ := by ext; dsimp; omega
    rw [hr1_eq]
  | succ k ih =>
    intro hk hr1 hr2
    by_cases hstart : k + 1 = r₁.val
    · have heq : (⟨k + 1, hk⟩ : Fin h) = r₁ := by ext; dsimp; omega
      rw [heq]
    · have hk_ge : r₁.val ≤ k := by omega
      have hk_lt : k < h := by omega
      have hprev : c ⟨k, hk_lt⟩ = c r₁ := ih hk_lt hk_ge (by omega)
      by_contra hne
      apply hno k hk hk_ge hr2
      apply Finset.eq_of_subset_of_card_le
      · rw [← himg]
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_image.mpr ⟨⟨k, hk_lt⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.mk_le_mk.mpr hk_ge, Fin.mk_le_mk.mpr (by omega)⟩, rfl⟩
        · exact Finset.mem_image.mpr ⟨⟨k + 1, hk⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.mk_le_mk.mpr (by omega), Fin.mk_le_mk.mpr hr2⟩, rfl⟩
      · have hne_pair : c ⟨k, hk_lt⟩ ≠ c ⟨k + 1, hk⟩ := by
          rw [hprev]; exact Ne.symm hne
        rw [hS2, Finset.card_pair hne_pair]

private lemma two_color_interval_has_adjacent_transition
    {h : ℕ}
    (c : Fin h → Fin 5)
    (r₁ r₂ : Fin h) (hle : r₁ ≤ r₂)
    (S : Finset (Fin 5)) (hS2 : S.card = 2)
    (himg : (Finset.univ.filter (fun r : Fin h => r₁ ≤ r ∧ r ≤ r₂)).image c = S) :
    ∃ k : ℕ, ∃ hk : k + 1 < h, r₁.val ≤ k ∧ k + 1 ≤ r₂.val ∧
      ({c ⟨k, by omega⟩, c ⟨k + 1, hk⟩} : Finset (Fin 5)) = S := by
  by_contra hno
  push Not at hno
  have hconst := const_on_range c r₁ r₂ S hS2 himg hno
  have hsub : S ⊆ {c r₁} := by
    rw [← himg]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    have hbounds := (Finset.mem_filter.mp hr).2
    rw [Finset.mem_singleton]
    exact hconst r.val r.isLt hbounds.1 hbounds.2
  have hle1 : S.card ≤ ({c r₁} : Finset (Fin 5)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hle1
  omega

private lemma list_getD_eq_getElem {α : Type*} (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    xs.getD i d = xs[i]'hi := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma list_getElem_eq_of_idx {α : Type*} (xs : List α) {i j : ℕ} (hi : i < xs.length)
    (hj : j < xs.length) (hij : i = j) : xs[j]'hj = xs[i]'hi := by
  subst hij; rfl

/-- Characterization of `pureHullPairs P` as contiguous hull `2`-color subsets. -/
theorem pure_hull_pairs_eq (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t) :
    ∀ S : Finset (Fin 5), S.card = 2 →
      (S ∈ pureHullPairs P ↔
        ∃ r₁ r₂ : Fin ((topTiePts P).card + 1), r₁ ≤ r₂ ∧
          ((Finset.univ : Finset (Fin ((topTiePts P).card + 1))).filter (fun r => r₁ ≤ r ∧ r ≤ r₂)).image (hullColors P) = S) := by
  intro S hS2
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  have hlen_l : l.length = h := List.length_ofFn
  have hcs_def : compressedColors P = compressAdj l := rfl
  constructor
  · intro hmem
    unfold pureHullPairs at hmem
    rw [hcs_def] at hmem
    rw [List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨k, hk_mem, hk_eq⟩ := hmem
    rw [List.mem_range] at hk_mem
    have hk : k + 1 < (compressAdj l).length := by omega
    have hk0 : k < (compressAdj l).length := Nat.lt_of_succ_lt hk
    rw [list_getD_eq_getElem (compressAdj l) k 0 hk0,
      list_getD_eq_getElem (compressAdj l) (k + 1) 0 hk] at hk_eq
    obtain ⟨m, hm, h1, h2, _⟩ := compressAdj_adj_pair l k hk
    have hm_h : m + 1 < h := by rw [← hlen_l]; exact hm
    let r₁ : Fin h := ⟨m, by omega⟩
    let r₂ : Fin h := ⟨m + 1, hm_h⟩
    refine ⟨r₁, r₂, by change m ≤ m + 1; omega, ?_⟩
    have hfilt : (Finset.univ : Finset (Fin h)).filter (fun r => r₁ ≤ r ∧ r ≤ r₂) = {r₁, r₂} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
      dsimp [r₁, r₂]
      omega
    rw [hfilt, Finset.image_insert, Finset.image_singleton]
    have hl1 : l[m]'(Nat.lt_of_succ_lt hm) = hullColors P r₁ := by
      dsimp [l, r₁]; rw [List.getElem_ofFn]
    have hl2 : l[m + 1]'hm = hullColors P r₂ := by
      dsimp [l, r₂]; rw [List.getElem_ofFn]
    rw [← hl1, ← hl2, ← h1, ← h2]
    exact hk_eq
  · rintro ⟨r₁, r₂, hr12, himg⟩
    obtain ⟨m, hm, _, _, hpair⟩ :=
      two_color_interval_has_adjacent_transition (hullColors P) r₁ r₂ hr12 S hS2 himg
    have hm_l : m + 1 < l.length := by rw [hlen_l]; exact hm
    have hl1 : l[m]'(Nat.lt_of_succ_lt hm_l) = hullColors P ⟨m, by omega⟩ := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hl2 : l[m + 1]'hm_l = hullColors P ⟨m + 1, hm⟩ := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hne : l[m]'(Nat.lt_of_succ_lt hm_l) ≠ l[m + 1]'hm_l := by
      rw [hl1, hl2]
      intro heq
      simp [heq] at hpair
      rw [← hpair, Finset.card_singleton] at hS2
      omega
    obtain ⟨k, hk, h1, h2⟩ := adj_pair_in_compressAdj l m hm_l hne
    have hk0 : k < (compressAdj l).length := Nat.lt_of_succ_lt hk
    unfold pureHullPairs
    rw [hcs_def, List.mem_toFinset, List.mem_map]
    refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
    rw [list_getD_eq_getElem (compressAdj l) k 0 hk0,
      list_getD_eq_getElem (compressAdj l) (k + 1) 0 hk]
    rw [h1, h2, hl1, hl2]
    exact hpair

private lemma realizesDualMask_ext_iff (P : DualConfig) (S : Finset (Fin 5)) (z : ℝ × ℝ)
    (hreal : RealizesDualMask P (fun i => !decide (i ∈ S)) z) :
    ∀ i : Fin 5, i ∈ S ↔ ∃ a : Fin 10, vecColor a = i ∧ 1 < dot2 (P.vec a) z := by
  intro i
  have hi := hreal i
  by_cases his : i ∈ S
  · simp only [his, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hi
    refine ⟨fun _ => ?_, fun _ => his⟩
    rcases hi with h1 | h2
    · exact ⟨⟨2 * i.val, by omega⟩, Fin.ext (by dsimp [vecColor]; omega), by rw [P.vec_even i]; exact h1⟩
    · exact ⟨⟨2 * i.val + 1, by omega⟩, Fin.ext (by dsimp [vecColor]; omega), by rw [P.vec_odd i]; exact h2⟩
  · simp only [his, decide_false, Bool.not_false, ↓reduceIte] at hi
    refine ⟨fun h => absurd h his, ?_⟩
    rintro ⟨a, ha_col, ha_dot⟩
    exfalso
    have heq_i : (⟨a.val / 2, by omega⟩ : Fin 5) = i := ha_col
    unfold DualConfig.MemOpen at hi
    unfold DualConfig.vec at ha_dot
    split_ifs at ha_dot
    · rw [heq_i] at ha_dot; linarith [hi.1]
    · rw [heq_i] at ha_dot; linarith [hi.2]

/-- Dual Island Rule: active hull vertices of any nonempty realized exterior set `S` lie in a
single island of `S` along `H_Ω`, with missing colors assisted from incident sectors/flaps. -/
theorem dual_island_rule (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (S : Finset (Fin 5)) (hne : S.Nonempty)
    (z : ℝ × ℝ) (hz : InOmega z)
    (hreal : RealizesDualMask P (fun i => !decide (i ∈ S)) z) :
    ∃ r₁ r₂ : Fin ((topTiePts P).card + 1), r₁ ≤ r₂ ∧
      (∀ r, 1 < dot2 (hullVerts P r) z ↔ r₁ ≤ r ∧ r ≤ r₂) ∧
      (∀ r, r₁ ≤ r → r ≤ r₂ → hullColors P r ∈ S) := by
  let h := (topTiePts P).card + 1
  have hspec := hullVerts_spec P hgp htop
  have hiff := realizesDualMask_ext_iff P S z hreal
  let A : Finset (Fin h) := Finset.univ.filter fun r : Fin h => 1 < dot2 (hullVerts P r) z
  have hA_ne : A.Nonempty := by
    obtain ⟨i, hiS⟩ := hne
    obtain ⟨a, _, ha_dot⟩ := (hiff i).mp hiS
    by_cases hex : ∃ r, hullIdx P r = a
    · obtain ⟨r, hr⟩ := hex
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by unfold hullVerts; rw [hr]; exact ha_dot⟩⟩
    · push Not at hex
      rcases hull_domination P hgp htop a hex with ⟨_, hdom⟩ | ⟨_, hdom⟩ | ⟨r, hr, _, _, hdom⟩
      · exact ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdom z hz (le_of_lt ha_dot)⟩⟩
      · exact ⟨⟨h - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdom z hz (le_of_lt ha_dot)⟩⟩
      · rcases hdom z hz (le_of_lt ha_dot) with h1 | h2
        · exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
        · exact ⟨⟨r.val + 1, hr⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
  let r₁ := A.min' hA_ne
  let r₂ := A.max' hA_ne
  have hr1_mem : r₁ ∈ A := Finset.min'_mem A hA_ne
  have hr2_mem : r₂ ∈ A := Finset.max'_mem A hA_ne
  have hr12 : r₁ ≤ r₂ := Finset.min'_le A r₂ hr2_mem
  have hdot_iff : ∀ r : Fin h, 1 < dot2 (hullVerts P r) z ↔ r₁ ≤ r ∧ r ≤ r₂ := by
    intro r
    constructor
    · intro hr
      have hm : r ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      exact ⟨Finset.min'_le A r hm, Finset.le_max' A r hm⟩
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with rfl | h1'
      · exact (Finset.mem_filter.mp hr1_mem).2
      · rcases eq_or_lt_of_le h2 with rfl | h2'
        · exact (Finset.mem_filter.mp hr2_mem).2
        · exact hspec.2.2.2.2.2.2 z hz r₁ r r₂ h1' h2'
            (Finset.mem_filter.mp hr1_mem).2 (Finset.mem_filter.mp hr2_mem).2
  refine ⟨r₁, r₂, hr12, hdot_iff, fun r hr1 hr2 => ?_⟩
  exact (hiff (hullColors P r)).mpr ⟨hullIdx P r, rfl, (hdot_iff r).mpr ⟨hr1, hr2⟩⟩

/-- Bound on interior-assisted `2`-subsets outside `pureHullPairs P`. -/
theorem interior_assisted_pairs (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (S : Finset (Fin 5)) (hcard : S.card = 2) (hnot : S ∉ pureHullPairs P)
    (z : ℝ × ℝ) (hz : InOmega z)
    (hreal : RealizesDualMask P (fun i => !decide (i ∈ S)) z) :
    ∃ a : Fin 10, (∀ r, hullIdx P r ≠ a) ∧ vecColor a ∈ S ∧
      1 < dot2 (P.vec a) z ∧
      ∀ r, hullColors P r = vecColor a → dot2 (hullVerts P r) z < 1 := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r₁, r₂, hr12, hdot_iff, hcol_in⟩ := dual_island_rule P hgp htop S hne z hz hreal
  have himg_ne :
      (Finset.univ.filter (fun r : Fin ((topTiePts P).card + 1) => r₁ ≤ r ∧ r ≤ r₂)).image (hullColors P) ≠ S := by
    intro heq
    exact hnot ((pure_hull_pairs_eq P hgp htop S hcard).mpr ⟨r₁, r₂, hr12, heq⟩)
  have himg_sub :
      (Finset.univ.filter (fun r : Fin ((topTiePts P).card + 1) => r₁ ≤ r ∧ r ≤ r₂)).image (hullColors P) ⊆ S := by
    intro c hc
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
    have hb := (Finset.mem_filter.mp hr).2
    exact hcol_in r hb.1 hb.2
  have hssub :
      (Finset.univ.filter (fun r : Fin ((topTiePts P).card + 1) => r₁ ≤ r ∧ r ≤ r₂)).image (hullColors P) ⊂ S :=
    lt_of_le_of_ne himg_sub himg_ne
  obtain ⟨c, hcS, hc_not⟩ := Finset.exists_of_ssubset hssub
  have hiff := realizesDualMask_ext_iff P S z hreal
  obtain ⟨a, ha_col, ha_dot⟩ := (hiff c).mp hcS
  have ha_not : ∀ r, hullIdx P r ≠ a := by
    intro r hr
    have hact : 1 < dot2 (hullVerts P r) z := by unfold hullVerts; rw [hr]; exact ha_dot
    have hmem_int := (hdot_iff r).mp hact
    apply hc_not
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem_int⟩,
      by unfold hullColors; rw [hr, ha_col]⟩
  refine ⟨a, ha_not, ha_col ▸ hcS, ha_dot, fun r hr_col => ?_⟩
  rw [ha_col] at hr_col
  by_contra hle
  replace hle : 1 ≤ dot2 (hullVerts P r) z := not_lt.mp hle
  have hr_out : ¬ (r₁ ≤ r ∧ r ≤ r₂) := by
    intro hmem_int
    apply hc_not
    exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem_int⟩, hr_col⟩
  have hr1_act : 1 < dot2 (hullVerts P r₁) z := (hdot_iff r₁).mpr ⟨le_rfl, hr12⟩
  have hr2_act : 1 < dot2 (hullVerts P r₂) z := (hdot_iff r₂).mpr ⟨hr12, le_rfl⟩
  have hr_lt_or_gt : r < r₁ ∨ r₂ < r := by
    by_contra hnot_og
    push Not at hnot_og
    exact hr_out ⟨hnot_og.1, hnot_og.2⟩
  rcases hr_lt_or_gt with hr_lt | hr_gt
  · by_cases hadj : r.val + 1 = r₁.val
    · have himg2 :
          (Finset.univ.filter (fun s : Fin ((topTiePts P).card + 1) => r ≤ s ∧ s ≤ r₁)).image (hullColors P) = S := by
        have hfilt : Finset.univ.filter (fun s : Fin ((topTiePts P).card + 1) => r ≤ s ∧ s ≤ r₁) = {r, r₁} := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
          omega
        rw [hfilt, Finset.image_insert, Finset.image_singleton, hr_col]
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hcS
          · exact hcol_in r₁ le_rfl hr12
        · have hc_ne : c ≠ hullColors P r₁ := by
            intro heq
            apply hc_not
            exact Finset.mem_image.mpr ⟨r₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hr12⟩, heq.symm⟩
          rw [hcard, Finset.card_pair hc_ne]
      exact hnot ((pure_hull_pairs_eq P hgp htop S hcard).mpr ⟨r, r₁, le_of_lt hr_lt, himg2⟩)
    · let r' : Fin ((topTiePts P).card + 1) := ⟨r.val + 1, by omega⟩
      have hr_r' : r < r' := by change r.val < r.val + 1; omega
      have hr'_r1 : r' < r₁ := by change r.val + 1 < r₁.val; omega
      have hact_r' : 1 < dot2 (hullVerts P r') z :=
        hullVerts_contig_le P hgp htop z hz r r' r₁ hr_r' hr'_r1 hle (le_of_lt hr1_act)
      have hmem_r' := (hdot_iff r').mp hact_r'
      exact absurd (lt_of_le_of_lt hmem_r'.1 hr'_r1) (lt_irrefl _)
  · by_cases hadj : r₂.val + 1 = r.val
    · have himg2 :
          (Finset.univ.filter (fun s : Fin ((topTiePts P).card + 1) => r₂ ≤ s ∧ s ≤ r)).image (hullColors P) = S := by
        have hfilt : Finset.univ.filter (fun s : Fin ((topTiePts P).card + 1) => r₂ ≤ s ∧ s ≤ r) = {r₂, r} := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
          omega
        rw [hfilt, Finset.image_insert, Finset.image_singleton, hr_col]
        refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hcol_in r₂ hr12 le_rfl
          · exact hcS
        · have hc_ne : hullColors P r₂ ≠ c := by
            intro heq
            apply hc_not
            exact Finset.mem_image.mpr ⟨r₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr12, le_rfl⟩, heq⟩
          rw [hcard, Finset.card_pair hc_ne]
      exact hnot ((pure_hull_pairs_eq P hgp htop S hcard).mpr ⟨r₂, r, le_of_lt hr_gt, himg2⟩)
    · let r' : Fin ((topTiePts P).card + 1) := ⟨r₂.val + 1, by omega⟩
      have hr2_r' : r₂ < r' := by change r₂.val < r₂.val + 1; omega
      have hr'_r : r' < r := by change r₂.val + 1 < r.val; omega
      have hact_r' : 1 < dot2 (hullVerts P r') z :=
        hullVerts_contig_le P hgp htop z hz r₂ r' r hr2_r' hr'_r (le_of_lt hr2_act) hle
      have hmem_r' := (hdot_iff r').mp hact_r'
      exact absurd (lt_of_lt_of_le hr2_r' hmem_r'.2) (lt_irrefl _)

private def blockIndicesAux : ℕ → List (Fin 5) → List ℕ
  | _, [] => []
  | k, [_] => [k]
  | k, x :: y :: rest => k :: blockIndicesAux (if x = y then k else k + 1) (y :: rest)

private lemma blockIndicesAux_length (k : ℕ) (l : List (Fin 5)) :
    (blockIndicesAux k l).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y rest => dsimp only [blockIndicesAux]; rw [List.length_cons, ih]; rfl

private lemma blockIndicesAux_bounds :
    ∀ (k : ℕ) (l : List (Fin 5)) (r : ℕ) (hr : r < l.length),
      k ≤ (blockIndicesAux k l)[r]'(by rw [blockIndicesAux_length]; exact hr) ∧
      (blockIndicesAux k l)[r]'(by rw [blockIndicesAux_length]; exact hr) < k + (compressAdj l).length
  | k, [], r, hr => by simp at hr
  | k, [x], r, hr => by
    have hr0 : r = 0 := by simp at hr; omega
    subst hr0; simp [blockIndicesAux, compressAdj]
  | k, x :: y :: rest, r, hr => by
    cases r with
    | zero =>
      simp only [blockIndicesAux, List.getElem_cons_zero]
      have hlen : 0 < (compressAdj (x :: y :: rest)).length := by
        simp only [compressAdj]
        split_ifs
        · cases h : compressAdj (y :: rest) with
          | nil =>
            have hmem := (compressAdj_mem_iff (y :: rest) y).mpr (by simp)
            rw [h] at hmem; simp at hmem
          | cons _ _ => simp
        · simp
      omega
    | succ r' =>
      simp only [blockIndicesAux, List.getElem_cons_succ, compressAdj]
      have hr' : r' < (y :: rest).length := by simpa using hr
      split_ifs with hxy
      · exact blockIndicesAux_bounds k (y :: rest) r' hr'
      · have hb := blockIndicesAux_bounds (k + 1) (y :: rest) r' hr'
        simp only [List.length_cons]
        omega

private lemma blockIndicesAux_zero (k : ℕ) (x : Fin 5) (xs : List (Fin 5)) :
    (blockIndicesAux k (x :: xs))[0]'(by rw [blockIndicesAux_length]; simp) = k := by
  cases xs <;> rfl

private lemma blockIndicesAux_head (k : ℕ) (l : List (Fin 5)) (hl : 0 < l.length) :
    (blockIndicesAux k l)[0]'(by rw [blockIndicesAux_length]; exact hl) = k := by
  cases l with
  | nil => simp at hl
  | cons x xs => exact blockIndicesAux_zero k x xs

private lemma blockIndicesAux_last :
    ∀ (k : ℕ) (l : List (Fin 5)) (hl : 0 < l.length),
      (blockIndicesAux k l)[l.length - 1]'(by rw [blockIndicesAux_length]; omega) =
        k + (compressAdj l).length - 1
  | k, [], hl => by simp at hl
  | k, [x], _ => by simp [blockIndicesAux, compressAdj]
  | k, x :: y :: rest, _ => by
    have hlen_pos : 0 < (y :: rest).length := by simp
    have hlast := blockIndicesAux_last (if x = y then k else k + 1) (y :: rest) hlen_pos
    have hsub1 : (x :: y :: rest).length - 1 = rest.length + 1 := rfl
    have hsub2 : (y :: rest).length - 1 = rest.length := rfl
    simp_rw [hsub1]
    simp_rw [hsub2] at hlast
    dsimp only [blockIndicesAux]
    rw [List.getElem_cons_succ, hlast]
    dsimp only [compressAdj]
    have hlen_comp : 0 < (compressAdj (y :: rest)).length := by
      cases h : compressAdj (y :: rest) with
      | nil =>
        have hmem := (compressAdj_mem_iff (y :: rest) y).mpr (by simp)
        rw [h] at hmem; simp at hmem
      | cons _ _ => simp
    split_ifs with hxy
    · rfl
    · rw [List.length_cons]
      omega

private lemma blockIndicesAux_adj :
    ∀ (k : ℕ) (l : List (Fin 5)) (r : ℕ) (hr : r + 1 < l.length),
      (blockIndicesAux k l)[r]'(by rw [blockIndicesAux_length]; omega) ≤
        (blockIndicesAux k l)[r + 1]'(by rw [blockIndicesAux_length]; exact hr) ∧
      (blockIndicesAux k l)[r + 1]'(by rw [blockIndicesAux_length]; exact hr) ≤
        (blockIndicesAux k l)[r]'(by rw [blockIndicesAux_length]; omega) + 1
  | k, [], r, hr => by simp at hr
  | k, [x], r, hr => by simp at hr
  | k, x :: y :: rest, r, hr => by
    cases r with
    | zero =>
      simp only [blockIndicesAux, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [blockIndicesAux_zero]
      split_ifs <;> omega
    | succ r' =>
      simp only [blockIndicesAux, List.getElem_cons_succ]
      exact blockIndicesAux_adj (if x = y then k else k + 1) (y :: rest) r' (by simpa using hr)

private lemma blockIndicesAux_getElem :
    ∀ (k : ℕ) (l : List (Fin 5)) (r : ℕ) (hr : r < l.length),
      let idx := (blockIndicesAux k l)[r]'(by rw [blockIndicesAux_length]; exact hr)
      have hb := blockIndicesAux_bounds k l r hr
      (compressAdj l)[idx - k]'(by dsimp [idx] at hb ⊢; omega) = l[r]'hr
  | k, [], r, hr => by simp at hr
  | k, [x], r, hr => by
    have hr0 : r = 0 := by simp at hr; omega
    subst hr0; simp [blockIndicesAux, compressAdj]
  | k, x :: y :: rest, r, hr => by
    cases r with
    | zero =>
      dsimp only [blockIndicesAux, compressAdj]
      split_ifs with hxy
      · simp only [hxy, ↓reduceIte, List.getElem_cons_zero, Nat.sub_self]
        obtain ⟨zs, hcons⟩ := List.head?_eq_some_iff.mp (compressAdj_head? y rest)
        simp only [hcons, List.getElem_cons_zero]
      · simp only [hxy, ↓reduceIte, List.getElem_cons_zero, Nat.sub_self]
    | succ r' =>
      have hr' : r' < (y :: rest).length := by simpa using hr
      dsimp only [blockIndicesAux, compressAdj]
      split_ifs with hxy
      · simp only [hxy, ↓reduceIte, List.getElem_cons_succ]
        exact blockIndicesAux_getElem k (y :: rest) r' hr'
      · simp only [hxy, ↓reduceIte, List.getElem_cons_succ]
        have ih := blockIndicesAux_getElem (k + 1) (y :: rest) r' hr'
        have hb := blockIndicesAux_bounds (k + 1) (y :: rest) r' hr'
        dsimp only at hb ih ⊢
        have hsub : (blockIndicesAux (k + 1) (y :: rest))[r']'(by rw [blockIndicesAux_length]; exact hr') - k =
            ((blockIndicesAux (k + 1) (y :: rest))[r']'(by rw [blockIndicesAux_length]; exact hr') - (k + 1)) + 1 := by
          omega
        simp_rw [hsub]
        rw [List.getElem_cons_succ]
        exact ih

private lemma blockIndicesAux_mono (k : ℕ) (l : List (Fin 5)) {r₁ r₂ : ℕ}
    (hr1 : r₁ ≤ r₂) (hr2 : r₂ < l.length) :
    (blockIndicesAux k l)[r₁]'(by rw [blockIndicesAux_length]; omega) ≤
      (blockIndicesAux k l)[r₂]'(by rw [blockIndicesAux_length]; exact hr2) := by
  induction r₂ with
  | zero =>
    have hr10 : r₁ = 0 := by omega
    subst hr10; rfl
  | succ m ih =>
    rcases eq_or_lt_of_le hr1 with rfl | hlt
    · rfl
    · have hm_lt : m < l.length := by omega
      exact (ih (by omega) hm_lt).trans (blockIndicesAux_adj k l m hr2).1

private lemma blockIndicesAux_surj_interval (k : ℕ) (l : List (Fin 5))
    {r₁ r₂ : ℕ} (hr1 : r₁ ≤ r₂) (hr2 : r₂ < l.length)
    (j : ℕ)
    (hj1 : (blockIndicesAux k l)[r₁]'(by rw [blockIndicesAux_length]; omega) ≤ j)
    (hj2 : j ≤ (blockIndicesAux k l)[r₂]'(by rw [blockIndicesAux_length]; exact hr2)) :
    ∃ r : ℕ, r₁ ≤ r ∧ r ≤ r₂ ∧
      ∀ (hr : r < l.length), (blockIndicesAux k l)[r]'(by rw [blockIndicesAux_length]; exact hr) = j := by
  induction r₂ with
  | zero =>
    have hr10 : r₁ = 0 := by omega
    subst hr10
    exact ⟨0, le_rfl, le_rfl, fun _ => by omega⟩
  | succ m ih =>
    rcases eq_or_lt_of_le hr1 with rfl | hlt
    · exact ⟨m + 1, le_rfl, le_rfl, fun _ => by omega⟩
    · by_cases hle : j ≤ (blockIndicesAux k l)[m]'(by rw [blockIndicesAux_length]; omega)
      · obtain ⟨r, h1, h2, hr_eq⟩ := ih (by omega) (by omega) hj1 hle
        exact ⟨r, h1, by omega, hr_eq⟩
      · have hadj := blockIndicesAux_adj k l m hr2
        exact ⟨m + 1, by omega, le_rfl, fun _ => by omega⟩

private lemma non_hull_slab_constraint (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    {n : ℕ} (hn_eq : hullBlockCount P = n) (hn2 : 2 ≤ n) :
    let h := (topTiePts P).card + 1
    let l := List.ofFn (hullColors P)
    let b := fun r : Fin h => (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, List.length_ofFn]; exact r.isLt)
    ∀ a : Fin 10, (∀ r, hullIdx P r ≠ a) →
      ∃ j : ℕ, j < n - 1 ∧
        ∀ (z : ℝ × ℝ) (hz : InOmega z) (ha_dot : 1 < dot2 (P.vec a) z)
          (r₁ r₂ : Fin h),
          (∀ r, 1 < dot2 (hullVerts P r) z ↔ r₁ ≤ r ∧ r ≤ r₂) →
          (b r₁ ≤ j + 1 ∧ j ≤ b r₂) := by
  intro h l b a ha_not
  have hlen_l : l.length = h := List.length_ofFn
  have hcs_len : (compressedColors P).length = n := hn_eq
  have hb_lt : ∀ r : Fin h, b r < n := fun r => by
    have := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    change b r < 0 + (compressedColors P).length at this
    omega
  have hb0 : b ⟨0, by omega⟩ = 0 :=
    blockIndicesAux_head 0 l (by rw [hlen_l]; omega)
  have hblast : b ⟨h - 1, by omega⟩ = n - 1 := by
    have hl_pos : 0 < l.length := by rw [hlen_l]; omega
    have hlast := blockIndicesAux_last 0 l hl_pos
    dsimp [b]
    have hidx_eq : h - 1 = l.length - 1 := by omega
    have hval : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) =
        (blockIndicesAux 0 l)[l.length - 1]'(by rw [blockIndicesAux_length]; omega) := by
      congr 1
    rw [hval, hlast]
    change 0 + (compressedColors P).length - 1 = n - 1
    omega
  rcases hull_domination P hgp htop a ha_not with ⟨_, hdom⟩ | ⟨_, hdom⟩ | ⟨r, hr, _, _, hdom⟩
  · refine ⟨0, by omega, fun z hz ha_dot r₁ r₂ hiff => ?_⟩
    have h0_act := (hiff ⟨0, by omega⟩).mp (hdom z hz (le_of_lt ha_dot))
    have hr1_0 : r₁ = ⟨0, by omega⟩ := Fin.ext (Nat.le_zero.mp h0_act.1)
    rw [hr1_0, hb0]
    exact ⟨by omega, Nat.zero_le _⟩
  · refine ⟨n - 2, by omega, fun z hz ha_dot r₁ r₂ hiff => ?_⟩
    have hL_act := (hiff ⟨h - 1, by omega⟩).mp (hdom z hz (le_of_lt ha_dot))
    have hr2_L : r₂ = ⟨h - 1, by omega⟩ :=
      Fin.ext (le_antisymm (Nat.le_pred_of_lt r₂.isLt) hL_act.2)
    rw [hr2_L, hblast]
    exact ⟨by have := hb_lt r₁; omega, by omega⟩
  · let r' : Fin h := ⟨r.val + 1, hr⟩
    have hadj := blockIndicesAux_adj 0 l r.val (by rw [hlen_l]; exact hr)
    change b r ≤ b r' ∧ b r' ≤ b r + 1 at hadj
    refine ⟨min (b r) (n - 2), by omega, fun z hz ha_dot r₁ r₂ hiff => ?_⟩
    rcases hdom z hz (le_of_lt ha_dot) with h1 | h2
    · have hact := (hiff r).mp h1
      have hm1 := blockIndicesAux_mono 0 l hact.1 (by rw [hlen_l]; exact r.isLt)
      have hm2 := blockIndicesAux_mono 0 l hact.2 (by rw [hlen_l]; exact r₂.isLt)
      change b r₁ ≤ b r at hm1
      change b r ≤ b r₂ at hm2
      have := hb_lt r
      rcases le_or_gt (b r) (n - 2) with hle | hgt
      · rw [min_eq_left hle]; exact ⟨by omega, hm2⟩
      · rw [min_eq_right (le_of_lt hgt)]; exact ⟨by have := hb_lt r₁; omega, by omega⟩
    · have hact := (hiff r').mp h2
      have hm1 := blockIndicesAux_mono 0 l hact.1 (by rw [hlen_l]; exact r'.isLt)
      have hm2 := blockIndicesAux_mono 0 l hact.2 (by rw [hlen_l]; exact r₂.isLt)
      change b r₁ ≤ b r' at hm1
      change b r' ≤ b r₂ at hm2
      have := hb_lt r'
      rcases le_or_gt (b r) (n - 2) with hle | hgt
      · rw [min_eq_left hle]; exact ⟨by omega, by omega⟩
      · rw [min_eq_right (le_of_lt hgt)]
        have hbr_eq : b r = n - 1 := by have := hb_lt r; omega
        have hbr'_eq : b r' = n - 1 := by omega
        exact ⟨by have := hb_lt r₁; omega, by omega⟩

private lemma not_mem_pureHullPairs_of_no_adj (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    {n : ℕ} (hn_eq : hullBlockCount P = n) (c₁ c₂ : Fin 5) (hne : c₁ ≠ c₂)
    (hno_adj : ∀ k : ℕ, (hk : k + 1 < n) →
      ({(compressedColors P)[k]'(by have : (compressedColors P).length = n := hn_eq; omega),
        (compressedColors P)[k + 1]'(by have : (compressedColors P).length = n := hn_eq; omega)} : Finset (Fin 5)) ≠ {c₁, c₂}) :
    ({c₁, c₂} : Finset (Fin 5)) ∉ pureHullPairs P := by
  intro hmem
  have hlen_cs : (compressedColors P).length = n := hn_eq
  have hcard : ({c₁, c₂} : Finset (Fin 5)).card = 2 := Finset.card_pair hne
  obtain ⟨r₁, r₂, hr12, himg⟩ := (pure_hull_pairs_eq P hgp htop {c₁, c₂} hcard).mp hmem
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  have hlen_l : l.length = h := List.length_ofFn
  let S_diff : Finset (Fin h) := Finset.univ.filter fun r : Fin h =>
    r₁ < r ∧ r ≤ r₂ ∧ hullColors P r ≠ hullColors P r₁
  have hS_diff_ne : S_diff.Nonempty := by
    by_contra hnone
    rw [Finset.not_nonempty_iff_eq_empty] at hnone
    have hsub : (Finset.univ.filter (fun r : Fin h => r₁ ≤ r ∧ r ≤ r₂)).image (hullColors P) ⊆
        {hullColors P r₁} := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
      have hrb := (Finset.mem_filter.mp hr).2
      rw [Finset.mem_singleton]
      rcases eq_or_lt_of_le hrb.1 with rfl | hlt
      · rfl
      · by_contra hne_r
        have : r ∈ S_diff := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hrb.2, hne_r⟩
        rw [hnone] at this
        simp at this
    have hcard_le := Finset.card_le_card hsub
    rw [himg, hcard, Finset.card_singleton] at hcard_le
    omega
  let r_min := S_diff.min' hS_diff_ne
  have hr_min_mem := S_diff.min'_mem hS_diff_ne
  have hr_min_spec := (Finset.mem_filter.mp hr_min_mem).2
  let r_prev : Fin h := ⟨r_min.val - 1, by omega⟩
  have hr1_le_prev : r₁ ≤ r_prev := by
    change r₁.val ≤ r_min.val - 1
    have : r₁.val < r_min.val := hr_min_spec.1
    omega
  have hr_prev_lt : r_prev < r_min := by
    change r_min.val - 1 < r_min.val
    have : r₁.val < r_min.val := hr_min_spec.1
    omega
  have hr_prev_le2 : r_prev ≤ r₂ := le_trans (le_of_lt hr_prev_lt) hr_min_spec.2.1
  have hcol_prev : hullColors P r_prev = hullColors P r₁ := by
    rcases eq_or_lt_of_le hr1_le_prev with heq | hlt
    · rw [heq]
    · by_contra hne_p
      have hmem_p : r_prev ∈ S_diff := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hr_prev_le2, hne_p⟩
      exact absurd (S_diff.min'_le r_prev hmem_p) (not_le_of_gt hr_prev_lt)
  have hr_min_eq : r_prev.val + 1 = r_min.val := by
    dsimp [r_prev]; have : r₁.val < r_min.val := hr_min_spec.1; omega
  have hadj := blockIndicesAux_adj 0 l r_prev.val (by rw [hlen_l, hr_min_eq]; exact r_min.isLt)
  have hget_p := blockIndicesAux_getElem 0 l r_prev.val (by rw [hlen_l]; exact r_prev.isLt)
  have hget_m := blockIndicesAux_getElem 0 l r_min.val (by rw [hlen_l]; exact r_min.isLt)
  have hbp_lt : (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt) < n := by
    have := (blockIndicesAux_bounds 0 l r_prev.val (by rw [hlen_l]; exact r_prev.isLt)).2
    change _ < 0 + (compressedColors P).length at this
    rw [hlen_cs] at this; omega
  have hbm_lt : (blockIndicesAux 0 l)[r_min.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_min.isLt) < n := by
    have := (blockIndicesAux_bounds 0 l r_min.val (by rw [hlen_l]; exact r_min.isLt)).2
    change _ < 0 + (compressedColors P).length at this
    rw [hlen_cs] at this; omega
  have hl_p : l[r_prev.val]'(by rw [hlen_l]; exact r_prev.isLt) = hullColors P r_prev := by
    dsimp [l]; rw [List.getElem_ofFn]
  have hl_m : l[r_min.val]'(by rw [hlen_l]; exact r_min.isLt) = hullColors P r_min := by
    dsimp [l]; rw [List.getElem_ofFn]
  have hb_step :
      (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt) + 1 =
      (blockIndicesAux 0 l)[r_min.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_min.isLt) := by
    have hadj' :
        (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt) ≤
        (blockIndicesAux 0 l)[r_min.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_min.isLt) ∧
        (blockIndicesAux 0 l)[r_min.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_min.isLt) ≤
        (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt) + 1 := by
      simpa [hr_min_eq] using hadj
    by_contra hne_b
    have hbeq :
        (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt) =
        (blockIndicesAux 0 l)[r_min.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_min.isLt) := by
      omega
    dsimp only at hget_p hget_m
    simp only [Nat.sub_zero, hl_p, hl_m] at hget_p hget_m
    have h1 : hullColors P r_prev = hullColors P r_min := by
      rw [← hget_p, ← hget_m]
      congr 1
    exact hr_min_spec.2.2 (hcol_prev.symm.trans h1).symm
  let k := (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt)
  have hk_lt : k + 1 < n := by change k + 1 < n; rw [hb_step]; exact hbm_lt
  apply hno_adj k hk_lt
  have hidx_p : (blockIndicesAux 0 l)[r_prev.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_prev.isLt) - 0 = k :=
    Nat.sub_zero _
  have hidx_m : (blockIndicesAux 0 l)[r_min.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r_min.isLt) - 0 = k + 1 := by
    rw [Nat.sub_zero]; exact hb_step.symm
  have hcs_def : compressedColors P = compressAdj l := rfl
  have hcs1 : (compressedColors P)[k]'(by rw [hlen_cs]; exact Nat.lt_of_succ_lt hk_lt) = hullColors P r₁ := by
    change (compressAdj l)[k]'(by rw [← hcs_def, hlen_cs]; exact Nat.lt_of_succ_lt hk_lt) = hullColors P r₁
    exact (list_getElem_eq_of_idx (compressAdj l) _ _ hidx_p).trans (hget_p.trans (hl_p.trans hcol_prev))
  have hcs2 : (compressedColors P)[k + 1]'(by rw [hlen_cs]; exact hk_lt) = hullColors P r_min := by
    change (compressAdj l)[k + 1]'(by rw [← hcs_def, hlen_cs]; exact hk_lt) = hullColors P r_min
    exact (list_getElem_eq_of_idx (compressAdj l) _ _ hidx_m).trans (hget_m.trans hl_m)
  have hmem1 : hullColors P r₁ ∈ ({c₁, c₂} : Finset (Fin 5)) := by
    rw [← himg]
    exact Finset.mem_image.mpr ⟨r₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hr12⟩, rfl⟩
  have hmem2 : hullColors P r_min ∈ ({c₁, c₂} : Finset (Fin 5)) := by
    rw [← himg]
    exact Finset.mem_image.mpr ⟨r_min, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt hr_min_spec.1, hr_min_spec.2.1⟩, rfl⟩
  have hpair_sub : ({hullColors P r₁, hullColors P r_min} : Finset (Fin 5)) = {c₁, c₂} := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · rw [hcard, Finset.card_pair hr_min_spec.2.2.symm]
  rw [hcs1, hcs2]
  exact hpair_sub

private lemma island_rule_contradiction (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    {n : ℕ} (hn_eq : hullBlockCount P = n) (hn2 : 2 ≤ n)
    (S : Finset (Fin 5)) (z : ℝ × ℝ) (hz : InOmega z)
    (hreal : RealizesDualMask P (fun i => !decide (i ∈ S)) z)
    (r₁ r₂ : Fin ((topTiePts P).card + 1)) (hr12 : r₁ ≤ r₂)
    (hdot_iff : ∀ r, 1 < dot2 (hullVerts P r) z ↔ r₁ ≤ r ∧ r ≤ r₂)
    (c₁ c₂ : Fin 5) (hne : c₁ ≠ c₂) (hnot_pure : ({c₁, c₂} : Finset (Fin 5)) ∉ pureHullPairs P)
    (hc1S : c₁ ∈ S) (hc2S : c₂ ∈ S)
    (hno_nhd : ∀ k : Fin n,
      (blockIndicesAux 0 (List.ofFn (hullColors P)))[r₁.val]'(by rw [blockIndicesAux_length, List.length_ofFn]; exact r₁.isLt) ≤ k.val + 1 →
      k.val ≤ (blockIndicesAux 0 (List.ofFn (hullColors P)))[r₂.val]'(by rw [blockIndicesAux_length, List.length_ofFn]; exact r₂.isLt) + 1 →
      (compressedColors P)[k.val]'(by have : (compressedColors P).length = n := hn_eq; omega) ≠ c₁ ∧
      (compressedColors P)[k.val]'(by have : (compressedColors P).length = n := hn_eq; omega) ≠ c₂) :
    False := by
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  have hlen_l : l.length = h := List.length_ofFn
  have hlen_cs : (compressedColors P).length = n := hn_eq
  let b : Fin h → ℕ := fun r =>
    (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt)
  let colAt : Fin n → Fin 5 := fun k => (compressedColors P)[k.val]'(by rw [hlen_cs]; exact k.isLt)
  let T : Finset (Fin 5) := {c₁, c₂}
  have hT_card : T.card = 2 := Finset.card_pair hne
  have hT_ne : T.Nonempty := ⟨c₁, by simp [T]⟩
  obtain ⟨z', hz', hreal'⟩ := h_shat (fun i => !decide (i ∈ T))
  obtain ⟨a, ha_not, ha_inT, ha_dot', _⟩ :=
    interior_assisted_pairs P hgp htop T hT_card hnot_pure z' hz' hreal'
  obtain ⟨r'₁, r'₂, hr'12, hdot'_iff, hcol'_in⟩ :=
    dual_island_rule P hgp htop T hT_ne z' hz' hreal'
  have ha_cases : vecColor a = c₁ ∨ vecColor a = c₂ := by
    simpa [T, Finset.mem_insert, Finset.mem_singleton] using ha_inT
  have ha_S : vecColor a ∈ S := by rcases ha_cases with h | h <;> rw [h] <;> assumption
  have ha_no_nhd : ∀ k : Fin n, b r₁ ≤ k.val + 1 → k.val ≤ b r₂ + 1 → colAt k ≠ vecColor a := by
    intro k hk1 hk2
    have hnk := hno_nhd k hk1 hk2
    rcases ha_cases with h | h <;> rw [h] <;> [exact hnk.1; exact hnk.2]
  have hno_hull_act : ∀ r : Fin h, hullColors P r = vecColor a → ¬ (1 < dot2 (hullVerts P r) z) := by
    intro r hcr hact
    have hr_int := (hdot_iff r).mp hact
    have hb1 : b r₁ ≤ b r := blockIndicesAux_mono 0 l hr_int.1 (by rw [hlen_l]; exact r.isLt)
    have hb2 : b r ≤ b r₂ := blockIndicesAux_mono 0 l hr_int.2 (by rw [hlen_l]; exact r₂.isLt)
    have hbr_lt : b r < n := by
      have := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
      change b r < 0 + (compressedColors P).length at this
      rw [hlen_cs] at this; omega
    have hget := blockIndicesAux_getElem 0 l r.val (by rw [hlen_l]; exact r.isLt)
    have hl_r : l[r.val]'(by rw [hlen_l]; exact r.isLt) = hullColors P r := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hcol_eq : colAt ⟨b r, hbr_lt⟩ = vecColor a := by
      dsimp [colAt, compressedColors, b]
      exact (list_getElem_eq_of_idx (compressAdj l) _ _ (Nat.sub_zero _)).trans (hget.trans (hl_r.trans hcr))
    exact ha_no_nhd ⟨b r, hbr_lt⟩ (by dsimp; omega) (by dsimp; omega) hcol_eq
  obtain ⟨a', ha'_col, ha'_dot⟩ := (realizesDualMask_ext_iff P S z hreal (vecColor a)).mp ha_S
  have ha'_not : ∀ r, hullIdx P r ≠ a' := by
    intro r hr
    apply hno_hull_act r (by unfold hullColors; rw [hr, ha'_col])
    unfold hullVerts; rw [hr]; exact ha'_dot
  have h5col := hull_five_colors P hgp htop h_shat
  have ha'_eq : a' = a := h5col.2.2.2 a' a ha'_not ha_not ha'_col
  have ha_dot : 1 < dot2 (P.vec a) z := ha'_eq ▸ ha'_dot
  obtain ⟨j, hj_lt, hj_spec⟩ := non_hull_slab_constraint P hgp htop hn_eq hn2 a ha_not
  have hslab_z := hj_spec z hz ha_dot r₁ r₂ hdot_iff
  have hslab_z' := hj_spec z' hz' ha_dot' r'₁ r'₂ hdot'_iff
  change b r₁ ≤ j + 1 ∧ j ≤ b r₂ at hslab_z
  change b r'₁ ≤ j + 1 ∧ j ≤ b r'₂ at hslab_z'
  have hb'_mono : b r'₁ ≤ b r'₂ := blockIndicesAux_mono 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt)
  have hcs_def : compressedColors P = compressAdj l := rfl
  have hit : ∃ k : Fin n, b r₁ ≤ k.val + 1 ∧ k.val ≤ b r₂ + 1 ∧ colAt k ∈ T := by
    by_cases hj1 : b r'₁ ≤ j
    · obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt) j hj1 hslab_z'.2
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ T := hcol'_in ⟨r, by omega⟩ hr_lo hr_hi
      have hget := blockIndicesAux_getElem 0 l r (by rw [hlen_l]; omega)
      have hl_r : l[r]'(by rw [hlen_l]; omega) = hullColors P ⟨r, by omega⟩ := by
        dsimp [l]; rw [List.getElem_ofFn]
      refine ⟨⟨j, by omega⟩, by dsimp; omega, by dsimp; omega, ?_⟩
      change (compressAdj l)[j]'(by rw [← hcs_def, hlen_cs]; omega) ∈ T
      have hget' : (compressAdj l)[j]'(by rw [← hcs_def, hlen_cs]; omega) = l[r]'(by rw [hlen_l]; omega) :=
        (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hr_eq (by rw [hlen_l]; omega))).trans hget
      rw [hget', hl_r]; exact hcol_r
    · have hj2 : b r'₁ = j + 1 := by omega
      dsimp only [b] at hj2 hb'_mono hslab_z'
      obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt) (j + 1) (le_of_eq hj2)
          (le_trans (le_of_eq hj2.symm) hb'_mono)
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ T := hcol'_in ⟨r, by omega⟩ hr_lo hr_hi
      have hget := blockIndicesAux_getElem 0 l r (by rw [hlen_l]; omega)
      have hl_r : l[r]'(by rw [hlen_l]; omega) = hullColors P ⟨r, by omega⟩ := by
        dsimp [l]; rw [List.getElem_ofFn]
      refine ⟨⟨j + 1, by omega⟩, by dsimp; omega, by dsimp; omega, ?_⟩
      change (compressAdj l)[j + 1]'(by rw [← hcs_def, hlen_cs]; omega) ∈ T
      have hget' : (compressAdj l)[j + 1]'(by rw [← hcs_def, hlen_cs]; omega) = l[r]'(by rw [hlen_l]; omega) :=
        (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hr_eq (by rw [hlen_l]; omega))).trans hget
      rw [hget', hl_r]; exact hcol_r
  obtain ⟨k, hk1, hk2, hkT⟩ := hit
  have hnk := hno_nhd k hk1 hk2
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hkT
  rcases hkT with h | h <;> [exact hnk.1 h; exact hnk.2 h]

private lemma n5_island_rule_fin5 (a b : Fin 5) (hab : a ≤ b)
    (h1 : ¬ (a.val ≤ 1 ∧ 1 ≤ b.val))
    (h3 : ¬ (a.val ≤ 3 ∧ 3 ≤ b.val)) :
    ∃ u v : Fin 5,
      (u = 0 ∨ u = 2 ∨ u = 4) ∧
      (v = 0 ∨ v = 2 ∨ v = 4) ∧
      u ≠ v ∧
      u.val + 1 ≠ v.val ∧ v.val + 1 ≠ u.val ∧
      ¬ (a.val ≤ u.val + 1 ∧ u.val ≤ b.val + 1) ∧
      ¬ (a.val ≤ v.val + 1 ∧ v.val ≤ b.val + 1) := by
  revert a b; decide

/-- Elimination of `n_Ω = 5` via the Dual Island Rule on `{c₁, c₃, c₅}`. -/
theorem elim_n5 (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z) :
    hullBlockCount P ≠ 5 := by
  intro hn5
  have h5col := hull_five_colors P hgp htop h_shat
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  let cs := compressedColors P
  have hcs_len : cs.length = 5 := hn5
  have hlen_l : l.length = h := List.length_ofFn
  have hcs_def : compressedColors P = compressAdj l := rfl
  let colAt : Fin 5 → Fin 5 := fun k => cs[k.val]'(by rw [hcs_len]; exact k.isLt)
  have hcolAt_surj : Function.Surjective colAt := by
    intro i
    obtain ⟨r, hr⟩ := h5col.1 i
    have hb := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    let k : Fin 5 := ⟨(blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt),
      by change _ < 0 + cs.length at hb; omega⟩
    refine ⟨k, ?_⟩
    have hget := blockIndicesAux_getElem 0 l r.val (by rw [hlen_l]; exact r.isLt)
    have hl_r : l[r.val]'(by rw [hlen_l]; exact r.isLt) = hullColors P r := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hcol_eq : colAt k = hullColors P r := by
      dsimp [colAt, k, cs, compressedColors]
      exact (list_getElem_eq_of_idx (compressAdj l) _ _ (Nat.sub_zero _)).trans (hget.trans hl_r)
    rw [hcol_eq, hr]
  have hcolAt_inj : Function.Injective colAt := Finite.injective_iff_surjective.mpr hcolAt_surj
  let φ : Fin 5 ≃ Fin 5 := Equiv.ofBijective colAt ⟨hcolAt_inj, hcolAt_surj⟩
  let S : Finset (Fin 5) := {φ 0, φ 2, φ 4}
  have hS_ne : S.Nonempty := ⟨φ 0, by simp [S]⟩
  obtain ⟨z, hz, hreal⟩ := h_shat (fun i => !decide (i ∈ S))
  obtain ⟨r₁, r₂, hr12, hdot_iff, hcol_in⟩ := dual_island_rule P hgp htop S hS_ne z hz hreal
  let b : Fin h → ℕ := fun r =>
    (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt)
  have hb_lt : ∀ r : Fin h, b r < 5 := fun r => by
    have := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    change b r < 0 + cs.length at this
    rw [hcs_len] at this; omega
  have hb_mono : b r₁ ≤ b r₂ := blockIndicesAux_mono 0 l hr12 (by rw [hlen_l]; exact r₂.isLt)
  let α : Fin 5 := ⟨b r₁, hb_lt r₁⟩
  let β : Fin 5 := ⟨b r₂, hb_lt r₂⟩
  have hmem_024 : ∀ k : Fin 5, α ≤ k → k ≤ β → k = 0 ∨ k = 2 ∨ k = 4 := by
    intro k hk1 hk2
    obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
      blockIndicesAux_surj_interval 0 l hr12 (by rw [hlen_l]; exact r₂.isLt) k.val hk1 hk2
    have hcol_r : hullColors P ⟨r, by omega⟩ ∈ S := hcol_in ⟨r, by omega⟩ hr_lo hr_hi
    have hget := blockIndicesAux_getElem 0 l r (by rw [hlen_l]; omega)
    have hl_r : l[r]'(by rw [hlen_l]; omega) = hullColors P ⟨r, by omega⟩ := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hφ_k : φ k = hullColors P ⟨r, by omega⟩ := by
      change colAt k = hullColors P ⟨r, by omega⟩
      dsimp [colAt, cs, compressedColors]
      exact (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hr_eq (by rw [hlen_l]; omega))).trans
        (hget.trans hl_r)
    rw [← hφ_k] at hcol_r
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hcol_r
    rcases hcol_r with h0 | h2 | h4
    · exact Or.inl (φ.injective h0)
    · exact Or.inr (Or.inl (φ.injective h2))
    · exact Or.inr (Or.inr (φ.injective h4))
  have hno1 : ¬ (α.val ≤ 1 ∧ 1 ≤ β.val) := by
    rintro ⟨h1a, h1b⟩
    have hne1 : (1 : Fin 5) ≠ 0 ∧ (1 : Fin 5) ≠ 2 ∧ (1 : Fin 5) ≠ 4 := by decide
    rcases hmem_024 1 h1a h1b with h | h | h
    · exact hne1.1 h
    · exact hne1.2.1 h
    · exact hne1.2.2 h
  have hno3 : ¬ (α.val ≤ 3 ∧ 3 ≤ β.val) := by
    rintro ⟨h3a, h3b⟩
    have hne3 : (3 : Fin 5) ≠ 0 ∧ (3 : Fin 5) ≠ 2 ∧ (3 : Fin 5) ≠ 4 := by decide
    rcases hmem_024 3 h3a h3b with h | h | h
    · exact hne3.1 h
    · exact hne3.2.1 h
    · exact hne3.2.2 h
  obtain ⟨u, v, huS, hvS, huv, huv1, hvu1, hu_nhd, hv_nhd⟩ :=
    n5_island_rule_fin5 α β hb_mono hno1 hno3
  have hu_mem : φ u ∈ S := by
    rcases huS with rfl | rfl | rfl <;> simp [S]
  have hv_mem : φ v ∈ S := by
    rcases hvS with rfl | rfl | rfl <;> simp [S]
  refine island_rule_contradiction P hgp htop h_shat hn5 (by omega) S z hz hreal r₁ r₂ hr12 hdot_iff
    (φ u) (φ v) (φ.injective.ne huv) ?_ hu_mem hv_mem ?_
  · refine not_mem_pureHullPairs_of_no_adj P hgp htop hn5 (φ u) (φ v) (φ.injective.ne huv) ?_
    intro k hk heq
    have h1 : (compressedColors P)[k]'(by rw [hcs_len]; exact Nat.lt_of_succ_lt hk) = φ ⟨k, by omega⟩ := rfl
    have h2 : (compressedColors P)[k + 1]'(by rw [hcs_len]; exact hk) = φ ⟨k + 1, hk⟩ := rfl
    rw [h1, h2] at heq
    have hm1 : φ u ∈ ({φ ⟨k, by omega⟩, φ ⟨k + 1, hk⟩} : Finset (Fin 5)) := by rw [heq]; simp
    have hm2 : φ v ∈ ({φ ⟨k, by omega⟩, φ ⟨k + 1, hk⟩} : Finset (Fin 5)) := by rw [heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with hmu | hmu <;> rcases hm2 with hmv | hmv
    · exact huv (φ.injective (hmu.trans hmv.symm))
    · have hu_k := congrArg Fin.val (φ.injective hmu)
      have hv_k := congrArg Fin.val (φ.injective hmv)
      dsimp at hu_k hv_k
      exact huv1 (by omega)
    · have hu_k := congrArg Fin.val (φ.injective hmu)
      have hv_k := congrArg Fin.val (φ.injective hmv)
      dsimp at hu_k hv_k
      exact hvu1 (by omega)
    · exact huv (φ.injective (hmu.trans hmv.symm))
  · intro k hk1 hk2
    have hk_eq : (compressedColors P)[k.val]'(by rw [hcs_len]; exact k.isLt) = φ k := rfl
    rw [hk_eq]
    refine ⟨φ.injective.ne ?_, φ.injective.ne ?_⟩
    · intro hku; subst hku; exact hu_nhd ⟨hk1, hk2⟩
    · intro hkv; subst hkv; exact hv_nhd ⟨hk1, hk2⟩

private lemma word6_cases (i₁ i₂ : Fin 6) (hi12 : i₁ < i₂) (hi_gap : i₁.val + 2 ≤ i₂.val)
    (hi_not05 : (i₁.val, i₂.val) ≠ (0, 5)) :
    let rem := (List.finRange 6).filter fun k => k != i₁ && k != i₂
    (i₁ = 0 ∧ i₂ = 2 ∧ rem = [1, 3, 4, 5]) ∨
    (i₁ = 0 ∧ i₂ = 3 ∧ rem = [1, 2, 4, 5]) ∨
    (i₁ = 0 ∧ i₂ = 4 ∧ rem = [1, 2, 3, 5]) ∨
    (i₁ = 1 ∧ i₂ = 3 ∧ rem = [0, 2, 4, 5]) ∨
    (i₁ = 1 ∧ i₂ = 4 ∧ rem = [0, 2, 3, 5]) ∨
    (i₁ = 1 ∧ i₂ = 5 ∧ rem = [0, 2, 3, 4]) ∨
    (i₁ = 2 ∧ i₂ = 4 ∧ rem = [0, 1, 3, 5]) ∨
    (i₁ = 2 ∧ i₂ = 5 ∧ rem = [0, 1, 3, 4]) ∨
    (i₁ = 3 ∧ i₂ = 5 ∧ rem = [0, 1, 2, 4]) := by
  revert i₁ i₂; decide

private def checkIsland6Word (w : Fin 6 → Fin 5) (S₀ : List (Fin 5)) : Bool :=
  !(S₀.isEmpty) &&
  (List.finRange 6).all fun a =>
    (List.finRange 6).all fun b =>
      if !(decide (a ≤ b)) then true
      else if !((List.finRange 6).all fun k => if decide (a ≤ k ∧ k ≤ b) then S₀.contains (w k) else true) then true
      else
        S₀.any fun c₁ => S₀.any fun c₂ =>
          decide (c₁ ≠ c₂) &&
          (List.finRange 5).all (fun k =>
            !((w k.castSucc == c₁ && w k.succ == c₂) || (w k.castSucc == c₂ && w k.succ == c₁))) &&
          (List.finRange 6).all (fun k =>
            if decide (a.val ≤ k.val + 1 ∧ k.val ≤ b.val + 1) then w k != c₁ && w k != c₂ else true)

private lemma elim_n6_word_island (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hn6 : hullBlockCount P = 6) (φ : Fin 5 ≃ Fin 5)
    (w₀ : Fin 6 → Fin 5) (S₀ : List (Fin 5))
    (hw : ∀ k : Fin 6, φ.symm ((compressedColors P)[k.val]'(by have : (compressedColors P).length = 6 := hn6; omega)) = w₀ k)
    (hcheck : checkIsland6Word w₀ S₀ = true) : False := by
  unfold checkIsland6Word at hcheck
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.mem_finRange, true_implies] at hcheck
  rcases hcheck with ⟨hS_ne0, hblocks⟩
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  have hlen_l : l.length = h := List.length_ofFn
  let S : Finset (Fin 5) := S₀.toFinset.image φ
  have hS_ne : S.Nonempty := by
    cases S₀ with
    | nil => simp at hS_ne0
    | cons c cs => exact ⟨φ c, Finset.mem_image.mpr ⟨c, by simp, rfl⟩⟩
  obtain ⟨z, hz, hreal⟩ := h_shat (fun i => !decide (i ∈ S))
  obtain ⟨r₁, r₂, hr12, hdot_iff, hcol_in⟩ := dual_island_rule P hgp htop S hS_ne z hz hreal
  have hlen_cs : (compressedColors P).length = 6 := hn6
  let b : Fin h → ℕ := fun r =>
    (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt)
  have hb_lt : ∀ r : Fin h, b r < 6 := fun r => by
    have := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    change b r < 0 + (compressedColors P).length at this
    rw [hlen_cs] at this; omega
  have hb_mono : b r₁ ≤ b r₂ := blockIndicesAux_mono 0 l hr12 (by rw [hlen_l]; exact r₂.isLt)
  let α : Fin 6 := ⟨b r₁, hb_lt r₁⟩
  let β : Fin 6 := ⟨b r₂, hb_lt r₂⟩
  have hαβ : α ≤ β := hb_mono
  have hsub_ok : ((List.finRange 6).all fun k =>
      if decide (α ≤ k ∧ k ≤ β) then S₀.contains (w₀ k) else true) = true := by
    rw [List.all_eq_true]
    intro k _
    by_cases hk : α ≤ k ∧ k ≤ β
    · rw [if_pos (decide_eq_true hk), List.contains_eq_mem, decide_eq_true_eq]
      obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr12 (by rw [hlen_l]; exact r₂.isLt) k.val hk.1 hk.2
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ S := hcol_in ⟨r, by omega⟩ hr_lo hr_hi
      have hget := blockIndicesAux_getElem 0 l r (by rw [hlen_l]; omega)
      have hl_r : l[r]'(by rw [hlen_l]; omega) = hullColors P ⟨r, by omega⟩ := by
        dsimp [l]; rw [List.getElem_ofFn]
      have hw_k : φ (w₀ k) = hullColors P ⟨r, by omega⟩ := by
        rw [← hw k, Equiv.apply_symm_apply]
        exact (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hr_eq (by rw [hlen_l]; omega))).trans (hget.trans hl_r)
      rw [← hw_k] at hcol_r
      obtain ⟨c, hc_mem, hc_eq⟩ := Finset.mem_image.mp hcol_r
      rw [← φ.injective hc_eq]
      exact List.mem_toFinset.mp hc_mem
    · simp [hk]
  have hstep := hblocks α β
  simp only [decide_eq_true hαβ, hsub_ok, Bool.true_eq_false, ↓reduceIte] at hstep
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hstep
  obtain ⟨c₁, hc1_mem, c₂, hc2_mem, ⟨⟨hc_ne, hno_adj⟩, hno_nhd⟩⟩ := hstep
  refine island_rule_contradiction P hgp htop h_shat hn6 (by omega) S z hz hreal r₁ r₂ hr12 hdot_iff
    (φ c₁) (φ c₂) (φ.injective.ne hc_ne) ?_
    (Finset.mem_image.mpr ⟨c₁, List.mem_toFinset.mpr hc1_mem, rfl⟩)
    (Finset.mem_image.mpr ⟨c₂, List.mem_toFinset.mpr hc2_mem, rfl⟩) ?_
  · refine not_mem_pureHullPairs_of_no_adj P hgp htop hn6 (φ c₁) (φ c₂) (φ.injective.ne hc_ne) ?_
    intro k hk heq
    let kf : Fin 5 := ⟨k, by omega⟩
    have h1 : (compressedColors P)[k]'(by rw [hlen_cs]; exact Nat.lt_of_succ_lt hk) = φ (w₀ kf.castSucc) := by
      rw [← hw kf.castSucc, Equiv.apply_symm_apply]; rfl
    have h2 : (compressedColors P)[k + 1]'(by rw [hlen_cs]; exact hk) = φ (w₀ kf.succ) := by
      rw [← hw kf.succ, Equiv.apply_symm_apply]; rfl
    rw [h1, h2] at heq
    have hm1 : φ (w₀ kf.castSucc) ∈ ({φ c₁, φ c₂} : Finset (Fin 5)) := by rw [← heq]; simp
    have hm2 : φ (w₀ kf.succ) ∈ ({φ c₁, φ c₂} : Finset (Fin 5)) := by rw [← heq]; simp
    have ha := hno_adj kf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with hm1 | hm1 <;> rcases hm2 with hm2 | hm2
    · have : ({φ (w₀ kf.castSucc), φ (w₀ kf.succ)} : Finset (Fin 5)) = {φ c₁} := by
        rw [hm1, hm2]; simp
      have hsub : φ c₂ ∈ ({φ c₁} : Finset (Fin 5)) := by rw [← this, heq]; simp
      simp only [Finset.mem_singleton] at hsub
      exact hc_ne (φ.injective hsub.symm)
    · rcases ha.1 with h | h <;> exact h (φ.injective (by assumption))
    · rcases ha.2 with h | h <;> exact h (φ.injective (by assumption))
    · have : ({φ (w₀ kf.castSucc), φ (w₀ kf.succ)} : Finset (Fin 5)) = {φ c₂} := by
        rw [hm1, hm2]; simp
      have hsub : φ c₁ ∈ ({φ c₂} : Finset (Fin 5)) := by rw [← this, heq]; simp
      simp only [Finset.mem_singleton] at hsub
      exact hc_ne (φ.injective hsub)
  · intro k hk1 hk2
    let kf : Fin 6 := ⟨k.val, k.isLt⟩
    have hwk := hno_nhd kf
    have hcond : α.val ≤ kf.val + 1 ∧ kf.val ≤ β.val + 1 := ⟨hk1, hk2⟩
    rw [if_pos hcond] at hwk
    simp only [Bool.and_eq_true, bne_iff_ne] at hwk
    have hk_eq : (compressedColors P)[k.val]'(by rw [hlen_cs]; exact k.isLt) = φ (w₀ kf) := by
      rw [← hw kf, Equiv.apply_symm_apply]
    rw [hk_eq]
    exact ⟨φ.injective.ne hwk.1, φ.injective.ne hwk.2⟩


private lemma compressAdj_adj_ne :
    ∀ (l : List (Fin 5)) (k : ℕ) (hk : k + 1 < (compressAdj l).length),
      (compressAdj l)[k]'(Nat.lt_of_succ_lt hk) ≠ (compressAdj l)[k + 1]'hk := by
  intro l k hk
  obtain ⟨m, hm, h1, h2, hne⟩ := compressAdj_adj_pair l k hk
  rw [h1, h2]
  exact hne

private lemma w03_facts :
    (∀ k : Fin 6, (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 0 → k.val = 0 ∨ k.val = 3) ∧
    (∀ k : Fin 6, (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 0 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 4 → k.val = 0 ∨ k.val = 3 ∨ k.val = 5) ∧
    (∀ k : Fin 6, (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 4 → k.val = 5) ∧
    (∀ k : Fin 6, (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 0 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 2 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 4 → k.val ≠ 1 ∧ k.val ≠ 4) ∧
    (∀ k : Fin 6, k.val ≤ 1 → (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k ≠ 2 ∧ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k ≠ 4) ∧
    (∀ k : Fin 6, (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 0 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 1 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k = 4 → k.val ≠ 2 ∧ k.val ≠ 4) ∧
    (∀ k : Fin 6, 2 ≤ k.val → k.val ≤ 4 → (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k ≠ 1 ∧ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k ≠ 4) := by
  decide

private lemma elim_n6_orbit03 (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hn6 : hullBlockCount P = 6) (φ : Fin 5 ≃ Fin 5)
    (hX_no_nonhull : ∀ a : Fin 10, vecColor a = φ 0 → ∃ r : Fin ((topTiePts P).card + 1), hullIdx P r = a)
    (hw : ∀ k : Fin 6, φ.symm ((compressedColors P)[k.val]'(by have : (compressedColors P).length = 6 := hn6; omega)) = ![0, 1, 2, 0, 3, 4] k) :
    False := by
  let w₀ : Fin 6 → Fin 5 := ![0, 1, 2, 0, 3, 4]
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  have hlen_l : l.length = h := List.length_ofFn
  have hlen_cs : (compressedColors P).length = 6 := hn6
  have hcs_def : compressedColors P = compressAdj l := rfl
  let b : Fin h → ℕ := fun r =>
    (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt)
  have hb_lt : ∀ r : Fin h, b r < 6 := fun r => by
    have := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    change b r < 0 + (compressedColors P).length at this
    rw [hlen_cs] at this; omega
  have hcol_of_b : ∀ r : Fin h, hullColors P r = φ (w₀ ⟨b r, hb_lt r⟩) := fun r => by
    have hget := blockIndicesAux_getElem 0 l r.val (by rw [hlen_l]; exact r.isLt)
    have hl_r : l[r.val]'(by rw [hlen_l]; exact r.isLt) = hullColors P r := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hcs_r : (compressAdj l)[b r]'(by rw [← hcs_def, hlen_cs]; exact hb_lt r) = hullColors P r :=
      (list_getElem_eq_of_idx (compressAdj l) _ _ (Nat.sub_zero _)).trans (hget.trans hl_r)
    dsimp only [w₀]; rw [← hw ⟨b r, hb_lt r⟩, Equiv.apply_symm_apply]
    exact hcs_r.symm
  have hX_in_int : ∀ (S : Finset (Fin 5)) (z : ℝ × ℝ) (hreal : RealizesDualMask P (fun i => !decide (i ∈ S)) z)
      (r₁ r₂ : Fin h) (hdot_iff : ∀ r, 1 < dot2 (hullVerts P r) z ↔ r₁ ≤ r ∧ r ≤ r₂),
      φ 0 ∈ S → ∃ r₀ : Fin h, b r₁ ≤ b r₀ ∧ b r₀ ≤ b r₂ ∧ (b r₀ = 0 ∨ b r₀ = 3) := by
    intro S z hreal r₁ r₂ hdot_iff h0S
    obtain ⟨a0, ha0_col, ha0_dot⟩ := (realizesDualMask_ext_iff P S z hreal (φ 0)).mp h0S
    obtain ⟨r₀, hr₀⟩ := hX_no_nonhull a0 ha0_col
    have hr₀_dot : 1 < dot2 (hullVerts P r₀) z := by unfold hullVerts; rw [hr₀]; exact ha0_dot
    have hr₀_int := (hdot_iff r₀).mp hr₀_dot
    have hb1 : b r₁ ≤ b r₀ := blockIndicesAux_mono 0 l hr₀_int.1 (by rw [hlen_l]; exact r₀.isLt)
    have hb2 : b r₀ ≤ b r₂ := blockIndicesAux_mono 0 l hr₀_int.2 (by rw [hlen_l]; exact r₂.isLt)
    have hw0 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨b r₀, hb_lt r₀⟩ = 0 := by
      refine φ.injective ?_
      dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r₀]; unfold hullColors; rw [hr₀, ha0_col]
    have h03 : b r₀ = 0 ∨ b r₀ = 3 := w03_facts.1 ⟨b r₀, hb_lt r₀⟩ hw0
    exact ⟨r₀, hb1, hb2, h03⟩
  let T₀ : Finset (Fin 5) := {φ 0, φ 4}
  obtain ⟨z₀, hz₀, hreal₀⟩ := h_shat (fun i => !decide (i ∈ T₀))
  obtain ⟨r₁, r₂, hr12, hdot_iff₀, hcol_in₀⟩ := dual_island_rule P hgp htop T₀ ⟨φ 0, by simp [T₀]⟩ z₀ hz₀ hreal₀
  obtain ⟨r₀, hb1_0, hb2_0, h03_0⟩ := hX_in_int T₀ z₀ hreal₀ r₁ r₂ hdot_iff₀ (by simp [T₀])
  have hno_non04 : ∀ k : ℕ, b r₁ ≤ k → k ≤ b r₂ → k = 0 ∨ k = 3 ∨ k = 5 := by
    intro k hk1 hk2
    have hk6 : k < 6 := by have := hb_lt r₂; omega
    obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
      blockIndicesAux_surj_interval 0 l hr12 (by rw [hlen_l]; exact r₂.isLt) k hk1 hk2
    have hcol_r : hullColors P ⟨r, by omega⟩ ∈ T₀ := hcol_in₀ ⟨r, by omega⟩ hr_lo hr_hi
    have hfin_eq : (⟨b ⟨r, by omega⟩, hb_lt ⟨r, by omega⟩⟩ : Fin 6) = ⟨k, hk6⟩ :=
      Fin.ext (hr_eq (by rw [hlen_l]; omega))
    rw [hcol_of_b ⟨r, by omega⟩, hfin_eq] at hcol_r
    simp only [T₀, Finset.mem_insert, Finset.mem_singleton] at hcol_r
    have hw_04 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 0 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 4 := by
      dsimp only [w₀] at hcol_r
      rcases hcol_r with h | h <;> [left; right] <;> exact φ.injective h
    exact w03_facts.2.1 ⟨k, hk6⟩ hw_04
  have hbr0_eq : (b r₁ = 0 ∧ b r₂ = 0) ∨ (b r₁ = 3 ∧ b r₂ = 3) := by
    rcases h03_0 with h0 | h3
    · left
      have h1 : b r₁ = 0 := by omega
      have h2 : b r₂ = 0 := by
        by_contra hne
        have : 1 ≤ b r₂ := by omega
        rcases hno_non04 1 (by omega) this with h | h | h <;> omega
      exact ⟨h1, h2⟩
    · right
      have h1 : b r₁ = 3 := by
        by_contra hne
        have : b r₁ ≤ 2 := by omega
        rcases hno_non04 2 this (by omega) with h | h | h <;> omega
      have h2 : b r₂ = 3 := by
        by_contra hne
        have : 4 ≤ b r₂ := by omega
        rcases hno_non04 4 (by omega) this with h | h | h <;> omega
      exact ⟨h1, h2⟩
  have h5_not_int : ∀ r : Fin h, hullColors P r = φ 4 → ¬ (1 < dot2 (hullVerts P r) z₀) := by
    intro r hcr hact
    have hr_int := (hdot_iff₀ r).mp hact
    have hb2 : b r ≤ b r₂ := blockIndicesAux_mono 0 l hr_int.2 (by rw [hlen_l]; exact r₂.isLt)
    have hw4 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨b r, hb_lt r⟩ = 4 := by
      refine φ.injective ?_
      dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r, hcr]
    have hbr5 : b r = 5 := w03_facts.2.2.1 ⟨b r, hb_lt r⟩ hw4
    omega
  obtain ⟨a_D, haD_col, haD_dot⟩ := (realizesDualMask_ext_iff P T₀ z₀ hreal₀ (φ 4)).mp (by simp [T₀])
  have haD_not : ∀ r : Fin h, hullIdx P r ≠ a_D := fun r hr => by
    apply h5_not_int r (by unfold hullColors; rw [hr, haD_col])
    unfold hullVerts; rw [hr]; exact haD_dot
  obtain ⟨j_D, hjD_lt, hjD_spec⟩ := non_hull_slab_constraint P hgp htop hn6 (by omega) a_D haD_not
  have hjD_0 := hjD_spec z₀ hz₀ haD_dot r₁ r₂ hdot_iff₀
  change b r₁ ≤ j_D + 1 ∧ j_D ≤ b r₂ at hjD_0
  have h5col := hull_five_colors P hgp htop h_shat
  have hno_adj03 : ∀ c₁ c₂ : Fin 5, c₁ ≠ c₂ →
      (∀ k : Fin 5, !((w₀ k.castSucc == c₁ && w₀ k.succ == c₂) || (w₀ k.castSucc == c₂ && w₀ k.succ == c₁))) →
      ({φ c₁, φ c₂} : Finset (Fin 5)) ∉ pureHullPairs P := by
    intro c₁ c₂ hc_ne hadj
    refine not_mem_pureHullPairs_of_no_adj P hgp htop hn6 (φ c₁) (φ c₂) (φ.injective.ne hc_ne) ?_
    intro k hk heq
    let kf : Fin 5 := ⟨k, by omega⟩
    have h1 : (compressedColors P)[k]'(by rw [hlen_cs]; exact Nat.lt_of_succ_lt hk) = φ (w₀ kf.castSucc) := by
      dsimp only [w₀]; rw [← hw kf.castSucc, Equiv.apply_symm_apply]; rfl
    have h2 : (compressedColors P)[k + 1]'(by rw [hlen_cs]; exact hk) = φ (w₀ kf.succ) := by
      dsimp only [w₀]; rw [← hw kf.succ, Equiv.apply_symm_apply]; rfl
    rw [h1, h2] at heq
    have hm1 : φ (w₀ kf.castSucc) ∈ ({φ c₁, φ c₂} : Finset (Fin 5)) := by rw [← heq]; simp
    have hm2 : φ (w₀ kf.succ) ∈ ({φ c₁, φ c₂} : Finset (Fin 5)) := by rw [← heq]; simp
    have ha := hadj kf
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with hm1 | hm1 <;> rcases hm2 with hm2 | hm2
    · have : ({φ (w₀ kf.castSucc), φ (w₀ kf.succ)} : Finset (Fin 5)) = {φ c₁} := by rw [hm1, hm2]; simp
      have hsub : φ c₂ ∈ ({φ c₁} : Finset (Fin 5)) := by rw [← this, heq]; simp
      simp only [Finset.mem_singleton] at hsub
      exact hc_ne (φ.injective hsub.symm)
    · rcases ha.1 with h | h <;> exact h (φ.injective (by assumption))
    · rcases ha.2 with h | h <;> exact h (φ.injective (by assumption))
    · have : ({φ (w₀ kf.castSucc), φ (w₀ kf.succ)} : Finset (Fin 5)) = {φ c₂} := by rw [hm1, hm2]; simp
      have hsub : φ c₁ ∈ ({φ c₂} : Finset (Fin 5)) := by rw [← this, heq]; simp
      simp only [Finset.mem_singleton] at hsub
      exact hc_ne (φ.injective hsub)
  rcases hbr0_eq with ⟨hr01, hr02⟩ | ⟨hr01, hr02⟩
  · have hjD_eq : j_D = 0 := by omega
    let S₁ : Finset (Fin 5) := {φ 0, φ 2, φ 4}
    obtain ⟨z₁, hz₁, hreal₁⟩ := h_shat (fun i => !decide (i ∈ S₁))
    obtain ⟨r'₁, r'₂, hr'12, hdot_iff₁, hcol_in₁⟩ := dual_island_rule P hgp htop S₁ ⟨φ 0, by simp [S₁]⟩ z₁ hz₁ hreal₁
    obtain ⟨r'₀, hb1_1, hb2_1, h03_1⟩ := hX_in_int S₁ z₁ hreal₁ r'₁ r'₂ hdot_iff₁ (by simp [S₁])
    have hno_14 : ∀ k : ℕ, b r'₁ ≤ k → k ≤ b r'₂ → k ≠ 1 ∧ k ≠ 4 := by
      intro k hk1 hk2
      have hk6 : k < 6 := by have := hb_lt r'₂; omega
      obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt) k hk1 hk2
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ S₁ := hcol_in₁ ⟨r, by omega⟩ hr_lo hr_hi
      have hfin_eq : (⟨b ⟨r, by omega⟩, hb_lt ⟨r, by omega⟩⟩ : Fin 6) = ⟨k, hk6⟩ :=
        Fin.ext (hr_eq (by rw [hlen_l]; omega))
      rw [hcol_of_b ⟨r, by omega⟩, hfin_eq] at hcol_r
      simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at hcol_r
      have hw_024 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 0 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 2 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 4 := by
        dsimp only [w₀] at hcol_r
        rcases hcol_r with h | h | h
        · left; exact φ.injective h
        · right; left; exact φ.injective h
        · right; right; exact φ.injective h
      exact w03_facts.2.2.2.1 ⟨k, hk6⟩ hw_024
    have hb2_le3 : b r'₂ ≤ 3 := by
      by_contra hgt
      have := hno_14 4 (by omega) (by omega)
      exact this.2 rfl
    have h4_missing : ∀ r : Fin h, hullColors P r = φ 4 → ¬ (1 < dot2 (hullVerts P r) z₁) := by
      intro r hcr hact
      have hr_int := (hdot_iff₁ r).mp hact
      have hb2 : b r ≤ b r'₂ := blockIndicesAux_mono 0 l hr_int.2 (by rw [hlen_l]; exact r'₂.isLt)
      have hw4 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨b r, hb_lt r⟩ = 4 := by refine φ.injective ?_; dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r, hcr]
      have hbr5 : b r = 5 := w03_facts.2.2.1 ⟨b r, hb_lt r⟩ hw4
      omega
    obtain ⟨a'D, ha'D_col, ha'D_dot⟩ := (realizesDualMask_ext_iff P S₁ z₁ hreal₁ (φ 4)).mp (by simp [S₁])
    have ha'D_not : ∀ r : Fin h, hullIdx P r ≠ a'D := fun r hr => by
      apply h4_missing r (by unfold hullColors; rw [hr, ha'D_col])
      unfold hullVerts; rw [hr]; exact ha'D_dot
    have ha'D_eq : a'D = a_D := h5col.2.2.2 a'D a_D ha'D_not haD_not (ha'D_col.trans haD_col.symm)
    have hslab_1 := hjD_spec z₁ hz₁ (ha'D_eq ▸ ha'D_dot) r'₁ r'₂ hdot_iff₁
    change b r'₁ ≤ j_D + 1 ∧ j_D ≤ b r'₂ at hslab_1
    have hbr1_0 : b r'₁ = 0 := by
      have : b r'₁ ≤ 1 := by omega
      by_contra hne
      have : b r'₁ = 1 := by omega
      exact (hno_14 1 (by omega) (by omega)).1 rfl
    have hbr2_0 : b r'₂ = 0 := by
      by_contra hne
      have : 1 ≤ b r'₂ := by omega
      exact (hno_14 1 (by omega) this).1 rfl
    refine island_rule_contradiction P hgp htop h_shat hn6 (by omega) S₁ z₁ hz₁ hreal₁ r'₁ r'₂ hr'12 hdot_iff₁
      (φ 2) (φ 4) (φ.injective.ne (by decide)) (hno_adj03 2 4 (by decide) (by decide))
      (by simp [S₁]) (by simp [S₁]) ?_
    intro k hk1 hk2
    have hk_le1 : k.val ≤ 1 := by change b r'₁ ≤ k.val + 1 at hk1; change k.val ≤ b r'₂ + 1 at hk2; omega
    have hk_eq : (compressedColors P)[k.val]'(by rw [hlen_cs]; exact k.isLt) = φ ((![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k) := by
      rw [← hw k, Equiv.apply_symm_apply]
    rw [hk_eq]
    have hwf := w03_facts.2.2.2.2.1 k hk_le1
    exact ⟨φ.injective.ne hwf.1, φ.injective.ne hwf.2⟩
  · have hjD_23 : j_D = 2 ∨ j_D = 3 := by omega
    let S₂ : Finset (Fin 5) := {φ 0, φ 1, φ 4}
    obtain ⟨z₂, hz₂, hreal₂⟩ := h_shat (fun i => !decide (i ∈ S₂))
    obtain ⟨r'₁, r'₂, hr'12, hdot_iff₂, hcol_in₂⟩ := dual_island_rule P hgp htop S₂ ⟨φ 0, by simp [S₂]⟩ z₂ hz₂ hreal₂
    obtain ⟨r'₀, hb1_2, hb2_2, h03_2⟩ := hX_in_int S₂ z₂ hreal₂ r'₁ r'₂ hdot_iff₂ (by simp [S₂])
    have hno_24 : ∀ k : ℕ, b r'₁ ≤ k → k ≤ b r'₂ → k ≠ 2 ∧ k ≠ 4 := by
      intro k hk1 hk2
      have hk6 : k < 6 := by have := hb_lt r'₂; omega
      obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt) k hk1 hk2
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ S₂ := hcol_in₂ ⟨r, by omega⟩ hr_lo hr_hi
      have hfin_eq : (⟨b ⟨r, by omega⟩, hb_lt ⟨r, by omega⟩⟩ : Fin 6) = ⟨k, hk6⟩ :=
        Fin.ext (hr_eq (by rw [hlen_l]; omega))
      rw [hcol_of_b ⟨r, by omega⟩, hfin_eq] at hcol_r
      simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at hcol_r
      have hw_014 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 0 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 1 ∨ (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 4 := by
        dsimp only [w₀] at hcol_r
        rcases hcol_r with h | h | h
        · left; exact φ.injective h
        · right; left; exact φ.injective h
        · right; right; exact φ.injective h
      exact w03_facts.2.2.2.2.2.1 ⟨k, hk6⟩ hw_014
    have hb2_le3 : b r'₂ ≤ 3 := by
      by_contra hgt
      have := hno_24 4 (by omega) (by omega)
      exact this.2 rfl
    have h4_missing : ∀ r : Fin h, hullColors P r = φ 4 → ¬ (1 < dot2 (hullVerts P r) z₂) := by
      intro r hcr hact
      have hr_int := (hdot_iff₂ r).mp hact
      have hb2 : b r ≤ b r'₂ := blockIndicesAux_mono 0 l hr_int.2 (by rw [hlen_l]; exact r'₂.isLt)
      have hw4 : (![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) ⟨b r, hb_lt r⟩ = 4 := by refine φ.injective ?_; dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r, hcr]
      have hbr5 : b r = 5 := w03_facts.2.2.1 ⟨b r, hb_lt r⟩ hw4
      omega
    obtain ⟨a'D, ha'D_col, ha'D_dot⟩ := (realizesDualMask_ext_iff P S₂ z₂ hreal₂ (φ 4)).mp (by simp [S₂])
    have ha'D_not : ∀ r : Fin h, hullIdx P r ≠ a'D := fun r hr => by
      apply h4_missing r (by unfold hullColors; rw [hr, ha'D_col])
      unfold hullVerts; rw [hr]; exact ha'D_dot
    have ha'D_eq : a'D = a_D := h5col.2.2.2 a'D a_D ha'D_not haD_not (ha'D_col.trans haD_col.symm)
    have hslab_2 := hjD_spec z₂ hz₂ (ha'D_eq ▸ ha'D_dot) r'₁ r'₂ hdot_iff₂
    change b r'₁ ≤ j_D + 1 ∧ j_D ≤ b r'₂ at hslab_2
    have hbr1_3 : b r'₁ = 3 := by
      by_contra hne
      have : b r'₁ ≤ 2 := by omega
      exact (hno_24 2 this (by omega)).1 rfl
    have hbr2_3 : b r'₂ = 3 := by omega
    refine island_rule_contradiction P hgp htop h_shat hn6 (by omega) S₂ z₂ hz₂ hreal₂ r'₁ r'₂ hr'12 hdot_iff₂
      (φ 1) (φ 4) (φ.injective.ne (by decide)) (hno_adj03 1 4 (by decide) (by decide))
      (by simp [S₂]) (by simp [S₂]) ?_
    intro k hk1 hk2
    have hk_rng : 2 ≤ k.val ∧ k.val ≤ 4 := by change b r'₁ ≤ k.val + 1 at hk1; change k.val ≤ b r'₂ + 1 at hk2; omega
    have hk_eq : (compressedColors P)[k.val]'(by rw [hlen_cs]; exact k.isLt) = φ ((![0, 1, 2, 0, 3, 4] : Fin 6 → Fin 5) k) := by
      rw [← hw k, Equiv.apply_symm_apply]
    rw [hk_eq]
    have hwf := w03_facts.2.2.2.2.2.2 k hk_rng.1 hk_rng.2
    exact ⟨φ.injective.ne hwf.1, φ.injective.ne hwf.2⟩

private lemma w25_facts :
    (∀ k : Fin 6, (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 0 → k.val = 2 ∨ k.val = 5) ∧
    (∀ k : Fin 6, (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 0 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 1 → k.val = 0 ∨ k.val = 2 ∨ k.val = 5) ∧
    (∀ k : Fin 6, (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 1 → k.val = 0) ∧
    (∀ k : Fin 6, (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 0 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 1 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 4 → k.val ≠ 1 ∧ k.val ≠ 3) ∧
    (∀ k : Fin 6, 1 ≤ k.val → k.val ≤ 3 → (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k ≠ 1 ∧ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k ≠ 4) ∧
    (∀ k : Fin 6, (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 0 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 1 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k = 3 → k.val ≠ 1 ∧ k.val ≠ 4) ∧
    (∀ k : Fin 6, 4 ≤ k.val → (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k ≠ 1 ∧ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k ≠ 3) := by
  decide

private lemma elim_n6_orbit25 (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hn6 : hullBlockCount P = 6) (φ : Fin 5 ≃ Fin 5)
    (hX_no_nonhull : ∀ a : Fin 10, vecColor a = φ 0 → ∃ r : Fin ((topTiePts P).card + 1), hullIdx P r = a)
    (hw : ∀ k : Fin 6, φ.symm ((compressedColors P)[k.val]'(by have : (compressedColors P).length = 6 := hn6; omega)) = ![1, 2, 0, 3, 4, 0] k) :
    False := by
  let w₀ : Fin 6 → Fin 5 := ![1, 2, 0, 3, 4, 0]
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  have hlen_l : l.length = h := List.length_ofFn
  have hlen_cs : (compressedColors P).length = 6 := hn6
  have hcs_def : compressedColors P = compressAdj l := rfl
  let b : Fin h → ℕ := fun r =>
    (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt)
  have hb_lt : ∀ r : Fin h, b r < 6 := fun r => by
    have := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    change b r < 0 + (compressedColors P).length at this
    rw [hlen_cs] at this; omega
  have hcol_of_b : ∀ r : Fin h, hullColors P r = φ (w₀ ⟨b r, hb_lt r⟩) := fun r => by
    have hget := blockIndicesAux_getElem 0 l r.val (by rw [hlen_l]; exact r.isLt)
    have hl_r : l[r.val]'(by rw [hlen_l]; exact r.isLt) = hullColors P r := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hcs_r : (compressAdj l)[b r]'(by rw [← hcs_def, hlen_cs]; exact hb_lt r) = hullColors P r :=
      (list_getElem_eq_of_idx (compressAdj l) _ _ (Nat.sub_zero _)).trans (hget.trans hl_r)
    dsimp only [w₀]; rw [← hw ⟨b r, hb_lt r⟩, Equiv.apply_symm_apply]
    exact hcs_r.symm
  have hX_in_int : ∀ (S : Finset (Fin 5)) (z : ℝ × ℝ) (hreal : RealizesDualMask P (fun i => !decide (i ∈ S)) z)
      (r₁ r₂ : Fin h) (hdot_iff : ∀ r, 1 < dot2 (hullVerts P r) z ↔ r₁ ≤ r ∧ r ≤ r₂),
      φ 0 ∈ S → ∃ r₀ : Fin h, b r₁ ≤ b r₀ ∧ b r₀ ≤ b r₂ ∧ (b r₀ = 2 ∨ b r₀ = 5) := by
    intro S z hreal r₁ r₂ hdot_iff h0S
    obtain ⟨a0, ha0_col, ha0_dot⟩ := (realizesDualMask_ext_iff P S z hreal (φ 0)).mp h0S
    obtain ⟨r₀, hr₀⟩ := hX_no_nonhull a0 ha0_col
    have hr₀_dot : 1 < dot2 (hullVerts P r₀) z := by unfold hullVerts; rw [hr₀]; exact ha0_dot
    have hr₀_int := (hdot_iff r₀).mp hr₀_dot
    have hb1 : b r₁ ≤ b r₀ := blockIndicesAux_mono 0 l hr₀_int.1 (by rw [hlen_l]; exact r₀.isLt)
    have hb2 : b r₀ ≤ b r₂ := blockIndicesAux_mono 0 l hr₀_int.2 (by rw [hlen_l]; exact r₂.isLt)
    have hw0 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨b r₀, hb_lt r₀⟩ = 0 := by
      refine φ.injective ?_
      dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r₀]; unfold hullColors; rw [hr₀, ha0_col]
    have h25 : b r₀ = 2 ∨ b r₀ = 5 := w25_facts.1 ⟨b r₀, hb_lt r₀⟩ hw0
    exact ⟨r₀, hb1, hb2, h25⟩
  let T₀ : Finset (Fin 5) := {φ 0, φ 1}
  obtain ⟨z₀, hz₀, hreal₀⟩ := h_shat (fun i => !decide (i ∈ T₀))
  obtain ⟨r₁, r₂, hr12, hdot_iff₀, hcol_in₀⟩ := dual_island_rule P hgp htop T₀ ⟨φ 0, by simp [T₀]⟩ z₀ hz₀ hreal₀
  obtain ⟨r₀, hb1_0, hb2_0, h25_0⟩ := hX_in_int T₀ z₀ hreal₀ r₁ r₂ hdot_iff₀ (by simp [T₀])
  have hno_non01 : ∀ k : ℕ, b r₁ ≤ k → k ≤ b r₂ → k = 0 ∨ k = 2 ∨ k = 5 := by
    intro k hk1 hk2
    have hk6 : k < 6 := by have := hb_lt r₂; omega
    obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
      blockIndicesAux_surj_interval 0 l hr12 (by rw [hlen_l]; exact r₂.isLt) k hk1 hk2
    have hcol_r : hullColors P ⟨r, by omega⟩ ∈ T₀ := hcol_in₀ ⟨r, by omega⟩ hr_lo hr_hi
    have hfin_eq : (⟨b ⟨r, by omega⟩, hb_lt ⟨r, by omega⟩⟩ : Fin 6) = ⟨k, hk6⟩ :=
      Fin.ext (hr_eq (by rw [hlen_l]; omega))
    rw [hcol_of_b ⟨r, by omega⟩, hfin_eq] at hcol_r
    simp only [T₀, Finset.mem_insert, Finset.mem_singleton] at hcol_r
    have hw_01 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 0 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 1 := by
      dsimp only [w₀] at hcol_r
      rcases hcol_r with h | h <;> [left; right] <;> exact φ.injective h
    exact w25_facts.2.1 ⟨k, hk6⟩ hw_01
  have hbr0_eq : (b r₁ = 2 ∧ b r₂ = 2) ∨ (b r₁ = 5 ∧ b r₂ = 5) := by
    rcases h25_0 with h2 | h5
    · left
      have h1 : b r₁ = 2 := by
        by_contra hne
        have : b r₁ ≤ 1 := by omega
        rcases hno_non01 1 this (by omega) with h | h | h <;> omega
      have h2' : b r₂ = 2 := by
        by_contra hne
        have : 3 ≤ b r₂ := by omega
        rcases hno_non01 3 (by omega) this with h | h | h <;> omega
      exact ⟨h1, h2'⟩
    · right
      have h1 : b r₁ = 5 := by
        by_contra hne
        have : b r₁ ≤ 4 := by omega
        rcases hno_non01 4 this (by omega) with h | h | h <;> omega
      have h2' : b r₂ = 5 := by have := hb_lt r₂; omega
      exact ⟨h1, h2'⟩
  have h0_not_int : ∀ r : Fin h, hullColors P r = φ 1 → ¬ (1 < dot2 (hullVerts P r) z₀) := by
    intro r hcr hact
    have hr_int := (hdot_iff₀ r).mp hact
    have hb1 : b r₁ ≤ b r := blockIndicesAux_mono 0 l hr_int.1 (by rw [hlen_l]; exact r.isLt)
    have hw1 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨b r, hb_lt r⟩ = 1 := by refine φ.injective ?_; dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r, hcr]
    have hbr0 : b r = 0 := w25_facts.2.2.1 ⟨b r, hb_lt r⟩ hw1
    omega
  obtain ⟨a_A, haA_col, haA_dot⟩ := (realizesDualMask_ext_iff P T₀ z₀ hreal₀ (φ 1)).mp (by simp [T₀])
  have haA_not : ∀ r : Fin h, hullIdx P r ≠ a_A := fun r hr => by
    apply h0_not_int r (by unfold hullColors; rw [hr, haA_col])
    unfold hullVerts; rw [hr]; exact haA_dot
  obtain ⟨j_A, hjA_lt, hjA_spec⟩ := non_hull_slab_constraint P hgp htop hn6 (by omega) a_A haA_not
  have hjA_0 := hjA_spec z₀ hz₀ haA_dot r₁ r₂ hdot_iff₀
  change b r₁ ≤ j_A + 1 ∧ j_A ≤ b r₂ at hjA_0
  have h5col := hull_five_colors P hgp htop h_shat
  have hno_adj25 : ∀ c₁ c₂ : Fin 5, c₁ ≠ c₂ →
      (∀ k : Fin 5, !((w₀ k.castSucc == c₁ && w₀ k.succ == c₂) || (w₀ k.castSucc == c₂ && w₀ k.succ == c₁))) →
      ({φ c₁, φ c₂} : Finset (Fin 5)) ∉ pureHullPairs P := by
    intro c₁ c₂ hc_ne hadj
    refine not_mem_pureHullPairs_of_no_adj P hgp htop hn6 (φ c₁) (φ c₂) (φ.injective.ne hc_ne) ?_
    intro k hk heq
    let kf : Fin 5 := ⟨k, by omega⟩
    have h1 : (compressedColors P)[k]'(by rw [hlen_cs]; exact Nat.lt_of_succ_lt hk) = φ (w₀ kf.castSucc) := by
      dsimp only [w₀]; rw [← hw kf.castSucc, Equiv.apply_symm_apply]; rfl
    have h2 : (compressedColors P)[k + 1]'(by rw [hlen_cs]; exact hk) = φ (w₀ kf.succ) := by
      dsimp only [w₀]; rw [← hw kf.succ, Equiv.apply_symm_apply]; rfl
    rw [h1, h2] at heq
    have hm1 : φ (w₀ kf.castSucc) ∈ ({φ c₁, φ c₂} : Finset (Fin 5)) := by rw [← heq]; simp
    have hm2 : φ (w₀ kf.succ) ∈ ({φ c₁, φ c₂} : Finset (Fin 5)) := by rw [← heq]; simp
    have ha := hadj kf
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with hm1 | hm1 <;> rcases hm2 with hm2 | hm2
    · have : ({φ (w₀ kf.castSucc), φ (w₀ kf.succ)} : Finset (Fin 5)) = {φ c₁} := by rw [hm1, hm2]; simp
      have hsub : φ c₂ ∈ ({φ c₁} : Finset (Fin 5)) := by rw [← this, heq]; simp
      simp only [Finset.mem_singleton] at hsub
      exact hc_ne (φ.injective hsub.symm)
    · rcases ha.1 with h | h <;> exact h (φ.injective (by assumption))
    · rcases ha.2 with h | h <;> exact h (φ.injective (by assumption))
    · have : ({φ (w₀ kf.castSucc), φ (w₀ kf.succ)} : Finset (Fin 5)) = {φ c₂} := by rw [hm1, hm2]; simp
      have hsub : φ c₁ ∈ ({φ c₂} : Finset (Fin 5)) := by rw [← this, heq]; simp
      simp only [Finset.mem_singleton] at hsub
      exact hc_ne (φ.injective hsub)
  rcases hbr0_eq with ⟨hr01, hr02⟩ | ⟨hr01, hr02⟩
  · have hjA_12 : j_A = 1 ∨ j_A = 2 := by omega
    let S₂ : Finset (Fin 5) := {φ 0, φ 1, φ 4}
    obtain ⟨z₂, hz₂, hreal₂⟩ := h_shat (fun i => !decide (i ∈ S₂))
    obtain ⟨r'₁, r'₂, hr'12, hdot_iff₂, hcol_in₂⟩ := dual_island_rule P hgp htop S₂ ⟨φ 0, by simp [S₂]⟩ z₂ hz₂ hreal₂
    obtain ⟨r'₀, hb1_2, hb2_2, h25_2⟩ := hX_in_int S₂ z₂ hreal₂ r'₁ r'₂ hdot_iff₂ (by simp [S₂])
    have hno_13 : ∀ k : ℕ, b r'₁ ≤ k → k ≤ b r'₂ → k ≠ 1 ∧ k ≠ 3 := by
      intro k hk1 hk2
      have hk6 : k < 6 := by have := hb_lt r'₂; omega
      obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt) k hk1 hk2
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ S₂ := hcol_in₂ ⟨r, by omega⟩ hr_lo hr_hi
      have hfin_eq : (⟨b ⟨r, by omega⟩, hb_lt ⟨r, by omega⟩⟩ : Fin 6) = ⟨k, hk6⟩ :=
        Fin.ext (hr_eq (by rw [hlen_l]; omega))
      rw [hcol_of_b ⟨r, by omega⟩, hfin_eq] at hcol_r
      simp only [S₂, Finset.mem_insert, Finset.mem_singleton] at hcol_r
      have hw_014 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 0 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 1 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 4 := by
        dsimp only [w₀] at hcol_r
        rcases hcol_r with h | h | h
        · left; exact φ.injective h
        · right; left; exact φ.injective h
        · right; right; exact φ.injective h
      exact w25_facts.2.2.2.1 ⟨k, hk6⟩ hw_014
    have hb1_ge2 : 2 ≤ b r'₁ := by
      by_contra hlt
      have := hno_13 1 (by omega) (by omega)
      exact this.1 rfl
    have h1_missing : ∀ r : Fin h, hullColors P r = φ 1 → ¬ (1 < dot2 (hullVerts P r) z₂) := by
      intro r hcr hact
      have hr_int := (hdot_iff₂ r).mp hact
      have hb1 : b r'₁ ≤ b r := blockIndicesAux_mono 0 l hr_int.1 (by rw [hlen_l]; exact r.isLt)
      have hw1 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨b r, hb_lt r⟩ = 1 := by refine φ.injective ?_; dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r, hcr]
      have hbr0 : b r = 0 := w25_facts.2.2.1 ⟨b r, hb_lt r⟩ hw1
      omega
    obtain ⟨a'A, ha'A_col, ha'A_dot⟩ := (realizesDualMask_ext_iff P S₂ z₂ hreal₂ (φ 1)).mp (by simp [S₂])
    have ha'A_not : ∀ r : Fin h, hullIdx P r ≠ a'A := fun r hr => by
      apply h1_missing r (by unfold hullColors; rw [hr, ha'A_col])
      unfold hullVerts; rw [hr]; exact ha'A_dot
    have ha'A_eq : a'A = a_A := h5col.2.2.2 a'A a_A ha'A_not haA_not (ha'A_col.trans haA_col.symm)
    have hslab_2 := hjA_spec z₂ hz₂ (ha'A_eq ▸ ha'A_dot) r'₁ r'₂ hdot_iff₂
    change b r'₁ ≤ j_A + 1 ∧ j_A ≤ b r'₂ at hslab_2
    have hbr1_2 : b r'₁ = 2 := by
      by_contra hne
      have : b r'₁ = 3 := by omega
      exact (hno_13 3 (by omega) (by omega)).2 rfl
    have hbr2_2 : b r'₂ = 2 := by
      by_contra hne
      have : 3 ≤ b r'₂ := by omega
      exact (hno_13 3 (by omega) this).2 rfl
    refine island_rule_contradiction P hgp htop h_shat hn6 (by omega) S₂ z₂ hz₂ hreal₂ r'₁ r'₂ hr'12 hdot_iff₂
      (φ 1) (φ 4) (φ.injective.ne (by decide)) (hno_adj25 1 4 (by decide) (by decide))
      (by simp [S₂]) (by simp [S₂]) ?_
    intro k hk1 hk2
    have hk_rng : 1 ≤ k.val ∧ k.val ≤ 3 := by change b r'₁ ≤ k.val + 1 at hk1; change k.val ≤ b r'₂ + 1 at hk2; omega
    have hk_eq : (compressedColors P)[k.val]'(by rw [hlen_cs]; exact k.isLt) = φ ((![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k) := by
      rw [← hw k, Equiv.apply_symm_apply]
    rw [hk_eq]
    have hwf := w25_facts.2.2.2.2.1 k hk_rng.1 hk_rng.2
    exact ⟨φ.injective.ne hwf.1, φ.injective.ne hwf.2⟩
  · have hjA_4 : j_A = 4 := by omega
    let S₁ : Finset (Fin 5) := {φ 0, φ 1, φ 3}
    obtain ⟨z₁, hz₁, hreal₁⟩ := h_shat (fun i => !decide (i ∈ S₁))
    obtain ⟨r'₁, r'₂, hr'12, hdot_iff₁, hcol_in₁⟩ := dual_island_rule P hgp htop S₁ ⟨φ 0, by simp [S₁]⟩ z₁ hz₁ hreal₁
    obtain ⟨r'₀, hb1_1, hb2_1, h25_1⟩ := hX_in_int S₁ z₁ hreal₁ r'₁ r'₂ hdot_iff₁ (by simp [S₁])
    have hno_14 : ∀ k : ℕ, b r'₁ ≤ k → k ≤ b r'₂ → k ≠ 1 ∧ k ≠ 4 := by
      intro k hk1 hk2
      have hk6 : k < 6 := by have := hb_lt r'₂; omega
      obtain ⟨r, hr_lo, hr_hi, hr_eq⟩ :=
        blockIndicesAux_surj_interval 0 l hr'12 (by rw [hlen_l]; exact r'₂.isLt) k hk1 hk2
      have hcol_r : hullColors P ⟨r, by omega⟩ ∈ S₁ := hcol_in₁ ⟨r, by omega⟩ hr_lo hr_hi
      have hfin_eq : (⟨b ⟨r, by omega⟩, hb_lt ⟨r, by omega⟩⟩ : Fin 6) = ⟨k, hk6⟩ :=
        Fin.ext (hr_eq (by rw [hlen_l]; omega))
      rw [hcol_of_b ⟨r, by omega⟩, hfin_eq] at hcol_r
      simp only [S₁, Finset.mem_insert, Finset.mem_singleton] at hcol_r
      have hw_013 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 0 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 1 ∨ (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨k, hk6⟩ = 3 := by
        dsimp only [w₀] at hcol_r
        rcases hcol_r with h | h | h
        · left; exact φ.injective h
        · right; left; exact φ.injective h
        · right; right; exact φ.injective h
      exact w25_facts.2.2.2.2.2.1 ⟨k, hk6⟩ hw_013
    have hb1_ge2 : 2 ≤ b r'₁ := by
      by_contra hlt
      have := hno_14 1 (by omega) (by omega)
      exact this.1 rfl
    have h1_missing : ∀ r : Fin h, hullColors P r = φ 1 → ¬ (1 < dot2 (hullVerts P r) z₁) := by
      intro r hcr hact
      have hr_int := (hdot_iff₁ r).mp hact
      have hb1 : b r'₁ ≤ b r := blockIndicesAux_mono 0 l hr_int.1 (by rw [hlen_l]; exact r.isLt)
      have hw1 : (![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) ⟨b r, hb_lt r⟩ = 1 := by refine φ.injective ?_; dsimp only [w₀] at hcol_of_b; rw [← hcol_of_b r, hcr]
      have hbr0 : b r = 0 := w25_facts.2.2.1 ⟨b r, hb_lt r⟩ hw1
      omega
    obtain ⟨a'A, ha'A_col, ha'A_dot⟩ := (realizesDualMask_ext_iff P S₁ z₁ hreal₁ (φ 1)).mp (by simp [S₁])
    have ha'A_not : ∀ r : Fin h, hullIdx P r ≠ a'A := fun r hr => by
      apply h1_missing r (by unfold hullColors; rw [hr, ha'A_col])
      unfold hullVerts; rw [hr]; exact ha'A_dot
    have ha'A_eq : a'A = a_A := h5col.2.2.2 a'A a_A ha'A_not haA_not (ha'A_col.trans haA_col.symm)
    have hslab_1 := hjA_spec z₁ hz₁ (ha'A_eq ▸ ha'A_dot) r'₁ r'₂ hdot_iff₁
    change b r'₁ ≤ j_A + 1 ∧ j_A ≤ b r'₂ at hslab_1
    have hbr1_5 : b r'₁ = 5 := by
      by_contra hne
      have : b r'₁ ≤ 4 := by omega
      exact (hno_14 4 this (by omega)).2 rfl
    have hbr2_5 : b r'₂ = 5 := by have := hb_lt r'₂; omega
    refine island_rule_contradiction P hgp htop h_shat hn6 (by omega) S₁ z₁ hz₁ hreal₁ r'₁ r'₂ hr'12 hdot_iff₁
      (φ 1) (φ 3) (φ.injective.ne (by decide)) (hno_adj25 1 3 (by decide) (by decide))
      (by simp [S₁]) (by simp [S₁]) ?_
    intro k hk1 hk2
    have hk_ge4 : 4 ≤ k.val := by change b r'₁ ≤ k.val + 1 at hk1; change k.val ≤ b r'₂ + 1 at hk2; omega
    have hk_eq : (compressedColors P)[k.val]'(by rw [hlen_cs]; exact k.isLt) = φ ((![1, 2, 0, 3, 4, 0] : Fin 6 → Fin 5) k) := by
      rw [← hw k, Equiv.apply_symm_apply]
    rw [hk_eq]
    have hwf := w25_facts.2.2.2.2.2.2 k hk_ge4
    exact ⟨φ.injective.ne hwf.1, φ.injective.ne hwf.2⟩

/-- Elimination of nine of the ten repeat placements for `n_Ω = 6`, leaving only `(1, 6)`. -/
theorem elim_n6_except_1_6 (P : DualConfig) (hgp : IsGenPos P)
    (htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < topEnv P t)
    (h_shat : ∀ m : Fin 5 → Bool, ∃ z : ℝ × ℝ, InOmega z ∧ RealizesDualMask P m z)
    (hn6 : hullBlockCount P = 6) :
    hullColors P ⟨0, by omega⟩ =
      hullColors P ⟨(topTiePts P).card, by omega⟩ := by
  by_contra hne_ends
  have h5col := hull_five_colors P hgp htop h_shat
  let h := (topTiePts P).card + 1
  let l := List.ofFn (hullColors P)
  let cs := compressedColors P
  have hcs_len : cs.length = 6 := hn6
  have hlen_l : l.length = h := List.length_ofFn
  let colAt : Fin 6 → Fin 5 := fun k => cs[k.val]'(by rw [hcs_len]; exact k.isLt)
  have hcs_def : compressedColors P = compressAdj l := rfl
  have hcolAt0 : colAt ⟨0, by omega⟩ = hullColors P ⟨0, by omega⟩ := by
    have hget := blockIndicesAux_getElem 0 l 0 (by rw [hlen_l]; omega)
    have hidx0 : (blockIndicesAux 0 l)[0]'(by rw [blockIndicesAux_length, hlen_l]; omega) = 0 :=
      blockIndicesAux_head 0 l (by rw [hlen_l]; omega)
    change (compressAdj l)[0]'(by rw [← hcs_def, hcs_len]; omega) = hullColors P ⟨0, by omega⟩
    have hget' : (compressAdj l)[0]'(by rw [← hcs_def, hcs_len]; omega) =
        l[0]'(by rw [hlen_l]; omega) :=
      (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hidx0)).trans hget
    rw [hget']
    dsimp [l]; rw [List.getElem_ofFn]; rfl
  have hcolAt5 : colAt ⟨5, by omega⟩ = hullColors P ⟨(topTiePts P).card, by omega⟩ := by
    have hlast := blockIndicesAux_last 0 l (by rw [hlen_l]; omega)
    have hget := blockIndicesAux_getElem 0 l (h - 1) (by rw [hlen_l]; omega)
    have hidx_eq : h - 1 = l.length - 1 := by omega
    have hval : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) =
        (blockIndicesAux 0 l)[l.length - 1]'(by rw [blockIndicesAux_length]; omega) := by congr 1
    have hidx5 : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) = 5 := by
      rw [hval, hlast]; change 0 + cs.length - 1 = 5; omega
    change (compressAdj l)[5]'(by rw [← hcs_def, hcs_len]; omega) =
        hullColors P ⟨(topTiePts P).card, by omega⟩
    have hget' : (compressAdj l)[5]'(by rw [← hcs_def, hcs_len]; omega) =
        l[h - 1]'(by rw [hlen_l]; omega) :=
      (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hidx5)).trans hget
    rw [hget']
    dsimp [l]; rw [List.getElem_ofFn]; congr 1
  have hcolAt_ne05 : colAt ⟨0, by omega⟩ ≠ colAt ⟨5, by omega⟩ := by
    rw [hcolAt0, hcolAt5]; exact hne_ends
  have hcolAt_adj : ∀ k : ℕ, (hk : k + 1 < 6) → colAt ⟨k, by omega⟩ ≠ colAt ⟨k + 1, hk⟩ := fun k hk =>
    compressAdj_adj_ne l k (by rw [← hcs_def, hcs_len]; exact hk)
  have hcolAt_surj : Function.Surjective colAt := by
    intro i
    obtain ⟨r, hr⟩ := h5col.1 i
    have hb := (blockIndicesAux_bounds 0 l r.val (by rw [hlen_l]; exact r.isLt)).2
    let k : Fin 6 := ⟨(blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt),
      by change _ < 0 + cs.length at hb; omega⟩
    refine ⟨k, ?_⟩
    have hget := blockIndicesAux_getElem 0 l r.val (by rw [hlen_l]; exact r.isLt)
    have hl_r : l[r.val]'(by rw [hlen_l]; exact r.isLt) = hullColors P r := by
      dsimp [l]; rw [List.getElem_ofFn]
    have hcol_eq : colAt k = hullColors P r := by
      dsimp [colAt, k, cs, compressedColors]
      exact (list_getElem_eq_of_idx (compressAdj l) _ _ (Nat.sub_zero _)).trans (hget.trans hl_r)
    rw [hcol_eq, hr]
  have hnot_inj : ¬ Function.Injective colAt := by
    intro hinj
    have := Fintype.card_le_of_injective colAt hinj
    simp at this
  obtain ⟨i₁, i₂, hcol_eq, hi12_ne⟩ := Function.not_injective_iff.mp hnot_inj
  wlog hi12_lt : i₁ < i₂
  · exact this P hgp htop h_shat hn6 hne_ends h5col hcs_len hlen_l hcs_def hcolAt0 hcolAt5 hcolAt_ne05 hcolAt_adj hcolAt_surj
      hnot_inj i₂ i₁ hcol_eq.symm hi12_ne.symm (lt_of_le_of_ne (not_lt.mp hi12_lt) hi12_ne.symm)
  have hi_gap : i₁.val + 2 ≤ i₂.val := by
    by_contra hlt
    have heq1 : i₂.val = i₁.val + 1 := by change i₁.val < i₂.val at hi12_lt; omega
    have hi2_eq : i₂ = ⟨i₁.val + 1, by omega⟩ := Fin.ext heq1
    rw [hi2_eq] at hcol_eq
    exact hcolAt_adj i₁.val (by omega) hcol_eq
  have hi_not05 : (i₁.val, i₂.val) ≠ (0, 5) := by
    intro hp
    have h0 : i₁ = ⟨0, by omega⟩ := Fin.ext (congrArg Prod.fst hp)
    have h5 : i₂ = ⟨5, by omega⟩ := Fin.ext (congrArg Prod.snd hp)
    rw [h0, h5] at hcol_eq
    exact hcolAt_ne05 hcol_eq
  let X : Fin 5 := colAt i₁
  have hX_unique : ∀ j : Fin 6, colAt j = X → j = i₁ ∨ j = i₂ := by
    intro j hj
    by_contra hnot
    push Not at hnot
    have hsub_range : (Finset.univ \ ({X} : Finset (Fin 5))) ⊆ (Finset.univ \ ({i₁, i₂, j} : Finset (Fin 6))).image colAt := by
      intro c hc
      obtain ⟨k, hk⟩ := hcolAt_surj c
      have hcX : c ≠ X := by simp at hc; exact hc
      have hki1 : k ≠ i₁ := fun h => hcX (by rw [← hk, h])
      have hki2 : k ≠ i₂ := fun h => hcX (by rw [← hk, h, ← hcol_eq])
      have hkj : k ≠ j := fun h => hcX (by rw [← hk, h, hj])
      exact Finset.mem_image.mpr ⟨k, by simp [hki1, hki2, hkj], hk⟩
    have hcard_lhs : (Finset.univ \ ({X} : Finset (Fin 5))).card = 4 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Finset.card_singleton]
    have hcard_rhs : ((Finset.univ \ ({i₁, i₂, j} : Finset (Fin 6))).image colAt).card ≤ 3 := by
      refine (Finset.card_image_le).trans ?_
      have h3 : ({i₁, i₂, j} : Finset (Fin 6)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · exact hnot.2.symm
        · simp [hi12_lt.ne, hnot.1.symm]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h3]
    have := Finset.card_le_card hsub_range
    omega
  let rem : List (Fin 6) := (List.finRange 6).filter fun k => k != i₁ && k != i₂
  have hrem_len : rem.length = 4 := by
    have hnd : rem.Nodup := (List.nodup_finRange 6).filter _
    have hcard : rem.toFinset = Finset.univ \ ({i₁, i₂} : Finset (Fin 6)) := by
      ext k; simp [rem, Bool.and_eq_true, bne_iff_ne]
    rw [← List.toFinset_card_of_nodup hnd, hcard, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin, Finset.card_pair hi12_lt.ne]
  have hrem_ne : ∀ a : Fin 4, rem[a.val]'(by rw [hrem_len]; exact a.isLt) ≠ i₁ ∧
      rem[a.val]'(by rw [hrem_len]; exact a.isLt) ≠ i₂ := by
    intro a
    have hm := List.getElem_mem (by rw [hrem_len]; exact a.isLt : a.val < rem.length)
    simp only [rem, List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true, bne_iff_ne] at hm
    exact hm
  have hrem_inj : ∀ a b : Fin 4,
      colAt (rem[a.val]'(by rw [hrem_len]; exact a.isLt)) =
      colAt (rem[b.val]'(by rw [hrem_len]; exact b.isLt)) → a = b := by
    intro a b hab
    by_contra hne
    let ka := rem[a.val]'(by rw [hrem_len]; exact a.isLt)
    let kb := rem[b.val]'(by rw [hrem_len]; exact b.isLt)
    have hnd : rem.Nodup := (List.nodup_finRange 6).filter _
    have hka_ne_kb : ka ≠ kb := fun heq => hne (Fin.ext ((hnd.getElem_inj_iff).mp heq))
    have hka_neX : colAt ka ≠ X := fun h => by
      rcases hX_unique ka h with h1 | h2
      · exact (hrem_ne a).1 h1
      · exact (hrem_ne a).2 h2
    have hsub_range : (Finset.univ \ ({X, colAt ka} : Finset (Fin 5))) ⊆
        (Finset.univ \ ({i₁, i₂, ka, kb} : Finset (Fin 6))).image colAt := by
      intro c hc
      obtain ⟨k, hk⟩ := hcolAt_surj c
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and, not_or] at hc
      have hki1 : k ≠ i₁ := fun h => hc.1 (by rw [← hk, h])
      have hki2 : k ≠ i₂ := fun h => hc.1 (by rw [← hk, h, ← hcol_eq])
      have hkka : k ≠ ka := fun h => hc.2 (by rw [← hk, h])
      have hkkb : k ≠ kb := fun h => hc.2 (by rw [← hk, h, ← hab])
      exact Finset.mem_image.mpr ⟨k, by simp [hki1, hki2, hkka, hkkb], hk⟩
    have hcard_lhs : (Finset.univ \ ({X, colAt ka} : Finset (Fin 5))).card = 3 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_pair hka_neX.symm]
    have hcard_rhs : ((Finset.univ \ ({i₁, i₂, ka, kb} : Finset (Fin 6))).image colAt).card ≤ 2 := by
      refine (Finset.card_image_le).trans ?_
      have h4 : ({i₁, i₂, ka, kb} : Finset (Fin 6)).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hka_ne_kb]
        · intro hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hm | hm
          · exact (hrem_ne a).2 hm.symm
          · exact (hrem_ne b).2 hm.symm
        · intro hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with hm | hm | hm
          · exact hi12_lt.ne hm
          · exact (hrem_ne a).1 hm.symm
          · exact (hrem_ne b).1 hm.symm
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h4]
    have := Finset.card_le_card hsub_range
    omega
  let ψ : Fin 5 → Fin 5 := fun c =>
    if h0 : c.val = 0 then X
    else colAt (rem[c.val - 1]'(by rw [hrem_len]; omega))
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0
    · exact Fin.ext (ha0.trans hb0.symm)
    · exfalso
      dsimp only [ψ] at hab
      rw [dif_pos ha0, dif_neg hb0] at hab
      rcases hX_unique _ hab.symm with h1 | h2
      · exact (hrem_ne ⟨b.val - 1, by omega⟩).1 h1
      · exact (hrem_ne ⟨b.val - 1, by omega⟩).2 h2
    · exfalso
      dsimp only [ψ] at hab
      rw [dif_neg ha0, dif_pos hb0] at hab
      rcases hX_unique _ hab with h1 | h2
      · exact (hrem_ne ⟨a.val - 1, by omega⟩).1 h1
      · exact (hrem_ne ⟨a.val - 1, by omega⟩).2 h2
    · dsimp only [ψ] at hab
      rw [dif_neg ha0, dif_neg hb0] at hab
      have heq' := hrem_inj ⟨a.val - 1, by omega⟩ ⟨b.val - 1, by omega⟩ hab
      have hv := congrArg Fin.val heq'
      dsimp at hv
      exact Fin.ext (by omega)
  have hψ_surj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψ_inj
  let φ : Fin 5 ≃ Fin 5 := Equiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩
  have hφ_X : φ.symm X = 0 := by
    rw [Equiv.symm_apply_eq]; dsimp [φ, ψ]
  have hφ_rem : ∀ (i : ℕ) (hi : i < 4),
      φ.symm (colAt (rem[i]'(by rw [hrem_len]; exact hi))) = ⟨i + 1, by omega⟩ := by
    intro i hi
    rw [Equiv.symm_apply_eq]
    dsimp [φ, ψ]
    exact congrArg colAt (list_getElem_eq_of_idx rem _ _ rfl)
  -- Check X has NO non-hull vector:
  have hX_no_nonhull : ∀ a : Fin 10, vecColor a = X → ∃ r : Fin h, hullIdx P r = a := by
    intro a ha_col
    obtain ⟨r₁, hr1⟩ : ∃ r : Fin h, (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt) = i₁.val := by
      have h0' : (blockIndicesAux 0 l)[0]'(by rw [blockIndicesAux_length, hlen_l]; omega) = 0 :=
        blockIndicesAux_head 0 l (by rw [hlen_l]; omega)
      have hL' : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) = 5 := by
        have hlast := blockIndicesAux_last 0 l (by rw [hlen_l]; omega)
        have hidx_eq : h - 1 = l.length - 1 := by omega
        have hval : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) =
            (blockIndicesAux 0 l)[l.length - 1]'(by rw [blockIndicesAux_length]; omega) := by congr 1
        rw [hval, hlast]; change 0 + cs.length - 1 = 5; omega
      obtain ⟨r, _, _, hr_eq⟩ := blockIndicesAux_surj_interval 0 l (by omega : 0 ≤ h - 1) (by rw [hlen_l]; omega)
        i₁.val (by omega) (by have := i₁.isLt; omega)
      exact ⟨⟨r, by omega⟩, hr_eq (by rw [hlen_l]; omega)⟩
    obtain ⟨r₂, hr2⟩ : ∃ r : Fin h, (blockIndicesAux 0 l)[r.val]'(by rw [blockIndicesAux_length, hlen_l]; exact r.isLt) = i₂.val := by
      have h0' : (blockIndicesAux 0 l)[0]'(by rw [blockIndicesAux_length, hlen_l]; omega) = 0 :=
        blockIndicesAux_head 0 l (by rw [hlen_l]; omega)
      have hL' : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) = 5 := by
        have hlast := blockIndicesAux_last 0 l (by rw [hlen_l]; omega)
        have hidx_eq : h - 1 = l.length - 1 := by omega
        have hval : (blockIndicesAux 0 l)[h - 1]'(by rw [blockIndicesAux_length, hlen_l]; omega) =
            (blockIndicesAux 0 l)[l.length - 1]'(by rw [blockIndicesAux_length]; omega) := by congr 1
        rw [hval, hlast]; change 0 + cs.length - 1 = 5; omega
      obtain ⟨r, _, _, hr_eq⟩ := blockIndicesAux_surj_interval 0 l (by omega : 0 ≤ h - 1) (by rw [hlen_l]; omega)
        i₂.val (by omega) (by have := i₂.isLt; omega)
      exact ⟨⟨r, by omega⟩, hr_eq (by rw [hlen_l]; omega)⟩
    have hr12_ne : r₁ ≠ r₂ := fun h => by subst h; have := hr1.symm.trans hr2; exact hi12_lt.ne (Fin.ext this)
    have hidx_ne : hullIdx P r₁ ≠ hullIdx P r₂ := (hullVerts_spec P hgp htop).2.2.1.ne hr12_ne
    have hcol1 : vecColor (hullIdx P r₁) = X := by
      have hget := blockIndicesAux_getElem 0 l r₁.val (by rw [hlen_l]; exact r₁.isLt)
      have hl1 : l[r₁.val]'(by rw [hlen_l]; exact r₁.isLt) = hullColors P r₁ := by
        dsimp [l]; rw [List.getElem_ofFn]
      have h1 : colAt i₁ = hullColors P r₁ := by
        dsimp [colAt, cs, compressedColors]
        exact (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hr1)).trans (hget.trans hl1)
      exact h1.symm
    have hcol2 : vecColor (hullIdx P r₂) = X := by
      have hget := blockIndicesAux_getElem 0 l r₂.val (by rw [hlen_l]; exact r₂.isLt)
      have hl2 : l[r₂.val]'(by rw [hlen_l]; exact r₂.isLt) = hullColors P r₂ := by
        dsimp [l]; rw [List.getElem_ofFn]
      have h2 : colAt i₂ = hullColors P r₂ := by
        dsimp [colAt, cs, compressedColors]
        exact (list_getElem_eq_of_idx (compressAdj l) _ _ (by rw [Nat.sub_zero]; exact hr2)).trans (hget.trans hl2)
      exact (hcol_eq.trans h2).symm
    have h_two : a = hullIdx P r₁ ∨ a = hullIdx P r₂ := by
      have hc0 := congrArg Fin.val ha_col
      have hc1 := congrArg Fin.val hcol1
      have hc2 := congrArg Fin.val hcol2
      have hne12 := Fin.val_ne_of_ne hidx_ne
      dsimp [vecColor] at hc0 hc1 hc2
      by_contra hno; push Not at hno
      have h1 := Fin.val_ne_of_ne hno.1
      have h2 := Fin.val_ne_of_ne hno.2
      omega
    rcases h_two with rfl | rfl
    · exact ⟨r₁, rfl⟩
    · exact ⟨r₂, rfl⟩
  have hX_no' : ∀ a : Fin 10, vecColor a = φ 0 → ∃ r : Fin h, hullIdx P r = a := fun a ha =>
    hX_no_nonhull a (by simpa [φ, ψ] using ha)
  have hrem_get : ∀ (xs : List (Fin 6)) (hxs : rem = xs) (i : ℕ) (hi : i < 4),
      rem[i]'(by rw [hrem_len]; exact hi) = xs[i]'(by rw [← hxs, hrem_len]; exact hi) := by
    intro xs hxs i hi; subst hxs; rfl
  have hf0 := hφ_rem 0 (by omega)
  have hf1 := hφ_rem 1 (by omega)
  have hf2 := hφ_rem 2 (by omega)
  have hf3 := hφ_rem 3 (by omega)
  have hφ_X2 : φ.symm (colAt i₂) = 0 := by rw [← hcol_eq]; exact hφ_X
  have hcases := word6_cases i₁ i₂ hi12_lt hi_gap hi_not05
  dsimp only at hcases
  rcases hcases with ⟨rfl, rfl, hrem⟩ | ⟨rfl, rfl, hrem⟩ | ⟨rfl, rfl, hrem⟩ |
      ⟨rfl, rfl, hrem⟩ | ⟨rfl, rfl, hrem⟩ | ⟨rfl, rfl, hrem⟩ |
      ⟨rfl, rfl, hrem⟩ | ⟨rfl, rfl, hrem⟩ | ⟨rfl, rfl, hrem⟩
  · have hg0 := hrem_get [1, 3, 4, 5] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [1, 3, 4, 5] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [1, 3, 4, 5] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [1, 3, 4, 5] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![0, 1, 0, 2, 3, 4] [1, 2, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hφ_X
    · exact hf0
    · exact hφ_X2
    · exact hf1
    · exact hf2
    · exact hf3
  · have hg0 := hrem_get [1, 2, 4, 5] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [1, 2, 4, 5] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [1, 2, 4, 5] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [1, 2, 4, 5] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_orbit03 P hgp htop h_shat hn6 φ hX_no' (fun k => ?_)
    fin_cases k
    · exact hφ_X
    · exact hf0
    · exact hf1
    · exact hφ_X2
    · exact hf2
    · exact hf3
  · have hg0 := hrem_get [1, 2, 3, 5] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [1, 2, 3, 5] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [1, 2, 3, 5] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [1, 2, 3, 5] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![0, 1, 2, 3, 0, 4] [1, 3, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hφ_X
    · exact hf0
    · exact hf1
    · exact hf2
    · exact hφ_X2
    · exact hf3
  · have hg0 := hrem_get [0, 2, 4, 5] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [0, 2, 4, 5] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [0, 2, 4, 5] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [0, 2, 4, 5] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![1, 0, 2, 0, 3, 4] [1, 2, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hf0
    · exact hφ_X
    · exact hf1
    · exact hφ_X2
    · exact hf2
    · exact hf3
  · have hg0 := hrem_get [0, 2, 3, 5] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [0, 2, 3, 5] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [0, 2, 3, 5] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [0, 2, 3, 5] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![1, 0, 2, 3, 0, 4] [1, 3, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hf0
    · exact hφ_X
    · exact hf1
    · exact hf2
    · exact hφ_X2
    · exact hf3
  · have hg0 := hrem_get [0, 2, 3, 4] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [0, 2, 3, 4] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [0, 2, 3, 4] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [0, 2, 3, 4] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![1, 0, 2, 3, 4, 0] [1, 2, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hf0
    · exact hφ_X
    · exact hf1
    · exact hf2
    · exact hf3
    · exact hφ_X2
  · have hg0 := hrem_get [0, 1, 3, 5] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [0, 1, 3, 5] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [0, 1, 3, 5] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [0, 1, 3, 5] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![1, 2, 0, 3, 0, 4] [1, 3, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hf0
    · exact hf1
    · exact hφ_X
    · exact hf2
    · exact hφ_X2
    · exact hf3
  · have hg0 := hrem_get [0, 1, 3, 4] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [0, 1, 3, 4] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [0, 1, 3, 4] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [0, 1, 3, 4] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_orbit25 P hgp htop h_shat hn6 φ hX_no' (fun k => ?_)
    fin_cases k
    · exact hf0
    · exact hf1
    · exact hφ_X
    · exact hf2
    · exact hf3
    · exact hφ_X2
  · have hg0 := hrem_get [0, 1, 2, 4] hrem 0 (by decide); dsimp at hg0; rw [hg0] at hf0
    have hg1 := hrem_get [0, 1, 2, 4] hrem 1 (by decide); dsimp at hg1; rw [hg1] at hf1
    have hg2 := hrem_get [0, 1, 2, 4] hrem 2 (by decide); dsimp at hg2; rw [hg2] at hf2
    have hg3 := hrem_get [0, 1, 2, 4] hrem 3 (by decide); dsimp at hg3; rw [hg3] at hf3
    refine elim_n6_word_island P hgp htop h_shat hn6 φ ![1, 2, 3, 0, 4, 0] [1, 3, 4] (fun k => ?_) (by decide)
    fin_cases k
    · exact hf0
    · exact hf1
    · exact hf2
    · exact hφ_X
    · exact hf3
    · exact hφ_X2

end CaseA
end
