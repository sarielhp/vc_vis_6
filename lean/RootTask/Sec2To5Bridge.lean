import Mathlib
import RootTask.PolygonDefs
import RootTask.PolygonEnclosureCore
import RootTask.SixWedges
import RootTask.Sec5HalfPlane
import RootTask.Sec6Targets
import RootTask.ArrangementBounds

open scoped Classical BigOperators
open Finset

noncomputable section

namespace Sec2To5Bridge

/-!
# Sections 2–5 to Section 6 Interface Glue (`mk_sec2To5Interface`)

Connects the proved Sections 2–5 theorems (`PolygonCore`, `SixWedges`, `Sec5HP`,
and `ArrangementBounds`) to all 12 fields of `Sec2To5Interface P S w`.
-/

/-! ## Part 1: Wedge Intersection & Subwedge Helpers for `wedge_extraction` -/

private lemma openWedge_intersection_at_apex (R₀ U : OpenWedge)
    (hy : R₀.y = U.y) (p₀ : ℝ × ℝ) (hpR : R₀.MemOpen p₀) (hpU : U.MemOpen p₀) :
    ∃ R : OpenWedge, R.y = U.y ∧
      (∀ z : ℝ × ℝ, R.MemOpen z ↔ R₀.MemOpen z ∧ U.MemOpen z) ∧
      (∀ z : ℝ × ℝ, R.MemExt z ↔ R₀.MemExt z ∨ U.MemExt z) := by
  let y := U.y
  let e₁ : ℝ × ℝ := (p₀.1 - y.1, p₀.2 - y.2)
  let e₂ : ℝ × ℝ := (-e₁.2, e₁.1)
  have he1_sq : 0 < e₁.1 ^ 2 + e₁.2 ^ 2 := by
    by_contra hle
    have hle' : e₁.1 ^ 2 + e₁.2 ^ 2 ≤ 0 := not_lt.mp hle
    have hs1 : e₁.1 ^ 2 = 0 := by nlinarith [sq_nonneg e₁.1, sq_nonneg e₁.2]
    have hs2 : e₁.2 ^ 2 = 0 := by nlinarith [sq_nonneg e₁.1, sq_nonneg e₁.2]
    have h0 : e₁.1 = 0 ∧ e₁.2 = 0 := ⟨sq_eq_zero_iff.mp hs1, sq_eq_zero_iff.mp hs2⟩
    have h1 := hpU.1
    change 0 < U.u₁.1 * e₁.1 + U.u₁.2 * e₁.2 at h1
    rw [h0.1, h0.2, mul_zero, mul_zero, add_zero] at h1
    exact lt_irrefl 0 h1
  let dotE1 : ℝ × ℝ → ℝ := fun u => u.1 * e₁.1 + u.2 * e₁.2
  let dotE2 : ℝ × ℝ → ℝ := fun u => u.1 * e₂.1 + u.2 * e₂.2
  have hU1 : 0 < dotE1 U.u₁ := by simpa [dotE1, e₁, y] using hpU.1
  have hU2 : 0 < dotE1 U.u₂ := by simpa [dotE1, e₁, y] using hpU.2
  have hR1 : 0 < dotE1 R₀.u₁ := by simpa [dotE1, e₁, y, hy] using hpR.1
  have hR2 : 0 < dotE1 R₀.u₂ := by simpa [dotE1, e₁, y, hy] using hpR.2
  let k : ℝ × ℝ → ℝ := fun u => dotE2 u / dotE1 u
  have hdet_iff : ∀ u v : ℝ × ℝ, 0 < dotE1 u → 0 < dotE1 v →
      (0 < u.1 * v.2 - u.2 * v.1 ↔ k u < k v) := by
    intro u v hu hv
    have hid : (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.1 * v.2 - u.2 * v.1) =
        dotE1 u * dotE2 v - dotE2 u * dotE1 v := by
      dsimp [dotE1, dotE2, e₁, e₂]; ring
    dsimp [k]
    rw [div_lt_div_iff₀ hu hv]
    constructor
    · intro hdet; have := mul_pos he1_sq hdet; linarith
    · intro hlt; have hmul : 0 < (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.1 * v.2 - u.2 * v.1) := by linarith
      exact pos_of_mul_pos_right hmul (le_of_lt he1_sq)
  have hkU : k U.u₁ < k U.u₂ := (hdet_iff U.u₁ U.u₂ hU1 hU2).mp U.h_nondeg
  have hkR : k R₀.u₁ < k R₀.u₂ := (hdet_iff R₀.u₁ R₀.u₂ hR1 hR2).mp R₀.h_nondeg
  let u₁s : ℝ × ℝ := if k U.u₁ ≤ k R₀.u₁ then U.u₁ else R₀.u₁
  let u₂s : ℝ × ℝ := if k U.u₂ ≤ k R₀.u₂ then R₀.u₂ else U.u₂
  have hu1s_dot : 0 < dotE1 u₁s := by dsimp [u₁s]; split_ifs <;> assumption
  have hu2s_dot : 0 < dotE1 u₂s := by dsimp [u₂s]; split_ifs <;> assumption
  have hku1s : k u₁s ≤ k U.u₁ ∧ k u₁s ≤ k R₀.u₁ := by
    dsimp [u₁s]; split_ifs with h
    · exact ⟨le_rfl, h⟩
    · exact ⟨le_of_lt (not_le.mp h), le_rfl⟩
  have hku2s : k U.u₂ ≤ k u₂s ∧ k R₀.u₂ ≤ k u₂s := by
    dsimp [u₂s]; split_ifs with h
    · exact ⟨h, le_rfl⟩
    · exact ⟨le_rfl, le_of_lt (not_le.mp h)⟩
  have hk12 : k u₁s < k u₂s := lt_of_le_of_lt hku1s.1 (lt_of_lt_of_le hkU hku2s.1)
  let R : OpenWedge :=
    { y := y
      u₁ := u₁s
      u₂ := u₂s
      h_nondeg := (hdet_iff u₁s u₂s hu1s_dot hu2s_dot).mpr hk12 }
  have hcomb : ∀ u : ℝ × ℝ, 0 < dotE1 u → k u₁s ≤ k u → k u ≤ k u₂s →
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (0 < α ∨ 0 < β) ∧
        ∀ z : ℝ × ℝ, u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2) =
          α * (u₁s.1 * (z.1 - y.1) + u₁s.2 * (z.2 - y.2)) +
          β * (u₂s.1 * (z.1 - y.1) + u₂s.2 * (z.2 - y.2)) := by
    intro u hu hlo hhi
    let den := k u₂s - k u₁s
    have hden : 0 < den := sub_pos.mpr hk12
    let t := (k u - k u₁s) / den
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (le_of_lt hden)
    have hk12_ne : k u₂s - k u₁s ≠ 0 := sub_ne_zero.mpr (ne_of_gt hk12)
    have ht1 : 0 ≤ 1 - t := by
      have : 1 - t = (k u₂s - k u) / den := by
        dsimp [t, den]; field_simp [hk12_ne]; ring
      rw [this]; exact div_nonneg (sub_nonneg.mpr hhi) (le_of_lt hden)
    let α := dotE1 u * (1 - t) / dotE1 u₁s
    let β := dotE1 u * t / dotE1 u₂s
    refine ⟨α, β, div_nonneg (mul_nonneg (le_of_lt hu) ht1) (le_of_lt hu1s_dot),
      div_nonneg (mul_nonneg (le_of_lt hu) ht0) (le_of_lt hu2s_dot), ?_, fun z => ?_⟩
    · by_cases ht_zero : t = 0
      · left; dsimp [α]; rw [ht_zero, sub_zero, mul_one]; exact div_pos hu hu1s_dot
      · right; dsimp [β]; exact div_pos (mul_pos hu (lt_of_le_of_ne ht0 (Ne.symm ht_zero))) hu2s_dot
    · have hbasis : ∀ v : ℝ × ℝ, (e₁.1 ^ 2 + e₁.2 ^ 2) * v.1 = dotE1 v * e₁.1 + dotE2 v * e₂.1 ∧
          (e₁.1 ^ 2 + e₁.2 ^ 2) * v.2 = dotE1 v * e₁.2 + dotE2 v * e₂.2 := by
        intro v; constructor <;> dsimp [dotE1, dotE2, e₁, e₂] <;> ring
      have hsum_e1 : α * dotE1 u₁s + β * dotE1 u₂s = dotE1 u := by
        dsimp [α, β]; field_simp [ne_of_gt hu1s_dot, ne_of_gt hu2s_dot]; ring
      have hsum_e2 : α * dotE2 u₁s + β * dotE2 u₂s = dotE2 u := by
        have hku1 : dotE2 u₁s = k u₁s * dotE1 u₁s := by
          dsimp [k]; rw [div_mul_cancel₀ _ (ne_of_gt hu1s_dot)]
        have hku2 : dotE2 u₂s = k u₂s * dotE1 u₂s := by
          dsimp [k]; rw [div_mul_cancel₀ _ (ne_of_gt hu2s_dot)]
        have hku : dotE2 u = k u * dotE1 u := by
          dsimp [k]; rw [div_mul_cancel₀ _ (ne_of_gt hu)]
        rw [hku1, hku2, hku]
        dsimp [α, β, t, den]
        field_simp [ne_of_gt hu1s_dot, ne_of_gt hu2s_dot, hk12_ne]
        ring
      have h1 : (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.1 - (α * u₁s.1 + β * u₂s.1)) = 0 := by
        have hv1 := (hbasis u).1
        have hw1 := (hbasis u₁s).1
        have hw2 := (hbasis u₂s).1
        linear_combination hv1 - α * hw1 - β * hw2 - e₁.1 * hsum_e1 - e₂.1 * hsum_e2
      have h2 : (e₁.1 ^ 2 + e₁.2 ^ 2) * (u.2 - (α * u₁s.2 + β * u₂s.2)) = 0 := by
        have hv2 := (hbasis u).2
        have hw1 := (hbasis u₁s).2
        have hw2 := (hbasis u₂s).2
        linear_combination hv2 - α * hw1 - β * hw2 - e₁.2 * hsum_e1 - e₂.2 * hsum_e2
      have hu1_eq : u.1 = α * u₁s.1 + β * u₂s.1 := by
        have := (mul_eq_zero.mp h1).resolve_left (ne_of_gt he1_sq); linarith
      have hu2_eq : u.2 = α * u₁s.2 + β * u₂s.2 := by
        have := (mul_eq_zero.mp h2).resolve_left (ne_of_gt he1_sq); linarith
      rw [hu1_eq, hu2_eq]; ring
  have hcU1 := hcomb U.u₁ hU1 hku1s.1 (le_trans (le_of_lt hkU) hku2s.1)
  have hcU2 := hcomb U.u₂ hU2 (le_trans hku1s.1 (le_of_lt hkU)) hku2s.1
  have hcR1 := hcomb R₀.u₁ hR1 hku1s.2 (le_trans (le_of_lt hkR) hku2s.2)
  have hcR2 := hcomb R₀.u₂ hR2 (le_trans hku1s.2 (le_of_lt hkR)) hku2s.2
  have himp_pos : ∀ {u : ℝ × ℝ} {z : ℝ × ℝ},
      (∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (0 < α ∨ 0 < β) ∧
        ∀ w : ℝ × ℝ, u.1 * (w.1 - y.1) + u.2 * (w.2 - y.2) =
          α * (u₁s.1 * (w.1 - y.1) + u₁s.2 * (w.2 - y.2)) +
          β * (u₂s.1 * (w.1 - y.1) + u₂s.2 * (w.2 - y.2))) →
      R.MemOpen z → 0 < u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2) := by
    rintro u z ⟨α, β, hα, hβ, hpos, heq⟩ ⟨hz1, hz2⟩
    change 0 < u₁s.1 * (z.1 - y.1) + u₁s.2 * (z.2 - y.2) at hz1
    change 0 < u₂s.1 * (z.1 - y.1) + u₂s.2 * (z.2 - y.2) at hz2
    rw [heq z]
    rcases hpos with hαp | hβp
    · linarith [mul_pos hαp hz1, mul_nonneg hβ (le_of_lt hz2)]
    · linarith [mul_nonneg hα (le_of_lt hz1), mul_pos hβp hz2]
  have himp_neg : ∀ {u : ℝ × ℝ} {z : ℝ × ℝ},
      (∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ (0 < α ∨ 0 < β) ∧
        ∀ w : ℝ × ℝ, u.1 * (w.1 - y.1) + u.2 * (w.2 - y.2) =
          α * (u₁s.1 * (w.1 - y.1) + u₁s.2 * (w.2 - y.2)) +
          β * (u₂s.1 * (w.1 - y.1) + u₂s.2 * (w.2 - y.2))) →
      u.1 * (z.1 - y.1) + u.2 * (z.2 - y.2) < 0 → R.MemExt z := by
    rintro u z ⟨α, β, hα, hβ, _, heq⟩ hneg
    rw [heq z] at hneg
    by_contra hno
    dsimp [OpenWedge.MemExt, R] at hno
    push Not at hno
    linarith [mul_nonneg hα hno.1, mul_nonneg hβ hno.2]
  refine ⟨R, rfl, fun z => ⟨fun hz => ?_, fun ⟨hzR, hzU⟩ => ?_⟩, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change 0 < R₀.u₁.1 * (z.1 - R₀.y.1) + R₀.u₁.2 * (z.2 - R₀.y.2); rw [hy]; exact himp_pos hcR1 hz
    · change 0 < R₀.u₂.1 * (z.1 - R₀.y.1) + R₀.u₂.2 * (z.2 - R₀.y.2); rw [hy]; exact himp_pos hcR2 hz
    · exact himp_pos hcU1 hz
    · exact himp_pos hcU2 hz
  · constructor
    · dsimp [R, u₁s]; split_ifs
      · exact hzU.1
      · change 0 < R₀.u₁.1 * (z.1 - y.1) + R₀.u₁.2 * (z.2 - y.2); dsimp [y]; rw [← hy]; exact hzR.1
    · dsimp [R, u₂s]; split_ifs
      · change 0 < R₀.u₂.1 * (z.1 - y.1) + R₀.u₂.2 * (z.2 - y.2); dsimp [y]; rw [← hy]; exact hzR.2
      · exact hzU.2
  · rcases hz with hz1 | hz2
    · dsimp [R, u₁s] at hz1; split_ifs at hz1
      · exact Or.inr (Or.inl hz1)
      · exact Or.inl (Or.inl (by change R₀.u₁.1 * (z.1 - R₀.y.1) + R₀.u₁.2 * (z.2 - R₀.y.2) < 0; rw [hy]; exact hz1))
    · dsimp [R, u₂s] at hz2; split_ifs at hz2
      · exact Or.inl (Or.inr (by change R₀.u₂.1 * (z.1 - R₀.y.1) + R₀.u₂.2 * (z.2 - R₀.y.2) < 0; rw [hy]; exact hz2))
      · exact Or.inr (Or.inr hz2)
  · rcases hz with (hzR1 | hzR2) | (hzU1 | hzU2)
    · exact himp_neg hcR1 (by dsimp [y]; rw [← hy]; exact hzR1)
    · exact himp_neg hcR2 (by dsimp [y]; rw [← hy]; exact hzR2)
    · exact himp_neg hcU1 hzU1
    · exact himp_neg hcU2 hzU2

private lemma pos_sub_of_eps_abs {A B ε : ℝ} (hε : 0 ≤ ε) (h : ε * |B| < A) :
    0 < A - ε * B ∧ 0 < A + ε * B := by
  have h1 : ε * B ≤ ε * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hε
  have h2 : -(ε * |B|) ≤ ε * B := by linarith [mul_le_mul_of_nonneg_left (neg_abs_le B) hε]
  exact ⟨by linarith, by linarith⟩

private lemma subwedge_from_ray (U : OpenWedge) (F : Finset (ℝ × ℝ)) (r₀ : ℝ × ℝ)
    (hr₀_1 : 0 < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2)
    (hr₀_2 : 0 < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2)
    (hx_det_ne : ∀ x ∈ F, (x.1 - U.y.1) * r₀.2 - (x.2 - U.y.2) * r₀.1 ≠ 0) :
    ∃ R : OpenWedge, R.y = U.y ∧ (∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z) ∧
      (∀ x ∈ F, R.MemExt x) := by
  let y := U.y
  let nr0sq : ℝ := r₀.1 ^ 2 + r₀.2 ^ 2
  have hnr0 : 0 < nr0sq := by
    by_contra hle
    have hle' : nr0sq ≤ 0 := not_lt.mp hle
    have hs1 : r₀.1 ^ 2 = 0 := by dsimp [nr0sq] at hle'; nlinarith [sq_nonneg r₀.1, sq_nonneg r₀.2]
    have hs2 : r₀.2 ^ 2 = 0 := by dsimp [nr0sq] at hle'; nlinarith [sq_nonneg r₀.1, sq_nonneg r₀.2]
    have h0 : r₀.1 = 0 ∧ r₀.2 = 0 := ⟨sq_eq_zero_iff.mp hs1, sq_eq_zero_iff.mp hs2⟩
    rw [h0.1, h0.2, mul_zero, mul_zero, add_zero] at hr₀_1
    exact lt_irrefl 0 hr₀_1
  let εU1 : ℝ := (U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2) / (|U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| + 1)
  let εU2 : ℝ := (U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2) / (|U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| + 1)
  let εF : ℝ := if hne : F.Nonempty then
    F.inf' hne (fun x => |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| /
      (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1)) else 1
  have hεU1 : 0 < εU1 := div_pos hr₀_1 (by positivity)
  have hεU2 : 0 < εU2 := div_pos hr₀_2 (by positivity)
  have hεF : 0 < εF := by
    dsimp [εF]
    split_ifs with hne
    · rw [Finset.lt_inf'_iff]
      intro x hx
      exact div_pos (abs_pos.mpr (hx_det_ne x hx)) (by positivity)
    · exact zero_lt_one
  obtain ⟨ε, hε_pos, hε1, hε2, hε_lt_F⟩ :
      ∃ ε : ℝ, 0 < ε ∧ ε < εU1 ∧ ε < εU2 ∧ ε < εF := by
    refine ⟨min 1 (min εU1 (min εU2 εF)) / 2, by positivity, ?_, ?_, ?_⟩
    · have := min_le_left εU1 (min εU2 εF)
      have := min_le_right 1 (min εU1 (min εU2 εF))
      linarith
    · have := min_le_left εU2 εF
      have := min_le_right εU1 (min εU2 εF)
      have := min_le_right 1 (min εU1 (min εU2 εF))
      linarith
    · have := min_le_right εU2 εF
      have := min_le_right εU1 (min εU2 εF)
      have := min_le_right 1 (min εU1 (min εU2 εF))
      linarith
  have hmul_U1 : ε * |U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 := by
    have hlt : ε * (|U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| + 1) < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 :=
      (lt_div_iff₀ (by positivity : 0 < |U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1| + 1)).mp hε1
    linarith
  have hmul_U2 : ε * |U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 := by
    have hlt : ε * (|U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| + 1) < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 :=
      (lt_div_iff₀ (by positivity : 0 < |U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1| + 1)).mp hε2
    linarith
  let n₁ : ℝ × ℝ := (r₀.2 + ε * r₀.1, -r₀.1 + ε * r₀.2)
  let n₂ : ℝ × ℝ := (-r₀.2 + ε * r₀.1, r₀.1 + ε * r₀.2)
  have hdet_n : 0 < n₁.1 * n₂.2 - n₁.2 * n₂.1 := by
    have hid : n₁.1 * n₂.2 - n₁.2 * n₂.1 = 2 * ε * nr0sq := by dsimp [n₁, n₂, nr0sq]; ring
    rw [hid]; positivity
  let R : OpenWedge :=
    { y := y
      u₁ := n₁
      u₂ := n₂
      h_nondeg := hdet_n }
  refine ⟨R, rfl, fun z hz => ?_, fun x hx => ?_⟩
  · let d₁ : ℝ × ℝ := (r₀.1 - ε * r₀.2, r₀.2 + ε * r₀.1)
    let d₂ : ℝ × ℝ := (r₀.1 + ε * r₀.2, r₀.2 - ε * r₀.1)
    have hz1 := hz.1
    have hz2 := hz.2
    change 0 < n₁.1 * (z.1 - y.1) + n₁.2 * (z.2 - y.2) at hz1
    change 0 < n₂.1 * (z.1 - y.1) + n₂.2 * (z.2 - y.2) at hz2
    let α := (n₂.1 * (z.1 - y.1) + n₂.2 * (z.2 - y.2)) / (2 * ε * nr0sq)
    let β := (n₁.1 * (z.1 - y.1) + n₁.2 * (z.2 - y.2)) / (2 * ε * nr0sq)
    have hα : 0 < α := div_pos hz2 (by positivity)
    have hβ : 0 < β := div_pos hz1 (by positivity)
    have hden_ne : 2 * ε * nr0sq ≠ 0 := ne_of_gt (by positivity)
    have hzx : z.1 - y.1 = α * d₁.1 + β * d₂.1 := by
      dsimp [α, β, d₁, d₂, n₁, n₂]; field_simp [hden_ne]; dsimp [nr0sq]; ring
    have hzy : z.2 - y.2 = α * d₁.2 + β * d₂.2 := by
      dsimp [α, β, d₁, d₂, n₁, n₂]; field_simp [hden_ne]; dsimp [nr0sq]; ring
    have hd1_U1 : 0 < U.u₁.1 * d₁.1 + U.u₁.2 * d₁.2 := by
      have hid : U.u₁.1 * d₁.1 + U.u₁.2 * d₁.2 =
          (U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2) + ε * (U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1) := by
        dsimp [d₁]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U1).2
    have hd2_U1 : 0 < U.u₁.1 * d₂.1 + U.u₁.2 * d₂.2 := by
      have hid : U.u₁.1 * d₂.1 + U.u₁.2 * d₂.2 =
          (U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2) - ε * (U.u₁.1 * (-r₀.2) + U.u₁.2 * r₀.1) := by
        dsimp [d₂]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U1).1
    have hd1_U2 : 0 < U.u₂.1 * d₁.1 + U.u₂.2 * d₁.2 := by
      have hid : U.u₂.1 * d₁.1 + U.u₂.2 * d₁.2 =
          (U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2) + ε * (U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1) := by
        dsimp [d₁]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U2).2
    have hd2_U2 : 0 < U.u₂.1 * d₂.1 + U.u₂.2 * d₂.2 := by
      have hid : U.u₂.1 * d₂.1 + U.u₂.2 * d₂.2 =
          (U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2) - ε * (U.u₂.1 * (-r₀.2) + U.u₂.2 * r₀.1) := by
        dsimp [d₂]; ring
      rw [hid]; exact (pos_sub_of_eps_abs (le_of_lt hε_pos) hmul_U2).1
    refine ⟨?_, ?_⟩
    · change 0 < U.u₁.1 * (z.1 - y.1) + U.u₁.2 * (z.2 - y.2)
      rw [hzx, hzy]
      have : U.u₁.1 * (α * d₁.1 + β * d₂.1) + U.u₁.2 * (α * d₁.2 + β * d₂.2) =
          α * (U.u₁.1 * d₁.1 + U.u₁.2 * d₁.2) + β * (U.u₁.1 * d₂.1 + U.u₁.2 * d₂.2) := by ring
      rw [this]; exact add_pos (mul_pos hα hd1_U1) (mul_pos hβ hd2_U1)
    · change 0 < U.u₂.1 * (z.1 - y.1) + U.u₂.2 * (z.2 - y.2)
      rw [hzx, hzy]
      have : U.u₂.1 * (α * d₁.1 + β * d₂.1) + U.u₂.2 * (α * d₁.2 + β * d₂.2) =
          α * (U.u₂.1 * d₁.1 + U.u₂.2 * d₁.2) + β * (U.u₂.1 * d₂.1 + U.u₂.2 * d₂.2) := by ring
      rw [this]; exact add_pos (mul_pos hα hd1_U2) (mul_pos hβ hd2_U2)
  · have hεx : ε < |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| /
        (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1) := by
      have hne : F.Nonempty := ⟨x, hx⟩
      have hinf : εF ≤ |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| /
          (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1) := by
        dsimp [εF]; rw [dif_pos hne]
        exact Finset.inf'_le _ hx
      exact lt_of_lt_of_le hε_lt_F hinf
    have hmul : ε * |(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| <
        |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| := by
      have hlt : ε * (|(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1) <
          |(x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1| :=
        (lt_div_iff₀ (by positivity : 0 < |(x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2| + 1)).mp hεx
      linarith
    have h1_eq : n₁.1 * (x.1 - y.1) + n₁.2 * (x.2 - y.2) =
        ((x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1) +
        ε * ((x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2) := by
      dsimp [n₁]; ring
    have h2_eq : n₂.1 * (x.1 - y.1) + n₂.2 * (x.2 - y.2) =
        ((x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1) * (-1) +
        ε * ((x.1 - y.1) * r₀.1 + (x.2 - y.2) * r₀.2) := by
      dsimp [n₂]; ring
    dsimp [OpenWedge.MemExt, R]
    rcases lt_or_gt_of_ne (hx_det_ne x hx) with hlt | hgt
    · left; rw [h1_eq]; rw [abs_of_neg hlt] at hmul
      linarith only [(pos_sub_of_eps_abs (le_of_lt hε_pos) hmul).1]
    · right; rw [h2_eq]; rw [abs_of_pos hgt] at hmul
      linarith only [(pos_sub_of_eps_abs (le_of_lt hε_pos) hmul).1]

private lemma subwedge_avoiding_finset (U : OpenWedge) (F : Finset (ℝ × ℝ)) (hF : U.y ∉ F) :
    ∃ R : OpenWedge, R.y = U.y ∧ (∀ z : ℝ × ℝ, R.MemOpen z → U.MemOpen z) ∧
      (∀ x ∈ F, R.MemExt x) := by
  let y := U.y
  let p₀ : ℝ × ℝ := (y.1 + (SixWedges.dir1 U).1 + (SixWedges.dir2 U).1,
                     y.2 + (SixWedges.dir1 U).2 + (SixWedges.dir2 U).2)
  let d₀ : ℝ × ℝ := (p₀.1 - y.1, p₀.2 - y.2)
  let v₀ : ℝ × ℝ := (-d₀.2, d₀.1)
  have hd_in_U1 : 0 < U.u₁.1 * d₀.1 + U.u₁.2 * d₀.2 := by
    have : U.u₁.1 * d₀.1 + U.u₁.2 * d₀.2 = U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1 := by
      dsimp [d₀, p₀, SixWedges.dir1, SixWedges.dir2]; ring
    rw [this]; exact U.h_nondeg
  have hd_in_U2 : 0 < U.u₂.1 * d₀.1 + U.u₂.2 * d₀.2 := by
    have : U.u₂.1 * d₀.1 + U.u₂.2 * d₀.2 = U.u₁.1 * U.u₂.2 - U.u₁.2 * U.u₂.1 := by
      dsimp [d₀, p₀, SixWedges.dir1, SixWedges.dir2]; ring
    rw [this]; exact U.h_nondeg
  let u1d : ℝ := U.u₁.1 * d₀.1 + U.u₁.2 * d₀.2
  let u1v : ℝ := U.u₁.1 * v₀.1 + U.u₁.2 * v₀.2
  let u2d : ℝ := U.u₂.1 * d₀.1 + U.u₂.2 * d₀.2
  let u2v : ℝ := U.u₂.1 * v₀.1 + U.u₂.2 * v₀.2
  let tBound : ℝ := min (u1d / (|u1v| + 1)) (u2d / (|u2v| + 1)) / 2
  have htBound_pos : 0 < tBound := by
    dsimp [tBound]
    positivity
  let badT : Finset ℝ := F.image (fun x =>
    -((x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1) / ((x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1))
  obtain ⟨t, ht_mem⟩ := (Set.Ioo_infinite htBound_pos).sdiff badT.finite_toSet |>.nonempty
  have ht_pos : 0 < t := ht_mem.1.1
  have ht_lt : t < tBound := ht_mem.1.2
  have ht_nb : t ∉ badT := by simpa using ht_mem.2
  let r₀ : ℝ × ℝ := (d₀.1 + t * v₀.1, d₀.2 + t * v₀.2)
  have hr₀_1 : 0 < U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 := by
    have hlt : |t * u1v| < u1d := by
      rw [abs_mul, abs_of_pos ht_pos]
      have h1 : t < u1d / (|u1v| + 1) := by
        have := min_le_left (u1d / (|u1v| + 1)) (u2d / (|u2v| + 1))
        dsimp [tBound] at ht_lt; linarith
      have h2 := (lt_div_iff₀ (by positivity : 0 < |u1v| + 1)).mp h1
      nlinarith [abs_nonneg u1v]
    have heq : U.u₁.1 * r₀.1 + U.u₁.2 * r₀.2 = u1d + t * u1v := by dsimp [r₀, u1d, u1v]; ring
    rw [heq]; linarith [neg_abs_le (t * u1v)]
  have hr₀_2 : 0 < U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 := by
    have hlt : |t * u2v| < u2d := by
      rw [abs_mul, abs_of_pos ht_pos]
      have h1 : t < u2d / (|u2v| + 1) := by
        have := min_le_right (u1d / (|u1v| + 1)) (u2d / (|u2v| + 1))
        dsimp [tBound] at ht_lt; linarith
      have h2 := (lt_div_iff₀ (by positivity : 0 < |u2v| + 1)).mp h1
      nlinarith [abs_nonneg u2v]
    have heq : U.u₂.1 * r₀.1 + U.u₂.2 * r₀.2 = u2d + t * u2v := by dsimp [r₀, u2d, u2v]; ring
    rw [heq]; linarith [neg_abs_le (t * u2v)]
  have hx_det_ne : ∀ x ∈ F, (x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1 ≠ 0 := by
    intro x hx h0
    have hden_eq : (x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1 =
        (x.1 - y.1) * d₀.1 + (x.2 - y.2) * d₀.2 := by dsimp [v₀]; ring
    by_cases hden0 : (x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1 = 0
    · have hnum0 : (x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1 = 0 := by
        have hid : (x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1 =
            ((x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1) +
            t * ((x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1) := by dsimp [r₀]; ring
        rw [hid, hden0, mul_zero, add_zero] at h0; exact h0
      have hd0_sq : 0 < d₀.1 ^ 2 + d₀.2 ^ 2 := by
        have hnz : d₀.1 ≠ 0 ∨ d₀.2 ≠ 0 := by
          by_contra hno; push Not at hno
          rw [hno.1, hno.2, mul_zero, mul_zero, add_zero] at hd_in_U1; exact lt_irrefl 0 hd_in_U1
        rcases hnz with h1 | h2
        · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h1) (sq_nonneg _)
        · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h2)
      have hx1 : (d₀.1 ^ 2 + d₀.2 ^ 2) * (x.1 - y.1) = 0 := by
        rw [hden_eq] at hden0; linear_combination d₀.1 * hden0 + d₀.2 * hnum0
      have hx2 : (d₀.1 ^ 2 + d₀.2 ^ 2) * (x.2 - y.2) = 0 := by
        rw [hden_eq] at hden0; linear_combination d₀.2 * hden0 - d₀.1 * hnum0
      have hxy : x = y := by
        ext <;> linarith [(mul_eq_zero.mp hx1).resolve_left (ne_of_gt hd0_sq),
                          (mul_eq_zero.mp hx2).resolve_left (ne_of_gt hd0_sq)]
      exact hF (by dsimp [y] at hxy; rw [← hxy]; exact hx)
    · apply ht_nb
      refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
      have hid : (x.1 - y.1) * r₀.2 - (x.2 - y.2) * r₀.1 =
          ((x.1 - y.1) * d₀.2 - (x.2 - y.2) * d₀.1) +
          t * ((x.1 - y.1) * v₀.2 - (x.2 - y.2) * v₀.1) := by dsimp [r₀]; ring
      rw [hid] at h0
      field_simp [hden0]
      linarith
  exact subwedge_from_ray U F r₀ hr₀_1 hr₀_2 hx_det_ne

/-! ## Part 2: `Sec6Targets` ↔ `PolygonCore` Predicate Bridges -/

private lemma hullVertices_eq {n : ℕ} (S : Fin n → ℝ × ℝ) :
    PolygonCore.hullVertices S = hullVertices S := by
  ext i; simp [PolygonCore.hullVertices, hullVertices]

private lemma interiorPoints_eq {n : ℕ} (S : Fin n → ℝ × ℝ) :
    PolygonCore.interiorPoints S = interiorPoints S := by
  rw [PolygonCore.interiorPoints, interiorPoints, hullVertices_eq]

private lemma isCCWEdge_iff_isCCWHullEdge {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) (C : Finset (Fin n)) (a b : Fin n) :
    IsCCWEdge S C a b ↔ PolygonCore.IsCCWHullEdge (C.image S) (S a) (S b) := by
  constructor
  · rintro ⟨ha, hb, hab, hall⟩
    refine ⟨Finset.mem_image_of_mem S ha, Finset.mem_image_of_mem S hb, hPoly.s_inj.ne hab, ?_⟩
    intro z hz hza hzb
    rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
    exact hall r hr (fun h => hza (congrArg S h)) (fun h => hzb (congrArg S h))
  · rintro ⟨ha, hb, hab, hall⟩
    rcases Finset.mem_image.mp ha with ⟨a', ha', ha_eq⟩
    rcases Finset.mem_image.mp hb with ⟨b', hb', hb_eq⟩
    have haa' : a' = a := hPoly.s_inj ha_eq
    have hbb' : b' = b := hPoly.s_inj hb_eq
    subst haa' hbb'
    refine ⟨ha', hb', fun h => hab (congrArg S h), ?_⟩
    intro r hr hra hrb
    exact hall (S r) (Finset.mem_image_of_mem S hr) (hPoly.s_inj.ne hra) (hPoly.s_inj.ne hrb)

private lemma isFrontVertexOf_of_isFrontVertex {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) {C : Finset (Fin n)} {f : Fin n} (hf : f ∈ C)
    {v : ℝ × ℝ} (hfront : PolygonCore.IsFrontVertex (C.image S) v (S f)) :
    IsFrontVertexOf S C f v := by
  rcases hfront with ⟨b_pt, c_pt, hbf_pt, hfc_pt, hbv, hcv⟩
  refine ⟨hf, fun a b hab heq => ?_⟩
  have hab_pt := (isCCWEdge_iff_isCCWHullEdge hPoly C a b).mp hab
  rcases heq with rfl | rfl
  · have hb_eq : S b = c_pt := PolygonCore.isCCWHullEdge_succ_unique hab_pt hfc_pt
    rw [hb_eq]; exact hcv
  · have ha_eq : S a = b_pt := PolygonCore.isCCWHullEdge_pred_unique hab_pt hbf_pt
    rw [ha_eq]; exact hbv

private lemma isFrontVertex_of_isFrontVertexOf {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) {C : Finset (Fin n)} (hCB : C ⊆ hullVertices S)
    (hC3 : 3 ≤ C.card) {f : Fin n} {v : ℝ × ℝ}
    (hfront : IsFrontVertexOf S C f v) :
    PolygonCore.IsFrontVertex (C.image S) v (S f) := by
  have hC_conv : IsConvexPos S C := hullVertices_convexPos S hCB
  obtain ⟨cyc⟩ := exists_ccwCycle S C (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    hC_conv (show C.card = (C.card - 3) + 3 by omega)
  obtain ⟨i, rfl⟩ := ccwCycle_exists_index cyc hfront.1
  have e1 := ccwCycle_isCCWEdge cyc (i - 1)
  rw [sub_add_cancel] at e1
  have e2 := ccwCycle_isCCWEdge cyc i
  have ho := (isFrontVertexOf_iff_ccwCycle cyc i v).mp hfront
  exact ⟨S (cyc.toFun (i - 1)), S (cyc.toFun (i + 1)),
    (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e1,
    (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e2,
    ho.1, ho.2⟩

private lemma isBackVertexOf_iff_isBackVertex {n : ℕ} {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) {C : Finset (Fin n)} (hCB : C ⊆ hullVertices S)
    (hC3 : 3 ≤ C.card) {p : Fin n} {v : ℝ × ℝ} :
    IsBackVertexOf S C p v ↔ PolygonCore.IsBackVertex (C.image S) v (S p) := by
  have hC_conv : IsConvexPos S C := hullVertices_convexPos S hCB
  obtain ⟨cyc⟩ := exists_ccwCycle S C (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    hC_conv (show C.card = (C.card - 3) + 3 by omega)
  constructor
  · intro hback
    obtain ⟨i, rfl⟩ := ccwCycle_exists_index cyc hback.1
    have e1 := ccwCycle_isCCWEdge cyc (i - 1)
    rw [sub_add_cancel] at e1
    have e2 := ccwCycle_isCCWEdge cyc i
    have ho := (isBackVertexOf_iff_ccwCycle cyc i v).mp hback
    exact ⟨S (cyc.toFun (i - 1)), S (cyc.toFun (i + 1)),
      (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e1,
      (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp e2,
      ho.1, ho.2⟩
  · rintro ⟨b_pt, c_pt, hbp_pt, hpc_pt, hbv, hcv⟩
    obtain ⟨p', hp'C, hp'eq⟩ := Finset.mem_image.mp hbp_pt.2.1
    have hpp' : p' = p := hPoly.s_inj hp'eq
    subst hpp'
    refine ⟨hp'C, fun a b hab heq => ?_⟩
    have hab_pt := (isCCWEdge_iff_isCCWHullEdge hPoly C a b).mp hab
    rcases heq with rfl | rfl
    · have hb_eq : S b = c_pt := PolygonCore.isCCWHullEdge_succ_unique hab_pt hpc_pt
      rw [hb_eq]; exact hcv
    · have ha_eq : S a = b_pt := PolygonCore.isCCWHullEdge_pred_unique hab_pt hbp_pt
      rw [ha_eq]; exact hbv

private lemma certifiedVertices_eq_certifiedSet {n : ℕ} (hn : 3 ≤ n) {P : Set (ℝ × ℝ)}
    {S : Fin n → ℝ × ℝ} {w : Finset (Fin n) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) :
    certifiedVertices S w = PolygonCore.certifiedSet P S w := by
  let B := hullVertices S
  have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
  obtain ⟨cyc⟩ := exists_ccwCycle S B (fun a _ b _ h => hPoly.s_inj h)
    (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
      (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
      (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
    (hullVertices_convexPos S Finset.Subset.rfl) (show B.card = (B.card - 3) + 3 by omega)
  ext f
  simp only [certifiedVertices, PolygonCore.certifiedSet, PolygonCore.IsCertified, Finset.mem_filter]
  constructor
  · rintro ⟨hfB, T, hfT, hbT, hcT, hfront⟩
    refine ⟨hfB, hfB, T, fun hsees => hfT ((hPoly.shatters T f).mp hsees), ?_, ?_⟩
    · intro b hbB h_or
      refine (hPoly.shatters T b).mpr ?_
      rcases h_or with hbf | hfb
      · exact hbT b ((isCCWEdge_iff_isCCWHullEdge hPoly B b f).mpr hbf)
      · exact hcT b ((isCCWEdge_iff_isCCWHullEdge hPoly B f b).mpr hfb)
    · exact isFrontVertex_of_isFrontVertexOf hPoly Finset.Subset.rfl hB3 hfront
  · rintro ⟨hfB, _, T, hvnf, hvs, hfront⟩
    refine ⟨hfB, T, fun hfT => hvnf ((hPoly.shatters T f).mpr hfT), ?_, ?_, ?_⟩
    · intro b hbf
      have hbB : b ∈ B := hbf.1
      exact (hPoly.shatters T b).mp (hvs b hbB (Or.inl ((isCCWEdge_iff_isCCWHullEdge hPoly B b f).mp hbf)))
    · intro c hfc
      have hcB : c ∈ B := hfc.2.1
      exact (hPoly.shatters T c).mp (hvs c hcB (Or.inr ((isCCWEdge_iff_isCCWHullEdge hPoly B f c).mp hfc)))
    · exact isFrontVertexOf_of_isFrontVertex hPoly hfB hfront

/-! ## Part 3: Main Bridge Theorem `mk_sec2To5Interface` -/

theorem mk_sec2To5Interface {P : Set (ℝ × ℝ)} {S : Fin 10 → ℝ × ℝ} {w : Finset (Fin 10) → ℝ × ℝ}
    (hPoly : ShatteredSimplePolygon P S w) : Sec2To5Interface P S w := by
  have hn : (3 : ℕ) ≤ 10 := by decide
  have hcert_eq : certifiedVertices S w = PolygonCore.certifiedSet P S w :=
    certifiedVertices_eq_certifiedSet hn hPoly
  refine
    { three_halfplanes := ArrangementBounds.three_halfplanes_not_all_8
      two_hp_three_wedges := ArrangementBounds.two_hp_three_wedges_not_all_32
      cone_lemma := fun a b c w0 x _ _ _ _ _ hwb hwc hnwa ha hxb hxc hxab hxac hxwa =>
        (PolygonCore.mem_uCone_iff_inOpenTri a b c x).mp
          (PolygonCore.cone_of_shattered hPoly hwb hwc hnwa ha hxb hxc hxab hxac hxwa)
      wedge_extraction := ?_
      fan_corollary := ?_
      hidden_targets := ?_
      hidden_front := ?_
      front_restoration := ?_
      certified_structure := ?_
      side_preservation := ?_
      exit_edge_lemma := ?_
      endpoint_back_criterion := ?_
      half_plane_lemma := ?_ }
  · -- wedge_extraction
    intro a b c W' U hab hac hbc hW' hUy hU_sep hX_in_U
    by_cases hX : ∃ x ∈ W', Sees P x (S a)
    · obtain ⟨p₀, hp₀W', hp₀_sees⟩ := hX
      obtain ⟨R₀, hR₀y, hR₀_test⟩ :=
        PolygonCore.wedge_extraction hPoly hab hbc hac hW' U hUy hU_sep hX_in_U
      obtain ⟨R, hRy, hR_open, hR_ext⟩ :=
        openWedge_intersection_at_apex R₀ U (hR₀y.trans hUy.symm) p₀
          (((hR₀_test p₀ hp₀W').2).mp hp₀_sees) (hX_in_U p₀ hp₀W' hp₀_sees)
      refine ⟨R, hRy.trans hUy, fun z hz => (hR_open z).mp hz |>.2, fun x hx => ?_⟩
      refine ⟨?_, ?_⟩
      · rcases (hR₀_test x hx).1 with h1 | h2
        · by_cases hsees : Sees P x (S a)
          · exact Or.inl ((hR_open x).mpr ⟨h1, hX_in_U x hx hsees⟩)
          · exact Or.inr ((hR_ext x).mpr (Or.inl (((hR₀_test x hx).2).not.mp hsees |> fun hno =>
              ((hR₀_test x hx).1).resolve_left hno)))
        · exact Or.inr ((hR_ext x).mpr (Or.inl h2))
      · constructor
        · intro hsees
          exact (hR_open x).mpr ⟨((hR₀_test x hx).2).mp hsees, hX_in_U x hx hsees⟩
        · intro hmem
          exact ((hR₀_test x hx).2).mpr ((hR_open x).mp hmem).1
    · push Not at hX
      let W'_idx : Finset (Finset (Fin 10)) := Finset.univ.filter (fun T => w T ∈ W')
      let F : Finset (ℝ × ℝ) := W'_idx.image w
      have hF : U.y ∉ F := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨T, _, heq⟩
        exact hPoly.s_ne_w a T (hUy.symm.trans heq.symm)
      obtain ⟨R, hRy, hRU, hRF⟩ := subwedge_avoiding_finset U F hF
      refine ⟨R, hRy.trans hUy, hRU, fun x hx => ?_⟩
      obtain ⟨T, _, _, rfl⟩ := hW' hx
      have hxF : w T ∈ F := Finset.mem_image_of_mem w (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hx⟩)
      have hext := hRF (w T) hxF
      refine ⟨Or.inr hext, fun hsees => absurd hsees (hX (w T) hx), fun hopen => ?_⟩
      rcases hext with h1 | h2
      · linarith [hopen.1]
      · linarith [hopen.2]
  · -- fan_corollary
    intro Tw F a hFT ha_not ha_conv
    rw [Set.union_singleton] at ha_conv
    obtain ⟨R, _, hR_test⟩ := PolygonCore.fan hPoly hFT ha_not ha_conv
    exact ⟨R, hR_test⟩
  · -- hidden_targets
    intro T hTB htarg
    apply PolygonCore.hidden_targets hPoly T hTB
    intro t ht
    obtain ⟨b, c, Tv, hb, hc, _, hbTv, hcTv, htTv, htri⟩ := htarg t ht
    exact ⟨b, hb, c, hc, Tv, (hPoly.shatters Tv b).mpr hbTv, (hPoly.shatters Tv c).mpr hcTv,
      fun h => htTv ((hPoly.shatters Tv t).mp h), htri⟩
  · -- hidden_front
    intro C Tv f b c hCB hC3 hf hbf hfc hbTv hcTv hfTv hfront
    have hbC : b ∈ C := hbf.1
    have hcC : c ∈ C := hfc.2.1
    obtain ⟨htri, hall⟩ := PolygonCore.hidden_front_vertex hPoly C hCB hC3 Tv hf hbC hcC
      ((isCCWEdge_iff_isCCWHullEdge hPoly C b f).mp hbf)
      ((isCCWEdge_iff_isCCWHullEdge hPoly C f c).mp hfc)
      (isFrontVertex_of_isFrontVertexOf hPoly hCB hC3 hfront)
      ((hPoly.shatters Tv b).mpr hbTv) ((hPoly.shatters Tv c).mpr hcTv)
      (fun h => hfTv ((hPoly.shatters Tv f).mp h))
    refine ⟨htri, fun Tx hbTx hcTx => ?_⟩
    obtain ⟨hx_tri, hx_front⟩ := hall Tx ((hPoly.shatters Tx b).mpr hbTx) ((hPoly.shatters Tx c).mpr hcTx)
    exact ⟨hx_tri, isFrontVertexOf_of_isFrontVertex hPoly hf hx_front⟩
  · -- front_restoration
    intro C D' f v hCD' hD'_conv hC3 _ hfront
    have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
    have hD'3 : 3 ≤ D'.card := le_trans hC3 (Finset.card_le_card hCD')
    have hD'_img_conv : PolygonCore.IsConvexPos (D'.image S) := by
      refine ⟨fun p hp hmem => ?_, fun x hx y hy z hz hxy hyz hxz => ?_⟩
      · rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
        apply hD'_conv i hi
        refine convexHull_mono ?_ hmem
        intro q hq
        rcases Finset.mem_image.mp (Finset.mem_erase.mp hq).2 with ⟨j, hj, rfl⟩
        exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hq).1 (congrArg S h), hj⟩, rfl⟩
      · rcases Finset.mem_image.mp hx with ⟨ix, _, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨iy, _, rfl⟩
        rcases Finset.mem_image.mp hz with ⟨iz, _, rfl⟩
        exact hPoly.no_three_collinear _ _ _ (Or.inl ⟨ix, rfl⟩) (Or.inl ⟨iy, rfl⟩) (Or.inl ⟨iz, rfl⟩)
          hxy hyz hxz
    obtain ⟨cycC⟩ := exists_ccwCycle S C (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
        (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
        (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
      (fun i hi hmem => hD'_conv i (hCD' hi) (convexHull_mono (by
        intro q hq
        rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
        exact Finset.mem_image_of_mem S (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hj).1, hCD' (Finset.mem_erase.mp hj).2⟩)) hmem))
      (show C.card = (C.card - 3) + 3 by omega)
    obtain ⟨cycD'⟩ := exists_ccwCycle S D' (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
        (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
        (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
      hD'_conv (show D'.card = (D'.card - 3) + 3 by omega)
    obtain ⟨iC, rfl⟩ := ccwCycle_exists_index cycC hfront.1
    have eC1 := ccwCycle_isCCWEdge cycC (iC - 1)
    rw [sub_add_cancel] at eC1
    have eC2 := ccwCycle_isCCWEdge cycC iC
    have hoC := (isFrontVertexOf_iff_ccwCycle cycC iC v).mp hfront
    have hfrontC : PolygonCore.IsFrontVertex (C.image S) v (S (cycC.toFun iC)) :=
      ⟨S (cycC.toFun (iC - 1)), S (cycC.toFun (iC + 1)),
        (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp eC1,
        (isCCWEdge_iff_isCCWHullEdge hPoly C _ _).mp eC2,
        hoC.1, hoC.2⟩
    have hfD' : cycC.toFun iC ∈ D' := hCD' hfront.1
    obtain ⟨iD, hiD⟩ := ccwCycle_exists_index cycD' hfD'
    have eD1 := ccwCycle_isCCWEdge cycD' (iD - 1)
    rw [sub_add_cancel, hiD] at eD1
    have eD2 := ccwCycle_isCCWEdge cycD' iD
    rw [hiD] at eD2
    have hfrontD' := PolygonCore.front_restoration (Finset.image_subset_image hCD') hD'_img_conv
      (Finset.mem_image_of_mem S hfront.1) hfrontC
      ((isCCWEdge_iff_isCCWHullEdge hPoly D' _ _).mp eD1)
      ((isCCWEdge_iff_isCCWHullEdge hPoly D' _ _).mp eD2)
    exact isFrontVertexOf_of_isFrontVertex hPoly hfD' hfrontD'
  · -- certified_structure
    dsimp only []
    rw [hcert_eq]
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    refine ⟨?_, ?_⟩
    · by_cases hHne : H.Nonempty
      · have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
        obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
        have ⟨h₀, hh₀⟩ := hHne
        obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h5⟩ :=
          PolygonCore.certified_structure hPoly hn cb vc hHne
        rwa [interiorPoints_eq S] at h5
      · have hHempty : PolygonCore.certifiedSet P S w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hHne
        rw [hHempty, Finset.card_empty, add_zero]
        have h0 := PolygonCore.hidden_targets hPoly ∅ (Finset.empty_subset B) (fun _ h => by simp at h)
        rw [interiorPoints_eq S] at h0
        simpa using h0
    · intro hHne
      have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
      obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
      have ⟨h₀, hh₀⟩ := hHne
      obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
      obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, hlD, hrD, hlr, hblock, hpart_ii, _⟩ :=
        PolygonCore.certified_structure hPoly hn cb vc hHne
      haveI : NeZero (cb.m + 3) := ⟨by omega⟩
      have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
        have h := Finset.mem_image_of_mem cb.p_idx (Finset.mem_univ j)
        rwa [cb.hp_idx_img] at h
      have hcb_ex : ∀ x ∈ B, ∃ k : ℕ, k < cb.m + 3 ∧ cb.p_idx (PolygonCore.finShift vc.i_max k) = x := by
        intro x hx
        rw [← cb.hp_idx_img] at hx
        rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
        refine ⟨(j - vc.i_max).val, (j - vc.i_max).isLt, ?_⟩
        rw [PolygonCore.finShift_eq_add vc.i_max (j - vc.i_max).isLt]
        simp [add_sub_cancel]
      have hd_pos : ∀ d ∈ D, d ≠ l → d ≠ r → 0 < orient2D (S l) (S r) (S d) := by
        intro d hd hdl hdr
        obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.mem_sdiff.mp hd).1
        have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
          rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hd).2
        have hkd_ne_l : kd ≠ k_f - 1 := fun h => hdl (by rw [← hkd_eq, hl_eq, h])
        have hkd_ne_r : kd ≠ k_g + 1 := fun h => hdr (by rw [← hkd_eq, hr_eq, h])
        have h_cyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
            (PolygonCore.finShift vc.i_max (k_g + 1)) (PolygonCore.finShift vc.i_max kd) := by
          have hd_vc := vc.hd_lt
          rcases (by omega : kd < k_f - 1 ∨ k_g + 1 < kd) with hlt | hgt
          · apply PolygonCore.cyclicOrder_cycle
            exact PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega)
          · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkd_lt
        rw [← hkd_eq, hl_eq, hr_eq]
        exact cb.hcyc _ _ _ h_cyc
      refine ⟨l, r, hlD, hrD, hlr, ?_, ?_, hd_pos, ?_, ?_, ?_, ?_⟩
      · intro hD3
        exact ⟨hlD, hrD, hlr, hd_pos⟩
      · intro h hh
        obtain ⟨kh, hkh_lt, hkh_eq⟩ := hcb_ex h (Finset.filter_subset _ _ hh)
        have hkh_range : k_f ≤ kh ∧ kh ≤ k_g := (hblock kh hkh_lt).mpr (by rw [hkh_eq]; exact hh)
        have hd_vc := vc.hd_lt
        have h_cyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
            (PolygonCore.finShift vc.i_max kh) (PolygonCore.finShift vc.i_max (k_g + 1)) :=
          PolygonCore.cyclicOrder_finShift vc.i_max (by omega) (by omega) (by omega)
        have hpos := cb.hcyc _ _ _ h_cyc
        rw [hkh_eq, ← hl_eq, ← hr_eq] at hpos
        rw [orient2D_swap23]; linarith
      · intro h T hh hlT hrT
        exact hpart_ii h hh T ((hPoly.shatters T l).mpr hlT) ((hPoly.shatters T r).mpr hrT)
      · intro d hd hdl hdr x hxB
        have hD3 : 3 ≤ D.card := by
          have hsub : {l, r, d} ⊆ D := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have h3 : ({l, r, d} : Finset (Fin 10)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hdr.symm]
            simp [hlr, hdl.symm]
          exact h3 ▸ Finset.card_le_card hsub
        obtain ⟨cycB⟩ := exists_ccwCycle S B (fun a _ b _ h => hPoly.s_inj h)
          (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
            (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
            (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
          (hullVertices_convexPos S Finset.Subset.rfl) (show B.card = (B.card - 3) + 3 by omega)
        obtain ⟨cycD⟩ := exists_ccwCycle S D (fun a _ b _ h => hPoly.s_inj h)
          (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
            (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
            (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
          (hullVertices_convexPos S Finset.sdiff_subset) (show D.card = (D.card - 3) + 3 by omega)
        obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.mem_sdiff.mp hd).1
        have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
          rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hd).2
        have hkd_ne_l : kd ≠ k_f - 1 := fun h => hdl (by rw [← hkd_eq, hl_eq, h])
        have hkd_ne_r : kd ≠ k_g + 1 := fun h => hdr (by rw [← hkd_eq, hr_eq, h])
        have h_pred_B : ∃ p₀ ∈ D, IsCCWEdge S B p₀ d := by
          let kp := if kd = 0 then cb.m + 2 else kd - 1
          have hkp_lt : kp < cb.m + 3 := by dsimp [kp]; split_ifs <;> omega
          have hkp_notH : ¬ (k_f ≤ kp ∧ kp ≤ k_g) := by
            dsimp [kp]; split_ifs with h0
            · have := vc.hd_lt; omega
            · omega
          have hp_memB : cb.p_idx (PolygonCore.finShift vc.i_max kp) ∈ B := hcb_mem _
          have hp_notH : cb.p_idx (PolygonCore.finShift vc.i_max kp) ∉ H := by
            rw [← hblock kp hkp_lt]; exact hkp_notH
          refine ⟨cb.p_idx (PolygonCore.finShift vc.i_max kp), Finset.mem_sdiff.mpr ⟨hp_memB, hp_notH⟩,
            hp_memB, (Finset.mem_sdiff.mp hd).1, ?_, ?_⟩
          · intro heq
            have hinj := cb.hp_idx_inj (heq.trans hkd_eq.symm)
            have hsub := congrArg (· - vc.i_max) hinj
            rw [PolygonCore.finShift_eq_add vc.i_max hkp_lt,
              PolygonCore.finShift_eq_add vc.i_max hkd_lt,
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            have hval := congrArg Fin.val hsub
            dsimp [kp] at hval; split_ifs at hval <;> omega
          · intro z hz hzp hzd
            obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
            have hkz_ne_p : kz ≠ kp := fun h => hzp (by rw [← hkz_eq, h])
            have hkz_ne_d : kz ≠ kd := fun h => hzd (by rw [← hkz_eq, ← hkd_eq, h])
            have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kp)
                (PolygonCore.finShift vc.i_max kd) (PolygonCore.finShift vc.i_max kz) := by
              dsimp [kp] at hkz_ne_p ⊢
              split_ifs at hkz_ne_p ⊢ with h0
              · subst h0
                exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                  (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
              · rcases (by omega : kz < kd - 1 ∨ kd < kz) with hlt | hgt
                · exact PolygonCore.cyclicOrder_cycle
                    (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) hkd_lt)
                · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
            rw [← hkz_eq, ← hkd_eq]
            exact cb.hcyc _ _ _ hcyc
        have h_succ_B : ∃ s₀ ∈ D, IsCCWEdge S B d s₀ := by
          let ks := if kd + 1 = cb.m + 3 then 0 else kd + 1
          have hks_lt : ks < cb.m + 3 := by dsimp [ks]; split_ifs <;> omega
          have hks_notH : ¬ (k_f ≤ ks ∧ ks ≤ k_g) := by
            dsimp [ks]; split_ifs with hmax
            · omega
            · have := vc.hd_lt; omega
          have hs_memB : cb.p_idx (PolygonCore.finShift vc.i_max ks) ∈ B := hcb_mem _
          have hs_notH : cb.p_idx (PolygonCore.finShift vc.i_max ks) ∉ H := by
            rw [← hblock ks hks_lt]; exact hks_notH
          refine ⟨cb.p_idx (PolygonCore.finShift vc.i_max ks), Finset.mem_sdiff.mpr ⟨hs_memB, hs_notH⟩,
            (Finset.mem_sdiff.mp hd).1, hs_memB, ?_, ?_⟩
          · intro heq
            have hinj := cb.hp_idx_inj (hkd_eq.trans heq)
            have hsub := congrArg (· - vc.i_max) hinj
            rw [PolygonCore.finShift_eq_add vc.i_max hkd_lt,
              PolygonCore.finShift_eq_add vc.i_max hks_lt,
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            have hval := congrArg Fin.val hsub
            dsimp [ks] at hval; split_ifs at hval <;> omega
          · intro z hz hzd hzs
            obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
            have hkz_ne_d : kz ≠ kd := fun h => hzd (by rw [← hkz_eq, ← hkd_eq, h])
            have hkz_ne_s : kz ≠ ks := fun h => hzs (by rw [← hkz_eq, h])
            have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kd)
                (PolygonCore.finShift vc.i_max ks) (PolygonCore.finShift vc.i_max kz) := by
              dsimp [ks] at hkz_ne_s ⊢
              split_ifs at hkz_ne_s ⊢ with hmax
              · have hkd_eq_m2 : kd = cb.m + 2 := by omega
                rw [hkd_eq_m2] at hkz_ne_d ⊢
                exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                  (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
              · rcases (by omega : kz < kd ∨ kd + 1 < kz) with hlt | hgt
                · exact PolygonCore.cyclicOrder_cycle
                    (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega : kd + 1 < cb.m + 3))
                · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
            rw [← hkz_eq, ← hkd_eq]
            exact cb.hcyc _ _ _ hcyc
        obtain ⟨p₀, hp0D, hp0B⟩ := h_pred_B
        obtain ⟨s₀, hs0D, hs0B⟩ := h_succ_B
        have hp0D_edge : IsCCWEdge S D p₀ d := ⟨hp0D, hd, hp0B.2.2.1,
          fun z hz h1 h2 => hp0B.2.2.2 z (Finset.sdiff_subset hz) h1 h2⟩
        have hs0D_edge : IsCCWEdge S D d s₀ := ⟨hd, hs0D, hs0B.2.2.1,
          fun z hz h1 h2 => hs0B.2.2.2 z (Finset.sdiff_subset hz) h1 h2⟩
        constructor
        · constructor
          · intro hB
            have hxp : x = p₀ := isCCWEdge_unique_pred cycB hB hp0B
            rw [hxp]; exact hp0D_edge
          · intro hD
            have hxp : x = p₀ := isCCWEdge_unique_pred cycD hD hp0D_edge
            rw [hxp]; exact hp0B
        · constructor
          · intro hB
            have hxs : x = s₀ := isCCWEdge_unique_succ cycB hB hs0B
            rw [hxs]; exact hs0D_edge
          · intro hD
            have hxs : x = s₀ := isCCWEdge_unique_succ cycD hD hs0D_edge
            rw [hxs]; exact hs0B
      · intro hH1 h hh
        obtain ⟨kh, hkh_lt, hkh_eq⟩ := hcb_ex h (Finset.filter_subset _ _ hh)
        have hkh_range : k_f ≤ kh ∧ kh ≤ k_g := (hblock kh hkh_lt).mpr (by rw [hkh_eq]; exact hh)
        have hkf_inH : cb.p_idx (PolygonCore.finShift vc.i_max k_f) ∈ H := by
          rw [← hblock k_f (by have := vc.hd_lt; omega)]; exact ⟨le_rfl, hkfg⟩
        have hkg_inH : cb.p_idx (PolygonCore.finShift vc.i_max k_g) ∈ H := by
          rw [← hblock k_g (by have := vc.hd_lt; omega)]; exact ⟨hkfg, le_rfl⟩
        have hfg_eq : k_f = k_g := by
          by_contra hne
          have hneq_pts : cb.p_idx (PolygonCore.finShift vc.i_max k_f) ≠
              cb.p_idx (PolygonCore.finShift vc.i_max k_g) := by
            intro heq
            have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
            have := vc.hd_lt
            rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f < cb.m + 3),
              PolygonCore.finShift_eq_add vc.i_max (by omega : k_g < cb.m + 3),
              add_sub_cancel_left, add_sub_cancel_left] at hsub
            exact hne (by simpa using congrArg Fin.val hsub)
          have h2 : 2 ≤ H.card := Finset.one_lt_card.mpr ⟨_, hkf_inH, _, hkg_inH, hneq_pts⟩
          dsimp [H] at h2; omega
        have hkh_kf : kh = k_f := by omega
        have hkh_kg : kh = k_g := by omega
        have hd_vc := vc.hd_lt
        refine ⟨⟨Finset.sdiff_subset hlD, Finset.filter_subset _ _ hh, fun h' => hlD |> fun h'' =>
          (Finset.mem_sdiff.mp h'').2 (h' ▸ hh), fun z hz hzl hzh => ?_⟩,
          ⟨Finset.filter_subset _ _ hh, Finset.sdiff_subset hrD, fun h' => hrD |> fun h'' =>
          (Finset.mem_sdiff.mp h'').2 (h'.symm ▸ hh), fun z hz hzh hzr => ?_⟩⟩
        · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_l : kz ≠ k_f - 1 := fun e => hzl (by rw [← hkz_eq, hl_eq, e])
          have hkz_h : kz ≠ k_f := fun e => hzh (by rw [← hkz_eq, ← hkh_eq, hkh_kf, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
              (PolygonCore.finShift vc.i_max k_f) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_f - 1 ∨ k_f < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle
                (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq, ← hkh_eq, hkh_kf, hl_eq]
          exact cb.hcyc _ _ _ hcyc
        · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_h : kz ≠ k_g := fun e => hzh (by rw [← hkz_eq, ← hkh_eq, hkh_kg, e])
          have hkz_r : kz ≠ k_g + 1 := fun e => hzr (by rw [← hkz_eq, hr_eq, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max k_g)
              (PolygonCore.finShift vc.i_max (k_g + 1)) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_g ∨ k_g + 1 < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle
                (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq, ← hkh_eq, hkh_kg, hr_eq]
          exact cb.hcyc _ _ _ hcyc
      · intro hH2
        have hkf_lt_kg : k_f < k_g := by
          by_contra hge
          have hkf_eq : k_f = k_g := by omega
          have hsub : H ⊆ {cb.p_idx (PolygonCore.finShift vc.i_max k_f)} := by
            intro h hh
            obtain ⟨kh, hkh_lt, hkh_eq⟩ := hcb_ex h (Finset.filter_subset _ _ hh)
            have hkr := (hblock kh hkh_lt).mpr (by rw [hkh_eq]; exact hh)
            have : kh = k_f := by omega
            simp [← hkh_eq, this]
          have hle : H.card ≤ 1 := (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
          dsimp [H] at hle; omega
        have hd_vc := vc.hd_lt
        let h1 := cb.p_idx (PolygonCore.finShift vc.i_max k_f)
        let h2 := cb.p_idx (PolygonCore.finShift vc.i_max (k_f + 1))
        have hh1 : h1 ∈ H := by rw [← hblock k_f (by omega)]; exact ⟨le_rfl, le_of_lt hkf_lt_kg⟩
        have hh2 : h2 ∈ H := by rw [← hblock (k_f + 1) (by omega)]; exact ⟨by omega, by omega⟩
        have h12 : h1 ≠ h2 := by
          intro heq
          have hsub := congrArg (· - vc.i_max) (cb.hp_idx_inj heq)
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max (by omega : k_f + 1 < cb.m + 3),
            add_sub_cancel_left, add_sub_cancel_left] at hsub
          have hval := congrArg Fin.val hsub
          simp only [Fin.val_mk] at hval
          omega
        refine ⟨h1, h2, hh1, hh2, h12, ?_, ?_⟩
        · refine ⟨Finset.sdiff_subset hlD, Finset.filter_subset _ _ hh1, fun heq => (Finset.mem_sdiff.mp hlD).2 (heq ▸ hh1),
            fun z hz hzl hzh => ?_⟩
          obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_l : kz ≠ k_f - 1 := fun e => hzl (by rw [← hkz_eq, hl_eq, e])
          have hkz_h1 : kz ≠ k_f := fun e => hzh (by rw [← hkz_eq, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
              (PolygonCore.finShift vc.i_max k_f) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_f - 1 ∨ k_f < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle
                (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq, hl_eq]
          exact cb.hcyc _ _ _ hcyc
        · refine ⟨Finset.filter_subset _ _ hh1, Finset.filter_subset _ _ hh2, h12, fun z hz hzh1 hzh2 => ?_⟩
          obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
          have hkz_h1 : kz ≠ k_f := fun e => hzh1 (by rw [← hkz_eq, e])
          have hkz_h2 : kz ≠ k_f + 1 := fun e => hzh2 (by rw [← hkz_eq, e])
          have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max k_f)
              (PolygonCore.finShift vc.i_max (k_f + 1)) (PolygonCore.finShift vc.i_max kz) := by
            rcases (by omega : kz < k_f ∨ k_f + 1 < kz) with hlt | hgt
            · exact PolygonCore.cyclicOrder_cycle
                (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
            · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
          rw [← hkz_eq]
          exact cb.hcyc _ _ _ hcyc
  · -- side_preservation
    dsimp only []
    rw [hcert_eq]
    intro hHne hD5 Q M₀ hQD hQ2 hM0M hQ_back
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
    obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
    have ⟨h₀, hh₀⟩ := hHne
    obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
    obtain ⟨k_f, k_g, l, r, hkf0, hkfg, hkg_lt, hl_eq, hr_eq, _, _, _, hblock, _, _⟩ :=
      PolygonCore.certified_structure hPoly hn cb vc hHne
    have hM0' : M₀ ⊆ interiorPoints S ∪ H := by
      intro x hx
      have hxM := hM0M hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hxM
      by_cases hxB : x ∈ B
      · refine Finset.mem_union.mpr (Or.inr ?_)
        by_contra hxH; exact hxM ⟨hxB, hxH⟩
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxB⟩))
    have hQ_back' : ∀ p ∈ Q, ∃ O : Finset (Fin 10), p ∉ O ∧
        (∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ PolygonCore.IsCCWHullEdge (B.image S) (S a) (S b)) ∧
        PolygonCore.IsBackVertex (B.image S) (w (Finset.univ \ O)) (S p) := by
      intro p hpQ
      obtain ⟨O, hpO, hOnoadj, hp_back⟩ := hQ_back p hpQ
      refine ⟨O, hpO, fun a ha b hb h_edge => hOnoadj a ha b hb
        ((isCCWEdge_iff_isCCWHullEdge hPoly B a b).mpr h_edge), ?_⟩
      exact (isBackVertexOf_iff_isBackVertex hPoly Finset.Subset.rfl hB3).mp hp_back
    have hsp := (PolygonCore.side_preservation hPoly hn cb vc hHne hD5 hkf0 hkfg hkg_lt
      hl_eq hr_eq hblock).2 Q hQD hQ2 hQ_back' M₀ hM0'
    intro h hh
    obtain ⟨a, haF, b, hbF, hall⟩ := hsp h hh
    have hab : a ≠ b := by
      intro heq; subst heq
      have htri := hall {a} ((hPoly.shatters {a} a).mpr (by simp)) ((hPoly.shatters {a} a).mpr (by simp))
      have hha : h ≠ a := by
        intro h'; subst h'
        have hhM0 : h ∉ M₀ := (Finset.mem_sdiff.mp hh).2
        rcases Finset.mem_union.mp haF with haD | haM0
        · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp haD).1).2 (Finset.mem_sdiff.mp hh).1
        · exact hhM0 haM0
      rcases htri with ⟨μ₁, μ₂, μ₃, _, _, _, hsum, hx1, hx2⟩
      have hcol : orient2D (w {a}) (S a) (S h) = 0 := by
        unfold orient2D; rw [hx1, hx2, show μ₁ = 1 - μ₂ - μ₃ by linarith]; ring
      exact hPoly.no_three_collinear (w {a}) (S a) (S h) (Or.inr ⟨{a}, rfl⟩)
        (Or.inl ⟨a, rfl⟩) (Or.inl ⟨h, rfl⟩) (hPoly.s_ne_w a {a}).symm
        (hPoly.s_inj.ne hha.symm) (hPoly.s_ne_w h {a}).symm hcol
    refine ⟨a, b, haF, hbF, hab, fun x hx => ?_⟩
    obtain ⟨Tx, hsub, _, rfl⟩ := hx
    exact hall Tx ((hPoly.shatters Tx a).mpr (hsub (by simp))) ((hPoly.shatters Tx b).mpr (hsub (by simp)))
  · -- exit_edge_lemma
    dsimp only []
    rw [hcert_eq]
    intro hD3 y hyM
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    have hyM' : y ∈ interiorPoints S ∪ H := by
      have hy := Finset.mem_sdiff.mp hyM
      by_cases hyB : y ∈ B
      · refine Finset.mem_union.mpr (Or.inr ?_)
        by_contra hyH; exact hy.2 (Finset.mem_sdiff.mpr ⟨hyB, hyH⟩)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyB⟩))
    obtain ⟨dc⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly Finset.sdiff_subset hD3
    obtain ⟨⟨i, ⟨hpos_i, htri_i⟩, huniq_i⟩, himp_i⟩ := PolygonCore.exit_edge hPoly hn hD3 dc y hyM'
    obtain ⟨hall_i, hB_edge⟩ := himp_i i hpos_i htri_i
    have hD_conv : IsConvexPos S D := hullVertices_convexPos S Finset.sdiff_subset
    have hD3' : 3 ≤ D.card := hD3
    obtain ⟨cycD⟩ := exists_ccwCycle S D (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
        (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
        (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
      hD_conv (show D.card = (D.card - 3) + 3 by omega)
    have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
      have h := Finset.mem_image_of_mem dc.p_idx (Finset.mem_univ j)
      rwa [dc.hp_idx_img] at h
    have hdc_edge : ∀ j : Fin (dc.m + 3), IsCCWEdge S D (dc.p_idx j) (dc.p_idx (j + 1)) := by
      intro j
      haveI : NeZero (dc.m + 3) := ⟨by omega⟩
      have hj1_ne : j ≠ j + 1 := by
        intro h
        nth_rw 1 [← add_zero j] at h
        have h01 := add_left_cancel h
        have hv := congrArg Fin.val h01
        simp [Nat.mod_eq_of_lt (by omega : 1 < dc.m + 3)] at hv
      refine ⟨hdc_mem j, hdc_mem (j + 1), fun h => hj1_ne (dc.hp_idx_inj h), fun r hr hr1 hr2 => ?_⟩
      change r ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w at hr
      rw [← dc.hp_idx_img] at hr
      rcases Finset.mem_image.mp hr with ⟨k, _, rfl⟩
      have hkj : k ≠ j := fun h => hr1 (congrArg dc.p_idx h)
      have hkj1 : k ≠ j + 1 := fun h => hr2 (congrArg dc.p_idx h)
      have hcyc := PolygonCore.cyclicOrder_succ (by omega : 3 ≤ dc.m + 3) hkj hkj1
      have h1mod : (⟨1 % (dc.m + 3), Nat.mod_lt 1 (by omega)⟩ : Fin (dc.m + 3)) = 1 :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [h1mod] at hcyc
      exact dc.hcyc j (j + 1) k hcyc
    refine ⟨dc.p_idx i, dc.p_idx (i + 1), hdc_edge i, hpos_i, htri_i, ?_, ?_, ?_⟩
    · intro l r hHne _ hHneg heq
      obtain ⟨h, hh⟩ := hHne
      have hB_lr := (isCCWEdge_iff_isCCWHullEdge hPoly B (dc.p_idx i) (dc.p_idx (i + 1))).mpr (hB_edge ⟨h, hh⟩)
      have heq1 : dc.p_idx i = l := (Prod.ext_iff.mp heq).1
      have heq2 : dc.p_idx (i + 1) = r := (Prod.ext_iff.mp heq).2
      have hhl : h ≠ l := fun e => (Finset.mem_sdiff.mp (heq1 ▸ hdc_mem i)).2 (e ▸ hh)
      have hhr : h ≠ r := fun e => (Finset.mem_sdiff.mp (heq2 ▸ hdc_mem (i + 1))).2 (e ▸ hh)
      have hpos := hB_lr.2.2.2 h (Finset.filter_subset _ _ hh) (heq1 ▸ hhl) (heq2 ▸ hhr)
      have hneg := hHneg h hh
      rw [heq1, heq2] at hpos
      linarith
    · intro x hx
      obtain ⟨Tx, hsub, _, rfl⟩ := hx
      exact hall_i Tx ((hPoly.shatters Tx _).mpr (hsub (by simp))) ((hPoly.shatters Tx _).mpr (hsub (by simp)))
    · intro u' v' huv' hpos' hy_conv
      have h_match : ∃ j : Fin (dc.m + 3), u' = dc.p_idx j ∧ v' = dc.p_idx (j + 1) := by
        have hu'D : u' ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w := huv'.1
        rw [← dc.hp_idx_img] at hu'D
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu'D
        have hv'eq : v' = dc.p_idx (j + 1) :=
          isCCWEdge_unique_succ cycD huv' (hdc_edge j)
        exact ⟨j, rfl, hv'eq⟩
      rcases h_match with ⟨j, rfl, rfl⟩
      have hclosed : InClosedTri (w D) (S (dc.p_idx j)) (S (dc.p_idx (j + 1))) (S y) :=
        (inClosedTri_iff_mem_convexHull _ _ _ _).mpr hy_conv
      have hy_notD : y ∉ D := (Finset.mem_sdiff.mp hyM).2
      have hyn1 : y ≠ dc.p_idx j := fun h => hy_notD (h ▸ hdc_mem j)
      have hyn2 : y ≠ dc.p_idx (j + 1) := fun h => hy_notD (h ▸ hdc_mem (j + 1))
      have h12 : dc.p_idx j ≠ dc.p_idx (j + 1) := (hdc_edge j).2.2.1
      have hopen : PolygonCore.InOpenTri (w D) (S (dc.p_idx j)) (S (dc.p_idx (j + 1))) (S y) :=
        PolygonCore.inOpenTri_of_noncollinear_inClosedTri hclosed
          (hPoly.no_three_collinear _ _ _ (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)
            (hPoly.s_inj.ne h12) (hPoly.s_inj.ne hyn2.symm) (hPoly.s_inj.ne hyn1.symm))
          (hPoly.no_three_collinear _ _ _ (Or.inl ⟨_, rfl⟩) (Or.inr ⟨D, rfl⟩) (Or.inl ⟨_, rfl⟩)
            (hPoly.s_ne_w _ D) (hPoly.s_ne_w _ D).symm (hPoly.s_inj.ne hyn2.symm))
          (hPoly.no_three_collinear _ _ _ (Or.inr ⟨D, rfl⟩) (Or.inl ⟨_, rfl⟩) (Or.inl ⟨_, rfl⟩)
            (hPoly.s_ne_w _ D).symm (hPoly.s_inj.ne hyn1.symm) (hPoly.s_ne_w _ D).symm)
      have hj_eq : j = i := huniq_i j ⟨hpos', hopen⟩
      subst hj_eq
      exact ⟨rfl, rfl⟩
  · -- endpoint_back_criterion
    dsimp only []
    rw [hcert_eq]
    intro hHne hD5 l r p y_other hlD hrD hlr hed hHneg hp_end ⟨O, hpO, hOnoadj, hp_back⟩
    let B := hullVertices S
    let H := PolygonCore.certifiedSet P S w
    let D := B \ H
    have hB3 : 3 ≤ B.card := PolygonCore.hullVertices_card_ge_three hn hPoly
    have hD3 : 3 ≤ D.card := by dsimp [D, B, H] at hD5 ⊢; omega
    obtain ⟨cb⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly (Finset.Subset.refl B) hB3
    have ⟨h₀, hh₀⟩ := hHne
    obtain ⟨vc⟩ := PolygonCore.exists_q_visibleContour hPoly hn cb (Finset.mem_filter.mp hh₀).2
    obtain ⟨k_f, k_g, l₀, r₀, hkf0, hkfg, hkg_lt, hl0_eq, hr0_eq, hl0D, hr0D, hl0r0, hblock, _, _⟩ :=
      PolygonCore.certified_structure hPoly hn cb vc hHne
    have hcb_ex : ∀ x ∈ B, ∃ k : ℕ, k < cb.m + 3 ∧ cb.p_idx (PolygonCore.finShift vc.i_max k) = x := by
      intro x hx; rw [← cb.hp_idx_img] at hx
      rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
      refine ⟨(j - vc.i_max).val, (j - vc.i_max).isLt, ?_⟩
      rw [PolygonCore.finShift_eq_add vc.i_max (j - vc.i_max).isLt]; simp [add_sub_cancel]
    -- Note (l, r) must equal (l₀, r₀) since both are CCW edges of D with H on the negative side!
    have hl_eq_l0 : l = l₀ ∧ r = r₀ := by
      have hl_memB : l ∈ B := Finset.sdiff_subset hlD
      have hr_memB : r ∈ B := Finset.sdiff_subset hrD
      obtain ⟨kl, hkl_lt, hkl_eq⟩ := hcb_ex l hl_memB
      obtain ⟨kr, hkr_lt, hkr_eq⟩ := hcb_ex r hr_memB
      have hkl_notH : ¬ (k_f ≤ kl ∧ kl ≤ k_g) := by
        rw [hblock kl hkl_lt, hkl_eq]; exact (Finset.mem_sdiff.mp hlD).2
      have hkr_notH : ¬ (k_f ≤ kr ∧ kr ≤ k_g) := by
        rw [hblock kr hkr_lt, hkr_eq]; exact (Finset.mem_sdiff.mp hrD).2
      have hd_vc := vc.hd_lt
      have h_lr_neg : orient2D (S l) (S r) (S h₀) < 0 := hHneg h₀ hh₀
      obtain ⟨kh0, hkh0_lt, hkh0_eq⟩ := hcb_ex h₀ (Finset.filter_subset _ _ hh₀)
      have hkh0_range : k_f ≤ kh0 ∧ kh0 ≤ k_g := (hblock kh0 hkh0_lt).mpr (by rw [hkh0_eq]; exact hh₀)
      have hkl_ne_r : kl ≠ kr := fun e => hlr (by rw [← hkl_eq, ← hkr_eq, e])
      have hkl_ne_h : kl ≠ kh0 := fun e => (Finset.mem_sdiff.mp hlD).2 (by rw [← hkl_eq, e, hkh0_eq]; exact hh₀)
      have hkr_ne_h : kr ≠ kh0 := fun e => (Finset.mem_sdiff.mp hrD).2 (by rw [← hkr_eq, e, hkh0_eq]; exact hh₀)
      have h_not_cyc_lr_h : ¬ PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kl)
          (PolygonCore.finShift vc.i_max kr) (PolygonCore.finShift vc.i_max kh0) := by
        intro hcyc
        have hpos := cb.hcyc _ _ _ hcyc
        rw [hkl_eq, hkr_eq, hkh0_eq] at hpos
        linarith
      have hkl_lt_kf : kl < k_f := by
        by_contra hge
        have hkl_gt : k_g < kl := by omega
        rcases (by omega : kr < k_f ∨ k_g < kr) with hkr_lt' | hkr_gt'
        · exact h_not_cyc_lr_h (PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
            (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : kr < kh0) (by omega) hkl_lt)))
        · have hkr_lt_kl : kr < kl := by
            by_contra hle
            have hlt : kl < kr := by omega
            exact h_not_cyc_lr_h (PolygonCore.cyclicOrder_cycle
              (PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hlt hkr_lt))
          have hl0_ne_l : l₀ ≠ l := fun e => by
            have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hl0_eq.symm.trans (e.trans hkl_eq.symm)))
            rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f - 1 < cb.m + 3),
              PolygonCore.finShift_eq_add vc.i_max hkl_lt, add_sub_cancel_left, add_sub_cancel_left] at this
            have hv := congrArg Fin.val this
            simp only [Fin.val_mk] at hv
            omega
          have hl0_ne_r : l₀ ≠ r := fun e => by
            have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hl0_eq.symm.trans (e.trans hkr_eq.symm)))
            rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f - 1 < cb.m + 3),
              PolygonCore.finShift_eq_add vc.i_max hkr_lt, add_sub_cancel_left, add_sub_cancel_left] at this
            have hv := congrArg Fin.val this
            simp only [Fin.val_mk] at hv
            omega
          have hpos_l0 := hed.2.2.2 l₀ hl0D hl0_ne_l hl0_ne_r
          have hcyc_l0 := PolygonCore.cyclicOrder_finShift vc.i_max (by omega : k_f - 1 < kr) hkr_lt_kl hkl_lt
          have hneg_l0 := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_cycle hcyc_l0)
          rw [← hl0_eq, hkr_eq, hkl_eq, orient2D_swap12] at hneg_l0
          linarith
      have hkr_gt_kg : k_g < kr := by
        by_contra hle
        have hkr_lt' : kr < k_f := by omega
        have hkr_lt_kl : kr < kl := by
          by_contra hle'
          have hlt : kl < kr := by omega
          exact h_not_cyc_lr_h (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) hkh0_lt)
        have hr0_ne_l : r₀ ≠ l := fun e => by
          have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hr0_eq.symm.trans (e.trans hkl_eq.symm)))
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_g + 1 < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max hkl_lt, add_sub_cancel_left, add_sub_cancel_left] at this
          have hv := congrArg Fin.val this
          simp only [Fin.val_mk] at hv
          omega
        have hr0_ne_r : r₀ ≠ r := fun e => by
          have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hr0_eq.symm.trans (e.trans hkr_eq.symm)))
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_g + 1 < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max hkr_lt, add_sub_cancel_left, add_sub_cancel_left] at this
          have hv := congrArg Fin.val this
          simp only [Fin.val_mk] at hv
          omega
        have hpos_r0 := hed.2.2.2 r₀ hr0D hr0_ne_l hr0_ne_r
        have hcyc_r0 := PolygonCore.cyclicOrder_finShift vc.i_max hkr_lt_kl (by omega : kl < k_g + 1) (by omega)
        have hneg_r0 := cb.hcyc _ _ _ hcyc_r0
        rw [← hr0_eq, hkr_eq, hkl_eq, orient2D_swap12] at hneg_r0
        linarith
      have hkl_eq_kf : kl = k_f - 1 := by
        by_contra hne
        have hlt : kl < k_f - 1 := by omega
        have hl0_ne_l : l₀ ≠ l := fun e => by
          have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hl0_eq.symm.trans (e.trans hkl_eq.symm)))
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f - 1 < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max hkl_lt, add_sub_cancel_left, add_sub_cancel_left] at this
          have hv := congrArg Fin.val this
          simp only [Fin.val_mk] at hv
          omega
        have hl0_ne_r : l₀ ≠ r := fun e => by
          have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hl0_eq.symm.trans (e.trans hkr_eq.symm)))
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_f - 1 < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max hkr_lt, add_sub_cancel_left, add_sub_cancel_left] at this
          have hv := congrArg Fin.val this
          simp only [Fin.val_mk] at hv
          omega
        have hpos_l0 := hed.2.2.2 l₀ hl0D hl0_ne_l hl0_ne_r
        have hcyc_l0 := PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega : k_f - 1 < kr) hkr_lt
        have hneg_l0 := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle hcyc_l0))
        rw [← hl0_eq, hkr_eq, hkl_eq, orient2D_swap12] at hneg_l0
        linarith
      have hkr_eq_kg : kr = k_g + 1 := by
        by_contra hne
        have hgt : k_g + 1 < kr := by omega
        have hr0_ne_l : r₀ ≠ l := fun e => by
          have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hr0_eq.symm.trans (e.trans hkl_eq.symm)))
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_g + 1 < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max hkl_lt, add_sub_cancel_left, add_sub_cancel_left] at this
          have hv := congrArg Fin.val this
          simp only [Fin.val_mk] at hv
          omega
        have hr0_ne_r : r₀ ≠ r := fun e => by
          have := congrArg (· - vc.i_max) (cb.hp_idx_inj (hr0_eq.symm.trans (e.trans hkr_eq.symm)))
          rw [PolygonCore.finShift_eq_add vc.i_max (by omega : k_g + 1 < cb.m + 3),
            PolygonCore.finShift_eq_add vc.i_max hkr_lt, add_sub_cancel_left, add_sub_cancel_left] at this
          have hv := congrArg Fin.val this
          simp only [Fin.val_mk] at hv
          omega
        have hpos_r0 := hed.2.2.2 r₀ hr0D hr0_ne_l hr0_ne_r
        have hcyc_r0 := PolygonCore.cyclicOrder_finShift vc.i_max (by omega : kl < k_g + 1) hgt hkr_lt
        have hneg_r0 := cb.hcyc _ _ _ (PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle hcyc_r0))
        rw [← hr0_eq, hkr_eq, hkl_eq, orient2D_swap12] at hneg_r0
        linarith
      exact ⟨by rw [← hkl_eq, hkl_eq_kf, hl0_eq], by rw [← hkr_eq, hkr_eq_kg, hr0_eq]⟩
    obtain ⟨hl_eq', hr_eq'⟩ := hl_eq_l0
    subst hl_eq' hr_eq'
    obtain ⟨dc⟩ := PolygonCore.exists_cyclicSubsetBoundary hPoly Finset.sdiff_subset hD3
    have hp_back' := (isBackVertexOf_iff_isBackVertex hPoly Finset.Subset.rfl hB3).mp hp_back
    have hOnoadj' : ∀ a ∈ O ∩ D, ∀ b ∈ O ∩ D, ¬ PolygonCore.IsCCWHullEdge (B.image S) (S a) (S b) :=
      fun a ha b hb he => hOnoadj a ha b hb ((isCCWEdge_iff_isCCWHullEdge hPoly B a b).mpr he)
    obtain ⟨h_part1, h_part2⟩ := PolygonCore.endpoint_back_vertex_criterion hPoly hn cb vc hHne hD5 dc
      hkf0 hkfg hkg_lt hl0_eq hr0_eq hblock hp_end O hpO hOnoadj' hp_back'
    have hdc_mem : ∀ j : Fin (dc.m + 3), dc.p_idx j ∈ D := fun j => by
      have h := Finset.mem_image_of_mem dc.p_idx (Finset.mem_univ j)
      rwa [dc.hp_idx_img] at h
    have hdc_edge : ∀ j : Fin (dc.m + 3), IsCCWEdge S D (dc.p_idx j) (dc.p_idx (j + 1)) := by
      intro j
      haveI : NeZero (dc.m + 3) := ⟨by omega⟩
      have hj1_ne : j ≠ j + 1 := by
        intro h; nth_rw 1 [← add_zero j] at h
        have hv := congrArg Fin.val (add_left_cancel h)
        simp [Nat.mod_eq_of_lt (by omega : 1 < dc.m + 3)] at hv
      refine ⟨hdc_mem j, hdc_mem (j + 1), fun h => hj1_ne (dc.hp_idx_inj h), fun z hz hz1 hz2 => ?_⟩
      change z ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w at hz
      rw [← dc.hp_idx_img] at hz
      rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩
      have hkj : k ≠ j := fun h => hz1 (congrArg dc.p_idx h)
      have hkj1 : k ≠ j + 1 := fun h => hz2 (congrArg dc.p_idx h)
      have hcyc := PolygonCore.cyclicOrder_succ (by omega : 3 ≤ dc.m + 3) hkj hkj1
      have h1mod : (⟨1 % (dc.m + 3), Nat.mod_lt 1 (by omega)⟩ : Fin (dc.m + 3)) = 1 :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [h1mod] at hcyc
      exact dc.hcyc j (j + 1) k hcyc
    have hD_conv : IsConvexPos S D := hullVertices_convexPos S Finset.sdiff_subset
    have hD3' : 3 ≤ D.card := hD3
    obtain ⟨cycD⟩ := exists_ccwCycle S D (fun a _ b _ h => hPoly.s_inj h)
      (fun a _ b _ c _ hab hbc hac => hPoly.no_three_collinear _ _ _
        (Or.inl ⟨a, rfl⟩) (Or.inl ⟨b, rfl⟩) (Or.inl ⟨c, rfl⟩)
        (hPoly.s_inj.ne hab) (hPoly.s_inj.ne hbc) (hPoly.s_inj.ne hac))
      hD_conv (show D.card = (D.card - 3) + 3 by omega)
    refine ⟨?_, ?_⟩
    · intro h hh u v huv htri
      by_cases huv_lr : (u = l ∧ v = r)
      · rcases hp_end with ⟨_, hyr⟩ | ⟨_, hyl⟩
        · exact Or.inr (huv_lr.2.trans hyr.symm)
        · exact Or.inl (huv_lr.1.trans hyl.symm)
      · have huD : u ∈ PolygonCore.hullVertices S \ PolygonCore.certifiedSet P S w := huv.1
        rw [← dc.hp_idx_img] at huD
        rcases Finset.mem_image.mp huD with ⟨i, _, rfl⟩
        have hv_eq : v = dc.p_idx (i + 1) := isCCWEdge_unique_succ cycD huv (hdc_edge i)
        subst hv_eq
        have huv_B : IsCCWEdge S B (dc.p_idx i) (dc.p_idx (i + 1)) := by
          have h_not_both_lr : ¬ ((dc.p_idx i = l ∨ dc.p_idx i = r) ∧
              (dc.p_idx (i + 1) = l ∨ dc.p_idx (i + 1) = r)) := by
            rintro ⟨hi | hi, hi1 | hi1⟩
            · exact huv.2.2.1 (hi.trans hi1.symm)
            · exact huv_lr ⟨hi, hi1⟩
            · have ⟨d, hdD, hd1, hd2⟩ : ∃ d ∈ D, d ≠ l ∧ d ≠ r := by
                have hlt : ({l, r} : Finset (Fin 10)).card < D.card := by
                  have := Finset.card_le_two (a := l) (b := r); omega
                obtain ⟨d, hd1, hd2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd2
                exact ⟨d, hd1, hd2.1, hd2.2⟩
              have ho1 := huv.2.2.2 d hdD (hi ▸ hd2) (hi1 ▸ hd1)
              obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.sdiff_subset hdD)
              have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
                rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hdD).2
              have hkd_ne_l : kd ≠ k_f - 1 := fun e => hd1 (by rw [← hkd_eq, hl0_eq, e])
              have hkd_ne_r : kd ≠ k_g + 1 := fun e => hd2 (by rw [← hkd_eq, hr0_eq, e])
              have hd_vc := vc.hd_lt
              have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max (k_f - 1))
                  (PolygonCore.finShift vc.i_max (k_g + 1)) (PolygonCore.finShift vc.i_max kd) := by
                rcases (by omega : kd < k_f - 1 ∨ k_g + 1 < kd) with hlt | hgt
                · exact PolygonCore.cyclicOrder_cycle
                    (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega))
                · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkd_lt
              have ho2 := cb.hcyc _ _ _ hcyc
              rw [← hl0_eq, ← hr0_eq, hkd_eq] at ho2
              rw [hi, hi1, orient2D_swap12] at ho1
              linarith
            · exact huv.2.2.1 (hi.trans hi1.symm)
          have h_edge_B_of_D_sub : ∀ d ∈ D, d ≠ l → d ≠ r → ∀ x ∈ D,
              (IsCCWEdge S D x d → IsCCWEdge S B x d) ∧ (IsCCWEdge S D d x → IsCCWEdge S B d x) := by
            intro d hd hdl hdr x hx
            obtain ⟨kd, hkd_lt, hkd_eq⟩ := hcb_ex d (Finset.mem_sdiff.mp hd).1
            have hkd_notH : ¬ (k_f ≤ kd ∧ kd ≤ k_g) := by
              rw [hblock kd hkd_lt, hkd_eq]; exact (Finset.mem_sdiff.mp hd).2
            have hkd_ne_l : kd ≠ k_f - 1 := fun e => hdl (by rw [← hkd_eq, hl0_eq, e])
            have hkd_ne_r : kd ≠ k_g + 1 := fun e => hdr (by rw [← hkd_eq, hr0_eq, e])
            have hcb_mem : ∀ j : Fin (cb.m + 3), cb.p_idx j ∈ B := fun j => by
              have h' := Finset.mem_image_of_mem cb.p_idx (Finset.mem_univ j); rwa [cb.hp_idx_img] at h'
            let kp := if kd = 0 then cb.m + 2 else kd - 1
            have hkp_lt : kp < cb.m + 3 := by dsimp [kp]; split_ifs <;> omega
            have hp_D : cb.p_idx (PolygonCore.finShift vc.i_max kp) ∈ D := Finset.mem_sdiff.mpr
              ⟨hcb_mem _, by rw [← hblock kp hkp_lt]; dsimp [kp]; split_ifs with h0; have := vc.hd_lt; omega; omega⟩
            have hp_B : IsCCWEdge S B (cb.p_idx (PolygonCore.finShift vc.i_max kp)) d := by
              refine ⟨Finset.sdiff_subset hp_D, Finset.sdiff_subset hd, fun heq => ?_, fun z hz hzp hzd => ?_⟩
              · have hinj := cb.hp_idx_inj (heq.trans hkd_eq.symm)
                have hsub := congrArg (· - vc.i_max) hinj
                rw [PolygonCore.finShift_eq_add vc.i_max hkp_lt, PolygonCore.finShift_eq_add vc.i_max hkd_lt,
                  add_sub_cancel_left, add_sub_cancel_left] at hsub
                have hv := congrArg Fin.val hsub
                dsimp [kp] at hv; split_ifs at hv <;> omega
              · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
                have hkz_p : kz ≠ kp := fun e => hzp (by rw [← hkz_eq, e])
                have hkz_d : kz ≠ kd := fun e => hzd (by rw [← hkz_eq, ← hkd_eq, e])
                have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kp)
                    (PolygonCore.finShift vc.i_max kd) (PolygonCore.finShift vc.i_max kz) := by
                  dsimp [kp] at hkz_p ⊢; split_ifs at hkz_p ⊢ with h0
                  · subst h0; exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                      (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
                  · rcases (by omega : kz < kd - 1 ∨ kd < kz) with hlt | hgt
                    · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) hkd_lt)
                    · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
                rw [← hkz_eq, ← hkd_eq]; exact cb.hcyc _ _ _ hcyc
            have hp_D_edge : IsCCWEdge S D (cb.p_idx (PolygonCore.finShift vc.i_max kp)) d :=
              ⟨hp_D, hd, hp_B.2.2.1, fun z hz h1 h2 => hp_B.2.2.2 z (Finset.sdiff_subset hz) h1 h2⟩
            let ks := if kd + 1 = cb.m + 3 then 0 else kd + 1
            have hks_lt : ks < cb.m + 3 := by dsimp [ks]; split_ifs <;> omega
            have hs_D : cb.p_idx (PolygonCore.finShift vc.i_max ks) ∈ D := Finset.mem_sdiff.mpr
              ⟨hcb_mem _, by rw [← hblock ks hks_lt]; dsimp [ks]; split_ifs with hm; omega; have := vc.hd_lt; omega⟩
            have hs_B : IsCCWEdge S B d (cb.p_idx (PolygonCore.finShift vc.i_max ks)) := by
              refine ⟨Finset.sdiff_subset hd, Finset.sdiff_subset hs_D, fun heq => ?_, fun z hz hzd hzs => ?_⟩
              · have hinj := cb.hp_idx_inj (hkd_eq.trans heq)
                have hsub := congrArg (· - vc.i_max) hinj
                rw [PolygonCore.finShift_eq_add vc.i_max hkd_lt, PolygonCore.finShift_eq_add vc.i_max hks_lt,
                  add_sub_cancel_left, add_sub_cancel_left] at hsub
                have hv := congrArg Fin.val hsub
                dsimp [ks] at hv; split_ifs at hv <;> omega
              · obtain ⟨kz, hkz_lt, hkz_eq⟩ := hcb_ex z hz
                have hkz_d : kz ≠ kd := fun e => hzd (by rw [← hkz_eq, ← hkd_eq, e])
                have hkz_s : kz ≠ ks := fun e => hzs (by rw [← hkz_eq, e])
                have hcyc : PolygonCore.CyclicOrder (PolygonCore.finShift vc.i_max kd)
                    (PolygonCore.finShift vc.i_max ks) (PolygonCore.finShift vc.i_max kz) := by
                  dsimp [ks] at hkz_s ⊢; split_ifs at hkz_s ⊢ with hm
                  · have hkd_m2 : kd = cb.m + 2 := by omega
                    rw [hkd_m2] at hkz_d ⊢
                    exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_cycle
                      (PolygonCore.cyclicOrder_finShift vc.i_max (by omega : 0 < kz) (by omega : kz < cb.m + 2) (by omega)))
                  · rcases (by omega : kz < kd ∨ kd + 1 < kz) with hlt | hgt
                    · exact PolygonCore.cyclicOrder_cycle (PolygonCore.cyclicOrder_finShift vc.i_max hlt (by omega) (by omega : kd + 1 < cb.m + 3))
                    · exact PolygonCore.cyclicOrder_finShift vc.i_max (by omega) hgt hkz_lt
                rw [← hkz_eq, ← hkd_eq]; exact cb.hcyc _ _ _ hcyc
            have hs_D_edge : IsCCWEdge S D d (cb.p_idx (PolygonCore.finShift vc.i_max ks)) :=
              ⟨hd, hs_D, hs_B.2.2.1, fun z hz h1 h2 => hs_B.2.2.2 z (Finset.sdiff_subset hz) h1 h2⟩
            exact ⟨fun hD => by rw [isCCWEdge_unique_pred cycD hD hp_D_edge]; exact hp_B,
                   fun hD => by rw [isCCWEdge_unique_succ cycD hD hs_D_edge]; exact hs_B⟩
          by_cases hu_lr : dc.p_idx i = l ∨ dc.p_idx i = r
          · have hv_not : dc.p_idx (i + 1) ≠ l ∧ dc.p_idx (i + 1) ≠ r := by
              by_contra hno
              rw [not_and_or, not_not, not_not] at hno
              exact h_not_both_lr ⟨hu_lr, hno⟩
            exact (h_edge_B_of_D_sub (dc.p_idx (i + 1)) huv.2.1 hv_not.1 hv_not.2 (dc.p_idx i) huv.1).1 huv
          · push Not at hu_lr
            exact (h_edge_B_of_D_sub (dc.p_idx i) huv.1 hu_lr.1 hu_lr.2 (dc.p_idx (i + 1)) huv.2.1).2 huv
        have hh_pos_uv : 0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S h) :=
          huv_B.2.2.2 h (Finset.filter_subset _ _ hh)
            (fun e => (Finset.mem_sdiff.mp huv.1).2 (e ▸ hh))
            (fun e => (Finset.mem_sdiff.mp huv.2.1).2 (e ▸ hh))
        have hpos : 0 < orient2D (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (w D) := by
          rcases htri with ⟨μ₁, μ₂, μ₃, hμ1, _, _, hsum, hx1, hx2⟩
          have hid := orient2D_convex_comb3 (S (dc.p_idx i)) (S (dc.p_idx (i + 1)))
            (w D) (S (dc.p_idx i)) (S (dc.p_idx (i + 1))) (S h) μ₁ μ₂ μ₃ hsum hx1 hx2
          simp only [orient2D_self_outer, orient2D_self_right, mul_zero, add_zero] at hid
          rw [hid] at hh_pos_uv
          exact pos_of_mul_pos_right hh_pos_uv (le_of_lt hμ1)
        rcases h_part1 h hh i hpos htri with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
    · rintro ⟨O', hyO', hO'noadj, hy_back⟩
      exact h_part2 O' hyO'
        (fun a ha b hb he => hO'noadj a ha b hb ((isCCWEdge_iff_isCCWHullEdge hPoly B a b).mpr he))
        ((isBackVertexOf_iff_isBackVertex hPoly Finset.Subset.rfl hB3).mp hy_back)
  · -- half_plane_lemma
    intro Tv Tq a p c hpTv haTv hcTv haTq hpTq hcTq hap hpc hcross hiv
    obtain ⟨hsap, hoap⟩ := hap
    obtain ⟨hspc, hopc⟩ := hpc
    have ha_ne0 : orient2D (w Tv) (w Tq) (S a) ≠ 0 := by
      intro h0; rw [OnSameSide, h0, zero_mul] at hsap; exact lt_irrefl 0 hsap
    have hp_ne0 : orient2D (w Tv) (w Tq) (S p) ≠ 0 := by
      intro h0; rw [OnSameSide, h0, mul_zero] at hsap; exact lt_irrefl 0 hsap
    have hor_ap : 0 < orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S p) := by
      have hmul : (orient2D (w Tv) (w Tq) (S a)) ^ 2 *
          (orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S p)) =
          (orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S a)) *
          (orient2D (w Tv) (w Tq) (S a) * orient2D (w Tv) (w Tq) (S p)) := by ring
      nlinarith [sq_pos_of_ne_zero ha_ne0, mul_pos (by linarith : 0 < orient2D (w Tv) (S a) (S p) * orient2D (w Tv) (w Tq) (S a)) hsap]
    have hor_pc : 0 < orient2D (w Tv) (S p) (S c) * orient2D (w Tv) (w Tq) (S p) := by
      unfold OnSameSide at *; linarith
    have hiv' : Sees P (w Tv) (w Tq) ∨
        ∃ ie : Fin 10, Sees P (w Tv) (S ie) ∧ Sees P (w Tq) (S ie) ∧
          Sec5HP.SameSideOfLine (w Tv) (w Tq) (S ie) (S a) ∧
          0 < orient2D (w Tv) (S ie) (S a) * orient2D (w Tv) (w Tq) (S p) := by
      rcases hiv with hvq | ⟨e, heTv, heTq, he_ang⟩
      · exact Or.inl hvq
      · right
        refine ⟨e, (hPoly.shatters Tv e).mpr heTv, (hPoly.shatters Tq e).mpr heTq, he_ang.1, ?_⟩
        have he_same : 0 < orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S a) := he_ang.1
        have he_ne0 : orient2D (w Tv) (w Tq) (S e) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at he_same; exact lt_irrefl 0 he_same
        have hsame_ep : 0 < orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S p) := by
          have hmul : (orient2D (w Tv) (w Tq) (S a)) ^ 2 *
              (orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S p)) =
              (orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S a)) *
              (orient2D (w Tv) (w Tq) (S a) * orient2D (w Tv) (w Tq) (S p)) := by ring
          nlinarith [sq_pos_of_ne_zero ha_ne0, mul_pos he_same hsap]
        have hmul : (orient2D (w Tv) (w Tq) (S e)) ^ 2 *
            (orient2D (w Tv) (S e) (S a) * orient2D (w Tv) (w Tq) (S p)) =
            (orient2D (w Tv) (S e) (S a) * orient2D (w Tv) (w Tq) (S e)) *
            (orient2D (w Tv) (w Tq) (S e) * orient2D (w Tv) (w Tq) (S p)) := by ring
        nlinarith [sq_pos_of_ne_zero he_ne0, mul_pos (by linarith [he_ang.2] : 0 < orient2D (w Tv) (S e) (S a) * orient2D (w Tv) (w Tq) (S e)) hsame_ep]
    obtain ⟨H_hp, hH_test, _⟩ := Sec5HP.half_plane_lemma_orient hPoly Tv Tq a p c
      ((hPoly.shatters Tv p).mpr hpTv)
      (fun h => haTv ((hPoly.shatters Tv a).mp h))
      (fun h => hcTv ((hPoly.shatters Tv c).mp h))
      ((hPoly.shatters Tq a).mpr haTq)
      ((hPoly.shatters Tq p).mpr hpTq)
      ((hPoly.shatters Tq c).mpr hcTq)
      hsap (by unfold OnSameSide at hspc; change 0 < orient2D (w Tv) (w Tq) (S c) * orient2D (w Tv) (w Tq) (S p); linarith)
      hor_ap hor_pc hcross hiv'
    exact ⟨H_hp, hH_test⟩

end Sec2To5Bridge

export Sec2To5Bridge (mk_sec2To5Interface)

end
