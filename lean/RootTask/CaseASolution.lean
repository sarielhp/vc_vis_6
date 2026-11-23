import Mathlib
import RootTask.Defs
import RootTask.CaseAElim

open scoped Classical BigOperators
open Finset

noncomputable section

/-- Section 10.4 (Case A Origin Subcase, including Proposition 10.10):
    Five nondegenerate open wedges with apices in `Q₃ = (-∞, 0)²` all containing `(0, 0)`
    cannot shatter all `32` strict masks on the L-shaped domain `Ω = {p ∈ ℝ² : p.1 < 0 ∨ p.2 < 0}`. -/
theorem five_wedges_L_domain_caseA_origin
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p))
    (W : Fin 5 → OpenWedge)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (h_orig : ∀ i : Fin 5, (W i).MemOpen (0, 0)) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p) := by
  intro h_shat_primal
  have h_no_vdata : ∀ f : Fin 5 → CaseA.VFuncData,
      ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, CaseA.RealizesVDataMask f m p) := by
    intro f hf
    apply h_thm1 (fun i => ⟨(f i).a, (f i).b, (f i).c, (f i).d, (f i).hle⟩)
    intro m
    obtain ⟨p, hp⟩ := hf m
    refine ⟨p, fun i => ?_⟩
    simpa [RealizesVMask, VFunc.eval, CaseA.RealizesVDataMask, CaseA.VFuncData.eval] using hp i
  have h_orig_dot : ∀ i : Fin 5,
      0 < -CaseA.dot2 (W i).u₁ (W i).y ∧ 0 < -CaseA.dot2 (W i).u₂ (W i).y := by
    intro i
    obtain ⟨h1, h2⟩ := h_orig i
    refine ⟨?_, ?_⟩ <;> { unfold CaseA.dot2; linarith }
  obtain ⟨P₀, _, hP₀_iff⟩ := CaseA.DualConfig.ofPrimal_spec
    (fun i => (W i).y) (fun i => (W i).u₁) (fun i => (W i).u₂)
    (fun i => (W i).h_nondeg) h_apex h_orig_dot
  have h_shat_dual0 : ∀ m : Fin 5 → Bool,
      ∃ z : ℝ × ℝ, CaseA.InOmega z ∧ CaseA.RealizesDualMask P₀ m z := by
    intro m
    obtain ⟨z, hz_om, hz_mask⟩ := h_shat_primal m
    refine ⟨z, hz_om, fun i => ?_⟩
    have hm_i := hz_mask i
    by_cases hmi : m i
    · simp only [hmi, ↓reduceIte] at hm_i ⊢
      exact (hP₀_iff i z).1.mpr hm_i
    · simp only [hmi, Bool.false_eq_true, ↓reduceIte] at hm_i ⊢
      exact (hP₀_iff i z).2.mpr hm_i
  obtain ⟨P, hgp, h_shat⟩ := CaseA.exists_genPos_shattering P₀ h_shat_dual0
  have htop : ∀ {t : ℝ}, 0 ≤ t → t ≤ 3 → 0 < CaseA.topEnv P t :=
    CaseA.topEnv_pos_of_shattering h_no_vdata P hgp h_shat
  exact CaseA.elim_n7_all P hgp htop h_shat

end
