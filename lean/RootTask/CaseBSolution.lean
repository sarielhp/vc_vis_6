import Mathlib
import RootTask.Defs
import RootTask.CaseBTri
import RootTask.CaseBFace
import RootTask.CaseBK1
import RootTask.CaseBK234

open scoped Classical BigOperators
open Finset CaseB

noncomputable section

theorem five_wedges_L_domain_caseB
    (h_thm1 : ∀ f : Fin 5 → VFunc, ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p))
    (W : Fin 5 → OpenWedge)
    (h_apex : ∀ i : Fin 5, (W i).y.1 < 0 ∧ (W i).y.2 < 0)
    (h_pa : ∃ pa : ℝ × ℝ, 0 < pa.1 ∧ (∀ i : Fin 5, (W i).MemOpen pa))
    (h_pb : ∃ pb : ℝ × ℝ, 0 < pb.2 ∧ (∀ i : Fin 5, (W i).MemOpen pb))
    (h_disj_q1 : ¬ ∃ q : ℝ × ℝ, 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ∀ i : Fin 5, (W i).MemOpen q) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, (p.1 < 0 ∨ p.2 < 0) ∧ RealizesWedgeMask W m p) := by
  intro h_masks
  obtain ⟨pa, hxa, ha⟩ := h_pa
  obtain ⟨pb, hyb, hb⟩ := h_pb
  obtain ⟨hya, hxb, hC⟩ := caseB_pa_pb_signs W pa pb hxa ha hyb hb h_disj_q1
  obtain ⟨i_ex, hi_ex⟩ := caseB_Lgt_nonempty W pa pb h_apex hxa hya hxb hyb hC ha hb h_disj_q1
  obtain ⟨W', h_apex', ha', hb', _, h_lgt_iff, h_masks', hGP⟩ :=
    exists_gp_perturbation W pa pb h_apex hxa hya hxb hyb hC ha hb h_masks
  let Lgt : Finset (Fin 5) := Finset.univ.filter (fun i : Fin 5 => isLgt (W' i) pa pb)
  have hk_pos : 1 ≤ Lgt.card :=
    Finset.card_pos.mpr ⟨i_ex, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h_lgt_iff i_ex).mpr hi_ex⟩⟩
  have hk_le : Lgt.card ≤ 5 :=
    (Finset.card_filter_le _ _).trans_eq (by rw [Finset.card_fin])
  rcases (by omega : Lgt.card = 1 ∨ Lgt.card = 2 ∨ Lgt.card = 3 ∨ Lgt.card = 4 ∨ Lgt.card = 5)
      with hk1 | hk2 | hk3 | hk4 | hk5
  · exact caseB_k1_elim hGP pa pb h_apex' hxa hya hxb hyb hC ha' hb' h_masks' hk1
  · exact caseB_k2_k3_elim hGP pa pb h_apex' hxa hya hxb hyb hC ha' hb' h_masks' (Or.inl hk2)
  · exact caseB_k2_k3_elim hGP pa pb h_apex' hxa hya hxb hyb hC ha' hb' h_masks' (Or.inr hk3)
  · exact caseB_k4_elim hGP pa pb h_apex' hxa hya hxb hyb hC ha' hb' h_masks' hk4
  · have hLgt_eq : Lgt = Finset.univ :=
      Finset.eq_univ_of_card Lgt (by rw [hk5, Fintype.card_fin])
    have h_all_gt : ∀ i : Fin 5, isLgt (W' i) pa pb := fun i => by
      have hi : i ∈ Lgt := by rw [hLgt_eq]; exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2
    have h_all' : ∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesWedgeMask W' m p := fun m =>
      let ⟨p, _, hp⟩ := h_masks' m; ⟨p, hp⟩
    exact caseB_k5_elim h_thm1 W' pa pb h_apex' hxa hya hxb hyb hC ha' hb' h_all_gt h_all'
end
