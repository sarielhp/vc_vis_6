import Mathlib
import RootTask.Defs
import RootTask.Sec9Elim

open scoped Classical BigOperators
open Finset

noncomputable section

/-- Theorem 9.1(1) (`upper_9.tex` Theorem `v-epigraph`(1)):
    Five V-epigraphs `f_i(x) = max(a_i x + b_i, c_i x + d_i)` in `ℝ²` cannot realize all `32` strict Boolean masks. -/
theorem five_v_epigraphs_not_all_32_masks (f : Fin 5 → VFunc) :
    ¬ (∀ m : Fin 5 → Bool, ∃ p : ℝ × ℝ, RealizesVMask f m p) :=
  Sec9.five_v_epigraphs_not_all_32_masks_proved f

end
