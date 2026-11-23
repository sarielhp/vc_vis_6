import RootTask.VCDim6.CoreClauseSoundness
import RootTask.VCDim6.Cases.Case32

noncomputable section

namespace VCDim6

theorem case32_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case32_spec) : False :=
  unsat_of_valid_canonical_and_cert hV (by decide) Cases.case32_cert_ok

end VCDim6

end
