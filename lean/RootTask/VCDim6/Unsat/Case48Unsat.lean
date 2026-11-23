import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case48
import RootTask.VCDim6.Cases.Shards.Case48_C000
import RootTask.VCDim6.Cases.Shards.Case48_R000
import RootTask.VCDim6.Cases.Shards.Case48_R001

noncomputable section

namespace VCDim6

theorem case48_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case48_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case48_vars_ok
  have hm := masterRangeSound_xH val Cases.case48_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case48_core_000 hm
  have hm := verifiedMidRup_sound Cases.case48_rup_000 hm
  exact verifiedFinRup_sound Cases.case48_rup_001 hm

end VCDim6

end
