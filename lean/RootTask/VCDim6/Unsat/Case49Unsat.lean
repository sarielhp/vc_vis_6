import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case49
import RootTask.VCDim6.Cases.Shards.Case49_C000
import RootTask.VCDim6.Cases.Shards.Case49_C001
import RootTask.VCDim6.Cases.Shards.Case49_R000
import RootTask.VCDim6.Cases.Shards.Case49_R001

noncomputable section

namespace VCDim6

theorem case49_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case49_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case49_vars_ok
  have hm := masterRangeSound_xH val Cases.case49_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case49_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case49_core_001 hm
  have hm := verifiedMidRup_sound Cases.case49_rup_000 hm
  exact verifiedFinRup_sound Cases.case49_rup_001 hm

end VCDim6

end
