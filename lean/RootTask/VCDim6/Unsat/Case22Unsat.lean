import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case22
import RootTask.VCDim6.Cases.Shards.Case22_C000
import RootTask.VCDim6.Cases.Shards.Case22_C001
import RootTask.VCDim6.Cases.Shards.Case22_R000
import RootTask.VCDim6.Cases.Shards.Case22_R001
import RootTask.VCDim6.Cases.Shards.Case22_R002

noncomputable section

namespace VCDim6

theorem case22_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case22_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case22_vars_ok
  have hm := masterRangeSound_xH val Cases.case22_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case22_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case22_core_001 hm
  have hm := verifiedMidRup_sound Cases.case22_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case22_rup_001 hm
  exact verifiedFinRup_sound Cases.case22_rup_002 hm

end VCDim6

end
