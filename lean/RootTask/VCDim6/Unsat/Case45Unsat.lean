import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case45
import RootTask.VCDim6.Cases.Shards.Case45_C000
import RootTask.VCDim6.Cases.Shards.Case45_C001
import RootTask.VCDim6.Cases.Shards.Case45_C002
import RootTask.VCDim6.Cases.Shards.Case45_R000
import RootTask.VCDim6.Cases.Shards.Case45_R001
import RootTask.VCDim6.Cases.Shards.Case45_R002
import RootTask.VCDim6.Cases.Shards.Case45_R003
import RootTask.VCDim6.Cases.Shards.Case45_R004

noncomputable section

namespace VCDim6

theorem case45_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case45_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case45_vars_ok
  have hm := masterRangeSound_xH val Cases.case45_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case45_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case45_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case45_core_002 hm
  have hm := verifiedMidRup_sound Cases.case45_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case45_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case45_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case45_rup_003 hm
  exact verifiedFinRup_sound Cases.case45_rup_004 hm

end VCDim6

end
