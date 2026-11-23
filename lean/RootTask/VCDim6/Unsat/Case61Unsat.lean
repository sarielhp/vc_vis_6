import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case61
import RootTask.VCDim6.Cases.Shards.Case61_C000
import RootTask.VCDim6.Cases.Shards.Case61_C001
import RootTask.VCDim6.Cases.Shards.Case61_C002
import RootTask.VCDim6.Cases.Shards.Case61_C003
import RootTask.VCDim6.Cases.Shards.Case61_R000
import RootTask.VCDim6.Cases.Shards.Case61_R001
import RootTask.VCDim6.Cases.Shards.Case61_R002
import RootTask.VCDim6.Cases.Shards.Case61_R003
import RootTask.VCDim6.Cases.Shards.Case61_R004
import RootTask.VCDim6.Cases.Shards.Case61_R005
import RootTask.VCDim6.Cases.Shards.Case61_R006
import RootTask.VCDim6.Cases.Shards.Case61_R007

noncomputable section

namespace VCDim6

theorem case61_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case61_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case61_vars_ok
  have hm := masterRangeSound_xH val Cases.case61_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case61_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case61_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case61_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case61_core_003 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case61_rup_006 hm
  exact verifiedFinRup_sound Cases.case61_rup_007 hm

end VCDim6

end
