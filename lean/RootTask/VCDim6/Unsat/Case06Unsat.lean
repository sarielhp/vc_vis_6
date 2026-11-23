import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case06
import RootTask.VCDim6.Cases.Shards.Case06_C000
import RootTask.VCDim6.Cases.Shards.Case06_C001
import RootTask.VCDim6.Cases.Shards.Case06_C002
import RootTask.VCDim6.Cases.Shards.Case06_C003
import RootTask.VCDim6.Cases.Shards.Case06_C004
import RootTask.VCDim6.Cases.Shards.Case06_C005
import RootTask.VCDim6.Cases.Shards.Case06_C006
import RootTask.VCDim6.Cases.Shards.Case06_R000
import RootTask.VCDim6.Cases.Shards.Case06_R001
import RootTask.VCDim6.Cases.Shards.Case06_R002
import RootTask.VCDim6.Cases.Shards.Case06_R003
import RootTask.VCDim6.Cases.Shards.Case06_R004
import RootTask.VCDim6.Cases.Shards.Case06_R005
import RootTask.VCDim6.Cases.Shards.Case06_R006
import RootTask.VCDim6.Cases.Shards.Case06_R007
import RootTask.VCDim6.Cases.Shards.Case06_R008
import RootTask.VCDim6.Cases.Shards.Case06_R009
import RootTask.VCDim6.Cases.Shards.Case06_R010
import RootTask.VCDim6.Cases.Shards.Case06_R011

noncomputable section

namespace VCDim6

theorem case06_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case06_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case06_vars_ok
  have hm := masterRangeSound_xH val Cases.case06_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case06_core_006 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case06_rup_010 hm
  exact verifiedFinRup_sound Cases.case06_rup_011 hm

end VCDim6

end
