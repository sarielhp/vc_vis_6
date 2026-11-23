import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case08
import RootTask.VCDim6.Cases.Shards.Case08_C000
import RootTask.VCDim6.Cases.Shards.Case08_C001
import RootTask.VCDim6.Cases.Shards.Case08_C002
import RootTask.VCDim6.Cases.Shards.Case08_C003
import RootTask.VCDim6.Cases.Shards.Case08_C004
import RootTask.VCDim6.Cases.Shards.Case08_C005
import RootTask.VCDim6.Cases.Shards.Case08_C006
import RootTask.VCDim6.Cases.Shards.Case08_C007
import RootTask.VCDim6.Cases.Shards.Case08_R000
import RootTask.VCDim6.Cases.Shards.Case08_R001
import RootTask.VCDim6.Cases.Shards.Case08_R002
import RootTask.VCDim6.Cases.Shards.Case08_R003
import RootTask.VCDim6.Cases.Shards.Case08_R004
import RootTask.VCDim6.Cases.Shards.Case08_R005
import RootTask.VCDim6.Cases.Shards.Case08_R006
import RootTask.VCDim6.Cases.Shards.Case08_R007
import RootTask.VCDim6.Cases.Shards.Case08_R008
import RootTask.VCDim6.Cases.Shards.Case08_R009
import RootTask.VCDim6.Cases.Shards.Case08_R010
import RootTask.VCDim6.Cases.Shards.Case08_R011
import RootTask.VCDim6.Cases.Shards.Case08_R012

noncomputable section

namespace VCDim6

theorem case08_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case08_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case08_vars_ok
  have hm := masterRangeSound_xH val Cases.case08_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case08_core_007 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case08_rup_011 hm
  exact verifiedFinRup_sound Cases.case08_rup_012 hm

end VCDim6

end
