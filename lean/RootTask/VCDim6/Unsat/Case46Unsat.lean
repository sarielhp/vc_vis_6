import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case46
import RootTask.VCDim6.Cases.Shards.Case46_C000
import RootTask.VCDim6.Cases.Shards.Case46_C001
import RootTask.VCDim6.Cases.Shards.Case46_C002
import RootTask.VCDim6.Cases.Shards.Case46_C003
import RootTask.VCDim6.Cases.Shards.Case46_C004
import RootTask.VCDim6.Cases.Shards.Case46_C005
import RootTask.VCDim6.Cases.Shards.Case46_C006
import RootTask.VCDim6.Cases.Shards.Case46_C007
import RootTask.VCDim6.Cases.Shards.Case46_C008
import RootTask.VCDim6.Cases.Shards.Case46_C009
import RootTask.VCDim6.Cases.Shards.Case46_C010
import RootTask.VCDim6.Cases.Shards.Case46_R000
import RootTask.VCDim6.Cases.Shards.Case46_R001
import RootTask.VCDim6.Cases.Shards.Case46_R002
import RootTask.VCDim6.Cases.Shards.Case46_R003
import RootTask.VCDim6.Cases.Shards.Case46_R004
import RootTask.VCDim6.Cases.Shards.Case46_R005
import RootTask.VCDim6.Cases.Shards.Case46_R006
import RootTask.VCDim6.Cases.Shards.Case46_R007
import RootTask.VCDim6.Cases.Shards.Case46_R008
import RootTask.VCDim6.Cases.Shards.Case46_R009
import RootTask.VCDim6.Cases.Shards.Case46_R010
import RootTask.VCDim6.Cases.Shards.Case46_R011
import RootTask.VCDim6.Cases.Shards.Case46_R012
import RootTask.VCDim6.Cases.Shards.Case46_R013
import RootTask.VCDim6.Cases.Shards.Case46_R014
import RootTask.VCDim6.Cases.Shards.Case46_R015
import RootTask.VCDim6.Cases.Shards.Case46_R016
import RootTask.VCDim6.Cases.Shards.Case46_R017
import RootTask.VCDim6.Cases.Shards.Case46_R018
import RootTask.VCDim6.Cases.Shards.Case46_R019
import RootTask.VCDim6.Cases.Shards.Case46_R020
import RootTask.VCDim6.Cases.Shards.Case46_R021
import RootTask.VCDim6.Cases.Shards.Case46_R022
import RootTask.VCDim6.Cases.Shards.Case46_R023
import RootTask.VCDim6.Cases.Shards.Case46_R024

noncomputable section

namespace VCDim6

theorem case46_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case46_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case46_vars_ok
  have hm := masterRangeSound_xH val Cases.case46_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_007 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_008 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_009 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case46_core_010 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_022 hm
  have hm := verifiedMidRup_sound Cases.case46_rup_023 hm
  exact verifiedFinRup_sound Cases.case46_rup_024 hm

end VCDim6

end
