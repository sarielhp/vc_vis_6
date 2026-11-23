import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case60
import RootTask.VCDim6.Cases.Shards.Case60_C000
import RootTask.VCDim6.Cases.Shards.Case60_C001
import RootTask.VCDim6.Cases.Shards.Case60_C002
import RootTask.VCDim6.Cases.Shards.Case60_C003
import RootTask.VCDim6.Cases.Shards.Case60_C004
import RootTask.VCDim6.Cases.Shards.Case60_C005
import RootTask.VCDim6.Cases.Shards.Case60_C006
import RootTask.VCDim6.Cases.Shards.Case60_C007
import RootTask.VCDim6.Cases.Shards.Case60_R000
import RootTask.VCDim6.Cases.Shards.Case60_R001
import RootTask.VCDim6.Cases.Shards.Case60_R002
import RootTask.VCDim6.Cases.Shards.Case60_R003
import RootTask.VCDim6.Cases.Shards.Case60_R004
import RootTask.VCDim6.Cases.Shards.Case60_R005
import RootTask.VCDim6.Cases.Shards.Case60_R006
import RootTask.VCDim6.Cases.Shards.Case60_R007
import RootTask.VCDim6.Cases.Shards.Case60_R008
import RootTask.VCDim6.Cases.Shards.Case60_R009
import RootTask.VCDim6.Cases.Shards.Case60_R010
import RootTask.VCDim6.Cases.Shards.Case60_R011
import RootTask.VCDim6.Cases.Shards.Case60_R012
import RootTask.VCDim6.Cases.Shards.Case60_R013
import RootTask.VCDim6.Cases.Shards.Case60_R014
import RootTask.VCDim6.Cases.Shards.Case60_R015
import RootTask.VCDim6.Cases.Shards.Case60_R016
import RootTask.VCDim6.Cases.Shards.Case60_R017
import RootTask.VCDim6.Cases.Shards.Case60_R018
import RootTask.VCDim6.Cases.Shards.Case60_R019
import RootTask.VCDim6.Cases.Shards.Case60_R020
import RootTask.VCDim6.Cases.Shards.Case60_R021
import RootTask.VCDim6.Cases.Shards.Case60_R022
import RootTask.VCDim6.Cases.Shards.Case60_R023
import RootTask.VCDim6.Cases.Shards.Case60_R024

noncomputable section

namespace VCDim6

theorem case60_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case60_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case60_vars_ok
  have hm := masterRangeSound_xH val Cases.case60_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case60_core_007 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_022 hm
  have hm := verifiedMidRup_sound Cases.case60_rup_023 hm
  exact verifiedFinRup_sound Cases.case60_rup_024 hm

end VCDim6

end
