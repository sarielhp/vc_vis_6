import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case09
import RootTask.VCDim6.Cases.Shards.Case09_C000
import RootTask.VCDim6.Cases.Shards.Case09_C001
import RootTask.VCDim6.Cases.Shards.Case09_C002
import RootTask.VCDim6.Cases.Shards.Case09_C003
import RootTask.VCDim6.Cases.Shards.Case09_C004
import RootTask.VCDim6.Cases.Shards.Case09_C005
import RootTask.VCDim6.Cases.Shards.Case09_C006
import RootTask.VCDim6.Cases.Shards.Case09_C007
import RootTask.VCDim6.Cases.Shards.Case09_C008
import RootTask.VCDim6.Cases.Shards.Case09_C009
import RootTask.VCDim6.Cases.Shards.Case09_C010
import RootTask.VCDim6.Cases.Shards.Case09_C011
import RootTask.VCDim6.Cases.Shards.Case09_C012
import RootTask.VCDim6.Cases.Shards.Case09_C013
import RootTask.VCDim6.Cases.Shards.Case09_C014
import RootTask.VCDim6.Cases.Shards.Case09_C015
import RootTask.VCDim6.Cases.Shards.Case09_C016
import RootTask.VCDim6.Cases.Shards.Case09_C017
import RootTask.VCDim6.Cases.Shards.Case09_C018
import RootTask.VCDim6.Cases.Shards.Case09_C019
import RootTask.VCDim6.Cases.Shards.Case09_C020
import RootTask.VCDim6.Cases.Shards.Case09_C021
import RootTask.VCDim6.Cases.Shards.Case09_C022
import RootTask.VCDim6.Cases.Shards.Case09_C023
import RootTask.VCDim6.Cases.Shards.Case09_R000
import RootTask.VCDim6.Cases.Shards.Case09_R001
import RootTask.VCDim6.Cases.Shards.Case09_R002
import RootTask.VCDim6.Cases.Shards.Case09_R003
import RootTask.VCDim6.Cases.Shards.Case09_R004
import RootTask.VCDim6.Cases.Shards.Case09_R005
import RootTask.VCDim6.Cases.Shards.Case09_R006
import RootTask.VCDim6.Cases.Shards.Case09_R007
import RootTask.VCDim6.Cases.Shards.Case09_R008
import RootTask.VCDim6.Cases.Shards.Case09_R009
import RootTask.VCDim6.Cases.Shards.Case09_R010
import RootTask.VCDim6.Cases.Shards.Case09_R011
import RootTask.VCDim6.Cases.Shards.Case09_R012
import RootTask.VCDim6.Cases.Shards.Case09_R013
import RootTask.VCDim6.Cases.Shards.Case09_R014
import RootTask.VCDim6.Cases.Shards.Case09_R015
import RootTask.VCDim6.Cases.Shards.Case09_R016
import RootTask.VCDim6.Cases.Shards.Case09_R017
import RootTask.VCDim6.Cases.Shards.Case09_R018
import RootTask.VCDim6.Cases.Shards.Case09_R019
import RootTask.VCDim6.Cases.Shards.Case09_R020
import RootTask.VCDim6.Cases.Shards.Case09_R021
import RootTask.VCDim6.Cases.Shards.Case09_R022
import RootTask.VCDim6.Cases.Shards.Case09_R023
import RootTask.VCDim6.Cases.Shards.Case09_R024
import RootTask.VCDim6.Cases.Shards.Case09_R025
import RootTask.VCDim6.Cases.Shards.Case09_R026
import RootTask.VCDim6.Cases.Shards.Case09_R027
import RootTask.VCDim6.Cases.Shards.Case09_R028
import RootTask.VCDim6.Cases.Shards.Case09_R029
import RootTask.VCDim6.Cases.Shards.Case09_R030
import RootTask.VCDim6.Cases.Shards.Case09_R031
import RootTask.VCDim6.Cases.Shards.Case09_R032
import RootTask.VCDim6.Cases.Shards.Case09_R033
import RootTask.VCDim6.Cases.Shards.Case09_R034
import RootTask.VCDim6.Cases.Shards.Case09_R035
import RootTask.VCDim6.Cases.Shards.Case09_R036
import RootTask.VCDim6.Cases.Shards.Case09_R037
import RootTask.VCDim6.Cases.Shards.Case09_R038
import RootTask.VCDim6.Cases.Shards.Case09_R039
import RootTask.VCDim6.Cases.Shards.Case09_R040
import RootTask.VCDim6.Cases.Shards.Case09_R041
import RootTask.VCDim6.Cases.Shards.Case09_R042
import RootTask.VCDim6.Cases.Shards.Case09_R043
import RootTask.VCDim6.Cases.Shards.Case09_R044
import RootTask.VCDim6.Cases.Shards.Case09_R045
import RootTask.VCDim6.Cases.Shards.Case09_R046
import RootTask.VCDim6.Cases.Shards.Case09_R047
import RootTask.VCDim6.Cases.Shards.Case09_R048
import RootTask.VCDim6.Cases.Shards.Case09_R049
import RootTask.VCDim6.Cases.Shards.Case09_R050
import RootTask.VCDim6.Cases.Shards.Case09_R051
import RootTask.VCDim6.Cases.Shards.Case09_R052
import RootTask.VCDim6.Cases.Shards.Case09_R053
import RootTask.VCDim6.Cases.Shards.Case09_R054
import RootTask.VCDim6.Cases.Shards.Case09_R055
import RootTask.VCDim6.Cases.Shards.Case09_R056
import RootTask.VCDim6.Cases.Shards.Case09_R057
import RootTask.VCDim6.Cases.Shards.Case09_R058
import RootTask.VCDim6.Cases.Shards.Case09_R059
import RootTask.VCDim6.Cases.Shards.Case09_R060

noncomputable section

namespace VCDim6

theorem case09_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case09_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case09_vars_ok
  have hm := masterRangeSound_xH val Cases.case09_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_007 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_008 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_009 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_010 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_011 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_012 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_013 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_014 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_015 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_016 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_017 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_018 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_019 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_020 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_021 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_022 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case09_core_023 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_022 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_023 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_024 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_025 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_026 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_027 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_028 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_029 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_030 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_031 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_032 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_033 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_034 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_035 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_036 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_037 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_038 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_039 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_040 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_041 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_042 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_043 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_044 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_045 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_046 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_047 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_048 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_049 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_050 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_051 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_052 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_053 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_054 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_055 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_056 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_057 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_058 hm
  have hm := verifiedMidRup_sound Cases.case09_rup_059 hm
  exact verifiedFinRup_sound Cases.case09_rup_060 hm

end VCDim6

end
