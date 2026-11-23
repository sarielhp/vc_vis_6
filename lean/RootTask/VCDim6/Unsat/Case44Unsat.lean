import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case44
import RootTask.VCDim6.Cases.Shards.Case44_C000
import RootTask.VCDim6.Cases.Shards.Case44_C001
import RootTask.VCDim6.Cases.Shards.Case44_C002
import RootTask.VCDim6.Cases.Shards.Case44_C003
import RootTask.VCDim6.Cases.Shards.Case44_C004
import RootTask.VCDim6.Cases.Shards.Case44_C005
import RootTask.VCDim6.Cases.Shards.Case44_C006
import RootTask.VCDim6.Cases.Shards.Case44_C007
import RootTask.VCDim6.Cases.Shards.Case44_C008
import RootTask.VCDim6.Cases.Shards.Case44_C009
import RootTask.VCDim6.Cases.Shards.Case44_C010
import RootTask.VCDim6.Cases.Shards.Case44_C011
import RootTask.VCDim6.Cases.Shards.Case44_C012
import RootTask.VCDim6.Cases.Shards.Case44_C013
import RootTask.VCDim6.Cases.Shards.Case44_C014
import RootTask.VCDim6.Cases.Shards.Case44_R000
import RootTask.VCDim6.Cases.Shards.Case44_R001
import RootTask.VCDim6.Cases.Shards.Case44_R002
import RootTask.VCDim6.Cases.Shards.Case44_R003
import RootTask.VCDim6.Cases.Shards.Case44_R004
import RootTask.VCDim6.Cases.Shards.Case44_R005
import RootTask.VCDim6.Cases.Shards.Case44_R006
import RootTask.VCDim6.Cases.Shards.Case44_R007
import RootTask.VCDim6.Cases.Shards.Case44_R008
import RootTask.VCDim6.Cases.Shards.Case44_R009
import RootTask.VCDim6.Cases.Shards.Case44_R010
import RootTask.VCDim6.Cases.Shards.Case44_R011
import RootTask.VCDim6.Cases.Shards.Case44_R012
import RootTask.VCDim6.Cases.Shards.Case44_R013
import RootTask.VCDim6.Cases.Shards.Case44_R014
import RootTask.VCDim6.Cases.Shards.Case44_R015
import RootTask.VCDim6.Cases.Shards.Case44_R016
import RootTask.VCDim6.Cases.Shards.Case44_R017
import RootTask.VCDim6.Cases.Shards.Case44_R018
import RootTask.VCDim6.Cases.Shards.Case44_R019
import RootTask.VCDim6.Cases.Shards.Case44_R020
import RootTask.VCDim6.Cases.Shards.Case44_R021
import RootTask.VCDim6.Cases.Shards.Case44_R022
import RootTask.VCDim6.Cases.Shards.Case44_R023
import RootTask.VCDim6.Cases.Shards.Case44_R024
import RootTask.VCDim6.Cases.Shards.Case44_R025
import RootTask.VCDim6.Cases.Shards.Case44_R026
import RootTask.VCDim6.Cases.Shards.Case44_R027
import RootTask.VCDim6.Cases.Shards.Case44_R028
import RootTask.VCDim6.Cases.Shards.Case44_R029
import RootTask.VCDim6.Cases.Shards.Case44_R030
import RootTask.VCDim6.Cases.Shards.Case44_R031
import RootTask.VCDim6.Cases.Shards.Case44_R032
import RootTask.VCDim6.Cases.Shards.Case44_R033
import RootTask.VCDim6.Cases.Shards.Case44_R034
import RootTask.VCDim6.Cases.Shards.Case44_R035
import RootTask.VCDim6.Cases.Shards.Case44_R036
import RootTask.VCDim6.Cases.Shards.Case44_R037
import RootTask.VCDim6.Cases.Shards.Case44_R038
import RootTask.VCDim6.Cases.Shards.Case44_R039
import RootTask.VCDim6.Cases.Shards.Case44_R040
import RootTask.VCDim6.Cases.Shards.Case44_R041

noncomputable section

namespace VCDim6

theorem case44_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case44_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case44_vars_ok
  have hm := masterRangeSound_xH val Cases.case44_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_007 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_008 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_009 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_010 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_011 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_012 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_013 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case44_core_014 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_022 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_023 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_024 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_025 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_026 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_027 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_028 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_029 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_030 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_031 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_032 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_033 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_034 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_035 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_036 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_037 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_038 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_039 hm
  have hm := verifiedMidRup_sound Cases.case44_rup_040 hm
  exact verifiedFinRup_sound Cases.case44_rup_041 hm

end VCDim6

end
