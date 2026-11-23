import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case20
import RootTask.VCDim6.Cases.Shards.Case20_C000
import RootTask.VCDim6.Cases.Shards.Case20_C001
import RootTask.VCDim6.Cases.Shards.Case20_C002
import RootTask.VCDim6.Cases.Shards.Case20_C003
import RootTask.VCDim6.Cases.Shards.Case20_C004
import RootTask.VCDim6.Cases.Shards.Case20_C005
import RootTask.VCDim6.Cases.Shards.Case20_C006
import RootTask.VCDim6.Cases.Shards.Case20_C007
import RootTask.VCDim6.Cases.Shards.Case20_C008
import RootTask.VCDim6.Cases.Shards.Case20_C009
import RootTask.VCDim6.Cases.Shards.Case20_C010
import RootTask.VCDim6.Cases.Shards.Case20_C011
import RootTask.VCDim6.Cases.Shards.Case20_R000
import RootTask.VCDim6.Cases.Shards.Case20_R001
import RootTask.VCDim6.Cases.Shards.Case20_R002
import RootTask.VCDim6.Cases.Shards.Case20_R003
import RootTask.VCDim6.Cases.Shards.Case20_R004
import RootTask.VCDim6.Cases.Shards.Case20_R005
import RootTask.VCDim6.Cases.Shards.Case20_R006
import RootTask.VCDim6.Cases.Shards.Case20_R007
import RootTask.VCDim6.Cases.Shards.Case20_R008
import RootTask.VCDim6.Cases.Shards.Case20_R009
import RootTask.VCDim6.Cases.Shards.Case20_R010
import RootTask.VCDim6.Cases.Shards.Case20_R011
import RootTask.VCDim6.Cases.Shards.Case20_R012
import RootTask.VCDim6.Cases.Shards.Case20_R013
import RootTask.VCDim6.Cases.Shards.Case20_R014
import RootTask.VCDim6.Cases.Shards.Case20_R015
import RootTask.VCDim6.Cases.Shards.Case20_R016
import RootTask.VCDim6.Cases.Shards.Case20_R017
import RootTask.VCDim6.Cases.Shards.Case20_R018
import RootTask.VCDim6.Cases.Shards.Case20_R019
import RootTask.VCDim6.Cases.Shards.Case20_R020
import RootTask.VCDim6.Cases.Shards.Case20_R021
import RootTask.VCDim6.Cases.Shards.Case20_R022
import RootTask.VCDim6.Cases.Shards.Case20_R023
import RootTask.VCDim6.Cases.Shards.Case20_R024
import RootTask.VCDim6.Cases.Shards.Case20_R025
import RootTask.VCDim6.Cases.Shards.Case20_R026
import RootTask.VCDim6.Cases.Shards.Case20_R027
import RootTask.VCDim6.Cases.Shards.Case20_R028

noncomputable section

namespace VCDim6

theorem case20_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case20_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case20_vars_ok
  have hm := masterRangeSound_xH val Cases.case20_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_007 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_008 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_009 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_010 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case20_core_011 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_022 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_023 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_024 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_025 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_026 hm
  have hm := verifiedMidRup_sound Cases.case20_rup_027 hm
  exact verifiedFinRup_sound Cases.case20_rup_028 hm

end VCDim6

end
