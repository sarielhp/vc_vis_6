import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case19
import RootTask.VCDim6.Cases.Shards.Case19_C000
import RootTask.VCDim6.Cases.Shards.Case19_C001
import RootTask.VCDim6.Cases.Shards.Case19_C002
import RootTask.VCDim6.Cases.Shards.Case19_C003
import RootTask.VCDim6.Cases.Shards.Case19_C004
import RootTask.VCDim6.Cases.Shards.Case19_C005
import RootTask.VCDim6.Cases.Shards.Case19_C006
import RootTask.VCDim6.Cases.Shards.Case19_C007
import RootTask.VCDim6.Cases.Shards.Case19_C008
import RootTask.VCDim6.Cases.Shards.Case19_C009
import RootTask.VCDim6.Cases.Shards.Case19_C010
import RootTask.VCDim6.Cases.Shards.Case19_R000
import RootTask.VCDim6.Cases.Shards.Case19_R001
import RootTask.VCDim6.Cases.Shards.Case19_R002
import RootTask.VCDim6.Cases.Shards.Case19_R003
import RootTask.VCDim6.Cases.Shards.Case19_R004
import RootTask.VCDim6.Cases.Shards.Case19_R005
import RootTask.VCDim6.Cases.Shards.Case19_R006
import RootTask.VCDim6.Cases.Shards.Case19_R007
import RootTask.VCDim6.Cases.Shards.Case19_R008
import RootTask.VCDim6.Cases.Shards.Case19_R009
import RootTask.VCDim6.Cases.Shards.Case19_R010
import RootTask.VCDim6.Cases.Shards.Case19_R011
import RootTask.VCDim6.Cases.Shards.Case19_R012
import RootTask.VCDim6.Cases.Shards.Case19_R013
import RootTask.VCDim6.Cases.Shards.Case19_R014
import RootTask.VCDim6.Cases.Shards.Case19_R015
import RootTask.VCDim6.Cases.Shards.Case19_R016
import RootTask.VCDim6.Cases.Shards.Case19_R017
import RootTask.VCDim6.Cases.Shards.Case19_R018
import RootTask.VCDim6.Cases.Shards.Case19_R019
import RootTask.VCDim6.Cases.Shards.Case19_R020
import RootTask.VCDim6.Cases.Shards.Case19_R021
import RootTask.VCDim6.Cases.Shards.Case19_R022
import RootTask.VCDim6.Cases.Shards.Case19_R023

noncomputable section

namespace VCDim6

theorem case19_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case19_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case19_vars_ok
  have hm := masterRangeSound_xH val Cases.case19_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_007 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_008 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_009 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case19_core_010 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case19_rup_022 hm
  exact verifiedFinRup_sound Cases.case19_rup_023 hm

end VCDim6

end
