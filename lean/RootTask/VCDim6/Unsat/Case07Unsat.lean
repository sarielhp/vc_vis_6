import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case07
import RootTask.VCDim6.Cases.Shards.Case07_C000
import RootTask.VCDim6.Cases.Shards.Case07_C001
import RootTask.VCDim6.Cases.Shards.Case07_C002
import RootTask.VCDim6.Cases.Shards.Case07_C003
import RootTask.VCDim6.Cases.Shards.Case07_C004
import RootTask.VCDim6.Cases.Shards.Case07_C005
import RootTask.VCDim6.Cases.Shards.Case07_C006
import RootTask.VCDim6.Cases.Shards.Case07_C007
import RootTask.VCDim6.Cases.Shards.Case07_C008
import RootTask.VCDim6.Cases.Shards.Case07_C009
import RootTask.VCDim6.Cases.Shards.Case07_C010
import RootTask.VCDim6.Cases.Shards.Case07_C011
import RootTask.VCDim6.Cases.Shards.Case07_C012
import RootTask.VCDim6.Cases.Shards.Case07_R000
import RootTask.VCDim6.Cases.Shards.Case07_R001
import RootTask.VCDim6.Cases.Shards.Case07_R002
import RootTask.VCDim6.Cases.Shards.Case07_R003
import RootTask.VCDim6.Cases.Shards.Case07_R004
import RootTask.VCDim6.Cases.Shards.Case07_R005
import RootTask.VCDim6.Cases.Shards.Case07_R006
import RootTask.VCDim6.Cases.Shards.Case07_R007
import RootTask.VCDim6.Cases.Shards.Case07_R008
import RootTask.VCDim6.Cases.Shards.Case07_R009
import RootTask.VCDim6.Cases.Shards.Case07_R010
import RootTask.VCDim6.Cases.Shards.Case07_R011
import RootTask.VCDim6.Cases.Shards.Case07_R012
import RootTask.VCDim6.Cases.Shards.Case07_R013
import RootTask.VCDim6.Cases.Shards.Case07_R014
import RootTask.VCDim6.Cases.Shards.Case07_R015
import RootTask.VCDim6.Cases.Shards.Case07_R016
import RootTask.VCDim6.Cases.Shards.Case07_R017
import RootTask.VCDim6.Cases.Shards.Case07_R018
import RootTask.VCDim6.Cases.Shards.Case07_R019
import RootTask.VCDim6.Cases.Shards.Case07_R020
import RootTask.VCDim6.Cases.Shards.Case07_R021
import RootTask.VCDim6.Cases.Shards.Case07_R022
import RootTask.VCDim6.Cases.Shards.Case07_R023
import RootTask.VCDim6.Cases.Shards.Case07_R024
import RootTask.VCDim6.Cases.Shards.Case07_R025
import RootTask.VCDim6.Cases.Shards.Case07_R026
import RootTask.VCDim6.Cases.Shards.Case07_R027

noncomputable section

namespace VCDim6

theorem case07_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case07_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case07_vars_ok
  have hm := masterRangeSound_xH val Cases.case07_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_003 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_004 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_005 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_006 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_007 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_008 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_009 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_010 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_011 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case07_core_012 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_005 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_006 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_007 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_008 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_009 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_010 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_011 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_012 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_013 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_014 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_015 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_016 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_017 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_018 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_019 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_020 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_021 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_022 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_023 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_024 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_025 hm
  have hm := verifiedMidRup_sound Cases.case07_rup_026 hm
  exact verifiedFinRup_sound Cases.case07_rup_027 hm

end VCDim6

end
