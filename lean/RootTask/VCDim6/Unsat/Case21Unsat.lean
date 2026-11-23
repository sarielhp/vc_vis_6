import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case21
import RootTask.VCDim6.Cases.Shards.Case21_C000
import RootTask.VCDim6.Cases.Shards.Case21_C001
import RootTask.VCDim6.Cases.Shards.Case21_C002
import RootTask.VCDim6.Cases.Shards.Case21_C003
import RootTask.VCDim6.Cases.Shards.Case21_R000
import RootTask.VCDim6.Cases.Shards.Case21_R001
import RootTask.VCDim6.Cases.Shards.Case21_R002
import RootTask.VCDim6.Cases.Shards.Case21_R003
import RootTask.VCDim6.Cases.Shards.Case21_R004
import RootTask.VCDim6.Cases.Shards.Case21_R005

noncomputable section

namespace VCDim6

theorem case21_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case21_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case21_vars_ok
  have hm := masterRangeSound_xH val Cases.case21_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case21_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case21_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case21_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case21_core_003 hm
  have hm := verifiedMidRup_sound Cases.case21_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case21_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case21_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case21_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case21_rup_004 hm
  exact verifiedFinRup_sound Cases.case21_rup_005 hm

end VCDim6

end
