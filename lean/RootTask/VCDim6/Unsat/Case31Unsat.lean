import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case31
import RootTask.VCDim6.Cases.Shards.Case31_C000
import RootTask.VCDim6.Cases.Shards.Case31_C001
import RootTask.VCDim6.Cases.Shards.Case31_C002
import RootTask.VCDim6.Cases.Shards.Case31_R000
import RootTask.VCDim6.Cases.Shards.Case31_R001
import RootTask.VCDim6.Cases.Shards.Case31_R002
import RootTask.VCDim6.Cases.Shards.Case31_R003
import RootTask.VCDim6.Cases.Shards.Case31_R004
import RootTask.VCDim6.Cases.Shards.Case31_R005

noncomputable section

namespace VCDim6

theorem case31_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case31_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case31_vars_ok
  have hm := masterRangeSound_xH val Cases.case31_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case31_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case31_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case31_core_002 hm
  have hm := verifiedMidRup_sound Cases.case31_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case31_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case31_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case31_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case31_rup_004 hm
  exact verifiedFinRup_sound Cases.case31_rup_005 hm

end VCDim6

end
