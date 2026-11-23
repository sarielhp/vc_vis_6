import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case50
import RootTask.VCDim6.Cases.Shards.Case50_C000
import RootTask.VCDim6.Cases.Shards.Case50_C001
import RootTask.VCDim6.Cases.Shards.Case50_C002
import RootTask.VCDim6.Cases.Shards.Case50_C003
import RootTask.VCDim6.Cases.Shards.Case50_R000
import RootTask.VCDim6.Cases.Shards.Case50_R001
import RootTask.VCDim6.Cases.Shards.Case50_R002
import RootTask.VCDim6.Cases.Shards.Case50_R003
import RootTask.VCDim6.Cases.Shards.Case50_R004
import RootTask.VCDim6.Cases.Shards.Case50_R005
import RootTask.VCDim6.Cases.Shards.Case50_R006

noncomputable section

namespace VCDim6

theorem case50_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case50_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case50_vars_ok
  have hm := masterRangeSound_xH val Cases.case50_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case50_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case50_core_001 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case50_core_002 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case50_core_003 hm
  have hm := verifiedMidRup_sound Cases.case50_rup_000 hm
  have hm := verifiedMidRup_sound Cases.case50_rup_001 hm
  have hm := verifiedMidRup_sound Cases.case50_rup_002 hm
  have hm := verifiedMidRup_sound Cases.case50_rup_003 hm
  have hm := verifiedMidRup_sound Cases.case50_rup_004 hm
  have hm := verifiedMidRup_sound Cases.case50_rup_005 hm
  exact verifiedFinRup_sound Cases.case50_rup_006 hm

end VCDim6

end
