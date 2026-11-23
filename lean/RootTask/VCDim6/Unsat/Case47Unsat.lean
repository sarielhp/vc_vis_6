import RootTask.VCDim6.MasterTableSoundness
import RootTask.VCDim6.Cases.Case47
import RootTask.VCDim6.Cases.Shards.Case47_C000
import RootTask.VCDim6.Cases.Shards.Case47_C001
import RootTask.VCDim6.Cases.Shards.Case47_R000
import RootTask.VCDim6.Cases.Shards.Case47_R001

noncomputable section

namespace VCDim6

theorem case47_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case47_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case47_vars_ok
  have hm := masterRangeSound_xH val Cases.case47_master
  have hm := checkCoreShard_sound hV hM htt hval Cases.case47_core_000 hm
  have hm := checkCoreShard_sound hV hM htt hval Cases.case47_core_001 hm
  have hm := verifiedMidRup_sound Cases.case47_rup_000 hm
  exact verifiedFinRup_sound Cases.case47_rup_001 hm

end VCDim6

end
