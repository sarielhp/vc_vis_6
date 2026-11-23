import RootTask.VCDim6.ChunkedCertSoundness
import RootTask.VCDim6.Cases.Case02
import RootTask.VCDim6.Cases.Shards.Case02_S000
import RootTask.VCDim6.Cases.Shards.Case02_S001
import RootTask.VCDim6.Cases.Shards.Case02_S002
import RootTask.VCDim6.Cases.Shards.Case02_S003

noncomputable section

namespace VCDim6

theorem case02_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case02_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case02_vars_ok
  have h := evalRawTree_empty_stream val
  have h := checkMidChunk_sound hV hM htt hval Cases.case02_chunk_000 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case02_chunk_001 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case02_chunk_002 h
  exact checkFinalChunk_sound hV hM htt hval Cases.case02_chunk_003 h

end VCDim6

end
