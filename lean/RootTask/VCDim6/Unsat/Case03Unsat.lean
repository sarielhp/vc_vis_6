import RootTask.VCDim6.ChunkedCertSoundness
import RootTask.VCDim6.Cases.Case03

noncomputable section

namespace VCDim6

theorem case03_unsat {P : Set (ℝ × ℝ)} {S : Fin 7 → ℝ × ℝ} {w : Finset (Fin 7) → ℝ × ℝ}
    (hV : ValidCanonicalInstance P S w Cases.case03_spec) : False := by
  obtain ⟨hM, _, val, htt, hval⟩ := init_chunked_val (P := P) (S := S) (w := w) (by decide) Cases.case03_vars_ok
  have h := evalRawTree_empty_stream val
  have h := checkMidChunk_sound hV hM htt hval Cases.case03_chunk_000 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case03_chunk_001 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case03_chunk_002 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case03_chunk_003 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case03_chunk_004 h
  have h := checkMidChunk_sound hV hM htt hval Cases.case03_chunk_005 h
  exact checkFinalChunk_sound hV hM htt hval Cases.case03_chunk_006 h

end VCDim6

end
