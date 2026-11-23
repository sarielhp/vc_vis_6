import RootTask.VCDim6.Cases.Case31

set_option maxRecDepth 2000000

namespace VCDim6.Cases

open VCDim6.FastTrieRUP

noncomputable section

noncomputable def case31_cjust_002 : ChunkTree :=
  mk_chunk_tree "a0706050c0001060a0a0706050c01010905060506040c01010705060506040c,10109090806050c0101030c"

theorem case31_core_002 :
    checkCoreShard case31_spec case31_vars case31_master (mk_pidx 3001) (mk_pidx 3006) 5 case31_cjust_002 = true := by
  kernel_rfl_true

end

end VCDim6.Cases
