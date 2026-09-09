import LeanDag.Steelhead.Coin.Statement
import LeanDag.Steelhead.Helpers.Coin
/-!
# The coin — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Coin.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U wa
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T r hwa hcard hpop₃ hpopd
    exact ⟨ratio_le_commitProb hwa hcard hpop₃ hpopd, third_le_commitProb hwa hcard hpop₃ hpopd⟩
  · intro coin V r h hV
    exact chainCommit_of_mem_goodAt h hV
  · intro T r₀ m hwa hcard hpop
    exact noCommitProb_le hwa hcard hpop
  · exact tail_tendsto_zero

end Coin

end Steelhead

end LeanDag
