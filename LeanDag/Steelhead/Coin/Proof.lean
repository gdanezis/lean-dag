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
  intro Validator BlockId Payload _ _ _ _ U ws wa I K
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T r hwa hcard hpop₃ hpopd
    exact ⟨ratio_le_commitProb hwa hcard hpop₃ hpopd, third_le_commitProb hwa hcard hpop₃ hpopd⟩
  · intro T r hwa hcard hpop₂ hpopd
    exact inv_card_le_commitProb hwa hcard hpop₂ hpopd
  · intro coin V r h hV
    exact chainCommit_of_mem_goodAt h hV
  · intro T r₀ m hwa hcard hpop
    exact noCommitProb_le hwa hcard hpop
  · exact tail_tendsto_zero
  · intro T upd k₀ known d s M hws hle hwa hwaK hKI hcard h₀ hK hupd hpop
    exact undecidedProb_le hws hle hwa hwaK hKI hcard h₀ hK hupd hpop
  · exact undecided_tail_tendsto_zero
  · intro _ _ U T upd k₀ known s hws hle hwa hwaK hKI hcard h₀ hK hupd hpop
    exact decidedAlmostSurely hws hle hwa hwaK hKI hcard h₀ hK hupd hpop

end Coin

end Steelhead

end LeanDag
