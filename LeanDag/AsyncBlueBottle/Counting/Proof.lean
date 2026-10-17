import LeanDag.AsyncBlueBottle.Counting.Statement
import LeanDag.AsyncBlueBottle.Helpers.Counting
/-!
# The counting lemma — proof

Generated proof layer; not part of the audit surface. The common core is
Mahi-Mahi's (the core's T3c carried upward); the rest is
`Helpers/Counting.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Counting

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c₀ hc₀ hc₀r
    exact exists_commonCore card_compl_correct_le card_add_f_lt_two_mul_quorum hc₀ hc₀r
  · intro T r hcard hpop
    exact goodNonempty hcard hpop
  · intro T r hT hcard hpop1 hpop2
    exact goodCard hT hcard hpop1 hpop2
  · intro T r hT hcard hpop1 hpop2 M hM hMcard
    exact multiLeader hT hcard hpop1 hpop2 hM hMcard

end Counting

end AsyncBlueBottle

end LeanDag
