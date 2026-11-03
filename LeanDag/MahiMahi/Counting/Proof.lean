import LeanDag.MahiMahi.Counting.Statement
import LeanDag.MahiMahi.Helpers.Counting
/-!
# The counting lemma — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Counting.lean`.
-/

namespace LeanDag

namespace MahiMahi

namespace Counting

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c₀ hc₀ hc₀r
    exact exists_commonCore card_compl_correct_le card_add_f_lt_two_mul_quorum hc₀ hc₀r
  · intro T r hw _ hcard hpop2 hpopd
    exact goodNonempty hw hcard hpop2 hpopd
  · intro T r hw _ hcard hpop3 hpopd
    exact goodCard hw hcard hpop3 hpopd
  · intro T r hw _ hcard hpop3 hpopd M hM hMcard
    exact multiLeader hw hcard hpop3 hpopd hM hMcard

end Counting

end MahiMahi

end LeanDag
