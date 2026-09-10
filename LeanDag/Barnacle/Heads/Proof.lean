import LeanDag.Barnacle.Heads.Statement
import LeanDag.Barnacle.Helpers.Heads
/-!
# BN9 — proof

Generated proof layer; not part of the audit surface. Each clause is
one helper of `Helpers/Heads.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Heads

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ R slack C c₀
    refine ⟨?_, ?_, ?_⟩
    · intro hD S U V b top hspan hdec htop
      exact stretchDescent hD S V hspan hdec htop
    · intro hD hw U V Rnd N T hT C' ρ hRnd hN hheads
      exact headsDecide_at C' hD hw V hT ρ hRnd hN hheads
    · intro hD hw hheads
      exact liveOn_of_headsRun C hD hw hheads
  · intro n hn T slack g hT hbound
    exact roundRobin_headsRun n hn T slack g hT hbound
  · intro n hn BlockId Payload _ R slack hD hw hbound C hC
    exact liveOn_roundRobin hn R hD hw hbound C hC

end Heads

end Barnacle

end LeanDag
