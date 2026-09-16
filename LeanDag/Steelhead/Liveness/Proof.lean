import LeanDag.Steelhead.Liveness.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Liveness at a wavelength function — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Liveness.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Liveness

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U w ws wa k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T V R N k hw hT hcard hs hpop hR hN hV hlead
    exact commitsOfSynchrony hw hT hcard hs hpop hR hN hV hlead
  · intro T c hw hT hcard hspan fair R k
    exact allDecidedBelowOfSynchrony hw hT hcard hspan fair R k
  · intro T V k hcard hcrash hpop hV
    exact skipsCrashed hcard hcrash hpop hV
  · intro T V k L q hw hcard hL huniq hq hqr hqT hqL hs hpop hV
    exact commitsOfDissemination hw hcard hL huniq hq hqr hqT hqL hs hpop hV
  · intro T V R N k a hw hid hT hcard hs hpop hR hka hlead hdec hN hV
    exact decidedOfReliableAboveFloor hw hid hT hcard hs hpop hR hka hlead hdec hN hV
  · intro T V R N h x hw hid hT hcard hs hpop hR hhop hlead hN hV
    exact floorChainDecides hw hid hT hcard hs hpop hV h x hR hhop hlead hN
  · intro n hn T
    exact ⟨fun _ hlt => roundRobin_fairRun hn hlt, fun hT r => roundRobin_near hn hT r⟩
  · intro coin V c N hwa hrun hV r hr
    exact chainAllDecidedBelow hwa hrun hV r hr
  · intro coin T hwa hT hcard fair R k
    exact chainAllDecidedBelowOfSynchrony hwa coin hT hcard fair R k
  · intro coin V b hwa hgood hV
    exact chainAllDecidedBelowOfRun hwa hgood hV
  · intro V ws wa k hws hk hid hcert hskip i hi v h
    exact stall hws hk hid hcert hskip hi h
  · intro V b hw hle hid hrun
    exact allDecidedBelowOfRun hw hle hid hrun
  · intro V c N hwa hid hrun hV r hr
    exact allDecidedBelowAtPeriodOne hwa hid hrun hV r hr
  · intro hid hws hwa r hr
    exact asyncSlotCost hid hws hwa hr

end Liveness

end Steelhead

end LeanDag
