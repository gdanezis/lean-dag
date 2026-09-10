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
  intro Validator BlockId Payload _ _ _ _ S U w wa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T V R N k hw hT hcard hs hpop hR hN hV hlead
    exact commitsOfSynchrony hw hT hcard hs hpop hR hN hV hlead
  · intro T c hw hT hcard hspan fair R k
    exact allDecidedBelowOfSynchrony hw hT hcard hspan fair R k
  · intro coin V c N hwa hrun hV r hr
    exact chainAllDecidedBelow hwa hrun hV r hr
  · intro coin T hwa hT hcard fair R k
    exact chainAllDecidedBelowOfSynchrony hwa coin hT hcard fair R k
  · intro V ws wa k hws hk hid hcert hskip i hi v h
    exact stall hws hk hid hcert hskip hi h
  · intro V b hw hle hid hrun
    exact allDecidedBelowOfRun hw hle hid hrun

end Liveness

end Steelhead

end LeanDag
