import LeanDag.Hydrozoan.Properties.Statement
import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Hydrozoan.Helpers.Skippability
import LeanDag.Properties.Derived.FromBand
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Properties.Arcs.Headline
/-!
# Hydrozoan conforms to the target properties — proof

The band (`Helpers/Banded.lean`) rests on one idea: `Extends.reaches_old`
puts nothing new in an old anchor's causal history, so every premise a
derivation carries is either monotone or read from history unchanged by
the extension. The direct skip survives for the same reason: a blame
references no candidate, old references stay old, so the count does not
move — unlike a rule that quantifies over candidates directly.
-/

namespace LeanDag

namespace Hydrozoan

namespace Properties

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}


/-! ## The assembly -/

theorem holds : Statement := by
  intro Replica _ _ BlockId _ _ _
  refine ⟨banded, agree, commitsCandidate, ?_⟩
  · exact skipsUnsupported

/-! ## The headlines

No self-parent clause, so progress rather than inclusion. -/

theorem safety : LeanDag.Properties.Safe (rule (Replica := Replica) (BlockId := BlockId)) :=
  LeanDag.Properties.safety banded agree commitsCandidate

theorem progress : LeanDag.Properties.Support.Progresses
    (hzSupport (Replica := Replica) (BlockId := BlockId)) (hzReliability Replica) :=
  LeanDag.Properties.Support.progress hzSupport_commits

end Properties

end Hydrozoan

end LeanDag
