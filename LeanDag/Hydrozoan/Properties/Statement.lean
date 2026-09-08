import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.Truncation
import LeanDag.Hydrozoan.Helpers.Skippability
/-!
# Hydrozoan conforms to the target properties — statement

**HZ9.** Hydrozoan's universes are block DAGs, its verdicts survive a
growing DAG and a truncation, and it skips an unsupported slot at
`qFast ≤ |T|` — the one graded property, since a correct quorum only
skips when `f + c ≤ p`; Optimal-Hydrozoan needs no such condition.
`Persist`, `Local` and `LocalTruncate` are absent but all hold, each
`Banded` applied, so a conformance statement need not name them.
Statement only; the proof lives in `Proof.lean`.
-/

namespace LeanDag

namespace Hydrozoan

namespace Properties

/-- **HZ9.** Hydrozoan is a lawful carrier; every verdict reads a band,
two views agree, and it skips an unsupported slot given `qFast`
blamers. Persistence and locality are the band applied, and truncation
invariance follows from the band's offsets without being stated
here. -/
def Statement : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    (BlockId : Type) [DecidableEq BlockId] [LinearOrder BlockId]
    [LeanDag.Hydrozoan.Faults Replica],
    LeanDag.Properties.Banded (rule (Replica := Replica) (BlockId := BlockId)) ∧
    LeanDag.Properties.Agree (rule (Replica := Replica) (BlockId := BlockId)) ∧
    LeanDag.Properties.CommitsCandidate (rule (Replica := Replica) (BlockId := BlockId)) ∧
    LeanDag.Properties.SkipsUnsupported (rule (Replica := Replica) (BlockId := BlockId))
      (fun T => LeanDag.Hydrozoan.qFast Replica ≤ T.card)

end Properties

end Hydrozoan

end LeanDag
