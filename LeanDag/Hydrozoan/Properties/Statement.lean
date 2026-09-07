import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.Truncation
import LeanDag.Hydrozoan.Helpers.Skippability
/-!
# Hydrozoan conforms to the target properties — statement

**HZ9.** Hydrozoan's universes are block DAGs; its verdicts survive a
growing DAG **unconditionally** and a truncation; and it skips a slot
whose candidates nobody in `T` supports — **at `qFast ≤ |T|`**.

Persistence is unconditional. Hydrozoan's direct skip counts slotBlames at
the slot, and a count of blocks that are still present does not move
under an extension. The core's skip once quantified over candidates and
needed a grade to survive; that was a defect in the rule, since repaired
(`docs/target-properties.md` §3.2), and `Persist` carries no grade any
more.

`CommitsCandidate` is the newest, and it is stated because Hydrozoan
proves it directly: a commit names a block the DAG holds, at the slot's
round, by the slot's leader. Chain quality is what consumes it.

**What is stated here is smaller than what Hydrozoan satisfies.**
`Persist`, `Local` and `LocalTruncate` are absent, and all three hold:
each is `Banded` applied, derived once in `Properties/Derived/` for
every rule with a band. A conformance statement lists what a protocol
*owes*, so naming a consequence here would invent an obligation. A
mechanism that wants one of the three reaches it from `Banded`, which is
listed.

**The last grade is the finding.** A quorum of correct replicas has
`q = n − f − c` members and Hydrozoan's skip needs `qFast = n − p`, so a
correct quorum skips an unsupported slot exactly when `f + c ≤ p` — the
condition `docs/hydrozoan-integration.md` §2 records, the grade of a property. Optimal-Hydrozoan's skip is at
`qCert ≤ q` and needs no such condition.

What conformance is worth: any mechanism stated against these
properties applies to Hydrozoan without further proof. Crash recovery
is the first (`Properties/Arcs/SafeSkip.lean`) and garbage collection
the second (`Properties/Arcs/GC.lean`); the mechanisms that follow cost
this arc nothing more.

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
