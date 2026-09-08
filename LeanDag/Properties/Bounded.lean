import LeanDag.Properties.Agree
/-!
# Verdicts decided below a slot bound

`docs/target-properties.md` §4. What an adaptive leader schedule
consumes from a protocol on the safety side: since a schedule computes
high-slot leaders from low-slot verdicts, a verdict needs a **bound**
above which reassigning leaders cannot change it. `DecidedBelow` states
this as a definition over `Decided` alone, so a protocol proves nothing
to have it; its laws sit in `Derived/Bounded.lean` as theorems.
`LeaderCommits` and `Descends` (`Commit.lean`) produce a verdict at a
tight bound; `Witness.lean` derives the untight version from the band.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A verdict decided below `B`**: the slot sits below the bound, the
verdict holds, and it is unchanged by any reassignment of the leaders at
or above the bound. The round structure is held fixed, which is what
reassignment means. -/
def DecidedBelow (R : DagRule Validator BlockId Payload) (S : Slots Validator) (B : ℕ)
    {U : R.Universe} (V : R.View U) (k : ℕ) (v : Option BlockId) : Prop :=
  k < B ∧ R.Decided S V k v ∧
    ∀ S' : Slots Validator, S'.slotRound = S.slotRound →
      (∀ m, m < B → S'.leader m = S.leader m) → R.Decided S' V k v

end Properties

end LeanDag
