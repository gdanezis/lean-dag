import LeanDag.Properties.Extends
/-!
# Persistence

`docs/target-properties.md` §11.4b. *Verdicts survive extension of the
DAG.* Not a consequence of safety but its prerequisite as the DAG
grows, since every uniqueness theorem is stated for two views of the
*same* universe. Both instances obtain it from `Banded`
(`Derived/FromBand.lean`); it stays a named property because that is
what crash recovery consumes, and a bandless rule could still prove it
directly.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Persistence.** A verdict reached on `V` is reached again on any
larger view of any extension.

**This carried a grade `Ok` and no longer does.** The core once needed
one: its skip quantified over the candidates a universe holds, so a slot
with none was skipped for nothing and a later candidate broke the
derivation, and the grade named the quorum that would have blamed it.
That premise was the defect, not the grade — a skip resting on the
absence of a candidate is not final, which is the one thing a skip rule
exists to be — and it has been replaced by a count of blockers.

The parameter was then kept against a rule that decides on a block's
*absence* rather than on the contents of blocks present. Such a rule
fails `Banded` too, since the band admits extra blocks inside itself, so
the grade would not save a protocol that proves the band; and every
route to persistence here runs through the band. The parameter added an
argument to every consumer and no generality, so it is gone. -/
def Persist (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) (U U' : R.Universe), Extends R U U' →
    ∀ (V : R.View U) (V' : R.View U'), R.viewIds V ⊆ R.viewIds V' →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V k v → R.Decided S V' k v

end Properties

end LeanDag
