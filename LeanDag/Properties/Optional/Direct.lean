import LeanDag.Properties.Candidate
/-!
# What a rule owes about its own direct rule

`docs/target-properties.md` §11.4b. Optional, like the rest of
`Properties/Optional/`: a rule with no direct-commit predicate owes
nothing here. `Barnacle`'s leader count adapts on a window count of
directly committed slots, filtered on the rule's own direct predicate,
so this property is what ties that predicate to the decision relation
— without it, a direct predicate holding of everything would inflate
the count with every theorem about it still true.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A direct commit is a verdict.** The converse of
`CommitsCandidate`, parameterised by the rule's own direct-commit
predicate — what counts as *direct* is the rule's business and not the
carrier's, which is why `Direct` is an argument rather than a field. -/
def CommitsDirect (R : DagRule Validator BlockId Payload)
    (Direct : ∀ {U : R.Universe}, R.View U → BlockId → ℕ → Prop) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (k : ℕ) (L : BlockId),
    R.IsCandidate S U k L → Direct V L (S.slotRound k) → R.Decided S V k (some L)

end Properties

end LeanDag
