import LeanDag.Properties.Carrier
/-!
# Agreement above a round: the vocabulary locality is stated in

`docs/target-properties.md` §3.1. *If two DAGs agree above round `r`,
they decide alike at every slot whose round is at least `r`.* Stated as
agreement rather than existence, so a protocol proving it gets garbage
collection at every admissible horizon, not one; the indirect rule's
upward recursion is closed under this region (`Causal.refs_above`), and
no window formulation would serve since the chain is unbounded above.
Locality is about restriction alone — the renumbering half is
`Reindex.lean`.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Two views agree above a round.** Read at the source universe's
rounds, which `RebasedAbove` makes the target's shifted rounds wherever
the question arises.

A truncation asks exactly this of its views, so there is one definition
where there were two: `ViewTruncates` was the same proposition under
another name. -/
def ViewAgreeAbove (R : DagRule Validator BlockId Payload) {U U' : R.Universe}
    (V : R.View U) (V' : R.View U') (r : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (b ∈ R.viewIds V ↔ b ∈ R.viewIds V')


end Properties

end LeanDag
