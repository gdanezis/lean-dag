import LeanDag.Barnacle.Model.Anchored
import LeanDag.Mysticeti.Rule
/-!
# Barnacle over Mysticeti — statement

The three-round rule (report §3) as a Barnacle base rule: `ofAnchored`
at `coreAnchored`, so the universe is the block universe, the views its
views, the wave length three and the direct predicate `DirectCommitIn`.
The claim is that it satisfies the interface's laws.

Consumed by the witnesses in Phase 1 and by nothing in the generic
development, which is stated over an arbitrary `BaseRule` with `Laws`;
in Phase 5 it is one of the rules the arc's theorems are instantiated
at. Statements only; the proof lives in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Mysticeti as a base rule**: the core's anchored rule. -/
def mysticeti [Faults Validator] : BaseRule Validator BlockId Payload :=
  ofAnchored (coreAnchored Validator BlockId Payload)

namespace Mysticeti

/-- **Mysticeti satisfies the interface**, over every committee and
every block universe: its views are causally complete, the history view
is the history, verdicts agree across views for a fixed schedule (M6),
and a directly committed candidate is a commit verdict. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId],
    BaseRule.Laws (mysticeti (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

end Mysticeti

end Barnacle

end LeanDag
