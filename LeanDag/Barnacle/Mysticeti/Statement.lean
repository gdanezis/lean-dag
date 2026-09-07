import LeanDag.Barnacle.Model.Rule
import LeanDag.Barnacle.Helpers.Mysticeti
import LeanDag.Mysticeti.Properties
/-!
# Barnacle over Mysticeti — statement

The three-round rule (report §3) as a `BaseRule`, and the claim that it
satisfies the interface's laws: `BlockUniverse` and `View`, the
view-relative direct commit `DirectCommitIn`, the decision relation
`Decided`; the laws are M6 (`decided_agree`) and the view structure.

The one import beyond `Model/` is `Helpers/Mysticeti.lean`, for
`historyViewOf`, the anchor's history as a `View` — a construction the
core's `View` type cannot express without a closure proof. It is not
trusted: the law `historyView_ids` of `Statement` pins its ids to the
history, whatever the helper builds.

Consumed by the witnesses in Phase 1 and by nothing in the generic
development, which is stated over an arbitrary `BaseRule` with `Laws`;
in Phase 5 it is one of the three rules the arc's theorems are
instantiated at. Statements only; the proof lives in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Mysticeti as a base rule** — the data. Wave length three; the
direct commit predicate counts certificates. -/
def mysticeti [Faults Validator] : BaseRule Validator BlockId Payload where
  toDagRule := MysticetiProperties.mysticetiRule
  full := fun U => LeanDag.View.full U
  historyView := fun U A hA => historyViewOf U A hA
  waveLength := 3
  DirectCommitIn := fun V L r => LeanDag.DirectCommitIn _ V L r
  decDirect := fun _ _ _ => inferInstance

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
