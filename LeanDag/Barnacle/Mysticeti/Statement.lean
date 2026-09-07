import LeanDag.Barnacle.Model.Anchored
import LeanDag.Mysticeti.Rule
/-!
# Barnacle over Mysticeti — statement

The three-round rule (report §3) as a Barnacle base rule, `ofAnchored`
at `coreAnchored`, and the claim that it satisfies the laws. Statements
only; the proof lives in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Mysticeti as a base rule**: the core's anchored rule. -/
def mysticeti [Faults Validator] : BaseRule Validator BlockId Payload :=
  ofAnchored (coreAnchored Validator BlockId Payload)

namespace Mysticeti

/-- **Mysticeti satisfies the laws**, over every committee and every block
universe; agreement is M6. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId],
    BaseRule.Laws (mysticeti (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

end Mysticeti

end Barnacle

end LeanDag
