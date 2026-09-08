import LeanDag.FinWhale.Anchor
import LeanDag.FinWhale.Model.Decided
import LeanDag.Common.Anchored.Bounded
/-!
# FinWhale — the least candidate at a rung

The relation's choice, and nothing about a verdict assignment: at
FinWhale's one rung the link is decidable and the identifier order
well-founded, so a nonempty rung has a least candidate. `Carrier.lean`
reads it for totality and the descent.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Slots Validator}
variable [LinearOrder BlockId]

/-- **The rung has a choice.** -/
theorem exists_least {A : BlockId} {i k : ℕ}
    (_ : i < (finWhaleAnchored Validator BlockId Payload).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) D k L ∧
      (finWhaleAnchored Validator BlockId Payload).Link i D A L S k) :
    ∃ L, IsLeaderBlock (S := S) D k L ∧ (finWhaleAnchored Validator BlockId Payload).Link i D A L S k ∧
      (finWhaleAnchored Validator BlockId Payload).Least (S := S) D A i k L :=
  AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h


end FinWhale

end LeanDag
