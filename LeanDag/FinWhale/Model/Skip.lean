import LeanDag.FinWhale.Model.Rule
/-!
# FinWhale — the direct skip rule

The rule marks a slot **to-skip** when both halves hold: an SP-skip
pattern at round `r + 1`, meaning every block of the slot has a quorum of
round-`(r+1)` validators declining to vote for it; and a quorum of
**Non-FP-evidence** blocks at round `r + 2`, a block being
Non-FP-evidence when it is FP-evidence for no block of the slot.

This file states the two halves. `Model/Decision.lean` combines them into
`DirectSkip`, and `Skip.lean` proves that a commit rules them out.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- The validators whose round-`(r+1)` block declines to vote for `l`:
the record's `blames` at the round above `l`. -/
abbrev nonVoters (D : Dag Validator BlockId Payload) (l : BlockId) : Finset Validator :=
  blames D l ((D.block l).round + 1)

/-- **Non-FP-evidence**: a round-`(r+2)` block that is FP-evidence for no
block of the slot. -/
def NonFPEvidence (D : Dag Validator BlockId Payload) (b : BlockId) (slot : Finset BlockId) :
    Prop :=
  ∀ l ∈ slot, ¬ FPEvidence D b l

instance (D : Dag Validator BlockId Payload) (b : BlockId) (slot : Finset BlockId) :
    Decidable (NonFPEvidence D b slot) :=
  inferInstanceAs (Decidable (∀ l ∈ slot, ¬ FPEvidence D b l))

/-- **The SP-skip half of the direct skip rule**, at one block of the
slot: a quorum of round-`(r+1)` validators decline to vote for it. -/
def SPSkip (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  spQuorum Validator ≤ (nonVoters D l).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (SPSkip D l) := inferInstanceAs (Decidable (_ ≤ _))

end FinWhale

end LeanDag
