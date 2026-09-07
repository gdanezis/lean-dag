import LeanDag.Barnacle.Model.Anchored
/-!
# The laws of an anchored rule, once

Not part of the audit surface. `BaseRule.Laws` for `ofAnchored` and
`ofAnchoredOn`: the view laws by construction, the three properties from
`Common/Anchored/Band.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {R : AnchoredRule Validator BlockId Payload P honest}

/-- **An anchored rule with its laws satisfies Barnacle's.** -/
theorem ofAnchored_laws (hl : R.Laws) : (ofAnchored R).Laws where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := AnchoredRule.agree hl
  commitsDirect := AnchoredRule.commitsDirect
  candidates := AnchoredRule.commitsCandidate

/-- **And under an invariant** that implies the laws' own at every schedule. -/
theorem ofAnchoredOn_laws {I : BlockRecord Validator BlockId Payload P honest → Prop}
    {J : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hl : R.Laws J) (hJ : ∀ S U, I U → J S U) : (ofAnchoredOn R I).Laws where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := AnchoredRule.agreeOn hl hJ
  commitsDirect := AnchoredRule.commitsDirectOn
  candidates := AnchoredRule.commitsCandidateOn

end Barnacle

end LeanDag
