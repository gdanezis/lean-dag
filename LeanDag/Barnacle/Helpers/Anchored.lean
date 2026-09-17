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
theorem ofAnchored_laws (hw : ∀ r, R.waveAt r = R.waveAt 0) (hl : R.Laws) :
    (ofAnchored R hw).Laws where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := AnchoredRule.agree hl
  commitsDirect := AnchoredRule.commitsDirect
  candidates := AnchoredRule.commitsCandidate

/-- **And through a projection** whose images satisfy the laws' invariant
at every schedule. -/
theorem ofAnchoredVia_laws {X : Type} {f : X → BlockRecord Validator BlockId Payload P honest}
    {J : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hw : ∀ r, R.waveAt r = R.waveAt 0) (hl : R.Laws J) (hJ : ∀ S U, J S (f U)) :
    (ofAnchoredVia R f hw).Laws where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := AnchoredRule.agreeVia hl hJ
  commitsDirect := AnchoredRule.commitsDirectVia
  candidates := AnchoredRule.commitsCandidateVia

/-- **And under an invariant** that implies the laws' own at every schedule. -/
theorem ofAnchoredOn_laws {I : BlockRecord Validator BlockId Payload P honest → Prop}
    {J : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hw : ∀ r, R.waveAt r = R.waveAt 0) (hl : R.Laws J) (hJ : ∀ S U, I U → J S U) :
    (ofAnchoredOn R I hw).Laws :=
  ofAnchoredVia_laws hw hl fun S U => hJ S U.val U.property

end Barnacle

end LeanDag
