import LeanDag.Properties.Record
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Scheme.Properties
/-!
# The family on the record

The family's carrier reads its universes as block records under the
invariant that `Hon` does not equivocate, by the identity maps: the
witness from which the cut, the fill and re-genesis are the record's own
(`Properties/Arcs/Record.lean`); and the prompt skip after an extension,
from `SkipsUnsupported`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} [P.Mechanised] {honest : Finset Validator}

/-- **The family's carrier, read as block records.** -/
def onRecord (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (Hon : Finset Validator) :
    (schemeRule p σ Hon).OnRecord P honest (fun U => U.NoEquivOn Hon) where
  toRec := fun U => U.val
  inv := fun U => U.property
  ofRec := fun W h => ⟨W, h⟩
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toRec_ofRec := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

open LeanDag.Properties in
/-- **The prompt skip**: after an extension, a slot whose candidates are
all new is skipped at once, at a vote round one above the slot and a
quorum of old blocks one round up that meets the skip threshold. -/
theorem decided_none_of_novel {p : Params} {σ : VoteSel Validator BlockId Payload P honest}
    {Hon : Finset Validator} (hv : p.voteOffset = 1)
    {U U' : (schemeRule p σ Hon).Universe} (he : Extends (schemeRule p σ Hon) U U')
    (S : Slots Validator) {V' : (schemeRule p σ Hon).View U'} {T : Finset Validator} {k : ℕ}
    (hok : p.skipThreshold ≤ T.card) (hpres : PresentAt (schemeRule p σ Hon) V' T (S.slotRound k + 1))
    (hnov : ∀ L, (schemeRule p σ Hon).IsCandidate S U' k L → L ∉ (schemeRule p σ Hon).ids U)
    (hold : ∀ c, c ∈ (schemeRule p σ Hon).viewIds V' →
      ((schemeRule p σ Hon).block U' c).creator ∈ T →
      ((schemeRule p σ Hon).block U' c).round = S.slotRound k + 1 →
      c ∈ (schemeRule p σ Hon).ids U) :
    (schemeRule p σ Hon).Decided S V' k none :=
  Arcs.decided_none_of_novel (skipsUnsupported hv) he S hok hpres hnov hold

end Scheme

end LeanDag
