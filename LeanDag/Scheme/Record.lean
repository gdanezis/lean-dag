import LeanDag.Properties.Record
import LeanDag.Scheme.Model.Local
/-!
# The family on the record

The family's carrier reads its universes as block records under the
invariant that `Hon` does not equivocate, by the identity maps: the
witness from which the cut, the fill and re-genesis are the record's own
(`Properties/Arcs/Record.lean`).
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

end Scheme

end LeanDag
