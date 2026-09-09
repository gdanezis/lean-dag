import LeanDag.Properties.Record
import LeanDag.MahiMahi.Properties
/-!
# Mahi-Mahi on the record

The witness that Mahi-Mahi runs on the core's universes, from which the cut, the copy fill and
re-genesis are the record's own and every verdict cell is
`Properties/Arcs/Record.lean` at this instance.
-/

namespace LeanDag

namespace MahiMahiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section MahiMahiRecord

variable [Faults Validator] {B : Type} [LinearOrder B]

/-- **Mahi-Mahi's carrier, read as block records**, at each wave width. -/
def onRecord (w : ℕ) :
    (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) w).OnRecord ValidWrt (Correct : Finset Validator) BlockRecord.Any where
  toRec := fun U => U
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toRec_ofRec := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

end MahiMahiRecord

end MahiMahiProperties

end LeanDag
