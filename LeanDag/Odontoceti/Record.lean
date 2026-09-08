import LeanDag.Properties.Record
import LeanDag.Odontoceti.Properties
/-!
# Odontoceti on the record

The witness that Odontoceti runs on the core's universes, from which the cut, the copy fill and
re-genesis are the record's own and every verdict cell is
`Properties/Arcs/Record.lean` at this instance.
-/

namespace LeanDag

namespace OdontocetiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section OdontocetiRecord

variable [Faults5 Validator] {B : Type} [LinearOrder B]

/-- **Odontoceti's carrier, read as block records**: the core's, at its
fault model. -/
def onRecord :
    (OdontocetiProperties.odontocetiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)).OnRecord ValidWrt (Correct : Finset Validator) BlockRecord.Any where
  toRec := fun U => U
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

end OdontocetiRecord

end OdontocetiProperties

end LeanDag
