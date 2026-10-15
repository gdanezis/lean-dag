import LeanDag.Properties.Record
import LeanDag.Steelhead.Properties
/-!
# Steelhead on the record

The witness that Steelhead runs on the core's universes, from which the cut, the copy fill and
re-genesis are the record's own and every verdict cell is
`Properties/Arcs/Record.lean` at this instance.
-/

namespace LeanDag

namespace SteelheadProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {Payload : Type}

section SteelheadRecord

variable [Faults Validator] {B : Type} [LinearOrder B]

/-- **Steelhead's carrier, read as block records**, at each wavelength function. -/
def onRecord (w : ℕ → ℕ) :
    (steelheadRule (Validator := Validator) (BlockId := B) (Payload := Payload) w).OnRecord
      ValidWrt (Correct : Finset Validator) BlockRecord.Any where
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

end SteelheadRecord

end SteelheadProperties

end LeanDag
