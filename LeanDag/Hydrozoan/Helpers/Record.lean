import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Properties.Record
/-!
# Hydrozoan's universe as a block record

Not part of the audit surface. Hydrozoan's universe *is* the block
record at `Hydrozoan.ValidWrt` with non-equivocation asked of the
non-Byzantine replicas, so what this file supplies is the carrier's `OnRecord`, every map the
identity; that its validity is `Mechanised` and does not read the
creator is stated with the universe, in `Model/BlockUniverse.lean`. The
mechanisms of `Integration/HydrozoanMechanisms.lean` are then the
record's.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]

/-- **The carrier, on the record**: every map the identity. -/
def onRecord : (rule (Replica := Replica) (BlockId := BlockId)).OnRecord ValidWrt
    (NonByzantine : Finset Replica) BlockRecord.Any where
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

end Hydrozoan

end LeanDag
