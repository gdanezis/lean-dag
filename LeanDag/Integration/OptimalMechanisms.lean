import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.Integration.HydrozoanMechanisms
/-!
# Garbage collection, crash recovery and re-genesis for Optimal-Hydrozoan

Optimal-Hydrozoan's universe is the block record at its own validity,
which is `Mechanised` and `CopyStable` (`Optimal/Model/Universe.lean`),
so the carrier reads as records with every map the identity and every
mechanism cell is `Arcs/Record.lean` at `optOnRecord`. Leader exclusion
needs no proof of its own here: it is a clause of validity, and the
record's cut, copy fill and re-genesis preserve validity clause by
clause.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan's carrier, on the record**: every map the
identity, the views read at the projection. -/
def optOnRecord :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).OnRecord LeanDag.OptimalHydrozoan.ValidOpt
      (LeanDag.Hydrozoan.NonByzantine : Finset Replica) BlockRecord.Any where
  toRec := fun U => U
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  ofView := fun V => ⟨V.ids, V.subset_ids, V.complete⟩
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

end Integration

end LeanDag
