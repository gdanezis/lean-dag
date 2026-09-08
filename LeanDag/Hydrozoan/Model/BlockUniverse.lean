import LeanDag.Hydrozoan.Model.Block
import LeanDag.Common.BlockRecord
/-!
# The block universe

Every block that exists across the whole execution, authored by anyone.
"Exists" means accepted by the DAG-building layer, not merely emitted:
malformed Byzantine emissions are filtered before entering any DAG, so
`complete` and `valid` hold of Byzantine-authored blocks too, and what
survives is equivocation and the adversarial choice of refs and votes.
Non-equivocation is stated at the universe level, guarded by
`NonByzantine` rather than `Correct`: crashed replicas never equivocate,
only Byzantine ones are unconstrained.
-/

namespace LeanDag

namespace Hydrozoan

/-- **The block universe**: the block record at Hydrozoan's validity,
with non-equivocation asked of the non-Byzantine replicas. `block` is
total, with junk outside `ids`; every clause quantifies over `i ∈ ids`,
so the junk is never observed. -/
abbrev BlockUniverse (Replica BlockId : Type*) [Fintype Replica]
    [DecidableEq Replica] [F : LeanDag.Hydrozoan.Faults Replica] :=
  BlockRecord Replica BlockId Unit ValidWrt (NonByzantine : Finset Replica)

section Mechanised

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : Faults Replica]

/-- **Hydrozoan's validity is the family** at `q`, with distinct creators
and no further clause, and so is mechanised. -/
instance ValidWrt.mechanised :
    Validity.Mechanised (ValidWrt (Replica := Replica) (BlockId := BlockId)) :=
  Validity.Mechanised.of_iff (Q := ValidAt (q Replica) Clause.distinct) fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators⟩,
     fun h => ⟨h.predecessor, h.clause, h.quorum⟩⟩

/-- **With distinct creators among references.** -/
instance ValidWrt.distinct :
    Validity.Distinct (ValidWrt (Replica := Replica) (BlockId := BlockId)) :=
  Validity.Distinct.of_validAt (C := Clause.distinct) (fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators⟩,
     fun h => ⟨h.predecessor, h.clause, h.quorum⟩⟩) fun _ _ h => h

/-- **And quorate at `q`.** -/
instance ValidWrt.quorate :
    Validity.Quorate (ValidWrt (Replica := Replica) (BlockId := BlockId)) (q Replica) :=
  Validity.Quorate.of_validAt (C := Clause.distinct)
    (by have := F.card_replicas; unfold q; omega) fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators⟩,
     fun h => ⟨h.predecessor, h.clause, h.quorum⟩⟩

/-- **And does not read the creator.** -/
instance ValidWrt.copyStable :
    Validity.CopyStable (ValidWrt (Replica := Replica) (BlockId := BlockId)) :=
  Validity.CopyStable.of_iff (Q := ValidAt (q Replica) Clause.distinct) fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators⟩,
     fun h => ⟨h.predecessor, h.clause, h.quorum⟩⟩

end Mechanised

end Hydrozoan

end LeanDag
