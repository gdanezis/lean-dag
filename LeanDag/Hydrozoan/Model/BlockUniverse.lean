import LeanDag.Hydrozoan.Model.Block
import LeanDag.Common.BlockRecord
/-!
# The block universe

Trusted core: every block that exists across the whole execution —
authored by anyone, Byzantine, crashed, or correct. Later phases carve
per-replica views out of this universe; the safety theorems quantify
over it.

Here "exists" means **accepted by the DAG-building layer**, not merely
emitted: per `sections/algorithms.tex`, a replica stores a block only
after its entire causal history has been validated, and the decision
rules operate on stored blocks alone. Malformed Byzantine emissions —
dangling parent ids, wrong rounds, duplicate creators — are filtered
before entering any DAG, which is why `complete` and `valid` below hold
for Byzantine-authored blocks too. The Byzantine power that survives the
filter, and that the model does represent, is equivocation and the
adversarial choice of refs, votes, and withholding. The filtering
itself is assumed from Mysticeti, not formalized.

Non-equivocation is stated **here**, at the universe level, rather than
on any individual local DAG. Per-DAG would be too weak: two local DAGs
could each satisfy "at most one block per honest creator per round" while
holding *different* such blocks — which is exactly that creator
equivocating, with both DAGs looking well-formed.

The guard is `NonByzantine`, not `Correct`: crashed replicas follow the
protocol until they halt — they may creator *fewer* blocks (or none), but
never two in one round. Only Byzantine replicas are unconstrained, so
equivocation by them is representable; the witness models exhibit it.
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
