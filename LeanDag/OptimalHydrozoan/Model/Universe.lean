import LeanDag.Hydrozoan.Model.DirectRules
/-!
# Optimal-Hydrozoan: the block universe with leader exclusion

Trusted core of the Optimal-Hydrozoan arc; definitions only. Optimal's
validity is Hydrozoan's with one more clause, `Clause.leaderExcluded`:
a block whose parents have voted for two distinct blocks of one replica
references nothing by that replica. The leader of a witnessed
equivocation is then a detected Byzantine replica, which is what the
seam proof counts (`sections/optimal-protocol.tex`). `OptUniverse` is
the block record at that validity, and `toBlockRecord` forgets the
clause: Hydrozoan's rules and lemmas read an Optimal universe through it.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- **Optimal-Hydrozoan's validity**: Hydrozoan's, and leader exclusion. -/
abbrev ValidOpt : Validity Replica BlockId Unit := fun blk b =>
  LeanDag.Hydrozoan.ValidWrt blk b ∧ Clause.leaderExcluded blk b

section Mechanised

omit [DecidableEq BlockId] in
private theorem validOpt_iff (blk : BlockId → Block Replica BlockId Unit)
    (b : Block Replica BlockId Unit) :
    ValidOpt blk b ↔ ValidAt (q Replica) (Clause.distinct.and Clause.leaderExcluded) blk b :=
  ⟨fun h => ⟨h.1.predecessor, h.1.quorum, h.1.distinct_creators, h.2⟩,
   fun h => ⟨⟨h.predecessor, h.clause.1, h.quorum⟩, h.clause.2⟩⟩

/-- **Optimal's validity is the family** at `q`, with distinct creators
and leader exclusion, and so is mechanised. -/
instance ValidOpt.mechanised :
    Validity.Mechanised (ValidOpt (Replica := Replica) (BlockId := BlockId)) :=
  Validity.Mechanised.of_iff (Q := ValidAt (q Replica) (Clause.distinct.and Clause.leaderExcluded))
    validOpt_iff

instance ValidOpt.distinct :
    Validity.Distinct (ValidOpt (Replica := Replica) (BlockId := BlockId)) :=
  Validity.Distinct.of_validAt (C := Clause.distinct.and Clause.leaderExcluded) validOpt_iff
    fun _ _ h => h.1

instance ValidOpt.quorate :
    Validity.Quorate (ValidOpt (Replica := Replica) (BlockId := BlockId)) (q Replica) :=
  Validity.Quorate.of_validAt (C := Clause.distinct.and Clause.leaderExcluded)
    (by have := F.card_replicas; unfold q; omega) validOpt_iff

instance ValidOpt.copyStable :
    Validity.CopyStable (ValidOpt (Replica := Replica) (BlockId := BlockId)) :=
  Validity.CopyStable.of_iff (Q := ValidAt (q Replica) (Clause.distinct.and Clause.leaderExcluded))
    validOpt_iff

end Mechanised

/-- **The block universe**: the block record at Optimal's validity, with
non-equivocation asked of the non-Byzantine replicas. -/
abbrev OptUniverse (Replica BlockId : Type*) [Fintype Replica]
    [DecidableEq Replica] [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica] :=
  BlockRecord Replica BlockId Unit ValidOpt (NonByzantine : Finset Replica)

/-- **The Hydrozoan universe beneath**: the same blocks, the exclusion
forgotten. Hydrozoan's rules and lemmas read an Optimal universe through
it. -/
def OptUniverse.toBlockRecord (U : OptUniverse Replica BlockId) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  { U with valid := fun i hi => (U.valid i hi).1 }

variable [S : Slots Replica]

/-- `b` witnesses an equivocation in slot `k` (the paper's
`WitnessesEquivocation(b, w)`, Algorithm 3): two *distinct* candidates of
slot `k` are each voted for by some parent of `b`. -/
def WitnessesEquivocation (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ)
    (b : BlockId) : Prop :=
  ∃ L₁ L₂, IsLeaderBlock U k L₁ ∧ IsLeaderBlock U k L₂ ∧ L₁ ≠ L₂ ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₂)

/-- **Leader exclusion at a schedule** — the validity rule as
`sections/optimal-protocol.tex` states it: a block at the decision round
of slot `k` that witnesses an equivocation in `k` references no block by
`k`'s leader. The form the decision relation's laws hold under; every
Optimal universe satisfies it at every schedule
(`OptUniverse.leader_excluded`). -/
def LeaderExcluded (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  ∀ b ∈ U.ids, ∀ k,
    (U.block b).round = LeanDag.Hydrozoan.decisionRound Replica k →
    WitnessesEquivocation U k b →
    ∀ j ∈ (U.block b).refs, (U.block j).creator ≠ S.leader k

end OptimalHydrozoan

end LeanDag
