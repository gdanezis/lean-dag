import LeanDag.Hydrozoan.Model.DirectRules
/-!
# Optimal-Hydrozoan: the block universe with leader exclusion

Trusted core of the Optimal-Hydrozoan arc: the "DAG-building layer"
paragraph of `sections/optimal-protocol.tex`, i.e. FinWhale's validity
rule, as one extra well-formedness condition on the block universe.
Definitions only.

`OptUniverse` *extends* Hydrozoan's `BlockUniverse` (frozen, untouched):
every condition of the base — completeness, validity, non-equivocation
of non-Byzantine creators — is inherited, and every Hydrozoan lemma
applies to `U.toBlockRecord`. Views are Hydrozoan's `View` over that
projection; nothing new is needed there.

The extra condition is what buys the arc its extra fast-path fault: a
decision-round block that has *seen* a leader equivocate (its refs
vote for two distinct blocks of that leader's slot) must not reference
that leader's own block. The leader is then a **detected** Byzantine
replica, and the seam proof (O6) counts at most `f − 1` undetected
Byzantine replicas among the block's refs. The rule constrains which
blocks a replica references — not how votes are counted; the counting
dividend is a theorem, not a definition.

**Fidelity** (decision D6): "a parent votes for `L`" is the direct
reference `L ∈ refs`, exactly the paper's `Votes(b, ·)` read at wave
length 3; and the paper's `WitnessesEquivocation(b, w)` quantifies over
the leader blocks in the local DAG, which coincides with the
universe-level form here because the two blocks a witnessing block sees
are refs of its refs, hence held by any view holding the block.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-- A block of round `r` authored by `v` — `IsLeaderBlock` with the
slot's `(round, leader)` pair given directly. -/
def IsCandidateAt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (r : ℕ)
    (v : Replica) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = r ∧ (U.block L).creator = v

/-- `b` has watched `v` equivocate at round `r`: two distinct blocks of
round `r` by `v`, each voted for by one of `b`'s refs. -/
def WitnessesAt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (r : ℕ)
    (v : Replica) (b : BlockId) : Prop :=
  ∃ L₁ L₂, IsCandidateAt U r v L₁ ∧ IsCandidateAt U r v L₂ ∧ L₁ ≠ L₂ ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₂)

/-- **Leader exclusion, without a schedule.** A block that has watched a
replica equivocate two rounds below it references nothing by that
replica. The clause depends on a slot only through its `(round, leader)`
pair, so this is the form a DAG-building layer can enforce without
knowing who leads which slot, and the form the carrier's universes
carry; the round is read off the block rather than quantified, which
keeps it decidable on a finite model. It implies the slot form at every
schedule (`leaderExcluded_of_all`). -/
def LeaderExcludedAll (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  ∀ b ∈ U.ids, ∀ v : Replica, 2 ≤ (U.block b).round →
    WitnessesAt U ((U.block b).round - 2) v b →
    ∀ j ∈ (U.block b).refs, (U.block j).creator ≠ v

variable [S : Slots Replica]

/-- `b` witnesses an equivocation in slot `k` (the paper's
`WitnessesEquivocation(b, w)`, Algorithm 3): two *distinct* candidates of
slot `k` — two blocks by `k`'s leader at `k`'s propose round — are each
voted for by some parent of `b`. Stated for any block `b`; the round at
which the rule applies is fixed by `OptUniverse.leader_excluded`.

A plain definition, like the top-level rules of `Model/DirectRules.lean`:
its `Decidable` instance (over a `Fintype` of ids) lives in
`Optimal/Helpers/Universe.lean`. -/
def WitnessesEquivocation (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ)
    (b : BlockId) : Prop :=
  ∃ L₁ L₂, IsLeaderBlock U k L₁ ∧ IsLeaderBlock U k L₂ ∧ L₁ ≠ L₂ ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₂)

/-- **Leader exclusion at a schedule** — the validity rule of
`sections/optimal-protocol.tex`: a block at the decision round of slot
`k` that witnesses an equivocation in `k` references no block authored
by `k`'s leader. The round guard is stated explicitly (decision D4)
although it is *redundant* for `b ∈ ids`: witnessing already forces
`b`'s round to be `k`'s decision round (twice `predecessor`, from a
voted candidate at `k`'s propose round), so no witness can tell its
presence — it is here so the rule reads as the paper states it. With
several slots per round the rule applies to each slot separately, which
the `∀ k` gives directly. The invariant the decision relation's laws
hold under. -/
def LeaderExcluded (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  ∀ b ∈ U.ids, ∀ k,
    (U.block b).round = LeanDag.Hydrozoan.decisionRound Replica k →
    WitnessesEquivocation U k b →
    ∀ j ∈ (U.block b).refs, (U.block j).creator ≠ S.leader k

/-- Hydrozoan's block universe plus the leader-exclusion rule. -/
structure OptUniverse (Replica BlockId : Type*) [Fintype Replica]
    [DecidableEq Replica] [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
    [S : Slots Replica] extends LeanDag.Hydrozoan.BlockUniverse Replica BlockId where
  /-- **Leader exclusion**, at the schedule the universe is indexed by. -/
  leader_excluded : LeaderExcluded toBlockRecord

end OptimalHydrozoan

end LeanDag
