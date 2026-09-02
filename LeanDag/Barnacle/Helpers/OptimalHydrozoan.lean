import LeanDag.Barnacle.Helpers.Hydrozoan
import LeanDag.OptimalHydrozoan.Model.Decided

/-!
# Optimal-Hydrozoan instance helpers — the schedule-free exclusion rule

Not part of the audit surface. What `docs/hydrozoan-integration.md`
§4.1's obstacle needs, in the form that resolves it.

**The obstacle.** `OptUniverse` is indexed by a `Slots` instance,
because its `leader_excluded` field names `S.leader k` and
`decisionRound k`. `Barnacle.BaseRule` fixes `Universe : Type` before
the schedule arrives and then varies the schedule over that fixed
universe, so the carrier cannot be `OptUniverse`.

**The resolution.** The clause depends on a slot only through its
`(round, leader)` pair, so it can be stated over a pair directly, with
no schedule anywhere — `LeaderExcludedAll` below. That is the rule a
DAG-building layer can actually enforce: it does not need to know who
leads which slot, only that a block which has watched a replica
equivocate two rounds below must not build on that replica.

`optUniverseOf` then produces an `OptUniverse` at **any** schedule, so
the interface may vary the schedule as freely as it likes.

**It is the same condition, not a stronger one.** Leader exclusion at
every schedule and exclusion at every pair imply each other: a slot
gives a pair, and for any pair there is a schedule with a slot at that
round led by that replica. The pair form is simply the one that can be
written down without a schedule. §4.1's earlier proposal quantified
over schedules, and `Barnacle.sched_pair_mono` shows the family Barnacle
actually ranges over is nested — but neither is needed once the clause
is stated where it belongs.
-/

namespace LeanDag

namespace Barnacle

namespace OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]

/-! ## Optimal's fast threshold

Stated in its own section: `OptimalFaults` carries a `Faults` instance
of its own, so having both in scope at once would leave which one a
`BlockUniverse` is indexed by to the elaborator. -/

section FastThreshold

variable [LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- Optimal's fast commit in view is a cardinality comparison, so the
interface's `decDirect` field can synthesise it. -/
instance decFastCommitOptInView
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V : LeanDag.Hydrozoan.View U) (L : BlockId) (r : ℕ) :
    Decidable (LeanDag.OptimalHydrozoan.FastCommitOptInView U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

end FastThreshold

section Rule

variable [LeanDag.Hydrozoan.Faults Replica]

/-- A block of round `r` authored by `v` — `IsLeaderBlock` with the
slot's `(round, leader)` pair given directly. -/
def IsCandidateAt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (r : ℕ)
    (v : Replica) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = r ∧ (U.block L).author = v

/-- `b` has watched `v` equivocate at round `r`: two distinct blocks of
round `r` by `v`, each voted for by one of `b`'s parents. -/
def WitnessesAt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (r : ℕ)
    (v : Replica) (b : BlockId) : Prop :=
  ∃ L₁ L₂, IsCandidateAt U r v L₁ ∧ IsCandidateAt U r v L₂ ∧ L₁ ≠ L₂ ∧
    (∃ j ∈ (U.block b).parents, LeanDag.Hydrozoan.IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).parents, LeanDag.Hydrozoan.IsVote U j L₂)

instance decIsCandidateAt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (r : ℕ) (v : Replica) (L : BlockId) : Decidable (IsCandidateAt U r v L) :=
  inferInstanceAs (Decidable (L ∈ U.ids ∧ (U.block L).round = r ∧ (U.block L).author = v))

instance decWitnessesAt [Fintype BlockId]
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (r : ℕ) (v : Replica) (b : BlockId) : Decidable (WitnessesAt U r v b) :=
  inferInstanceAs (Decidable (∃ L₁ L₂, IsCandidateAt U r v L₁ ∧ IsCandidateAt U r v L₂ ∧
    L₁ ≠ L₂ ∧ (∃ j ∈ (U.block b).parents, LeanDag.Hydrozoan.IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).parents, LeanDag.Hydrozoan.IsVote U j L₂)))

/-- **Leader exclusion, without a schedule.** A block that has watched a
replica equivocate two rounds below it references nothing by that
replica. The round is read off the block rather than quantified, which
keeps the statement decidable on a finite model. -/
def LeaderExcludedAll (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  ∀ b ∈ U.ids, ∀ v : Replica, 2 ≤ (U.block b).round →
    WitnessesAt U ((U.block b).round - 2) v b →
    ∀ j ∈ (U.block b).parents, (U.block j).author ≠ v

instance [Fintype BlockId] (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    Decidable (LeaderExcludedAll U) :=
  inferInstanceAs (Decidable (∀ b ∈ U.ids, ∀ v : Replica, 2 ≤ (U.block b).round →
    WitnessesAt U ((U.block b).round - 2) v b →
    ∀ j ∈ (U.block b).parents, (U.block j).author ≠ v))

end Rule

section OfSchedule

variable [LeanDag.Hydrozoan.Faults Replica] [S : LeanDag.Hydrozoan.Slots Replica]

/-- **The schedule-free rule yields an `OptUniverse` at every
schedule**, which is what lets the carrier be fixed before the
interface supplies one. -/
def optUniverseOf (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : LeaderExcludedAll U) :
    LeanDag.OptimalHydrozoan.OptUniverse Replica BlockId :=
  { U with
    leader_excluded := by
      intro b hb k hround hwit j hj
      have h2 : 2 ≤ (U.block b).round := by
        rw [hround]; unfold LeanDag.Hydrozoan.decisionRound; omega
      have hr : (U.block b).round - 2 = S.slotRound k := by
        rw [hround]; unfold LeanDag.Hydrozoan.decisionRound; omega
      exact h b hb (S.leader k) h2 (by rw [hr]; exact hwit) j hj }

@[simp] theorem optUniverseOf_toBlockUniverse
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (h : LeaderExcludedAll U) :
    (optUniverseOf U h).toBlockUniverse = U := rfl

end OfSchedule

end OptimalHydrozoan

end Barnacle

end LeanDag
