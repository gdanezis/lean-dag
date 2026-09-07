import LeanDag.OptimalHydrozoan.Model.Universe
import LeanDag.Hydrozoan.Helpers.Block
/-!
# Optimal-Hydrozoan: universe lemmas

Generated proof infrastructure over `Optimal/Model/Universe.lean`; not
part of the audit surface.

`leaderExcluded_of_bounded` is the bridge the witness models use: the
`leader_excluded` field quantifies over every slot `k`, which `decide`
cannot enumerate, but for a universe whose rounds stop at `N` only slots
with a decision round `≤ N` matter, and a concrete schedule bounds those
slots by some `B` (`B = N` for the pipelined schedule, `B = 2N` with two
slots per round) — so the bounded, decidable form suffices. The
`Decidable` instance lets the witness models check
`WitnessesEquivocation` by `decide` (the existential ranges over a
`Fintype` of ids).
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

/-! ## The schedule-free exclusion -/

instance decIsCandidateAt (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (r : ℕ) (v : Replica) (L : BlockId) : Decidable (IsCandidateAt U r v L) :=
  inferInstanceAs (Decidable (L ∈ U.ids ∧ (U.block L).round = r ∧ (U.block L).creator = v))

instance decWitnessesAt [Fintype BlockId]
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (r : ℕ) (v : Replica) (b : BlockId) : Decidable (WitnessesAt U r v b) :=
  inferInstanceAs (Decidable (∃ L₁ L₂, IsCandidateAt U r v L₁ ∧ IsCandidateAt U r v L₂ ∧
    L₁ ≠ L₂ ∧ (∃ j ∈ (U.block b).refs, IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).refs, IsVote U j L₂)))

instance [Fintype BlockId] (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    Decidable (LeaderExcludedAll U) :=
  inferInstanceAs (Decidable (∀ b ∈ U.ids, ∀ v : Replica, 2 ≤ (U.block b).round →
    WitnessesAt U ((U.block b).round - 2) v b →
    ∀ j ∈ (U.block b).refs, (U.block j).creator ≠ v))

variable [S : Slots Replica]

omit [DecidableEq BlockId] in
/-- **The schedule-free exclusion is exclusion at every schedule.** -/
theorem leaderExcluded_of_all (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : LeaderExcludedAll U) : LeaderExcluded (S := S) U := by
  intro b hb k hround hwit j hj
  have h2 : 2 ≤ (U.block b).round := by
    rw [hround]; unfold LeanDag.Hydrozoan.decisionRound; omega
  have hr : (U.block b).round - 2 = S.slotRound k := by
    rw [hround]; unfold LeanDag.Hydrozoan.decisionRound; omega
  exact h b hb (S.leader k) h2 (by rw [hr]; exact hwit) j hj

/-- **The schedule-free rule yields an `OptUniverse` at every
schedule**, which is what lets the carrier be fixed before a schedule
is supplied. -/
def optUniverseOf (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : LeaderExcludedAll U) : OptUniverse Replica BlockId :=
  ⟨U, leaderExcluded_of_all U h⟩

@[simp] theorem optUniverseOf_toBlockRecord
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (h : LeaderExcludedAll U) :
    (optUniverseOf U h).toBlockRecord = U := rfl

/-! ## Witnessing, decided through the refs -/

omit [DecidableEq BlockId] in
/-- Witnessing an equivocation, read off the refs' refs: the two
candidates are votes' targets, so they sit two references below `b`.
This is the form the witness models decide — a few dozen checks instead
of a quadratic scan of all ids. -/
theorem witnessesEquivocation_iff_refs (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (k : ℕ) (b : BlockId) :
    WitnessesEquivocation U k b ↔
      ∃ j₁ ∈ (U.block b).refs, ∃ L₁ ∈ (U.block j₁).refs,
      ∃ j₂ ∈ (U.block b).refs, ∃ L₂ ∈ (U.block j₂).refs,
        IsLeaderBlock U k L₁ ∧ IsLeaderBlock U k L₂ ∧ L₁ ≠ L₂ := by
  constructor
  · rintro ⟨L₁, L₂, h₁, h₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    exact ⟨j₁, hj₁, L₁, hv₁, j₂, hj₂, L₂, hv₂, h₁, h₂, hne⟩
  · rintro ⟨j₁, hj₁, L₁, hv₁, j₂, hj₂, L₂, hv₂, h₁, h₂, hne⟩
    exact ⟨L₁, L₂, h₁, h₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩

/-- Witnessing an equivocation is decidable, through the refs' form. -/
instance decidableWitnessesEquivocation
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ) (b : BlockId) :
    Decidable (WitnessesEquivocation U k b) :=
  decidable_of_iff _ (witnessesEquivocation_iff_refs U k b).symm

omit [DecidableEq BlockId] in
/-- A universe with no two blocks of one creator in one round witnesses no
equivocation anywhere: the two candidates would be such a pair. -/
theorem not_witnessesEquivocation_of_noEquivocation (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator = (U.block j).creator →
      (U.block i).round = (U.block j).round → i = j)
    (k : ℕ) (b : BlockId) : ¬ WitnessesEquivocation U k b := by
  rintro ⟨L₁, L₂, hL₁, hL₂, hne, -, -⟩
  exact hne (h L₁ hL₁.1 L₂ hL₂.1 (hL₁.2.2.trans hL₂.2.2.symm)
    (hL₁.2.1.trans hL₂.2.1.symm))

omit [DecidableEq BlockId] in
/-- In such a universe the leader-exclusion clause holds vacuously — the
cheap route for equivocation-free witness models. -/
theorem leaderExcluded_of_noEquivocation (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator = (U.block j).creator →
      (U.block i).round = (U.block j).round → i = j) :
    LeaderExcluded (S := S) U :=
  fun b _ k _ hw => absurd hw (not_witnessesEquivocation_of_noEquivocation U h k b)

omit [DecidableEq BlockId] in
/-- The leader-exclusion clause follows from its restriction to slots
`k ≤ B`, given that every slot whose decision round is at most `N` has
index at most `B`, and that no block sits above round `N`. -/
theorem leaderExcluded_of_bounded (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (N B : ℕ)
    (hslot : ∀ k, S.slotRound k + 2 ≤ N → k ≤ B)
    (hround : ∀ b ∈ U.ids, (U.block b).round ≤ N)
    (h : ∀ b ∈ U.ids, ∀ k ≤ B,
      (U.block b).round = LeanDag.Hydrozoan.decisionRound Replica k →
      WitnessesEquivocation U k b →
      ∀ j ∈ (U.block b).refs, (U.block j).creator ≠ S.leader k) :
    LeaderExcluded (S := S) U := by
  intro b hb k hk
  refine h b hb k ?_ hk
  have h1 := hround b hb
  simp only [LeanDag.Hydrozoan.decisionRound] at hk
  exact hslot k (by omega)

end OptimalHydrozoan

end LeanDag
