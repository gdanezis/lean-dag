import LeanDag.Integration.Hydrozoan.ChopDecided
import LeanDag.Barnacle.Helpers.OptimalHydrozoan

/-!
# Optimal-Hydrozoan's validity clause across the transformers

`docs/hydrozoan-integration.md` §5's prior obligation, and the gate on
HI7 and HI9 for `DecidedOpt`. `transport` (§10.4) carries
`SelfParenting` for every transformer by one lemma
(`selfParenting_ofCore`); an `OptUniverse` carries a second clause,
leader exclusion, and a transformer must preserve that too before
`optUniverseOf` can rebuild the Optimal universe on the other side.

The clause is stated schedule-free, as `Barnacle.OptimalHydrozoan`'s
`LeaderExcludedAll`: a block that has watched a replica equivocate two
rounds below it references nothing by that replica. §4.1 records why
that form and not the `OptUniverse` field's — the field names
`S.leader k`, and a transformer changes the schedule.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

open LeanDag.Barnacle.OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [LeanDag.Hydrozoan.Faults Replica] [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {hsp : SelfParenting U} {G : ℕ}

/-! ## The cut

A truncation removes blocks and empties the references of the layer it
retains at the bottom. Both directions are in its favour: the emptied
layer discharges the clause vacuously, and above it every block, every
reference and every vote is the one it was, so a witness in the
truncation is a witness in the universe it came from. -/

/-- A candidate of the truncation is a candidate of the original, at
the round shifted by the horizon. -/
theorem isCandidateAt_of_chopHZ {r : ℕ} {v : Replica} {L : BlockId}
    (h : IsCandidateAt (chopHZ U hsp G) r v L) :
    IsCandidateAt U (G + r) v L := by
  obtain ⟨hmem, hround, hauth⟩ := h
  obtain ⟨hL, hGL⟩ := mem_chopHZ_ids.mp hmem
  rw [chopHZ_round] at hround
  rw [chopHZ_author] at hauth
  exact ⟨hL, by omega, hauth⟩

/-- And a witness in the truncation is a witness in the original. A vote
is membership in the voter's references, and the cut empties those only
at the layer it retains at the bottom — so a vote that survives the cut
was read from a block above it, whose references are unchanged. -/
theorem witnessesAt_of_chopHZ {r : ℕ} {v : Replica} {b : BlockId}
    (hb : G < (U.block b).round) (h : WitnessesAt (chopHZ U hsp G) r v b) :
    WitnessesAt U (G + r) v b := by
  obtain ⟨L₁, L₂, h1, h2, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := h
  rw [chopHZ_parents_of_lt hb] at hj₁ hj₂
  refine ⟨L₁, L₂, isCandidateAt_of_chopHZ h1, isCandidateAt_of_chopHZ h2, hne,
    ⟨j₁, hj₁, ?_⟩, ⟨j₂, hj₂, ?_⟩⟩
  · rcases lt_or_ge G (U.block j₁).round with hj | hj
    · rwa [LeanDag.Hydrozoan.IsVote, chopHZ_parents_of_lt hj] at hv₁
    · rw [LeanDag.Hydrozoan.IsVote, chopHZ_parents_of_le hj] at hv₁
      exact absurd hv₁ (Finset.notMem_empty _)
  · rcases lt_or_ge G (U.block j₂).round with hj | hj
    · rwa [LeanDag.Hydrozoan.IsVote, chopHZ_parents_of_lt hj] at hv₂
    · rw [LeanDag.Hydrozoan.IsVote, chopHZ_parents_of_le hj] at hv₂
      exact absurd hv₂ (Finset.notMem_empty _)

/-- **Leader exclusion survives the cut.** -/
theorem leaderExcludedAll_chopHZ (h : LeaderExcludedAll U) :
    LeaderExcludedAll (chopHZ U hsp G) := by
  intro b hb v h2 hwit j hj
  -- a block whose references the cut emptied discharges the clause
  by_cases hlow : (U.block b).round ≤ G
  · rw [chopHZ_parents_of_le hlow] at hj; exact absurd hj (Finset.notMem_empty j)
  rw [not_le] at hlow
  rw [chopHZ_parents_of_lt hlow] at hj
  rw [chopHZ_author]
  rw [chopHZ_round] at h2 hwit
  refine h b (mem_chopHZ_ids.mp hb).1 v (by omega) ?_ j hj
  have := witnessesAt_of_chopHZ (hsp := hsp) hlow hwit
  have hrw : G + ((U.block b).round - G - 2) = (U.block b).round - 2 := by omega
  rwa [hrw] at this

/-! ## The fill does not preserve the clause

The recovering replica's block references its own anchor `B1` **and**
the donor's references at that round. Neither block need have seen what
the other saw, so the pair can witness an equivocation that nothing in
the original universe witnessed — and then leader exclusion, which held
before the recovery, fails after it.

Concretely, at the first gap round `k = r0 + 1`: the filled block's
references are `insert B1 (U.block (line (r0+1))).refs`, all at round
`r0`. Let `v` equivocate at round `r0 - 1` with twins `L₁ ≠ L₂`, let
`B1` reference `L₁`, and let some reference of `line (r0+1)` reference
`L₂`. The filled block then witnesses `v`'s equivocation at its own
round minus two, and its references include a block authored by `v`.
In the original universe nothing witnesses: `line (r0+1)` sees only
`L₂`, and `hline_chain` puts `line r0` among its references but says
nothing about `B1`.

This is not a defect of `skipFill`, which proves the four validity
rules of a `BlockUniverse` and never claimed the Optimal clause. It is
the point at which the two protocols separate for a second time, and
`docs/hydrozoan-integration.md` §5.1 records the first. The repair
belongs to the fill: a recovering replica applying the Optimal rule
would drop the references the rule excludes, which is a different
construction from `skipFill` rather than a side condition on it.

`leaderExcludedAll_chopHZ` above therefore carries HI7 for `DecidedOpt`,
and HI9 for `DecidedOpt` waits on that construction.
`LeanDagTest/Integration/HydrozoanOptimal.lean` witnesses the failure. -/

end Hydrozoan

end Integration

end LeanDag
