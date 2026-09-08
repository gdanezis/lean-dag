import LeanDag.Properties.Agreement
/-!
# Truncation: pruning below a horizon, and renumbering from it

`docs/target-properties.md` §3.4. Restriction and renumbering are not
separately realisable properties: a renumbering alone would put the
retained bottom layer at round zero carrying the references it had
higher up, which a round-zero block's empty-references clause forbids
(`Hydrozoan/Helpers/Truncation.lean` carries the witness). `Truncates`
below is the one combined relation that does have models, with
`truncates_chopHZ` exhibiting the development's own truncation as a
witness. `Local` states what a verdict reads and survives unchanged; it
is simply not what a renumbering mechanism consumes.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **The schedule moves with the DAG.** Slot `k` of the truncated
schedule is slot `d + k` of the original, at a round `G` lower, leading
the same replica. Separate from the block relation, since the two axes
are independent and a mechanism touching only one states only one. -/
structure Rebases (S S' : Slots Validator) (G d : ℕ) : Prop where
  /-- Rounds fall by the horizon. -/
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  /-- And each slot leads the same replica. -/
  leader : ∀ k, S'.leader k = S.leader (d + k)
  /-- The horizon does not reach past the base slot. -/
  base : G ≤ S.slotRound d

/-- **`U'` is `U` pruned below `G` and renumbered from slot `d`.**
`mem` keeps only what lies at or above the horizon, and `refs` compares
references strictly above it, so the retained bottom layer may lose
what pointed below it. Both are `RebasedAbove`'s, at `R₀ = G`; what
this structure adds is the schedule half. -/
structure Truncates (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (S S' : Slots Validator) (G d : ℕ) : Prop
    extends RebasedAbove R U U' G G, Rebases S S' G d

namespace Truncates

variable {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}

/-- **What survives the cut**, in the shape the cut is usually read in:
the blocks at or above the horizon, and no others. The inherited `mem`
pairs the round condition on both sides, which at `R₀ = G` is vacuous on
the right. -/
theorem mem_iff (h : Truncates R U U' S S' G d) (b : BlockId) :
    b ∈ R.ids U' ↔ (b ∈ R.ids U ∧ G ≤ (R.block U b).round) := by
  constructor
  · intro hb; exact (h.mem b).mpr ⟨hb, by omega⟩
  · rintro ⟨hb, hr⟩; exact ((h.mem b).mp ⟨hb, hr⟩).1

/-- Rounds fall by the horizon, read from the truncation. -/
theorem round_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U') :
    (R.block U' b).round + G = (R.block U b).round :=
  have hm := (h.mem_iff b).mp hb
  h.round b hm.1 hm.2

/-- Authors are untouched, read from the truncation. -/
theorem creator_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U') :
    (R.block U' b).creator = (R.block U b).creator :=
  have hm := (h.mem_iff b).mp hb
  h.creator b hm.1 hm.2

/-- And references survive strictly above the horizon. -/
theorem refs_of (h : Truncates R U U' S S' G d) {b : BlockId} (hb : b ∈ R.ids U')
    (hgt : G < (R.block U b).round) :
    (R.block U' b).refs = (R.block U b).refs :=
  h.refs b ((h.mem_iff b).mp hb).1 hgt

end Truncates

end Properties

end LeanDag
