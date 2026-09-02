import LeanDag.Integration.Hydrozoan.OptimalTransport

/-!
# The fill breaks leader exclusion — the witness

`docs/hydrozoan-integration.md` §5 argues that `skipFill` does not
preserve Optimal-Hydrozoan's validity clause. This file settles it, in
the way §2's `c ≤ k` was settled: by a universe on which the clause
holds and on whose fill it fails.

**The configuration.** Four replicas, `2` Byzantine, `q = 3`. Replica
`2` equivocates at round `0` with the twins `2` and `4`. The recovering
replica `1` authors the anchor `5` at round `1`, and `5` is the only
block in the universe that references the twin `2` — every other
round-`1` block references the twin `4`. The donor `0` runs the line
`7`, `9`.

**Why the clause holds.** A block must be two rounds above the
equivocation to witness it, so only `9` could, and `9`'s references are
`{7, 6, 8}`. None of those references the twin `2`: the only block that
does is the anchor `5`, and `9` does not reference `5` — which is the
crash, since replica `1` stopped and nobody built on it.

**Why the fill breaks it.** The filled block `12` references
`insert B1 (block (line 2)).refs = {5, 6, 7, 8}`. The anchor `5` brings
the twin `2` into view and `6` brings the twin `4`, so `12` witnesses
replica `2`'s equivocation two rounds below itself — and `12`
references `6`, which replica `2` authored. That is exactly what the
clause forbids.

The recovery put the anchor and the donor's references side by side.
Neither had seen what the other saw, and the pair witnesses what
neither did.
-/

namespace LeanDagTest

namespace Integration

open LeanDag LeanDag.Integration.Hydrozoan
open LeanDag.Barnacle.OptimalHydrozoan

/-- Four replicas with one Byzantine and none crashed: `q = 3`, and
`3·(f + c) + 1 = 4` meets the committee bound exactly. -/
instance exclFaults : LeanDag.Hydrozoan.Faults (Fin 4) where
  f := 1
  c := 0
  k := 0
  byzantine := {2}
  crashed := ∅
  byzantine_disjoint_crashed := by decide
  card_replicas := by decide
  card_byzantine := by decide
  card_crashed := by decide

instance : Fact (HybridCommittee (Fin 4)) := ⟨by decide⟩

/-- Ten blocks. Round `0` carries five, two of them replica `2`'s
twins; round `1` carries one per replica; round `2` carries the donor's
line block alone. -/
def lkx : ℕ → LeanDag.Hydrozoan.Block (Fin 4) ℕ := fun i =>
  if i = 0 then { round := 0, author := 0, parents := ∅ }
  else if i = 1 then { round := 0, author := 1, parents := ∅ }
  else if i = 2 then { round := 0, author := 2, parents := ∅ }
  else if i = 3 then { round := 0, author := 3, parents := ∅ }
  else if i = 4 then { round := 0, author := 2, parents := ∅ }
  -- round 1: the anchor `5` is the only block that sees the twin `2`
  else if i = 5 then { round := 1, author := 1, parents := {1, 2, 0} }
  else if i = 6 then { round := 1, author := 2, parents := {4, 0, 3} }
  else if i = 7 then { round := 1, author := 0, parents := {0, 4, 3} }
  else if i = 8 then { round := 1, author := 3, parents := {3, 4, 0} }
  -- round 2: the donor's line block, which does not reference the anchor
  else if i = 9 then { round := 2, author := 0, parents := {7, 6, 8} }
  else { round := 0, author := 0, parents := ∅ }

/-- The universe. -/
def Ux : LeanDag.Hydrozoan.BlockUniverse (Fin 4) ℕ where
  ids := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
  block := lkx
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem selfParenting_Ux : SelfParenting Ux := by decide

/-! ## The clause holds before the recovery -/

/-- Replica `2` does equivocate: two distinct blocks at round `0`. -/
example : (Ux.block 2).round = 0 ∧ (Ux.block 4).round = 0 ∧
    (Ux.block 2).author = 2 ∧ (Ux.block 4).author = 2 ∧ (2 : ℕ) ≠ 4 := by decide

/-- Every block the round-`2` block can read a vote from votes only for
`0`, `3` or `4` — never for the twin `2`, which only the anchor `5`
references. Bounded by two `Finset`s, so `decide` settles it. -/
theorem votes_of_nine :
    ∀ j ∈ (Ux.block 9).parents, ∀ L ∈ (Ux.block j).parents,
      L = 0 ∨ L = 3 ∨ L = 4 := by decide

/-- So the round-`2` block witnesses nothing: the three blocks it can
see are authored by three different replicas, and a witness needs two
by the same one. -/
theorem no_witness_nine (v : Fin 4) : ¬ WitnessesAt Ux 0 v 9 := by
  rintro ⟨L₁, L₂, ⟨-, -, ha1⟩, ⟨-, -, ha2⟩, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
  rcases votes_of_nine j₁ hj₁ L₁ hv₁ with rfl | rfl | rfl <;>
    rcases votes_of_nine j₂ hj₂ L₂ hv₂ with rfl | rfl | rfl <;>
      first | exact hne rfl | exact absurd (ha1.trans ha2.symm) (by decide)

/-- And no other block is high enough to witness anything. -/
theorem no_witness_Ux :
    ∀ b ∈ Ux.ids, ∀ v : Fin 4, 2 ≤ (Ux.block b).round →
      ¬ WitnessesAt Ux ((Ux.block b).round - 2) v b := by
  intro b hb v h2
  simp only [Ux, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact absurd h2 (by decide) | exact no_witness_nine v

/-- **Leader exclusion holds**, vacuously through the absent witness. -/
theorem leaderExcludedAll_Ux : LeaderExcludedAll Ux := by
  intro b hb v h2 hwit
  exact absurd hwit (no_witness_Ux b hb v h2)

/-! ## The recovery -/

/-- Replica `1` rejoins from its round-`1` anchor, on replica `0`'s
line, filling round `2` alone. -/
def skx : SkipMsg (toCore Ux selfParenting_Ux) where
  v1 := 1
  B1 := 5
  v2 := 0
  r := 2
  line k := if k = 1 then 7 else 9
  fresh k := 10 + k
  idx b := b - 10
  hB1uniq := by decide
  hv12 := by decide
  hB1 := by decide
  hB1c := by decide
  hline_mem := by
    intro k hk1 hk2
    have : k = 1 ∨ k = 2 := by
      have hr : ((toCore Ux selfParenting_Ux).block 5).round = 1 := rfl
      rw [hr] at hk1; omega
    rcases this with rfl | rfl <;> decide
  hline_creator := by
    intro k hk1 hk2
    have : k = 1 ∨ k = 2 := by
      have hr : ((toCore Ux selfParenting_Ux).block 5).round = 1 := rfl
      rw [hr] at hk1; omega
    rcases this with rfl | rfl <;> decide
  hline_round := by
    intro k hk1 hk2
    have : k = 1 ∨ k = 2 := by
      have hr : ((toCore Ux selfParenting_Ux).block 5).round = 1 := rfl
      rw [hr] at hk1; omega
    rcases this with rfl | rfl <;> decide
  hline_chain := by
    intro k hk1 hk2
    have : k = 2 := by
      have hr : ((toCore Ux selfParenting_Ux).block 5).round = 1 := rfl
      rw [hr] at hk1; omega
    subst this; decide
  hfresh_new := by
    intro k hk
    have : (10 + k) ∈ Ux.ids := hk
    simp only [Ux, Finset.mem_insert, Finset.mem_singleton] at this
    omega
  hidx := by intro k; show 10 + k - 10 = k; omega
  hgap := by
    intro b hb hc h1 h2
    have hb' : b ∈ Ux.ids := hb
    simp only [Ux, Finset.mem_insert, Finset.mem_singleton] at hb'
    rcases hb' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      revert hc h1 h2 <;> decide

/-- What the replica holds after the recovery. -/
abbrev Ufill : LeanDag.Hydrozoan.BlockUniverse (Fin 4) ℕ :=
  skipFillHZ Ux selfParenting_Ux skx

/-! ## And fails after it -/

/-- The filled block sits at round `2` and references the anchor `5`
alongside the donor's references — including `6`, replica `2`'s. -/
theorem fill_block_12 :
    (12 : ℕ) ∈ Ufill.ids ∧ (6 : ℕ) ∈ (Ufill.block 12).parents ∧
      (Ufill.block 12).round = 2 := by decide

/-- **The filled block witnesses the equivocation** that nothing in the
original universe witnessed: the anchor brings one twin, the donor's
reference the other. -/
theorem witness_Ufill : WitnessesAt Ufill 0 2 12 :=
  ⟨2, 4, by decide, by decide, by decide, ⟨5, by decide, by decide⟩,
    ⟨6, by decide, by decide⟩⟩

/-- **So leader exclusion fails after the recovery**, although it held
before it. The filled block references `6`, which replica `2` authored,
while witnessing replica `2` equivocate two rounds below. -/
theorem not_leaderExcludedAll_Ufill : ¬ LeaderExcludedAll Ufill := by
  intro h
  have h6 : (Ufill.block 6).author = 2 := by decide
  exact absurd h6
    (h 12 fill_block_12.1 2 (by decide) witness_Ufill 6 fill_block_12.2.1)

end Integration

end LeanDagTest
