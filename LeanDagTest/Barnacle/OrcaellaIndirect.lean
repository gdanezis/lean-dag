import LeanDagTest.Hybrid.Model
import LeanDagTest.Barnacle.Rules.Orcaella.Proof
/-!
# Barnacle over Orcaella — the indirect rule, witnessed

No hybrid universe in the repo exercised the indirect rule at an
*admissible* threshold (the only indirect derivations lived at the
one-short committee, where no threshold is admissible). Two models fix
that, and both route through the arc's `Descent.indirect` with the
verdict pinned by `agree`.

**`U5` — both ends of a non-tight interval, behaviourally distinct.**
`fb = 0, fc = 1, n = 5` is the repo's first committee with slack: the
admissible interval is `[kTight, kRel] = [2, 3]`. Nobody actually
crashes (the caps are upper bounds), so five validators author every
round, and round-`2` blocks — which must cite a quorum of four — can
*omit* the slot-`1` leader block `6`. The split is two supporters
against three blamers: neither direct rule fires at quorum `4`, the
anchor `18` (slot `3`) commits directly, and its cone holds exactly the
two supporters. So the **same DAG** commits `6` at threshold `2` and
skips it at threshold `3` — the interval's ends disagree on data, which
is what makes the threshold a real parameter.

**`UhybX` — the twins, at the genuinely mixed committee.** The tight
`n = 9` model of `LeanDagTest/Hybrid.lean` extended to five rounds,
with the schedule electing the Byzantine validator `0` at slot `1`: its
round-`1` twins `16` and `17` are both candidates, each with exactly
four cone supporters at the anchor `27` — `distinct_creators` caps a
block at one twin, so the eight round-`2` authors split four against
four. Both pass the indirect test at the (only) admissible threshold
`4`, neither direct rule fires, and the canonicity clause commits the
**least** twin and refuses the greater — the hybrid mirror of the
Odontoceti twin witness, on a DAG where a validator has also crashed.
This model also carries the first `Good` at `fb, fc > 0`: the original
two-round `Uhyb9` fails synchrony (block `10` omits block `7`) and is
too short for any anchor.
-/

namespace LeanDagTest

namespace Barnacle

namespace OrcaellaIndirect

set_option maxRecDepth 2048

open LeanDag LeanDag.Barnacle LeanDag.Hybrid

/-! ## `U5` — the slack committee and its split -/

instance hyb5 : HybridFaults (Fin 5) where
  fb := 0
  fc := 1
  byzantine := ∅
  crash := {4}
  disjoint := by decide
  card_byzantine := by decide
  card_crash := by decide
  card_validators := by decide

-- The first non-singleton admissible interval in the development.
example : Hybrid.q (Fin 5) = 4 := by decide
example : kTight (Fin 5) = 2 := by decide
example : kRel (Fin 5) = 3 := by decide
example : Admissible (Fin 5) 2 ∧ Admissible (Fin 5) 3 := by decide
example : ¬ Admissible (Fin 5) 1 := by decide
example : ¬ Admissible (Fin 5) 4 := by decide

/-- Five full lines — the crash-prone validator `4` never halts. Round
`2` splits on the slot-`1` leader block `6`: authors `1` (self-parent)
and `2` cite it, authors `0`, `3`, `4` omit it. Rounds `3` and `4`
anchor slot `3` and commit it. -/
def blk5 : Fin 25 → Block (Fin 5) (Fin 25) Unit := fun i =>
  if h : (i : ℕ) < 5 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 10 then
    { round := 1, creator := ⟨(i : ℕ) - 5, by omega⟩,
      refs := {0, 1, 2, 3, 4}, payload := () }
  else if h : (i : ℕ) < 15 then
    { round := 2, creator := ⟨(i : ℕ) - 10, by omega⟩,
      refs := if (i : ℕ) = 11 then {5, 6, 7, 8}
        else if (i : ℕ) = 12 then {6, 7, 8, 9}
        else {5, 7, 8, 9}, payload := () }
  else if h : (i : ℕ) < 20 then
    { round := 3, creator := ⟨(i : ℕ) - 15, by omega⟩,
      refs := if (i : ℕ) < 18 then {10, 11, 12, 13} else {11, 12, 13, 14}, payload := () }
  else
    { round := 4, creator := ⟨(i : ℕ) - 20, by have := i.isLt; omega⟩,
      refs := if (i : ℕ) < 24 then {15, 16, 17, 18} else {16, 17, 18, 19}, payload := () }

def U5 : BlockUniverse (Fin 5) (Fin 25) Unit where
  ids := Finset.univ
  block := blk5
  complete := by decide
  valid := by decide
  no_equivocation := by decide

instance hyb5Slots : Slots (Fin 5) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 5, by omega⟩)

abbrev bn5 : BaseRule (Fin 5) (Fin 25) Unit := orcaella 2
abbrev bn5' : BaseRule (Fin 5) (Fin 25) Unit := orcaella 3

/-- The subtype universe — nobody equivocates at all. -/
def O5 : {U : BlockUniverse (Fin 5) (Fin 25) Unit // HonestNoEquiv U} := ⟨U5, by decide⟩

-- Slot 1 (leader 1, block 6, the only candidate): two supporters, three
-- blamers — neither direct rule at quorum 4.
example : IsLeaderBlock U5 1 6 := by decide
example : ∀ M : Fin 25, IsLeaderBlock U5 1 M → M = 6 := by decide
example : (supporters U5 6 2 : Finset (Fin 5)) = {1, 2} := by decide
example : ¬ Hybrid.DirectCommitIn U5 (View.full U5) 6 1 := by decide
example : ¬ Hybrid.DirectSkipIn U5 (View.full U5) 6 1 := by decide

-- Slot 3 (leader 3, block 18): committed directly, whatever the
-- threshold — the anchor.
example : IsLeaderBlock U5 3 18 := by decide
example : Hybrid.DirectCommitIn U5 (View.full U5) 18 3 := by decide

-- The cone holds exactly the two supporters: thick at 2, thin at 3.
example : (Hybrid.coneSupports U5 18 6 1 : Finset (Fin 5)) = {1, 2} := by decide
example : Hybrid.ThickLink 2 U5 18 6 1 ∧ ¬ Hybrid.ThickLink 3 U5 18 6 1 := by decide

/-- The anchor, decided by hand at either threshold. -/
theorem u5_slot3 (k : ℕ) : Hybrid.Decided k U5 (View.full U5) 3 (some 18) :=
  Decided.directCommit (by decide) (by show Hybrid.DirectCommitIn _ _ _ _; decide)

/-- At threshold `2` the indirect rule **commits** slot `1`. -/
theorem u5_commit : Hybrid.Decided 2 U5 (View.full U5) 1 (some 6) := by
  refine Decided.indirectCommit (i := 0) (by omega) (by decide) (u5_slot3 2) ?_ (by decide)
    (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 2 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro L' hL' ht' hlt
    have hall : ∀ M : Fin 25, IsLeaderBlock U5 1 M → M = 6 := by decide
    have := hall L' hL'
    subst this
    exact absurd (show (6 : Fin 25) < 6 from hlt) (lt_irrefl _)

/-- At threshold `3` the same DAG **skips** it. -/
theorem u5_skip : Hybrid.Decided 3 U5 (View.full U5) 1 none := by
  refine Decided.indirectSkip (by omega) (by decide) (u5_slot3 3) ?_ ?_
  · intro i h1 h2 h3
    have : i = 2 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 25, IsLeaderBlock U5 1 M → M = 6 := by decide
    have := hall L hL
    subst this
    show ¬ Hybrid.ThickLink _ _ _ _ _
    decide

/-- The arc's `indirect` law at threshold `2`, verdict pinned by
`agree`: the commit. -/
theorem u5_indirect_commit :
    ∃ v, bn5.Decided hyb5Slots (bn5.full O5) 1 v ∧ v = some 6 := by
  obtain ⟨v, hv⟩ :=
    (LeanDag.Barnacle.Orcaella.holds.2.1 (Fin 5) (Fin 25) Unit 2 (by decide)).indirect
      hyb5Slots (bn5.full O5) 1 3 18 (by decide) (u5_slot3 2)
      (fun i' h1 h2 h3 => by
        have : i' = 2 := by omega
        subst this
        exact absurd h3 (by decide))
  exact ⟨v, hv, (LeanDag.Barnacle.Orcaella.holds.1 (Fin 5) (Fin 25) Unit 2 (by decide)).agree
    hyb5Slots _ _ 1 v (some 6) hv u5_commit⟩

/-- The arc's `indirect` law at threshold `3`, verdict pinned by
`agree`: the skip — the interval's ends disagree on one DAG. -/
theorem u5_indirect_skip :
    ∃ v, bn5'.Decided hyb5Slots (bn5'.full O5) 1 v ∧ v = none := by
  obtain ⟨v, hv⟩ :=
    (LeanDag.Barnacle.Orcaella.holds.2.1 (Fin 5) (Fin 25) Unit 3 (by decide)).indirect
      hyb5Slots (bn5'.full O5) 1 3 18 (by decide) (u5_slot3 3)
      (fun i' h1 h2 h3 => by
        have : i' = 2 := by omega
        subst this
        exact absurd h3 (by decide))
  exact ⟨v, hv, (LeanDag.Barnacle.Orcaella.holds.1 (Fin 5) (Fin 25) Unit 3 (by decide)).agree
    hyb5Slots _ _ 1 v none hv u5_skip⟩

/-! ## `UhybX` — the twins at the mixed committee -/

/-- The tight mixed committee's DAG, five rounds: genesis from all
nine; the Byzantine `0` produces twins `16`/`17` at round `1`;
validator `8` has crashed. Round `2` splits four-against-four on the
twins (`distinct_creators` caps a block at one twin; `0`'s own round-`2`
block `25` sides with `17`). The anchor `27` (slot `3`, leader `2`)
cites everything and commits on round `4`. -/
def blkX : Fin 40 → Block (Fin 9) (Fin 40) Unit := fun i =>
  if h : (i : ℕ) < 9 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 16 then
    { round := 1, creator := ⟨(i : ℕ) - 8, by omega⟩,
      refs := {1, 2, 3, 4, 5, 6, 7}, payload := () }
  else if h : (i : ℕ) = 16 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) = 17 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4, 5, 7}, payload := () }
  else if h : (i : ℕ) < 25 then
    { round := 2, creator := ⟨(i : ℕ) - 17, by omega⟩,
      refs := if (i : ℕ) < 22 then {9, 10, 11, 12, 13, 14, 15, 16}
        else {9, 10, 11, 12, 13, 14, 15, 17}, payload := () }
  else if h : (i : ℕ) = 25 then
    { round := 2, creator := 0, refs := {9, 10, 11, 12, 13, 14, 15, 17}, payload := () }
  else if h : (i : ℕ) < 33 then
    { round := 3, creator := ⟨(i : ℕ) - 25, by omega⟩,
      refs := if (i : ℕ) = 27 then {18, 19, 20, 21, 22, 23, 24, 25}
        else {18, 19, 20, 21, 22, 23, 24}, payload := () }
  else
    { round := 4, creator := ⟨(i : ℕ) - 32, by have := i.isLt; omega⟩,
      refs := {26, 27, 28, 29, 30, 31, 32}, payload := () }

def UhybX : BlockUniverse (Fin 9) (Fin 40) Unit where
  ids := Finset.univ
  block := blkX
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The schedule electing the Byzantine validator at slot `1`: leader
`(κ + 8) % 9`. -/
instance (priority := high) x9Slots : Slots (Fin 9) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 8) % 9, by omega⟩)

abbrev bnX : BaseRule (Fin 9) (Fin 40) Unit := orcaella 4

/-- The subtype universe: the only twins are the Byzantine
validator's. -/
def OX : bnX.Universe := ⟨UhybX, by decide⟩

-- Slot 1's candidates are exactly the twins; neither direct rule fires
-- on either.
example : IsLeaderBlock UhybX 1 16 ∧ IsLeaderBlock UhybX 1 17 := by decide
example : ∀ M : Fin 40, IsLeaderBlock UhybX 1 M → M = 16 ∨ M = 17 := by decide
example : ¬ Hybrid.DirectCommitIn UhybX (View.full UhybX) 16 1 := by decide
example : ¬ Hybrid.DirectSkipIn UhybX (View.full UhybX) 16 1 := by decide
example : ¬ Hybrid.DirectCommitIn UhybX (View.full UhybX) 17 1 := by decide
example : ¬ Hybrid.DirectSkipIn UhybX (View.full UhybX) 17 1 := by decide

-- The anchor: slot 3, leader 2, block 27, committed directly.
example : IsLeaderBlock UhybX 3 27 := by decide
example : Hybrid.DirectCommitIn UhybX (View.full UhybX) 27 3 := by decide

/-- **Both twins pass at the anchor**, four cone supporters each — the
canonicity clause is not decorative at the mixed committee. -/
theorem x9_both_pass :
    (Hybrid.coneSupports UhybX 27 16 1 : Finset (Fin 9)) = {1, 2, 3, 4} ∧
    (Hybrid.coneSupports UhybX 27 17 1 : Finset (Fin 9)) = {5, 6, 7, 0} ∧
    Hybrid.ThickLink 4 UhybX 27 16 1 ∧ Hybrid.ThickLink 4 UhybX 27 17 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The first `Good` at `fb, fc > 0`: the fully-correct class `{1, …, 7}`
carries the quorum `7`, synchronised from genesis and populating all
five rounds. -/
theorem x9_good :
    (orcaellaLive (Validator := Fin 9) (BlockId := Fin 40) (Payload := Unit) 4).Good
      OX 0 4 := by
  refine ⟨{1, 2, 3, 4, 5, 6, 7}, ⟨by decide, by decide⟩, ?_, fun r h1 h2 => by
    interval_cases r <;> decide⟩
  change SynchronisedOn UhybX {1, 2, 3, 4, 5, 6, 7} 0
  intro n hn b hb hround hbT a ha hround' haT
  have h4 : ∀ b : Fin 40, (UhybX.block b).round ≤ 4 := by decide
  have hn3 : n ≤ 3 := by have := h4 b; omega
  interval_cases n <;> revert b a <;> decide

/-- The anchor and the least twin, by hand. -/
theorem x9_slot3 : Hybrid.Decided 4 UhybX (View.full UhybX) 3 (some 27) :=
  Decided.directCommit (by decide) (by decide)

theorem x9_slot1 : Hybrid.Decided 4 UhybX (View.full UhybX) 1 (some 16) := by
  refine Decided.indirectCommit (i := 0) (by omega) (by decide) x9_slot3 ?_ (by decide)
    (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 2 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro L' hL' ht' hlt
    have hall : ∀ M : Fin 40, IsLeaderBlock UhybX 1 M → M = 16 ∨ M = 17 := by decide
    rcases hall L' hL' with h | h <;> subst h
    · exact absurd (show (16 : Fin 40) < 16 from hlt) (lt_irrefl _)
    · exact absurd (show (17 : Fin 40) < 16 from hlt) (by decide)

/-- The arc's `indirect` law commits the **least** twin and refuses the
greater — canonicity at the mixed committee, through `agree`. -/
theorem x9_least :
    (∃ v, bnX.Decided x9Slots (bnX.full OX) 1 v ∧ v = some 16) ∧
      ¬ bnX.Decided x9Slots (bnX.full OX) 1 (some 17) := by
  obtain ⟨v, hv⟩ :=
    (LeanDag.Barnacle.Orcaella.holds.2.1 (Fin 9) (Fin 40) Unit 4 (by decide)).indirect
      x9Slots (bnX.full OX) 1 3 27 (by decide) x9_slot3
      (fun i' h1 h2 h3 => by
        have : i' = 2 := by omega
        subst this
        exact absurd h3 (by decide))
  refine ⟨⟨v, hv, (LeanDag.Barnacle.Orcaella.holds.1 (Fin 9) (Fin 40) Unit 4 (by decide)).agree
    x9Slots _ _ 1 v (some 16) hv x9_slot1⟩, fun h => ?_⟩
  have := (LeanDag.Barnacle.Orcaella.holds.1 (Fin 9) (Fin 40) Unit 4 (by decide)).agree
    x9Slots _ _ 1 _ _ h x9_slot1
  simp at this

#print axioms u5_indirect_commit
#print axioms u5_indirect_skip
#print axioms x9_least

end OrcaellaIndirect

end Barnacle

end LeanDagTest
