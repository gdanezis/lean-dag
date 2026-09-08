import LeanDagTest.Mysticeti.Model
import LeanDag.MahiMahi.Model.Decision
/-!
# Mahi-Mahi witnesses — the rule at wave `w` on data

Every definition of `LeanDag/MahiMahi/Model/` settled by `decide` on
four-validator universes before anything is proved from it
(`mahi-mahi.md` §8). Three witnesses:

* `full4` — six fully connected rounds: the rules fire, at `w = 4` and
  `w = 5`, and the wave arithmetic is what the record says it is;
* `twin4` — a Byzantine leader's two twins both in one voter's cone: the
  minimality clause of `Votes` picks exactly one, and without it both
  would be candidates — the configuration canonical support exists for
  (`mahi-mahi.md` §2);
* `w3` — at `w = 3` the rules agree with the core's on `full4`
  (conservativity MM1d, on data, ahead of its proof).

The committee is the standard witness one, validator `0` Byzantine and
`f = 1` (`LeanDagTest/Model.lean`), so the quorum is `3`. The schedule is
local to this file: `Fin 4` carries other `Slots` instances elsewhere in
the test library, and a second global one would make resolution
ambiguous.
-/

namespace LeanDagTest

open LeanDag

/-- Round-robin, one leader per round: slot `k` at round `k`, led by
`k % 4`. Built through `uniformSingle`, so the class obligations are
discharged once in `Schedule.lean`. -/
local instance mmSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-! ## `full4` — six rounds, everyone referencing the whole round below -/

/-- Block `4m + v` is validator `v`'s round-`m` block; every non-genesis
block references all four blocks of the round below. -/
def mmFullBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩,
      refs := {0, 1, 2, 3}, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩,
      refs := {4, 5, 6, 7}, payload := () }
  else if h : (i : ℕ) < 16 then
    { round := 3, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := {8, 9, 10, 11}, payload := () }
  else if h : (i : ℕ) < 20 then
    { round := 4, creator := ⟨(i : ℕ) - 16, by omega⟩,
      refs := {12, 13, 14, 15}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 20, by have := i.isLt; omega⟩,
      refs := {16, 17, 18, 19}, payload := () }

/-- The fully connected universe: the existing `BlockUniverse` accepts it
unchanged, which is the reuse claim of `mahi-mahi.md` §0. -/
def full4 : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := mmFullBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ### The wave arithmetic -/

-- At `w = 4` a round-`1` candidate is voted on at round `3` and decided at
-- round `4`; at `w = 3` the rounds are the core's `r + 1`, `r + 2`.
example : MahiMahi.votingRound 4 1 = 3 := by decide
example : MahiMahi.decisionRoundAt 4 1 = 4 := by decide
example : MahiMahi.votingRound 3 1 = 2 := by decide
example : MahiMahi.decisionRoundAt 3 1 = 3 := by decide
example : (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 4).decisionRound 1 = 4 := by decide
example : (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 5).decisionRound 1 = 5 := by decide

-- Slot `5` may anchor slot `1` at `w = 4`; slot `4` may not.
example : (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 4).Eligible 1 5 := by decide
example : ¬ (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 4).Eligible 1 4 := by decide

/-! ### Support through the cone -/

-- The round-`2` block of validator `0` (id `8`) has exactly one block of
-- author `1` at round `0` in its cone, and votes for it.
example : MahiMahi.candidatesAt full4 8 1 0 = {1} := by decide
example : MahiMahi.Votes full4 8 1 := by decide
example : ¬ MahiMahi.Blames full4 8 1 0 := by decide

-- A block votes for nothing above its own round, and blames a slot no
-- block of the universe occupies at its round.
example : ¬ MahiMahi.Votes full4 8 12 := by decide
example : MahiMahi.candidatesAt full4 8 1 3 = ∅ := by decide

/-! ### Certificates and the direct rules at `w = 4` and `w = 5` -/

-- Slot `1`'s candidate is block `5` (round `1`, author `1`).
example : IsLeaderBlock full4 1 5 := by decide

-- At `w = 4` its voting round is `3`: every round-`3` block votes for it,
-- every round-`4` block certifies it, and it is directly committed.
example : MahiMahi.votesIn full4 16 5 = {12, 13, 14, 15} := by decide
example : MahiMahi.Certifies full4 16 5 := by decide
example : MahiMahi.certificates full4 4 5 1 = {16, 17, 18, 19} := by decide
example : MahiMahi.DirectCommit full4 4 5 1 := by decide
example : ¬ MahiMahi.DirectSkip full4 4 1 1 := by decide
example : MahiMahi.blamers full4 4 1 1 = ∅ := by decide

-- At `w = 5` the decision round is `5`, and the rule fires there too.
example : MahiMahi.certificates full4 5 5 1 = {20, 21, 22, 23} := by decide
example : MahiMahi.DirectCommit full4 5 5 1 := by decide

/-! ### The decision relation -/

-- Direct commit of slot `1` at `w = 4`, from the full view.
example : MahiMahi.Decided 4 full4 (View.full full4) 1 (some 5) :=
  MahiMahi.Decided.directCommit (by decide) (by decide)

-- And at `w = 5`.
example : MahiMahi.Decided 5 full4 (View.full full4) 1 (some 5) :=
  MahiMahi.Decided.directCommit (by decide) (by decide)

-- The indirect test on data: block `20` (round `5`) reaches certificate
-- `16` for slot `1` at `w = 4`.
example : MahiMahi.CertifiedIn full4 4 20 5 1 :=
  ⟨16, by decide, Reaches.single (by decide)⟩

/-! ## `twin4` — two twins in one cone -/

/-- Round `0`: blocks `0`–`3` by validators `0`–`3`, and block `4`, a
second round-`0` block by the Byzantine validator `0`. Round `1`:
validator `1` (block `5`) references twin `0`, validator `2` (block `6`)
references twin `4`, validator `3` (block `7`) references neither. Round
`2`: validator `1`'s block `8` references all three, so both twins lie in
its cone. -/
def mmTwinBlk : Fin 9 → Block (Fin 4) (Fin 9) Unit := fun i =>
  match i with
  | 0 => { round := 0, creator := 0, refs := ∅, payload := () }
  | 1 => { round := 0, creator := 1, refs := ∅, payload := () }
  | 2 => { round := 0, creator := 2, refs := ∅, payload := () }
  | 3 => { round := 0, creator := 3, refs := ∅, payload := () }
  | 4 => { round := 0, creator := 0, refs := ∅, payload := () }
  | 5 => { round := 1, creator := 1, refs := {0, 1, 2}, payload := () }
  | 6 => { round := 1, creator := 2, refs := {4, 1, 2}, payload := () }
  | 7 => { round := 1, creator := 3, refs := {1, 2, 3}, payload := () }
  | 8 => { round := 2, creator := 1, refs := {5, 6, 7}, payload := () }

/-- A valid universe: the twins are the Byzantine validator's, so
`no_equivocation` is not violated. -/
def twin4 : BlockUniverse (Fin 4) (Fin 9) Unit where
  ids := Finset.univ
  block := mmTwinBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Both twins are candidates at `(0, 0)` in block `8`'s cone …
example : MahiMahi.candidatesAt twin4 8 0 0 = {0, 4} := by decide

-- … and the vote goes to the least, and to the least only.
example : MahiMahi.Votes twin4 8 0 := by decide
example : ¬ MahiMahi.Votes twin4 8 4 := by decide

-- Without the minimality clause both would be voted for: the membership
-- half of `Votes` holds of each twin. This is the configuration
-- canonical support exists to arbitrate.
example : 4 ∈ MahiMahi.candidatesAt twin4 8 0 0 ∧
    0 ∈ MahiMahi.candidatesAt twin4 8 0 0 := by decide

-- Validator `3`'s round-`1` block reaches no twin, and blames the slot.
example : MahiMahi.Blames twin4 7 0 0 := by decide

/-! ## `w3` — conservativity on data -/

-- At `w = 3` the rules agree with the core's on `full4`, at the slots
-- the six rounds reach: both directions of MM1d, by `decide`.
example : MahiMahi.DirectCommit full4 3 5 1 ↔ LeanDag.DirectCommit full4 5 1 := by decide
example : MahiMahi.DirectCommit full4 3 1 0 ↔ LeanDag.DirectCommit full4 1 0 := by decide
example : MahiMahi.DirectCommit full4 3 10 2 ↔ LeanDag.DirectCommit full4 10 2 := by decide
example : MahiMahi.DirectSkip full4 3 1 1 ↔ LeanDag.DirectSkip full4 5 1 := by decide
example : MahiMahi.certificates full4 3 5 1 = LeanDag.certificates full4 5 1 := by decide
example : MahiMahi.votesIn full4 12 5 = LeanDag.votesIn full4 12 5 := by decide
example : (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 3).Eligible 1 4 ↔
    (LeanDag.coreAnchored (Fin 4) (Fin 24) Unit).Eligible 1 4 := by decide
example : ¬ (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 3).Eligible 1 3 ∧
    ¬ (LeanDag.coreAnchored (Fin 4) (Fin 24) Unit).Eligible 1 3 := by decide

-- The same verdict on slot `1` from both relations.
example : MahiMahi.Decided 3 full4 (View.full full4) 1 (some 5) :=
  MahiMahi.Decided.directCommit (by decide) (by decide)
example : LeanDag.Decided full4 (View.full full4) 1 (some 5) :=
  LeanDag.Decided.directCommit (by decide) (by decide)

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms full4
#print axioms twin4

end LeanDagTest
