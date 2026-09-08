import LeanDag.DoS.Pedigree
import LeanDag.DoS.Density
/-!
# The doubling step, machine-checked

`dos-equivocation-and-growth.md` §5. The claim under test: the nesting
mechanism behind the `2^e` family — an *exposed* helper author whose several
chains each carry a fresh chain of the doubled author to a different
gatherer — is realisable by **valid** blocks. This file settles it by
`decide` on a concrete universe.

The objection it answers: Byzantine validators cannot forge correct blocks
and cannot advance rounds alone. The construction respects both. Every
Byzantine block references seven *real* correct blocks of the immediately
preceding round (the quorum), and the correct validators — `9 = 2f+1` of
them at `β = f = 4` — advance rounds entirely among themselves, never
referencing anything Byzantine. Visibility is one-way: Byzantine nodes
receive the correct broadcasts and build alongside; correct nodes receive
nothing Byzantine until the reveal.

`f = 4`, validators `Fin 13`, Byzantine `{0,1,2,3}` in four roles:
validator 1 (`A₂`) is *doubled*, validator 2 (`A₃`) is the exposed helper,
validators 0 and 3 are unexposed scaffolds.

```
round 0  ids 0-12   genesis, one per validator
         ids 13-15  THREE more geneses by validator 1     -- four A₂-chains
         id  16     a second genesis by validator 2       -- two A₃-chains
round 1  ids 17-25  correct r1, refs = all 9 correct geneses
         id  26     by 0: refs {0, 1} + 7 correct         -- scaffold N adopts chain 1ᵃ
         id  27     by 2: refs {2, 13} + 7 correct        -- helper chain A carries 1ᵇ
         id  28     by 3: refs {3, 14} + 7 correct        -- scaffold M adopts chain 1ᶜ
         id  29     by 2: refs {16, 15} + 7 correct       -- helper chain B carries 1ᵈ
round 2  ids 30-38  correct r2, refs = all 9 correct r1
         id  39     by 0: refs {26, 27} + 7 correct r1    -- N swallows helper chain A
         id  40     by 3: refs {28, 29} + 7 correct r1    -- M swallows helper chain B
round 3  id  41     by 0: refs {39, 40} + 7 correct r2    -- the reveal
```

Block 39 is the crux: it *names* validator 2 (via 27) and is clean about it
— its cone holds helper chain A only, because branch M is elsewhere — while
being exposed to validator 1 (chains `1ᵃ` and `1ᵇ`), which it lawfully does
not reference. Block 41 gathers everything: **four chains of validator 1**,
two of validator 2, all under `DoSValid`, with `exposedTo = {1, 2}`.

Pedigrees of the four `A₂`-tops, in the anchored sense:
`1ᵃ → N` and `1ᶜ → M` (empty intermediates), `1ᵇ → helper A → N` and
`1ᵈ → helper B → M` (intermediate author list `[2]`). Four distinct
(anchor, list) pairs — the `(3f+1-e)·2^(e-1)` shape, attained.
-/

namespace LeanDagTest

open LeanDag

instance doubleFaults : Faults (Fin 13) where
  f := 4
  byzantine := {0, 1, 2, 3}
  card_validators := by decide
  card_byzantine := by decide

def lkd : Fin 42 → Block (Fin 13) (Fin 42) Unit := fun i =>
  if h : (i : ℕ) < 13 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) < 16 then
    { round := 0, creator := 1, refs := ∅, payload := () }
  else if (i : ℕ) = 16 then
    { round := 0, creator := 2, refs := ∅, payload := () }
  else if h : (i : ℕ) < 26 then
    { round := 1, creator := ⟨(i : ℕ) - 13, by omega⟩,
      refs := {4, 5, 6, 7, 8, 9, 10, 11, 12}, payload := () }
  else if (i : ℕ) = 26 then
    { round := 1, creator := 0, refs := {0, 1, 4, 5, 6, 7, 8, 9, 10}, payload := () }
  else if (i : ℕ) = 27 then
    { round := 1, creator := 2, refs := {2, 13, 4, 5, 6, 7, 8, 9, 10}, payload := () }
  else if (i : ℕ) = 28 then
    { round := 1, creator := 3, refs := {3, 14, 4, 5, 6, 7, 8, 9, 10}, payload := () }
  else if (i : ℕ) = 29 then
    { round := 1, creator := 2, refs := {16, 15, 4, 5, 6, 7, 8, 9, 10}, payload := () }
  else if h : (i : ℕ) < 39 then
    { round := 2, creator := ⟨(i : ℕ) - 26, by omega⟩,
      refs := {17, 18, 19, 20, 21, 22, 23, 24, 25}, payload := () }
  else if (i : ℕ) = 39 then
    { round := 2, creator := 0, refs := {26, 27, 17, 18, 19, 20, 21, 22, 23}, payload := () }
  else if (i : ℕ) = 40 then
    { round := 2, creator := 3, refs := {28, 29, 17, 18, 19, 20, 21, 22, 23}, payload := () }
  else
    { round := 3, creator := 0, refs := {39, 40, 30, 31, 32, 33, 34, 35, 36}, payload := () }

set_option maxRecDepth 4096 in
def Udouble : BlockUniverse (Fin 13) (Fin 42) Unit where
  ids := Finset.univ
  block := lkd
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## Every constraint, machine-checked -/

set_option maxRecDepth 4096 in
theorem udouble_dosValid : DoSValid Udouble := by decide

-- Byzantine blocks parasitize real correct blocks: the crux block 39
-- references seven correct round-1 blocks, exactly as the quorum demands.
example : (Fintype.card (Fin 13) - Faults.f (Fin 13)) ≤
    (creatorsOf Udouble.block (Udouble.block 39).refs).card := by decide

-- The correct validators never reference anything Byzantine, and advance
-- rounds among themselves: 9 = 2f+1 exactly.
example : (Correct : Finset (Fin 13)).card = (Fintype.card (Fin 13) - Faults.f (Fin 13)) := by decide
example : ∀ i ∈ Udouble.ids, (Udouble.block i).creator ∈ (Correct : Finset (Fin 13)) →
    ∀ j ∈ (Udouble.block i).refs, (Udouble.block j).creator ∈ (Correct : Finset (Fin 13)) := by
  decide

/-! ## The doubling, delivered -/

set_option maxRecDepth 4096 in
/-- **Four chains of validator 1** in one history. -/
theorem udouble_four_chains : topsOf Udouble 41 1 = {1, 13, 14, 15} := by decide

set_option maxRecDepth 4096 in
theorem udouble_exposed : exposedTo Udouble 41 = {1, 2} := by decide

-- The crux: block 39 names the helper (validator 2) and is CLEAN about it —
-- its cone holds helper chain A only — while lawfully exposed to validator 1.
set_option maxRecDepth 4096 in
example : ¬ ExposedIn Udouble 39 2 := by decide
set_option maxRecDepth 4096 in
example : ExposedIn Udouble 39 1 := by decide
set_option maxRecDepth 4096 in
example : ExposedIn Udouble 40 1 ∧ ¬ ExposedIn Udouble 40 2 := by decide

-- The helper IS exposed at the reveal: its two chains met only in block 41.
set_option maxRecDepth 4096 in
example : ExposedIn Udouble 41 2 := by decide

set_option maxRecDepth 4096 in
theorem udouble_exposed_one : ExposedIn Udouble 41 1 := by decide

/-- The proved ceiling `(3f+1-e)·e^(e-1) = 11·2 = 22` against the attained
`4 = 2^e` — the doubling step is real, and it is what keeps the bound
exponential in `e`. -/
example : (topsOf Udouble 41 1).card ≤
    (Fintype.card (Fin 13) - (exposedTo Udouble 41).card) *
      (exposedTo Udouble 41).card ^ ((exposedTo Udouble 41).erase 1).card :=
  card_topsOf_le_of_exposed udouble_dosValid (by decide) udouble_exposed_one

set_option maxRecDepth 4096 in
example : (topsOf Udouble 41 1).card = 4 := by decide

/-! ## Density, honoured throughout -/

set_option maxRecDepth 4096 in
/-- Even the reveal block misses at most `f` correct validators per round —
here it misses exactly `2` at rounds 1 and 2 (validators 11 and 12, whose
round-1 and round-2 blocks the Byzantine branch never referenced). -/
example : (missingAt Udouble 41 1).card ≤ Faults.f (Fin 13) ∧
    (missingAt Udouble 41 2).card ≤ Faults.f (Fin 13) := by decide

set_option maxRecDepth 4096 in
example : missingAt Udouble 41 2 = {11, 12} := by decide

#print axioms udouble_dosValid
#print axioms udouble_four_chains

end LeanDagTest
