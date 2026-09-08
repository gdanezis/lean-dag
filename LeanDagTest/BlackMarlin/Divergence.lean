import LeanDag.BlackMarlin.Model.Recursion
import LeanDag.BlackMarlin.Helpers.Descent
import LeanDag.BlackMarlin.Helpers.Ledger
import LeanDag.BlackMarlin.Helpers.Order
import Mathlib.Tactic.IntervalCases
/-!
# Black Marlin — two honest parties, two different blocks

A universe on which one validator outputs a Byzantine anchor's block `8`
and another outputs its twin `12`, and neither ever outputs the other.
That is Definition 1's **Agreement** refuted for the protocol as
specified (`black-marlin.md` §13).

Four validators, `0` Byzantine, seven rounds; ids run in production
order, with round `2` carrying five blocks because validator `0`
equivocates there. The rotation anchors rounds `0` to `6` by
`3, 3, 0, 1, 2, 3, 1`.

The construction turns on three facts, each settled by `decide` below.

* Block `8` is **committed by the rule**: three round-3 blocks reference
  it, and the round-3 anchor `14` both references it and carries three
  supporters. Its twin `12` is supported by one validator only, so BM1 is
  not contradicted.
* The round-4 anchor `19` **omits `14`** from its references — legal, a
  block needs `n − f = 3` of `4`, and a correct validator that has not
  yet received `14` will do exactly this. Its cone therefore holds no
  round-3 anchor, so a descent arriving at `19` skips round `3` and
  faces both twins at round `2`.
* The tie-break of L24 prefers `12`: `8` omits the round-1 anchor from
  its own references and `12` includes it, so `12` is one round from the
  highest anchor of its cone and `8` is two.

A validator that committed `8` at round `2` flushes it then. One whose
view at `delivery(4)` lacked `17`, `18` and `20` saw `14` unsupported,
so the attempt failed; the protocol never retries a round, so it commits
`19` at round `6` instead and its descent takes `12`.

**No timing hypothesis is needed.** Agreement is a safety property, which
the paper states holds during asynchrony as well, and asynchrony is
exactly the freedom to delay those three blocks to the second validator.
Every block below references only blocks of the round beneath it that
its author could have held, and each honest one carries every block of
that round it holds, as L46–L48 require.
-/

namespace LeanDagTest

namespace BlackMarlin

set_option maxRecDepth 2048

open LeanDag LeanDag.BlackMarlin

/-- Four validators, `0` Byzantine — the committee the construction runs
on, declared here now that the arc is the rule and this refutation. -/
local instance divFaults : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

/-- The rotation: rounds `0` to `6` anchored by `3, 3, 0, 1, 2, 3, 1`.
Round `2` is anchored by the Byzantine validator. -/
local instance divRot : Rotation (Fin 4) where
  anchor r := match r with
    | 0 => 3 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 1 | _ => 0

/-- The blocks. Id order is production order, so references always carry
smaller identifiers. -/
def divBlk : Fin 29 → Block (Fin 4) (Fin 29) Unit := fun i =>
  { round :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => 0
      | 4 | 5 | 6 | 7 => 1
      | 8 | 9 | 10 | 11 | 12 => 2
      | 13 | 14 | 15 | 16 => 3
      | 17 | 18 | 19 | 20 => 4
      | 21 | 22 | 23 | 24 => 5
      | _ => 6,
    creator :=
      match (i : ℕ) with
      | 0 | 4 | 8 | 12 | 13 | 17 | 21 | 25 => 0
      | 1 | 5 | 9 | 14 | 18 | 22 | 26 => 1
      | 2 | 6 | 10 | 15 | 19 | 23 | 27 => 2
      | _ => 3,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => ∅
      | 4 => {0, 1, 2} | 5 => {0, 1, 2} | 6 => {1, 2, 3} | 7 => {1, 2, 3}
      | 8 => {4, 5, 6} | 9 => {4, 5, 6} | 10 => {4, 5, 6} | 11 => {5, 6, 7}
      | 12 => {4, 6, 7}
      | 13 => {9, 10, 12} | 14 => {8, 9, 10} | 15 => {8, 9, 10} | 16 => {8, 9, 11}
      | 17 => {13, 14, 15} | 18 => {13, 14, 15} | 19 => {13, 15, 16}
      | 20 => {14, 15, 16}
      | 21 => {17, 18, 19} | 22 => {17, 18, 19} | 23 => {17, 18, 19}
      | 24 => {18, 19, 20}
      | 25 => {21, 22, 23} | 26 => {22, 23, 24} | 27 => {22, 23, 24}
      | _ => {22, 23, 24},
    payload := () }

/-- The universe: valid, and equivocating only at the Byzantine
validator. -/
def Udiv : BlockUniverse (Fin 4) (Fin 29) Unit where
  ids := Finset.univ
  block := divBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The equivocation, and what the rule admits -/

/-- Blocks `8` and `12` are twins: both anchor round `2`, both by the
Byzantine validator. -/
example : IsAnchor Udiv 2 8 ∧ IsAnchor Udiv 2 12 ∧ (8 : Fin 29) ≠ 12 ∧
    (Udiv.block 8).creator ∉ (Correct : Finset (Fin 4)) := by decide

/-- **The rule commits `8`** — and only `8`: its twin carries one
supporter, so anchor uniqueness is not contradicted. -/
example : Committed Udiv 8 2 ∧ ¬ Supported Udiv 12 2 := by decide

/-- The round-4 anchor omits the round-3 anchor, so its cone holds no
anchor of round `3` and a descent arriving there skips the round. -/
example : IsAnchor Udiv 4 19 ∧ (14 : Fin 29) ∉ (Udiv.block 19).refs ∧
    coneAnchors Udiv 19 3 = ∅ := by decide

/-- And the round-4 anchor is itself committed, so a validator that
missed round `2` still commits later. -/
example : Committed Udiv 19 4 := by decide

/-! ## The descent parts the two -/

/-- Both twins are candidates below the round-4 anchor, and the metric of
L24 prefers `12`. -/
example : maxAnchor Udiv (strongOf Udiv 19) = {8, 12} ∧
    anchorGap Udiv 12 = 1 ∧ anchorGap Udiv 8 = 2 := by decide

/-- Both metrics are readings of a real anchor rather than of an absent
one: each twin's cone holds an anchor, so L24 compares two defined
quantities and the preference for `12` does not rest on how the empty
case is read. -/
example : (anchorsOf Udiv (strongOf Udiv 8)).Nonempty ∧
    (anchorsOf Udiv (strongOf Udiv 12)).Nonempty ∧
    maxAnchorRound Udiv (strongOf Udiv 8) = 0 ∧
    maxAnchorRound Udiv (strongOf Udiv 12) = 1 := by decide

/-- And neither twin lies in the other's cone, so which twin a validator
flushes at round `2` is settled by the record alone — no property of the
sort `τ` enters. -/
example : (8 : Fin 29) ∉ history Udiv 12 ∧ (12 : Fin 29) ∉ history Udiv 8 := by decide

/-- **The records disagree at round `2`.** The validator that committed
`8` flushed `8`; the descent from the round-4 anchor takes `12`. -/
example : flushRecord Udiv 8 2 = some 8 ∧ flushRecord Udiv 19 2 = some 12 := by decide

/-! ## And so the two output different blocks

Identifiers run downward along references here too, so sorting by
identifier is a topological sort. -/

example : ∀ b : Fin 29, ∀ j ∈ (Udiv.block b).refs, j < b := by decide

/-- The sort of this model. -/
def divSort : TopoSort Udiv := TopoSort.ofFinOrder Udiv (by decide)

/-- The record of the validator that committed `8` at round `2`. -/
def vFlush : Flush Udiv := toFlush Udiv 8 (by decide) (by decide)

/-- The record of the validator that missed round `2` and committed the
round-4 anchor at round `6` instead. -/
def wFlush : Flush Udiv := toFlush Udiv 19 (by decide) (by decide)

example : wFlush.block 4 = some 19 ∧ wFlush.block 3 = none ∧
    wFlush.block 2 = some 12 ∧ wFlush.block 1 = some 7 ∧
    wFlush.block 0 = some 3 := by decide

/-- **Definition 1's Agreement, refuted.** The first validator outputs
`8` and never `12`; the second outputs `12` and never `8`. Both are
honest, both follow the rules, and the filter of L27 bars each from ever
emitting the other's block, since a block of that author and round has
already gone out. -/
example :
    (8 : Fin 29) ∈ deliverSeq Udiv vFlush divSort 3 ∧
    (12 : Fin 29) ∉ deliverSeq Udiv vFlush divSort 3 ∧
    (12 : Fin 29) ∈ deliverSeq Udiv wFlush divSort 5 ∧
    (8 : Fin 29) ∉ deliverSeq Udiv wFlush divSort 5 := by decide

/-- The second validator does flush `8` — it is in the round-4 anchor's
cone — and drops it only at the filter. So the divergence is not a
missing block but a **different choice of twin**. -/
example : (8 : Fin 29) ∈ ledgerSeq Udiv wFlush divSort 5 ∧
    key Udiv 8 = key Udiv 12 := by decide

/-- **The dilemma.** Both twins are flushed by the second validator, and
they carry one author-and-round between them, so L27 must drop one:
emitting both would output two blocks for a single `(party, round)`,
which Definition 1's Integrity forbids "at most once regardless of `B`".
It drops `8` — the block the first validator has already output. So the
execution admits no reading that satisfies both properties: filter, and
Agreement fails; do not filter, and Integrity does. -/
example : key Udiv 8 = key Udiv 12 ∧
    (8 : Fin 29) ∈ ledgerSeq Udiv wFlush divSort 5 ∧
    (12 : Fin 29) ∈ ledgerSeq Udiv wFlush divSort 5 ∧
    (8 : Fin 29) ∉ deliverSeq Udiv wFlush divSort 5 ∧
    (12 : Fin 29) ∈ deliverSeq Udiv wFlush divSort 5 := by decide

/-- Nothing above contradicts safety of the rule: the two records agree
wherever both flush a committed anchor, and `12` is not one. -/
example : ¬ Committed Udiv 12 2 := by decide


/-! ## Total order fails, and on blocks of reliable authors

The refutation above is of Agreement, and turns on which twin each
record delivers. The delivered **sequence** fails for a reason that does
not involve the twins at all. Blocks `5` and `7` are authored by
reliable validators, neither has a twin, and L27's filter never touches
either — yet the first validator delivers `5` before `7` and the second
`7` before `5`. What orders them is which segment they fall in: `5` lies
below `8` and `7` below `12`, so each record takes one of them in its
round-2 segment and the other only in the round-4 segment.

So Definition 1's **Total order** fails independently of which twin the
filter prefers, and no rule for choosing among twins repairs it. Only a
rule that makes the two descents agree does, which is `descendS`. This
is the tightness of BMT3: one Byzantine anchor below is enough. -/

/-- The first validator's record over both its commits: `8` at round `2`,
then the round-4 anchor. -/
def vBlockFull : ℕ → Option (Fin 29)
  | 2 => some 8
  | 4 => some 19
  | _ => none

def vFlushFull : Flush Udiv where
  block := vBlockFull
  isAnchor := by
    intro ρ L h
    match ρ with
    | 2 | 4 => simp only [vBlockFull, Option.some.injEq] at h; subst h; decide
    | 0 | 1 | 3 | (n + 5) => simp [vBlockFull] at h
  step := by
    intro ρ L M hL hM
    match ρ with
    | 2 | 4 => simp [vBlockFull] at hM
    | 0 | 1 | 3 | (n + 5) => simp [vBlockFull] at hL
  dense := by
    intro ρ M hM hne
    match ρ with
    | 1 =>
      simp only [vBlockFull, Option.some.injEq] at hM
      subst hM
      exact absurd hne (by decide)
    | 3 =>
      simp only [vBlockFull, Option.some.injEq] at hM
      subst hM
      exact absurd hne (by decide)
    | 0 | 2 | (n + 4) => simp [vBlockFull] at hM

/-- **Two reliable authors' blocks, delivered in opposite orders.** -/
example : (Udiv.block 5).creator ∈ (Correct : Finset (Fin 4)) ∧
    (Udiv.block 7).creator ∈ (Correct : Finset (Fin 4)) ∧
    (deliverSeq Udiv vFlushFull divSort 5).idxOf 5 <
      (deliverSeq Udiv vFlushFull divSort 5).idxOf 7 ∧
    (deliverSeq Udiv wFlush divSort 5).idxOf 7 <
      (deliverSeq Udiv wFlush divSort 5).idxOf 5 := by decide

/-- And neither is a twin: each is the only block of its author and
round, so the filter has no choice to make about them. -/
example : (∀ b ∈ Udiv.ids, (Udiv.block b).creator = (Udiv.block 5).creator →
      (Udiv.block b).round = (Udiv.block 5).round → b = 5) ∧
    (∀ b ∈ Udiv.ids, (Udiv.block b).creator = (Udiv.block 7).creator →
      (Udiv.block b).round = (Udiv.block 7).round → b = 7) := by decide

/-! ## The same two validators, under Algorithm 1 itself

`Flush` records the boundaries a validator flushed as a function of
round, and `ledgerSeq` reads them off in round order. Algorithm 1 runs
`commit(B)` afresh at each successful `delivery(r)`, threading `D`
across invocations, so a later commit can descend below a boundary an
earlier one passed and emit those blocks *after* blocks of a higher
round. `commitSeq` writes that recursion out, and the two validators of
this execution are run through it below.

The first commits `8` at `delivery(4)` and `19` at `delivery(6)`; the
second, lacking `17`, `18` and `20`, fails `delivery(4)` and commits
`19` at `delivery(6)` alone. -/

/-- What the first validator `ab-deliver`s, across both its commits. -/
def vRec : List (Fin 29) :=
  let a := commitSeq Udiv divSort 10 8 ∅
  a.1 ++ (commitSeq Udiv divSort 10 19 a.2).1

/-- And what the second does. -/
def wRec : List (Fin 29) := (commitSeq Udiv divSort 10 19 ∅).1

/-- **The inversion, under the algorithm as written.** -/
example : vRec = [3, 0, 1, 2, 4, 5, 6, 8, 7, 9, 10, 11, 13, 15, 16, 19] ∧
    wRec = [3, 1, 2, 7, 0, 4, 6, 12, 5, 9, 10, 11, 13, 15, 16, 19] ∧
    vRec.idxOf 5 < vRec.idxOf 7 ∧ wRec.idxOf 7 < wRec.idxOf 5 := by decide

/-- And the Agreement failure with it: each delivers one twin only. -/
example : (8 : Fin 29) ∈ vRec ∧ (12 : Fin 29) ∉ vRec ∧
    (12 : Fin 29) ∈ wRec ∧ (8 : Fin 29) ∉ wRec := by decide

/-- **The record abstraction, checked against the recursion.** The second
validator's `Flush` reproduces its output exactly. The first's differs in
one position and no more: the round-0 anchor `3` is flushed as its own
segment at `delivery(4)`, which a record with no round-0 boundary emits
inside the round-2 segment instead. The pair the order turns on is
unaffected. -/
example : deliverSeq Udiv wFlush divSort 5 = wRec ∧
    deliverSeq Udiv vFlushFull divSort 5 =
      [0, 1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11, 13, 15, 16, 19] ∧
    (deliverSeq Udiv vFlushFull divSort 5).filter (fun b => b ≠ 3) =
      vRec.filter (fun b => b ≠ 3) := by decide

end BlackMarlin

end LeanDagTest
