import LeanDagTest.BlackMarlin.Agreement
import LeanDag.BlackMarlin.Ledger.Proof
import LeanDag.BlackMarlin.Descent.Proof
import LeanDag.BlackMarlin.Order.Proof
import Mathlib.Tactic.IntervalCases

/-!
# Black Marlin witnesses — the delivered order on data

`black-marlin.md` §11. The covered four-round model carries a flush
record — the four anchors of rounds `0` to `3` — and on it the descent's
candidate sets are singletons, which is BMD1 on data. `OutputAt` then
places a block at the round it enters the ledger at, and the anti-vacuity
is that it does not enter earlier.
-/

namespace LeanDagTest

namespace BlackMarlin

open LeanDag LeanDag.BlackMarlin

/-- The rotation of BML5 at four validators, as in the other witnesses. -/
local instance bmRR3 : Rotation (Fin 4) := Liveness.roundRobin 4 (by omega)

/-! ## The descent has one candidate at each step -/

example : coneAnchors Ufull 5 0 = {0} := by decide
example : coneAnchors Ufull 10 1 = {5} := by decide
example : coneAnchors Ufull 15 2 = {10} := by decide

/-- Anti-vacuity: a cone two rounds deep is not a singleton by accident —
it holds the round-0 anchor as well, which is why the step matters. -/
example : (0 : Fin 16) ∈ coneAnchors Ufull 10 0 := by decide

/-- **BMD1′ on data**: at a round whose anchor is reliable the candidates
are a singleton however deep the cone — here validator `2` anchors round
`2` and is not Byzantine, so the round-3 anchor's cone holds exactly one
of its blocks. -/
example : ∀ X ∈ coneAnchors Ufull 15 2, ∀ Y ∈ coneAnchors Ufull 15 2, X = Y :=
  fun X hX Y hY =>
    (Ledger.holds (Fin 4) (Fin 16) Unit Ufull).2.1 2 15 X Y (by decide) hX hY

/-- The Byzantine validator is `0`, which anchors round `0`; that is the
only round of this model where a tie could arise at all. -/
example : Rotation.anchor (Validator := Fin 4) 0 ∉ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 1 ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 2 ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 3 ∈ (Correct : Finset (Fin 4)) := by decide

/-! ## The record -/

/-- The anchor of round `ρ` is validator `ρ % 4`, whose block at that
round is id `4 * ρ + ρ % 4`; the model stops at round `3`. -/
def fullBlock : ℕ → Option (Fin 16)
  | 0 => some 0
  | 1 => some 5
  | 2 => some 10
  | 3 => some 15
  | _ => none

/-- The flush record of the covered four-round model. -/
def fullFlush : Flush Ufull where
  block := fullBlock
  isAnchor := by
    intro ρ L h
    match ρ with
    | 0 | 1 | 2 | 3 => simp only [fullBlock, Option.some.injEq] at h; subst h; decide
    | (n + 4) => simp [fullBlock] at h
  step := by
    intro ρ L M hL hM
    match ρ with
    | 0 | 1 | 2 =>
        simp only [fullBlock, Option.some.injEq] at hL hM
        subst hL; subst hM; decide
    | 3 => simp [fullBlock] at hM
    | (n + 4) => simp [fullBlock] at hL
  dense := by
    intro ρ M hM _
    match ρ with
    | 0 | 1 | 2 => decide
    | 3 => simp [fullBlock] at hM
    | (n + 4) => simp [fullBlock] at hM

example : fullFlush.block 0 = some 0 ∧ fullFlush.block 1 = some 5 ∧
    fullFlush.block 2 = some 10 ∧ fullFlush.block 3 = some 15 ∧
    fullFlush.block 4 = none := by decide

/-! ## The ledger -/

/-- **BMD6 on data**: validator `3`'s genesis block enters the ledger at
round `1`, with the round-1 anchor — the first flushed anchor whose cone
holds it. -/
example : OutputAt Ufull fullFlush.block 3 1 := by
  refine ⟨⟨5, by decide, (mem_history_iff (by decide)).mp (by decide)⟩, ?_⟩
  intro σ hσ L hL hr
  have hσ0 : σ = 0 := by omega
  subst hσ0
  have : L = 0 := by
    have : fullFlush.block 0 = some 0 := by decide
    rw [this] at hL
    exact (Option.some.inj hL).symm
  subst this
  exact absurd ((mem_history_iff (by decide)).mpr hr) (by decide)

/-- And so it is in the ledger from round `2` on, but not before. -/
example : (3 : Fin 16) ∈ ledgerSet Ufull fullFlush.block 2 :=
  (Ledger.holds (Fin 4) (Fin 16) Unit Ufull).2.2.2.2.2.2.2.2.2.2
    fullFlush 1 5 3 (by decide) ((mem_history_iff (by decide)).mp (by decide))

/-! ## The descent computed

`flushRecord` runs L21–L24 rather than assuming a record, so the four
anchors above are what it returns. -/

example : flushRecord Ufull 15 3 = some 15 ∧ flushRecord Ufull 15 2 = some 10 ∧
    flushRecord Ufull 15 1 = some 5 ∧ flushRecord Ufull 15 0 = some 0 := by decide

/-- The computed record is the one built by hand. -/
example : flushRecord Ufull 15 0 = fullFlush.block 0 ∧
    flushRecord Ufull 15 1 = fullFlush.block 1 ∧
    flushRecord Ufull 15 2 = fullFlush.block 2 ∧
    flushRecord Ufull 15 3 = fullFlush.block 3 ∧
    flushRecord Ufull 15 4 = fullFlush.block 4 := by decide

/-- **BME5 on data**: the descent from the round-3 anchor and the descent
from the round-1 anchor meet at round `1`, so they agree at round `0` —
with no hypothesis about what lies between. -/
example : flushRecord Ufull 15 0 = flushRecord Ufull 5 0 :=
  (Descent.holds (Fin 4) (Fin 16) Unit Ufull).2.2.2.2 15 5 5 1 0
    (by decide) (by decide) (by decide) (by decide) (by omega)

#print axioms LeanDag.BlackMarlin.Descent.holds

/-! ## The delivered sequence

Identifiers of this model run downward along references — a block of
round `r` has id `4r + j` and references round `r − 1` — so sorting by
identifier is a topological sort, and `TopoSort` is not vacuous. -/

example : ∀ b : Fin 16, ∀ j ∈ (Ufull.block b).refs, j < b := by decide

/-- The sort of the covered four-round model. -/
def fullSort : TopoSort Ufull := TopoSort.ofFinOrder Ufull (by decide)

/-- **The list a validator outputs.** One segment per anchor round, each
sorted, each anchor last in its own segment: `[0]`, then `[1,2,3,5]`,
then `[4,6,7,10]`, then `[8,9,11,15]`. -/
example : deliverSeq Ufull fullFlush fullSort 4 =
    [0, 1, 2, 3, 5, 4, 6, 7, 10, 8, 9, 11, 15] := by decide

/-- Anti-vacuity: the round-3 blocks that no committed anchor reaches are
not output. -/
example : (12 : Fin 16) ∉ deliverSeq Ufull fullFlush fullSort 4 ∧
    (13 : Fin 16) ∉ deliverSeq Ufull fullFlush fullSort 4 := by decide

/-- **BMO4 on data**: no author-and-round appears twice. -/
example : (deliverSeq Ufull fullFlush fullSort 4).Pairwise
    (fun a b => key Ufull a ≠ key Ufull b) :=
  ((Order.holds (Fin 4) (Fin 16) Unit Ufull).2.2.2.1 fullFlush fullSort 4).1

/-- **BMO3 on data**: the list through round `2` is a prefix of the list
through round `4`. -/
example : deliverSeq Ufull fullFlush fullSort 2 <+: deliverSeq Ufull fullFlush fullSort 4 :=
  (Order.holds (Fin 4) (Fin 16) Unit Ufull).2.2.1 fullFlush fullSort 2 4 (by omega)

/-- **BMO6 on data**: validator `3`'s genesis block is output, by itself
rather than by a twin — validator `3` is not Byzantine here. -/
example : (3 : Fin 16) ∈ deliverSeq Ufull fullFlush fullSort 4 :=
  (Order.holds (Fin 4) (Fin 16) Unit Ufull).2.2.2.2.2.1 fullFlush fullSort 4 3
    (by decide) (by decide)

#print axioms LeanDag.BlackMarlin.Order.holds

#print axioms LeanDag.BlackMarlin.Ledger.holds

end BlackMarlin

end LeanDagTest
