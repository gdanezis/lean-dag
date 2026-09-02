import LeanDagTest.Hydrozoan.Decided
import LeanDag.Barnacle.Hydrozoan.Proof
import LeanDag.Barnacle.Model.Window
import LeanDag.Schedule

/-!
# Barnacle over Hydrozoan — the base witnesses

The fifth instantiation, evaluated on a concrete DAG before its
theorems are used, on the five-round seven-replica universe `U3` of
`LeanDagTest/Hydrozoan/Decided.lean` (`f = c = k = 1`, replica `0`
Byzantine and equivocating, replica `1` crashed after genesis; slot `k`
at round `k`, leader `(k + 2) % 7`).

What is pinned:

* **the adapter is faithful** — round, creator and refs of an adapted
  block are the round, author and parents of the original, by `rfl`,
  so the interface reads Hydrozoan's blocks and not a copy of them;
* **the two candidate predicates agree** — the interface's
  `IsLeaderBlock`, computed through the adapter, is Hydrozoan's;
* **the fast route reaches `DirectCommitIn`** — slot `3` fires the
  fast branch at exactly the quorum, and the disjunction is what the
  interface scores, so `SlotDirect` holds there;
* **a skipped slot is not `SlotDirect`** — slot `2` is skipped rather
  than committed, and the window count must not score it;
* **the laws are applied end to end** through `Hydrozoan.holds`, so a
  silently strengthened hypothesis fails the build by arity or type.

Every Hydrozoan name is written out. The witness universe's own
`Slots (Fin 7)` instance is in scope, and so is the rule's namespace;
each statement below fixes the schedule explicitly as `S7`, so nothing
depends on which instance resolution would otherwise pick — the
discipline `docs/hydrozoan-integration.md` §12 records for this arc.
-/

namespace LeanDagTest

namespace Barnacle

open LeanDag

/-- The pipelined schedule of the witness universe, as the interface's
`Slots`: slot `k` at round `k`, led by `(k + 2) % 7`. -/
@[reducible]
def S7 : LeanDag.Slots (Fin 7) :=
  LeanDag.Slots.uniformSingle 1 (by omega) fun k => ⟨(k + 2) % 7, by omega⟩

/-- The rule, at the witness universe's replica and id types. -/
abbrev R7 : LeanDag.Barnacle.BaseRule (Fin 7) (Fin 32) Unit :=
  LeanDag.Barnacle.hydrozoan

/-! ## The adapter is faithful -/

example : (R7.block LeanDagTest.Hydrozoan.U3 24).round
    = (LeanDagTest.Hydrozoan.U3.block 24).round := rfl
example : (R7.block LeanDagTest.Hydrozoan.U3 24).creator
    = (LeanDagTest.Hydrozoan.U3.block 24).author := rfl
example : (R7.block LeanDagTest.Hydrozoan.U3 24).refs
    = (LeanDagTest.Hydrozoan.U3.block 24).parents := rfl

/-! ## The candidate predicates agree, and are decidable through the interface -/

example : R7.IsLeaderBlock S7 LeanDagTest.Hydrozoan.U3 3 24 := by decide
example : ¬ R7.IsLeaderBlock S7 LeanDagTest.Hydrozoan.U3 3 23 := by decide

/-! ## The direct route, and what the window count scores

Slot `3` fast-commits at exactly the quorum, so the disjunction holds
and the slot is `SlotDirect`. Slot `2` is skipped, and neither branch
of the disjunction fires for its candidate — the count must not score a
skip as a commit. -/

example : R7.DirectCommitIn (U := LeanDagTest.Hydrozoan.U3)
    LeanDagTest.Hydrozoan.Vfull3 24 3 := by decide
example : R7.SlotDirect S7 LeanDagTest.Hydrozoan.U3 LeanDagTest.Hydrozoan.Vfull3 3 := by decide
example : ¬ R7.SlotDirect S7 LeanDagTest.Hydrozoan.U3 LeanDagTest.Hydrozoan.Vfull3 2 := by decide

/-! ## The history view, and the law that reads it -/

example (A : Fin 32) (hA : A ∈ LeanDagTest.Hydrozoan.U3.ids) :
    R7.viewIds (R7.historyView LeanDagTest.Hydrozoan.U3 A hA)
      = historyFrom (R7.block LeanDagTest.Hydrozoan.U3) A := rfl

/-! ## The laws, applied end to end -/

/-- The laws at the witness configuration. -/
theorem laws7 : LeanDag.Barnacle.BaseRule.Laws R7 :=
  LeanDag.Barnacle.Hydrozoan.holds (Fin 7) (Fin 32)

-- A fast-committed candidate is a commit verdict, by the law.
example : R7.Decided S7 LeanDagTest.Hydrozoan.Vfull3 3 (some 24) :=
  laws7.decided_of_directCommitIn S7 LeanDagTest.Hydrozoan.Vfull3 3 24 (by decide) (by decide)

-- And a commit verdict is a candidate of its slot, by the law.
example : R7.IsLeaderBlock S7 LeanDagTest.Hydrozoan.U3 3 24 :=
  laws7.candidates S7 LeanDagTest.Hydrozoan.Vfull3 3 24
    (laws7.decided_of_directCommitIn S7 LeanDagTest.Hydrozoan.Vfull3 3 24
      (by decide) (by decide))

-- Agreement across views: no view can disagree with the full view
-- about slot 3.
example (V : R7.View LeanDagTest.Hydrozoan.U3) (v : Option (Fin 32))
    (h : R7.Decided S7 V 3 v) : v = some 24 :=
  laws7.agree S7 V LeanDagTest.Hydrozoan.Vfull3 3 v (some 24) h
    (laws7.decided_of_directCommitIn S7 LeanDagTest.Hydrozoan.Vfull3 3 24
      (by decide) (by decide))

end Barnacle

end LeanDagTest
