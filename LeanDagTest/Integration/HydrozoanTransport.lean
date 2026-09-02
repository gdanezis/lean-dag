import LeanDagTest.Integration.HydrozoanUniverse
import LeanDag.Integration.Hydrozoan.Transport

/-!
# The transformer bridge — witnesses

B4 of `docs/hydrozoan-integration.md` §10.4, on the low-fault
four-replica universe `U7` of
`LeanDagTest/Hydrozoan/DirectLiveness.lean` — three rounds, replicas
`{0, 2, 3}` producing at each, replica `1` crashed after genesis — which
`LeanDagTest/Integration/HydrozoanUniverse.lean` shows self-parents.

What is pinned:

* **truncation lands back in Hydrozoan's universe** — `chopHZ U7 _ 1`
  is a Hydrozoan `BlockUniverse`, and its identifiers are `U7`'s above
  the cut, computed;
* **the side condition survives, by the general lemma** — the
  `SelfParenting` of the result is `selfParenting_ofCore` and not an
  argument about `chop`;
* **the rounds are rebased** — a round-`2` block of `U7` is a round-`1`
  block of the truncation.

**What is not instantiated here.** `skipFillHZ` is defined and its side
condition proved for every `SkipMsg`, but no `SkipMsg` is built over
`toCore U7` in this file: the fill's data — an anchor, a gap, and the
verdicts either side of it — is P8's subject, and building it here
would duplicate that. What P6 owes is that the bridge accepts a fill at
all, which its type states and `selfParenting_skipFillHZ` proves.
-/

namespace LeanDagTest

namespace Integration

open LeanDag LeanDag.Integration.Hydrozoan

/-- The truncation of the low-fault universe at horizon `1`. -/
abbrev U7chop : LeanDag.Hydrozoan.BlockUniverse (Fin 4) (Fin 9) :=
  chopHZ LeanDagTest.Hydrozoan.U7 selfParenting_U7 1

/-! ## Truncation lands back in Hydrozoan's universe

The identifiers are `U7`'s at rounds `1` and `2` — the six blocks by
replicas `{0, 2, 3}` above the cut, the three genesis blocks dropped. -/

example : U7chop.ids = {3, 4, 5, 6, 7, 8} := by decide

example : U7chop.ids.card = 6 := by decide

/-! ## The rounds are rebased by the cut -/

example : (U7chop.block 3).round = 0 := by decide
example : (U7chop.block 6).round = 1 := by decide

-- Authors are untouched.
example : (U7chop.block 6).author = (LeanDagTest.Hydrozoan.U7.block 6).author := rfl

/-! ## The side condition survives, and by the general lemma

`selfParenting_chopHZ` is `selfParenting_transport`, which is
`selfParenting_ofCore` — no argument about `chop` appears in it, which
is why a transformer added later costs no `SelfParenting` obligation.
The `decide` below confirms the same fact on data. -/

example : SelfParenting U7chop := selfParenting_chopHZ _ _ _

example : SelfParenting U7chop := by decide

/-! ## And the truncation is itself transportable

Which is what makes the transformers composable: the result of one is
an admissible input to the next. -/

example : SelfParenting (chopHZ U7chop (selfParenting_chopHZ _ _ _) 1) :=
  selfParenting_chopHZ _ _ _

end Integration

end LeanDagTest
