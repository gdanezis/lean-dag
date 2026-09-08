import LeanDag.DoS.Exclusion
import LeanDag.DoS.Counting
/-!
# A model at `f = 2`

`dos-equivocation-and-growth.md` §8. Every other model in
`LeanDagTest` is `f = 1` over `Fin 4`, and by **D10** the blow-up C1′ is about
**does not exist there**: at `f = 1` the layer recurrence is `m_s ≤ 4 + m_{s+1}`,
which is linear. Two equivocators amplifying each other is the smallest setting
in which the question is real, so it needs `f = 2`, `n = 7`.

`Ufault` is the substrate:

```
  round 0   ids 0-6    genesis by validators 0-6
            id  7      a SECOND genesis by validator 0   -- equivocation
            id  8      a SECOND genesis by validator 1   -- equivocation
  round 1   id  9      by 2, refs {0,1,2,3,4}            -- the A branch
            id  10     by 3, refs {7,8,2,3,4}            -- the B branch
            ids 11-13  by 4,5,6, refs {2,3,4,5,6}        -- neither
  round 2   ids 14-18  by 2-6, refs {9,10,11,12,13}      -- the MERGE
  round 3   ids 19-23  by 2-6, refs {14,15,16,17,18}
```

Both Byzantine validators equivocate at round 0, and both are exposed together
at the merge — so from round 2 the **whole fault budget** is spent and caught,
and D15a bites at the bound: the references of every block from round 3 on are
exactly the five correct validators, which is `2f+1` exactly.

This file does not attempt C1′. It builds the substrate and answers the
question raised before doing so — **whether `decide` can carry a model of
this size**, since `ExposedIn` searches a history quadratically and `DoSValid`
ranges over every block and every reference. The answer is recorded below.
-/

namespace LeanDagTest

open LeanDag

/-- Named, because `LeanDagTest.Growth`'s anonymous `Faults (Fin 4)` instance
would otherwise generate the same auto-name and the two files could not be
imported together. -/
instance twoFaults : Faults (Fin 7) where
  f := 2
  byzantine := {0, 1}
  card_validators := by decide
  card_byzantine := by decide

example : (Correct : Finset (Fin 7)) = {2, 3, 4, 5, 6} := by decide

/-- Exactly `2f+1` correct validators: the tight case, where a block that has
caught the whole budget has no choice of references at all. -/
example : (Correct : Finset (Fin 7)).card = (Fintype.card (Fin 7) - Faults.f (Fin 7)) := by decide

def lky : Fin 24 → Block (Fin 7) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 7 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if (i : ℕ) = 8 then
    { round := 0, creator := 1, refs := ∅, payload := () }
  else if (i : ℕ) = 9 then
    { round := 1, creator := 2, refs := {0, 1, 2, 3, 4}, payload := () }
  else if (i : ℕ) = 10 then
    { round := 1, creator := 3, refs := {7, 8, 2, 3, 4}, payload := () }
  else if h : (i : ℕ) < 14 then
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩, refs := {2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) < 19 then
    { round := 2, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := {9, 10, 11, 12, 13}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 17, by have := i.isLt; omega⟩,
      refs := {14, 15, 16, 17, 18}, payload := () }

def Ufault : BlockUniverse (Fin 7) (Fin 24) Unit where
  ids := Finset.univ
  block := lky
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## Two equivocators, caught together -/

-- Validator 0 and validator 1 both equivocate at round 0.
example : (Ufault.block 0).creator = (Ufault.block 7).creator := by decide
example : (Ufault.block 1).creator = (Ufault.block 8).creator := by decide

-- Neither branch alone reveals either of them.
example : ¬ ExposedIn Ufault 9 0 := by decide
example : ¬ ExposedIn Ufault 9 1 := by decide
example : ¬ ExposedIn Ufault 10 0 := by decide
example : ¬ ExposedIn Ufault 10 1 := by decide

-- The merge reveals both at once.
example : ExposedIn Ufault 14 0 := by decide
example : ExposedIn Ufault 14 1 := by decide

set_option maxRecDepth 2048 in
theorem ufault_dosValid : DoSValid Ufault := by decide

/-! ## D15a at the bound, with the budget fully spent

`exposedTo` is the *whole* Byzantine set from round 2 on, so the margin is zero
and `creators_refs_eq_correct` leaves no choice: every block from round 3 must
reference all five correct validators. -/

example : exposedTo Ufault 19 = {0, 1} := by decide
example : (exposedTo Ufault 19).card = Faults.f (Fin 7) := by decide

example : creatorsOf Ufault.block (Ufault.block 19).refs = (Correct : Finset (Fin 7)) :=
  creators_refs_eq_correct ufault_dosValid (by decide) (by decide) (by decide)

/-- And D15b on the same model: the correct blocks of a round are still an
admissible quorum, which is why the DAG can continue at all. -/
example : Fintype.card (Fin 7) - Faults.f (Fin 7) ≤
    (creatorsOf Ufault.block (correctBlocksAt Ufault 2)).card ∧
    ∀ i ∈ correctBlocksAt Ufault 2, (Ufault.block i).creator ∉ exposedTo Ufault 19 :=
  correctBlocksAt_admissible_quorum (by decide) (by decide)

/-! ## The counting results at `f = 2`

D19b is where C1′ has to bite, and the contrast the witness shows is the same
as at `f = 1` but with two authors instead of one: what a block *references*
contributes one per round, and what it does not reference is unconstrained. -/

example : (history Ufault 14).card = 15 := by decide

-- Referenced authors: one block per round, and the bound is attained.
example : ∀ n, (historyBlocksOf Ufault 14 2 n).card ≤ 1 :=
  not_exposedIn_iff_card_le_one.mp (by decide)

-- Unreferenced ones: two blocks at a single round, from both equivocators.
example : (historyBlocksOf Ufault 14 0 0).card = 2 := by decide
example : (historyBlocksOf Ufault 14 1 0).card = 2 := by decide

/-! ## `decide` cost

Everything above settles by `decide` on a 24-block model over `Fin 7`, in about
17 seconds for the file. But `DoSValid` — which walks every block, every
reference, and a quadratic search of each history — **exceeded the default
recursion depth** and needed `maxRecDepth 8000`. At 24 blocks over `Fin 7`, on
histories of at most 15, the approach is already at the edge of its default
budget.

**What that does and does not license.** It says the substrate is checkable; it
says the opposite about a *counterexample*. The whole point of a C1′
counterexample is a history that grows exponentially, `ExposedIn` is quadratic
in exactly that quantity, and `DoSValid` runs it once per block and reference —
so the checking cost grows as roughly the fourth power of the thing being
exhibited, from a starting point that already needs a raised recursion limit.

**So step 11 should not plan to `decide` its way to a refutation.** A
counterexample family will need its validity and its `DoSValid` proved as
theorems, parameterized by depth, in the manner of `Ugrow` rather than of
`Umerge`. That is a different and much larger job, and worth knowing now rather
than after building the model. -/

#print axioms ufault_dosValid

end LeanDagTest
