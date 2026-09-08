import LeanDagTest.MahiMahi.Model
import LeanDagTest.MahiMahi.Counting
import LeanDag.MahiMahi.Liveness.Statement
/-!
# Mahi-Mahi witnesses — the clause on data

The unpredictable-leader clause of `Model/Unpredictable.lean` settled on
the two universes of the earlier witnesses (`mahi-mahi.md` §5.3):

* **satisfiable** — on the fully connected `full4`, round-robin satisfies
  both forms of the clause;
* **refutable with a deterministic schedule (MM4a)** — on the aiming
  pattern `aim4`, round-robin violates the single-hit clause: the one
  window that matters names exactly the starved validator;
* **independent of fairness (MM4b)** — the same schedule satisfies the
  core's `FairScheduleOn Correct`, so the clause is not a consequence of
  fairness;
* **the run form is strictly stronger** — on `aim4` the single-hit clause
  with a window of two holds while the run form with runs of two fails;
* **`SpansEligible` on data** — at one leader per round a run of `w` slots
  spans eligibility.

The clause quantifies over every window below the horizon, which is not a
`decide`-able shape; each witness bounds the window index by `omega` on
the unfolded decision round and then decides the finitely many cases.
-/

namespace LeanDagTest

open LeanDag

/-- Round-robin, one leader per round, as in the other witness files. -/
local instance mmSlotsL : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-! ## Satisfiable: `full4` under round-robin -/

-- Every slot of the first two rounds is good at `w = 4` (six rounds reach
-- decision round `4`).
example : MahiMahi.good full4 4 0 = Finset.univ := by decide
example : MahiMahi.good full4 4 1 = Finset.univ := by decide

/-- The single-hit clause with windows of one: the only windows below the
horizon `5` are at `k = 0, 1`. -/
example : MahiMahi.UnpredictableWithin full4 4 1 5 := by
  intro k hk
  have hk' : k ≤ 1 := by
    simp [AnchoredRule.decisionRound, MahiMahi.mahiMahiAnchored] at hk
    omega
  refine ⟨k, le_refl k, by omega, ?_⟩
  interval_cases k <;> decide

/-- The run form with runs of two: the only window below the horizon is
`k = 0`, and slots `0, 1` are both good. -/
example : MahiMahi.UnpredictableRunWithin full4 4 1 2 5 := by
  intro k hk
  have hk' : k = 0 := by
    simp [AnchoredRule.decisionRound, MahiMahi.mahiMahiAnchored] at hk
    omega
  subst hk'
  refine ⟨0, le_refl 0, by omega, ?_⟩
  intro i hi
  interval_cases i <;> decide

/-! ## MM4a: refutable with a deterministic schedule -/

-- On the aiming pattern, the window at `k = 1` contains only slot `1`,
-- whose round-robin leader is the starved validator.
example : (1 : Fin 4) ∉ MahiMahi.good aim4 4 1 := by decide

example : ¬ MahiMahi.UnpredictableWithin aim4 4 1 5 := by
  intro h
  obtain ⟨k', hk1, hk2, hgood⟩ := h 1 (by decide)
  have : k' = 1 := by omega
  subst this
  exact absurd hgood (by decide)

/-! ## MM4b: independent of fairness -/

/-- Round-robin names a correct leader arbitrarily far out — the core's
fairness clause, on the same schedule the clause refutes. -/
example : FairScheduleOn (S := mmSlotsL) (Correct : Finset (Fin 4)) := by
  intro k
  refine ⟨4 * k + 1, by omega, ?_⟩
  have hl : mmSlotsL.leader (4 * k + 1) = (1 : Fin 4) := by
    apply Fin.ext
    simp
  rw [hl]
  decide

/-! ## The run form is strictly stronger -/

-- With windows of two, the only window below the horizon is `k = 0`, and
-- slot `0` is good: the single-hit clause holds on `aim4` ...
example : MahiMahi.UnpredictableWithin aim4 4 2 5 := by
  intro k hk
  have hk' : k = 0 := by
    simp [AnchoredRule.decisionRound, MahiMahi.mahiMahiAnchored] at hk
    omega
  subst hk'
  exact ⟨0, le_refl 0, by omega, by decide⟩

-- ... while a run of two starting in that window needs slot `1`, which is
-- not good: the run form fails.
example : ¬ MahiMahi.UnpredictableRunWithin aim4 4 1 2 5 := by
  intro h
  obtain ⟨k', hk1, hk2, hrun⟩ := h 0 (by decide)
  have : k' = 0 := by omega
  subst this
  exact absurd (hrun 1 (by omega)) (by decide)

/-! ## `SpansEligible` on data -/

/-- At one leader per round, a run of `w` slots spans eligibility: slot
`i < b` has decision round `i + w − 1 < b + w − 1`. -/
example : (MahiMahi.mahiMahiAnchored (Fin 4) (Fin 24) Unit 4).SpansEligible 4 := by
  intro b i hi
  simp [AnchoredRule.Eligible, EligibleAt, MahiMahi.mahiMahiAnchored]
  omega

/-! ## MM3a on data -/

-- A good leader's slot is committed from the full view.
example : (1 : Fin 4) ∈ MahiMahi.good full4 4 1 := by decide
example : MahiMahi.Decided 4 full4 (View.full full4) 1 (some 5) :=
  MahiMahi.Decided.directCommit (by decide) (by decide)

/-! ## Axioms -/

#print axioms aim4

end LeanDagTest
