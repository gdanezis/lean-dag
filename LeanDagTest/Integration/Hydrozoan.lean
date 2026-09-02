import LeanDagTest.Hydrozoan.DirectRules
import LeanDag.Integration.Hydrozoan.Faults
import LeanDag.Integration.Hydrozoan.Schedule

/-!
# The Hydrozoan bridges — witnesses

B1 and B2 of `docs/hydrozoan-integration.md` §10, evaluated before
anything rests on them, on the seven-replica model of
`LeanDagTest/Hydrozoan/Model.lean` (`f = c = k = 1`) and its pipelined
schedule.

What is pinned:

* **the projection computes** — the derived `HybridFaults` fields are
  Hydrozoan's, and the three diamond agreements hold on data;
* **the committee condition restricts** — `c ≤ k` holds at seven
  replicas and fails at the five-replica configuration of
  `LeanDagTest/Hydrozoan/Grounding.lean`, where Hydrozoan's committee
  bound still holds and the hybrid one does not, so the `Fact` is not a
  formality;
* **the schedule identification is pointwise** — the induced
  `LeanDag.Slots` agrees with Hydrozoan's at every slot.

The two arithmetic refutations are stated on the numbers rather than
through a second `Faults` instance, so that no competing instance for
one replica type enters this file — the discipline
`docs/hydrozoan-integration.md` §12 records.
-/

namespace LeanDagTest

namespace Integration

open LeanDag LeanDag.Integration.Hydrozoan

/-- The committee condition at the seven-replica model, which is what
makes the projection available there. -/
instance factSeven : Fact (HybridCommittee (Fin 7)) := ⟨by decide⟩

/-! ## B1 — the projection computes -/

example : HybridFaults.fb (Fin 7) = 1 ∧ HybridFaults.fc (Fin 7) = 1 := by
  constructor <;> rfl

example : (HybridFaults.byzantine : Finset (Fin 7)) = {0} := rfl
example : (HybridFaults.crash : Finset (Fin 7)) = {1} := rfl

/-! ## B1 — the diamond agreements, on data

`q = n − f − c = 5` at this configuration, and the core's quorum is the
same number by a different route. -/

example : LeanDag.Hydrozoan.q (Fin 7) = 5 := by decide

example : quorumCard (Fin 7) = LeanDag.Hydrozoan.q (Fin 7) := quorumCard_eq_q

example : (Correct : Finset (Fin 7))
    = (LeanDag.Hydrozoan.Correct : Finset (Fin 7)) := correct_eq

example : ((HybridFaults.byzantine : Finset (Fin 7)))ᶜ
    = (LeanDag.Hydrozoan.NonByzantine : Finset (Fin 7)) := nonByzantine_eq

-- And the pools are what the model says: replica 0 Byzantine, 1 crashed.
example : (LeanDag.Hydrozoan.Correct : Finset (Fin 7)) = {2, 3, 4, 5, 6} := by decide

/-! ## B1 — the committee condition is a real restriction

At `n = 5`, `f = 0`, `c = 2`, `k = 0` — the configuration
`LeanDagTest/Hydrozoan/Grounding.lean` uses for the per-slot-rotation
contrast — Hydrozoan's committee bound holds and the hybrid one does
not, so no `HybridFaults` instance is derivable there. Stated on the
numbers, so that no second `Faults (Fin 5)` enters this file. -/

example : 3 * 0 + 2 * 2 + 0 + 1 ≤ 5 := by decide
example : ¬ (3 * (0 + 2) + 1 ≤ 5) := by decide

-- And the eight-replica instance §2 of the record names.
example : 3 * 1 + 2 * 2 + 0 + 1 ≤ 8 := by decide
example : ¬ (3 * (1 + 2) + 1 ≤ 8) := by decide

-- The committee bound is the hypothesis, and it is strictly weaker than
-- the slack condition `c ≤ k`: at `n = 20`, `f = 1`, `c = 2`, `k = 0`
-- the projection is available and the slack condition fails, so stating
-- the bound admits configurations stating the slack would refuse.
example : 3 * (1 + 2) + 1 ≤ 20 := by decide
example : ¬ ((2 : ℕ) ≤ 0) := by decide

-- The seven-replica model satisfies the bound exactly.
example : HybridCommittee (Fin 7) := by decide
example : LeanDag.Hydrozoan.Faults.c (Fin 7) ≤ LeanDag.Hydrozoan.Faults.k (Fin 7) := by decide

/-! ## B2 — the schedule identification is pointwise

The pipelined schedule of `LeanDagTest/Hydrozoan/DirectRules.lean`:
slot `k` at round `k`, led by `(k + 2) % 7`. -/

example (k : ℕ) : LeanDag.Slots.slotRound (Fin 7) k
    = LeanDag.Hydrozoan.Slots.slotRound (Fin 7) k := slotRound_eq k

example (k : ℕ) : LeanDag.Slots.leader (Validator := Fin 7) k
    = LeanDag.Hydrozoan.Slots.leader (Replica := Fin 7) k := leader_eq k

example : LeanDag.Slots.slotRound (Fin 7) 3 = 3 := by decide
example : LeanDag.Slots.leader (Validator := Fin 7) 3 = 5 := by decide

/-! ## B2 — the schedule predicates coincide -/

example (k j : ℕ) : LeanDag.Eligible (Fin 7) k j
    ↔ LeanDag.Hydrozoan.EligibleAsAnchor (Fin 7) k j := eligible_eq k j

example (T : Finset (Fin 7)) (c : ℕ) : LeanDag.FairRunOn T c
    ↔ LeanDag.Hydrozoan.EventualDecision.FairRunOn (Fin 7) T c := fairRunOn_eq T c

example (c : ℕ) : LeanDag.SpansEligible (Validator := Fin 7) c
    ↔ LeanDag.Hydrozoan.IndirectLiveness.SpansEligible (Fin 7) c := spansEligible_eq c

-- Eligibility itself is decidable at a slot pair, and the runway under
-- the pipelined schedule is three rounds: slot 0 is anchored by slot 3
-- and not by slot 2.
example : LeanDag.Eligible (Fin 7) 0 3 := by decide
example : ¬ LeanDag.Eligible (Fin 7) 0 2 := by decide

end Integration

end LeanDagTest
