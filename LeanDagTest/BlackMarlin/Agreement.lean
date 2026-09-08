import LeanDagTest.BlackMarlin.Reactive
import LeanDag.BlackMarlin.Agreement.Proof
/-!
# Black Marlin witnesses — agreement on data

`black-marlin.md` §10. The no-divergence half on the covered four-round
model, where rounds `0` and `1` are committed and round `2` is not — the
DAG stops before its link can be supported — and the local half on the
pace, where the anchor of round `1` is committed by each of the three
reliable validators on its own view.
-/

namespace LeanDagTest

namespace BlackMarlin

open LeanDag LeanDag.BlackMarlin

/-- The rotation of BML5 at four validators, as in the other witnesses. -/
local instance bmRR2 : Rotation (Fin 4) := Liveness.roundRobin 4 (by omega)

/-! ## No divergence, on `Ufull` -/

/-- Rounds `0` and `1` are committed; round `2` is not, its linking
anchor having no round-4 support to draw on. -/
example : CommittedIn Ufull (View.full Ufull) 0 0 ∧ CommittedIn Ufull (View.full Ufull) 5 1 ∧
    ¬ CommittedIn Ufull (View.full Ufull) 10 2 := by decide

/-- **BMA1 on data**: the genesis anchor's delivery is carried by the
round-1 anchor. -/
example : (0 : Fin 16) ∈ history Ufull 5 :=
  (Agreement.holds (Fin 4) (Fin 16) Unit Ufull).1 (View.full Ufull) (View.full Ufull) 0 5 0 0 1
    (by decide) (by decide) (by omega) (by decide)

/-- Anti-vacuity: the two histories are not the same set, so the
containment above has content. -/
example : (3 : Fin 16) ∈ history Ufull 5 ∧ (3 : Fin 16) ∉ history Ufull 0 := by decide

/-! ## The recurring run -/

/-- **BMA4 on data**: round robin at four validators puts a reliably
anchored run of two above every round, with validator `0` Byzantine. -/
example (r : ℕ) : ∃ r', r ≤ r' ∧
    Rotation.anchor (Validator := Fin 4) r' ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) (r' + 1) ∈ (Correct : Finset (Fin 4)) :=
  (Agreement.holds (Fin 4) (Fin 16) Unit Ufull).2.1
    (Correct : Finset (Fin 4)) r (Liveness.holds.2 4 (by omega))

/-! ## The local commit, on the pace -/

/-- **BMA2 on data**: past GST, the anchor of round `1` is committed by
each of validators `1`, `2` and `3` on its own view — not merely
committable over the universe. -/
example (N : ℕ) (hN : 3 ≤ N) :
    ∃ L, IsAnchor (Ugrow N) 1 L ∧ Committed (Ugrow N) L 1 ∧
      ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), CommittedIn (Ugrow N)
        ((ugrowBM N).toPaceCore.viewAt v
          (max ((ugrowBM N).latest 2) ((ugrowBM N).latest 3) + (ugrowBM N).delay)) L 1 :=
  ((Agreement.holds (Fin 4) ℕ Unit (Ugrow N)).2.2 {1, 2, 3} N (ugrowBM N)).1 0 1
    (by decide) (by decide) (le_refl 0)
    (fun n _ => by change 2 * 2 + 7 ≤ 25; omega)
    (Nat.zero_le _) (by omega) (by decide) (by decide)

#print axioms LeanDag.BlackMarlin.Agreement.holds

end BlackMarlin

end LeanDagTest
