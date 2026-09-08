import LeanDagTest.BlackMarlin.Model
import LeanDag.BlackMarlin.Liveness.Proof
/-!
# Black Marlin witnesses — liveness on data

`black-marlin.md` §8. Figure 1 is a *safety* witness and cannot serve
here: its point is that validator `0` omits the round-3 anchor from its
round-4 block, which is exactly a failure of coverage, and `decide`
exhibits the omission below. So liveness runs on a second universe —
four rounds, every block referencing the whole round beneath it — where
coverage holds from round `0` and each claim is instantiated through
`Liveness.holds` itself.

The rotation is `roundRobin 4`, the one BML5 is stated about, and the
committee is the standard witness one with validator `0` Byzantine
(`LeanDagTest/Model.lean`). The reliable anchors therefore start at round
`1`: rounds `1` and `2` are the run of two, and round `3` supplies the
support that closes the link.
-/

namespace LeanDagTest

namespace BlackMarlin

open LeanDag LeanDag.BlackMarlin

/-- The rotation of BML5 at four validators. -/
local instance bmRR : Rotation (Fin 4) := Liveness.roundRobin 4 (by omega)

/-! ## Why Figure 1 will not do

Coverage among the reliable validators fails there: block `5` is a
reliable author's round-1 block, block `3` is a reliable author's
round-0 block, and the first does not reference the second. -/

example : (5 : Fin 24) ∈ Ubm.ids ∧ (Ubm.block 5).creator ∈ (Correct : Finset (Fin 4)) ∧
    (3 : Fin 24) ∈ Ubm.ids ∧ (Ubm.block 3).creator ∈ (Correct : Finset (Fin 4)) ∧
    (Ubm.block 3).round + 1 = (Ubm.block 5).round ∧
    (3 : Fin 24) ∉ (Ubm.block 5).refs := by decide

/-! ## The covered universe

Id `i` sits at round `i / 4` and is authored by validator `i % 4`; every
block references the whole round beneath it. -/

def bmFullBlk : Fin 16 → Block (Fin 4) (Fin 16) Unit := fun i =>
  { round := (i : ℕ) / 4,
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩,
    refs :=
      match (i : ℕ) / 4 with
      | 0 => ∅
      | 1 => {0, 1, 2, 3}
      | 2 => {4, 5, 6, 7}
      | _ => {8, 9, 10, 11},
    payload := () }

/-- Four fully connected rounds. -/
def Ufull : BlockUniverse (Fin 4) (Fin 16) Unit where
  ids := Finset.univ
  block := bmFullBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- Population at a Byzantine universe is decidable; the global instance
is declared where the denial-of-service arc first needed it
(`DoS/Exclusion.lean`), which this file has no other reason to import. -/
local instance decidablePopulatedOnFull (T : Finset (Fin 4)) (r : ℕ) :
    Decidable (PopulatedOn Ufull T r) :=
  inferInstanceAs (Decidable (PopulatedFrom Ufull.block Ufull.ids T r))

/-- Every validator authors at every round up to the horizon. -/
theorem ufull_populated {r : ℕ} (h : r ≤ 3) : Populated Ufull r := by
  interval_cases r <;> decide

/-- Anti-vacuity: the horizon is real. -/
example : ¬ Populated Ufull 4 := by decide

private theorem ufull_round_le : ∀ b : Fin 16, (Ufull.block b).round ≤ 3 := by decide

/-- Coverage among the reliable validators, from round `0`. -/
theorem ufull_synchronised : Synchronised Ufull 0 := by
  intro n _ b hb hbr hbc a ha har hac
  by_cases hn : n ≤ 2
  · revert b hb hbr hbc a ha har hac
    interval_cases n <;> decide
  · exfalso
    have := ufull_round_le b
    omega

/-! ## The anchors of the rotation

`roundRobin 4` anchors round `r` by validator `r % 4`, so round `0` is
anchored by the Byzantine validator and rounds `1` and `2` are the run
of two the rule needs. -/

example : IsAnchor Ufull 1 5 ∧ IsAnchor Ufull 2 10 ∧ IsAnchor Ufull 3 15 := by decide

example : Rotation.anchor (Validator := Fin 4) 1 ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 2 ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 0 ∉ (Correct : Finset (Fin 4)) := by decide

/-! ## The results, on this universe -/

/-- **BML1 on data.** Rounds `1` and `2` are reliably anchored and rounds
`1`, `2`, `3` are populated, so round `1` has a committed anchor —
derived from `Liveness.holds`, not restated. -/
example : ∃ L, IsAnchor Ufull 1 L ∧ Committed Ufull L 1 :=
  (Liveness.holds.1 (Fin 4) (Fin 16) Unit Ufull).1 (Correct : Finset (Fin 4)) 0 1
    card_correct ufull_synchronised (by omega)
    (ufull_populated (by omega)) (ufull_populated (by omega))
    (ufull_populated (by omega)) (by decide) (by decide)

/-- And the anchor it commits is block `5`, which `decide` confirms
directly — so the existential above is not satisfied by some other
block. -/
example : Committed Ufull 5 1 := by decide

/-- **BML2 on data**: the full view reaches the same verdict. -/
example : CommittedIn Ufull (View.full Ufull) 5 1 :=
  ((Liveness.holds.1 (Fin 4) (Fin 16) Unit Ufull).2.1 5 1).mpr (by decide)

/-- **BML3 on data**: validator `3`'s round-0 block lies in what the
round-2 anchor delivers. -/
example : (3 : Fin 16) ∈ history Ufull 10 :=
  (Liveness.holds.1 (Fin 4) (Fin 16) Unit Ufull).2.2.1 (Correct : Finset (Fin 4)) 0 0 3 10
    card_correct ufull_synchronised (by omega) (ufull_populated (by omega))
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Anti-vacuity: causal history is not everything. A round-1 block is
not delivered by a round-0 block. -/
example : (4 : Fin 16) ∉ history Ufull 3 := by decide

/-- **BML5 on data**: round-robin at four validators supplies the run of
two, with validator `0` Byzantine. -/
example : Liveness.FairRun (Rot := Liveness.roundRobin 4 (by omega))
    (Correct : Finset (Fin 4)) 2 :=
  Liveness.holds.2 4 (by omega)

#print axioms LeanDag.BlackMarlin.Liveness.holds

end BlackMarlin

end LeanDagTest
