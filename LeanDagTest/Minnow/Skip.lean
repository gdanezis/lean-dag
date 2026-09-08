import LeanDag.Minnow.Blocking
import LeanDagTest.Mysticeti.Model
/-!
# Minnow — the skip clause, counted as written, contradicts the quorum

`minnow.md` §4. Definition 9's escape reads "there are `2f + 1` vertices
that do not have an edge to `v′`". **Vertices**, where the quorum clause
counts processes: "a set `Q` of `2f + 1` vertices issued by distinct
processes".

A round holds `n = 3f + 1` vertices only while nobody equivocates. A
faulty process may issue several, and section 2 of the paper says correct processes hold them
all. Its extra vertices then count towards the skip total without costing
it a place in the quorum, and both clauses can hold of one vertex at
once — the rule saying in the same breath that a slot is committed and
that it is skipped.

Four processes at `f = 1`. Process `0` is Byzantine and issues three
vertices in round `1`: one pointing at the round-`0` vertex of process
`0`, two not. Processes `1` and `2` point to it; process `3` does not.
-/

namespace LeanDagTest

namespace Minnow

open LeanDag LeanDag.Minnow

/-- Round `0` carries one vertex per process; round `1` carries six,
three of them the equivocator's. -/
def kBlk : Fin 10 → Block (Fin 4) (Fin 10) Unit := fun i =>
  { round := if (i : ℕ) < 4 then 0 else 1,
    creator :=
      match (i : ℕ) with
      | 0 | 4 | 5 | 6 => 0
      | 1 | 7 => 1
      | 2 | 8 => 2
      | _ => 3,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => ∅
      | 4 | 7 | 8 => {0, 1, 2}
      | _ => {1, 2, 3},
    payload := () }

def Dk : Dag (Fin 4) (Fin 10) Unit where
  ids := Finset.univ
  block := kBlk
  complete := by decide
  valid := by decide
  correct_single := by decide

/-- The equivocator issues three vertices in round `1`, so the round
holds six. -/
example : (verticesAt Dk 1).card = 6 ∧ (slotBlocks Dk (0, 1)).card = 3 := by decide

/-- **Both clauses hold of the same vertex.** Three distinct processes
point to it, which is the quorum; and three vertices do not, which is the
skip. -/
example : Quorum Dk 0 ∧ SkippedByVertex Dk 0 := by decide

/-- Counting the skip by process instead leaves it out of reach, as it
must: the two sets then compete for the same `n` places. -/
example : ¬ Skipped Dk 0 ∧ pointers Dk 0 1 = {0, 1, 2} := by decide

/-- So the vertex is committed by the rule at the first position of
`leaders`, and simultaneously skipped by the clause that exists to
resolve slots the rule cannot commit. -/
example : CommittedAt Dk (fun _ => (0, 0)) 0 0 ∧ SkippedByVertex Dk 0 :=
  ⟨by simp only [CommittedAt]; decide, by decide⟩

end Minnow

end LeanDagTest
