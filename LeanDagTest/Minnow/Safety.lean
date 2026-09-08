import LeanDag.Minnow.Blocking
import LeanDagTest.Mysticeti.Model
/-!
# Minnow — one twin resolves a slot the other later commits

`report.md` §19.3. The second condition of `Φ*s` is satisfied by *some*
vertex of an earlier slot — "there is a vertex `v′` in slot `s′` in `D`
such that `v′ ⇝ ϕ(l)` …" — and resolving a slot that way does not decide
it. Where the slot's process equivocates, one twin can carry a later
leader past the slot while the other is still undecided, and then acquire
its quorum afterwards.

That is Safe-Commit, in the form the paper spells out: "if `P` is enabled
for a leader vertex `l` in `D`, then for all leader `l′ < l` in
`leaders` … if `P` is disabled for `l′` in `D` then it is also disabled
for `l′` in `D′`".

Four processes at `f = 1`, process `0` faulty and equivocating at round
`0` with `0` and `4`. One leader a round by round robin, so the leader of
round `r` is process `r`, and slot `(0, 0)` precedes slot `(1, 1)`.

Three round-1 vertices point to `0`, giving it a quorum in the whole DAG;
the fourth — process `1`'s, which is the round-1 leader — points to `4`
instead. A validator whose view is missing one of `0`'s three supporters
sees `0` undecided, resolves slot `(0, 0)` through `4`, and commits the
round-1 leader. The missing supporter then arrives.
-/

namespace LeanDagTest

namespace Minnow

open LeanDag LeanDag.Minnow

/-- The vertices. Round `0` carries five, two of them the equivocator's. -/
def sfBlk : Fin 13 → Block (Fin 4) (Fin 13) Unit := fun i =>
  { round :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 | 4 => 0
      | 5 | 6 | 7 | 8 => 1
      | _ => 2,
    creator :=
      match (i : ℕ) with
      | 0 | 4 | 5 | 9 => 0
      | 1 | 6 | 10 => 1
      | 2 | 7 | 11 => 2
      | _ => 3,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 | 4 => ∅
      | 5 => {0, 1, 2}
      | 6 => {4, 2, 3}
      | 7 => {0, 1, 2}
      | 8 => {0, 2, 3}
      | 12 => {5, 6, 7}
      | _ => {6, 7, 8},
    payload := () }

/-- The whole DAG. -/
def Dfull : Dag (Fin 4) (Fin 13) Unit where
  ids := Finset.univ
  block := sfBlk
  complete := by decide
  valid := by decide
  correct_single := by decide

/-- One validator's view: the same DAG without `5`, one of the three
vertices supporting the twin `0`, and without `12`, the only vertex that
references `5`. Reference-closed, and valid. -/
def Dpart : Dag (Fin 4) (Fin 13) Unit where
  ids := {0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11}
  block := sfBlk
  complete := by decide
  valid := by decide
  correct_single := by decide

/-- One leader a round, by round robin over the four processes. -/
def sfLead : ℕ → Slot (Fin 4) := fun k => (⟨k % 4, Nat.mod_lt _ (by omega)⟩, k)

example : Dpart.ids ⊆ Dfull.ids := by decide

/-! ## The equivocation, and the two views -/

/-- Process `0` issues two vertices in round `0`, and slot `(0, 0)` is
the first leader slot. -/
example : slotBlocks Dfull (0, 0) = {0, 4} ∧ sfLead 0 = (0, 0) ∧
    sfLead 1 = (1, 1) ∧ slotBlocks Dfull (1, 1) = {6} := by decide

/-- In the whole DAG the twin `0` carries a quorum and its twin `4` does
not, so BM-style uniqueness is not contradicted. -/
example : pointers Dfull 0 1 = {0, 2, 3} ∧ pointers Dfull 4 1 = {1} ∧
    Quorum Dfull 0 ∧ ¬ Quorum Dfull 4 := by decide

/-- In the partial view `0` is **undecided** — two supporters, one short,
and only one process not pointing at it, two short of a skip. -/
example : pointers Dpart 0 1 = {2, 3} ∧ ¬ Quorum Dpart 0 ∧
    ¬ Skipped Dpart 0 := by decide

/-- And undecided on the *literal* reading of the skip clause too, so the
finding does not rest on how `report.md` §19.2 settles it. Only one
round-`1` vertex of the view carries no edge to `0`, where three are
needed. -/
example : ¬ SkippedByVertex Dpart 0 := by decide

/-! ## The violation

The round-1 leader points to the other twin, which resolves the slot
without deciding it, and it carries a quorum of its own. -/

/-- `4 ⇝ 6` and `0` is not, so slot `(0, 0)` is resolved for the round-1
leader through the twin that will never be committed. -/
example : Reaches Dpart 6 4 ∧ ¬ Reaches Dpart 6 0 ∧ Quorum Dpart 6 := by decide

/-- **So the round-1 leader is committed in the partial view**, with the
earlier slot resolved and its own quorum met. -/
example : CommittedAt Dpart sfLead 1 6 := by
  simp only [CommittedAt]
  refine ⟨by decide, ?_⟩
  intro j hj
  have : j = 0 := by omega
  subst this
  exact ⟨4, by decide, Or.inl (by decide)⟩

/-- **And in the whole DAG the earlier leader is committed too.** It is
the first position of `leaders`, so its pattern is its quorum alone. -/
example : CommittedAt Dfull sfLead 0 0 := by simp only [CommittedAt]; decide

/-- **Safe-Commit, in the form the paper spells out.** `P` is enabled for
the round-1 leader in the smaller DAG; the earlier leader is disabled
there and enabled in the larger one. So a validator on the smaller view
outputs the round-1 leader with the earlier slot still undecided, and no
extension of its output can place the earlier leader where `leaders`
requires. -/
example : Dpart.ids ⊆ Dfull.ids ∧ CommittedAt Dpart sfLead 1 6 ∧
    ¬ Quorum Dpart 0 ∧ Quorum Dfull 0 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  simp only [CommittedAt]
  refine ⟨by decide, ?_⟩
  intro j hj
  have : j = 0 := by omega
  subst this
  exact ⟨4, by decide, Or.inl (by decide)⟩

/-- The equivocation is what does it. Without the second vertex in the
slot there is nothing to resolve it with: the twin `0` is not in the
round-1 leader's causal past, carries no quorum in that view and cannot
be skipped there. -/
example : ∀ v ∈ ({0} : Finset (Fin 13)), ¬ Reaches Dpart 6 v ∧
    ¬ Quorum Dpart v ∧ ¬ Skipped Dpart v := by decide

/-! ## Where Lemma 10 goes wrong

The paper's proof that `crs*` is safe ends in a case split. With
`D ⊆ D'`, `vz` committed in `D`, and `vk` committed in `D'` and ordered
before it: "if `vk ⇝ vz` in `D` then `vk` is also committed by indirect
commit in `crs*(D)`, or if they are concurrent then `vk < vz` by
`leaders` and `vz` is not committed in `crs*(D)` because
`Ps*(vk, D) = false`."

Read `vk` as the twin `0`, `vz` as the round-1 leader `6`, `D` as `Dpart`
and `D'` as `Dfull`. `report.md` §19.3 is where this is set out. -/

/-- **The execution is in the second case, and its hypothesis holds.**
The two are concurrent and the earlier one fails `Ps*` in the smaller
DAG, which is exactly what the proof concludes from. -/
example : Concurrent Dpart 6 0 ∧ ¬ Quorum Dpart 0 := by decide

/-- **And the conclusion drawn from it is false**: the later leader is
committed in the smaller DAG all the same. The proof's step needs the
second condition, applied by `vz` to `vk`'s slot, to be about `vk`. It is
an existential over the slot, and the slot holds two vertices — the other
one is in `vz`'s causal past. -/
example : (4 : Fin 13) ∈ slotBlocks Dpart (0, 0) ∧
    (0 : Fin 13) ∈ slotBlocks Dpart (0, 0) ∧ Reaches Dpart 6 4 := by decide

/-- **The uniqueness the proof opens with is true here**, and is not what
the step needs. At most one vertex of a slot can satisfy `Ps*`, because
two quorums of `2f + 1` would share a correct process pointing at both. -/
example : Quorum Dfull 0 ∧ ¬ Quorum Dfull 4 := by decide

/-- **The two come apart in the worst way.** The twin that resolves the
slot is the one that can never satisfy `Ps*`, and the twin that satisfies
it is the one out of reach. Uniqueness of the committable vertex says
nothing about which vertex may resolve the slot. -/
example : ¬ Quorum Dfull 4 ∧ Reaches Dpart 6 4 ∧ ¬ Reaches Dpart 6 0 := by decide

end Minnow

end LeanDagTest
