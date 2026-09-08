import LeanDag.Minnow.Blocking
import LeanDagTest.Mysticeti.Model
/-!
# Minnow — a DAG in which `crs*` commits nothing, ever

`minnow.md` §3. Four processes at `f = 1`, so `2f + 1 = 3`, with process
`0` Byzantine and every other process correct. Six rounds, four vertices
per round, `id = 4 · round + process`.

The whole construction is one habit of the Byzantine process: **it sends
its vertex to process `1` alone**. Process `1` receives it and points to
it, the Byzantine process points to it as well, and processes `2` and `3`
never receive it in time. So every vertex of process `0` is pointed to by
exactly **two** processes of the round above.

Two is the dead zone. Definition 9 commits at `2f + 1 = 3` pointers and
skips at `2f + 1 = 3` non-pointers, and with `n = 3f + 1 = 4` vertices in
a round those two demands leave `f = 1` value uncovered. A vertex with
two pointers has neither, and no later vertex can change the count: a
round holds `n` vertices and all four are already there.

Nothing after such a slot can commit. The second leader of its round is
concurrent with it, so the causal-past escape is unavailable; and under
round robin the next round's two leaders are processes `2` and `3` —
exactly the two that did not receive the vertex — so the escape is
unavailable there too. Only from two rounds up does the vertex enter
every causal past, and by then the Byzantine process leads again.

The leader sequence is round robin over all four processes, two a round,
which is section 5's `leaders` at `l = 2`. It is not chosen to suit the
construction: the adversary picks which process to send to, and round
robin tells it which two to avoid.

**No timing assumption is used, and none would help.** Global
stabilisation guarantees delivery of what correct processes send; it says
nothing about a vertex a Byzantine process withheld. The execution below
is as available after GST as before it.
-/

namespace LeanDagTest

namespace Minnow

open LeanDag LeanDag.Minnow

/-- The vertices. `id = 4 · round + process`; process `0` is Byzantine.
Processes `2` and `3` point to everything of the round below, processes
`0` and `1` omit the Byzantine vertex. -/
def mBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  { round := (i : ℕ) / 4,
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => ∅
      | 4 | 5 => {0, 1, 2, 3}
      | 6 | 7 => {1, 2, 3}
      | 8 | 9 => {4, 5, 6, 7}
      | 10 | 11 => {5, 6, 7}
      | 12 | 13 => {8, 9, 10, 11}
      | 14 | 15 => {9, 10, 11}
      | 16 | 17 => {12, 13, 14, 15}
      | 18 | 19 => {13, 14, 15}
      | 20 | 21 => {16, 17, 18, 19}
      | _ => {17, 18, 19},
    payload := () }

/-- The DAG. Valid by the paper's rule: every edge sits in the round
below, no two edges share a process, and each non-genesis vertex carries
at least three. -/
def Dm : Dag (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := mBlk
  complete := by decide
  valid := by decide
  correct_single := by decide

/-- Two leaders a round, processes `0` then `1` — round robin at
`l = 2`. -/
def mLead : ℕ → Slot (Fin 4) := fun k => (⟨k % 4, Nat.mod_lt _ (by omega)⟩, k / 2)

/-! ## The dead zone

Each of the Byzantine process's leader vertices is pointed to by exactly
two processes of the round above: too few to commit, too many to skip. -/

example : pointers Dm 0 1 = {0, 1} ∧ pointers Dm 8 3 = {0, 1} ∧
    pointers Dm 16 5 = {0, 1} ∧ quorumCard (Fin 4) = 3 := by decide

example : (¬ Quorum Dm 0 ∧ ¬ Skipped Dm 0) ∧ (¬ Quorum Dm 8 ∧ ¬ Skipped Dm 8) ∧
    (¬ Quorum Dm 16 ∧ ¬ Skipped Dm 16) := by decide

/-- Anti-vacuity: the rounds are full and no process equivocates, so the
counts above are the counts of the whole round. -/
example : ∀ r ∈ ({0, 1, 2, 3, 4, 5} : Finset ℕ), (verticesAt Dm r).card = 4 := by decide

/-- And every correct process's leader vertex carries a quorum, so what
stops those is the second clause and not the first. -/
example : Quorum Dm 1 ∧ Quorum Dm 6 ∧ Quorum Dm 7 ∧ Quorum Dm 9 ∧
    Quorum Dm 14 ∧ Quorum Dm 15 := by decide

/-! ## Nothing commits

Round robin puts the Byzantine process in a leader slot every other
round. Its vertex there is dead, its own round's other leader is
concurrent with it, and the next round's two leaders are exactly the two
processes it did not send to. -/

/-- Leader `0` — slot `(0, 0)`, vertex `0`. No quorum. -/
example : ¬ CommittedAt Dm mLead 0 0 := not_committedAt_of_not_quorum (by decide)

/-- Leader `1` — slot `(1, 0)`, vertex `1`, concurrent with the dead
slot beside it. -/
example : ¬ CommittedAt Dm mLead 1 1 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

/-- Leader `2` — slot `(2, 1)`, vertex `6`. Process `2` never received
the dead vertex, so it is not in its causal past either. -/
example : ¬ CommittedAt Dm mLead 2 6 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

/-- Leader `3` — slot `(3, 1)`, vertex `7`. Likewise process `3`. -/
example : ¬ CommittedAt Dm mLead 3 7 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

/-- Leader `4` — slot `(0, 2)`, vertex `8`. By now the round-0 dead slot
has entered every causal past, and this one has taken over. No quorum. -/
example : ¬ CommittedAt Dm mLead 4 8 := not_committedAt_of_not_quorum (by decide)

/-- Leader `5` — slot `(1, 2)`, vertex `9`. -/
example : ¬ CommittedAt Dm mLead 5 9 :=
  not_committedAt_of_dead (j := 4) (by omega) (by decide)

/-- Leader `6` — slot `(2, 3)`, vertex `14`. -/
example : ¬ CommittedAt Dm mLead 6 14 :=
  not_committedAt_of_dead (j := 4) (by omega) (by decide)

/-- Leader `7` — slot `(3, 3)`, vertex `15`. -/
example : ¬ CommittedAt Dm mLead 7 15 :=
  not_committedAt_of_dead (j := 4) (by omega) (by decide)

/-- Leader `8` — slot `(0, 4)`, vertex `16`. No quorum. -/
example : ¬ CommittedAt Dm mLead 8 16 := not_committedAt_of_not_quorum (by decide)

/-- Leader `9` — slot `(1, 4)`, vertex `17`. -/
example : ¬ CommittedAt Dm mLead 9 17 :=
  not_committedAt_of_dead (j := 8) (by omega) (by decide)

/-- **Why the construction has to repeat.** A dead slot is *resolved* for
later leaders without ever being *decided*: the first disjunct of the
second clause asks only that some vertex of the slot lie in the
candidate's causal past, not that it be committed or skipped. Two
pointers carry it there in two rounds, because a vertex references
`2f + 1` of the `3f + 1` below it and so cannot miss both. So the
round-`0` dead slot is out of reach for the leaders of rounds `0` and
`1` — its own round, where there is no causal path, and the round above,
whose leaders are the two processes that did not point to it — and is in
the causal past of every leader from round `2` on. One dead slot holds two
rounds and no more. -/
example : ¬ Reaches Dm 1 0 ∧ ¬ Reaches Dm 6 0 ∧ ¬ Reaches Dm 7 0 ∧
    Reaches Dm 8 0 ∧ Reaches Dm 9 0 ∧ Reaches Dm 14 0 := by decide

/-- The blocking slot is always the newest dead one, the older having
been absorbed: the round-1 dead vertex is in the round-3 leader's causal
past, and the round-2 one is not. -/
example : Reaches Dm 14 4 ∧ ¬ Reaches Dm 14 8 ∧ Reaches Dm 6 1 := by decide

/-- The leader sequence is round robin over all four processes, two a
round — section 5's `leaders` at `l = 2`. -/
example : mLead 0 = (0, 0) ∧ mLead 1 = (1, 0) ∧ mLead 2 = (2, 1) ∧
    mLead 3 = (3, 1) ∧ mLead 4 = (0, 2) ∧ mLead 9 = (1, 4) := by decide

/-! ## And a simpler way to the same end: a silent leader

The dead zone needs the Byzantine process to issue a vertex and place it
carefully. It need not bother. Definition 9 asks that "there is a vertex
`v′` in slot `s′` in `D` such that …", so a slot holding **no** vertex
satisfies neither disjunct: there is nothing to reach, nothing to commit
and nothing to skip. A process that simply stops issuing vertices leaves
every one of its leader slots empty, and every later leader blocked.

Rounds still advance — `n − f = 3` vertices complete a round — so the
DAG below is one the communication component builds. -/

/-- Three processes issuing, process `0` silent. `id = 3 · round + (p − 1)`. -/
def sBlk : Fin 12 → Block (Fin 4) (Fin 12) Unit := fun i =>
  { round := (i : ℕ) / 3,
    creator := ⟨(i : ℕ) % 3 + 1, by omega⟩,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 => ∅
      | 3 | 4 | 5 => {0, 1, 2}
      | 6 | 7 | 8 => {3, 4, 5}
      | _ => {6, 7, 8},
    payload := () }

def Ds : Dag (Fin 4) (Fin 12) Unit where
  ids := Finset.univ
  block := sBlk
  complete := by decide
  valid := by decide
  correct_single := by decide

/-- The silent process's slots are empty, and every other vertex carries
a quorum — so nothing but the second clause is in the way. -/
example : slotBlocks Ds (0, 0) = ∅ ∧ slotBlocks Ds (0, 1) = ∅ ∧
    slotBlocks Ds (0, 2) = ∅ ∧ Quorum Ds 0 ∧ Quorum Ds 3 := by decide

/-- **Every leader after the first empty slot is blocked**, the
hypothesis holding vacuously. -/
example : ¬ CommittedAt Ds mLead 1 0 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

example : ¬ CommittedAt Ds mLead 2 3 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

example : ¬ CommittedAt Ds mLead 3 3 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

example : ¬ CommittedAt Ds mLead 4 6 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

example : ¬ CommittedAt Ds mLead 5 6 :=
  not_committedAt_of_dead (j := 0) (by omega) (by decide)

end Minnow

end LeanDagTest
