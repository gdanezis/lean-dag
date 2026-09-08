import LeanDagTest.BlackMarlin.Divergence
/-!
# Black Marlin — counting support in the cone does not settle it either

`black-marlin.md` §14. The support-preferring descent reads `Supported`,
a quorum of the whole universe, which a validator's view need not carry.
The obvious weakening is to read support **relatively**: among the twins,
prefer the one more of the descent's own cone references. That is
view-independent by construction — every validator descending from one
block reads one cone — and on §13's execution it answers correctly.

It has no margin, and fails already at four validators. A committed twin
holds `2f + 1` supporters of `3f + 1`, of which at least `f + 1` are
reliable; a reliable supporter authors one block at the round above and
that block references the twin, so it is counted exactly when the cone
holds it — and a cone need only carry `n − f` authors, omitting up to
`f`. **One** cone-supporter is all the committed twin is promised. Its
twin is bounded the other way: a supporter of both authors two blocks at
one round, so the two supporter sets meet only inside the `f` Byzantine
validators, and outside the quorum there are `f` more. That gives `2f`,
and every one of them can sit in the cone, the Byzantine ones
contributing the block that references the twin rather than the block
that references the anchor. So `1` is weighed against `2f`.

Both ends are realised below at `f = 1`, where they are `1` and `2`.
Four validators, `0` Byzantine, seven rounds; the rotation anchors
rounds `0` to `6` by `3, 3, 0, 2, 3, 1, 1`.

Validator `0` equivocates at round `2` with `8` and `12`, **giving them
the same references**, so the twins agree in round, in creator and in
cone and nothing block-intrinsic separates them. Round `3` gives `12`
the quorum `{0, 1, 2}` and `8` only `{0, 3}` — one short — with `0`
equivocating again to support both. So `12` is committed and `8` is not.

The round-4 anchor `21` references the round-3 blocks of `1`, `3` and
`0`, taking the twin-`8` block from the equivocator. It omits the
round-3 anchor, so a descent arriving there skips the round and faces
both twins — and of the three round-3 blocks in its cone, **two
reference `8` and one references `12`**. Counting prefers the twin that
was not committed.

The second half of the file is the other horn. A validator could wait
for the quorum rather than count what it has, and waiting does not close
it either: the deciding supporter of `12` is authored by the
equivocator and referenced by no reliable block, so a view holding every
reliable block still sees neither twin supported. Deciding early is
unsafe and waiting can stop, which is the dichotomy `report.md` §18.14
draws.
-/

namespace LeanDagTest

namespace BlackMarlin

set_option maxRecDepth 4096

open LeanDag LeanDag.BlackMarlin

/-- Rounds `0` to `6` anchored by `3, 3, 0, 2, 3, 1, 1`. Round `2` is
anchored by the Byzantine validator. -/
local instance cntRot : Rotation (Fin 4) where
  anchor r := match r with
    | 0 => 3 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 3 | _ => 1

/-- The blocks. Id order is production order. -/
def cntBlk : Fin 30 → Block (Fin 4) (Fin 30) Unit := fun i =>
  { round :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => 0
      | 4 | 5 | 6 | 7 => 1
      | 8 | 9 | 10 | 11 | 12 => 2
      | 13 | 14 | 15 | 16 | 17 => 3
      | 18 | 19 | 20 | 21 => 4
      | 22 | 23 | 24 | 25 => 5
      | _ => 6,
    creator :=
      match (i : ℕ) with
      | 0 | 4 | 8 | 12 | 13 | 17 | 18 | 22 | 26 => 0
      | 1 | 5 | 9 | 14 | 19 | 23 | 27 => 1
      | 2 | 6 | 10 | 15 | 20 | 24 | 28 => 2
      | _ => 3,
    refs :=
      match (i : ℕ) with
      | 0 | 1 | 2 | 3 => ∅
      | 4 => {0, 1, 2} | 5 => {0, 1, 2} | 6 => {1, 2, 3} | 7 => {1, 2, 3}
      | 8 | 12 => {4, 5, 6}
      | 9 => {4, 5, 6} | 10 => {4, 5, 6} | 11 => {5, 6, 7}
      | 13 | 14 | 15 => {12, 9, 10}
      | 16 | 17 => {8, 10, 11}
      | 18 => {13, 14, 15}
      | 19 | 20 => {14, 15, 16}
      | 21 => {14, 16, 17}
      | 22 => {18, 19, 21}
      | 23 | 24 | 25 => {19, 20, 21}
      | 26 => {22, 23, 24}
      | _ => {23, 24, 25},
    payload := () }

def Ucnt : BlockUniverse (Fin 4) (Fin 30) Unit where
  ids := Finset.univ
  block := cntBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The equivocation -/

/-- The twins agree in round, in creator and in cone. Nothing intrinsic
to the blocks separates them. -/
example : IsAnchor Ucnt 2 8 ∧ IsAnchor Ucnt 2 12 ∧ (8 : Fin 30) ≠ 12 ∧
    (Ucnt.block 8).refs = (Ucnt.block 12).refs ∧
    strongOf Ucnt 8 = strongOf Ucnt 12 ∧
    (Ucnt.block 8).creator ∉ (Correct : Finset (Fin 4)) := by decide

/-- One carries the quorum and the other is one short, so BM1 is not
contradicted; and the first is committed. -/
example : supporters Ucnt 12 3 = {0, 1, 2} ∧ supporters Ucnt 8 3 = {0, 3} ∧
    quorumCard (Fin 4) = 3 ∧ Committed Ucnt 12 2 ∧ ¬ Supported Ucnt 8 2 := by decide

/-! ## The descent that skips -/

/-- The round-4 anchor commits, omits the round-3 anchor, and so faces
both twins a round further down. -/
example : Committed Ucnt 21 4 ∧ coneAnchors Ucnt 21 3 = ∅ ∧
    coneAnchors Ucnt 21 2 = {8, 12} := by decide

/-- Its cone, as a view. -/
def cntView : View (Fin 4) (Fin 30) Unit Ucnt where
  ids := history Ucnt 21
  subset_ids := history_subset_ids (by decide)
  complete := by decide

/-- **Counting in the cone prefers the twin that was not committed**, two
to one. The view is a legitimate one: reference-closed, and holding a
quorum of authors at the round it counts. -/
example : supportersIn Ucnt cntView 8 3 = {0, 3} ∧
    supportersIn Ucnt cntView 12 3 = {1} ∧
    quorumCard (Fin 4) ≤ (authorsIn Ucnt cntView.ids 3).card := by decide

/-- The paper's rule fails here too, its metric tying exactly — the twins
have one cone — so the identifier order decides, and picks the same
wrong twin. -/
example : anchorGap Ucnt 8 = anchorGap Ucnt 12 ∧ descend Ucnt 21 = some 8 := by decide

/-- **The divergence.** A validator that committed `12` at round `2`
flushes it; one that reaches the round-4 anchor first flushes `8`. -/
example : flushRecord Ucnt 21 2 = some 8 ∧ flushRecord Ucnt 12 2 = some 12 ∧
    Committed Ucnt 12 2 := by decide

/-- Only the quorum reading separates them, and that is the reading a
view need not be able to evaluate. -/
example : descendS Ucnt 21 = some 12 := by decide


/-! ## And waiting for the support does not help

A validator could decline to descend until it can see the quorum for
itself. That is the other horn, and it does not close either: the quorum
for `12` is `{0, 1, 2}`, and `0` is the Byzantine validator. Its
supporting block `13` is referenced by no reliable block, so a validator
holding **every** reliable block, and everything those reference, still
holds only `{1, 2}` — and holds `{0, 3}` for the other twin, so it
cannot tell the two apart in either direction.

Nothing obliges the equivocator to send `13`. Under partial synchrony
only the messages of reliable validators are delivered, so the wait need
never end, and a rule that waits is a rule that can stop. -/

/-- Every reliable block, and everything reliable blocks reference. -/
def relIds : Finset (Fin 30) :=
  (Finset.univ.filter (fun i => (Ucnt.block i).creator ∈ (Correct : Finset (Fin 4)))).biUnion
    (history Ucnt)

def relView : View (Fin 4) (Fin 30) Unit Ucnt where
  ids := relIds
  subset_ids := by decide
  complete := by decide

/-- The view holds every reliable block; what it misses is authored by
the equivocator. -/
example : (∀ i : Fin 30, (Ucnt.block i).creator ∈ (Correct : Finset (Fin 4)) → i ∈ relIds) ∧
    (13 : Fin 30) ∉ relIds ∧ (Ucnt.block 13).creator ∉ (Correct : Finset (Fin 4)) ∧
    (13 : Fin 30) ∈ (Ucnt.block 18).refs := by decide

/-- **Neither twin is supported in that view.** A validator that has
received everything it is owed cannot tell which of them was committed,
and no further reliable block will settle it. -/
example : supportersIn Ucnt relView 12 3 = {1, 2} ∧ supportersIn Ucnt relView 8 3 = {0, 3} ∧
    ¬ SupportedIn Ucnt relView 12 2 ∧ ¬ SupportedIn Ucnt relView 8 2 ∧
    Supported Ucnt 12 2 := by decide

end BlackMarlin

end LeanDagTest
