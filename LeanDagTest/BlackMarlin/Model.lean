import LeanDagTest.Mysticeti.Model
import LeanDag.BlackMarlin.Safety.Proof
/-!
# Black Marlin witnesses — Figure 1 on data

Every definition of `LeanDag/BlackMarlin/Model/` settled by `decide`
before anything is proved from it (`black-marlin.md` §6), on the
execution the paper draws: four validators, one fault, six rounds, one
anchor per round.

The figure's point is the last two rounds. Anchors `B0`, `B1`, `B2` and
`B3` all carry a quorum of support, but validator `0` omits `B3` from
`B4`, so `B3` fails the link clause of L16 while `B0`, `B1` and `B2`
satisfy the whole rule. That is the configuration the rule's second
clause exists for, and `decide` settles both halves of it here.

The committee is the standard witness one, validator `0` Byzantine and
`f = 1` (`LeanDagTest/Model.lean`), so the quorum is `3`. Validator `0`
is also the author of the omission, which is what the figure's caption
requires of it after stabilisation.
-/

namespace LeanDagTest

namespace BlackMarlin

open LeanDag LeanDag.BlackMarlin

/-- Round-robin, one anchor per round: round `r` anchored by `r % 4`. -/
local instance bmRotation : Rotation (Fin 4) where
  anchor r := ⟨r % 4, Nat.mod_lt _ (by omega)⟩

/-- The blocks of Figure 1: id `i` sits at round `i / 4` and is authored
by validator `i % 4`, so the anchor of round `r` is id `4 * r + r % 4`.

Every block references three of the four blocks below it, always
including its author's own — the self-parent clause the core requires
and the paper does not. The two departures from "reference everything
below" are the figure's: id `16`, the round-4 anchor, omits id `15`, the
round-3 anchor; and ids `7`, `11`, `18`, `23` drop one non-anchor
reference each, so that the counts below are quorums rather than the
whole committee. -/
def bmBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  { round := (i : ℕ) / 4,
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩,
    refs :=
      match (i : ℕ) with
      | 4 => {0, 1, 2} | 5 => {0, 1, 2} | 6 => {0, 1, 2} | 7 => {0, 2, 3}
      | 8 => {4, 5, 6} | 9 => {4, 5, 6} | 10 => {4, 5, 6} | 11 => {5, 6, 7}
      | 12 => {8, 9, 10} | 13 => {8, 9, 10} | 14 => {8, 9, 10} | 15 => {9, 10, 11}
      | 16 => {12, 13, 14} | 17 => {13, 14, 15} | 18 => {12, 14, 15}
      | 19 => {13, 14, 15}
      | 20 => {16, 17, 18} | 21 => {16, 17, 18} | 22 => {16, 17, 18}
      | 23 => {17, 18, 19}
      | _ => ∅,
    payload := () }

/-- The execution of Figure 1, as a block universe: all four conditions
by `decide`. -/
def Ubm : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := bmBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The anchors -/

/-- The six anchor blocks of the figure, at rounds `0` to `5`. -/
example : IsAnchor Ubm 0 0 ∧ IsAnchor Ubm 1 5 ∧ IsAnchor Ubm 2 10 ∧
    IsAnchor Ubm 3 15 ∧ IsAnchor Ubm 4 16 ∧ IsAnchor Ubm 5 21 := by decide

/-- The rotation is not vacuous the other way: no other round-3 block is
an anchor. -/
example : ¬ IsAnchor Ubm 3 12 ∧ ¬ IsAnchor Ubm 3 13 ∧ ¬ IsAnchor Ubm 3 14 := by decide

/-! ## Support

Every anchor of rounds `0` to `4` carries a quorum. `B3` is supported by
exactly the quorum `{1, 2, 3}` — validator `0` withholds — and `B5` is
unsupported only because the DAG stops at round `5`. -/

example : Supported Ubm 0 0 ∧ Supported Ubm 5 1 ∧ Supported Ubm 10 2 ∧
    Supported Ubm 15 3 ∧ Supported Ubm 16 4 := by decide

example : supporters Ubm 15 4 = {1, 2, 3} := by decide

example : ¬ Supported Ubm 21 5 := by decide

/-! ## The rule

`B0`, `B1` and `B2` satisfy L16; `B3` does not, and the clause it fails
is the link. -/

example : Committed Ubm 0 0 ∧ Committed Ubm 5 1 ∧ Committed Ubm 10 2 := by decide

/-- **The figure's point.** `B3` is a supported anchor and is still not
committed: the round-4 anchor does not reference it. -/
example : ¬ Committed Ubm 15 3 ∧ ¬ Linked Ubm 15 3 := by decide

/-- Nothing else fails: had `B4` referenced `B3`, the rule would have
admitted it. The link set of `B3` is empty because `B4` is the only
round-4 anchor and `15 ∉ B4.refs`. -/
example : linkers Ubm 15 3 = ∅ ∧ (15 : Fin 24) ∉ (Ubm.block 16).refs := by decide

/-- `B4` fails the other way: it is supported and its linking anchor `B5`
exists, but `B5` carries no support, the DAG having stopped. -/
example : ¬ Committed Ubm 16 4 ∧ ¬ Supported Ubm 21 5 := by decide

/-- **Why the rule has a second clause.** `B3` and `B4` are both
supported anchors, one round apart, and neither lies in the causal
history of the other. Support alone would admit both and leave them
incomparable, which is the middle case of BM5 and the only case the link
clause is used in. -/
example : Supported Ubm 15 3 ∧ Supported Ubm 16 4 ∧ ¬ Reaches Ubm 16 15 :=
  ⟨by decide, by decide,
    fun h => absurd ((mem_history_iff (by decide)).mpr h) (by decide)⟩

/-! ## The results, on this universe

The safety statements instantiated at Figure 1 — each derived from
`Safety.holds`, so what the witness exercises is the proved theorem and
not a restatement of it. -/

/-- BM1 on data: `B3` is the only supported anchor of round `3`. -/
example : (15 : Fin 24) = 15 :=
  (Safety.holds (Fin 4) (Fin 24) Unit Ubm).1 3 15 15 (by decide) (by decide)
    (by decide) (by decide)

/-- BM2 on data: `B0`, supported at round `0`, lies in the causal history
of every block from round `2` up — here the round-5 anchor. -/
example : Reaches Ubm 21 0 :=
  (Safety.holds (Fin 4) (Fin 24) Unit Ubm).2.1 0 0 21 (by decide) (by decide)
    (by decide)

/-- BM3 on data: round `2` carries a quorum of authors, witnessed from a
round-5 block. -/
example : quorumCard (Fin 4) ≤ (authorsAt Ubm 2).card :=
  (Safety.holds (Fin 4) (Fin 24) Unit Ubm).2.2.1 21 2 (by decide) (by decide)

/-- The full view: a validator that holds the whole DAG. Enough to
exercise the view-relative clauses, since a view can only under-report
and the results run in that direction. -/
def Vbm : View (Fin 4) (Fin 24) Unit Ubm where
  ids := Finset.univ
  subset_ids := by decide
  complete := by decide

/-- The rule fires from a view as it does over the universe, and `B3`
fails there too. -/
example : CommittedIn Ubm Vbm 0 0 ∧ CommittedIn Ubm Vbm 5 1 ∧
    CommittedIn Ubm Vbm 10 2 ∧ ¬ CommittedIn Ubm Vbm 15 3 := by decide

/-- BM4 on data: the view's verdict is the universe's, and the view holds
the block. -/
example : Committed Ubm 10 2 ∧ (10 : Fin 24) ∈ Vbm.ids :=
  (Safety.holds (Fin 4) (Fin 24) Unit Ubm).2.2.2.1 Vbm 10 2 (by decide)

/-- BM5 on data: the committed anchors are chained — `B0` lies in the
causal history of `B2`, two rounds up. -/
example : (0 : Fin 24) = 10 ∨ Reaches Ubm 0 10 ∨ Reaches Ubm 10 0 :=
  (Safety.holds (Fin 4) (Fin 24) Unit Ubm).2.2.2.2.1 Vbm Vbm 0 10 0 2
    (by decide) (by decide)

/-- BM6 on data: the delivered prefix of `B0` is contained in that of
`B2`. -/
example : history Ubm 0 ⊆ history Ubm 10 :=
  (Safety.holds (Fin 4) (Fin 24) Unit Ubm).2.2.2.2.2.1 Vbm Vbm 0 10 0 2
    (by decide) (by decide) (by decide)

/-- BM7 on data: under the pipelined round-robin schedule the anchors are
the core's leader blocks. -/
example : IsLeaderBlock (S := Slots.uniformSingle 1 Nat.one_pos bmRotation.anchor)
    Ubm 2 10 :=
  ((Safety.holds (Fin 4) (Fin 24) Unit Ubm).2.2.2.2.2.2 2 10).mp (by decide)

/-! ## The whole statement -/

#print axioms LeanDag.BlackMarlin.Safety.holds

end BlackMarlin

end LeanDagTest
