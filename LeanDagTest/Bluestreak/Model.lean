import LeanDag.Bluestreak.Liveness

/-!
# Bluestreak on concrete sparse DAGs

Four validators, `f = 1`, one leader per round, `leader k = k mod 4`.
Ids are `4·round + creator`.

* `U1`, six rounds: slot 0's candidate gathers three votes but only two
  claims, so it is settled neither way directly; slots 1, 2 and 3 commit
  directly, and slot 3 anchors slot 0's indirect commit through the claim
  block `8` carries.
* `U2`: slot 0 is directly skipped while the Byzantine round-3 leader
  block `15` links a claim for it — a Byzantine block's unbacked claim.
  `15` is not certified, so it is no anchor: the law `skip_link` holds of
  anchors and of nothing weaker.
* `U3`: the round-2 leader equivocates; every round-3 block omits one
  twin or the other, three omit each, and only two omit both. Bluestreak's
  per-candidate skip fires where the core's slot blame does not.
-/

namespace LeanDagTest

open LeanDag LeanDag.Bluestreak

instance bsSlots : Slots (Fin 4) := Slots.identity fun k => ⟨k % 4, Nat.mod_lt _ (by omega)⟩

/-- A block from its round, creator and references, over any id type. -/
def bsBlock {N : ℕ} (r : ℕ) (v : ℕ) (hv : v < 4) (refs : Finset (Fin N)) :
    Block (Fin 4) (Fin N) Unit :=
  { round := r, creator := ⟨v, hv⟩, refs := refs, payload := () }

/-! ## `U1`: direct commits and an indirect commit -/

section U1

instance bsFaults1 : Faults (Fin 4) where
  f := 1
  byzantine := {2}
  card_validators := by decide
  card_byzantine := by decide

def blk1 : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i => match (i : ℕ) with
  | 0 => bsBlock 0 0 (by omega) ∅ | 1 => bsBlock 0 1 (by omega) ∅
  | 2 => bsBlock 0 2 (by omega) ∅ | 3 => bsBlock 0 3 (by omega) ∅
  | 4 => bsBlock 1 0 (by omega) {0} | 5 => bsBlock 1 1 (by omega) {0, 1, 2, 3}
  | 6 => bsBlock 1 2 (by omega) {2} | 7 => bsBlock 1 3 (by omega) {3, 0}
  | 8 => bsBlock 2 0 (by omega) {4, 5} | 9 => bsBlock 2 1 (by omega) {5}
  | 10 => bsBlock 2 2 (by omega) {4, 5, 6, 7} | 11 => bsBlock 2 3 (by omega) {7, 5}
  | 12 => bsBlock 3 0 (by omega) {8, 10} | 13 => bsBlock 3 1 (by omega) {9, 10}
  | 14 => bsBlock 3 2 (by omega) {10} | 15 => bsBlock 3 3 (by omega) {8, 9, 10, 11}
  | 16 => bsBlock 4 0 (by omega) {12, 13, 14, 15} | 17 => bsBlock 4 1 (by omega) {13, 15}
  | 18 => bsBlock 4 2 (by omega) {14, 15} | 19 => bsBlock 4 3 (by omega) {15}
  | 20 => bsBlock 5 0 (by omega) {16} | 21 => bsBlock 5 1 (by omega) {16, 17, 18, 19}
  | 22 => bsBlock 5 2 (by omega) {18, 16} | 23 => bsBlock 5 3 (by omega) {19, 16}
  | _ => bsBlock 0 0 (by omega) ∅

/-- The explicit claims: `8` for the genesis leader `0`; `12`, `13` for
`5`; `17`, `19` for `10`; `20`, `23` for `15`. -/
instance claims1 : ClaimMap (Fin 24) where
  claim
    | 8 => some 0 | 12 => some 5 | 13 => some 5 | 17 => some 10 | 19 => some 10
    | 20 => some 15 | 23 => some 15 | _ => none

def U1 : Universe (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := blk1
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem U1_disciplined : Disciplined U1 :=
  Disciplined.of_decide (fun _ => rfl) (by decide) (by decide)

-- Slot 0's candidate is certified, claimed twice, and omitted once: undecided directly.
example : Certified U1 0 := by decide
example : claimers U1 0 = {8, 10} := by decide
example : ¬ DirectCommitIn U1 (View.full U1) 0 := by decide
example : ¬ DirectSkipIn U1 (View.full U1) 0 := by decide

/-- Slots 1, 2 and 3 commit directly: three claims each, one of them the
leader block's implicit claim. -/
theorem U1_slot1 : Decided U1 (View.full U1) 1 (some 5) :=
  Decided.directCommit (by decide) (by decide)
theorem U1_slot2 : Decided U1 (View.full U1) 2 (some 10) :=
  Decided.directCommit (by decide) (by decide)
theorem U1_slot3 : Decided U1 (View.full U1) 3 (some 15) :=
  Decided.directCommit (by decide) (by decide)

/-- Slot 0 commits indirectly: slot 3 is its nearest eligible anchor, and
`8`, claiming `0`, lies in `15`'s cone. -/
theorem U1_slot0 : Decided U1 (View.full U1) 0 (some 0) :=
  AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) (by omega) (by decide) U1_slot3
    (fun m _ _ h => absurd (show 0 + 2 < m from h) (by omega))
    (by decide) ⟨8, by decide, Reaches.single (by decide)⟩

/-- The claims a direct commit counts: slot 1's candidate is claimed by
every block of `{0, 1, 3}` at round 3, slot 0's is not at round 2. -/
example : ClaimsAt U1 {0, 1, 3} 1 5 := by decide
example : ¬ ClaimsAt U1 {0, 1, 3} 0 0 := by decide

/-- Agreement at the witness: whatever another view derives for slot 0, it
is `some 0`. -/
example (V : U1.View) (v : Option (Fin 24)) (h : Decided U1 V 0 v) : v = some 0 :=
  (AnchoredRule.decided_agree bluestreakLaws U1_disciplined h U1_slot0)

end U1

/-! ## `U2`: a Byzantine anchor candidate with an unbacked claim -/

section U2

instance bsFaults2 : Faults (Fin 4) where
  f := 1
  byzantine := {3}
  card_validators := by decide
  card_byzantine := by decide

def blk2 : Fin 16 → Block (Fin 4) (Fin 16) Unit := fun i => match (i : ℕ) with
  | 0 => bsBlock 0 0 (by omega) ∅ | 1 => bsBlock 0 1 (by omega) ∅
  | 2 => bsBlock 0 2 (by omega) ∅ | 3 => bsBlock 0 3 (by omega) ∅
  | 4 => bsBlock 1 0 (by omega) {0} | 5 => bsBlock 1 1 (by omega) {1, 2, 3}
  | 6 => bsBlock 1 2 (by omega) {2} | 7 => bsBlock 1 3 (by omega) {3}
  | 8 => bsBlock 2 0 (by omega) {4, 5} | 9 => bsBlock 2 1 (by omega) {5}
  | 10 => bsBlock 2 2 (by omega) {4, 5, 6, 7} | 11 => bsBlock 2 3 (by omega) {7, 5}
  | 12 => bsBlock 3 0 (by omega) {8, 10} | 13 => bsBlock 3 1 (by omega) {9, 10}
  | 14 => bsBlock 3 2 (by omega) {10} | 15 => bsBlock 3 3 (by omega) {8, 9, 10, 11}
  | _ => bsBlock 0 0 (by omega) ∅

/-- The Byzantine `11` claims `0` certified; `0` has one vote. -/
instance claims2 : ClaimMap (Fin 16) where
  claim | 11 => some 0 | _ => none

def U2 : Universe (Fin 4) (Fin 16) Unit where
  ids := Finset.univ
  block := blk2
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem U2_disciplined : Disciplined (S := bsSlots) U2 :=
  Disciplined.of_decide (fun _ => rfl) (by decide) (by decide)

/-- Slot 0 is directly skipped, the eligible candidate anchor `15` links
`0` through `11`, and `15` is not certified: without `Anchor U A`, the
skip law would ask the impossible. -/
example : DirectSkipIn (S := bsSlots) U2 (View.full U2) 0 := by decide
example : IsLeaderBlock (S := bsSlots) U2 3 15 ∧
    (bluestreakAnchored (Fin 4) (Fin 16) Unit).Eligible (S := bsSlots) 0 3 := by decide
example : ClaimedIn U2 15 0 := ⟨11, by decide, Reaches.single (by decide)⟩
example : ¬ Certified U2 15 := by decide
example : ¬ Certified U2 0 := by decide

end U2

/-! ## `U3`: the per-candidate skip against the core's slot blame -/

section U3

instance bsFaults3 : Faults (Fin 4) where
  f := 1
  byzantine := {2}
  card_validators := by decide
  card_byzantine := by decide

def blk3 : Fin 17 → Block (Fin 4) (Fin 17) Unit := fun i => match (i : ℕ) with
  | 0 => bsBlock 0 0 (by omega) ∅ | 1 => bsBlock 0 1 (by omega) ∅
  | 2 => bsBlock 0 2 (by omega) ∅ | 3 => bsBlock 0 3 (by omega) ∅
  | 4 => bsBlock 1 0 (by omega) {0} | 5 => bsBlock 1 1 (by omega) {0, 1, 2, 3}
  | 6 => bsBlock 1 2 (by omega) {2} | 7 => bsBlock 1 3 (by omega) {3}
  | 8 => bsBlock 2 0 (by omega) {4, 5} | 9 => bsBlock 2 1 (by omega) {5}
  | 10 => bsBlock 2 2 (by omega) {4, 5, 6, 7} | 11 => bsBlock 2 3 (by omega) {7, 5}
  | 12 => bsBlock 3 0 (by omega) {8} | 13 => bsBlock 3 1 (by omega) {9}
  | 14 => bsBlock 3 2 (by omega) {10} | 15 => bsBlock 3 3 (by omega) {8, 9, 16, 11}
  | 16 => bsBlock 2 2 (by omega) {4, 5, 6, 7}
  | _ => bsBlock 0 0 (by omega) ∅

instance claims3 : ClaimMap (Fin 17) where
  claim _ := none

def U3 : Universe (Fin 4) (Fin 17) Unit where
  ids := Finset.univ
  block := blk3
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem U3_disciplined : Disciplined (S := bsSlots) U3 :=
  Disciplined.of_decide (fun _ => rfl) (by decide) (by decide)

/-- Slot 2 has two candidates, `10` and `16`; three round-3 blocks omit
each, so Bluestreak skips it, and two omit both, so the core would not. -/
example : leaderBlocksAt (S := bsSlots) U3 2 = {10, 16} := by decide
example : DirectSkipIn (S := bsSlots) U3 (View.full U3) 2 := by decide
example : ¬ blameSkip (S := bsSlots) (quorumCard (Fin 4)) U3 (View.full U3) 2 := by decide
example : slotBlamers (S := bsSlots) U3 2 = {12, 13} := by decide

end U3

end LeanDagTest
