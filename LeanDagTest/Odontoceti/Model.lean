import LeanDag.Odontoceti.Properties
import LeanDag.Odontoceti.Liveness
import LeanDag.Common.Schedule
import LeanDag.DoS.Exclusion
import Mathlib.Tactic.IntervalCases

/-!
# Odontoceti at the boundary: `n = 6`, `f = 1`

`odontoceti.md` §6, OP0/OP1 witnesses. The boundary instance of
`n ≥ 5f+1`: six validators, Byzantine `{0}`, DAG quorum and direct
thresholds `n − f = 5`, indirect threshold `n − 3f = 3` — the thesis's
`4f+1` and `2f+1` exactly.

Three universes:

* **`Uodo`** — the sunny day: four rounds, every block referencing the
  whole previous round. Validity by `decide` settles the §2 reuse claim
  on data — the existing `BlockUniverse` accepts the Odontoceti
  parameters untouched — and every slot commits directly.
* **`Uskip`** — the full decision zoo on one universe: a direct skip
  (five blames, the sixth author pinned to support by its own
  self-parent), an undecided slot committed **indirectly** through the
  slot-3 anchor two rounds up (`ThickLink` at exactly `3`), and an
  undecided slot **indirectly skipped** through the slot-4 anchor (its
  two supporters cannot reach the threshold in any cone).
* **`Utwin6`** — **the thesis gap, on data.** Byzantine validator 0
  equivocates at round 0; each twin gathers exactly three supporters
  (disjoint correct pairs plus the equivocator's own split). A round-3
  block sees all of round 1, and **both twins pass `ThickLink` against
  it** — `decide` — so no counting argument can separate them, and the
  `∃`-style indirect rule would admit conflicting commits. The
  canonical (least-candidate) rule of `Decided.indirectCommit` is what
  restores agreement; at the slot's *actual* anchor the derivation
  commits the canonical twin.
-/

namespace LeanDagTest

set_option maxRecDepth 2048

open LeanDag LeanDag.Odontoceti

/-! ## The committee and the schedule -/

instance : Faults5 (Fin 6) where
  f := 1
  byzantine := {0}
  card_validators := by simp
  card_byzantine := by decide
  card_validators5 := by simp

instance odoSlots : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 6, by omega⟩)

@[simp]
theorem odoSlots_slotRound (k : ℕ) : odoSlots.slotRound k = k := by
  simp [odoSlots, Slots.uniformSingle_slotRound]

theorem odoSlots_leader (k : ℕ) : odoSlots.leader k = ⟨k % 6, by omega⟩ :=
  rfl

/-! ## `Uodo` — the sunny day -/

/-- Four rounds of six, everyone referencing the whole previous
round. -/
def odoBlk : Fin 24 → Block (Fin 6) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := {0, 1, 2, 3, 4, 5}, payload := () }
  else if h : (i : ℕ) < 18 then
    { round := 2, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := {6, 7, 8, 9, 10, 11}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 18, by have := i.isLt; omega⟩,
      refs := {12, 13, 14, 15, 16, 17}, payload := () }

/-- The reuse claim of `odontoceti.md` §2, as a computation: the
existing `BlockUniverse` accepts the Odontoceti parameters — quorum
`n − f = 5` — with no changes. -/
def Uodo : BlockUniverse (Fin 6) (Fin 24) Unit where
  ids := Finset.univ
  block := odoBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Slot 1's leader block is block 7 (round 1, author 1), supported by
-- the entire round 2: directly committed.
example : IsLeaderBlock Uodo 1 7 := by decide
example : Odontoceti.DirectCommit Uodo 7 1 := by decide

-- And as a decision, from the full view.
example : Odontoceti.Decided Uodo (View.full Uodo) 1 (some 7) :=
  Decided.directCommit (by decide) (by decide)

-- The boundary thresholds, on data: quorum 5, indirect threshold 3.
example : Fintype.card (Fin 6) - Faults.f (Fin 6) = 5 := by decide
example : Fintype.card (Fin 6) - 3 * Faults.f (Fin 6) = 3 := by decide

/-! ## `Uskip` — the decision zoo -/

/-- Six rounds of six. Slot 1 splits 3–3 (undecided), slot 2 splits
2–4 (undecided), slot 3 and slot 4 commit directly, slot 0 commits
directly. Reference sets per block; self-parents throughout. -/
def skipBlk : Fin 36 → Block (Fin 6) (Fin 36) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := if (i : ℕ) = 6 then {0, 1, 2, 3, 4}  -- pinned by self-parent
        else {1, 2, 3, 4, 5},                       -- blames slot 0's leader
      payload := () }
  else if h : (i : ℕ) < 18 then
    { round := 2, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := if (i : ℕ) = 13 ∨ (i : ℕ) = 14 ∨ (i : ℕ) = 15 then
          {6, 7, 8, 9, 10}      -- supports slot 1's leader (block 7)
        else {6, 8, 9, 10, 11},  -- blames it
      payload := () }
  else if h : (i : ℕ) < 24 then
    { round := 3, creator := ⟨(i : ℕ) - 18, by omega⟩,
      refs := if (i : ℕ) = 20 ∨ (i : ℕ) = 21 then
          {12, 13, 14, 15, 16}  -- supports slot 2's leader (block 14)
        else {12, 13, 15, 16, 17},  -- blames it
      payload := () }
  else if h : (i : ℕ) < 30 then
    { round := 4, creator := ⟨(i : ℕ) - 24, by omega⟩,
      refs := {18, 19, 20, 21, 22, 23}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 30, by have := i.isLt; omega⟩,
      refs := {24, 25, 26, 27, 28, 29}, payload := () }

def Uskip : BlockUniverse (Fin 6) (Fin 36) Unit where
  ids := Finset.univ
  block := skipBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Slot 0 (Byzantine leader, block 0): the five correct authors blame
-- it; author 0 itself is pinned to support by its mandatory
-- self-parent. Five blames is exactly the quorum: directly skipped.
example : (blames Uskip 0 1 : Finset (Fin 6)) = {1, 2, 3, 4, 5} := by
  decide
example : Odontoceti.DirectSkip Uskip 0 0 := by decide

/-- **The direct skip, as a decision**: every candidate of slot 0 — the
one block — is blamed by a quorum in the full view. -/
theorem uskip_slot0 :
    Odontoceti.Decided Uskip (View.full Uskip) 0 none :=
  Decided.directSkip (by decide)

-- Slot 1 (leader block 7): three supporters, three blamers — neither
-- direct rule fires.
example : (supporters Uskip 7 2 : Finset (Fin 6)) = {1, 2, 3} := by decide
example : ¬ Odontoceti.DirectCommit Uskip 7 1 := by decide
example : ¬ Odontoceti.DirectSkip Uskip 7 1 := by decide

-- Slot 3 (leader block 21) commits directly: the whole round 4
-- references it.
theorem uskip_slot3 :
    Odontoceti.Decided Uskip (View.full Uskip) 3 (some 21) :=
  Decided.directCommit (by decide) (by decide)

-- The anchor's cone carries exactly the threshold: `ThickLink` at 3.
example : (coneSupports Uskip 21 7 1 : Finset (Fin 6)) = {1, 2, 3} := by
  decide
example : Odontoceti.ThickLink Uskip 21 7 1 := by decide

/-- **The indirect commit, on data**: slot 1 is undecided by the direct
rules and committed through the slot-3 anchor — the nearest eligible
one, with nothing eligible between. -/
theorem uskip_slot1 :
    Odontoceti.Decided Uskip (View.full Uskip) 1 (some 7) := by
  refine Decided.indirectCommit (i := 0) (by omega) (by decide) uskip_slot3
    ?_ (by decide) (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 2 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro L' hL' ht' hlt
    have hall : ∀ M : Fin 36, IsLeaderBlock Uskip 1 M → M = 7 := by decide
    have := hall L' hL'
    subst this
    exact absurd (show (7 : Fin 36) < 7 from hlt) (lt_irrefl _)

-- Slot 2 (leader block 14): two supporters, four blamers — undecided,
-- and two supporters cannot reach the threshold in **any** cone.
example : (supporters Uskip 14 3 : Finset (Fin 6)) = {2, 3} := by decide
example : ¬ Odontoceti.DirectCommit Uskip 14 2 := by decide
example : ¬ Odontoceti.DirectSkip Uskip 14 2 := by decide

-- Slot 4 (leader block 28) commits directly…
theorem uskip_slot4 :
    Odontoceti.Decided Uskip (View.full Uskip) 4 (some 28) :=
  Decided.directCommit (by decide) (by decide)

/-- **The indirect skip, on data**: slot 2, anchored on slot 4, has no
candidate passing the indirect test. -/
theorem uskip_slot2 :
    Odontoceti.Decided Uskip (View.full Uskip) 2 none := by
  refine Decided.indirectSkip (by omega) (by decide) uskip_slot4 ?_ ?_
  · intro i h1 h2 h3
    have : i = 3 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 36, IsLeaderBlock Uskip 2 M → M = 14 := by decide
    have := hall L hL
    subst this
    show ¬ Odontoceti.ThickLink _ _ _ _
    decide

/-! ## `Utwin6` — the thesis gap, on data -/

/-- Byzantine validator 0 equivocates at round 0: blocks `0` and `6`
are twins. Supporters split three and three — disjoint correct pairs
plus the equivocator on each side. -/
def twinBlk : Fin 25 → Block (Fin 6) (Fin 25) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) = 6 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if h : (i : ℕ) < 13 then
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩,
      refs := if (i : ℕ) ≤ 9 then {0, 1, 2, 3, 4}    -- supports twin 0
        else if (i : ℕ) ≤ 11 then {6, 1, 2, 3, 4}     -- supports twin 6
        else {6, 1, 2, 3, 5},                          -- supports twin 6
      payload := () }
  else if h : (i : ℕ) < 19 then
    { round := 2, creator := ⟨(i : ℕ) - 13, by omega⟩,
      refs := if (i : ℕ) = 18 then {8, 9, 10, 11, 12}
        else {7, 8, 9, 10, 11},
      payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 19, by have := i.isLt; omega⟩,
      refs := {13, 14, 15, 16, 17, 18}, payload := () }

def Utwin6 : BlockUniverse (Fin 6) (Fin 25) Unit where
  ids := Finset.univ
  block := twinBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The split: each twin has exactly three supporters, so neither
-- direct rule fires for either.
example : (supporters Utwin6 0 1 : Finset (Fin 6)) = {0, 1, 2} := by decide
example : (supporters Utwin6 6 1 : Finset (Fin 6)) = {3, 4, 5} := by decide
example : ¬ Odontoceti.DirectCommit Utwin6 0 0 := by decide
example : ¬ Odontoceti.DirectSkip Utwin6 0 0 := by decide

/-- **The gap (thesis Lemma 5's silent step), realised**: block 19 sees
all of round 1, and **both** equivocating twins pass the indirect test
against it. No counting argument separates them; an `∃`-style indirect
rule would admit conflicting commits, and only the canonical choice
restores agreement. -/
theorem utwin6_both_pass :
    Odontoceti.ThickLink Utwin6 19 0 0 ∧
      Odontoceti.ThickLink Utwin6 19 6 0 := by
  constructor <;> decide

-- At the slot's *actual* anchor — slot 2, the first eligible committed
-- slot — only twin 0 passes (block 15's cone misses author 5's support
-- of twin 6)…
theorem utwin6_slot2 :
    Odontoceti.Decided Utwin6 (View.full Utwin6) 2 (some 15) :=
  Decided.directCommit (by decide) (by decide)

example : Odontoceti.ThickLink Utwin6 15 0 0 := by decide
example : ¬ Odontoceti.ThickLink Utwin6 15 6 0 := by decide

/-- …and the derivation commits the canonical twin. -/
theorem utwin6_slot0 :
    Odontoceti.Decided Utwin6 (View.full Utwin6) 0 (some 0) := by
  refine Decided.indirectCommit (i := 0) (by omega) (by decide) utwin6_slot2
    ?_ (by decide) (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 1 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro L' hL' ht' hlt
    have hall : ∀ M : Fin 25, IsLeaderBlock Utwin6 0 M → M = 0 ∨ M = 6 := by
      decide
    rcases hall L' hL' with h | h <;> subst h
    · exact absurd (show (0 : Fin 25) < 0 from hlt) (lt_irrefl _)
    · exact absurd (show Odontoceti.ThickLink _ _ _ _ from ht') (by decide)

/-! ## Liveness on data -/

private theorem uodo_round_le : ∀ b : Fin 24, (Uodo.block b).round ≤ 3 := by
  decide

theorem uodo_populated (r : ℕ) (h : r ≤ 3) : Populated Uodo r := by
  interval_cases r <;> decide

theorem uodo_synchronised : Synchronised Uodo 0 := by
  intro n _ b hb hbr hbc a ha har hac
  by_cases hn : n ≤ 2
  · revert b hb hbr hbc a ha har hac
    interval_cases n <;> decide
  · exfalso
    have := uodo_round_le b
    omega

/-- **O7 applied**: slot 2's leader commits directly from two populated
rounds and one synchronised step. -/
example : ∃ L, IsLeaderBlock Uodo 2 L ∧
    Odontoceti.Decided Uodo (View.full Uodo) 2 (some L) :=
  Odontoceti.decided_of_correct_leader (R := 0) uodo_synchronised
    (by simp) (by simpa using uodo_populated 2 (by omega))
    (by simpa using uodo_populated 3 (by omega))
    (View.full Uodo) (View.coversUpto_full Uodo _) (by decide)

/-- **O8 applied**: the pipelined identity schedule spans at `c = 2`. -/
example : (Odontoceti.odontocetiAnchored (Fin 6) (Fin 36) Unit).SpansEligible 2 :=
  (Odontoceti.odontocetiAnchored (Fin 6) (Fin 36) Unit).spansEligible_of_identity
    odoSlots_slotRound (fun _ => le_rfl)

/-- **O9 applied**: slots 3 and 4 of `Uskip` are a committed run of
two, and every slot below is decided. -/
example : ∀ i, i < 3 → ∃ v,
    Odontoceti.Decided Uskip (View.full Uskip) i v :=
  AnchoredRule.decided_below_of_committed_run (fun hi h => Odontoceti.exists_least hi h)
    (b := 3) (n := 4) (by omega)
    (fun i hi => by
      rw [(Odontoceti.odontocetiAnchored (Fin 6) (Fin 36) Unit).eligible_iff]
      simp
      omega)
    (fun j hj1 hj2 => by
      interval_cases j
      · exact ⟨21, uskip_slot3⟩
      · exact ⟨28, uskip_slot4⟩)

#print axioms LeanDag.AnchoredRule.decided_unique
#print axioms LeanDag.OdontocetiProperties.safety
#print axioms Odontoceti.all_decided_below_of_fairRun
#print axioms utwin6_both_pass
#print axioms uskip_slot1

end LeanDagTest
