import LeanDag.Network.Delivery
import LeanDag.DoS.Acceptance
import LeanDag.DoS.Exposure
/-!
# Counting blocks

`dos-equivocation-and-growth.md` §5, results D5, D6, D19a and D19b. Three
of the four bounds are one lemma applied to different sets: an
equivocation-free set spanning rounds `0…r` holds at most `(3f+1)(r+1)`
blocks (`card_le_of_equivFree`), read at a view (D5) and at a history
(D19a). D6 goes the other way and needs L0. D19b is the sharpest tool the
DoS condition gives: an author a block references contributes at most
one block per round to its history.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {s : Finset BlockId} {b : BlockId} {X : Validator} {m n r : ℕ}

/-! ## Equivocation-freedom, and the general bound -/

/-- The blocks of `s` at round `n`. Generalises `blocksAt`, which is this at
`s := U.ids`. -/
def atRound (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) (n : ℕ) :
    Finset BlockId :=
  s.filter (fun i => (U.block i).round = n)

omit [DecidableEq BlockId] in
@[simp]
theorem mem_atRound {i : BlockId} : i ∈ atRound U s n ↔ i ∈ s ∧ (U.block i).round = n := by
  simp [atRound]

omit [DecidableEq BlockId] in
theorem blocksAt_eq_atRound : blocksAt U n = atRound U U.ids n := rfl

/-- No two distinct blocks of `s` share an author and a round — a property
of the set, not of the universe. -/
def EquivFree (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j

/-- Decidable on concrete data, so a model can settle it by `decide`. -/
instance decidableEquivFree (U : BlockUniverse Validator BlockId Payload)
    (s : Finset BlockId) [DecidableEq BlockId] : Decidable (EquivFree U s) :=
  inferInstanceAs (Decidable (∀ i ∈ s, ∀ j ∈ s, (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j))

omit [DecidableEq BlockId] in
theorem EquivFree.subset {t : Finset BlockId} (h : EquivFree U t) (hsub : s ⊆ t) :
    EquivFree U s :=
  fun i hi j hj => h i (hsub hi) j (hsub hj)

omit [DecidableEq BlockId] in
/-- One round of an equivocation-free set has at most one block per validator,
so at most `3f+1` blocks. -/
theorem card_atRound_le (h : EquivFree U s) (n : ℕ) : (atRound U s n).card ≤ Fintype.card Validator := by
  have hinj : Set.InjOn (fun i => (U.block i).creator) (atRound U s n) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, mem_atRound] at hi hj
    exact h i hi.1 j hj.1 hij (by rw [hi.2, hj.2])
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_univ _

/-- **The general counting bound.** An equivocation-free set spanning rounds
`0…r` holds at most `(3f+1)(r+1)` blocks. -/
theorem card_le_of_equivFree (h : EquivFree U s) (hr : ∀ i ∈ s, (U.block i).round ≤ r) :
    s.card ≤ (Fintype.card Validator) * (r + 1) := by
  have hsub : s ⊆ (Finset.range (r + 1)).biUnion (atRound U s) := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨(U.block i).round,
      Finset.mem_range.mpr (by have := hr i hi; omega), mem_atRound.mpr ⟨hi, rfl⟩⟩
  calc s.card
      ≤ ((Finset.range (r + 1)).biUnion (atRound U s)).card := Finset.card_le_card hsub
    _ ≤ ∑ n ∈ Finset.range (r + 1), (atRound U s n).card := Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ Finset.range (r + 1), (Fintype.card Validator) :=
        Finset.sum_le_sum fun n _ => card_atRound_le h n
    _ = (r + 1) * (Fintype.card Validator) := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_range]
    _ = (Fintype.card Validator) * (r + 1) := Nat.mul_comm _ _

/-! ## D5 — a view without equivocation -/

/-- **D5.** A view whose blocks reach no higher than round `r`, and which
holds no equivocation, holds at most `(3f+1)(r+1)` blocks. -/
theorem View.card_le_of_equivFree {V : View Validator BlockId Payload U}
    (h : EquivFree U V.ids) (hr : ∀ i ∈ V.ids, (U.block i).round ≤ r) :
    V.ids.card ≤ (Fintype.card Validator) * (r + 1) :=
  _root_.LeanDag.card_le_of_equivFree h hr

/-! ## D19a — a history without equivocation: `ExposedIn` and `EquivFree`
are the same condition, stated per author and per pair. -/

theorem equivFree_history_iff :
    EquivFree U (history U b) ↔ ∀ X, ¬ ExposedIn U b X := by
  constructor
  · rintro h X ⟨i, hi, j, hj, hne, hic, hjc, hround⟩
    exact hne (h i hi j hj (by rw [hic, hjc]) hround)
  · intro h i hi j hj hcreator hround
    by_contra hne
    exact h (U.block i).creator ⟨i, hi, j, hj, hne, rfl, hcreator.symm, hround⟩

/-- **D19a.** A history exposing nobody is linear in the round: at most
`(3f+1)(r+1)` blocks, which is the no-equivocation baseline of D5 again. -/
theorem card_history_le_of_not_exposed (hb : b ∈ U.ids) (h : ∀ X, ¬ ExposedIn U b X) :
    (history U b).card ≤ (Fintype.card Validator) * ((U.block b).round + 1) :=
  card_le_of_equivFree (equivFree_history_iff.mpr h)
    fun _ hi => round_le_of_mem_history hb hi

/-! ## D19b — a block is clean about what it references -/

/-- An author not exposed in `b`'s history contributes at most one block per
round to it, hence at most `round b + 1` in all. -/
theorem card_filter_creator_le (hb : b ∈ U.ids) (h : ¬ ExposedIn U b X) :
    ((history U b).filter (fun j => (U.block j).creator = X)).card ≤ (U.block b).round + 1 := by
  have hone := not_exposedIn_iff_card_le_one.mp h
  have hsub : (history U b).filter (fun j => (U.block j).creator = X) ⊆
      (Finset.range ((U.block b).round + 1)).biUnion (historyBlocksOf U b X) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact Finset.mem_biUnion.mpr ⟨(U.block j).round,
      Finset.mem_range.mpr (by have := round_le_of_mem_history hb hj.1; omega),
      mem_historyBlocksOf.mpr ⟨hj.1, hj.2, rfl⟩⟩
  calc ((history U b).filter (fun j => (U.block j).creator = X)).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ n ∈ Finset.range ((U.block b).round + 1), (historyBlocksOf U b X n).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ Finset.range ((U.block b).round + 1), 1 :=
        Finset.sum_le_sum fun n _ => hone n
    _ = (U.block b).round + 1 := by
        rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_range, Nat.mul_one]

/-- **D19b.** Under the DoS condition, an author a block *references*
contributes at most `round b + 1` blocks to that block's history. -/
theorem card_filter_creator_le_of_mem_refs (hdos : DoSValid U) (hb : b ∈ U.ids)
    {i : BlockId} (hi : i ∈ (U.block b).refs) :
    ((history U b).filter (fun j => (U.block j).creator = (U.block i).creator)).card
      ≤ (U.block b).round + 1 :=
  card_filter_creator_le hb (hdos b hb i hi)

/-! ## D6 — the lower bound: grows with the round rather than bounding it,
from L0 and validity alone, no equivocation involved. -/

omit [DecidableEq BlockId] in
/-- Authors are the image of blocks, so a round has at least as many blocks as
authors. -/
theorem card_authorsAt_le_card_blocksAt : (authorsAt U n).card ≤ (blocksAt U n).card :=
  Finset.card_image_le

omit [DecidableEq BlockId] in
/-- Distinct rounds hold disjoint blocks: a block sits at one round. -/
theorem blocksAt_disjoint (h : m ≠ n) : Disjoint (blocksAt U m) (blocksAt U n) := by
  rw [Finset.disjoint_left]
  intro i him hin
  exact h ((mem_blocksAt.mp him).2.symm.trans (mem_blocksAt.mp hin).2)

omit [DecidableEq BlockId] in
/-- L0 in blocks rather than authors. -/
theorem card_blocksAt_of_lt (hn : n < r) {i : BlockId} (hi : i ∈ U.ids)
    (hir : (U.block i).round = r) : quorumCard Validator ≤ (blocksAt U n).card :=
  le_trans (card_authorsAt_of_lt hn hi hir) card_authorsAt_le_card_blocksAt

/-- **D6.** A universe holding a block at round `r` holds at least
`(n−f)·r + 1` blocks: `2f+1` at every round strictly below `r`, by L0, and
the block itself. -/
theorem card_ids_ge_of_round {i : BlockId} (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    (quorumCard Validator) * r + 1 ≤ U.ids.card := by
  have hsub : (Finset.range (r + 1)).biUnion (fun n => blocksAt U n) ⊆ U.ids := by
    intro j hj
    obtain ⟨n, -, hjn⟩ := Finset.mem_biUnion.mp hj
    exact (mem_blocksAt.mp hjn).1
  have hcard : ((Finset.range (r + 1)).biUnion (fun n => blocksAt U n)).card
      = ∑ n ∈ Finset.range (r + 1), (blocksAt U n).card :=
    Finset.card_biUnion fun _ _ _ _ hmn => blocksAt_disjoint hmn
  have hle := Finset.card_le_card hsub
  rw [hcard, Finset.sum_range_succ] at hle
  have hlow : (quorumCard Validator) * r ≤ ∑ n ∈ Finset.range r, (blocksAt U n).card := by
    calc (quorumCard Validator) * r = ∑ _n ∈ Finset.range r, (quorumCard Validator) := by
          rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_range, Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun n hn =>
          card_blocksAt_of_lt (Finset.mem_range.mp hn) hi hir
  have hone : 1 ≤ (blocksAt U r).card :=
    Finset.card_pos.mpr ⟨i, mem_blocksAt.mpr ⟨hi, hir⟩⟩
  omega

/-- The bounds together, on a universe with no equivocation at all: linear in
the round from both sides. -/
theorem card_ids_bounds (h : EquivFree U U.ids) {i : BlockId} (hi : i ∈ U.ids)
    (hir : (U.block i).round = r) (hmax : ∀ j ∈ U.ids, (U.block j).round ≤ r) :
    (quorumCard Validator) * r + 1 ≤ U.ids.card ∧ U.ids.card ≤ (Fintype.card Validator) * (r + 1) :=
  ⟨card_ids_ge_of_round hi hir, card_le_of_equivFree h hmax⟩

end LeanDag
