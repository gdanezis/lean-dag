import LeanDag.Common.Density
/-!
# Exclusion, over the raw block data

`dos-equivocation-and-growth.md` §4, D17, D27 and D28. An exposure is a test
of a block for an author that a block passes whenever one of its
references does (`InheritedOn`): twins in the history are one, evidence of
an equivocation carried by a block of the history another. Under the
matching DoS condition (`DoSValidOn`), a block may not reference an author
it exposes. Once every reliable block of a round exposes `X`, so does every
later block, since each references a reliable block one round below; no
block from one round up names `X` (D17), no block of a history from the
round up other than its top is by `X` (D27), and a union of histories holds
at most one block a round for each author not exposed (D28).
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}
variable {rel : Reliability Validator} {Exp : BlockId → Validator → Prop}

/-- **An exposure carried upward**: a block passes the test for `X` whenever
one of its references does. -/
def InheritedOn (blk : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (Exp : BlockId → Validator → Prop) : Prop :=
  ∀ b ∈ ids, ∀ i ∈ (blk b).refs, ∀ X, Exp i X → Exp b X

/-- **DoS validity for an exposure `Exp`**: no block references an author it
exposes. -/
def DoSValidOn (blk : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (Exp : BlockId → Validator → Prop) : Prop :=
  ∀ b ∈ ids, ∀ i ∈ (blk b).refs, ¬ Exp b (blk i).creator

/-- **D17 — exclusion is total, and permanent.** If every reliable block of
round `n+1` exposes `X`, so does every block from round `n+2` on, whoever
authored it. -/
theorem exposed_of_correct_exposed (C : CausalStructure blk ids) (hq : QuorateOn blk ids rel)
    (hup : InheritedOn blk ids Exp) {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ ids, (blk c).round = n + 1 → (blk c).creator ∈ rel.correct → Exp c X) :
    ∀ k, ∀ b ∈ ids, (blk b).round = n + 2 + k → Exp b X := by
  intro k
  induction k with
  | zero =>
      intro b hb hbr
      obtain ⟨i, hi, hi_ids, hi_correct, hi_round⟩ := exists_correct_memRefs C hq hb (by omega)
      exact hup b hb i hi X (hexp i hi_ids (by omega) hi_correct)
  | succ k ih =>
      intro b hb hbr
      obtain ⟨i, hi, hi_ids, _, hi_round⟩ := exists_correct_memRefs C hq hb (by omega)
      exact hup b hb i hi X (ih i hi_ids (by omega))

/-- The form the condition consumes: from `n+2` on, nobody may name `X`. -/
theorem not_mem_creators_refs_of_correct_exposed (C : CausalStructure blk ids)
    (hq : QuorateOn blk ids rel) (hdos : DoSValidOn blk ids Exp) (hup : InheritedOn blk ids Exp)
    {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ ids, (blk c).round = n + 1 → (blk c).creator ∈ rel.correct → Exp c X)
    {b : BlockId} (hb : b ∈ ids) (hbr : n + 2 ≤ (blk b).round) :
    X ∉ creatorsOf blk (blk b).refs := by
  obtain ⟨k, hk⟩ : ∃ k, (blk b).round = n + 2 + k := ⟨(blk b).round - (n + 2), by omega⟩
  intro hX
  obtain ⟨i, hi, rfl⟩ := mem_creatorsOf.mp hX
  exact hdos b hb i hi (exposed_of_correct_exposed C hq hup hexp k b hb hk)

variable [DecidableEq BlockId]

/-- **D27 — a history names no exposed author from the exposure up.** Once
every reliable block of round `n+1` exposes `X`, no block of a history at
round `n+1` or above other than its top is by `X`. -/
theorem creator_ne_of_correct_exposed (C : CausalStructure blk ids) (hq : QuorateOn blk ids rel)
    (hdos : DoSValidOn blk ids Exp) (hup : InheritedOn blk ids Exp) {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ ids, (blk c).round = n + 1 → (blk c).creator ∈ rel.correct → Exp c X)
    {b i : BlockId} (hb : b ∈ ids) (hi : i ∈ historyFrom blk b) (hne : i ≠ b)
    (hir : n + 1 ≤ (blk i).round) : (blk i).creator ≠ X := by
  obtain ⟨j, hj, hij⟩ := C.exists_mem_refs_of_mem_history hb hi hne
  have hj_ids := C.history_subset_ids hb hj
  have hjr := C.refs_round j hj_ids i hij
  intro hX
  exact not_mem_creators_refs_of_correct_exposed C hq hdos hup hexp hj_ids (by omega)
    (mem_creatorsOf.mpr ⟨i, hij, hX⟩)

/-- **D28 — one block a round for each author not exposed.** Let every
reliable block of round `n+1` expose each author of `E`, and let `S` be the
union of the histories of the blocks `B`. If no author outside `E` has two
blocks of `S` at round `k ≥ n+1`, then `S` holds at most one block of round
`k` for each author outside `E`, besides the blocks of `B` by authors of
`E`. -/
theorem card_union_history_round_le (C : CausalStructure blk ids) (hq : QuorateOn blk ids rel)
    (hdos : DoSValidOn blk ids Exp) (hup : InheritedOn blk ids Exp) {E : Finset Validator}
    {n k : ℕ}
    (hexp : ∀ X ∈ E, ∀ c ∈ ids, (blk c).round = n + 1 → (blk c).creator ∈ rel.correct →
      Exp c X)
    {B : Finset BlockId} (hB : B ⊆ ids) (hk : n + 1 ≤ k)
    (htw : ∀ i ∈ B.biUnion (historyFrom blk), ∀ j ∈ B.biUnion (historyFrom blk),
      (blk i).round = k → (blk j).round = k →
      (blk i).creator = (blk j).creator → (blk i).creator ∉ E → i = j) :
    ((B.biUnion (historyFrom blk)).filter fun i => (blk i).round = k).card ≤
      (Fintype.card Validator - E.card) +
        (B.filter fun t => (blk t).creator ∈ E ∧ (blk t).round = k).card := by
  classical
  set S := (B.biUnion (historyFrom blk)).filter fun i => (blk i).round = k with hS
  have hsplit : S ⊆ (S.filter fun i => (blk i).creator ∉ E) ∪
      (B.filter fun t => (blk t).creator ∈ E ∧ (blk t).round = k) := by
    intro i hi
    obtain ⟨hiu, hir⟩ := Finset.mem_filter.mp hi
    by_cases hiE : (blk i).creator ∈ E
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hiE, hir⟩)
      obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp hiu
      by_contra hiB
      exact creator_ne_of_correct_exposed C hq hdos hup (hexp _ hiE) (hB ht) hit
        (fun h => hiB (h ▸ ht)) (by omega) rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hiE⟩)
  refine (Finset.card_le_card hsplit).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _))
  rw [← Finset.card_compl]
  refine Finset.card_le_card_of_injOn (fun i => (blk i).creator) ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter] at hi
    exact Finset.mem_coe.mpr (Finset.mem_compl.mpr hi.2)
  · intro i hi j hj h
    rw [Finset.mem_coe, Finset.mem_filter, hS, Finset.mem_filter] at hi hj
    exact htw i hi.1.1 j hj.1.1 hi.1.2 hj.1.2 h hi.2

end LeanDag
