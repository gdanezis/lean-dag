import LeanDag.Scheme.Helpers.Restart
import LeanDag.Common.Ledger
/-!
# The loop's output is the ledger

`tryDecide` lists slots with the loop's assignment `loopAssign N`
(`tryDecide_eq_map`). From slot `0`, its committed blocks are
`commitSeq (loopAssign N)` over its length, the blocks they reach are
`ledgerSet` over its length, and every slot below its length is decided
by the relation with that verdict, which the agreement theorems of
`Common/Anchored.lean` read (`ledger_read`). Prefix-comparable outputs
give two validators prefix-comparable commit sequences and nested
ledgers (`ledger_agree`).
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} [S : Slots Validator]
variable {U : BlockRecord Validator BlockId Payload P honest} {V : U.View}

omit [Fintype Validator] in
/-- Every output entry is its slot with the loop's assignment. -/
theorem tryDecide_entry {lo N : ℕ} (hlo : lo ≤ N + 1) :
    ∀ e ∈ tryDecide p σ U V lo N, e.2 = loopAssign p σ U V N e.1 := by
  intro e he
  rw [tryDecide_eq hlo] at he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ((List.takeWhile_sublist _).subset ht)
  rfl

/-- **The output lists its slots with the loop's assignment.** -/
theorem tryDecide_eq_map (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {lo N : ℕ} (hlo : lo ≤ N + 1) :
    tryDecide p σ U V lo N = (List.range' lo (tryDecide p σ U V lo N).length).map
      (fun k => (k, loopAssign p σ U V N k)) := by
  rw [← (tryDecide_sound (σ := σ) (U := U) (V := V) hl hc hlo).1, List.map_map]
  conv_lhs => rw [← List.map_id (tryDecide p σ U V lo N)]
  exact List.map_congr_left fun e he => Prod.ext rfl (tryDecide_entry hlo e he)

/-- **The output from slot `0` is the ledger**: its committed blocks are
`commitSeq` of the loop's assignment, every slot below its length is
decided with the assignment's verdict, and the blocks its commits reach
are `ledgerSet`. -/
theorem ledger_read (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    (N : ℕ) :
    (tryDecide p σ U V 0 N).filterMap Prod.snd =
        commitSeq (loopAssign p σ U V N) (tryDecide p σ U V 0 N).length ∧
      (∀ k, k < (tryDecide p σ U V 0 N).length →
        (schemeAnchored p σ).Decided U V k (loopAssign p σ U V N k)) ∧
      ledgerSet U (loopAssign p σ U V N) (tryDecide p σ U V 0 N).length =
        {b | ∃ e ∈ tryDecide p σ U V 0 N, ∃ L, e.2 = some L ∧ Reaches U L b} := by
  have hmap := tryDecide_eq_map (σ := σ) (U := U) (V := V) hl hc (lo := 0) (N := N) (by omega)
  have hmem : ∀ k, k < (tryDecide p σ U V 0 N).length →
      (k, loopAssign p σ U V N k) ∈ tryDecide p σ U V 0 N := fun k hk => by
    rw [hmap]
    exact List.mem_map.mpr ⟨k, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩
  refine ⟨?_, fun k hk => (tryDecide_sound hl hc (by omega)).2 _ (hmem k hk), ?_⟩
  · conv_lhs => rw [hmap]
    rw [List.filterMap_map, commitSeq, List.range_eq_range']
    rfl
  · ext b
    constructor
    · rintro ⟨k, hk, L, hL, hr⟩
      exact ⟨_, hmem k hk, L, hL, hr⟩
    · rintro ⟨e, he, L, hL, hr⟩
      have he' := he
      rw [hmap] at he'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he'
      exact ⟨k, by simpa using (List.mem_range'_1.mp hk).2, L, hL, hr⟩

/-- **Two validators' ledgers are nested**, when the rule has its laws:
their commit sequences are prefix-comparable and one ledger contains the
other. -/
theorem ledger_agree (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hlaws : (schemeAnchored p σ).Laws I) (hI : I S U) (V₁ V₂ : U.View) (N₁ N₂ : ℕ) :
    (commitSeq (loopAssign p σ U V₁ N₁) (tryDecide p σ U V₁ 0 N₁).length <+:
        commitSeq (loopAssign p σ U V₂ N₂) (tryDecide p σ U V₂ 0 N₂).length ∧
      ledgerSet U (loopAssign p σ U V₁ N₁) (tryDecide p σ U V₁ 0 N₁).length ⊆
        ledgerSet U (loopAssign p σ U V₂ N₂) (tryDecide p σ U V₂ 0 N₂).length) ∨
    (commitSeq (loopAssign p σ U V₂ N₂) (tryDecide p σ U V₂ 0 N₂).length <+:
        commitSeq (loopAssign p σ U V₁ N₁) (tryDecide p σ U V₁ 0 N₁).length ∧
      ledgerSet U (loopAssign p σ U V₂ N₂) (tryDecide p σ U V₂ 0 N₂).length ⊆
        ledgerSet U (loopAssign p σ U V₁ N₁) (tryDecide p σ U V₁ 0 N₁).length) := by
  obtain ⟨c₁, -, s₁⟩ := ledger_read (σ := σ) (U := U) (V := V₁) hl hc N₁
  obtain ⟨c₂, -, s₂⟩ := ledger_read (σ := σ) (U := U) (V := V₂) hl hc N₂
  rw [← c₁, ← c₂, s₁, s₂]
  rcases tryDecide_prefix hl hc hlaws hI (lo := 0) (by omega) (by omega) V₁ V₂ with h | h
  · exact Or.inl ⟨h.filterMap _, fun b ⟨e, he, hrest⟩ => ⟨e, h.subset he, hrest⟩⟩
  · exact Or.inr ⟨h.filterMap _, fun b ⟨e, he, hrest⟩ => ⟨e, h.subset he, hrest⟩⟩

end Scheme

end LeanDag
