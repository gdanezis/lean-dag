import LeanDag.DoS.Exposure
import Mathlib.Data.Finset.Prod

/-!
# Self-parent chains, and what a reference costs

`dos-equivocation-and-growth.md` §5, results D20-D24. The self-parent
condition says a non-genesis block references some block by its own
creator. D20 says chains are contiguous to the ground: a block by an
author at every round down to 0. D21 says no block is exposed to its own
author, so equivocation cannot be laundered through one's own later
blocks. D22/D23 give the exact cost of a reference: naming an author at
round `r` puts exactly one block of that author at every round below
into the history. D24 is the floor: a valid block at round `r` carries
at least `(n−f)·r + 1` blocks. Together D21-D23 close the laundering gap
that made C1′ false without the condition.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

private theorem exists_self_ancestor_aux (n : ℕ) :
    ∀ {b : BlockId}, b ∈ U.ids → ∀ {t : ℕ}, t + n = (U.block b).round →
      ∃ i ∈ history U b,
        (U.block i).creator = (U.block b).creator ∧ (U.block i).round = t := by
  induction n with
  | zero =>
      intro b _ t ht
      exact ⟨b, mem_history_self, rfl, by omega⟩
  | succ n ih =>
      intro b hb t ht
      obtain ⟨p, hp, hpc⟩ := (U.valid b hb).self_parent (by omega)
      have hp_ids : p ∈ U.ids := U.complete b hb p hp
      have hp_round := U.round_of_mem_refs hb hp
      obtain ⟨i, hi, hic, hir⟩ := ih hp_ids (t := t) (by omega)
      exact ⟨i, history_subset_of_reaches hb (Reaches.single hp) hi,
        by rw [hic, hpc], hir⟩

/-- **D20 (chains reach the ground).** A block's history holds a block by
its own author at every round below it. -/
theorem exists_self_ancestor {b : BlockId} (hb : b ∈ U.ids) {t : ℕ}
    (ht : t ≤ (U.block b).round) :
    ∃ i ∈ history U b,
      (U.block i).creator = (U.block b).creator ∧ (U.block i).round = t :=
  exists_self_ancestor_aux ((U.block b).round - t) hb (by omega)

/-- **D21 (no self-laundering).** Under the DoS condition no valid block
is exposed to its own author: once an author's equivocation is visible
in some history, that author can never build on that history again. -/
theorem not_exposedIn_self_creator (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ¬ ExposedIn U b (U.block b).creator := by
  rcases Nat.eq_zero_or_pos (U.block b).round with h0 | hpos
  · exact not_exposedIn_of_round_le_one hb (by omega)
  · obtain ⟨p, hp, hpc⟩ := (U.valid b hb).self_parent hpos
    exact hpc ▸ hdos b hb p hp

/-- **D22, per round.** A block's own author sits in its history exactly
once per round: at least once by D20, at most once by D21 and D11. -/
theorem card_historyBlocksOf_self (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {t : ℕ} (ht : t ≤ (U.block b).round) :
    (historyBlocksOf U b (U.block b).creator t).card = 1 := by
  refine le_antisymm
    (not_exposedIn_iff_card_le_one.mp (not_exposedIn_self_creator hdos hb) t) ?_
  obtain ⟨i, hi, hic, hir⟩ := exists_self_ancestor hb ht
  exact Finset.card_pos.mpr ⟨i, mem_historyBlocksOf.mpr ⟨hi, hic, hir⟩⟩

/-- **D23, per round.** Referencing a block puts its author into the
history exactly once per round strictly below: `≤` from the DoS
condition, `≥` from the referenced block's own chain (D20). -/
theorem card_historyBlocksOf_of_mem_refs (hdos : DoSValid U) {b p : BlockId}
    (hb : b ∈ U.ids) (hp : p ∈ (U.block b).refs) {t : ℕ}
    (ht : t < (U.block b).round) :
    (historyBlocksOf U b (U.block p).creator t).card = 1 := by
  have hp_ids : p ∈ U.ids := U.complete b hb p hp
  have hp_round := U.round_of_mem_refs hb hp
  refine le_antisymm (not_exposedIn_iff_card_le_one.mp (hdos b hb p hp) t) ?_
  obtain ⟨i, hi, hic, hir⟩ := exists_self_ancestor hp_ids (t := t) (by omega)
  exact Finset.card_pos.mpr ⟨i, mem_historyBlocksOf.mpr
    ⟨history_subset_of_reaches hb (Reaches.single hp) hi, hic, hir⟩⟩

/-- **D22, totalled.** The own-author content of a history is exactly
`round + 1` blocks. -/
theorem card_filter_self_creator (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ((history U b).filter fun i => (U.block i).creator = (U.block b).creator).card
      = (U.block b).round + 1 := by
  rw [← Finset.card_range ((U.block b).round + 1)]
  refine Finset.card_bij (fun i _ => (U.block i).round) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_range]
    have := round_le_of_mem_history hb hi.1
    omega
  · intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    have h1 := not_exposedIn_iff_card_le_one.mp
      (not_exposedIn_self_creator hdos hb) (U.block i).round
    rw [Finset.card_le_one] at h1
    exact h1 i (mem_historyBlocksOf.mpr ⟨hi.1, hi.2, rfl⟩)
      j (mem_historyBlocksOf.mpr ⟨hj.1, hj.2, hij.symm⟩)
  · intro t ht
    rw [Finset.mem_range] at ht
    obtain ⟨i, hi, hic, hir⟩ := exists_self_ancestor hb (t := t) (by omega)
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hic⟩, hir⟩

/-- **D23, totalled.** For any other author the block references, the
cost is exactly `round` blocks: one clean chain, in full. -/
theorem card_filter_creator_of_mem_refs (hdos : DoSValid U) {b p : BlockId}
    (hb : b ∈ U.ids) (hp : p ∈ (U.block b).refs)
    (hne : (U.block p).creator ≠ (U.block b).creator) :
    ((history U b).filter fun i => (U.block i).creator = (U.block p).creator).card
      = (U.block b).round := by
  rw [← Finset.card_range (U.block b).round]
  refine Finset.card_bij (fun i _ => (U.block i).round) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_range]
    have hle := round_le_of_mem_history hb hi.1
    rcases Nat.lt_or_ge (U.block i).round (U.block b).round with h | h
    · exact h
    · exfalso
      have hib : i = b := eq_of_mem_history_of_round_eq hb hi.1 (by omega)
      subst hib
      exact hne hi.2.symm
  · intro i hi j hj hij
    rw [Finset.mem_filter] at hi hj
    have h1 := not_exposedIn_iff_card_le_one.mp (hdos b hb p hp) (U.block i).round
    rw [Finset.card_le_one] at h1
    exact h1 i (mem_historyBlocksOf.mpr ⟨hi.1, hi.2, rfl⟩)
      j (mem_historyBlocksOf.mpr ⟨hj.1, hj.2, hij.symm⟩)
  · intro t ht
    rw [Finset.mem_range] at ht
    have hp_ids : p ∈ U.ids := U.complete b hb p hp
    have hp_round := U.round_of_mem_refs hb hp
    obtain ⟨i, hi, hic, hir⟩ := exists_self_ancestor hp_ids (t := t) (by omega)
    exact ⟨i, Finset.mem_filter.mpr
      ⟨history_subset_of_reaches hb (Reaches.single hp) hi, hic⟩, hir⟩

/-- **D24 (the floor).** With self-parents, a valid block at round `r`
carries at least `(n−f)·r + 1` blocks — a full chain for each of its
quorum of referenced authors, plus itself. Needs no DoS hypothesis. -/
theorem card_history_ge {b : BlockId} (hb : b ∈ U.ids) (h0 : 0 < (U.block b).round) :
    (quorumCard Validator) * (U.block b).round + 1 ≤ (history U b).card := by
  set r := (U.block b).round with hr
  set C := creatorsOf U.block (U.block b).refs with hC
  set S := (history U b).filter (fun i => (U.block i).round < r) with hS
  -- the author-round pairs are all realised in `S`, one block each
  have hsurj : Set.SurjOn (fun i => ((U.block i).creator, (U.block i).round))
      ↑S ↑(C ×ˢ Finset.range r) := by
    rintro ⟨X, t⟩ hmem
    rw [Finset.mem_coe, Finset.mem_product] at hmem
    obtain ⟨hX, ht⟩ := hmem
    rw [hC, mem_creatorsOf] at hX
    rw [Finset.mem_range] at ht
    obtain ⟨p, hp, hpc⟩ := hX
    have hp_ids : p ∈ U.ids := U.complete b hb p hp
    have hp_round := U.round_of_mem_refs hb hp
    obtain ⟨i, hi, hic, hir⟩ := exists_self_ancestor hp_ids (t := t) (by omega)
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_coe, hS, Finset.mem_filter]
      exact ⟨history_subset_of_reaches hb (Reaches.single hp) hi, by omega⟩
    · show ((U.block i).creator, (U.block i).round) = (X, t)
      rw [hic, hpc, hir]
  have hcount : (quorumCard Validator) * r ≤ S.card := by
    calc (quorumCard Validator) * r
        ≤ C.card * r :=
          Nat.mul_le_mul_right r ((U.valid b hb).quorum h0)
      _ = (C ×ˢ Finset.range r).card := by rw [Finset.card_product, Finset.card_range]
      _ ≤ S.card := Finset.card_le_card_of_surjOn _ hsurj
  have hsub : S ⊆ (history U b).erase b := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    refine Finset.mem_erase.mpr ⟨?_, hi.1⟩
    intro hib
    subst hib
    omega
  have herase := Finset.card_erase_of_mem (mem_history_self (U := U) (b := b))
  have hpos : 0 < (history U b).card := Finset.card_pos.mpr ⟨b, mem_history_self⟩
  have := Finset.card_le_card hsub
  omega

end LeanDag
