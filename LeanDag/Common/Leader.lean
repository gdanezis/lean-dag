import LeanDag.Common.Support
import LeanDag.Common.Slots
/-!
# Leaders, candidates and blame

Slot `k` is proposed at `slotRound k` by `leader k`; its **candidates**
are the blocks at that round by that author, one for an honest leader
and possibly several for an equivocating one. Votes on the slot are cast
at its **voting round**, one above, and a voting-round block that
references no candidate **blames** the slot. The counts are
threshold-free; each rule names its own.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-! ## Candidates -/

section Candidates

variable [S : Slots Validator]

/-- `L` is a candidate block for slot `k`: the right round, the right
author. -/
@[reducible]
def IsLeaderBlock (U : BlockRecord Validator BlockId Payload P honest) (k : ℕ) (L : BlockId) :
    Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k

variable {U : BlockRecord Validator BlockId Payload P honest}

omit S in
/-- Decidable at any schedule a statement names, the schedule being a
plain implicit. -/
instance decidableIsLeaderBlock [DecidableEq Validator] [DecidableEq BlockId]
    {S : Slots Validator} (k : ℕ) (L : BlockId) : Decidable (IsLeaderBlock (S := S) U k L) :=
  inferInstanceAs (Decidable (L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧
    (U.block L).creator = S.leader k))

/-- **A block is the candidate of at most one slot** — what `Slots.keyed`
yields: two slots sharing a round are told apart by their leaders. -/
theorem slot_eq_of_isLeaderBlock {k₁ k₂ : ℕ} {L : BlockId}
    (h₁ : IsLeaderBlock U k₁ L) (h₂ : IsLeaderBlock U k₂ L) : k₁ = k₂ :=
  S.keyed (by simp only [← h₁.2.1, ← h₂.2.1, ← h₁.2.2, ← h₂.2.2])

/-- **An honest leader has at most one candidate**, so a tie between
candidates only arises under a dishonest leader. -/
theorem isLeaderBlock_unique_of_honest {k : ℕ} {L₁ L₂ : BlockId}
    (hk : S.leader k ∈ honest) (h₁ : IsLeaderBlock U k L₁) (h₂ : IsLeaderBlock U k L₂) :
    L₁ = L₂ :=
  U.no_equivocation L₁ h₁.1 L₂ h₂.1 (by rw [h₁.2.2]; exact hk)
    (by rw [h₁.2.2, h₂.2.2]) (by rw [h₁.2.1, h₂.2.1])

omit S in
/-- Only the leader clause of `IsLeaderBlock` consults the schedule's
leaders, at the slot itself. -/
theorem isLeaderBlock_congr {S₁ S₂ : Slots Validator} {k : ℕ} {L : BlockId}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : IsLeaderBlock (S := S₁) U k L) : IsLeaderBlock (S := S₂) U k L := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by rw [← hround]; exact h2, by rw [← hk]; exact h3⟩

variable [DecidableEq Validator] [DecidableEq BlockId]

/-- The candidates of slot `k`, as a set. -/
def leaderBlocksAt (U : BlockRecord Validator BlockId Payload P honest) (k : ℕ) :
    Finset BlockId :=
  (blocksAt U (S.slotRound k)).filter (fun b => (U.block b).creator = S.leader k)

@[simp] theorem mem_leaderBlocksAt {k : ℕ} {b : BlockId} :
    b ∈ leaderBlocksAt U k ↔ IsLeaderBlock U k b := by
  simp only [leaderBlocksAt, Finset.mem_filter, mem_blocksAt, IsLeaderBlock, and_assoc]

end Candidates

/-! ## The voting round, and blame

A slot is voted on one round above its proposal, whatever the rule. A
blame is the absence of **every** candidate from a voting-round block,
not of one named block: a slot holding no candidate would otherwise be
settled vacuously, and a candidate arriving later judged by nothing. As
stated, a later candidate is referenced by none of the blamers, and a
skip is final. -/

section Blame

variable [S : Slots Validator]

/-- The round at which slot `k` is voted on: one above its proposal. -/
abbrev votingRound (Validator : Type*) [S : Slots Validator] (k : ℕ) : ℕ :=
  S.slotRound k + 1

variable [DecidableEq Validator] [DecidableEq BlockId]
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The voting-round blocks that reference **no candidate** of slot `k`. -/
def slotBlamers (U : BlockRecord Validator BlockId Payload P honest) (k : ℕ) :
    Finset BlockId :=
  (blocksAt U (S.slotRound k + 1)).filter
    (fun q => ∀ j ∈ (U.block q).refs, ¬ IsLeaderBlock U k j)

/-- The validators whose voting-round block blames slot `k`. -/
def slotBlames (U : BlockRecord Validator BlockId Payload P honest) (k : ℕ) :
    Finset Validator :=
  creatorsOf U.block (slotBlamers U k)

/-- The blamers of slot `k` that a view holds. -/
def slotBlamesIn (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (k : ℕ) :
    Finset Validator :=
  heldAuthors U V (slotBlamers U k)

theorem mem_slotBlamers {k : ℕ} {q : BlockId} :
    q ∈ slotBlamers U k ↔
      q ∈ U.ids ∧ (U.block q).round = S.slotRound k + 1 ∧
        ∀ j ∈ (U.block q).refs, ¬ IsLeaderBlock U k j := by
  simp only [slotBlamers, Finset.mem_filter, mem_blocksAt, and_assoc]

theorem mem_slotBlames {k : ℕ} {v : Validator} :
    v ∈ slotBlames U k ↔
      ∃ q ∈ U.ids, (U.block q).round = S.slotRound k + 1 ∧
        (∀ j ∈ (U.block q).refs, ¬ IsLeaderBlock U k j) ∧ (U.block q).creator = v := by
  simp only [slotBlames, mem_creatorsOf, mem_slotBlamers]
  constructor
  · rintro ⟨q, ⟨hq, hr, hn⟩, hc⟩; exact ⟨q, hq, hr, hn, hc⟩
  · rintro ⟨q, hq, hr, hn, hc⟩; exact ⟨q, ⟨hq, hr, hn⟩, hc⟩

/-- **Blaming the slot is blaming each of its candidates.** -/
theorem slotBlamers_subset_omissionsOf {k : ℕ} {L : BlockId} (hL : IsLeaderBlock U k L) :
    slotBlamers U k ⊆ omissionsOf U L (S.slotRound k + 1) := by
  intro q hq
  rw [mem_slotBlamers] at hq
  rw [mem_omissionsOf]
  exact ⟨hq.1, hq.2.1, fun hmem => hq.2.2 L hmem hL⟩

/-- Blaming the slot is blaming each of its candidates, as counts. -/
theorem slotBlames_subset_blames {k : ℕ} {L : BlockId} (hL : IsLeaderBlock U k L) :
    slotBlames U k ⊆ blames U L (S.slotRound k + 1) :=
  Finset.image_subset_image (slotBlamers_subset_omissionsOf hL)

/-- **Supporters of a candidate and blamers of its slot together number
at most `n + m`**, on any non-equivocating set `Hon` with `m` outside it. -/
theorem card_supporters_add_card_slotBlames_le [Fintype Validator] {Hon : Finset Validator}
    {m : ℕ} (hne : U.NoEquivOn Hon) (hm : Honᶜ.card ≤ m) {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) :
    (supporters U L (S.slotRound k + 1)).card + (slotBlames U k).card ≤
      Fintype.card Validator + m :=
  le_trans (Nat.add_le_add_left (Finset.card_le_card (slotBlames_subset_blames hL)) _)
    (card_supporters_add_card_blames_le hne hm)

/-- **A slot with no candidate is blamed by every voting-round block**, so
its skip reduces to a quorum being present there. -/
theorem slotBlamers_of_no_candidate {k : ℕ} (hnone : ∀ L, ¬ IsLeaderBlock U k L) :
    slotBlamers U k = blocksAt U (S.slotRound k + 1) :=
  Finset.filter_true_of_mem fun _ _ j _ => hnone j

omit S in
/-- **Blame reads the schedule only at its own slot**: two schedules
naming the same round and the same leader there agree on who blames it. -/
theorem slotBlamers_congr {S₁ S₂ : Slots Validator} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k) :
    slotBlamers (S := S₁) U k = slotBlamers (S := S₂) U k := by
  ext q
  simp only [mem_slotBlamers, hround]
  constructor
  · rintro ⟨hq, hr, hn⟩
    exact ⟨hq, hr, fun j hj hjL => hn j hj (isLeaderBlock_congr hround.symm hk.symm hjL)⟩
  · rintro ⟨hq, hr, hn⟩
    exact ⟨hq, hr, fun j hj hjL => hn j hj (isLeaderBlock_congr hround hk hjL)⟩

omit S in
theorem slotBlamesIn_congr {S₁ S₂ : Slots Validator} {V : U.View} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k) :
    slotBlamesIn (S := S₁) U V k = slotBlamesIn (S := S₂) U V k := by
  unfold slotBlamesIn; rw [slotBlamers_congr hround hk]

end Blame

end LeanDag
