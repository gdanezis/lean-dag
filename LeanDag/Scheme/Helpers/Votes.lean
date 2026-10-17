import LeanDag.Scheme.Model.LeastSel
import LeanDag.Common.History
import LeanDag.Common.Block
/-!
# The scheme's votes, one round above the candidate

A block one round above a candidate holds in its history, at the
candidate's round, exactly its references; when those name distinct
authors, any vote-selection rule votes for a candidate exactly when the
block references it, and blames a slot exactly when it references no
candidate of it. The scheme's certificate and blame sets are then the
sets the rules of this development count.

A certificate is the block's own vote, or votes for the candidate among
its references from `cert` authors (`isCert_of_votes`); either way the
candidate lies in the certificate's history (`mem_history_of_isCert`).
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {U : BlockRecord Validator BlockId Payload P honest}
variable (σ : VoteSel Validator BlockId Payload P honest)

omit [P.Mechanised] in
/-- **A block votes for at most one block of a slot.** -/
theorem VoteSel.eq_of_votes {q L₁ L₂ : BlockId} (h₁ : σ.Votes U q L₁) (h₂ : σ.Votes U q L₂)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  unfold VoteSel.Votes at h₁ h₂
  rw [hc, hr, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- The references of `b` name distinct authors. -/
def DistinctRefs (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) : Prop :=
  ∀ i ∈ (U.block b).refs, ∀ j ∈ (U.block b).refs, (U.block i).creator = (U.block j).creator →
    i = j

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [P.Mechanised] in
/-- References name distinct authors wherever validity asks it. -/
theorem distinctRefs [P.Distinct] : ∀ b ∈ U.ids, DistinctRefs U b :=
  fun _ hb _ hi _ hj hc => U.distinct_creators hb hi hj hc

/-- **A vote one round up is a reference.** -/
theorem votes_iff {b L : BlockId} (hb : b ∈ U.ids) (hd : DistinctRefs U b)
    (hr : (U.block L).round + 1 = (U.block b).round) :
    σ.Votes U b L ↔ IsVote U b L := by
  constructor
  · intro h
    obtain ⟨hx, -, -⟩ := σ.sound U b _ _ L h
    exact mem_refs_of_mem_history_of_round_succ hb hx hr
  · intro hL
    unfold VoteSel.Votes
    cases hs : σ.sel U b (U.block L).creator (U.block L).round with
    | none => exact absurd rfl (σ.complete U b _ _ hb (by omega) hs L (mem_history_of_mem_refs hb hL) rfl)
    | some x =>
      obtain ⟨hx, hxc, hxr⟩ := σ.sound U b _ _ x hs
      have hxref := mem_refs_of_mem_history_of_round_succ hb hx (by rw [hxr]; exact hr)
      rw [hd x hxref L hL hxc]

variable [S : Slots Validator]

/-- **A blame one round up is a reference to no candidate.** -/
theorem sel_none_iff {b : BlockId} {k : ℕ} (hb : b ∈ U.ids)
    (hr : (U.block b).round = S.slotRound k + 1) :
    σ.sel U b (S.leader k) (S.slotRound k) = none ↔
      ∀ j ∈ (U.block b).refs, ¬ IsLeaderBlock U k j := by
  constructor
  · intro h j hj ⟨_, hjr, hjc⟩
    exact σ.complete U b _ _ hb (by omega) h j (mem_history_of_mem_refs hb hj) hjc hjr
  · intro h
    cases hs : σ.sel U b (S.leader k) (S.slotRound k) with
    | none => rfl
    | some x =>
      obtain ⟨hx, hxc, hxr⟩ := σ.sound U b _ _ x hs
      have hxref := mem_refs_of_mem_history_of_round_succ hb hx (by omega)
      exact absurd ⟨U.complete b hb x hxref, hxr, hxc⟩ (h x hxref)

variable (p : Params)

/-- **The scheme's blames are the slot's blamers**, at a vote round one up. -/
theorem blamersAt_eq (hv : p.voteOffset = 1) (k : ℕ) :
    blamersAt p σ U k = slotBlamers U k := by
  unfold blamersAt slotBlamers
  rw [hv]
  refine Finset.filter_congr fun b hb => ?_
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hb
  exact sel_none_iff σ hbU hbr

omit S in
/-- **Two-round certificates are the votes**, at a vote that is its own
certificate and a wave of two. -/
theorem certsAt_eq_votesFor (hv : p.voteIsCert = true) (hw : p.waveLength = 2)
    (hd : ∀ b ∈ U.ids, DistinctRefs U b) {L : BlockId} {r : ℕ}
    (hL : (U.block L).round = r) :
    certsAt p σ U L r = votesFor U L (r + 1) := by
  unfold certsAt votesFor
  rw [hw]
  refine Finset.filter_congr fun C hC => ?_
  obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hC
  simp only [IsCert, hv, if_true]
  exact votes_iff σ hCU (hd C hCU) (by omega)

omit S in
/-- **Three-round certificates are the core's**, at a wave of three. -/
theorem certsAt_eq_certificatesAt (hv : p.voteIsCert = false) (hw : p.waveLength = 3)
    (hd : ∀ b ∈ U.ids, DistinctRefs U b) {L : BlockId} {r : ℕ}
    (hL : (U.block L).round = r) :
    certsAt p σ U L r = certificatesAt U (IsVote U) p.certThreshold L (r + 2) := by
  unfold certsAt certificatesAt
  rw [hw]
  refine Finset.filter_congr fun C hC => ?_
  obtain ⟨hCU, hCr⟩ := mem_blocksAt.mp hC
  simp only [IsCert, hv, Bool.false_eq_true, if_false, CarriesVotes, carriedVotes]
  have : (U.block C).refs.filter (fun b => σ.Votes U b L) =
      (U.block C).refs.filter (fun b => IsVote U b L) := by
    refine Finset.filter_congr fun b hb => ?_
    have hbU := U.complete C hCU b hb
    have hbr := Validity.Mechanised.pred U.block (U.block C) (U.valid C hCU) b hb
    exact votes_iff σ hbU (hd b hbU) (by omega)
  rw [this]

/-! ## The least block -/

section Least

variable {B : Type} [LinearOrder B]

theorem leastOf_eq_some {s : Finset B} {L : B} (h : leastOf s = some L) :
    L ∈ s ∧ ∀ L' ∈ s, L ≤ L' := by
  unfold leastOf at h
  split at h
  · rename_i hs
    cases h
    exact ⟨s.min'_mem hs, fun L' hL' => s.min'_le L' hL'⟩
  · cases h

theorem leastOf_eq_none {s : Finset B} (h : leastOf s = none) : s = ∅ := by
  unfold leastOf at h
  split at h
  · cases h
  · rename_i hs
    exact Finset.not_nonempty_iff_eq_empty.mp hs

theorem leastOf_eq_some_iff {s : Finset B} {L : B} :
    leastOf s = some L ↔ L ∈ s ∧ ∀ L' ∈ s, L ≤ L' := by
  refine ⟨leastOf_eq_some, fun ⟨hL, hmin⟩ => ?_⟩
  have hs : s.Nonempty := ⟨L, hL⟩
  unfold leastOf
  rw [dif_pos hs, Option.some.injEq]
  exact le_antisymm (s.min'_le L hL) (s.le_min' hs L hmin)

end Least

/-! ## Certificates -/

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [P.Mechanised] S in
theorem Params.voteOffset_of_true {p : Params} (h : p.voteIsCert = true) :
    p.voteOffset = p.waveLength - 1 := by
  simp [Params.voteOffset, h]

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [P.Mechanised] S in
theorem Params.voteOffset_of_false {p : Params} (h : p.voteIsCert = false)
    (hw : 3 ≤ p.waveLength) : p.voteOffset = p.waveLength - 2 := by
  simp only [Params.voteOffset, h, Bool.false_eq_true, if_false]
  omega

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [P.Mechanised] S in
/-- The vote round is at most the decision round, at a wave of two or more. -/
theorem Params.voteOffset_le {p : Params} (hw : 2 ≤ p.waveLength) :
    p.voteOffset ≤ p.waveLength - 1 := by
  unfold Params.voteOffset; split <;> omega

omit [Fintype Validator] [DecidableEq Validator] [DecidableEq BlockId] [P.Mechanised] S in
/-- The vote round is above the proposal, at a wave of two or more. -/
theorem Params.one_le_voteOffset {p : Params} (hw : 2 ≤ p.waveLength) : 1 ≤ p.voteOffset := by
  unfold Params.voteOffset; split <;> omega

omit [Fintype Validator] [P.Mechanised] S in
theorem isCert_iff_votes (hv : p.voteIsCert = true) {C L : BlockId} :
    IsCert p σ U C L ↔ σ.Votes U C L := by
  simp [IsCert, hv]

omit [Fintype Validator] [P.Mechanised] S in
theorem isCert_iff_carries (hv : p.voteIsCert = false) {C L : BlockId} :
    IsCert p σ U C L ↔ CarriesVotes U (σ.Votes U) p.certThreshold C L := by
  simp [IsCert, hv]

omit [Fintype Validator] [P.Mechanised] S in
/-- **A certificate from votes**: the block's own vote where votes are
certificates, or `cert` authors among its references voting. -/
theorem isCert_of_votes {C L : BlockId} (hv : p.voteIsCert = true → σ.Votes U C L)
    (hc : p.voteIsCert = false → ∃ A : Finset Validator, p.certThreshold ≤ A.card ∧
      ∀ u ∈ A, ∃ b ∈ (U.block C).refs, (U.block b).creator = u ∧ σ.Votes U b L) :
    IsCert p σ U C L := by
  cases h : p.voteIsCert
  · obtain ⟨A, hA, hAv⟩ := hc h
    rw [isCert_iff_carries σ p h]
    refine le_trans hA (Finset.card_le_card fun u hu => ?_)
    obtain ⟨b, hb, hbc, hbv⟩ := hAv u hu
    exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hbv⟩, hbc⟩
  · exact (isCert_iff_votes σ p h).mpr (hv h)

omit [Fintype Validator] S in
/-- **A certified block lies in the certificate's history**, at a positive
certificate threshold. -/
theorem mem_history_of_isCert (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {C L : BlockId} (hC : C ∈ U.ids) (h : IsCert p σ U C L) : L ∈ history U C := by
  cases hv : p.voteIsCert
  · obtain ⟨b, hb, hbL⟩ := exists_vote_of_carriesVotes (hc hv) ((isCert_iff_carries σ p hv).mp h)
    exact history_subset_of_reaches hC (Reaches.single hb) (σ.sound U b _ _ L hbL).1
  · exact (σ.sound U C _ _ L ((isCert_iff_votes σ p hv).mp h)).1

end Scheme

end LeanDag
