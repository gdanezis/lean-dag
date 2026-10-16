import LeanDag.Scheme.Model.Rule
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
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {U : BlockRecord Validator BlockId Payload P honest}
variable (σ : VoteSel Validator BlockId Payload P honest)

/-- The references of `b` name distinct authors. -/
def DistinctRefs (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) : Prop :=
  ∀ i ∈ (U.block b).refs, ∀ j ∈ (U.block b).refs, (U.block i).creator = (U.block j).creator →
    i = j

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

end Scheme

end LeanDag
