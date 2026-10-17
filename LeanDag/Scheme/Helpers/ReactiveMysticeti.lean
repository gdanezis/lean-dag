import LeanDag.Scheme.Helpers.Reactive
import LeanDag.Scheme.Helpers.Rows
import LeanDag.Reactive.Mysticeti
/-!
# Reactive Mysticeti is the family run reactively, at the Mysticeti row

At the Mysticeti row the vote round is one above the proposal, so the
family's reach-or-wait clause is Reactive Mysticeti's `vote_or_wait` (a
reference to the leader block, or a wait and a reference to it if held),
and one round up a vote is a reference (`votes_iff`), so certify-or-wait
is its `cert_or_wait`. Every Reactive Mysticeti execution is therefore one
of the family (`ofReactiveM`), at every vote, pacing at the core's quorum
`n − f`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
  [Nonempty Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type} [S : Slots Validator]
variable {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {N : ℕ}

/-- At the Mysticeti row, `σ`'s certificate is the core's. -/
theorem isCert_mysticeti_iff (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    {c L : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = (U.block L).round + 2) :
    IsCert (Params.mysticeti (Fintype.card Validator) F.f) σ U c L ↔ Certifies U c L := by
  unfold IsCert
  rw [if_neg (by simp [Params.mysticeti])]
  show _ ≤ (creatorsOf U.block ((U.block c).refs.filter _)).card ↔
    _ ≤ (creatorsOf U.block ((U.block c).refs.filter _)).card
  rw [Finset.filter_congr fun b hb => votes_iff σ (U.complete c hc b hb)
    (distinctRefs b (U.complete c hc b hb))
    (by have := U.round_of_mem_refs hc hb; omega)]
  rfl

/-- **Every Reactive Mysticeti execution is the family run reactively** at the
Mysticeti row, when its reliable set is correct. -/
def ofReactiveM (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (hT : T ⊆ (Correct : Finset Validator)) (rm : ReactiveM U T N) :
    SchemeReactive (quorumCard Validator) (Params.mysticeti (Fintype.card Validator) F.f) σ U T N
    where
  toReactiveCore :=
    have hadv := rm.advances
    let rc := rm.toReactiveCore
    letI : Faults Validator := noFaults
    { rc with
      advances := fun v hv n hn t h => hadv v hv n hn t (le_trans (Nat.sub_le _ _) h) }
  advancesAt := rm.advances
  reach_or_wait := fun v hv k hN hlead L hL m hm c hc hcc hcr => by
    have hvo : (Params.mysticeti (Fintype.card Validator) F.f).voteOffset = 1 := by
      simp [Params.voteOffset, Params.mysticeti]
    have hm0 : m = 0 := by omega
    subst hm0
    rcases rm.vote_or_wait v hv k (by omega) hlead L hL c hc hcc (by simpa using hcr) with
      h | ⟨hw, hh⟩
    · exact Or.inl (Reaches.single h)
    · refine Or.inr ⟨by simpa using hw, fun b hb hbc hbr hbh => ?_⟩
      rw [U.eq_of_creator_eq hb hL.1 (hT hlead) hbc hL.2.2 (by rw [hbr, hL.2.1]; rfl)] at hbh ⊢
      exact hh (by simpa using hbh)
  cert_or_wait := fun _ v hv k hN hlead L hL c hc hcc hcr => by
    have hvo : (Params.mysticeti (Fintype.card Validator) F.f).voteOffset = 1 := by
      simp [Params.voteOffset, Params.mysticeti]
    rw [hvo] at hN hcr ⊢
    rcases rm.cert_or_wait v hv k (by omega) hlead L hL c hc hcc (by omega) with
      h | ⟨hw, hincl⟩
    · exact Or.inl ((isCert_mysticeti_iff σ hc (by rw [hcr, hL.2.1])).mpr h)
    · refine Or.inr ⟨by simpa using hw, fun b hb hbT hbr hbh hvote => ?_⟩
      exact hincl b hb hbT hbr (by simpa using hbh)
        ((votes_iff σ hb (distinctRefs b hb) (by rw [hbr, hL.2.1])).mp hvote)

end Scheme

end LeanDag
