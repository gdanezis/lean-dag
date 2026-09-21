import LeanDag.RedSnapper.Five.FullCertSafety.Statement
import LeanDag.RedSnapper.Helpers.Persistence

/-!
# Full-certificate safety — proof

Generated proof layer; not part of the audit surface. Every exclusion
is `stance_persists` plus one count: a full certificate (or full unlock
certificate) yields a correct core of `quorum − f` authors standing at
its value from the certificate's vote round on, and the excluded object
would need more authors than the rest of the committee holds — `half`
for a refutation, `quorum` for a rival certificate — at any committee
`n ≥ 3f + 1`. The `Five` bound is nowhere consumed.
-/

namespace LeanDag

namespace RedSnapper

namespace FullCertSafety

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

theorem singleStance : SingleStance U := by
  intro b hb tx tx' hconf hv hv'
  have h2 := hv'.2.2
  rw [← hconf.2] at h2
  have := stanceIs_unique hv.2.2 h2
  simp only [Option.some.injEq, Stance.ack.injEq] at this
  exact hconf.1 this

/-- The persisting ACK core of a full certificate: from the vote round
on, its correct authors stand at `ack tx`. -/
private theorem fullCert_core (hmove : MoveDiscipline U) {C : BlockId} {tx : Tx}
    (hC : C ∈ U.ids) (hfull : IsFullCert U C tx) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      quorum Validator ≤ S.card + F.f ∧
      ∀ b ∈ U.ids, (U.block b).author ∈ S →
        (U.block C).round ≤ (U.block b).round + 1 →
        StanceIs U (U.block b).author (T.input tx) b (some (Stance.ack tx)) := by
  obtain ⟨S, hS, hk, hP⟩ := correct_core_of_atLeast hC hfull
  have hρ : 0 < (U.block C).round := round_pos_of_atLeast hC quorum_pos hfull
  have hn := F.card_validators
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  refine ⟨S, hS, hk, fun b hb hbS hr => ?_⟩
  refine stance_persists (ρ₀ := (U.block C).round - 1) hmove hS hcount
    (fun v hv e he hae hre => ?_) hbS hb rfl (by omega)
  exact hae ▸ (hP v hv e he hae (by omega)).2.2

omit T in
/-- The persisting `⊥` core of a full unlock certificate. -/
private theorem fullUnlock_core (hmove : MoveDiscipline U) {C : BlockId} {o : Obj}
    (hC : C ∈ U.ids) (hfull : IsFullUnlockCert U C o) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      quorum Validator ≤ S.card + F.f ∧
      ∀ b ∈ U.ids, (U.block b).author ∈ S →
        (U.block C).round ≤ (U.block b).round + 1 →
        StanceIs U (U.block b).author o b (some Stance.bot) := by
  obtain ⟨S, hS, hk, hP⟩ := correct_core_of_atLeast hC hfull
  have hρ : 0 < (U.block C).round := round_pos_of_atLeast hC quorum_pos hfull
  have hn := F.card_validators
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  refine ⟨S, hS, hk, fun b hb hbS hr => ?_⟩
  refine stance_persists (ρ₀ := (U.block C).round - 1) hmove hS hcount
    (fun v hv e he hae hre => ?_) hbS hb rfl (by omega)
  exact hae ▸ hP v hv e he hae (by omega)

theorem commitExcludesRefutation (hmove : MoveDiscipline U) :
    CommitExcludesRefutation U := by
  intro C hC C' hC' tx hfull hle href
  obtain ⟨S, hS, hk, hstand⟩ := fullCert_core hmove hC hfull
  have hn := F.card_validators
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  refine not_atLeast_of_disjoint hcount ?_ href
  rintro q hq ⟨s'', hst, hne⟩ hqS
  have hqid : q ∈ U.ids := U.complete C' hC' q hq
  have hqr : (U.block q).round + 1 = (U.block C').round := round_of_mem_parents hC' hq
  have := hstand q hqid hqS (by omega)
  exact hne (Option.some.inj (stanceIs_unique hst this))

omit T in
theorem unlockExcludesRefutation (hmove : MoveDiscipline U) :
    UnlockExcludesRefutation U := by
  intro C hC C' hC' o hfull hle href
  obtain ⟨S, hS, hk, hstand⟩ := fullUnlock_core hmove hC hfull
  have hn := F.card_validators
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  refine not_atLeast_of_disjoint hcount ?_ href
  rintro q hq ⟨s'', hst, hne⟩ hqS
  have hqid : q ∈ U.ids := U.complete C' hC' q hq
  have hqr : (U.block q).round + 1 = (U.block C').round := round_of_mem_parents hC' hq
  have := hstand q hqid hqS (by omega)
  exact hne (Option.some.inj (stanceIs_unique hst this))

theorem commitExcludesUnlock (hmove : MoveDiscipline U) : CommitExcludesUnlock U := by
  intro C hC C' hC' tx hfull hunlock
  have hn := F.card_validators
  rcases le_total (U.block C).round (U.block C').round with hle | hle
  · obtain ⟨S, hS, hk, hstand⟩ := fullCert_core hmove hC hfull
    have hcount : Fintype.card Validator < S.card + quorum Validator := by
      unfold quorum at *
      omega
    refine not_atLeast_of_disjoint hcount ?_ hunlock
    intro q hq hbot hqS
    have hqid : q ∈ U.ids := U.complete C' hC' q hq
    have hqr : (U.block q).round + 1 = (U.block C').round := round_of_mem_parents hC' hq
    have := hstand q hqid hqS (by omega)
    have hcontra := stanceIs_unique hbot this
    simp at hcontra
  · obtain ⟨S, hS, hk, hstand⟩ := fullUnlock_core hmove hC' hunlock
    have hcount : Fintype.card Validator < S.card + quorum Validator := by
      unfold quorum at *
      omega
    refine not_atLeast_of_disjoint hcount ?_ hfull
    intro q hq hfv hqS
    have hqid : q ∈ U.ids := U.complete C hC q hq
    have hqr : (U.block q).round + 1 = (U.block C).round := round_of_mem_parents hC hq
    have := hstand q hqid hqS (by omega)
    have hcontra := stanceIs_unique hfv.2.2 this
    simp at hcontra

/-- The asymmetric half of uniqueness: no rival full certificate at or
above a full certificate's round. -/
private theorem fullCert_excludes_above (hmove : MoveDiscipline U) {C C' : BlockId}
    {tx tx' : Tx} (hC : C ∈ U.ids) (hC' : C' ∈ U.ids) (hconf : Conflict tx tx')
    (hle : (U.block C).round ≤ (U.block C').round) (hfull : IsFullCert U C tx) :
    ¬ IsFullCert U C' tx' := by
  intro hfull'
  obtain ⟨S, hS, hk, hstand⟩ := fullCert_core hmove hC hfull
  have hn := F.card_validators
  have hcount : Fintype.card Validator < S.card + quorum Validator := by
    unfold quorum at *
    omega
  refine not_atLeast_of_disjoint hcount ?_ hfull'
  intro q hq hfv hqS
  have hqid : q ∈ U.ids := U.complete C' hC' q hq
  have hqr : (U.block q).round + 1 = (U.block C').round := round_of_mem_parents hC' hq
  have hack := hstand q hqid hqS (by omega)
  have hack' := hfv.2.2
  rw [← hconf.2] at hack'
  have := stanceIs_unique hack' hack
  simp only [Option.some.injEq, Stance.ack.injEq] at this
  exact hconf.1 this.symm

theorem fullCertUniqueness (hmove : MoveDiscipline U) : FullCertUniqueness U := by
  intro C hC C' hC' tx tx' hconf hfull hfull'
  rcases le_total (U.block C).round (U.block C').round with hle | hle
  · exact fullCert_excludes_above hmove hC hC' hconf hle hfull hfull'
  · exact fullCert_excludes_above hmove hC' hC
      ⟨fun h => hconf.1 h.symm, hconf.2.symm⟩ hle hfull' hfull

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ U
  exact ⟨singleStance, fun hmove =>
    ⟨commitExcludesRefutation hmove, unlockExcludesRefutation hmove,
      commitExcludesUnlock hmove, fullCertUniqueness hmove⟩⟩

end FullCertSafety

end RedSnapper

end LeanDag
