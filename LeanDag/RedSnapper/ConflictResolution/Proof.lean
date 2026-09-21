import LeanDag.RedSnapper.ConflictResolution.Statement
import LeanDag.RedSnapper.Helpers.Liveness
import LeanDag.RedSnapper.CertificateExclusion.Proof

/-!
# Conflict resolution — proof

Generated proof layer; not part of the audit surface. The trichotomy:
every correct `r + 1` block is conflicted through the carrier and
declares; a kept ACK carries `CertVisible`, hence a certificate at or
below itself, which the `r + 2` block inherits; failing that, all
`|Correct| ≥ half` correct `r + 1` blocks are bot votes among the
`r + 2` block's parents — an unlock certificate. Anchor resolution:
a live certified candidate commits by `resolveCommit`; otherwise the
anchor's own chain passes through a trichotomy block, whose certificate
branch forces a release below (the other death disjuncts are
RS2-impossible) and whose unlock branch makes the anchor itself
release-ready — either way the least ready index resolves.
-/

namespace LeanDag

namespace RedSnapper

namespace ConflictResolution

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

open CertificateExclusion

omit [DecidableEq BlockId] in
theorem trichotomy : Trichotomy U := by
  intro hrule o r R b₀ hb₀ hc₀ hr₀ hconf₀ hRr hsync hpop1 b hb hcb hrb
  by_cases hack : ∃ b₁ ∈ U.ids, (U.block b₁).author ∈ (Correct : Finset Validator) ∧
      (U.block b₁).round = r + 1 ∧ ∃ tx, (U.block b₁).declares o = some (Stance.ack tx)
  · obtain ⟨b₁, hb₁, hc₁, hr₁, tx, hd⟩ := hack
    left
    have hpar₀ : b₀ ∈ (U.block b₁).parents :=
      hsync b₁ hb₁ hc₁ (by omega) b₀ hb₀ hc₀ (by omega)
    have hconf₁ : Conflicted U b₁ o := conflicted_mono (Reaches.single hpar₀) hconf₀
    have hcv := hrule.keep_certVisible b₁ hb₁ hc₁ o tx hconf₁ hd
    have hcand₁ : IsCandidate U b₁ o tx := hrule.ack_candidate b₁ hb₁ hc₁ o tx hd
    have hfv₁ : IsFastVote U b₁ tx :=
      ⟨hcand₁.1, hcand₁.2.2, hcand₁.2.1.symm ▸ stanceIs_self_of_declares hb₁ hd⟩
    have hHas₁ : HasCert U b₁ tx := hasCert_of_certVisible_of_fastVote hb₁ hfv₁ hcv
    have hpar₁ : b₁ ∈ (U.block b).parents :=
      hsync b hb hcb (by omega) b₁ hb₁ hc₁ (by omega)
    exact ⟨tx, isCandidate_mono (Reaches.single hpar₁) hcand₁,
      hasCert_mono (Reaches.single hpar₁) hHas₁⟩
  · right
    push Not at hack
    apply atLeast_of_correct_blocks half_le_card_correct
    intro v hv
    obtain ⟨b₁, hb₁, hab₁, hrb₁⟩ := hpop1 v hv
    have hc₁ : (U.block b₁).author ∈ (Correct : Finset Validator) := hab₁.symm ▸ hv
    have hpar₀ : b₀ ∈ (U.block b₁).parents :=
      hsync b₁ hb₁ hc₁ (by omega) b₀ hb₀ hc₀ (by omega)
    have hconf₁ : Conflicted U b₁ o := conflicted_mono (Reaches.single hpar₀) hconf₀
    have hdecl := hrule.conflicted_declares b₁ hb₁ hc₁ o hconf₁
    have hpar₁ : b₁ ∈ (U.block b).parents :=
      hsync b hb hcb (by omega) b₁ hb₁ hc₁ (by omega)
    refine ⟨b₁, hpar₁, hab₁, ?_⟩
    cases hds : (U.block b₁).declares o with
    | none => exact absurd hds hdecl
    | some s =>
        cases s with
        | ack tx => exact absurd hds (hack b₁ hb₁ hc₁ hrb₁ tx)
        | bot => exact ⟨stanceIs_self_of_declares hb₁ hds, hconf₁⟩

omit [DecidableEq BlockId] in
/-- `AnchorDecides` with its first branch located: the candidate is
certified under the given anchor and alive there — what `resolveCommit`
consumes, and what drops the rivals at the same anchor. -/
theorem anchorRoute (hdisc : StanceDiscipline U) (hrule : VotingRule U) {o : Obj}
    {r R : ℕ} {b₀ : BlockId} (hb₀ : b₀ ∈ U.ids)
    (hc₀ : (U.block b₀).author ∈ (Correct : Finset Validator))
    (hr₀ : (U.block b₀).round = r) (hconf₀ : Conflicted U b₀ o) (hRr : R ≤ r)
    (hsync : SynchronisedOn U (Correct : Finset Validator) R)
    (hpop1 : PopulatedOn U (Correct : Finset Validator) (r + 1))
    {A : Anchors U} {i : ℕ} {a : BlockId} (hia : A.seq[i]? = some a)
    (hca : (U.block a).author ∈ (Correct : Finset Validator))
    (hra : r + 2 ≤ (U.block a).round) :
    (Conflicted U a o ∧ ∃ tx, IsCandidate U a o tx ∧ HasCert U a tx ∧ ¬ DeadAt U A i tx) ∨
      ∃ j ≤ i, ResolvesAt U A j o := by
  have haid : a ∈ U.ids := anchor_mem_ids hia
  -- the anchor is conflicted, through its own round-(r+1) block
  have hconfa : Conflicted U a o := by
    obtain ⟨p, hp, hap, hrp, hreach⟩ := exists_own_block_of_le haid hca (m := r + 1)
      (by omega)
    have hpc : (U.block p).author ∈ (Correct : Finset Validator) := hap.symm ▸ hca
    have hpar₀ : b₀ ∈ (U.block p).parents :=
      hsync p hp hpc (by omega) b₀ hb₀ hc₀ (by omega)
    exact conflicted_mono hreach (conflicted_mono (Reaches.single hpar₀) hconf₀)
  by_cases hlive : ∃ tx, IsCandidate U a o tx ∧ HasCert U a tx ∧ ¬ DeadAt U A i tx
  · exact Or.inl ⟨hconfa, hlive⟩
  · right
    push Not at hlive
    obtain ⟨p, hp, hap, hrp, hreach⟩ := exists_own_block_of_le haid hca (m := r + 2) hra
    have hpc : (U.block p).author ∈ (Correct : Finset Validator) := hap.symm ▸ hca
    have htri := trichotomy hrule o r R b₀ hb₀ hc₀ hr₀ hconf₀ hRr hsync hpop1
      p hp hpc hrp
    have hready : ResolveReadyAt U A i o ∨ ReleasedBelow U A i o := by
      rcases htri with ⟨tx, hcand_p, hcert_p⟩ | huc
      · -- a certified candidate at the anchor, hence dead there; only the
        -- release disjunct survives RS2
        have hcert_a : HasCert U a tx := hasCert_mono hreach hcert_p
        have hcand_a : IsCandidate U a o tx := isCandidate_mono hreach hcand_p
        obtain ⟨a', ha', hdg⟩ := hlive tx hcand_a hcert_a
        rw [hia] at ha'
        cases ha'
        rcases hdg with ⟨tx', hconf', hcert'⟩ | ⟨Cs, hCs, hskip, -⟩ | hrel
        · obtain ⟨C, hC, hc, -⟩ := hcert_a
          obtain ⟨C', hC', hc', -⟩ := hcert'
          exact absurd (certUniqueness hdisc C hC C' hC' tx tx' hconf' hc hc') id
        · obtain ⟨C, hC, hc, -⟩ := hcert_a
          exact absurd (ackSkipExclusion hdisc C hC Cs hCs tx hc hskip) id
        · exact Or.inr (hcand_a.2.1 ▸ hrel)
      · -- the anchor itself is release-ready: conflicted, every certified
        -- candidate dead, the unlock certificate below it
        refine Or.inl ⟨a, hia, hconfa, ?_, p, hp, Or.inr huc, hreach⟩
        intro tx htx hcert
        obtain ⟨a', ha', hdg⟩ := hlive tx htx hcert
        rw [hia] at ha'
        cases ha'
        exact hdg
    rcases hready with h | h
    · obtain ⟨j, hj, hres⟩ := exists_resolvesAt_of_ready h
      exact ⟨j, hj, hres⟩
    · obtain ⟨j, hj, hready'⟩ := releasedBelow_iff_exists.mp h
      obtain ⟨j', hj', hres⟩ := exists_resolvesAt_of_ready hready'
      exact ⟨j', by omega, hres⟩

theorem anchorDecides : AnchorDecides U := by
  intro hdisc hrule o r R b₀ hb₀ hc₀ hr₀ hconf₀ hRr hsync hpop1 A i a V hia hca hra
  rcases anchorRoute hdisc hrule hb₀ hc₀ hr₀ hconf₀ hRr hsync hpop1 hia hca hra with
    ⟨hconfa, tx, hcand, hcert, hlive⟩ | hres
  · exact Or.inl ⟨tx, hcand, TxVerdict.resolveCommit hia (hcand.2.1.symm ▸ hconfa)
      (hcand.2.1.symm ▸ hcand) hcert hlive⟩
  · exact Or.inr hres

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U
  exact ⟨trichotomy, anchorDecides⟩

end ConflictResolution

end RedSnapper

end LeanDag
