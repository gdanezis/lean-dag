import LeanDag.RedSnapper.Uncontested.Statement
import LeanDag.RedSnapper.Helpers.Liveness

/-!
# Uncontested liveness — proof

Generated proof layer; not part of the audit surface. Synchrony carries
the transaction from the carrier into every correct block of the next
two rounds; with no rival anywhere, `fast_vote_of_sole` makes each of
them a fast vote; every correct `r₀ + 2` block then references a
correct quorum of fast votes and keeps its own ACK — a certificate —
and the correct pool is itself the quorum of certificate authors.
-/

namespace LeanDag

namespace RedSnapper

namespace Uncontested

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] in
/-- A correct round-`r₀ + 2` block that includes no valid rival is a
certificate: it includes the transaction through its author's own
`r₀ + 1` block, keeps its ACK, and references every correct `r₀ + 1`
fast vote — none of which includes a rival either, being its parents. -/
theorem isFastCert_of_local_sole (hrule : VotingRule U) {tx : Tx} {r₀ R : ℕ}
    {b₀ : BlockId} (hval : T.Valid tx)
    (hb₀ : b₀ ∈ U.ids) (hc₀ : (U.block b₀).author ∈ (Correct : Finset Validator))
    (hr₀ : (U.block b₀).round = r₀) (hinc₀ : Includes U b₀ tx) (hRr : R ≤ r₀)
    (hsync : SynchronisedOn U (Correct : Finset Validator) R)
    (hpop1 : PopulatedOn U (Correct : Finset Validator) (r₀ + 1))
    {b₂ : BlockId} (hb₂ : b₂ ∈ U.ids)
    (hvc₂ : (U.block b₂).author ∈ (Correct : Finset Validator))
    (hrb₂ : (U.block b₂).round = r₀ + 2)
    (hsole : ∀ tx', T.Valid tx' → Conflict tx tx' → ¬ Includes U b₂ tx') :
    IsFastCert U b₂ tx := by
  -- b₂ includes tx through its author's own r₀+1 block and the carrier
  obtain ⟨b₁ᵥ, hb₁ᵥ, hab₁ᵥ, hrb₁ᵥ⟩ := hpop1 _ hvc₂
  have hvc₁ᵥ : (U.block b₁ᵥ).author ∈ (Correct : Finset Validator) := hab₁ᵥ.symm ▸ hvc₂
  have hpar₀ : b₀ ∈ (U.block b₁ᵥ).parents :=
    hsync b₁ᵥ hb₁ᵥ hvc₁ᵥ (by omega) b₀ hb₀ hc₀ (by omega)
  have hpar₁ : b₁ᵥ ∈ (U.block b₂).parents :=
    hsync b₂ hb₂ hvc₂ (by omega) b₁ᵥ hb₁ᵥ hvc₁ᵥ (by omega)
  have hinc₂ : Includes U b₂ tx :=
    includes_mono (Reaches.of_mem_parents hpar₁ (Reaches.single hpar₀)) hinc₀
  refine ⟨fast_vote_of_local_sole hrule hval hb₂ hvc₂ hinc₂ hsole, ?_⟩
  -- every correct validator's r₀+1 block is a fast-vote parent of b₂
  apply atLeast_of_correct_blocks quorum_le_card_correct
  intro w hw
  obtain ⟨b₁, hb₁, hab₁, hrb₁⟩ := hpop1 w hw
  have hwc₁ : (U.block b₁).author ∈ (Correct : Finset Validator) := hab₁.symm ▸ hw
  have hpar₀' : b₀ ∈ (U.block b₁).parents :=
    hsync b₁ hb₁ hwc₁ (by omega) b₀ hb₀ hc₀ (by omega)
  have hinc₁ : Includes U b₁ tx := includes_mono (Reaches.single hpar₀') hinc₀
  have hpar₁' : b₁ ∈ (U.block b₂).parents :=
    hsync b₂ hb₂ hvc₂ (by omega) b₁ hb₁ hwc₁ (by omega)
  -- a rival included by the parent is included by b₂
  exact ⟨b₁, hpar₁', hab₁, fast_vote_of_local_sole hrule hval hb₁ hwc₁ hinc₁
    fun tx' hv' hc' h' => hsole tx' hv' hc' (includes_mono (Reaches.single hpar₁') h')⟩

omit [DecidableEq BlockId] in
/-- The certificate step with no valid rival included anywhere. -/
theorem isFastCert_of_correct (hrule : VotingRule U) {tx : Tx} {r₀ R : ℕ} {b₀ : BlockId}
    (hval : T.Valid tx)
    (hsole : ∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx')
    (hb₀ : b₀ ∈ U.ids) (hc₀ : (U.block b₀).author ∈ (Correct : Finset Validator))
    (hr₀ : (U.block b₀).round = r₀) (hinc₀ : Includes U b₀ tx) (hRr : R ≤ r₀)
    (hsync : SynchronisedOn U (Correct : Finset Validator) R)
    (hpop1 : PopulatedOn U (Correct : Finset Validator) (r₀ + 1))
    {b₂ : BlockId} (hb₂ : b₂ ∈ U.ids)
    (hvc₂ : (U.block b₂).author ∈ (Correct : Finset Validator))
    (hrb₂ : (U.block b₂).round = r₀ + 2) : IsFastCert U b₂ tx :=
  isFastCert_of_local_sole hrule hval hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hb₂ hvc₂ hrb₂
    fun tx' hv' hc' => hsole tx' hv' hc' b₂ hb₂

omit [DecidableEq BlockId] in
theorem fastLiveness : FastLiveness U := by
  intro hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hpop2
  apply atLeast_of_correct_blocks quorum_le_card_correct
  intro v hv
  obtain ⟨b₂, hb₂, hab₂, hrb₂⟩ := hpop2 v hv
  exact ⟨b₂, Finset.mem_filter.mpr ⟨hb₂, hrb₂⟩, hab₂,
    isFastCert_of_correct hrule hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hb₂
      (hab₂.symm ▸ hv) hrb₂⟩

theorem fastVerdict : FastVerdict U := by
  intro hrule tx r₀ R b₀ hown hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hpop2
    A V hVfull
  have hq := fastLiveness hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr
    hsync hpop1 hpop2
  refine TxVerdict.fastFinal (r := r₀ + 2) hown ?_
  unfold FastQuorumAtInView
  have heq : blocksAt U (r₀ + 2) ∩ V.ids = blocksAt U (r₀ + 2) :=
    Finset.inter_eq_left.mpr fun b hb => hVfull (mem_ids_of_mem_blocksAt hb)
  rw [heq]
  exact hq

theorem anchorVerdict : AnchorVerdict U := by
  intro hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1
    A V i a C hlk hC hcC hrC hreach
  have hcert : HasCert U a tx :=
    ⟨C, hC, isFastCert_of_correct hrule hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1
      hC hcC hrC, hreach⟩
  exact .finalizeOnCommit hlk (isCandidate_of_hasCert hcert)
    (not_conflicted_of_sole hsole a) hcert

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U
  exact ⟨fastLiveness, fastVerdict, anchorVerdict⟩

end Uncontested

end RedSnapper

end LeanDag
