import LeanDag.RedSnapper.Five.Uncontested.Statement
import LeanDag.RedSnapper.Helpers.Liveness
import LeanDag.RedSnapper.Helpers.Freeze

/-!
# Uncontested liveness at 5f+1 — proof

Generated proof layer; not part of the audit surface. The argument of
RS4 over the `5f+1` rule: synchrony carries the transaction from the
carrier into every correct block of the next round; with no rival
anywhere neither origin of `⊥` is available — a visible conflict
directly, a marker through the conflict its trigger anchor sees — so
`fast_vote_of_sole_of` makes each of them a fast vote, and every correct
`r₀ + 2` block references a correct quorum of them. The verdicts are one
constructor each on top.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveUncontested

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] in
/-- Behind every correct `⊥` there is a conflict somewhere: at the
declaring block, or at the anchor its marker names. -/
private theorem conflict_of_bot (hrule : VotingRuleFive U) :
    ∀ e ∈ U.ids, (U.block e).author ∈ (Correct : Finset Validator) →
      ∀ o : Obj, (U.block e).declares o = some Stance.bot → ∃ x, Conflicted U x o := by
  intro e he hc o hd
  rcases hrule.bot_contested e he hc o hd with hconf | hfr
  · exact ⟨e, hconf⟩
  · obtain ⟨aₖ, haₖ⟩ := Option.ne_none_iff_exists'.mp hfr
    exact ⟨aₖ, (hrule.freeze_triggered e he hc o aₖ haₖ).1⟩

omit [DecidableEq BlockId] in
theorem fullLiveness : FullLiveness U := by
  intro hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 C hC hcC hrC
  -- every correct validator's r₀+1 block is a fast-vote parent of C
  apply atLeast_of_correct_blocks quorum_le_card_correct
  intro w hw
  obtain ⟨b₁, hb₁, hab₁, hrb₁⟩ := hpop1 w hw
  have hwc₁ : (U.block b₁).author ∈ (Correct : Finset Validator) := hab₁.symm ▸ hw
  have hpar₀ : b₀ ∈ (U.block b₁).parents :=
    hsync b₁ hb₁ hwc₁ (by omega) b₀ hb₀ hc₀ (by omega)
  have hinc₁ : Includes U b₁ tx := includes_mono (Reaches.single hpar₀) hinc₀
  exact ⟨b₁, hsync C hC hcC (by omega) b₁ hb₁ hwc₁ (by omega), hab₁,
    fast_vote_of_sole_of hrule.ack_sole (conflict_of_bot hrule) hval hsole hb₁ hwc₁ hinc₁⟩

omit [DecidableEq BlockId] in
theorem fullVerdict : FullVerdict U := by
  intro hrule tx r₀ R b₀ hown hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hpop2
    A V prio hVfull
  -- the correct pool is nonempty, so the certificate round holds a correct block
  have hpos : 0 < (Correct : Finset Validator).card :=
    lt_of_lt_of_le quorum_pos quorum_le_card_correct
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  obtain ⟨C, hC, haC, hrC⟩ := hpop2 v hv
  exact .fullFinal hown (hVfull hC)
    (fullLiveness hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1
      C hC (haC.symm ▸ hv) hrC)

omit [DecidableEq BlockId] in
theorem mixedVerdict : MixedVerdict U := by
  intro hrule tx r₀ R b₀ hmix hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1
    A V prio i a C hlk hC hcC hrC hreach
  have hcert : IsFullCert U C tx :=
    fullLiveness hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1
      C hC hcC hrC
  exact .mixedFinal hmix hlk (isCandidate_mono hreach (isCandidate_of_fullCert hcert))
    hC hreach hcert

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U
  exact ⟨fullLiveness, fullVerdict, mixedVerdict⟩

end FiveUncontested

end RedSnapper

end LeanDag
