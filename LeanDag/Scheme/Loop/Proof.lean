import LeanDag.Scheme.Loop.Statement
import LeanDag.Scheme.Helpers.Order
import LeanDag.Scheme.Helpers.Ledger
/-!
# The commit loop — proof

Soundness by induction down the scan, completeness by induction on a
bounded derivation (`Helpers/TryDecide.lean`); prefix comparability and
completeness use the laws of `Helpers/Sufficiency.lean`; the restart,
the order and the ledger are `Helpers/Restart.lean`, `Helpers/Order.lean`
and `Helpers/Ledger.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Loop

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V lo N hl hc hlo
  exact tryDecide_sound hl hc hlo

/-- The rows the inequalities cover (`Params.Covered`) have positive
thresholds and their laws. -/
theorem family {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] {P : Validity Validator BlockId Payload} [P.Mechanised]
    {q : ℕ} [P.Quorate q] {honest Hon : Finset Validator} {f : ℕ} {p : Params}
    (σ : VoteSel Validator BlockId Payload P honest) (hHon : Honᶜ.card ≤ f)
    (hq : q ≤ Fintype.card Validator)
    (hfam : p.Covered (Fintype.card Validator) f q) :
    1 ≤ p.linkSize ∧ 1 ≤ p.commitThreshold ∧ (p.voteIsCert = false → 1 ≤ p.certThreshold) ∧
      (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) := by
  rcases hfam with ⟨hv, -, hl, hineq⟩ | ⟨hv, hw, hl, hineq⟩ | ⟨hv, -, hl, rfl, hineq⟩ |
    ⟨hv, hw, hl, hc1, rfl, hineq⟩
  · obtain ⟨-, -, hc⟩ := id hineq
    exact ⟨hl, by omega, fun h => absurd (hv.symm.trans h) (by simp),
      twoRoundLaws σ hv hHon hq hineq⟩
  · obtain ⟨ha, -, hc⟩ := id hineq
    exact ⟨by omega, by omega, fun _ => by omega, threeRoundLaws σ hv hw hHon hq hl hineq⟩
  · obtain ⟨-, hc⟩ := id hineq
    exact ⟨hl, by omega, fun h => absurd (hv.symm.trans h) (by simp),
      twoRoundCrashLaws σ hv hHon hq hineq⟩
  · obtain ⟨-, hc⟩ := id hineq
    exact ⟨by omega, by omega, fun _ => hc1, threeRoundCrashLaws σ hv hw hHon hq hl hineq⟩

theorem prefixComparable : PrefixComparable := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V₁ V₂ lo N₁ N₂
    hHon hq hne hfam h₁ h₂
  obtain ⟨hl, -, hc, hlaws⟩ := family σ hHon hq hfam
  exact tryDecide_prefix hl hc hlaws hne h₁ h₂ V₁ V₂

theorem complete : Complete := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V k v hHon hq hne hfam hd
  obtain ⟨hl, hcm, hc, hlaws⟩ := family σ hHon hq hfam
  exact decisionAt_eventually hl hcm hc hlaws hne hd

theorem outputComplete : OutputComplete := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V lo k hHon hq hne hfam
    hlok hall
  obtain ⟨hl, hcm, hc, hlaws⟩ := family σ hHon hq hfam
  exact tryDecide_eventually hl hcm hc hlaws hne hlok hall

theorem restart : Restart := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V lo lo' N hlo hlo'
  exact tryDecide_restart hlo hlo'

theorem resume : Resume := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V₁ V₂ lo N₁ N₂
    hHon hq hne hfam hsub hN
  obtain ⟨hl, hcm, hc, hlaws⟩ := family σ hHon hq hfam
  exact tryDecide_resume hl hcm hc hlaws hne hsub hN

theorem repeated : Repeated := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U lo W N
    hHon hq hne hfam hW hN
  obtain ⟨hl, hcm, hc, hlaws⟩ := family σ hHon hq hfam
  exact consumed_eq hl hcm hc hlaws hne hW hN

theorem order : Order := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V per m rLast rHigh hp hm h
  exact schemeTryDecide_eq hp hm h

theorem orderUniform : OrderUniform := by
  intro Validator per m rLast rHigh hp hm elect hblock
  exact schemeOrder_uniform hp hm

theorem restartRound : RestartRound := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V₁ V₂ per m rLast rHigh₁
    rHigh₂ k v hHon hq hne hfam hsub hp hm h₁ hH hlast
  obtain ⟨hl, hcm, hc, hlaws⟩ := family σ hHon hq hfam
  exact schemeTryDecide_restartRound hl hcm hc hlaws hne hsub hp hm h₁ hH hlast

theorem ledger : Ledger := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V N hl hc
  exact ledger_read hl hc N

theorem ledgerAgree : LedgerAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V₁ V₂ N₁ N₂
    hHon hq hne hfam
  obtain ⟨hl, -, hc, hlaws⟩ := family σ hHon hq hfam
  exact ledger_agree hl hc hlaws hne V₁ V₂ N₁ N₂

theorem holds : Statement :=
  ⟨sound, prefixComparable, complete, outputComplete, restart, resume, repeated, order,
    orderUniform, restartRound, ledger, ledgerAgree⟩

end Loop

end Scheme

end LeanDag
