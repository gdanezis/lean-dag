import LeanDag.Scheme.Loop.Statement
import LeanDag.Scheme.Helpers.TryDecide
/-!
# The commit loop — proof

Soundness by induction down the scan, completeness by induction on a
bounded derivation (`Helpers/TryDecide.lean`); prefix comparability and
completeness use the laws of `Helpers/Sufficiency.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Loop

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V lo N hl hc hlo
  exact tryDecide_sound hl hc hlo

/-- The rows the inequalities cover have positive thresholds and their
laws. -/
theorem family {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] {P : Validity Validator BlockId Payload} [P.Mechanised]
    {q : ℕ} [P.Quorate q] {honest Hon : Finset Validator} {f : ℕ} {p : Params}
    (σ : VoteSel Validator BlockId Payload P honest) (hHon : Honᶜ.card ≤ f)
    (hq : q ≤ Fintype.card Validator)
    (hfam : (p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) :
    1 ≤ p.linkSize ∧ 1 ≤ p.commitThreshold ∧ (p.voteIsCert = false → 1 ≤ p.certThreshold) ∧
      (schemeAnchored p σ).Laws (fun _ U => U.NoEquivOn Hon) := by
  rcases hfam with ⟨hv, -, hl, hineq⟩ | ⟨hv, hw, hl, hineq⟩
  · obtain ⟨-, -, hc⟩ := id hineq
    exact ⟨hl, by omega, fun h => absurd (hv.symm.trans h) (by simp),
      twoRoundLaws σ hv hHon hq hineq⟩
  · obtain ⟨ha, -, hc⟩ := id hineq
    exact ⟨by omega, by omega, fun _ => by omega, threeRoundLaws σ hv hw hHon hq hl hineq⟩

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

theorem holds : Statement := ⟨sound, prefixComparable, complete, outputComplete⟩

end Loop

end Scheme

end LeanDag
