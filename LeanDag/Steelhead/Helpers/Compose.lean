import LeanDag.Steelhead.Interface.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Helpers — the composite

Generated lemma infrastructure for `Interface/Statement.lean`; not part
of the audit surface. Each law of the composite is the law of the slot's
own rule, once the composite's rung count and tie-break are rewritten to
that rule's, which the family's agreement on them allows. The periodic
class reads its bounds off the two waves, its spanning off the identity
rounds, and its laws off the ones `Properties.lean` proves at any
wavelength function of two rounds or more.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- The composite's tie-break choice at a slot is the slot's rule's, once the ties agree. -/
theorem compose_least (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (ht : ∀ r, (rules r).tie = (rules 0).tie) {S : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {A L : BlockId} {i k : ℕ} :
    (compose rules).Least (S := S) U A i k L ↔
      (rules (S.slotRound k)).Least (S := S) U A i k L := by
  unfold AnchoredRule.Least
  simp only [compose, ht]

/-- **SH16a.** Every law of the composite at a slot is the law of the slot's rule. -/
theorem compose_laws (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (hl : ∀ r, (rules r).Laws) (hr : ∀ r, (rules r).rungs = (rules 0).rungs)
    (ht : ∀ r, (rules r).tie = (rules 0).tie) : (compose rules).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ hI hL₁ hL₂ h₁ h₂
    exact (hl (S.slotRound k)).commit_unique hI hL₁ hL₂ h₁ h₂
  commit_skip := by
    intro S U V₁ V₂ k L hI hL hc hs
    exact (hl (S.slotRound k)).commit_skip hI hL hc hs
  commit_link := by
    intro S U V k j L A hI hL hc hA he
    obtain ⟨i, hi, hh⟩ := (hl (S.slotRound k)).commit_link hI hL hc hA he
    exact ⟨i, hr _ ▸ hi, hh⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hI hL₁ hL₂ hc hA he hi hm hh hleast
    exact (hl (S.slotRound k)).commit_link_unique hI hL₁ hL₂ hc hA he
      (by simpa only [compose, hr] using hi) hm hh ((compose_least rules ht).mp hleast)
  skip_link := by
    intro S U V k i L A hI hs hL hi
    exact (hl (S.slotRound k)).skip_link hI hs hL (by simpa only [compose, hr] using hi)
  link_unique := by
    intro S U k j i L₁ L₂ A hI hL₁ hL₂ hA he hi hm hh₁ hh₂ hm₁ hm₂
    exact (hl (S.slotRound k)).link_unique hI hL₁ hL₂ hA he
      (by simpa only [compose, hr] using hi) hm hh₁ hh₂
      ((compose_least rules ht).mp hm₁) ((compose_least rules ht).mp hm₂)
  commit_mono := by
    intro S U V V' L r hI hsub hc
    exact (hl r).commit_mono (S := S) hI hsub hc
  skip_mono := by
    intro S U V V' k hI hsub hs
    exact (hl (S.slotRound k)).skip_mono hI hsub hs
  skip_congr := by
    intro S₁ S₂ U V k hI hround hleader hs
    change (rules (S₂.slotRound k)).Skip U V S₂ k
    rw [← hround]
    exact (hl (S₁.slotRound k)).skip_congr hI hround hleader hs
  link_congr := by
    intro S₁ S₂ U A L i k hround hleader hh
    change (rules (S₂.slotRound k)).Link i U A L S₂ k
    rw [← hround]
    exact (hl (S₁.slotRound k)).link_congr hround hleader hh

/-- **SH16b.** The relation's agreement at the composite's laws. -/
theorem compose_decided_unique (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (hl : ∀ r, (rules r).Laws) (hr : ∀ r, (rules r).rungs = (rules 0).rungs)
    (ht : ∀ r, (rules r).tie = (rules 0).tie) {S : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {V₁ V₂ : U.View} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : (compose rules).Decided (S := S) U V₁ k v₁)
    (h₂ : (compose rules).Decided (S := S) U V₂ k v₂) : v₁ = v₂ :=
  AnchoredRule.decided_unique (compose_laws rules hl hr ht) trivial h₁ V₂ v₂ h₂

/-- **SH16c.** Field by field, by definition. -/
theorem steelheadAnchored_eq_compose {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (w : ℕ → ℕ) :
    steelheadAnchored Validator BlockId Payload w =
      compose fun r => MahiMahi.mahiMahiAnchored Validator BlockId Payload (w r) :=
  rfl

/-! ## SH19, the periodic class -/

/-- The periodic wave is at least the smaller of the two waves. -/
theorem periodic_two_le {ws wa k : ℕ} (hws : 2 ≤ ws) (hwa : 2 ≤ wa) (r : ℕ) :
    2 ≤ periodic ws wa k r := by
  unfold periodic
  split <;> omega

/-- The periodic wave is at least three once both waves are. -/
theorem periodic_three_le {ws wa k : ℕ} (hws : 3 ≤ ws) (hwa : 3 ≤ wa) (r : ℕ) :
    3 ≤ periodic ws wa k r := by
  unfold periodic
  split <;> omega

/-- The periodic wave is at most the larger of the two waves. -/
theorem periodic_le_max (ws wa k r : ℕ) : periodic ws wa k r ≤ max ws wa := by
  unfold periodic
  split
  · exact le_max_right _ _
  · exact le_max_left _ _

section PeriodicClass

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Faults Validator]
  {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The periodic wave varies with the round**: at two distinct waves and a period of two or
more, round `0` is asynchronous and round `1` is not, so their wave offsets differ. -/
theorem periodic_waveAt_not_const {ws wa k : ℕ} (hws : 2 ≤ ws) (hwa : 2 ≤ wa) (hne : ws ≠ wa)
    (hk : 2 ≤ k) :
    ¬ ∀ r r', (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).waveAt r =
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).waveAt r' := by
  intro h
  have h01 := h 0 1
  simp only [steelheadAnchored_waveAt, periodic, Nat.zero_mod, Nat.one_mod_eq_zero_iff,
    ite_true] at h01
  rw [if_neg (show ¬ k = 1 by omega)] at h01
  omega

/-- **SH19.** The bounds are the waves', the spanning is `spansEligible_of_le`, and the laws are
`Properties.lean`'s at the periodic wavelength. -/
theorem periodicClass : Interface.PeriodicClass Validator BlockId Payload := by
  intro ws wa k hws hwa
  refine ⟨periodic_two_le hws hwa, periodic_le_max ws wa k, ?_,
    fun hne hk => periodic_waveAt_not_const hws hwa hne hk,
    SteelheadProperties.agree (periodic_two_le hws hwa),
    SteelheadProperties.steelheadExtendLaws (periodic_two_le hws hwa),
    SteelheadProperties.shSupport_local (periodic_two_le hws hwa),
    SteelheadProperties.shSupport_commits (periodic_two_le hws hwa),
    fun hws3 hwa3 => SteelheadProperties.shSupport_ofCoverage (periodic_three_le hws3 hwa3)⟩
  intro S hid
  exact spansEligible_of_le (S := S) (by omega) (periodic_le_max ws wa k) hid

end PeriodicClass

end Steelhead

end LeanDag
