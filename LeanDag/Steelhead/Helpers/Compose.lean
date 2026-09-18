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
      (rules (S.kind k)).Least (S := S) U A i k L := by
  unfold AnchoredRule.Least
  simp only [compose, ht]

/-- **SH16a.** Every law of the composite at a slot is the law of the slot's rule. -/
theorem compose_laws (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (hl : ∀ r, (rules r).Laws) (hr : ∀ r, (rules r).rungs = (rules 0).rungs)
    (ht : ∀ r, (rules r).tie = (rules 0).tie) : (compose rules).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ hI hL₁ hL₂ h₁ h₂
    exact (hl (S.kind k)).commit_unique hI hL₁ hL₂ h₁ h₂
  commit_skip := by
    intro S U V₁ V₂ k L hI hL hc hs
    exact (hl (S.kind k)).commit_skip hI hL hc hs
  commit_link := by
    intro S U V k j L A hI hL hc hA he
    obtain ⟨i, hi, hh⟩ := (hl (S.kind k)).commit_link hI hL hc hA he
    exact ⟨i, hr _ ▸ hi, hh⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hI hL₁ hL₂ hc hA he hi hm hh hleast
    exact (hl (S.kind k)).commit_link_unique hI hL₁ hL₂ hc hA he
      (by simpa only [compose, hr] using hi) hm hh ((compose_least rules ht).mp hleast)
  skip_link := by
    intro S U V k i L A hI hs hL hi
    exact (hl (S.kind k)).skip_link hI hs hL (by simpa only [compose, hr] using hi)
  link_unique := by
    intro S U k j i L₁ L₂ A hI hL₁ hL₂ hA he hi hm hh₁ hh₂ hm₁ hm₂
    exact (hl (S.kind k)).link_unique hI hL₁ hL₂ hA he
      (by simpa only [compose, hr] using hi) hm hh₁ hh₂
      ((compose_least rules ht).mp hm₁) ((compose_least rules ht).mp hm₂)
  commit_mono := by
    intro S U V V' L r κ hI hsub hc
    exact (hl κ).commit_mono (S := S) hI hsub hc
  skip_mono := by
    intro S U V V' k hI hsub hs
    exact (hl (S.kind k)).skip_mono hI hsub hs
  skip_congr := by
    intro S₁ S₂ U V k hI hround hleader hkind hs
    change (rules (S₂.kind k)).Skip U V S₂ k
    rw [← hkind]
    exact (hl (S₁.kind k)).skip_congr hI hround hleader hkind hs
  link_congr := by
    intro S₁ S₂ U A L i k hround hleader hkind hh
    change (rules (S₂.kind k)).Link i U A L S₂ k
    rw [← hkind]
    exact (hl (S₁.kind k)).link_congr hround hleader hkind hh

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
      compose fun κ => MahiMahi.mahiMahiAnchored Validator BlockId Payload (w κ) :=
  rfl

/-! ## SH19, the periodic class -/

/-- **A period of two or more assigns both kinds**: round `0` is asynchronous and round `1` is
not. -/
theorem periodicKind_not_const {k : ℕ} (hk : 2 ≤ k) :
    ∃ r r', periodicKind k r ≠ periodicKind k r' := by
  refine ⟨0, 1, ?_⟩
  unfold periodicKind
  rw [Nat.zero_mod, if_pos rfl, Nat.mod_eq_of_lt (by omega : 1 < k), if_neg (by omega)]
  decide

section PeriodicClass

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Faults Validator]
  {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The pair's wave varies with the kind**: at two distinct waves the two kinds' wave offsets
differ. -/
theorem wavelength_waveAt_ne {ws wa : ℕ} (hws : 2 ≤ ws) (hwa : 2 ≤ wa) (hne : ws ≠ wa) :
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 0 ≠
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 1 := by
  simp only [steelheadAnchored_waveAt, wavelength_zero, wavelength_one]
  omega

/-- **SH19.** The bounds are the waves', the spanning is `spansEligible_of_le`, and the laws are
`Properties.lean`'s at the pair's wavelength. -/
theorem periodicClass : Interface.PeriodicClass Validator BlockId Payload := by
  intro ws wa k hws hwa
  refine ⟨wavelength_two_le hws hwa, wavelength_le_max ws wa, ?_,
    fun hne => wavelength_waveAt_ne hws hwa hne, fun hk => periodicKind_not_const hk,
    SteelheadProperties.agree (wavelength_two_le hws hwa),
    SteelheadProperties.steelheadExtendLaws (wavelength_two_le hws hwa),
    SteelheadProperties.shSupport_local (wavelength_two_le hws hwa),
    SteelheadProperties.shSupport_commits (wavelength_two_le hws hwa),
    fun hws3 hwa3 => SteelheadProperties.shSupport_ofCoverage (wavelength_three_le hws3 hwa3)⟩
  intro S hid
  exact spansEligible_of_le (S := S) (by omega) (fun s => wavelength_le_max ws wa (S.kind s)) hid

end PeriodicClass

end Steelhead

end LeanDag
