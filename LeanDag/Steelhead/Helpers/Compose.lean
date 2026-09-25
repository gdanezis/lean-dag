import LeanDag.Steelhead.Interface.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Helpers — the composite

Generated lemma infrastructure for `Interface/Statement.lean`; not part
of the audit surface. Each law of the composite is the law of the slot's
own rule, once the composite's rung count, tie-break and anchor are
rewritten to that rule's, which the family's agreement on them allows. Nothing here
names a pair; the two instantiations are in `Helpers/MahiMahiPair.lean`
and `Helpers/BlueBottlePair.lean`.
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

/-- The composite's anchor is the slot's rule's, once the anchors agree. -/
theorem compose_anchor (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (ha : ∀ r, (rules r).Anchor = (rules 0).Anchor) (κ : ℕ)
    {U : BlockRecord Validator BlockId Payload P honest} {A : BlockId} :
    (compose rules).Anchor U A ↔ (rules κ).Anchor U A := by
  rw [ha κ]
  rfl

/-- **SH16a.** Every law of the composite at a slot is the law of the slot's rule. -/
theorem compose_laws (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (hl : ∀ r, (rules r).Laws) (hr : ∀ r, (rules r).rungs = (rules 0).rungs)
    (ht : ∀ r, (rules r).tie = (rules 0).tie) (ha : ∀ r, (rules r).Anchor = (rules 0).Anchor) :
    (compose rules).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ hI hL₁ hL₂ h₁ h₂
    exact (hl (S.kind k)).commit_unique hI hL₁ hL₂ h₁ h₂
  commit_skip := by
    intro S U V₁ V₂ k L hI hL hc hs
    exact (hl (S.kind k)).commit_skip hI hL hc hs
  commit_link := by
    intro S U V k j L A hI hL hc hA hanc he
    obtain ⟨i, hi, hh⟩ := (hl (S.kind k)).commit_link hI hL hc hA
      ((compose_anchor rules ha (S.kind k)).mp hanc) he
    exact ⟨i, hr _ ▸ hi, hh⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hI hL₁ hL₂ hc hA hanc he hi hm hh hleast
    exact (hl (S.kind k)).commit_link_unique hI hL₁ hL₂ hc hA
      ((compose_anchor rules ha (S.kind k)).mp hanc) he
      (by simpa only [compose, hr] using hi) hm hh ((compose_least rules ht).mp hleast)
  skip_link := by
    intro S U V k i L A hI hs hL hi hanc
    exact (hl (S.kind k)).skip_link hI hs hL (by simpa only [compose, hr] using hi)
      ((compose_anchor rules ha (S.kind k)).mp hanc)
  link_unique := by
    intro S U k j i L₁ L₂ A hI hL₁ hL₂ hA hanc he hi hm hh₁ hh₂ hm₁ hm₂
    exact (hl (S.kind k)).link_unique hI hL₁ hL₂ hA
      ((compose_anchor rules ha (S.kind k)).mp hanc) he
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
  anchor_commit := by
    intro S U V k L hI hL hc
    exact (compose_anchor rules ha (S.kind k)).mpr ((hl (S.kind k)).anchor_commit hI hL hc)
  anchor_link := by
    intro S U k j i A L hI hA hanc he hL hi hh
    exact (compose_anchor rules ha (S.kind k)).mpr ((hl (S.kind k)).anchor_link hI hA
      ((compose_anchor rules ha (S.kind k)).mp hanc) he hL
      (by simpa only [compose, hr] using hi) hh)

/-- **SH16b.** The relation's agreement at the composite's laws. -/
theorem compose_decided_unique (rules : ℕ → AnchoredRule Validator BlockId Payload P honest)
    (hl : ∀ r, (rules r).Laws) (hr : ∀ r, (rules r).rungs = (rules 0).rungs)
    (ht : ∀ r, (rules r).tie = (rules 0).tie) (ha : ∀ r, (rules r).Anchor = (rules 0).Anchor)
    {S : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {V₁ V₂ : U.View} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : (compose rules).Decided (S := S) U V₁ k v₁)
    (h₂ : (compose rules).Decided (S := S) U V₂ k v₂) : v₁ = v₂ :=
  AnchoredRule.decided_unique (compose_laws rules hl hr ht ha) trivial h₁ V₂ v₂ h₂

end Steelhead

end LeanDag
