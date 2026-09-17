import LeanDag.Steelhead.Model.Compose
import LeanDag.Steelhead.Model.Decision
import LeanDag.Steelhead.Properties
/-!
# The interface composes — statement

The paper's Theorem 1 at the interface level (`steelhead.md` §3): any
family of rules whose laws hold composes into a rule whose laws hold,
so that its verdicts agree across views, and Steelhead is one such
composite; and the periodic wavelength, the paper's dial, is a
wavelength function the laws' hypotheses admit and one that varies.
Four claims:

* **SH16a, the laws compose** — if every rule of a family satisfies the
  anchored relation's laws, and the family agrees on its rung count and
  tie-break, the composite satisfies them: each law of the composite at
  a slot is the law of the slot's own rule, since the composite reads
  every datum of a slot from that rule, the anchor's rule never entering;
* **SH16b, the composite agrees** — the relation's agreement across
  views at the composite's laws, for any two views and routes;
* **SH16c, Steelhead is a composite** — `steelheadAnchored w` is the
  composite of Mahi-Mahi's rule read at `w r`, by definition, so SH2 is
  an instance of SH16b;
* **SH19, the periodic class** — the paper's dial `w(r) = wa` at every
  `k`-th round and `ws` elsewhere (`periodic`), for any two waves of
  two rounds or more, is a wavelength function the results above take:
  every round's wave is at least two and at most the larger wave, so an
  identity-round schedule spans at that wave; agreement, the extension
  laws persistence rests on, and the support's locality, coverage and
  commit laws hold at it, the same way they hold at any wavelength
  function of two rounds or more, coverage asking three; and at
  `ws ≠ wa` and `k ≥ 2` no constant wave
  equals it, so what `waveAt` being a function of the round admits is a
  wave that varies, not a constant in disguise.

The laws are the paper's clauses A2 and A3 in the relation's terms, at
each rule's own wave: what the intersection law and the exclusion of
certificates by a skip must give for the anchor search to agree. A rule
of the interface that fails them, or a pair that disagrees on rungs or
ties, is outside Theorem 1, as the paper's discharge table has it for
the clauses it marks open.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Interface

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH16a, the laws compose.** -/
def LawsCompose (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] : Prop :=
  ∀ (rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct),
    -- every rule of the family satisfies the laws, and the family agrees on rungs and ties
    (∀ r, (rules r).Laws) → (∀ r, (rules r).rungs = (rules 0).rungs) →
    (∀ r, (rules r).tie = (rules 0).tie) →
    -- then so does the composite
    (compose rules).Laws

/-- **SH16b, the composite agrees.** -/
def ComposeAgreement (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct) [S : Slots Validator]
    (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    (∀ r, (rules r).Laws) → (∀ r, (rules r).rungs = (rules 0).rungs) →
    (∀ r, (rules r).tie = (rules 0).tie) →
    (compose rules).Decided (S := S) U V₁ k v₁ → (compose rules).Decided (S := S) U V₂ k v₂ →
    v₁ = v₂

/-- **SH16c, Steelhead is a composite.** -/
def SteelheadComposes (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] : Prop :=
  ∀ w : ℕ → ℕ,
    steelheadAnchored Validator BlockId Payload w =
      compose fun r => MahiMahi.mahiMahiAnchored Validator BlockId Payload (w r)

/-- **SH19, the periodic class.** -/
def PeriodicClass (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] : Prop :=
  ∀ ws wa k : ℕ, 2 ≤ ws → 2 ≤ wa →
    -- every round's wave is at least two and at most the larger wave ...
    (∀ r, 2 ≤ periodic ws wa k r) ∧ (∀ r, periodic ws wa k r ≤ max ws wa) ∧
    -- ... so an identity-round schedule spans at that wave
    (∀ [S : Slots Validator], (∀ s, S.slotRound s = s) →
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).SpansEligible (S := S)
        (max ws wa)) ∧
    -- the wave varies: at two distinct waves and a period of two or more, no constant equals it
    (ws ≠ wa → 2 ≤ k → ¬ ∀ r r',
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).waveAt r =
        (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).waveAt r') ∧
    -- and the laws hold at it: agreement, the extension laws persistence rests on, the support's
    -- locality and commits, and its coverage law at waves of three or more
    Properties.Agree (SteelheadProperties.steelheadRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload) (periodic ws wa k)) ∧
    (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).ExtendLaws ∧
    Properties.Support.Local (R := SteelheadProperties.steelheadRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload) (periodic ws wa k))
      (SteelheadProperties.shSupport (periodic ws wa k)) ∧
    Properties.Support.Commits (R := SteelheadProperties.steelheadRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload) (periodic ws wa k))
      (SteelheadProperties.shSupport (periodic ws wa k)) (coreReliability Validator) ∧
    (3 ≤ ws → 3 ≤ wa →
      Timed.OfCoverage (R := SteelheadProperties.steelheadRule (Validator := Validator)
        (BlockId := BlockId) (Payload := Payload) (periodic ws wa k))
        (SteelheadProperties.shSupport (periodic ws wa k)) (coreReliability Validator))

/-- The interface, over every fault configuration and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload),
    LawsCompose Validator BlockId Payload ∧ ComposeAgreement U ∧
      SteelheadComposes Validator BlockId Payload ∧ PeriodicClass Validator BlockId Payload

end Interface

end Steelhead

end LeanDag
