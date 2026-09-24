import LeanDag.Steelhead.Model.Compose
import LeanDag.Steelhead.Model.Decision
import LeanDag.Steelhead.Properties
/-!
# The interface composes — statement

The paper's Theorem 1 at the interface level (`steelhead.md` §3), for
**any** family of rules, named or not: whichever rule a slot is decided
by, the anchor search reads the slot's own rule, so the verdicts agree
across views. Two claims:

* **SH16a, the laws compose** — if every rule of a family satisfies the
  anchored relation's laws, and the family agrees on its rung count,
  tie-break and anchor, the composite satisfies them: each law of the composite at
  a slot is the law of the slot's own rule, since the composite reads
  every datum of a slot from that rule, the anchor's rule never entering;
* **SH16b, the composite agrees** — the relation's agreement across
  views at the composite's laws, for any two views and routes.

The laws are the paper's clauses A2 and A3 in the relation's terms, at
each rule's own wave: what the intersection law and the exclusion of
certificates by a skip must give for the anchor search to agree. A rule
of the interface that fails them, or a pair that disagrees on rungs,
ties or anchors, is outside Theorem 1.

The two pairs the paper instantiates are stated in the sibling
directories, at the families `Model/Pair.lean` names: `MahiMahiPair/`
for Mysticeti and Mahi-Mahi at `n ≥ 3f + 1` (SH-MM16c, SH-MM19), and
`BlueBottlePair/` for Odontoceti and Async BlueBottle at `n ≥ 5f + 1`
(SH-BB3, SH-BB16). Nothing here mentions either.

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
    -- every rule of the family satisfies the laws, and the family agrees on rungs, ties and
    -- anchors
    (∀ r, (rules r).Laws) → (∀ r, (rules r).rungs = (rules 0).rungs) →
    (∀ r, (rules r).tie = (rules 0).tie) → (∀ r, (rules r).Anchor = (rules 0).Anchor) →
    -- then so does the composite
    (compose rules).Laws

/-- **SH16b, the composite agrees.** -/
def ComposeAgreement (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct) [S : Slots Validator]
    (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    (∀ r, (rules r).Laws) → (∀ r, (rules r).rungs = (rules 0).rungs) →
    (∀ r, (rules r).tie = (rules 0).tie) → (∀ r, (rules r).Anchor = (rules 0).Anchor) →
    (compose rules).Decided (S := S) U V₁ k v₁ → (compose rules).Decided (S := S) U V₂ k v₂ →
    v₁ = v₂

/-- The interface, over every fault configuration and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload),
    LawsCompose Validator BlockId Payload ∧ ComposeAgreement U

end Interface

end Steelhead

end LeanDag
