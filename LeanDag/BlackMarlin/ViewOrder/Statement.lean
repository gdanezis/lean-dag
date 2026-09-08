import LeanDag.BlackMarlin.Order.Statement
/-!
# Black Marlin — the delivered order at a validator's view, stated

BMV1 and BMV2 conclude `B ∈ history U L`: membership in what a validator
delivers, not position in the sequence, which `black-marlin.md` §15 left
open. BMT1 says two records flushing at a reliably anchored round flush
the same block — there being only one such block, non-equivocation
ruling out a second. BMT2 carries that agreement down through any
stretch either record flushes at. BMT3 says where every anchor below a
round is reliable, two records flushing at the same rounds deliver the
same list.

**Which is exactly as far as it goes.** BMT3's hypothesis cannot be
weakened to allow one Byzantine anchor below: in the execution of §13
two records deliver `5` before `7` and `7` before `5`, both reliably
authored with no twin, ordered only by which segment the descents'
diverging choice a round below put them in. Definition 1's Total order
fails on honest blocks, independent of which twin the filter prefers —
only a rule making the two descents agree would fix it, which is §14's
repair, and §15 records that it has no live implementation.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace ViewOrder

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BMT1, a reliable anchor pins every record.** The block flushed at
such a round is that round's anchor, and its author is correct, so
`no_equivocation` leaves one candidate in the whole universe. No view
enters the argument. -/
def ReliableAnchorPins (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ : ℕ) (L₁ L₂ : BlockId),
    Rot.anchor ρ ∈ (Correct : Finset Validator) →
    f₁.block ρ = some L₁ → f₂.block ρ = some L₂ → L₁ = L₂

/-- **BMT2, and agreement descends from it.** BMD3 needs a round the two
records agree at; a reliably anchored round both flush at is one, by
BMT1, with nothing assumed about either validator's view. -/
def AgreeOnReliableStretch (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ d : ℕ),
    Rot.anchor (ρ + d) ∈ (Correct : Finset Validator) →
    (f₁.block (ρ + d)).isSome → (f₂.block (ρ + d)).isSome →
    (∀ i, 0 < i → i ≤ d → (f₁.block (ρ + i)).isSome) →
    f₁.block ρ = f₂.block ρ

/-- **BMT3, and the delivered lists coincide.** Where no Byzantine
validator anchors a round below `n`, two records that flush at the same
rounds deliver one list — Definition 1's Total order, unconditionally,
on that stretch. The hypothesis is tight:
`LeanDagTest/BlackMarlin/Divergence` exhibits a single Byzantine anchor
below producing two reliably authored blocks in opposite orders. -/
def OrderAgreesWhenAnchorsReliable (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (τ : TopoSort U) (n : ℕ),
    (∀ σ, σ < n → Rot.anchor σ ∈ (Correct : Finset Validator)) →
    (∀ σ, σ < n → ((f₁.block σ).isSome ↔ (f₂.block σ).isSome)) →
    deliverSeq U f₁ τ n = deliverSeq U f₂ τ n

/-- The delivered order of the Black Marlin commit rule where the
rotation names reliable validators, over every fault configuration,
rotation and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    ReliableAnchorPins U ∧ AgreeOnReliableStretch U ∧ OrderAgreesWhenAnchorsReliable U

end ViewOrder

end BlackMarlin

end LeanDag
