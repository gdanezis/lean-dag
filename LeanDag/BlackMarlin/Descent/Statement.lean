import LeanDag.BlackMarlin.Model.Descent
/-!
# Black Marlin — the descent computed, stated

`Ledger/Statement.lean` takes the record `commit`'s descent leaves as
given; this phase computes the descent and discharges that hypothesis
(`black-marlin.md` §11). BME1 and BME2 say the choice of L21–L24 is a
sound and total function of the candidate; BME3 says the generated
record is a `Flush`; BME4 says the record below a visited block is that
block's own, which is why BME5's agreement — two records reaching one
block agree at every round below it — needs no hypothesis about the
rounds between.

Ties are broken by the `≤`-least survivor under a `LinearOrder` on
identifiers, as Odontoceti and Mahi-Mahi read their canonical choices;
nothing below depends on which rule it is.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Descent

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BME1, the choice is sound.** -/
def DescendSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B A : BlockId), B ∈ U.ids → descend U B = some A →
    A ∈ U.ids ∧ IsAnchorBlock U A ∧ A ∈ strongOf U B ∧
      (U.block A).round = maxAnchorRound U (strongOf U B) ∧
      (U.block A).round < (U.block B).round

/-- **BME2, and total where an anchor lies below.** -/
def DescendTotal (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B : BlockId), (anchorsOf U (strongOf U B)).Nonempty → (descend U B).isSome

/-- **BME3, the record is a flush record.** The three conditions
`Flush` asks for, here derived from the descent rather than assumed of
it. -/
def RecordIsFlush (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B : BlockId), B ∈ U.ids → IsAnchorBlock U B →
    (∀ (ρ : ℕ) (L : BlockId), flushRecord U B ρ = some L → IsAnchor U ρ L) ∧
    (∀ (ρ : ℕ) (L M : BlockId), flushRecord U B ρ = some L →
      flushRecord U B (ρ + 1) = some M → L ∈ (U.block M).refs) ∧
    (∀ (ρ : ℕ) (M : BlockId), flushRecord U B (ρ + 1) = some M →
      (coneAnchors U M ρ).Nonempty → (flushRecord U B ρ).isSome)

/-- **BME4, the record below a visited block is that block's own.** -/
def Suffix (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B M : BlockId) (σ ρ : ℕ), B ∈ U.ids →
    flushRecord U B σ = some M → ρ ≤ σ →
    flushRecord U B ρ = flushRecord U M ρ

/-- **BME5, agreement with no definedness hypothesis.** Two descents that
reach the same block at a round agree at every round below it, whatever
happens between — which is what BMD3 has to assume of an abstract
record. -/
def AgreeBelow (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B₁ B₂ M : BlockId) (σ ρ : ℕ), B₁ ∈ U.ids → B₂ ∈ U.ids →
    flushRecord U B₁ σ = some M → flushRecord U B₂ σ = some M → ρ ≤ σ →
    flushRecord U B₁ ρ = flushRecord U B₂ ρ

/-- The descent of `commit`, over every fault configuration, rotation and
block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    DescendSound U ∧ DescendTotal U ∧ RecordIsFlush U ∧ Suffix U ∧ AgreeBelow U

end Descent

end BlackMarlin

end LeanDag
