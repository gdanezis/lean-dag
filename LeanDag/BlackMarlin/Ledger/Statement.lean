import LeanDag.BlackMarlin.Model.Ledger
/-!
# Black Marlin — the delivered order, stated

What `commit`'s descent settles that the commit rule alone does not
(`black-marlin.md` §11). BM6 and BMA3 give the delivered **set**; the
order is the record of anchors the descent flushed. BMD1 says the
descent has at most one candidate where it steps by one round, so BMD2
and BMD3 carry agreement at a round down through any stretch the record
flushes at every round of. BMD4 gives BMD3 its starting point: two
records flushing directly committed anchors at one round flush the
same block. BMD5 is the phase's point — the commit rule's link clause,
used only once for safety, here stops a *committed* anchor's round from
being the one the descent skips, which is what would otherwise let two
twins of an equivocating anchor both become candidates. BMD6 packages
the result as a ledger.

**What is left over.** Where the descent does skip an anchor round and
lands on an equivocating one, the paper's tie-break L21–L24 is not
modelled, so BMD3 carries its stretch as a hypothesis rather than
deriving it. Ordering *within* a segment is the deterministic sort `τ`,
not modelled either, so the ledger is a set and a record's rounds are
the positions in it.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Ledger

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **BMD1, the step is unambiguous.** -/
def StepUnique (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (ρ : ℕ) (M X Y : BlockId),
    M ∈ U.ids → (U.block M).round = ρ + 1 →
    X ∈ coneAnchors U M ρ → Y ∈ coneAnchors U M ρ → X = Y

/-- **BMD1′, a Byzantine anchor is necessary for a tie.** At a round whose
elected validator is reliable, the candidates are a singleton, so a
choice needs both a skipped anchor round and an equivocating anchor
where the descent lands. -/
def CorrectAnchorUnique (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (ρ : ℕ) (C X Y : BlockId),
    Rot.anchor ρ ∈ (Correct : Finset Validator) →
    X ∈ coneAnchors U C ρ → Y ∈ coneAnchors U C ρ → X = Y

/-- **BMD2, agreement descends one round.** Where both records flush, the
step makes their blocks candidates of one cone; where one does not, the
cone is empty and neither does. -/
def AgreeStep (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ : ℕ) (M : BlockId),
    f₁.block (ρ + 1) = some M → f₂.block (ρ + 1) = some M →
    f₁.block ρ = f₂.block ρ

/-- **BMD3, agreement descends a stretch.** The definedness hypothesis is
exactly the descent not skipping a round; where it does, the paper's
tie-break would be needed and this says nothing. -/
def AgreeBelow (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ d : ℕ),
    f₁.block (ρ + d) = f₂.block (ρ + d) →
    (∀ i, 0 < i → i ≤ d → (f₁.block (ρ + i)).isSome) →
    f₁.block ρ = f₂.block ρ

/-- **BMD4, directly committed anchors pin the record.** -/
def CommittedPins (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (σ : ℕ) (L₁ L₂ : BlockId),
    f₁.block σ = some L₁ → f₂.block σ = some L₂ →
    Committed U L₁ σ → Committed U L₂ σ →
    f₁.block σ = f₂.block σ

/-- **BMD5, the link clause keeps the descent from skipping.** Above a
committed anchor sits a supported anchor, which propagation puts in every
cone from three rounds up — so a descent arriving there finds a candidate
rather than an empty round. -/
def LinkPopulates (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L C : BlockId) (ρ : ℕ),
    Committed U L ρ → C ∈ U.ids → ρ + 3 ≤ (U.block C).round →
    (coneAnchors U C (ρ + 1)).Nonempty

/-- **BMD6, the ledger.** Nothing output is dropped; records that agree
below a round output the same blocks there; a block enters at exactly one
round; and records that agree concur on which. The last is total-order
safety at the granularity of segments — the order *within* one needs
`τ`. -/
def Ledger (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (f : Flush U) (n m : ℕ), n ≤ m → ledgerSet U f.block n ⊆ ledgerSet U f.block m) ∧
  (∀ (f₁ f₂ : Flush U) (n : ℕ),
    (∀ ρ, ρ < n → f₁.block ρ = f₂.block ρ) →
    ledgerSet U f₁.block n = ledgerSet U f₂.block n) ∧
  (∀ (f : Flush U) (b : BlockId) (ρ₁ ρ₂ : ℕ),
    OutputAt U f.block b ρ₁ → OutputAt U f.block b ρ₂ → ρ₁ = ρ₂) ∧
  (∀ (f₁ f₂ : Flush U) (n : ℕ) (b : BlockId) (ρ : ℕ),
    (∀ σ, σ < n → f₁.block σ = f₂.block σ) → ρ < n →
    OutputAt U f₁.block b ρ → OutputAt U f₂.block b ρ) ∧
  (∀ (f : Flush U) (ρ : ℕ) (L b : BlockId),
    f.block ρ = some L → Reaches U L b → b ∈ ledgerSet U f.block (ρ + 1))

/-- The delivered order of the Black Marlin commit rule, over every fault
configuration, rotation and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    StepUnique U ∧ CorrectAnchorUnique U ∧ AgreeStep U ∧ AgreeBelow U ∧ CommittedPins U ∧
      LinkPopulates U ∧ Ledger U

end Ledger

end BlackMarlin

end LeanDag
