import LeanDag.Steelhead.Model.Decision
import LeanDag.Common.Ledger
/-!
# Atomic broadcast at a wavelength function — statement

The paper's Definition 1, clause by clause, read off a validator's
verdict assignment over a settled prefix (`steelhead.md` §3), as the
ledger theorems (SH13) and the liveness theorems make them true. Four
claims:

* **SH17a, agreement** — "if one honest validator commits a block, all
  honest validators eventually commit it": a block one view delivers
  over a settled prefix, every view delivers over any settled prefix at
  least as long. That every view eventually settles such a prefix is the
  liveness half, SH6b under synchrony and SH14b/SH15 under asynchrony;
* **SH17b, integrity** — "each honest validator commits a block at most
  once, and only if it was proposed by its author": a block enters the
  ledger at one slot, and a delivered block is a block of the record,
  which carries its author;
* **SH17c, validity** — "if an honest validator proposes a block, all
  honest validators eventually commit it": after GST, a reliable block
  lies in the cone of every reliable block two rounds up, so it is
  delivered with the first committed reliable leader above, once the
  prefix below is settled. That such a leader commits is SH6a, that the
  prefix settles SH6b; under asynchrony the committed leaders are the
  coin's (SH14, SH15) and the delivery of a reliable block to them is
  the substrate's, which the model states as `SynchronisedOn` and not
  otherwise;
* **SH17d, total order** — "if an honest validator commits `b` before
  `b'`, no honest validator commits `b'` before `b`": the slots at which
  two blocks enter the ledger are the same in every view that settled
  them, so their order is. Within one slot the order of the blocks a
  commit releases is a tie-break the development does not assume.

SH17a and SH17d assume `2 ≤ w r`, what the laws need; SH17b assumes
nothing of the wave; SH17c reads no wave, since a committed leader's
cone is what it reads.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Broadcast

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH17a, agreement.** -/
def Agreement (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n m : ℕ) (g₁ g₂ : ℕ → Option BlockId)
    (b : BlockId),
    (∀ r, 2 ≤ w r) →
    -- V₁ settled every slot below n, V₂ every slot below m ≥ n
    (∀ k, k < n → Decided w U V₁ k (g₁ k)) → (∀ k, k < m → Decided w U V₂ k (g₂ k)) → n ≤ m →
    -- a block V₁ delivers, V₂ delivers
    b ∈ ledgerSet U g₁ n → b ∈ ledgerSet U g₂ m

/-- **SH17b, integrity.** -/
def Integrity (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (n : ℕ) (g : ℕ → Option BlockId) (b : BlockId)
    (k₁ k₂ : ℕ),
    (∀ k, k < n → Decided w U V k (g k)) →
    -- a delivered block is a block of the record, so one its author proposed ...
    (b ∈ ledgerSet U g n → b ∈ U.ids) ∧
      -- ... and it enters the ledger at one slot
      (OutputAt U g b k₁ → OutputAt U g b k₂ → k₁ = k₂)

/-- **SH17c, validity.** -/
def Validity (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (n k r : ℕ)
    (g : ℕ → Option BlockId) (b L : BlockId),
    -- V settled every slot below n, and committed L at slot k below n
    (∀ k, k < n → Decided w U V k (g k)) → k < n → g k = some L →
    -- b is a reliable block at round r, and T is synchronised from r and populates r + 1
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    SynchronisedOn U T r → PopulatedOn U T (r + 1) →
    b ∈ U.ids → (U.block b).round = r → (U.block b).creator ∈ T →
    -- slot k lies two rounds up or more
    r + 2 ≤ S.slotRound k →
    -- then V delivers b
    b ∈ ledgerSet U g n

/-- **SH17d, total order.** -/
def TotalOrder (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n : ℕ) (g₁ g₂ : ℕ → Option BlockId)
    (b b' : BlockId) (k k' : ℕ),
    (∀ r, 2 ≤ w r) →
    -- both views settled every slot below n
    (∀ i, i < n → Decided w U V₁ i (g₁ i)) → (∀ i, i < n → Decided w U V₂ i (g₂ i)) →
    -- V₁ outputs b at slot k and b' at the later slot k', below n
    OutputAt U g₁ b k → OutputAt U g₁ b' k' → k < k' → k' < n →
    -- then V₂ outputs them at the same slots, so in the same order
    OutputAt U g₂ b k ∧ OutputAt U g₂ b' k'

/-- Atomic broadcast at a wavelength function, over every fault configuration, schedule, block
universe and wavelength function the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ),
    Agreement U w ∧ Integrity U w ∧ Validity U w ∧ TotalOrder U w

end Broadcast

end Steelhead

end LeanDag
