import LeanDag.Steelhead.Model.Decision
import LeanDag.Common.Ledger
/-!
# The ledger at a wavelength function — statement

What the output layer owes once the verdicts are agreed
(`steelhead.md` §3): the paper's Corollary 2, order and integrity, at
the rule of a wavelength function. Five claims, all read off a validator's
verdict assignment `g` over a settled prefix of slots:

* **SH13a, the committed-leader sequence is agreed** — two validators
  that settled the same prefix read off the same list, in slot order,
  which is round order since `slotRound` is monotone;
* **SH13b, the ledger is agreed** — and so is the set of blocks it
  delivers, the causal histories of those leaders;
* **SH13c, the ledger is monotone** — nothing already output is dropped
  as further slots settle;
* **SH13d, a block enters at one slot, agreed** — the slot a block
  enters at is the same in both views, and no block enters at two slots;
* **SH13e, a committed block belongs to one slot** — the integrity half:
  without it one block could be delivered by two slots.

SH13a to SH13d assume `2 ≤ w r`, what Steelhead's laws need, and a
settled prefix; SH13e assumes neither, since a commit names its slot
whatever the wave. They are order and integrity, not progress: under the
stall (SH8) the prefix is short, and that is a liveness question.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Ledger

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH13a to SH13d, the output of a settled prefix.** -/
def Output (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n : ℕ) (g₁ g₂ : ℕ → Option BlockId),
    (∀ r, 2 ≤ w r) →
    -- each view settled every slot below n, g its verdicts there
    (∀ k, k < n → Decided w U V₁ k (g₁ k)) →
    (∀ k, k < n → Decided w U V₂ k (g₂ k)) →
    -- the committed-leader sequence and the ledger are the same ...
    commitSeq g₁ n = commitSeq g₂ n ∧
      ledgerSet U g₁ n = ledgerSet U g₂ n ∧
      -- ... the ledger only grows as further slots settle ...
      (∀ m, n ≤ m → ledgerSet U g₁ n ⊆ ledgerSet U g₁ m) ∧
      -- ... and a block enters at one slot, which both views name
      (∀ (b : BlockId) (k : ℕ), k < n → OutputAt U g₁ b k → OutputAt U g₂ b k) ∧
      ∀ (b : BlockId) (k₁ k₂ : ℕ), OutputAt U g₁ b k₁ → OutputAt U g₁ b k₂ → k₁ = k₂

/-- **SH13e, integrity**: a committed block is the candidate of one slot,
whichever views and routes committed it. -/
def Integrity (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k₁ k₂ : ℕ) (L : BlockId),
    Decided w U V₁ k₁ (some L) → Decided w U V₂ k₂ (some L) → k₁ = k₂

/-- The ledger at a wavelength function, over every fault configuration,
schedule, block universe and wavelength function the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ),
    Output U w ∧ Integrity U w

end Ledger

end Steelhead

end LeanDag
