import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Helpers.DagRule
/-!
# AL14 — the segmented ledger

The committed sequence a segmented run outputs, in the three parts BN5
states of Barnacle's (`adaptive-leaders.md` §9): it is one list across
validators as far as both reach, it only grows, and it holds each block
once. Stated of runs whose output stops at each configuration's boundary
while its decisions reach the anchor, so a block decided above a
boundary is in no range's ledger — `Adaptive.decided_and_not_output`.

Integrity is easier here than in Barnacle. Consecutive output ranges are
`(start k, start k + interval]` and abut by `start_succ`, so the rounds
partition by construction rather than through an argument about where
the anchors fall.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Adaptive

namespace Ledger

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## What this asks of the rule

`Agree`, through the agreement theorem, and `CommitsCandidate`, to
identify a committed block's slot — both properties, in place of the
seven-clause `R.Laws`. -/

/-- **BN5a, the ledger is agreed**: two runs over one universe read the
same committed sequence from every range both have closed, hence the
same list to every height both reach. -/
def SegLedgerAgreement (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) : Prop :=
  -- One universe; two validators' runs, from any two views, closed to
  -- heights `K₁` and `K₂`.
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : SegRun R P upd C₀ U V₁ K₁) (R₂ : SegRun R P upd C₀ U V₂ K₂),
    -- Every range both have closed yields the same committed blocks, in the
    -- same order …
    (∀ k, k < min K₁ K₂ → R₁.rangeLedger k = R₂.rangeLedger k) ∧
      -- … so the ledger to any height both reach — ranges `0` to `K − 1`,
      -- concatenated — is one list.
      ∀ K, K ≤ min K₁ K₂ → R₁.ledgerUpto K = R₂.ledgerUpto K

/-- **BN5b, the ledger grows**: to a lower height it is a prefix of itself
to a higher one — nothing committed is ever reordered or withdrawn. -/
def SegLedgerPrefix (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) : Prop :=
  -- One run, any height;
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ) (Rn : SegRun R P upd C₀ U V K)
    -- its ledger to a lower height is a prefix (`<+:`) of its ledger to a
    -- higher one: later ranges only append.
    (K₁ K₂ : ℕ), K₁ ≤ K₂ → Rn.ledgerUpto K₁ <+: Rn.ledgerUpto K₂

/-- **BN5c, integrity**: no block appears twice in the ledger, to any
height the run reaches. -/
def SegLedgerNodup (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) : Prop :=
  -- One run of height `K`;
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ) (Rn : SegRun R P upd C₀ U V K)
    -- its ledger to any height it has closed holds no block twice — within
    -- a range by `Slots.keyed`, across ranges by disjoint rounds.
    (K' : ℕ), K' ≤ K → (Rn.ledgerUpto K').Nodup

/-- The ledger is agreed, grows, and holds each block once, for every
base rule satisfying the laws and every update rule. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload),
    Properties.Agree R.toDagRule → Properties.CommitsCandidate R.toDagRule →
    ∀ (P : Params) (upd : UpdateRule R) (C₀ : Config Validator), Anchored R upd →
      SegLedgerAgreement R P upd C₀ ∧ SegLedgerPrefix R P upd C₀ ∧
        SegLedgerNodup R P upd C₀


end Ledger

end Adaptive

end LeanDag
