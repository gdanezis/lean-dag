import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Model.Run
/-!
# BN5 — the ledger

The paper's Safety theorem in the form this development states it
(`barnacle.md` §6): the committed sequence read from any two runs is one
list as far as both reach (Agreement, Total Order), it only grows (Total
Order), and a block appears in it at most once (Integrity). Stated of
partial runs, the only runs there are (`barnacle.md` §5). Integrity
rests on `candidates`: a committed block is a candidate of its slot, so
two slots of one range holding it are one slot (`Slots.keyed`), and two
ranges hold blocks of disjoint rounds.

* **BN5a, the ledger is agreed** — range by range, and as one list, as
  far as both runs reach.
* **BN5b, the ledger grows** — the ledger to a lower height is a prefix
  of the ledger to a higher one.
* **BN5c, integrity** — no block appears twice, to any height the run
  reaches.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Ledger

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## What this asks of the rule

`Agree`, through the agreement theorem, and `CommitsCandidate`, to
identify a committed block's slot — both properties, in place of the
seven-clause `R.Laws`. -/

/-- **BN5a, the ledger is agreed**: two runs over one universe read the
same committed sequence from every range both have closed, hence the
same list to every height both reach. -/
def LedgerAgreement (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) (upd : UpdateRule R) : Prop :=
  -- One universe; two validators' runs, from any two views, closed to
  -- heights `K₁` and `K₂`.
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : PartialRun R P getLeader hk upd U V₁ K₁) (R₂ : PartialRun R P getLeader hk upd U V₂ K₂),
    -- Every range both have closed yields the same committed blocks, in the
    -- same order …
    (∀ k, k < min K₁ K₂ → R₁.rangeLedger k = R₂.rangeLedger k) ∧
      -- … so the ledger to any height both reach — ranges `0` to `K − 1`,
      -- concatenated — is one list.
      ∀ K, K ≤ min K₁ K₂ → R₁.ledgerUpto K = R₂.ledgerUpto K

/-- **BN5b, the ledger grows**: to a lower height it is a prefix of itself
to a higher one — nothing committed is ever reordered or withdrawn. -/
def LedgerPrefix (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) (upd : UpdateRule R) : Prop :=
  -- One run, any height;
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ) (Rn : PartialRun R P getLeader hk upd U V K)
    -- its ledger to a lower height is a prefix (`<+:`) of its ledger to a
    -- higher one: later ranges only append.
    (K₁ K₂ : ℕ), K₁ ≤ K₂ → Rn.ledgerUpto K₁ <+: Rn.ledgerUpto K₂

/-- **BN5c, integrity**: no block appears twice in the ledger, to any
height the run reaches. -/
def LedgerNodup (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) (upd : UpdateRule R) : Prop :=
  -- One run of height `K`;
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ) (Rn : PartialRun R P getLeader hk upd U V K)
    -- its ledger to any height it has closed holds no block twice — within
    -- a range by `Slots.keyed`, across ranges by disjoint rounds.
    (K' : ℕ), K' ≤ K → (Rn.ledgerUpto K').Nodup

/-- The ledger is agreed, grows, and holds each block once, for every
base rule satisfying the laws and every update rule. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload),
    Properties.Agree R.toDagRule → Properties.CommitsCandidate R.toDagRule →
    ∀ (P : Params) (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
      (upd : UpdateRule R), Anchored R upd →
      LedgerAgreement R P getLeader hk upd ∧ LedgerPrefix R P getLeader hk upd ∧
        LedgerNodup R P getLeader hk upd

end Ledger

end Barnacle

end LeanDag
