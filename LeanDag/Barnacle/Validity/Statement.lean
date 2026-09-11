import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Model.Run
import LeanDag.Barnacle.Model.Live
/-!
# BN14 — validity: a good author's block is delivered

BN5 gives Agreement, Total order and Integrity; this is the fourth
property the rest of this development proves of a commit rule — that a
correct validator's block eventually reaches the ledger — absent from
the paper but held to the development's own bar.

A run of height `K` commits an anchor at each configuration, at the
round the next one starts (`start_succ`), and a good author's block two
rounds below such an anchor lies in its causal history by
`LiveRule.Delivers` — coverage read as delivery, holding of whoever
authored the anchor. Nothing about leadership is needed: the author
need not lead a slot or ever lead again, which costs no rotation
hypothesis.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Validity

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN14, validity.** In a run of height `K`, a good author's block two
rounds below the anchor of a configuration the run closed lies in the
causal history of the block that configuration commits. -/
def Delivered (R : LiveRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator) (slack : ℕ) : Prop :=
  -- Given the base protocol's delivery law …
  R.Delivers slack →
  -- … on any run over a good DAG …
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : PartialRun R.toBaseRule P upd C₀ U V K) (Rnd N : ℕ),
    R.Good U Rnd N →
    -- … there is a good set, all but at most `slack` validators, …
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      -- … each of whose blocks, past the synchrony round and under the
      -- horizon, and two rounds below a closed configuration's anchor, …
      ∀ b ∈ R.ids U, (R.block U b).creator ∈ T → Rnd ≤ (R.block U b).round →
        (R.block U b).round + 1 ≤ N →
        ∀ k, k < K → (R.block U b).round + 2 ≤ Rn.start (k + 1) →
          -- … is in the history of the block that configuration commits.
          ∃ A, Rn.vdct k (Rn.anchor k) = some A ∧ b ∈ historyFrom (R.block U) A

/-- Validity, for every live rule satisfying the laws. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload),
    Properties.CommitsCandidate R.toBaseRule.toDagRule →
    ∀ (P : Params) (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator) (slack : ℕ),
      Delivered R P upd C₀ slack

end Validity

end Barnacle

end LeanDag
