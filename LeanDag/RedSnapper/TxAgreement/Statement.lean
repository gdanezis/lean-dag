import LeanDag.RedSnapper.Model.Verdict

/-!
# Transaction agreement — statement

RS3: the paper's Theorem commit-safety, with §5's mixed-object
corollary — the headline safety of the fast path.

* **Verdict agreement**: two derivable verdicts for one transaction, in
  any two views, over any routes, name the same fate. No transaction is
  ever both finalized and dropped: consensusless against consensusless
  (Lemma cross-route), consensusless against the anchors (Lemmas
  finalize-safety and fast-unlock-exclusion — a quorum of certificates
  propagates into every later anchor's history, and an unlock
  certificate at or below the certificates' round cannot exist), and
  anchor against anchor (Lemma resolve-safety — the release recursion
  and its one-shot).
* **No conflicting finalizations**: two finalized transactions never
  conflict — every finalization route carries a certificate, and
  certificates are unique per input (Lemma cert-unique).
* **Mixed via anchor** (Lemma mixed-object safety): a finalized mixed
  transaction has its certificate below some committed anchor — the
  `Owned` gate keeps it off the consensusless route, so it was ordered
  before it finalised.

The first two consume the stance discipline of correct validators and
nothing else about behaviour; the mixed corollary consumes nothing at
all — it is a fact about the routes' shapes, and the arc-wide audit
moved it outside the discipline arrow accordingly.
-/

namespace LeanDag

namespace RedSnapper

namespace TxAgreement

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Verdict agreement**: across views and routes, one fate per
transaction. -/
def VerdictAgreement (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (V₁ V₂ : View U) (tx : Tx) (f₁ f₂ : Fate),
    TxVerdict U A V₁ tx f₁ → TxVerdict U A V₂ tx f₂ → f₁ = f₂

/-- **No conflicting finalizations**: two finalized transactions never
spend one object version. -/
def NoConflictingFinal (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (V₁ V₂ : View U) (tx tx' : Tx),
    TxVerdict U A V₁ tx Fate.finalized → TxVerdict U A V₂ tx' Fate.finalized →
    ¬ Conflict tx tx'

/-- **Mixed via anchor**: a finalized mixed transaction has its
certificate in the causal history of some committed anchor. -/
def MixedViaAnchor (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (V : View U) (tx : Tx), T.Mixed tx → TxVerdict U A V tx Fate.finalized →
    ∃ (i : ℕ) (a : BlockId), A.seq[i]? = some a ∧ HasCert U a tx

/-- Transaction agreement, over every fault configuration, transaction
data, universe and committed anchor sequence the model admits, under the
stance discipline of correct validators. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (A : Anchors U),
    (StanceDiscipline U → VerdictAgreement U A ∧ NoConflictingFinal U A) ∧
      MixedViaAnchor U A

end TxAgreement

end RedSnapper

end LeanDag
