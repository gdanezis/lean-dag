import LeanDag.RedSnapper.Model.Five.Moves

/-!
# Full-certificate safety — statement

RS6: the certificate-level safety of §4's `5f+1` analysis — Lemmas
single-stance-5f, full-excludes-refutation, unlock-excludes-half (in
the algorithm's refutation form, finding 8), commit-excludes-unlock,
and full-cert-unique.

**None of these consumes the `Five` bound.** The persistence core — a
correct set standing at one value keeps standing, because a move needs
`half` anti-voters and the set leaves at most `n − |S| ≤ 2f < half` of
them — closes at every committee `n ≥ 3f + 1`, and so does each
intersection count on top of it. The safety of the vote-revocation
rules therefore needs only `3f + 1`; what `n ≥ 5f + 1` buys is
*exposure* — a quorum of votes always licenses a move (RS1's
`ExposureAtQuorum`) — that is, the liveness of revocation, exactly the
seam §10 draws.

* **Single stance** (Lemma single-stance-5f): no block is a fast vote
  for two conflicting transactions — unconditional, from the
  functionality of the stance read.
* **A commit excludes refutations** (Lemma full-excludes-refutation): a
  full certificate for `tx` forbids a refutation of `ack tx` at any
  block from its round on — the certificate's correct core never moves
  again.
* **An unlock excludes refutations** (the algorithm's form of Lemma
  unlock-excludes-half): a full unlock certificate forbids a refutation
  of `⊥` from its round on, even split across rival transactions.
* **A commit excludes an unlock** (Lemma full-excludes-unlock): a full
  certificate and a full unlock certificate for one input never
  coexist, at any round pair — whichever formed first pins its correct
  core forever.
* **Full-certificate uniqueness** (Lemma full-cert-unique): conflicting
  transactions never both reach a full certificate.

The last four consume `MoveDiscipline` — the move rule of correct
validators — and nothing else about behaviour.
-/

namespace LeanDag

namespace RedSnapper

namespace FullCertSafety

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Single stance**: no block fast-votes for two conflicting
transactions. -/
def SingleStance (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ b ∈ U.ids, ∀ tx tx' : Tx, Conflict tx tx' →
    IsFastVote U b tx → ¬ IsFastVote U b tx'

/-- **A commit excludes refutations**: no refutation of `ack tx` at or
above a full certificate's round. -/
def CommitExcludesRefutation (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ tx : Tx,
    IsFullCert U C tx → (U.block C).round ≤ (U.block C').round →
    ¬ IsRefutation U C' (T.input tx) (Stance.ack tx)

/-- **An unlock excludes refutations**: no refutation of `⊥` at or above
a full unlock certificate's round. -/
def UnlockExcludesRefutation (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ o : Obj,
    IsFullUnlockCert U C o → (U.block C).round ≤ (U.block C').round →
    ¬ IsRefutation U C' o Stance.bot

/-- **A commit excludes an unlock**: never both, at any round pair. -/
def CommitExcludesUnlock (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ tx : Tx,
    IsFullCert U C tx → ¬ IsFullUnlockCert U C' (T.input tx)

/-- **Full-certificate uniqueness**: conflicting transactions never both
reach a full certificate. -/
def FullCertUniqueness (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ tx tx' : Tx, Conflict tx tx' →
    IsFullCert U C tx → ¬ IsFullCert U C' tx'

/-- Full-certificate safety, over every fault configuration — the
committee bound is `3f + 1`, not `5f + 1` — transaction data, and
universe the model admits: single stance unconditionally, the four
exclusions under the move rule. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj),
    SingleStance U ∧
      (MoveDiscipline U →
        CommitExcludesRefutation U ∧ UnlockExcludesRefutation U ∧
          CommitExcludesUnlock U ∧ FullCertUniqueness U)

end FullCertSafety

end RedSnapper

end LeanDag
