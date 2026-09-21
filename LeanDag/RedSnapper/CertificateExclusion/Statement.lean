import LeanDag.RedSnapper.Model.Certificates

/-!
# Certificate exclusion — statement

RS2: the certificate-level safety of the paper's §4 — the five lemmas
every route-level agreement claim rests on.

* **Honest single ACK** (Lemma single-ack): a correct validator never
  fast-votes for two conflicting transactions, at any two of its blocks.
* **Certificate uniqueness** (Lemma cert-unique): two conflicting
  transactions are never both certified — two quorums of `n − f`
  authors share a correct one.
* **Ack/skip exclusivity** (Lemma univalent): a certificate for `tx` and
  a skip certificate for its input never both exist — `quorum` ACKers
  and `half` skip voters share a correct validator, who would have both
  ACKed and never ACKed.
* **A fast commit excludes an unlock certificate at or below its round**
  (Lemma fast-unlock-exclusion, the half the paper proves): a
  certificate for `tx` and an unlock certificate for its input at a
  round at most the certificate's never both exist. Above the
  certificate's round the claim needs the voting rule, not the
  discipline; the arc does not restate it — the anchor route resolves
  the bivalent case instead (RS3), and the revised paper's
  unconditional form is finding 22 of the record.
* **Certificate propagation** (Lemma cert-propagation): once a quorum of
  blocks at one round certify `tx`, every block above that round has a
  certificate for `tx` in its causal history.

Propagation is pure counting on the DAG. The four exclusivity claims
consume `StanceDiscipline` — the automaton of correct validators on
declarations — and nothing else about behaviour; the statement keeps the
two apart.
-/

namespace LeanDag

namespace RedSnapper

namespace CertificateExclusion

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Honest single ACK**: at two blocks of one correct author, no fast
votes for conflicting transactions. -/
def HonestSingleAck (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ b ∈ U.ids, ∀ b' ∈ U.ids,
    (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b').author = (U.block b).author →
    ∀ tx tx' : Tx, Conflict tx tx' → IsFastVote U b tx → ¬ IsFastVote U b' tx'

/-- **Certificate uniqueness**: conflicting transactions are never both
certified, by any two blocks (`2 · quorum > n + f`). -/
def CertUniqueness (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ tx tx' : Tx,
    Conflict tx tx' → IsFastCert U C tx → IsFastCert U C' tx' → False

/-- **Ack/skip exclusivity**: a certificate for `tx` and a skip certificate
for its input never both exist (`quorum + half > n + f`). -/
def AckSkipExclusion (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ tx : Tx,
    IsFastCert U C tx → IsSkipCert U C' (T.input tx) → False

/-- **A fast commit excludes an unlock certificate at or below its
round**: a certificate for `tx` and an unlock certificate for its input
at a round at most the certificate's never both exist
(`quorum + half > n + f`, and the automaton: `⊥` is absorbing). -/
def AckUnlockExclusionBelow (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ C ∈ U.ids, ∀ C' ∈ U.ids, ∀ tx : Tx,
    IsFastCert U C tx → IsUnlockCert U C' (T.input tx) →
    (U.block C').round ≤ (U.block C).round → False

/-- **Certificate propagation**: a quorum of certificates for `tx` at
round `r` puts a certificate for `tx` in the causal history of every
block above `r` — every block's parents meet the certifying quorum in a
correct author, whose round-`r` block is unique. -/
def CertPropagation (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (r : ℕ) (tx : Tx), FastQuorumAt U r tx →
    ∀ b ∈ U.ids, r < (U.block b).round → HasCert U b tx

/-- Certificate exclusion, over every fault configuration, transaction
data, and universe the model admits: propagation unconditionally, the
four exclusivity claims under the stance discipline of correct
validators. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Transactions Tx Obj] (U : Universe Validator BlockId Tx Obj),
    CertPropagation U ∧
      (StanceDiscipline U →
        HonestSingleAck U ∧ CertUniqueness U ∧ AckSkipExclusion U ∧
          AckUnlockExclusionBelow U)

end CertificateExclusion

end RedSnapper

end LeanDag
