import LeanDag.RedSnapper.Model.Dead
import LeanDag.RedSnapper.Model.View

/-!
# Verdicts

Trusted core: the four decision routes of the paper's `TryDecide`
(`Alg:Snapper3f+1`) — `TryFastDecideTX`, `TrySkipDecideObj`,
`FinalizeOnCommitTX` (both of its loops), `ResolveOnCommitObj` — as one
order-free inductive
relation (D6 of `docs/red-snapper.md`): a constructor per route, any
derivable verdict counts, and that all derivable verdicts agree is the
theorem of `TxAgreement/`, never a side condition.

The paper's procedures carry local state (`fastCommittedTX`,
`skippedTX`, `decidedObj`) and run in a fixed order; those guards keep a
*validator's* decisions consistent and appear here as no clause — the
relation admits every justifiable verdict, and RS3 proves they never
disagree. The consensusless routes read a **view** (a validator's local
DAG) and are gated as the paper gates them: the fast route by `Owned` —
a mixed transaction must be ordered before it finalises (D9) — while the
skip route drops owned and mixed candidates alike. The anchor routes
read the global `(U, A)` of D4, so their cross-validator agreement is
definitional.

Three transcription notes; the first two are provable rather than
assumed, the third is a modelling choice. In
`finalizeOnCommit`, the paper's `¬Dead` and
`OwnedInputs ∩ RecoveryObjs = ∅` clauses reduce, under the constructor's
`¬Conflicted`, to nothing: every disjunct of `Dead` forces a visible
conflict on the input (releases included, through `Anchors.chained`).
In `resolveCommit`, the paper commits "the unique transaction in `H`" —
here any member of `H`, whose uniqueness is a consequence of certificate
uniqueness. `FinalizeOnCommitTX`'s first loop drops the candidates of
an object already in `decidedObj`; that local set is rendered by what
put the object there, globally: a release at an earlier anchor is
`releasedDrop` — the candidate first included after its object's
release, which in general no other route reaches (a witness has it as
the only route to a verdict) — and a finalized rival is
`resolveDropRival`, at whichever anchor holds the rival's certificate
(RS11's `DecidedAgainst`). When the object was decided consensuslessly
the relation drops the late candidate only at an anchor above the
quorum's round, possibly later than the validator does; that such an
anchor then always does so is argued in the record, not proved.
-/

namespace LeanDag

namespace RedSnapper

/-- The fate of a decided transaction: finalized (executed) or dropped
(skipped). -/
inductive Fate where
  /-- The transaction is finalized. -/
  | finalized
  /-- The transaction is dropped. -/
  | dropped
  deriving DecidableEq

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- A quorum of certificate authors for `tx` at round `r`, among the
blocks the view holds — what `TryFastDecideTX` reads. A view can
under-report the quorum, never exceed it. -/
def FastQuorumAtInView (U : Universe Validator BlockId Tx Obj) (V : View U) (r : ℕ)
    (tx : Tx) : Prop :=
  AtLeast U (quorum Validator) (blocksAt U r ∩ V.ids) fun C => IsFastCert U C tx

/-- A quorum of skip-certificate authors for `o` at round `r`, among the
blocks the view holds — what `TrySkipDecideObj` reads. -/
def SkipQuorumAtInView (U : Universe Validator BlockId Tx Obj) (V : View U) (r : ℕ)
    (o : Obj) : Prop :=
  AtLeast U (quorum Validator) (blocksAt U r ∩ V.ids) fun C => IsSkipCert U C o

/-- The verdict relation: `TxVerdict U A V tx f` — the validator holding
view `V`, over the committed anchors `A`, can justify fate `f` for
`tx`. -/
inductive TxVerdict (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (V : View U) :
    Tx → Fate → Prop where
  /-- Consensusless finality (`TryFastDecideTX`): an owned transaction
  with a quorum of certificates at one round of the view. -/
  | fastFinal {tx : Tx} {r : ℕ} :
      Owned tx →                        -- the IsOwned gate: mixed never finalises consensuslessly
      FastQuorumAtInView U V r tx →     -- |{b ∈ DAG[r] : IsFastCertTX(b, tx)}| ≥ quorum, authors
      TxVerdict U A V tx Fate.finalized
  /-- Consensusless skip (`TrySkipDecideObj`): a quorum of skip
  certificates for the input at one round of the view drops every
  candidate seen at that round — owned or mixed. -/
  | skipDecide {tx : Tx} {r : ℕ} {b : BlockId} :
      b ∈ blocksAt U r ∩ V.ids →        -- the paper's B = DAG[r], as held by the view
      IsCandidate U b (T.input tx) tx → -- tx ∈ ⋃_{b ∈ B} Candidates(b, o): the drop loop's set
      SkipQuorumAtInView U V r (T.input tx) →
                                        -- |{b ∈ B : IsSkipCertObj(b, o)}| ≥ quorum, authors
      TxVerdict U A V tx Fate.dropped
  /-- Commit at an anchor (`FinalizeOnCommitTX`): a candidate whose
  input is uncontested at the anchor, certified in its history. -/
  | finalizeOnCommit {tx : Tx} {i : ℕ} {a : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      IsCandidate U a (T.input tx) tx → -- Includes(A, tx), valid — tx in the anchor's history
      ¬ Conflicted U a (T.input tx) →   -- OwnedInputs ∩ RecoveryObjs(A) = ∅ (D2); subsumes ¬Dead
      HasCert U a tx →                  -- HasCertTX(A, tx): a certificate below the anchor
      TxVerdict U A V tx Fate.finalized
  /-- Drop of a late candidate (`FinalizeOnCommitTX`, first loop): a
  candidate of an anchor whose input was released at an earlier one. -/
  | releasedDrop {tx : Tx} {i j : ℕ} {a : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      IsCandidate U a (T.input tx) tx → -- tx ∈ Candidates(A, o) ...
      j < i →                           -- ... with o ∈ decidedObj: released at an
      ResolvesAt U A j (T.input tx) →   -- earlier anchor (Resolves, there)
      TxVerdict U A V tx Fate.dropped
  /-- Commit at an anchor, contested (`ResolveOnCommitObj`, first
  branch): a candidate of a conflicted input, certified in the anchor's
  history and alive there. -/
  | resolveCommit {tx : Tx} {i : ℕ} {a : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      Conflicted U a (T.input tx) →     -- o ∈ RecoveryObjs(A): the resolve loop's range (D2)
      IsCandidate U a (T.input tx) tx → -- tx ∈ Candidates(A, o)
      HasCert U a tx →                  -- membership in H: certified in the anchor's history ...
      ¬ DeadAt U A i tx →               -- ... and alive — in particular, not released earlier
      TxVerdict U A V tx Fate.finalized
  /-- Drop of the rivals (`ResolveOnCommitObj`, first branch): a
  candidate beside a conflicting candidate that is certified in the
  anchor's history and alive there. -/
  | resolveDropRival {tx' : Tx} {i : ℕ} {a : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      IsCandidate U a (T.input tx') tx' →
                                        -- tx' ∈ K: an undecided candidate of the object
      (∃ tx, Conflict tx' tx ∧ IsCandidate U a (T.input tx') tx ∧ HasCert U a tx ∧
        ¬ DeadAt U A i tx) →            -- H ≠ ∅: some rival is the tx* the branch commits
      TxVerdict U A V tx' Fate.dropped
  /-- Release (`ResolveOnCommitObj`, second branch): the input resolves
  at this anchor — the first release-ready one — and every candidate
  there is dropped. -/
  | resolveDrop {tx : Tx} {i : ℕ} {a : BlockId} :
      A.seq[i]? = some a →              -- a committed anchor
      ResolvesAt U A i (T.input tx) →   -- Resolves(A, o): H empty, release evidence, first anchor
      IsCandidate U a (T.input tx) tx → -- tx ∈ K: every candidate of the released object
      TxVerdict U A V tx Fate.dropped

end RedSnapper

end LeanDag
