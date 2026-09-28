import LeanDag.RedSnapper.Model.Votes

/-!
# Certificates

Trusted core: the paper's threshold objects (`Alg:FastPathPredicates`:
`IsFastCertTX`, `HasCertTX`, `CertVisible`, `IsSkipCertObj`,
`IsUnlockCertObj`) and the round-level quorum of certificates that the
consensusless finality route reads.

Every threshold is counted over a block's parents from the immediately
preceding round — all of its parents, since the model has no weak links
(`Model/Block.lean`) — and counts **authors**, never blocks, since
Byzantine validators equivocate. A threshold is stated as an explicit
witness set: `AtLeast U k s P` holds when some subset of `s` consists of
blocks satisfying `P` and has `k` distinct authors. The trusted core
therefore never decides the vote predicates, which read reachability;
the computable form is a lemma in `Helpers/`.

Votes from several rounds are never added together: a certificate from an
earlier round counts only through `HasCert`, when the completed
certificate lies in the causal history. Thresholds per D1: the ack
certificate at `quorum = n − f`, the skip and unlock certificates at
`half = 2f + 1`. A view judges a certificate it holds exactly as the
universe does, since it holds the block's whole history; views
under-report only the round-level counts, which the routes of the next
phase read.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- At least `k` distinct authors among the blocks of `s` satisfy `P`:
some subset of `s` consists of `P`-blocks and has `k` authors. -/
def AtLeast (U : Universe Validator BlockId Tx Obj) (k : ℕ) (s : Finset BlockId)
    (P : BlockId → Prop) : Prop :=
  ∃ t ⊆ s, (∀ b ∈ t, P b) ∧ k ≤ (authorsOf U.block t).card

/-- The blocks of round `r` — the paper's `DAG[r]`. -/
def blocksAt (U : Universe Validator BlockId Tx Obj) (r : ℕ) : Finset BlockId :=
  U.ids.filter fun i => (U.block i).round = r

/-- `C` is a certificate for `tx` (the paper's `IsFastCertTX`): a quorum
of `C`'s parents are fast votes for `tx`, and `C` itself is one — a
validator cannot use its parents' votes to certify `tx` while retracting
its own ACK. -/
def IsFastCert (U : Universe Validator BlockId Tx Obj) (C : BlockId) (tx : Tx) : Prop :=
  IsFastVote U C tx ∧
    AtLeast U (quorum Validator) (U.block C).parents fun b => IsFastVote U b tx

/-- A certificate for `tx` lies in `b`'s causal history (the paper's
`HasCertTX`; reflexive: `b` itself may be the certificate). -/
def HasCert (U : Universe Validator BlockId Tx Obj) (b : BlockId) (tx : Tx) : Prop :=
  ∃ C ∈ U.ids, IsFastCert U C tx ∧ Reaches U b C

/-- A certificate for `tx` is visible from `b`'s parents (the paper's
`CertVisible`): a quorum of the parents are fast votes for `tx` — so `b`
would certify `tx` by keeping its ACK — or a parent already has a
certificate in its history. A function of the parents alone: it never
reads the stance `b` writes. -/
def CertVisible (U : Universe Validator BlockId Tx Obj) (b : BlockId) (tx : Tx) : Prop :=
  AtLeast U (quorum Validator) (U.block b).parents (fun p => IsFastVote U p tx) ∨
    ∃ p ∈ (U.block b).parents, HasCert U p tx

/-- `C` is a skip certificate for `o` (the paper's `IsSkipCertObj`):
`half` of its parents are skip votes on `o`. A quorum rejected the
candidates without ever supporting one. -/
def IsSkipCert (U : Universe Validator BlockId Tx Obj) (C : BlockId) (o : Obj) : Prop :=
  AtLeast U (half Validator) (U.block C).parents fun b => IsSkipVote U b o

/-- `C` is an unlock certificate for `o` (the paper's `IsUnlockCertObj`):
`half` of its parents vote `⊥` on `o`, skip or unlock. Weaker than a skip
certificate — some of the quorum may have ACKed before the conflict
became visible — and so bivalent. -/
def IsUnlockCert (U : Universe Validator BlockId Tx Obj) (C : BlockId) (o : Obj) : Prop :=
  AtLeast U (half Validator) (U.block C).parents fun b => IsBotVote U b o

/-- A quorum of certificates for `tx` at round `r`: the evidence the
consensusless finality route reads from one round. -/
def FastQuorumAt (U : Universe Validator BlockId Tx Obj) (r : ℕ) (tx : Tx) : Prop :=
  AtLeast U (quorum Validator) (blocksAt U r) fun C => IsFastCert U C tx

end RedSnapper

end LeanDag
