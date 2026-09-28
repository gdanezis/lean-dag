import LeanDag.RedSnapper.Model.Transaction
import LeanDag.RedSnapper.Model.Stance

/-!
# Votes

Trusted core: the three vote shapes of the paper's §7 ("Vote shapes",
`Alg:FastPathPredicates`: `IsFastVoteTX`, `IsSkipVoteObj`,
`IsUnlockVoteObj`), each a property of one block read from its causal
history.

A block is a *fast vote* (ACK) for a transaction when the transaction is
valid, lies in the block's causal history, and the author's stance on
the transaction's owned input, read at the block, is an ACK for it —
merely carrying a transaction is not a vote. A block is a *skip vote* on
an object version when the author stands at `⊥` while a conflict on the
version is visible and the author never ACKed a candidate for it; an
*unlock vote* is the same declaration from an author that had ACKed one.
The two share their stance and differ by `AckedBefore` alone — a skip
voter never contributed to a certificate, an unlock voter may have. The
paper names no union of the two; `IsBotVote` is that union, what an
unlock certificate counts.

With one owned input per transaction (D2) the paper's "for every owned
input" is one stance read; with D2 the paper's `RecoveryObjs` is
`Conflicted` (see `Model/Transaction.lean`).
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- `b` is a fast vote for `tx` (the paper's `IsFastVoteTX`): `tx` is
valid, included by `b`, and `b`'s author stands at `ack tx` on `tx`'s
owned input, read at `b`. -/
def IsFastVote (U : Universe Validator BlockId Tx Obj) (b : BlockId) (tx : Tx) : Prop :=
  T.Valid tx ∧ Includes U b tx ∧
    StanceIs U (U.block b).author (T.input tx) b (some (Stance.ack tx))

/-- `b` votes `⊥` on `o` with a conflict visible: a skip vote or an unlock
vote — what an unlock certificate counts. -/
def IsBotVote (U : Universe Validator BlockId Tx Obj) (b : BlockId) (o : Obj) : Prop :=
  StanceIs U (U.block b).author o b (some Stance.bot) ∧ Conflicted U b o

/-- `b` is a skip vote on `o` (the paper's `IsSkipVoteObj`): `⊥` with a
conflict visible, from an author that never ACKed a candidate for `o`. -/
def IsSkipVote (U : Universe Validator BlockId Tx Obj) (b : BlockId) (o : Obj) : Prop :=
  IsBotVote U b o ∧ ¬ AckedBefore U (U.block b).author o b

/-- `b` is an unlock vote on `o` (the paper's `IsUnlockVoteObj`): `⊥`
with a conflict visible, from an author that had ACKed a candidate for
`o` — a public retraction. -/
def IsUnlockVote (U : Universe Validator BlockId Tx Obj) (b : BlockId) (o : Obj) : Prop :=
  IsBotVote U b o ∧ AckedBefore U (U.block b).author o b

end RedSnapper

end LeanDag
