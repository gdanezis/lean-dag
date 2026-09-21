import LeanDag.RedSnapper.Model.Liveness
import LeanDag.RedSnapper.Model.HonestVoting
import LeanDag.RedSnapper.Model.Verdict

/-!
# Termination — statement

RS11: the paper's Lemma termination-3f, the Termination property of its
Conditional State-Machine Replication — every transaction placed in the
global order is eventually decided, `Commit` or `Abort`. The lemma's
proof has two halves, and so has the statement.

**Decided against** (the lemma's first case: an owned input "already
decided against `tx`"). A candidate of a committed anchor is dropped
when its object resolved at or below that anchor, or when the anchor
holds the certificate of a finalized rival. No voting rule and no
synchrony: this is the half that speaks of executions where the correct
validators have decided the object and fallen silent on it — executions
in which `VotingRule` is false, since the rule does not model the
decided-stop, and on which the second half is therefore silent. The
release case is one constructor (`resolveDrop` or `releasedDrop`); the
rival case needs the stance discipline, for the finalized rival to be
alive at the anchor.

**Decided** (the lemma's other cases). A valid transaction included by
a correct block is decided, under both `3f + 1` hypotheses and the
structural synchrony, given a correct-authored committed anchor four
rounds above the carrier (C4). No premise says whether the transaction
is contested: the proof splits on whether the anchor's own block two
rounds above the carrier includes a valid rival. If not, that block is a
certificate (RS4's argument, the rival premise read at that block alone
— finding 18's "before certification") and the anchor commits the
transaction, or, had the object been released below, drops it. If so,
RS5 applies from that block. The paper's proof invokes (C5); the
statement does not: a correct anchor's own chain carries the evidence.
The bound `r₀ + 4` is RS5's; `r₀ + 2` would do on the first branch.

The statement does not say *where* the verdict is derived, only that
one is; and since every route the proof uses is an anchor route, the
view is immaterial — it is quantified because the relation carries one.

**Decided, from the global order** restates the second claim in the
paper's shape: "placed in the global order" is valid and in the causal
history of a committed anchor; a correct-authored anchor committed at or
after it includes the transaction too, by `Anchors.chained`, and is the
carrier.

Scope: one owned input per transaction (D2) — the lemma's closing
sentence, on `RecoveryObjs` across the inputs of one transaction, has no
counterpart.
-/

namespace LeanDag

namespace RedSnapper

namespace Termination

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Decided against**: a candidate of a committed anchor whose object
resolved at or below it, or whose finalized rival is certified under it,
is dropped. -/
def DecidedAgainst (U : Universe Validator BlockId Tx Obj) : Prop :=
  StanceDiscipline U →                -- keeps the finalized rival alive at the anchor
  ∀ (A : Anchors U) (V V' : View U) (i : ℕ) (a : BlockId) (tx : Tx),
    A.seq[i]? = some a →              -- a committed anchor ...
    IsCandidate U a (T.input tx) tx → -- ... with tx among its candidates, and
    ((∃ j ≤ i, ResolvesAt U A j (T.input tx)) ∨
                                      -- the object released at or below it, or
      ∃ tx', Conflict tx tx' ∧ HasCert U a tx' ∧ TxVerdict U A V' tx' Fate.finalized) →
                                      -- a rival finalized — by any route, in any
                                      -- view — and certified under the anchor:
    TxVerdict U A V tx Fate.dropped

/-- **Decided**: a valid transaction included by a correct block
receives a verdict, given a correct-authored committed anchor four
rounds above. -/
def Decided (U : Universe Validator BlockId Tx Obj) : Prop :=
  StanceDiscipline U →                -- certificate exclusions, and RS5's resolution
  VotingRule U →                      -- the liveness-side CastVotes clauses
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    T.Valid tx →                      -- a valid transaction ...
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ →
    Includes U b₀ tx →                -- ... included by a correct round-r₀ block
    R ≤ r₀ →
    SynchronisedOn U (Correct : Finset Validator) R →
                                      -- "after GST", from a round at or before r₀
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
                                      -- RS4's ACK round
    PopulatedOn U (Correct : Finset Validator) (r₀ + 3) →
                                      -- RS5's voting round, when a rival is seen
    ∀ (A : Anchors U) (V : View U) (i : ℕ) (a : BlockId),
      A.seq[i]? = some a →            -- a committed anchor, given (C4) ...
      (U.block a).author ∈ (Correct : Finset Validator) →
      r₀ + 4 ≤ (U.block a).round →    -- ... correct-authored, at or above RS5's
                                      -- trichotomy round:
      TxVerdict U A V tx Fate.finalized ∨ TxVerdict U A V tx Fate.dropped

/-- **Decided, from the global order**: the same, for a valid
transaction in the causal history of a committed anchor, with a
correct-authored anchor committed at or after it as the carrier. -/
def DecidedOrdered (U : Universe Validator BlockId Tx Obj) : Prop :=
  StanceDiscipline U → VotingRule U →
  ∀ (tx : Tx) (R : ℕ) (A : Anchors U) (V : View U) (k m i : ℕ) (a₀ b₀ a : BlockId),
    T.Valid tx →
    A.seq[k]? = some a₀ → Includes U a₀ tx →
                                      -- placed in the global order
    k ≤ m → A.seq[m]? = some b₀ →
    (U.block b₀).author ∈ (Correct : Finset Validator) →
                                      -- a correct-authored anchor at or after it (C4)
    R ≤ (U.block b₀).round →
    SynchronisedOn U (Correct : Finset Validator) R →
    PopulatedOn U (Correct : Finset Validator) ((U.block b₀).round + 1) →
    PopulatedOn U (Correct : Finset Validator) ((U.block b₀).round + 3) →
    A.seq[i]? = some a →
    (U.block a).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round + 4 ≤ (U.block a).round →
                                      -- and another, four rounds above (C4)
    TxVerdict U A V tx Fate.finalized ∨ TxVerdict U A V tx Fate.dropped

/-- Termination at `n ≥ 3f + 1`, over every fault configuration,
transaction data, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj),
    DecidedAgainst U ∧ Decided U ∧ DecidedOrdered U

end Termination

end RedSnapper

end LeanDag
