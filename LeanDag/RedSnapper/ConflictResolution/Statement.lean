import LeanDag.RedSnapper.Model.Liveness
import LeanDag.RedSnapper.Model.HonestVoting
import LeanDag.RedSnapper.Model.Verdict

/-!
# Conflict resolution — statement

RS5: the paper's Lemma equiv-live, structurally, in the corrected form
the mechanisation forced (`docs/red-snapper.md` §3, finding 5): the
paper's Case 3 claims an unlock certificate always forms at `r + 2`,
which is refutable — a correct validator that sees a certificate keeps
its ACK. What holds is the disjunction.

* **The trichotomy**: with the conflict visible at a correct round-`r`
  block, synchrony from `R ≤ r`, and `Correct` populated at `r + 1`,
  every correct block at `r + 2` has a certified candidate of the object
  in its causal history, or is itself an unlock certificate for it —
  each correct validator either kept its ACK, with a certificate visible
  (which is then a certificate at or below its block), or declared `⊥`,
  and `|Correct| ≥ half` retractions among a synchronised block's
  parents are the unlock certificate.
* **Anchor resolution**: under the same hypotheses, at any committed
  anchor that is correct-authored and at round at least `r + 2`, either
  some candidate of the object is finalized (`resolveCommit`: certified
  in the anchor's history and alive), or the object resolves at an
  anchor at or below this one — the paper's "the first committed
  proposer satisfying these conditions resolves the object", with the
  anchor *given*: its existence is what (C4) supplies operationally,
  and no clock enters the statement.
-/

namespace LeanDag

namespace RedSnapper

namespace ConflictResolution

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **The trichotomy at `r + 2`**: a certified candidate in the history,
or an unlock certificate at the block itself. -/
def Trichotomy (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRule U →                      -- the liveness-side CastVotes clauses;
                                      -- the safety automaton is not consumed here
                                      -- (arc audit: dropped as dead); AnchorDecides
                                      -- below does consume it, through RS2
  ∀ (o : Obj) (r R : ℕ) (b₀ : BlockId),
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r →
    Conflicted U b₀ o →               -- the carrier: the conflict visible at a
                                      -- correct round-r block; synchrony spreads it
    R ≤ r →
    SynchronisedOn U (Correct : Finset Validator) R →
                                      -- "after GST": correct blocks reference every
                                      -- correct block of the round below, from R on
    PopulatedOn U (Correct : Finset Validator) (r + 1) →
                                      -- the voting round exists for everyone correct
    ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
      (U.block b).round = r + 2 →     -- any correct block two rounds above the carrier
      (∃ tx, IsCandidate U b o tx ∧ HasCert U b tx) ∨ IsUnlockCert U b o
                                      -- Case 1 (an ACK was kept: a certificate in the
                                      -- history) or Cases 2/3 (all correct retracted:
                                      -- b itself is the unlock certificate)

/-- **Anchor resolution**: at a correct-authored committed anchor above
`r + 2`, a candidate is finalized or the object resolves at or below
this anchor. -/
def AnchorDecides (U : Universe Validator BlockId Tx Obj) : Prop :=
  StanceDiscipline U → VotingRule U →
  ∀ (o : Obj) (r R : ℕ) (b₀ : BlockId),
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r → Conflicted U b₀ o →
    R ≤ r → SynchronisedOn U (Correct : Finset Validator) R →
    PopulatedOn U (Correct : Finset Validator) (r + 1) →
                                      -- the Trichotomy hypotheses, verbatim
    ∀ (A : Anchors U) (i : ℕ) (a : BlockId) (V : View U),
      A.seq[i]? = some a →            -- a committed anchor, GIVEN: its existence
                                      -- is what (C4) supplies operationally
      (U.block a).author ∈ (Correct : Finset Validator) →
      r + 2 ≤ (U.block a).round →     -- at or above the trichotomy round, so its
                                      -- own chain passes through a round-(r+2) block
      (∃ tx, IsCandidate U a o tx ∧ TxVerdict U A V tx Fate.finalized) ∨
        ∃ j ≤ i, ResolvesAt U A j o
                                      -- a candidate commits at this anchor
                                      -- (resolveCommit), or the object resolves at
                                      -- an anchor at or below it (and its
                                      -- candidates were dropped there)

/-- Conflict resolution, over every fault configuration, transaction
data, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj),
    Trichotomy U ∧ AnchorDecides U

end ConflictResolution

end RedSnapper

end LeanDag
