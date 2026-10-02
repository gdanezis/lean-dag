import LeanDag.RedSnapper.Model.Liveness
import LeanDag.RedSnapper.Model.HonestVoting
import LeanDag.RedSnapper.Model.Verdict

/-!
# Uncontested liveness — statement

RS4: the paper's Lemma fp-liveness, structurally — a valid transaction
with no valid rival anywhere, carried by a correct block at round `r₀`,
reaches a consensusless quorum of certificates two synchronised rounds
later. The rival quantifier is gated by validity (record finding 18):
an included invalid rival is never a candidate and must not void the
claim.

The shape of the claim: under the voting rule alone — the arc-wide audit found the
safety automaton dead in both proofs and it was dropped —,
with `Correct` populated at rounds `r₀ + 1` and `r₀ + 2` and
synchronised from some `R ≤ r₀`, every correct block at `r₀ + 1` is a
fast vote (the transaction spreads through synchrony; the sole-candidate
rule adopts it; `⊥` is impossible with no conflict anywhere), and every
correct block at `r₀ + 2` is then a certificate — a quorum of them,
since `quorum ≤ |Correct|`. When the transaction is owned, the
`fastFinal` verdict follows in any full view, over every anchor
sequence.

A mixed transaction takes the consensus route instead: the same
certificates, once under a committed anchor (C5, rendered structurally
as an anchor reaching a correct round-`r₀ + 2` block), give the
`finalizeOnCommit` verdict — the input is unconflicted at the anchor
because no valid rival is included anywhere. The route has no class
gate, so the claim is stated for any valid transaction.
-/

namespace LeanDag

namespace RedSnapper

namespace Uncontested

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Fast liveness**: an unrivalled valid transaction, carried by a
correct round-`r₀` block, has a quorum of certificates at `r₀ + 2`. -/
def FastLiveness (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRule U →                      -- the liveness-side CastVotes clauses;
                                      -- the safety automaton is not consumed
                                      -- (arc audit: dropped as dead)
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    T.Valid tx →                      -- a valid transaction ...
    (∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx') →
                                      -- ... with no valid rival included anywhere:
                                      -- the sole candidate of its input (finding 18)
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ →
    Includes U b₀ tx →                -- carried by a correct round-r₀ block;
                                      -- synchrony disseminates it from there
    R ≤ r₀ →
    SynchronisedOn U (Correct : Finset Validator) R →
                                      -- "after GST", from a round at or before r₀
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
    PopulatedOn U (Correct : Finset Validator) (r₀ + 2) →
                                      -- the ACK round and the certificate round
    FastQuorumAt U (r₀ + 2) tx        -- every correct r₀+2 block is a certificate:
                                      -- the consensusless evidence, two rounds on

/-- **Fast finality**: with the transaction owned, the consensusless
verdict follows in any view holding the whole universe, over every
anchor sequence. -/
def FastVerdict (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRule U →
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    Owned tx →                        -- the consensusless route's gate (D9)
    T.Valid tx →
    (∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx') →
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ → Includes U b₀ tx →
    R ≤ r₀ → SynchronisedOn U (Correct : Finset Validator) R →
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
    PopulatedOn U (Correct : Finset Validator) (r₀ + 2) →
                                      -- the FastLiveness hypotheses, verbatim
    ∀ (A : Anchors U) (V : View U), U.ids ⊆ V.ids →
                                      -- any anchors; any view holding everything
                                      -- (with `subset_ids` this is the full view)
      TxVerdict U A V tx Fate.finalized
                                      -- the fastFinal verdict: consensusless
                                      -- finality, no anchor consulted

/-- **Anchor finality**: a committed anchor above a correct
round-`r₀ + 2` block finalises the transaction, owned or mixed, in every
view. -/
def AnchorVerdict (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRule U →
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    T.Valid tx →
    (∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx') →
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ → Includes U b₀ tx →
    R ≤ r₀ → SynchronisedOn U (Correct : Finset Validator) R →
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
                                      -- the FastLiveness hypotheses, less the
                                      -- certificate round: its block is given below
    ∀ (A : Anchors U) (V : View U) (i : ℕ) (a C : BlockId),
      A.seq[i]? = some a →            -- a committed anchor ...
      C ∈ U.ids → (U.block C).author ∈ (Correct : Finset Validator) →
      (U.block C).round = r₀ + 2 →
      Reaches U a C →                 -- ... above a correct certificate-round
                                      -- block (C5):
      TxVerdict U A V tx Fate.finalized
                                      -- the finalizeOnCommit verdict

/-- Uncontested liveness, over every fault configuration, transaction
data, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj),
    FastLiveness U ∧ FastVerdict U ∧ AnchorVerdict U

end Uncontested

end RedSnapper

end LeanDag
