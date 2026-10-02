import LeanDag.RedSnapper.Model.Liveness
import LeanDag.RedSnapper.Model.Five.HonestVoting
import LeanDag.RedSnapper.Model.Five.Verdict

/-!
# Uncontested liveness at 5f+1 — statement

RS10: the paper's Lemma uncontended-liveness, structurally, in the shape
of RS4 — a valid transaction with no valid rival anywhere, carried by a
correct block at round `r₀`, is fully certified two synchronised rounds
later, and the certificate finalises it by the route of its class.

The shape of the claim: under the `5f+1` voting rule, with `Correct`
populated at round `r₀ + 1` and synchronised from some `R ≤ r₀`, every
correct block at `r₀ + 1` is a fast vote (the transaction spreads
through synchrony; the sole-candidate rule adopts it; `⊥` is impossible,
since both of its origins need a conflict somewhere), and every correct
block at `r₀ + 2` then carries a full certificate — its correct parents
alone are a quorum.

An owned transaction is final on one observed certificate
(`fullFinal`); a mixed one at a committed anchor above a certificate
block (`mixedFinal`; C5, rendered structurally as in RS4's
`AnchorVerdict`). None of it needs `Five`: the full certificate is a
`quorum`, which `Correct` fills at any committee.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveUncontested

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Full liveness**: an unrivalled valid transaction, carried by a
correct round-`r₀` block, is fully certified by every correct block at
`r₀ + 2`. -/
def FullLiveness (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRuleFive U →                  -- the liveness-side CastVotes clauses
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    T.Valid tx →                      -- a valid transaction ...
    (∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx') →
                                      -- ... with no valid rival included anywhere
                                      -- (finding 18)
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ →
    Includes U b₀ tx →                -- carried by a correct round-r₀ block
    R ≤ r₀ →
    SynchronisedOn U (Correct : Finset Validator) R →
                                      -- "after GST", from a round at or before r₀
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
                                      -- the ACK round
    ∀ C ∈ U.ids, (U.block C).author ∈ (Correct : Finset Validator) →
      (U.block C).round = r₀ + 2 →
      IsFullCert U C tx               -- every correct r₀+2 block is a full certificate

/-- **Full finality**: with the transaction owned and the certificate
round populated, the consensusless verdict follows in any view holding
the whole universe, over every anchor sequence. -/
def FullVerdict (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRuleFive U →
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    Owned tx →                        -- the consensusless route's gate (D9)
    T.Valid tx →
    (∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx') →
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ → Includes U b₀ tx →
    R ≤ r₀ → SynchronisedOn U (Correct : Finset Validator) R →
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
                                      -- the FullLiveness hypotheses, verbatim
    PopulatedOn U (Correct : Finset Validator) (r₀ + 2) →
                                      -- the certificate round: some certificate exists
    ∀ (A : Anchors U) (V : View U) (prio : Tx → Tx → Prop), U.ids ⊆ V.ids →
                                      -- any anchors and order; any view holding
                                      -- everything
      VerdictFive U A V prio tx Fate.finalized
                                      -- the fullFinal verdict: no anchor consulted

/-- **Anchor finality**: with the transaction mixed, a committed anchor
above a correct round-`r₀ + 2` block finalises it, in every view. -/
def MixedVerdict (U : Universe Validator BlockId Tx Obj) : Prop :=
  VotingRuleFive U →
  ∀ (tx : Tx) (r₀ R : ℕ) (b₀ : BlockId),
    T.Mixed tx →                      -- the consensus route's gate
    T.Valid tx →
    (∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx') →
    b₀ ∈ U.ids → (U.block b₀).author ∈ (Correct : Finset Validator) →
    (U.block b₀).round = r₀ → Includes U b₀ tx →
    R ≤ r₀ → SynchronisedOn U (Correct : Finset Validator) R →
    PopulatedOn U (Correct : Finset Validator) (r₀ + 1) →
                                      -- the FullLiveness hypotheses, verbatim
    ∀ (A : Anchors U) (V : View U) (prio : Tx → Tx → Prop) (i : ℕ) (a C : BlockId),
      A.seq[i]? = some a →            -- a committed anchor ...
      C ∈ U.ids → (U.block C).author ∈ (Correct : Finset Validator) →
      (U.block C).round = r₀ + 2 →
      Reaches U a C →                 -- ... above a correct certificate block (C5):
      VerdictFive U A V prio tx Fate.finalized
                                      -- the mixedFinal verdict

/-- Uncontested liveness at the `5f+1` rules, over every fault
configuration — at any committee `n ≥ 3f + 1` — transaction data, and
universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj),
    FullLiveness U ∧ FullVerdict U ∧ MixedVerdict U

end FiveUncontested

end RedSnapper

end LeanDag
