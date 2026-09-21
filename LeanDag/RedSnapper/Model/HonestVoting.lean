import LeanDag.RedSnapper.Model.Votes
import LeanDag.RedSnapper.Model.Certificates

/-!
# The voting rule

Trusted core: the liveness half of D5 — what `CastVotes`
(`Alg:Snapper3f+1`) says a correct validator *does* write, as a
hypothesis-predicate on the universe. Safety consumed only the stance
discipline (`Model/Stance.lean`); the liveness results additionally
consume the five clauses here, and nothing else of the algorithm.

Scope, stated once. The rule models validators that have **not yet
decided** the object: the paper's decided-stop (`held = decided`, no
further declarations) is not modelled. A validator that decides an
object before ever declaring on it then falls silent where
`conflicted_declares` — or, deciding before adopting, `ack_sole` —
demands a stance; and the rule is one predicate over all objects and
rounds, so a single such validator anywhere voids it for the whole
universe. The liveness claims are conditional on the rule and simply do
not apply there — the honest analogue of `SynchronisedOn` being an
assumption. The phase-2 retraction-on-`Dead` clause is not modelled
either: no claim of this arc consumes it.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- The `CastVotes` rule of correct validators, clause by clause. -/
structure VotingRule (U : Universe Validator BlockId Tx Obj) : Prop where
  /-- An ACK declares a candidate: `Adopt` is only ever called on a
  member of `Candidates(b, o)` (phases 3 and 2's keep branch). -/
  ack_candidate : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), (U.block b).declares o = some (Stance.ack tx) →
      IsCandidate U b o tx
  /-- `⊥` is declared only with the conflict visible: phase 2 ranges
  over `RecoveryObjs(b)`, which is `Conflicted` under D2. -/
  bot_conflicted : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, (U.block b).declares o = some Stance.bot → Conflicted U b o
  /-- The uncontested path (phase 3, with persistence folded into the
  stance read): where a sole candidate is visible and the author does
  not stand at `⊥`, it stands at the candidate. The `⊥` premise is
  redundant under `bot_conflicted` — a `⊥` read needs a visible
  conflict, contradicting soleness — and kept for fidelity to the
  paper's `held ∈ {none, tx}` guard. -/
  ack_sole : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), IsCandidate U b o tx →
      (∀ tx', IsCandidate U b o tx' → tx' = tx) →
      ¬ StanceIs U (U.block b).author o b (some Stance.bot) →
      StanceIs U (U.block b).author o b (some (Stance.ack tx))
  /-- A conflicted correct block declares: phase 2 writes the stance
  again in every round while the object is in recovery and undecided. -/
  conflicted_declares : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, Conflicted U b o → (U.block b).declares o ≠ none
  /-- The keep branch of phase 2: an ACK declared under a visible
  conflict has a certificate visible from the parents. -/
  keep_certVisible : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), Conflicted U b o →
      (U.block b).declares o = some (Stance.ack tx) → CertVisible U b tx

end RedSnapper

end LeanDag
