import LeanDag.RedSnapper.Model.Five.Freeze

/-!
# The voting rule at 5f+1

Trusted core: the liveness half of `CastVotes` (`Alg:Voting5f+1`) — what
a correct validator *does* write where no conflict exists — as a
hypothesis-predicate on the universe. The safety results consume
`MoveDiscipline` and `FreezeDiscipline`; uncontested liveness consumes
the three clauses here, and nothing else of the algorithm.

The `3f+1` `VotingRule` does not carry over. Its `bot_conflicted` is not
justified here: phase 2 writes `⊥` for a validator with no stance when
it freezes, and carries no `ConflictedObjs(b)` guard — the conflict is
the trigger anchor's, and the model does not assume a marker block
reaches its trigger. So a `⊥` declaration is traced to a visible
conflict *or* an own marker (`bot_contested`), and a marker to an anchor
that triggers (`freeze_triggered`); together they place a conflict
somewhere in the universe behind every correct `⊥`. Its
`keep_certVisible` reads the `3f+1` certificate and has no counterpart.

Scope, as for `VotingRule`: the rule models validators that have not yet
decided the object; the decided-stop is not modelled, and the claims
consuming the rule are conditional on it. With `Spendable` dropped from
candidacy (D3), `ack_sole` asks for an ACK on a version the paper would
not yet vote on; there the rule is false and the claims are silent,
never unsound. That a held ACK names a candidate — what lets phase 4's
`held ∈ {none, tx}` guard read as a stance — is
`FreezeDiscipline.ack_candidate`, not restated here.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- The `CastVotes` rule of correct validators at `5f+1`, clause by
clause: the uncontested path and the two origins of `⊥`. -/
structure VotingRuleFive (U : Universe Validator BlockId Tx Obj) : Prop where
  /-- The uncontested path (phase 4, with persistence folded into the
  stance read): where a sole candidate is visible and the author does
  not stand at `⊥`, it stands at the candidate. -/
  ack_sole : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), IsCandidate U b o tx →
      (∀ tx', IsCandidate U b o tx' → tx' = tx) →
      ¬ StanceIs U (U.block b).author o b (some Stance.bot) →
      StanceIs U (U.block b).author o b (some (Stance.ack tx))
  /-- `⊥` is declared only under a visible conflict (phase 3 ranges over
  `ConflictedObjs(b)`) or together with a freeze marker (phase 2). -/
  bot_contested : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, (U.block b).declares o = some Stance.bot →
      Conflicted U b o ∨ (U.block b).freezes o ≠ none
  /-- A marker names an anchor that triggers: phase 2 freezes on
  `TriggerAnchor(o)`. -/
  freeze_triggered : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (aₖ : BlockId), (U.block b).freezes o = some aₖ → Triggers U aₖ o

end RedSnapper

end LeanDag
