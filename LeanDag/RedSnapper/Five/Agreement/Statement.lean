import LeanDag.RedSnapper.Model.Five.Verdict
import LeanDag.RedSnapper.Model.Five.Moves

/-!
# 5f+1 agreement — statement

RS8: the paper's Theorem safety-5f, over the order-free verdict
relation: all derivable verdicts for one transaction agree across
views and routes, and no two conflicting transactions are both
finalised.

As with RS3, this is where the algorithm's `decidedObj` one-shot, route
precedence and `skippedTX` guards are discharged: the relation admits
every justifiable verdict, and the theorem shows route pairs never
disagree — the certificate pairs by RS6 (`FullCertUniqueness`,
`CommitExcludesUnlock`), the certificate-versus-recovery pairs by RS7
(`RecoveryReflects` closes the paper's miscited step of finding 9), and
the recovery pairs by resolution uniqueness. The three drops of
`FinalizeOnCommitTX`'s first loop — beside an observed or a certified
rival, above a resolution not won — close by the same lemmas. The two certificate routes
— `fullFinal` for an owned transaction, `mixedFinal` for a mixed one —
rest on the same evidence, a full certificate somewhere in the
universe, so every pair above covers both. The theorem takes the
`Five` bound — RS7's reflection claim needs it — together with the move
and freeze rules and the shared transaction order.

A mixed transaction is never finalised on an observation alone: every
route that finalises it runs at a committed anchor including it, which
is what lets execution order it against the shared-object traffic. That
claim reads the relation only and takes no hypothesis, like RS3's
`MixedViaAnchor`.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveAgreement

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Verdict agreement**: any two derivable verdicts for one
transaction, from any two views, carry the same fate. -/
def VerdictAgreement (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop) : Prop :=
  ∀ (V V' : View U) (tx : Tx) (f f' : Fate),
    VerdictFive U A V prio tx f → VerdictFive U A V' prio tx f' → f = f'

/-- **No conflicting finalisation**: two conflicting transactions are
never both finalised, from any two views. -/
def NoConflictingFinal (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop) : Prop :=
  ∀ (V V' : View U) (tx tx' : Tx), Conflict tx tx' →
    VerdictFive U A V prio tx Fate.finalized →
    VerdictFive U A V' prio tx' Fate.finalized → False

/-- **Mixed via anchor**: a finalised mixed transaction is a candidate
of some committed anchor, and that anchor holds what finalised it — a
full certificate in its history, or the election it resolves. -/
def MixedViaAnchor (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop) : Prop :=
  ∀ (V : View U) (tx : Tx), T.Mixed tx → VerdictFive U A V prio tx Fate.finalized →
    ∃ (i : ℕ) (a : BlockId), A.seq[i]? = some a ∧ IsCandidate U a (T.input tx) tx ∧
      ((∃ C ∈ U.ids, Reaches U a C ∧ IsFullCert U C tx) ∨
        ∃ (i' : ℕ) (aₖ : BlockId), ResolvesFiveAt U A (T.input tx) i' i ∧
          A.seq[i']? = some aₖ ∧ EligibleFive U aₖ a (T.input tx) tx)

/-- Fast-path safety at `n ≥ 5f + 1`, over every fault configuration,
transaction data, universe, anchor sequence, and shared linear order
the model admits: agreement under the move and freeze rules, and the
anchor claim under none. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop),
    (IsLinearOrder Tx prio →
      Five Validator → MoveDiscipline U → FreezeDiscipline U →
      VerdictAgreement U A prio ∧ NoConflictingFinal U A prio) ∧
      MixedViaAnchor U A prio

end FiveAgreement

end RedSnapper

end LeanDag
