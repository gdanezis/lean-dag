import LeanDag.RedSnapper.Model.Five.Verdict

/-!
# Termination at 5f+1 — statement

RS12: the paper's Lemma termination-5f — every transaction placed in the
global order is eventually decided — on its contested half. The
uncontested half is RS10: a transaction with no valid rival is
finalized.

RS9b's `ConflictDecides` says that a contested *object* is decided: some
transaction on it receives a verdict. This is the per-transaction form,
which the algorithm has only since `FinalizeOnCommitTX`'s first loop
aborts owned candidates too (record finding 33): every candidate of a
committed anchor receives a verdict, by the lemma's cases. A full unlock
certificate drops it. Its own full certificate finalises it, on
observation if owned and at a committed anchor above the certificate if
mixed. A rival's full certificate drops it — the loser of a fast commit,
which no route reached before: on observation if the rival is owned
(`observedRivalDrop`), under the certificate's anchor if it is mixed
(`certifiedRivalDrop`). With no certificate anywhere and a rival ordered
too, some committed anchor sees the conflict, RS9b's trigger and
resolution exist, and the transaction is decided at the resolving anchor
if it is a candidate there, and otherwise either won or is dropped above
it (`resolvedDrop`).

The view holds the whole universe ("eventually observed"), and the
consensus-liveness inputs are those of `ConflictDecides`: a mixed
transaction's full certificate lands under a committed anchor, and,
where no certificate exists, the trigger's markers follow it and land
under a later anchor. Where no certificate exists the statement also
asks for a rival under a committed anchor — contested, in the global
order. What is left between this half and RS10 is a run with no
certificate in which a valid rival is included somewhere and never
ordered: RS10's premise, which speaks of every block of the universe,
fails there, and so does this one.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveTermination

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Decided**: every candidate of a committed anchor receives a
verdict, in any view holding the whole universe, given the
consensus-liveness inputs and, where no certificate exists, an ordered
rival. -/
def Decided (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (prio : Tx → Tx → Prop), IsLinearOrder Tx prio →
  ∀ (V : View U) (tx : Tx) (m : ℕ) (a : BlockId),
    U.ids ⊆ V.ids →                       -- every certificate is eventually observed
    A.seq[m]? = some a → IsCandidate U a (T.input tx) tx →
                                          -- placed in the global order
    (∀ tx', T.Mixed tx' → T.input tx' = T.input tx → ∀ C ∈ U.ids, IsFullCert U C tx' →
      ∃ (k : ℕ) (a' : BlockId), A.seq[k]? = some a' ∧ Reaches U a' C) →
                                          -- a mixed transaction's full certificate
                                          -- lands under a committed anchor (C5)
    ((∀ C ∈ U.ids, ¬ IsFullUnlockCert U C (T.input tx)) →
      (∀ tx', T.input tx' = T.input tx → ∀ C ∈ U.ids, ¬ IsFullCert U C tx') →
                                          -- where no certificate exists anywhere:
      (∃ (k : ℕ) (a' : BlockId) (tx' : Tx), A.seq[k]? = some a' ∧
        IsCandidate U a' (T.input tx) tx' ∧ tx' ≠ tx) ∧
                                          -- a rival is in the global order too, and
      ∀ (i' : ℕ) (aₖ : BlockId), TriggerAt U A (T.input tx) i' → A.seq[i']? = some aₖ →
        (∀ i'' ≤ i', ∀ a'', A.seq[i'']? = some a'' → ¬ FreezeQuorum U aₖ (T.input tx) a'') ∧
          ∃ (j : ℕ) (a' : BlockId), A.seq[j]? = some a' ∧
            ∀ v ∈ (Correct : Finset Validator), Frozen U aₖ v (T.input tx) a') →
                                          -- the trigger's markers follow it, and land
                                          -- under a later anchor: `ConflictDecides`' input
    VerdictFive U A V prio tx Fate.finalized ∨ VerdictFive U A V prio tx Fate.dropped

/-- Termination at the `5f+1` rules, contested half, over every fault
configuration — at any committee `n ≥ 3f + 1` — transaction data,
universe and anchor sequence the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (A : Anchors U),
    Decided U A

end FiveTermination

end RedSnapper

end LeanDag
