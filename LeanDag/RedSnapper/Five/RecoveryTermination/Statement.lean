import LeanDag.RedSnapper.Model.Five.Verdict

/-!
# Recovery termination — statement

RS9b: the paper's Lemma recovery-termination, conditional on its two
consensus-liveness inputs rendered structurally — anchors keep coming
(C4) is the given later index, and "some committed anchor contains the
markers" (C5) plus the freeze rule's liveness is the premise that every
correct validator's marker is visible at it. None of it needs `Five`:
the marker quorum is filled by `Correct` alone at any committee.

* **The trigger exists**: an anchor seeing the conflict, in a universe
  where no certificate route ever fires — no full certificate for any
  transaction on the object, owned or mixed, and no full unlock
  certificate, the "not resolved by a certificate" hypothesis, taken
  globally — triggers; the least such index is the trigger index. The
  global form is strictly stronger than the paper's temporal reading
  (there certificate-absence is *derived* from the routes never
  firing); the model has no route-fired event to condition on, and for
  a termination lemma the stronger premise is the honest side to err
  on.
* **The resolution exists**: with the trigger at `i` and a later anchor
  seeing markers from every correct validator, some index in between
  (bounds included on the right) resolves — the first marker quorum.
  The premise that no anchor at or before the trigger sees a quorum is
  the structural reading of "markers causally follow the trigger's
  commit"; without it the paper's one-shot clause (now exact, Phase 8)
  could refuse every index.
* **The resolution decides**: at a resolving anchor, under any shared
  linear order, every candidate of the object receives a verdict
  — the `prio`-minimal eligible transaction is finalised and the rest
  dropped, or, with nothing eligible, all are dropped. The minimal
  element exists because eligible transactions are carried in the
  anchor's finite history.
* **The conflict is decided**: the lemma as the paper now states it, by
  its three cases. A full unlock certificate drops the candidates; a
  full certificate finalises its transaction — on observation if owned,
  at a committed anchor above the certificate if mixed (C5); and with
  neither anywhere, the three claims above compose. The view holds the
  whole universe ("eventually observed", as in RS4's `FastVerdict`), and
  the consensus-liveness inputs are premises: mixed certificates land
  under an anchor, and the trigger's markers land under a later one.
  The marker input is asked only where no certificate exists, as in the
  paper: a validator that has decided the object on a certificate never
  freezes, so with a certificate around the markers may never come.
-/

namespace LeanDag

namespace RedSnapper

namespace RecoveryTermination

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- **The trigger exists**: a conflicted anchor in a certificate-free
universe yields a trigger index at or below its own. -/
def TriggerExists (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (o : Obj) (i : ℕ) (a : BlockId),
    A.seq[i]? = some a →                  -- a committed anchor ...
    Conflicted U a o →                    -- ... that sees the conflict, while
    (∀ C ∈ U.ids, ¬ IsFullUnlockCert U C o) →
                                          -- no full unlock certificate and
    (∀ tx, T.input tx = o → ∀ C ∈ U.ids, ¬ IsFullCert U C tx) →
                                          -- no full certificate exists anywhere —
                                          -- no certificate route ever fires:
    ∃ i' ≤ i, TriggerAt U A o i'          -- then the trigger index exists, at or below

/-- **The resolution exists**: full marker visibility at a later anchor
yields a resolving index in between. -/
def ResolutionExists (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (o : Obj) (i j : ℕ) (aₖ a : BlockId),
    TriggerAt U A o i →                   -- the trigger at index i ...
    A.seq[i]? = some aₖ → A.seq[j]? = some a →
                                          -- ... and a committed anchor (C4; that
                                          -- j > i follows from the premises)
    (∀ i' ≤ i, ∀ a', A.seq[i']? = some a' → ¬ FreezeQuorum U aₖ o a') →
                                          -- no quorum at or before the trigger: the
                                          -- structural "markers causally follow the
                                          -- trigger's commit"
    (∀ v ∈ (Correct : Finset Validator), Frozen U aₖ v o a) →
                                          -- every correct validator's marker is visible
                                          -- at it (C5 + the freeze rule's liveness):
    ∃ j', i < j' ∧ j' ≤ j ∧ ResolvesFiveAt U A o i j'
                                          -- then some index in (i, j] resolves

/-- **The resolution decides**: every candidate of the resolving anchor
receives a verdict, in every view. -/
def RecoveryDecides (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (prio : Tx → Tx → Prop), IsLinearOrder Tx prio →
                                          -- the shared tie-break order (D8)
  ∀ (V : View U) (o : Obj) (i j : ℕ) (a : BlockId) (tx : Tx),
    ResolvesFiveAt U A o i j →            -- a resolution ...
    A.seq[j]? = some a →
    IsCandidate U a o tx →                -- ... and any candidate it sees:
    VerdictFive U A V prio tx Fate.finalized ∨ VerdictFive U A V prio tx Fate.dropped
                                          -- the candidate is decided, in every view

/-- **The conflict is decided**: an object conflicted at a committed
anchor has a transaction with a verdict, in any view holding the whole
universe, given the two consensus-liveness inputs. -/
def ConflictDecides (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  ∀ (prio : Tx → Tx → Prop), IsLinearOrder Tx prio →
  ∀ (V : View U) (o : Obj) (i : ℕ) (a : BlockId),
    U.ids ⊆ V.ids →                       -- every certificate is eventually observed
    A.seq[i]? = some a → Conflicted U a o →
                                          -- a committed anchor sees the conflict
    (∀ tx, T.Mixed tx → T.input tx = o → ∀ C ∈ U.ids, IsFullCert U C tx →
      ∃ (i' : ℕ) (a' : BlockId), A.seq[i']? = some a' ∧ Reaches U a' C) →
                                          -- a mixed transaction's full certificate
                                          -- lands under a committed anchor (C5)
    ((∀ C ∈ U.ids, ¬ IsFullUnlockCert U C o) →
      (∀ tx, T.input tx = o → ∀ C ∈ U.ids, ¬ IsFullCert U C tx) →
                                          -- where no certificate exists anywhere:
      ∀ (i' : ℕ) (aₖ : BlockId), TriggerAt U A o i' → A.seq[i']? = some aₖ →
        (∀ i'' ≤ i', ∀ a'', A.seq[i'']? = some a'' → ¬ FreezeQuorum U aₖ o a'') ∧
          ∃ (j : ℕ) (a' : BlockId), A.seq[j]? = some a' ∧
            ∀ v ∈ (Correct : Finset Validator), Frozen U aₖ v o a') →
                                          -- the trigger's markers follow it, and land
                                          -- under a later anchor (C5 + the freeze rule):
                                          -- the premises of `ResolutionExists`
    ∃ tx, T.input tx = o ∧
      (VerdictFive U A V prio tx Fate.finalized ∨ VerdictFive U A V prio tx Fate.dropped)
                                          -- then some transaction on the object is decided

/-- Recovery termination, over every fault configuration — at any
committee `n ≥ 3f + 1` — transaction data, universe and anchor
sequence the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (A : Anchors U),
    TriggerExists U A ∧ ResolutionExists U A ∧ RecoveryDecides U A ∧ ConflictDecides U A

end RecoveryTermination

end RedSnapper

end LeanDag
