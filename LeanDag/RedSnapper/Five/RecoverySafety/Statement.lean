import LeanDag.RedSnapper.Model.Five.Freeze
import LeanDag.RedSnapper.Model.Five.Moves

/-!
# Recovery safety — statement

RS7: the safety of §8's deterministic fallback — Lemmas
recovery-determinism (in its in-model form), recovery-reflects, and
recovery-safety.

Recovery-determinism in the paper says all correct validators compute
the same trigger anchor, frozen set, `W` and `win`; under D4 the
anchors are one global value and every recovery quantity is a function
of `(U, A)`, so cross-validator agreement is definitional — what
remains, and what `ResolutionUnique` states, is that the *relations*
rendering them are functional: one resolving index pair per object, one
`prio`-minimal winner. Recovery-reflects is stated without the paper's
candidacy premise — candidacy at the resolving anchor is *derived*,
through `FreezeDiscipline.ack_candidate`, from the frozen ACKs the
certificate forces — which is the strengthening RS8's cross-route cases
need. The paper's second clause of recovery-reflects — a full unlock
certificate empties the election — is stated beside it, and needs no
wide committee: the unlocking core's `⊥` stances persist into the
markers and leave no room for `half` frozen supporters.

Where the committee bound finally bites: `RecoveryReflects` and
`RecoverySafetyBot`'s conflicted case count `|F ∩ S| ≥ |S| − f` and
`|F| − 2f`, which need `n ≥ 5f + 1` — the first results of the arc to
consume `Five`, taken as an explicit hypothesis exactly there.
`RecoverySafetyWin` needs only the `half` frozen supporters of the
winner (`f + 1` of them correct and permanent) and holds at any
committee, like all of RS6 (finding 19) — and, the arc-wide audit
found, under the freeze rule alone, at any block, with no resolution in
sight: the three election claims are stated at a bare marker quorum (or
bare eligibility, for the winner), which every resolving anchor
supplies a fortiori.

* **Resolution uniqueness**: at most one `(i, j)` resolves an object,
  and at most one eligible transaction is `prio`-minimal.
* **Recovery reflects a hidden commit** (Lemma recovery-reflects): if
  a transaction on the resolved object, owned or mixed, holds a full
  certificate anywhere — at any round, before or after the resolution —
  then it is eligible and uniquely so: `W = {tx}`.
* **Recovery reflects a hidden release** (Lemma recovery-reflects,
  second clause): if the object holds a full unlock certificate
  anywhere, nothing is eligible: `W = ∅`.
* **Recovery safety, release** (Lemma recovery-safety, claim 1): if
  nothing is eligible at the resolution, no transaction on the object
  ever holds a full certificate.
* **Recovery safety, winner** (Lemma recovery-safety, claim 2): a
  conflicting rival of any eligible transaction holds no full
  certificate above the resolving anchor's round.
-/

namespace LeanDag

namespace RedSnapper

namespace RecoverySafety

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Resolution uniqueness**: one index pair per object, one
`prio`-minimal winner. -/
def ResolutionUnique (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop) : Prop :=
  (∀ (o : Obj) (i j i' j' : ℕ),
    ResolvesFiveAt U A o i j → ResolvesFiveAt U A o i' j' → i = i' ∧ j = j') ∧
  ∀ (aₖ a : BlockId) (o : Obj) (tx tx' : Tx),
    EligibleFive U aₖ a o tx → (∀ t, EligibleFive U aₖ a o t → prio tx t) →
    EligibleFive U aₖ a o tx' → (∀ t, EligibleFive U aₖ a o t → prio tx' t) →
    tx = tx'

/-- **Recovery reflects a hidden commit**: a full certificate anywhere
makes its transaction the unique eligible one — at *any* block carrying
a marker quorum. The arc-wide audit found the resolution apparatus
(`ResolvesFiveAt`'s trigger and one-shot clauses) dead in the proof and
dropped it: the quorum of markers is all the claim consumes, so it
covers every resolving anchor a fortiori. -/
def RecoveryReflects (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (o : Obj) (aₖ a : BlockId) (tx : Tx),
    a ∈ U.ids → FreezeQuorum U aₖ o a →
    T.input tx = o →
    (∃ C ∈ U.ids, IsFullCert U C tx) →
    EligibleFive U aₖ a o tx ∧ ∀ tx', EligibleFive U aₖ a o tx' → tx' = tx

/-- **Recovery reflects a hidden release**: a full unlock certificate
anywhere leaves nothing eligible, at any block — no marker quorum is
consumed, and no wide committee. -/
def UnlockEmptiesElection (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (o : Obj) (aₖ a : BlockId),
    a ∈ U.ids →
    (∃ C ∈ U.ids, IsFullUnlockCert U C o) →
    ∀ tx, ¬ EligibleFive U aₖ a o tx

/-- **Recovery safety, release**: an empty election at a marker quorum
forbids a full certificate for any transaction on the object, at any
round. -/
def RecoverySafetyBot (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (o : Obj) (aₖ a : BlockId),
    a ∈ U.ids → FreezeQuorum U aₖ o a →
    (∀ tx, ¬ EligibleFive U aₖ a o tx) →
    ∀ tx, T.input tx = o → ∀ C ∈ U.ids, ¬ IsFullCert U C tx

/-- **Recovery safety, winner**: no rival of an eligible transaction
reaches a full certificate above the electing block's round. Like the
reflection claim, stated at any block — and, the audit found, needing
neither the resolution nor the move rule: the winner's frozen
supporters alone carry it. -/
def RecoverySafetyWin (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (o : Obj) (aₖ a : BlockId) (tx : Tx),
    a ∈ U.ids →
    EligibleFive U aₖ a o tx →
    ∀ tx', Conflict tx tx' →
      ∀ C ∈ U.ids, (U.block a).round < (U.block C).round → ¬ IsFullCert U C tx'

/-- Recovery safety, over every fault configuration, transaction data,
universe and anchor sequence the model admits: uniqueness for any
linear order; under the freeze rule alone, the winner claim at any
committee; adding the move rule, the hidden-release claim, still at any
committee; and, adding `n ≥ 5f + 1`, the reflection and release
claims. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj),
    (∀ (A : Anchors U) (prio : Tx → Tx → Prop), IsLinearOrder Tx prio →
      ResolutionUnique U A prio) ∧
      (FreezeDiscipline U →
        RecoverySafetyWin U ∧
          (MoveDiscipline U →
            UnlockEmptiesElection U ∧
              (Five Validator → RecoveryReflects U ∧ RecoverySafetyBot U)))

end RecoverySafety

end RedSnapper

end LeanDag
