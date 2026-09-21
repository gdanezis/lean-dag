import LeanDag.RedSnapper.Model.Five.Certificates
import LeanDag.RedSnapper.Model.Anchors
import LeanDag.RedSnapper.Model.Transaction

/-!
# Freeze and the deterministic recovery

Trusted core: §8's fallback machinery (`Alg:FastPathPredicates5f+1`:
`Triggers`, `TriggerAnchor`, `Frozen`, `Resolves`; `Alg:snapper5f`:
`ResolveOnCommitObj`'s `F` and `W`) over the anchors of D4.

The `5f+1` recovery works over the paper's `Candidates`, where owned
and mixed transactions compete on their owned input: the shared
`IsCandidate`, with no class gate. An anchor *triggers* recovery for an
object when it sees the object conflicted and neither a full
certificate for a candidate nor a full unlock certificate anywhere in
its history. The **trigger anchor** is the first committed anchor that
triggers — the paper's recovery parameter `k` is fixed at `0`: it only
delays the fallback, appears in no safety argument, and a general
"`k`-th anchor satisfying a property" would put an exact count into the
trusted core for nothing audited.

A validator *freezes* by publishing a marker naming the trigger anchor
(`Block.freezes`); `Frozen` reads markers from causal history. The
**resolving anchor** is the first committed anchor after the trigger
whose history carries markers from a quorum of validators — one-shot,
by the least-index clause; the paper's defensive `Link(A_k, A)` test is
implied by `Anchors.chained` and dropped. At the resolving anchor, a
candidate is *eligible* — the paper's `W` — when `half` of the frozen
validators stand at it. Validator-set thresholds use `AtLeastV`, the
witness-set counting of `AtLeast` over validators, so the trusted core
never decides `Frozen`.

`FreezeDiscipline` is the Phase 8 behavioural hypothesis on correct
validators, alongside the untouched `MoveDiscipline`: a marker block
declares its frozen value (phase 2 publishes it "one last time"); at or
above an own marker the declaration never changes; and a declared ACK
names a candidate of the declaring block — the `Adopt` guard "never
adopt a candidate this block does not admit", which is what places a
frozen transaction inside the resolving anchor's history.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- At least `k` validators satisfy `P`: the witness-set threshold of
`AtLeast`, over validators. -/
def AtLeastV (k : ℕ) (P : Validator → Prop) : Prop :=
  ∃ t : Finset Validator, (∀ v ∈ t, P v) ∧ k ≤ t.card

/-- `a` triggers recovery for `o` (the paper's `Triggers`): `a` sees `o`
conflicted, and neither a full unlock certificate for `o` nor a full
certificate for any candidate anywhere in its history. -/
def Triggers (U : Universe Validator BlockId Tx Obj) (a : BlockId) (o : Obj) : Prop :=
  Conflicted U a o ∧
    (¬ ∃ b ∈ U.ids, Reaches U a b ∧ IsFullUnlockCert U b o) ∧
    ¬ ∃ tx, IsCandidate U a o tx ∧ ∃ b ∈ U.ids, Reaches U a b ∧ IsFullCert U b tx

/-- The trigger anchor sits at index `i` (the paper's `TriggerAnchor`
at `k = 0`): the least committed index whose anchor triggers. -/
def TriggerAt (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (o : Obj)
    (i : ℕ) : Prop :=
  (∃ a, A.seq[i]? = some a ∧ Triggers U a o) ∧
    ∀ j < i, ∀ a, A.seq[j]? = some a → ¬ Triggers U a o

/-- `id` froze on `o` for the trigger anchor `aₖ`, visibly from `b` (the
paper's `Frozen`): an own block in `b`'s history carries the marker. -/
def Frozen (U : Universe Validator BlockId Tx Obj) (aₖ : BlockId) (id : Validator)
    (o : Obj) (b : BlockId) : Prop :=
  ∃ m ∈ U.ids, (U.block m).author = id ∧ Reaches U b m ∧
    (U.block m).freezes o = some aₖ

/-- `b` sees freeze markers for `(aₖ, o)` from a quorum of validators. -/
def FreezeQuorum (U : Universe Validator BlockId Tx Obj) (aₖ : BlockId) (o : Obj)
    (b : BlockId) : Prop :=
  AtLeastV (quorum Validator) fun id => Frozen U aₖ id o b

/-- The recovery resolves `o` at the index pair `(i, j)` (the paper's
`Resolves`): the trigger sits at `i`, `j` is a later index whose anchor
sees a quorum of freeze markers for it, and no committed anchor before
`j` — the trigger itself included — sees one: the paper's one-shot
clause, exactly. The paper's `Link(A_k, A)` test is implied by
`Anchors.chained`. -/
def ResolvesFiveAt (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (o : Obj)
    (i j : ℕ) : Prop :=
  TriggerAt U A o i ∧ i < j ∧
    (∃ aₖ a, A.seq[i]? = some aₖ ∧ A.seq[j]? = some a ∧ FreezeQuorum U aₖ o a) ∧
    ∀ j' < j, ∀ aₖ a, A.seq[i]? = some aₖ → A.seq[j']? = some a →
      ¬ FreezeQuorum U aₖ o a

/-- `tx` is eligible at the resolving anchor `a` under trigger `aₖ`
(membership in the paper's `W`): a candidate of `a`, owned or mixed, at
which `half` of the frozen validators stand. -/
def EligibleFive (U : Universe Validator BlockId Tx Obj) (aₖ a : BlockId) (o : Obj)
    (tx : Tx) : Prop :=
  IsCandidate U a o tx ∧
    AtLeastV (half Validator) fun id =>
      Frozen U aₖ id o a ∧ StanceIs U id o a (some (Stance.ack tx))

/-- The freeze rule of correct validators (phase 2 of `CastVotes`, plus
the `Adopt` guard), as a hypothesis-predicate: what the recovery-safety
results consume beyond `MoveDiscipline`. -/
structure FreezeDiscipline (U : Universe Validator BlockId Tx Obj) : Prop where
  /-- A correct marker block publishes its frozen value: freezing on `o`
  declares on `o` — the frozen stance is readable from the marker. -/
  freeze_declares : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (aₖ : BlockId), (U.block b).freezes o = some aₖ →
      (U.block b).declares o ≠ none
  /-- The frozen stance is permanent: at or above an own marker block, a
  correct block declares on `o` nothing, or exactly what the marker
  block declared. -/
  freeze_final : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ m ∈ U.ids, (U.block m).author = (U.block b).author → Reaches U b m →
    ∀ (o : Obj) (aₖ : BlockId), (U.block m).freezes o = some aₖ →
      (U.block b).declares o = none ∨ (U.block b).declares o = (U.block m).declares o
  /-- A correct ACK declaration names a candidate of the declaring block
  (the `Adopt` guard): a frozen transaction therefore lies in the
  history of whatever sees the marker. -/
  ack_candidate : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), (U.block b).declares o = some (Stance.ack tx) →
      IsCandidate U b o tx

end RedSnapper

end LeanDag
