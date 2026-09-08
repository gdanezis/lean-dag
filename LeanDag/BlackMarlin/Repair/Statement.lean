import LeanDag.BlackMarlin.Model.Repair
import LeanDag.BlackMarlin.Liveness.Statement
/-!
# Black Marlin — the repair, stated

The execution of `black-marlin.md` §13 turns on `commit`'s descent
taking an unsupported twin where the rule had committed the supported
one. This phase asks what a side-condition on the descent yields and what
it costs (`black-marlin.md` §14); `descend` and `flushRecord` stand
unaltered. `descendSupp` prefers a supported candidate where there is
one (BMP2) and is L21–L24 verbatim otherwise (BMP3) — a refinement, not
a replacement — since at most one candidate of a step is ever supported
(BMP1). It never stalls (BMP4), agrees with any other support-preferring
record wherever an anchor is supported (BMP5, what §13's execution
needed), and leaves the liveness results untouched since `Committed` is
a property of the rule alone (BMP6). `descendS` instead drops the
tie-break outright and descends to the highest-round supported anchor of
the cone (BMP7–BMP12). BMP13 is the one case a validator can apply
either from its own view: a reliable author's anchor, past the round
coverage takes hold — not the case the repair exists for.

**What this does not settle.** A validator computes support from its own
view, which under-reports, so a record it builds meets
`SupportPreferring` only if the support it needs is in view when it
descends — true in §13's execution, not established in general. The
repair is stated, not supplied; §14 records what supplying it would
take.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Repair

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BMP1, at most one candidate of a step is supported.** -/
def AtMostOneSupported (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B A C : BlockId), A ∈ suppCandidates U B → C ∈ suppCandidates U B → A = C

/-- **BMP2, the repair takes the supported candidate.** -/
def RepairPrefers (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B L : BlockId), descendSupp U B = some L → (suppCandidates U B).Nonempty →
    Supported U L (U.block L).round

/-- **BMP3, and is the original rule where there is none.** -/
def RepairRefines (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B : BlockId), ¬ (suppCandidates U B).Nonempty → descendSupp U B = descend U B

/-- **BMP4, the repair changes which block a step returns, never whether
it returns one nor at which round.** Stated of a step, not of a record:
a chain through a different block descends through a different cone, so
the rounds a record flushes at may differ downstream. -/
def NoStall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (B : BlockId), (descendSupp U B).isSome ↔ (descend U B).isSome) ∧
  (∀ (B L L' : BlockId), descendSupp U B = some L → descend U B = some L' →
    (U.block L).round = (U.block L').round)

/-- **BMP5, support-preferring records cannot part at a supported
round.** The whole content of the repair, and what the execution of
`black-marlin.md` §13 needed. -/
def Agrees (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ : ℕ),
    SupportPreferring U f₁ → SupportPreferring U f₂ →
    (f₁.block ρ).isSome → (f₂.block ρ).isSome →
    (∃ A, IsAnchor U ρ A ∧ Supported U A ρ) →
    f₁.block ρ = f₂.block ρ

/-- **BMP6, liveness is untouched.** What the liveness results conclude
is `Committed`, which is a property of the commit rule and mentions no
part of the descent — so the repair leaves them
untouched, and the statement is the identity it looks like. -/
def LivenessUntouched (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (ρ : ℕ),
    Committed U L ρ ↔ (IsAnchor U ρ L ∧ Supported U L ρ ∧ Linked U L ρ)

/-! ## The strengthened repair

`descendSupp` only chooses among the candidates L21–L24 already offers;
`descendS` drops the tie-break and descends to the highest-round
supported anchor of the cone outright. -/

/-- **BMP7, every boundary is supported.** So a round whose anchors carry
no quorum is not a boundary at all: where an anchor equivocates and
neither twin is supported, the strengthened descent makes no choice
there, and two records cannot part over one. -/
def StrongSupported (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B L : BlockId), descendS U B = some L → Supported U L (U.block L).round

/-- **BMP8, and no committed anchor is passed by.** A supported anchor
sits at every round the chain could land on above a committed one — the
committed anchor itself from two rounds up, and its linking anchor from
one, which the commit rule makes supported — and anchor uniqueness fixes
which block each of those is. -/
def StrongReaches (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B L : BlockId) (ρ : ℕ), B ∈ U.ids → Committed U L ρ → L ∈ strongOf U B →
    flushRecordS U B ρ = some L

/-- **BMP9, and agreement runs down from any meeting point.** With BMP8
this is what the refutation needed: two records whose tops are committed
anchors both reach the lower of the two — BM5 puts it in the higher's
cone — and so agree at every round below it. -/
def StrongAgrees (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B₁ B₂ M : BlockId) (σ ρ : ℕ), B₁ ∈ U.ids → B₂ ∈ U.ids →
    flushRecordS U B₁ σ = some M → flushRecordS U B₂ σ = some M → ρ ≤ σ →
    flushRecordS U B₁ ρ = flushRecordS U B₂ ρ

/-- **BMP10, and it does not stall.** A choice is made whenever the cone
holds a supported anchor, and it sits strictly lower, so the descent
terminates. Coarser segments deliver the same blocks: a round that is no
longer a boundary has its blocks come out inside the next segment
above. -/
def StrongNoStall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (B : BlockId), (suppAnchorsOf U (strongOf U B)).Nonempty → (descendS U B).isSome) ∧
  (∀ (B L : BlockId), B ∈ U.ids → descendS U B = some L →
    (U.block L).round < (U.block B).round)

/-- **BMP11, two records with committed tops agree.** The composition:
chaining puts the lower top in the higher's cone (BM5), BMP8 makes both
descents reach it, and BMP9 carries agreement to every round below. This
is what the execution of `black-marlin.md` §13 needed and did not have,
and it holds with no hypothesis about what lies between the two tops. -/
def StrongAgreesCommitted (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B₁ B₂ : BlockId) (r₁ r₂ ρ : ℕ), B₁ ∈ U.ids → B₂ ∈ U.ids →
    Committed U B₁ r₁ → Committed U B₂ r₂ → r₁ ≤ r₂ → ρ ≤ r₁ →
    flushRecordS U B₁ ρ = flushRecordS U B₂ ρ

/-- **BMP13, when the support is in view.** Both repairs read
`Supported`, a fact about the universe, where a validator reads its own
view; they agree at a reliable author's anchor past the round coverage
takes hold, since coverage puts the quorum in any view holding the round
above. For a Byzantine author's anchor coverage says nothing, so this
does not reach the case the repair exists for. -/
def SupportInView (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ) (V : View Validator BlockId Payload U) (L : BlockId),
    quorumCard Validator ≤ T.card →
    SynchronisedOn U T R → R ≤ ρ → PopulatedOn U T (ρ + 1) →
    L ∈ U.ids → (U.block L).round = ρ → (U.block L).creator ∈ T →
    (∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = ρ + 1 → b ∈ V.ids) →
    SupportedIn U V L ρ

variable (Validator BlockId Payload) in
/-- **BMP12, and no execution is stuck.** Recurrence of committed rounds
is a statement about `Committed` and the rotation, neither touched by
the repair, so it holds word for word of the repaired protocol. -/
def NotStuck : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    quorumCard Validator ≤ T.card → Liveness.FairRun T 2 →
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ Liveness.CommitsAtRound BlockId Payload T R r'

/-- The repaired descent, over every fault configuration, rotation and
block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    AtMostOneSupported U ∧ RepairPrefers U ∧ RepairRefines U ∧ NoStall U ∧
      Agrees U ∧ LivenessUntouched U ∧
      StrongSupported U ∧ StrongReaches U ∧ StrongAgrees U ∧ StrongNoStall U ∧
      StrongAgreesCommitted U ∧ SupportInView U ∧
      NotStuck Validator BlockId Payload

end Repair

end BlackMarlin

end LeanDag
