import LeanDag.BlackMarlin.Agreement.Statement
/-!
# Black Marlin — liveness at a validator's view, stated

BML1–BML5 and BMR1–BMR6 conclude `Committed U L r`: the **universe**
admits a commit. A validator delivers from its own view, so liveness
has to be read there or it is about the wrong thing
(`black-marlin.md` §15). BMV1 is BML4 and BMP12 read at the view: above
every round a later one that every reliable validator commits on its
own view, by an explicit time. BMV2 is BMA3 with its round hypothesis
discharged. BMV3 is why both go through: at a reliably anchored round
past coverage, a validator holding the round above's reliable blocks
can evaluate the support clause with no waiting.

**It stops at the delivered order.** The descent reads `Supported` at
whichever anchor its chain lands on, and where that anchor is Byzantine
BMV3 has no counterpart: coverage says nothing about a Byzantine
validator's blocks, and a committed anchor's quorum of `2f + 1`
supporters need contain only `f + 1` reliable ones.
`LeanDagTest/BlackMarlin/Counting` exhibits a view holding every
reliable block in which neither of an equivocator's twins is supported.
So the repair of §14 has no live implementation: a validator running
`descendS` either decides from what it holds and can select the wrong
block, or waits for a quorum the equivocator need never complete. BMV3
is the line between the two.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace ViewLiveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **What it means for a round to be committed by every reliable
validator on its own view.** Universe, growth and pace are quantified
inside, as `Liveness.CommitsAtRound` quantifies the universe and for the
same reason: the rotation names the round before any DAG is fixed, and
fixing one first would cap how far the rotation may reach. -/
def CommitsInViews (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    (T : Finset Validator) (R r : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ) (pc : Pace U T N),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    r + 2 ≤ N →
    ∃ L, IsAnchor U r L ∧ Committed U L r ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r

variable (Validator BlockId Payload) in
/-- **BMV1, no reliable validator is stuck.** BML4 says a round recurs
that the universe admits a commit at; this says a round recurs that
every reliable validator commits at, on its own view and by a time the
pace names. -/
def NoValidatorStuck : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    quorumCard Validator ≤ T.card → Liveness.FairRun T 2 →
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ CommitsInViews BlockId Payload T R r'

/-- **What it means for a round to deliver, at every reliable view, what
some view committed below.** -/
def DeliversInViews (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    (T : Finset Validator) (R ρ r : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ) (pc : Pace U T N)
    (V : View Validator BlockId Payload U) (A B : BlockId),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    r + 2 ≤ N →
    CommittedIn U V A ρ → B ∈ history U A →
    ∃ L, IsAnchor U r L ∧ B ∈ history U L ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r

variable (Validator BlockId Payload) in
/-- **BMV2, nothing one validator delivered is held back from another.**
BMA3 asks for a reliably anchored round above `ρ`; the rotation supplies
one, so the hypothesis becomes a conclusion. -/
def NothingHeldBack : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ),
    quorumCard Validator ≤ T.card → Liveness.FairRun T 2 →
    ∃ r, ρ ≤ r ∧ R ≤ r ∧ DeliversInViews BlockId Payload T R ρ r

/-- **BMV3, the rule is readable at a reliable anchor.** Past the round
coverage takes hold, an anchor whose author is reliable is referenced by
every reliable block of the round above, so a view holding those sees
the quorum with no block a Byzantine validator might withhold — the
boundary of the arc, since coverage constrains only `T`-authored
blocks. -/
def ReadableAtReliableAnchor (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ) (V : View Validator BlockId Payload U) (L : BlockId),
    quorumCard Validator ≤ T.card →
    SynchronisedOn U T R → R ≤ ρ → PopulatedOn U T (ρ + 1) →
    Rot.anchor ρ ∈ T → IsAnchor U ρ L →
    (∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = ρ + 1 → b ∈ V.ids) →
    SupportedIn U V L ρ

/-- Liveness of the Black Marlin commit rule read at a validator's view,
over every fault configuration, rotation and block universe the model
admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator],
    NoValidatorStuck Validator BlockId Payload ∧
      NothingHeldBack Validator BlockId Payload ∧
      ∀ (U : BlockUniverse Validator BlockId Payload), ReadableAtReliableAnchor U

end ViewLiveness

end BlackMarlin

end LeanDag
