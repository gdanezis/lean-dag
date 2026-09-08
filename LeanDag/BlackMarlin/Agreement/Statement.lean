import LeanDag.BlackMarlin.Model.Round
import LeanDag.BlackMarlin.Liveness.Statement
/-!
# Black Marlin — agreement, stated

Definition 1's **Agreement**: if an honest party delivers a block, every
honest party eventually delivers it (`black-marlin.md` §10). BMA1 is
no-divergence; BMA2 says a run of two reliable anchors is committed by
every reliable validator on its own view; BMA3 composes the two into
delivery agreement across validators; BMA4 supplies the growing round
BMA3 needs, from the rotation's fairness.

This is agreement on the delivered **set** — `B ∈ history U L` for the
anchor `L` each validator commits — not on the delivered sequence or on
the choice among an equivocator's twins, both of which the recursion and
the deterministic sort `τ` arbitrate elsewhere.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Agreement

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
  {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {N : ℕ}

/-- **BMA1, no divergence.** A block delivered with a committed anchor is
delivered with every committed anchor from that round on, whichever views
the two verdicts were reached from. -/
def Monotone (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (A₁ A₂ B : BlockId) (r₁ r₂ : ℕ),
    CommittedIn U V₁ A₁ r₁ → CommittedIn U V₂ A₂ r₂ → r₁ ≤ r₂ →
    B ∈ history U A₁ → B ∈ history U A₂

/-- **BMA2, the commit is local.** Past GST, with the timeout clearing
`2Δ + proc`, a run of two reliable anchors is committed by **every**
reliable validator on its own view — where the universe-level results
say a verdict is available, this says each validator reaches it. -/
def LocalCommit (pc : Pace U T N) : Prop :=
  ∀ (R r : ℕ),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    R ≤ r → r + 2 ≤ N →
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T →
    ∃ L, IsAnchor U r L ∧ Committed U L r ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r

/-- **BMA3, agreement.** What one validator delivered with an anchor
committed at round `ρ` — from any view, by any route — every reliable
validator delivers with the anchor it commits at a reliably anchored
round `r ≥ ρ`, on its own view and by an explicit time. -/
def Delivered (pc : Pace U T N) : Prop :=
  ∀ (R r ρ : ℕ) (V : View Validator BlockId Payload U) (A B : BlockId),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    R ≤ r → r + 2 ≤ N → ρ ≤ r →
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T →
    CommittedIn U V A ρ → B ∈ history U A →
    ∃ L, IsAnchor U r L ∧ B ∈ history U L ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r

variable (Validator) in
/-- **BMA4, the round BMA3 asks for recurs.** Under the fairness clause
the rotation puts a reliably anchored run of two above every round, so
the growth hypothesis of BMA3 is met by any DAG grown far enough rather
than assumed. This is `FairRun` at `c = 2`, read as the two rounds the
commit rule names. -/
def RunRecurs : Prop :=
  ∀ (T : Finset Validator) (r : ℕ), Liveness.FairRun T 2 →
    ∃ r', r ≤ r' ∧ Rot.anchor r' ∈ T ∧ Rot.anchor (r' + 1) ∈ T

/-- Agreement for the Black Marlin commit rule, over every fault
configuration, rotation, block universe and pacing structure the model
admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    Monotone U ∧ RunRecurs Validator ∧
      ∀ (T : Finset Validator) (N : ℕ) (pc : Pace U T N),
        LocalCommit pc ∧ Delivered pc

end Agreement

end BlackMarlin

end LeanDag
