import LeanDag.Hydrozoan.Model.Faults
/-!
# Threshold arithmetic — statement

The six slack-cap inequalities the two-protocol consistency argument
rests on, one definition per table row, stated over an arbitrary
`Faults` instance and claimed for every `k ≥ 0` the class admits — no
cap on the slack is assumed. Rows with subtraction are restated
subtraction-free (`a − b ≥ c` as `a ≥ b + c`) against truncation.
-/

namespace LeanDag

namespace Hydrozoan

namespace ThresholdArithmetic

variable (Replica : Type*) [Fintype Replica] [DecidableEq Replica] [F : LeanDag.Hydrozoan.Faults Replica]

/-- **Certificate uniqueness**, `2·q_cert > n + f`: two certificate vote
sets must overlap in a non-Byzantine replica, so no two conflicting blocks
are both certified in the same slot. -/
def CertUniqueness : Prop :=
  Fintype.card Replica + F.f < 2 * qCert Replica

/-- **No two conflicting fast commits**, `2·q_fast > n + f`: two fast
quorums must overlap in a non-Byzantine replica, so no two conflicting
leaders are both fast-committed. -/
def FastUniqueness : Prop :=
  Fintype.card Replica + F.f < 2 * qFast Replica

/-- **A fast commit starves conflicts below the weak rung**,
`q_fast + q_weak > n + f`: a conflicting candidate's support falls
strictly below `q_weak`, so the graded indirect rule can never
resurrect it. -/
def FastStarvation : Prop :=
  Fintype.card Replica + F.f < qFast Replica + qWeak Replica

/-- **The slow path is collectible**, `q_cert ≤ q`: a decision-round block
references `q` refs, so a certificate's `q_cert` votes fit among them —
the certificate threshold never outruns what a single block can carry. -/
def SlowCollectible : Prop :=
  qCert Replica ≤ q Replica

/-- **An anchor sees any slow commit**, `q + q_slow > n + f` (the note's
identity `Q + SLOW = n + f + 1`): an anchor's `q` refs meet the
`q_slow` certificates of any slow commit in a non-Byzantine replica. -/
def AnchorSeesSlow : Prop :=
  Fintype.card Replica + F.f < q Replica + qSlow Replica

/-- **An anchor sees the fast footprint**: a fast quorum and an anchor's
parent set always intersect in at least `q_weak` replicas, so a
fast-committed leader's anchor always reaches the weak rung and can
never indirect-skip it. Stated subtraction-free as
`n + q_weak ≤ q_fast + q`. -/
def AnchorSeesFast : Prop :=
  Fintype.card Replica + qWeak Replica ≤ qFast Replica + q Replica

/-- The full slack-cap table, for every fault configuration the model
admits — no analogue of Hydrangea's Theorem 1 slack cap is assumed. -/
def Statement : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica] [LeanDag.Hydrozoan.Faults Replica],
    CertUniqueness Replica ∧ FastUniqueness Replica ∧ FastStarvation Replica ∧
      SlowCollectible Replica ∧ AnchorSeesSlow Replica ∧ AnchorSeesFast Replica

end ThresholdArithmetic

end Hydrozoan

end LeanDag
