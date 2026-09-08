import LeanDag.OptimalHydrozoan.Model.Faults
import LeanDag.Hydrozoan.ThresholdArithmetic.Statement
/-!
# Optimal-Hydrozoan: threshold arithmetic — statement

The rows of `lem:opt-thresholds`, one definition per row. Three
(`CertUniqueness`, `AnchorSeesSlow`, `SlowCollectible`) are Hydrozoan's,
unchanged; three (`CertFastExclusion`, `EvidencePlain`, `EvidenceEquiv`)
replace Hydrozoan's weak-rung rows; `FastUniqueness` is Hydrozoan's
re-stated over `qFastOpt` with the paper's `f ≥ 1` guard. Rows with
subtraction are restated subtraction-free (`a − b ≥ c` as `a ≥ b + c`),
so truncation cannot distort them.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace ThresholdArithmetic

variable (Replica : Type*) [Fintype Replica] [DecidableEq Replica]
  [O : OptimalFaults Replica]

/-- **A fast commit starves every conflicting certificate**,
`q_cert + q_fast > n + f` (row 2): the two quorums overlap in a
non-Byzantine replica, which is also what makes `q_cert` slotBlames
exclude a fast commit. -/
def CertFastExclusion : Prop :=
  Fintype.card Replica + O.f < qCert Replica + qFastOpt Replica

/-- **Fast evidence without an exposed equivocation**, row 5: the
paper's identity `q_fast + q − n − f = t_plain`, stated subtraction-free
as `q_fast + q = n + f + t_plain` with `t_plain ≥ 1` — the equality is
also the truncation guard on `tPlain`. -/
def EvidencePlain : Prop :=
  qFastOpt Replica + q Replica = Fintype.card Replica + O.f + tPlain Replica ∧
    1 ≤ tPlain Replica

/-- **Fast evidence with an exposed equivocation**, row 6: subtraction-free
as `n + f + t_equiv ≤ q_fast + q + 1`. The `+ 1` is the leader-exclusion
dividend — a witnessing block excludes the leader, so at most `f − 1` of
its refs are undetected Byzantine. -/
def EvidenceEquiv : Prop :=
  Fintype.card Replica + O.f + tEquiv Replica ≤ qFastOpt Replica + q Replica + 1

/-- **No two conflicting fast commits**, `2·q_fast > n + f`, guarded by
`f ≥ 1`: two fast quorums overlap in a non-Byzantine replica. The guard
is necessary — at `f = 0` the row can fail
(`fourCrashOnlySlack`) — and `1 ≤ f` is the paper's exact form; a
silently stronger guard would still pass every witness, since a
weakening of a true row is invisible to `decide`. -/
def FastUniqueness : Prop :=
  1 ≤ O.f → Fintype.card Replica + O.f < 2 * qFastOpt Replica

/-- The full table of `lem:opt-thresholds`: Hydrozoan's rows 1, 3, 4
inherited, plus the four Optimal rows. -/
def Statement : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica] [OptimalFaults Replica],
    Hydrozoan.ThresholdArithmetic.CertUniqueness Replica ∧
      Hydrozoan.ThresholdArithmetic.AnchorSeesSlow Replica ∧
      Hydrozoan.ThresholdArithmetic.SlowCollectible Replica ∧
      CertFastExclusion Replica ∧ EvidencePlain Replica ∧
      EvidenceEquiv Replica ∧ FastUniqueness Replica

end ThresholdArithmetic

end OptimalHydrozoan

end LeanDag
