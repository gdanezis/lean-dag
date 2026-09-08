import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Replicas, hybrid faults, and thresholds

The fault model and the five thresholds of the hybrid model: `n ≥ 3f +
2c + k + 1` replicas, at most `f` Byzantine (may equivocate), at most `c`
crashed (never equivocate, but not counted on), `k` a tunable slack
widening the fast path. `p = ⌊(c + k)/2⌋` is derived, never an input, so
a too-large `p` is unrepresentable rather than assumed away. Definitions
only; lemmas live in `Helpers/`.
-/

namespace LeanDag

namespace Hydrozoan

/-- The hybrid fault model: `n ≥ 3f + 2c + k + 1` replicas, at most `f`
Byzantine, at most `c` crashed, `k` a tunable slack widening the fast path.

The `byzantine` and `crashed` sets are the *actual* fault assignment of a
run; the bounds `f` and `c` are what the protocol is configured to
tolerate. -/
class Faults (Replica : Type*) [Fintype Replica] [DecidableEq Replica] where
  /-- The Byzantine fault bound. -/
  f : ℕ
  /-- The crash fault bound. -/
  c : ℕ
  /-- The slack parameter. -/
  k : ℕ
  /-- The Byzantine replicas: may deviate arbitrarily, in particular
  equivocate. -/
  byzantine : Finset Replica
  /-- The crashed replicas: follow the protocol but may halt; they never
  equivocate. -/
  crashed : Finset Replica
  /-- No replica is both Byzantine and crashed. -/
  byzantine_disjoint_crashed : Disjoint byzantine crashed
  /-- There are at least `3f + 2c + k + 1` replicas. -/
  card_replicas : 3 * f + 2 * c + k + 1 ≤ Fintype.card Replica
  /-- At most `f` replicas are Byzantine. -/
  card_byzantine : byzantine.card ≤ f
  /-- At most `c` replicas are crashed. -/
  card_crashed : crashed.card ≤ c

section Thresholds

variable (Replica : Type*) [Fintype Replica] [DecidableEq Replica] [F : LeanDag.Hydrozoan.Faults Replica]

/-- `p = ⌊(c + k)/2⌋` — the fast path's fault allowance. Derived from `c`
and `k` (ℕ division is floor division), never an input. -/
def p : ℕ := (F.c + F.k) / 2

/-- `q = n − f − c`: the DAG quorum governing round advancement and the
number of refs each block references (`q` in the paper). -/
def q : ℕ := Fintype.card Replica - F.f - F.c

/-- `q_fast = n − p`: the quorum of votes at the voting round to
fast-commit a leader; also the quorum of slotBlames to directly skip it. -/
def qFast : ℕ := Fintype.card Replica - p Replica

/-- `q_cert = ⌈(n + f + 1)/2⌉`: the quorum of votes a decision-round block
must reference to count as a certificate, written as the smallest strict
majority of `n + f` so that `2 · q_cert > n + f` is immediate. -/
def qCert : ℕ := (Fintype.card Replica + F.f) / 2 + 1

/-- `q_slow = 2f + c + 1`: the quorum of certificates at the decision
round to (slow) direct-commit a leader. -/
def qSlow : ℕ := 2 * F.f + F.c + 1

/-- `q_weak = f + p + 1`: the quorum of anchor-linked votes to indirectly
commit a leader — the second rung of the graded indirect rule. -/
def qWeak : ℕ := F.f + p Replica + 1

end Thresholds

section Pools

variable {Replica : Type*} [Fintype Replica] [DecidableEq Replica] [F : LeanDag.Hydrozoan.Faults Replica]

/-- The correct replicas: neither Byzantine nor crashed. The pool that
availability and liveness arguments count. -/
def Correct : Finset Replica := (F.byzantine ∪ F.crashed)ᶜ

/-- The non-Byzantine replicas: correct or crashed — every replica that
never equivocates. The pool that uniqueness arguments count. -/
def NonByzantine : Finset Replica := F.byzantineᶜ

end Pools

end Hydrozoan

end LeanDag
