import LeanDag.Hydrozoan.Model.Faults
/-!
# Optimal-Hydrozoan: fault model and thresholds

`OptimalFaults` extends Hydrozoan's `Faults` with one field; `q`,
`qCert`, `qSlow`, `Correct` and `NonByzantine` are inherited unchanged.
The fast-path allowance becomes `pOpt = ⌊(c+k)/2⌋ + 1`, one fault more
than Hydrozoan tolerates; `q_weak` is replaced by two per-block
thresholds, `tPlain` and `tEquiv`, on the votes a single decision-round
block references. Definitions only; lemmas live in `Helpers/`.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

/-- Hydrozoan's `Faults`, plus the standing assumption `f + c ≥ 1`: at
`f = c = 0` the threshold arithmetic is not guaranteed (it fails at
`n = 1`), so the case is excluded here rather than assumed away in every
statement. -/
class OptimalFaults (Replica : Type*) [Fintype Replica] [DecidableEq Replica]
    extends LeanDag.Hydrozoan.Faults Replica where
  /-- The fault model is non-trivial: at least one fault of some kind is
  tolerated (`f + c ≥ 1`). -/
  nontrivial : 1 ≤ f + c

section Thresholds

variable (Replica : Type*) [Fintype Replica] [DecidableEq Replica]
  [O : OptimalFaults Replica]

/-- `pOpt = ⌊(c+k)/2⌋ + 1`: the fast path's fault allowance, one more
than Hydrozoan's `p`, defined through it. -/
def pOpt : ℕ := p Replica + 1

/-- `q_fast = n − pOpt`: the quorum of votes at the voting round to
fast-commit a leader, one fewer than Hydrozoan's at the same committee
size. Unlike Hydrozoan, this is not the direct skip's blame quorum,
which becomes `q_cert`. -/
def qFastOpt : ℕ := Fintype.card Replica - pOpt Replica

/-- `t_plain = n − 2f − c − pOpt`: the votes for a leader block a
decision-round block must reference to be fast evidence for it, absent
an equivocation witness. A truncated ℕ subtraction on purpose: the
arithmetic phase's identity `q_fast + q = n + f + t_plain` fails under
truncation, so proving it also certifies none occurred. -/
def tPlain : ℕ := Fintype.card Replica - (2 * O.f + O.c + pOpt Replica)

/-- `t_equiv = f + pOpt`: the same threshold when the decision-round block
witnesses an equivocation of the leader — it must then reference at
least `t_equiv` votes for the candidate and fewer than `t_equiv` for
every conflicting block (`IsFastEvidence`, second case; O4). -/
def tEquiv : ℕ := O.f + pOpt Replica

end Thresholds

end OptimalHydrozoan

end LeanDag
