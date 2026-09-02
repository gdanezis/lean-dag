import LeanDag.Liveness
import LeanDag.Hydrozoan.EventualDecision.Statement
import LeanDag.Hydrozoan.IndirectLiveness.Statement

/-!
# B2 — the schedule bridge

`docs/hydrozoan-integration.md` §1 and §10.2. `LeanDag.Slots` and
`LeanDag.Hydrozoan.Slots` carry the same five fields —
`slotRound`, `leader`, `mono`, `unbounded`, `keyed` — so the
identification is field-for-field and every component is `rfl`.

**What it carries.** The integration arc's layer-S results are
functions of a `Slots` instance and nothing else (`integration.md`
§3.2), so they hold of a Hydrozoan schedule as soon as it is one. The
two schedule predicates the liveness capstones consume agree on the
nose: `FairRunOn` is the same quantifier in both, and `SpansEligible`
differs only in the name of the eligibility predicate, the core's
`Eligible` and Hydrozoan's `EligibleAsAnchor` both unfolding to
`decisionRound k < slotRound j`.

The wave arithmetic agrees for the same reason:
`Hydrozoan.decisionRound k` and `LeanDag.decisionRound k` are both
`slotRound k + 2`, which is what makes the wave-length-three
instantiation of `Barnacle.LiveRule.Descent` line up
(`Barnacle/HydrozoanLive/Statement.lean`).
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type*}

/-- **A Hydrozoan schedule is a schedule.** Every field by `rfl`. -/
instance toCoreSlots [S : LeanDag.Hydrozoan.Slots Replica] : LeanDag.Slots Replica where
  slotRound := S.slotRound
  leader := S.leader
  mono := S.mono
  unbounded := S.unbounded
  keyed := S.keyed

/-- The same identification read the other way, as a function rather
than an instance: a schedule the core produces — `Slots.chop`'s, in
particular — read back as Hydrozoan's. -/
@[reducible]
def ofCoreSlots (S : LeanDag.Slots Replica) : LeanDag.Hydrozoan.Slots Replica where
  slotRound := S.slotRound
  leader := S.leader
  mono := S.mono
  unbounded := S.unbounded
  keyed := S.keyed

section Agreements

variable [S : LeanDag.Hydrozoan.Slots Replica]

@[simp] theorem slotRound_eq (k : ℕ) :
    LeanDag.Slots.slotRound Replica k = S.slotRound k := rfl

@[simp] theorem leader_eq (k : ℕ) :
    LeanDag.Slots.leader (Validator := Replica) k = S.leader k := rfl

/-- The two decision rounds coincide, both being `slotRound k + 2`. -/
@[simp] theorem decisionRound_eq (k : ℕ) :
    LeanDag.decisionRound Replica k = LeanDag.Hydrozoan.decisionRound Replica k := rfl

/-- Anchor eligibility coincides: the core's `Eligible` and
Hydrozoan's `EligibleAsAnchor` are one predicate. -/
@[simp] theorem eligible_eq (k j : ℕ) :
    LeanDag.Eligible Replica k j ↔ LeanDag.Hydrozoan.EligibleAsAnchor Replica k j := Iff.rfl

/-- Run fairness coincides. -/
@[simp] theorem fairRunOn_eq (T : Finset Replica) (c : ℕ) :
    LeanDag.FairRunOn T c
      ↔ LeanDag.Hydrozoan.EventualDecision.FairRunOn Replica T c := Iff.rfl

/-- The run-shape condition coincides, by `eligible_eq`. -/
@[simp] theorem spansEligible_eq (c : ℕ) :
    LeanDag.SpansEligible (Validator := Replica) c
      ↔ LeanDag.Hydrozoan.IndirectLiveness.SpansEligible Replica c := Iff.rfl

end Agreements

end Hydrozoan

end Integration

end LeanDag
