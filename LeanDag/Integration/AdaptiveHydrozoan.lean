import LeanDag.Adaptive.Liveness
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Properties.Derived.Progress
/-!
# Adaptive leaders over Hydrozoan

`docs/target-properties.md` §4.5. The arc's thesis, at the point where
it pays: Hydrozoan and the adaptive-leader mechanism were developed
independently and never met, and this file marries them without either
one being told about the other.

Nothing is proved here that is not an application. Hydrozoan supplies
`Agree`, `Banded`, `LeaderCommits` and `Descends`; the mechanism
supplies `run_agree` and `run_exists` over any rule with those; and the
two theorems below are the composites. Safety needs `Agree` alone and
holds under no synchrony or fairness hypothesis whatever, for arbitrary
adapted policies. Liveness needs the other two, plus the policy clause
`PlacesRuns` that prices the reassignment.

**And progress survives a fill**, which is the other half of §11.4c:
`decidedBelow_of_run` says every slot below a reliable-led run has a
verdict, so a candidate the fill added to a slot nobody voted for is
disposed of by the anchored rule. Hydrozoan needs no direct skip for
that, and nothing in the argument mentions the fill.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable [S : LeanDag.Slots Replica]
variable {P : Adaptive.Policy (rule (Replica := Replica) (BlockId := BlockId))}
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {T : Finset Replica} {c : ℕ}

/-- **Safety: the adaptive fixpoint over Hydrozoan is unique.** Two
total runs on one universe, from any two views, hold the same verdicts
and run the same schedule — under no synchrony, fairness or population
hypothesis, and for any adapted policy, adversarial ones included. -/
theorem adaptiveRun_agree_hz {V₁ V₂ : LeanDag.Hydrozoan.View U}
    (A₁ : Adaptive.Run P U V₁) (A₂ : Adaptive.Run P U V₂) :
    (∀ k, A₁.vdct k = A₂.vdct k) ∧ (∀ m, A₁.assign m = A₂.assign m) :=
  Adaptive.run_agree LeanDag.Hydrozoan.agree A₁ A₂

/-- **Liveness: the adaptive fixpoint over Hydrozoan exists.** Under a
policy that places runs, with Hydrozoan's own liveness precondition
holding at every height under the schedule that height computes, a total
adaptive run exists. With the theorem above it is THE fixpoint. -/
theorem adaptiveRun_exists_hz (hc : 0 < c) (hruns : Adaptive.PlacesRuns P T c)
    (hspans : (LeanDag.Hydrozoan.hydrozoanAnchored Replica BlockId).SpansEligible (S := S) c)
    (V : LeanDag.Hydrozoan.View U)
    (hlive : ∀ (E : ℕ) (A : Adaptive.PartialRun P U V E),
      LeanDag.Hydrozoan.hzLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T
        P.W (P.W * (E + 2))) :
    Nonempty (Adaptive.Run P U V) :=
  Adaptive.run_exists LeanDag.Hydrozoan.agree LeanDag.Hydrozoan.leaderCommits
    (Adaptive.descends_slotsOf LeanDag.Hydrozoan.indirect hc hspans P.inj)
    hruns V hlive

/-- **Progress survives whatever a mechanism adds.** Every slot below a
run of `c` reliable-led slots has a verdict, so a candidate a fill put
on a slot that nobody voted for does not stall Hydrozoan: the anchored
rule disposes of it. No direct skip is needed, and the fill is not
mentioned. -/
theorem decidedBelow_of_run_hz {c : ℕ} (hc : 0 < c)
    (hspans : (LeanDag.Hydrozoan.hydrozoanAnchored Replica BlockId).SpansEligible (S := S) c)
    (V : LeanDag.Hydrozoan.View U) (b : ℕ)
    (hlive : LeanDag.Hydrozoan.hzLive S V T b (b + c))
    (hlead : ∀ i, i < c → S.leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ v, DecidedBelow (rule (Replica := Replica) (BlockId := BlockId))
      S (b + c) V i v :=
  decidedBelow_of_run LeanDag.Hydrozoan.leaderCommits
    (LeanDag.Hydrozoan.descends hc hspans) V T b hlive hlead

end Integration

end LeanDag
