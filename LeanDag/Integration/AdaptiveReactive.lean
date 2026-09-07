import LeanDag.Adaptive.Mysticeti
import LeanDag.Reactive.MysticetiProperties
/-!
# Adaptive leaders over reactive Mysticeti

`docs/target-properties.md` §4. The first result the schedule family
produces that the bespoke development did not have: Hammerhead-style
adaptive leaders over the *reactive* Mysticeti execution.

Safety is `adaptiveRun_agree` unchanged — the rule is the core's, and
the reactive discipline changes no verdict. Liveness is the generic
`Adaptive.run_exists` fed with `leaderCommits_reactive` in place of the
timed `leaderCommits`; nothing else moves. The precondition is staged,
as the generic theorem states it: at every height `E`, the reactive
clauses hold under the schedule the policy computes from a height-`E`
partial run's verdicts, over the slots `[W, W·(E+2))` that schedule has
determined. Any two height-`E` runs compute the same leaders there
(`partialRun_agree` and `adapted`), so the hypothesis names one
schedule prefix per height — the one the validators followed.
-/

namespace LeanDag

namespace Integration

open Properties MysticetiProperties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {P : AdaptivePolicy Validator BlockId Payload} {T : Finset Validator} {c : ℕ}

/-- **Partial runs exist at every height, reactively.** -/
theorem exists_partialRun_reactive (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U) (E : ℕ)
    (hlive : ∀ (E' : ℕ), E' < E → ∀ (A : PartialRun P U V E'),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E' + 2))) :
    Nonempty (PartialRun P U V E) :=
  Adaptive.exists_partialRun leaderCommits_reactive
    (Adaptive.descends_slotsOf indirect hc hspans P.inj) hruns V E hlive

/-- **The adaptive fixpoint exists over reactive Mysticeti.** Under a
policy that places runs, with the reactive clauses holding at every
height under the schedule that height computes, a total adaptive run
exists; with `adaptiveRun_agree` it is unique. -/
theorem adaptiveRun_exists_reactive (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U)
    (hlive : ∀ (E : ℕ) (A : PartialRun P U V E),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E + 2))) :
    Nonempty (AdaptiveRun P U V) :=
  Adaptive.run_exists agree leaderCommits_reactive
    (Adaptive.descends_slotsOf indirect hc hspans P.inj) hruns V hlive

/-- **Reliable-led slots commit, reactively.** In any run, a slot past
the first epoch led by a member of `T` commits, under the staged
reactive precondition. -/
theorem adaptiveRun_commits_reactive (V : View Validator BlockId Payload U)
    (A : AdaptiveRun P U V)
    (hlive : ∀ (E : ℕ) (A' : PartialRun P U V E),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A'.vdct m)) V T P.W (P.W * (E + 2)))
    {k : ℕ} (hk : P.W ≤ k) (hlead : A.assign k ∈ T) : ∃ L, A.vdct k = some L := by
  have hlt : k < P.W * (epochOf P.W k + 2) := by
    have := (epochOf_lt_iff P.W_pos).mp (show epochOf P.W k < epochOf P.W k + 2 by omega)
    exact this
  exact Adaptive.Run.commits agree leaderCommits_reactive A
    (Adaptive.Run.live_of_staged (Live := fun S {U} V T lo K => reactiveLive S (U := U) V T lo K)
      A hlive (epochOf P.W k)) hk hlt hlead

end Integration

end LeanDag
