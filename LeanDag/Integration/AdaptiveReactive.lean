import LeanDag.Integration.AdaptiveMysticeti
import LeanDag.Reactive.MysticetiProperties
/-!
# Adaptive leaders over reactive Mysticeti

`docs/target-properties.md` §4: Hammerhead-style adaptive leaders over
the reactive Mysticeti execution. Safety is `adaptiveRun_agree`
unchanged, since the rule is the core's and the reactive discipline
changes no verdict. Liveness is the generic `Adaptive.run_exists` fed
with `leaderCommits_reactive` in place of the timed `leaderCommits`,
staged at every height over the schedule that height's partial run
computes.
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

/-- **Partial runs exist at every height, reactively.** The core's
staged theorem, with the reactive bridge supplying its precondition. -/
theorem exists_partialRun_reactive (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U) (E : ℕ)
    (hlive : ∀ (E' : ℕ), E' < E → ∀ (A : PartialRun P U V E'),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E' + 2))) :
    Nonempty (PartialRun P U V E) :=
  exists_partialRun hc hruns hspans V E
    fun E' hE' A => coreSupport_live_of_reactiveLive (hlive E' hE' A)

/-- **The adaptive fixpoint exists over reactive Mysticeti.** -/
theorem adaptiveRun_exists_reactive (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (V : View Validator BlockId Payload U)
    (hlive : ∀ (E : ℕ) (A : PartialRun P U V E),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E + 2))) :
    Nonempty (AdaptiveRun P U V) :=
  adaptiveRun_exists hc hruns hspans V
    fun E A => coreSupport_live_of_reactiveLive (hlive E A)

/-- **Reliable-led slots commit, reactively.** -/
theorem adaptiveRun_commits_reactive (V : View Validator BlockId Payload U)
    (A : AdaptiveRun P U V)
    (hlive : ∀ (E : ℕ) (A' : PartialRun P U V E),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A'.vdct m)) V T P.W (P.W * (E + 2)))
    {k : ℕ} (hk : P.W ≤ k) (hlead : A.assign k ∈ T) : ∃ L, A.vdct k = some L := by
  have hlt : k < P.W * (epochOf P.W k + 2) :=
    (epochOf_lt_iff P.W_pos).mp (show epochOf P.W k < epochOf P.W k + 2 by omega)
  refine adaptiveRun_commits A hk hlt ?_ hlead
  exact coreSupport_live_of_reactiveLive
    (Adaptive.Run.live_of_staged (Live := fun S {U} V T lo K => reactiveLive S (U := U) V T lo K)
      A hlive (epochOf P.W k))

end Integration

end LeanDag
