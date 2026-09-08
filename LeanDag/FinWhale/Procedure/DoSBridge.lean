import LeanDag.FinWhale.Procedure.Protocol
import LeanDag.FinWhale.DoSBridge
import LeanDag.FinWhale.Reactive
import LeanDag.DoS.Exposure
/-!
# FinWhale — a Run over a DoS-valid universe

Procedure side: a `Run` collects an execution and the verdicts the
reverse pass gives it, so these constructors go with the pass.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- **A run over a DoS-valid universe**: the same data a `Run` asks for,
less three fields the identification with the universe discharges. -/
def Run.ofDoSValid [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (leader : ℕ → Validator) (hdos : DoSValid U)
    (horizon : ℕ) (rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ horizon)
    (paceHorizon : ℕ) (pace : PaceCore U (Correct : Finset Validator) paceHorizon)
    (rounds_advance : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pace.top u, n ≤ pace.built u n)
    (stable : ℕ) (gst_le : pace.gst ≤ stable) (liveHorizon : ℕ)
    (commits : CommitsCorrectLeaders (Slots.identity leader) (Dag.ofDoSValid U leader hdos)
      stable liveHorizon)
    (live_le : liveHorizon ≤ paceHorizon) (roundRobin : RoundRobin leader) :
    Run Validator BlockId Payload where
  dag := Dag.ofDoSValid U leader hdos
  sched := (Slots.identity leader)
  roundId := fun _ => rfl
  paced := U
  ids_eq := rfl
  block_eq := rfl
  horizon := horizon
  rounds_le := rounds_le
  paceHorizon := paceHorizon
  pace := pace
  rounds_advance := rounds_advance
  stable := stable
  gst_le := gst_le
  liveHorizon := liveHorizon
  commits := commits
  live_le := live_le
  roundRobin := roundRobin
  selfParented := selfParented_ofDoSValid hdos

/-! ## A reactive deployment over a DoS-protected DAG

`Run.ofDoSValid` still needs the liveness input; this section supplies
it from the core's reactive schedule, whose two citation obligations
are both confined to reliable authors, so nothing it requires is
anything `DoSValid` forbids. -/

variable [S : Slots Validator]

omit P S in
/-- **A DoS-valid universe on the reactive schedule is a run**: the pace
is the reactive one and the liveness input is `commits_of_reactive`,
with four of `Run`'s fields discharged by identification with the
universe. -/
noncomputable def Run.ofDoSValidReactive [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (hdos : DoSValid U) {N : ℕ}
    (rm : ReactiveM U (Correct : Finset Validator) N)
    (hround : ∀ k, S.slotRound k = k) (hrr : RoundRobin S.leader)
    (horizon : ℕ) (rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ horizon)
    (rounds_advance : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ rm.top u,
      n ≤ rm.built u n)
    (stable : ℕ) (hgst : rm.gst ≤ stable)
    (hto : ∀ n, stable ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) :
    Run Validator BlockId Payload :=
  Run.ofDoSValid U S.leader hdos horizon rounds_le N rm.toPaceCore rounds_advance
    stable hgst N
    (commits_of_reactive rm rfl rfl hround (fun _ => rfl) (fun _ => rfl) rfl hgst hto)
    (le_refl N) hrr

end FinWhale

end LeanDag
