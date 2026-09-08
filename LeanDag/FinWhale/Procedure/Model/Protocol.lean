import LeanDag.FinWhale.Model.Liveness
import LeanDag.FinWhale.Model.Schedule
import LeanDag.FinWhale.Procedure.Model.Verdict
/-!
# FinWhale — one execution, and what a validator reads off it

`Run` collects everything a deployment fixes — the blocks, the schedule
and network that carried them, the rotation, the self-parent edge, and
the liveness input — so that the four guarantees stated over it need not
mention a verdict assignment, a view, or a well-formedness condition.
`Run.view` is what a validator holds once the network has delivered
every reliable block the schedule reaches; `Run.verdicts` and
`Run.delivers` sit in `Protocol.lean` beside the proof they need.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type}

/-- **A run of FinWhale.** The blocks every correct validator ever holds,
the schedule and network that carried them, and the rotation that names
leaders. -/
structure Run (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Params Validator] [DecidableEq BlockId] [LinearOrder BlockId] where
  /-- Every block any correct validator holds. -/
  dag : Dag Validator BlockId Payload
  /-- The same blocks, as the pacing line reads them. -/
  paced : BlockUniverse Validator BlockId Payload
  /-- The two readings describe the same blocks. -/
  ids_eq : dag.ids = paced.ids
  /-- And denote them the same way. -/
  block_eq : dag.block = paced.block
  /-- No block sits above this round. -/
  horizon : ℕ
  /-- Which is a horizon. -/
  rounds_le : ∀ b ∈ dag.ids, (dag.block b).round ≤ horizon
  /-- The rounds the schedule reaches. -/
  paceHorizon : ℕ
  /-- The schedule and the network. -/
  pace : PaceCore paced (Correct : Finset Validator) paceHorizon
  /-- Rounds advance real time. -/
  rounds_advance : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pace.top u, n ≤ pace.built u n
  /-- The leader schedule the execution runs. It belongs to the
  execution rather than to the DAG: a DAG is blocks, and a schedule is
  not. -/
  sched : Slots Validator
  /-- FinWhale runs one slot per round, which is what the reverse pass
  enumerates. -/
  roundId : ∀ k, sched.slotRound k = k
  /-- The network has stabilised by this round. -/
  stable : ℕ
  /-- Which is past GST. -/
  gst_le : pace.gst ≤ stable
  /-- Below this round the liveness argument applies. -/
  liveHorizon : ℕ
  /-- Every correct-led slot below it carries a commit — the input §10
  supplies, by either route. -/
  commits : CommitsCorrectLeaders sched dag stable liveHorizon
  /-- The schedule reaches that far. -/
  live_le : liveHorizon ≤ paceHorizon
  /-- Leaders rotate. -/
  roundRobin : RoundRobin sched.leader
  /-- Every block references its author's previous block. -/
  selfParented : SelfParented dag

namespace Run

variable (run : Run Validator BlockId Payload) {v w : Validator}

/-- **What a validator holds**, once the network has delivered every
reliable block of every round the schedule reaches. -/
def view (v : Validator) : Finset BlockId := run.pace.holds v (settled run.pace)

end Run

end FinWhale

end LeanDag
