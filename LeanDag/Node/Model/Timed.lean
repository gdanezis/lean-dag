import LeanDag.Node.Model.Trace
/-!
# Timed traces

`docs/validator.md` §5.1. A timed trace is a trace with a time for each
event (`time i` for event `i`). Read off it, for a node `v` and a time
`t`: the events at or before `t` (`eventsBy`), `v`'s state after them
(`stateAt`), its top round (`topAt`), and the decisions it output by
then (`decisionsBy`);
and the time at which `v` built its round-`n` block (`builtAt`), the time
of the event whose outputs persist it.

Definitions only; the claims are `Node/Live/Statement.lean`.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (cfg : Config Validator BlockId Payload) (tr : Trace Validator BlockId Payload)
  (time : ℕ → ℕ)

/-- **The events at or before `t`**, counted. -/
def eventsBy (t : ℕ) : ℕ := ((List.range tr.length).filter fun i => time i ≤ t).length

/-- **Node `v`'s state after the events at or before `t`.** -/
def stateAt (v : Validator) (t : ℕ) : State Validator BlockId Payload :=
  stateBefore cfg tr (eventsBy tr time t) v

/-- Node `v`'s top round at `t`, `0` before it starts. -/
def topAt (v : Validator) (t : ℕ) : ℕ := ((stateAt cfg tr time v t).top).getD 0

/-- **The decisions node `v` output by `t`.** -/
def decisionsBy (v : Validator) (t : ℕ) : List (ℕ × Option BlockId) :=
  commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr (eventsBy tr time t) v)).2

/-- **When node `v` built its round-`n` block**: the time of the first
event of `v` whose outputs persist a block of round `n`, `0` if none. -/
def builtAt (v : Validator) (n : ℕ) : ℕ :=
  match (List.range tr.length).find? (fun i => decide ((tr[i]?.map Prod.fst) = some v) &&
      (persists (outputsAt cfg tr i)).any (fun e => decide (e.2.round = n))) with
  | some i => time i
  | none => 0

end Node

end LeanDag
