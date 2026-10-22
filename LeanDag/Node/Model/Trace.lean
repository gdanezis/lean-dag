import LeanDag.Node.Model.Run
/-!
# Many honest nodes over one trace

`docs/validator.md` §4. The nodes share one configuration but for their
identity (`Config.at`). A trace lists every node's inputs in the order
they occur; what the inputs are, and in what order they arrive, is the
network's and the adversary's. Node `v`'s state before event `i` is its
run over its inputs among the first `i` events (`stateBefore`); the
outputs of event `i` are its node's step there (`outputsAt`); node `v`'s
run over the whole trace is `runOf`, and what it knew `knownOf`; and an
output sends a message to other nodes (`Sends`): a broadcast block to
every other node, a request for blocks and a block sent to the node it
names.

Definitions only; the claims over traces are `Node/Runs/Statement.lean`,
`Node/Converge/Statement.lean` and `Node/Live/Statement.lean`.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (Validator BlockId Payload) in
/-- **A trace**: every node's inputs, in the order they occur. -/
abbrev Trace := List (Validator × Input Validator BlockId Payload)

/-- Node `v`'s inputs among the first `i` events. -/
def inputsBefore (tr : Trace Validator BlockId Payload) (i : ℕ) (v : Validator) :
    List (Input Validator BlockId Payload) :=
  (tr.take i).filterMap fun e => if e.1 = v then some e.2 else none

variable (cfg : Config Validator BlockId Payload)

/-- The configuration of node `v`. -/
def Config.at (v : Validator) : Config Validator BlockId Payload := { cfg with me := v }

/-- **Node `v`'s state before event `i`.** -/
def stateBefore (tr : Trace Validator BlockId Payload) (i : ℕ) (v : Validator) :
    State Validator BlockId Payload :=
  (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).1

/-- **The outputs of event `i`**: its node's step there. -/
def outputsAt (tr : Trace Validator BlockId Payload) (i : ℕ) :
    List (Output Validator BlockId Payload) :=
  match tr[i]? with
  | some (v, inp) => (step (cfg.at v) (stateBefore cfg tr i v) inp).2
  | none => []

/-- **Node `v`'s run** over the whole trace. -/
def runOf (tr : Trace Validator BlockId Payload) (v : Validator) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr tr.length v)

/-- What node `v` knew over the trace: the blocks delivered to it with
their hash, and its own. -/
def knownOf (tr : Trace Validator BlockId Payload) (v : Validator) :
    List (BlockId × Block Validator BlockId Payload) :=
  delivered (cfg.at v) (inputsBefore tr tr.length v) ++ persists (runOf cfg tr v).2

/-- **The decisions node `v` output** over the trace. -/
def decisionsOf (tr : Trace Validator BlockId Payload) (v : Validator) : List (ℕ × Option BlockId) :=
  commitsOf (runOf cfg tr v).2

/-- **What node `u`'s outputs send**: a broadcast block to every other
node, a request for blocks and a block sent to the node it names. -/
def Sends (u : Validator) (out : List (Output Validator BlockId Payload))
    (m : Validator × Input Validator BlockId Payload) : Prop :=
  ∃ o ∈ out, match o with
    | .broadcast id b => m.1 ≠ u ∧ m.2 = .deliver id b
    | .fetch peer r ids => m.1 = peer ∧ m.2 = .fetchRequest u r ids
    | .send peer id b => m.1 = peer ∧ m.2 = .deliver id b
    | _ => False

end Node

end LeanDag
