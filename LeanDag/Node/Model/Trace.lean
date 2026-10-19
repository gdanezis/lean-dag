import LeanDag.Node.Model.Run
/-!
# Many honest nodes over one trace

`docs/validator.md` §3.7. A trace lists every node's inputs in the order
they occur. Node `v`'s state before event `i` is its run over its inputs
among the first `i` events (`stateBefore`); the outputs of event `i` are
its node's step there (`outputsAt`); and an output sends a message to
other nodes (`Sends`): a broadcast block and a request for blocks or for
the base to every other node, an answer or a base to the node it names.

Definitions only; the claims are `Node/Converge/Statement.lean`.
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

/-- **The decisions node `v` output** over the trace. -/
def decisionsOf (tr : Trace Validator BlockId Payload) (v : Validator) : List (ℕ × Option BlockId) :=
  commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr tr.length v)).2

/-- **What node `u`'s outputs send**: a broadcast block and a request for
blocks or for the base to every other node, an answer or a base to the
node it names. -/
def Sends (u : Validator) (out : List (Output Validator BlockId Payload))
    (m : Validator × Input Validator BlockId Payload) : Prop :=
  ∃ o ∈ out, match o with
    | .broadcast id b => m.1 ≠ u ∧ m.2 = .deliver id b
    | .requestBase => m.1 ≠ u ∧ m.2 = .baseRequest u
    | .serveBase peer G bs => m.1 = peer ∧ m.2 = .baseOffer u G bs
    | .fetch ids => m.1 ≠ u ∧ m.2 = .fetchRequest u ids
    | .send peer id b => m.1 = peer ∧ m.2 = .deliver id b
    | _ => False

end Node

end LeanDag
