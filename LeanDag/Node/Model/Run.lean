import LeanDag.Node.Model.Step
/-!
# An honest node — over a sequence of inputs

`run cfg s is` feeds the inputs `is` to the node in turn and collects its
outputs. `persists` reads the node's own blocks among the outputs,
`broadcasts` those it sent, and `delivered` the blocks among the inputs,
delivered or offered, whose identifier is their hash: together, what
the node knew. `isFetch` marks the requests and answers that move blocks
without building one.

`commitsOf` reads the decisions among the outputs. Over many nodes,
`Config.at` is node `v`'s configuration, `runOf` its run and `knownOf`
what it knew.

Definitions only; the claims are `Node/Local/Statement.lean` and
`Node/Runs/Statement.lean`.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (cfg : Config Validator BlockId Payload)

/-- **The node over a sequence of inputs**: its last state and all its
outputs, in order. -/
def run : State Validator BlockId Payload → List (Input Validator BlockId Payload) →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | s, [] => (s, [])
  | s, i :: is =>
    let r := step cfg s i
    let r' := run r.1 is
    (r'.1, r.2 ++ r'.2)

/-- The blocks among some inputs, delivered or offered, whose identifier
is their hash. -/
def delivered (is : List (Input Validator BlockId Payload)) :
    List (BlockId × Block Validator BlockId Payload) :=
  is.flatMap fun
    | .deliver id b => if id = cfg.idOf b then [(id, b)] else []
    | .baseOffer _ _ bs => bs.filter fun e => decide (e.1 = cfg.idOf e.2)
    | _ => []

variable {cfg}

/-- The blocks among some outputs that the node persisted: its own. -/
def persists (out : List (Output Validator BlockId Payload)) :
    List (BlockId × Block Validator BlockId Payload) :=
  out.filterMap fun
    | .persist id b => some (id, b)
    | _ => none

/-- The blocks among some outputs that the node broadcast. -/
def broadcasts (out : List (Output Validator BlockId Payload)) :
    List (BlockId × Block Validator BlockId Payload) :=
  out.filterMap fun
    | .broadcast id b => some (id, b)
    | _ => none

/-- **An output that moves blocks between nodes without building one**:
a request or an answer. -/
def Output.isFetch : Output Validator BlockId Payload → Bool
  | .fetch _ => true
  | .send _ _ _ => true
  | .requestBase => true
  | .serveBase _ _ _ => true
  | _ => false

/-- The decisions among some outputs. -/
def commitsOf (out : List (Output Validator BlockId Payload)) : List (ℕ × Option BlockId) :=
  out.filterMap fun
    | .commit k d => some (k, d)
    | _ => none

/-! ## Many nodes

A run of many nodes gives each honest node its own sequence of inputs;
the nodes share one configuration but for their identity. What the
inputs are, and in what order they arrive, is the network's and the
adversary's; the claims about runs constrain it only by
authentication and by the hash. -/

variable (cfg) in
/-- The configuration of node `v`. -/
def Config.at (v : Validator) : Config Validator BlockId Payload := { cfg with me := v }

variable (cfg) in
/-- **Node `v`'s run**, from the initial state over its inputs. -/
def runOf (ins : Validator → List (Input Validator BlockId Payload)) (v : Validator) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  run (cfg.at v) (State.init (cfg.at v)) (ins v)

variable (cfg) in
/-- What node `v` knew: the blocks delivered or offered to it with their
hash, and its own. -/
def knownOf (ins : Validator → List (Input Validator BlockId Payload)) (v : Validator) :
    List (BlockId × Block Validator BlockId Payload) :=
  delivered (cfg.at v) (ins v) ++ persists (runOf cfg ins v).2

end Node

end LeanDag
