import LeanDag.Node.Model.Step
/-!
# An honest node — over a sequence of inputs

`run cfg s is` feeds the inputs `is` to the node in turn and collects its
outputs. `persists` reads the node's own blocks among the outputs,
`broadcasts` those it sent, and `delivered` the blocks delivered among
the inputs whose identifier is their hash: together, what the node
knew. `isQuiet` marks the outputs that neither persist nor
broadcast a block.

`commitsOf` reads the decisions among the outputs. Many nodes run over
one trace (`Model/Trace.lean`).

Definitions only; the claims are `Node/Local/Statement.lean`.
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

/-- The blocks among some inputs, delivered or streamed, whose identifier
is their hash. -/
def delivered (is : List (Input Validator BlockId Payload)) :
    List (BlockId × Block Validator BlockId Payload) :=
  is.flatMap fun
    | .deliver _ id b => if id = cfg.idOf b then [(id, b)] else []
    | .stream _ L => L.filter fun e => decide (e.1 = cfg.idOf e.2)
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

/-- **An output that neither persists nor broadcasts a block.** -/
def Output.isQuiet : Output Validator BlockId Payload → Bool
  | .persist _ _ => false
  | .broadcast _ _ => false
  | _ => true

/-- The decisions among some outputs. -/
def commitsOf (out : List (Output Validator BlockId Payload)) : List (ℕ × Option BlockId) :=
  out.filterMap fun
    | .commit k d => some (k, d)
    | _ => none

end Node

end LeanDag
