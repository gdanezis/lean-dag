import LeanDag.Node.Model.Run
/-!
# Rate limiting bounds what a node holds — statement

`docs/validator.md` §3.9, V10. With a budget `τ` and a window `W` in the
configuration, over any sequence of inputs from the initial state, so
under any adversary:

* every block the node holds, in its store or pending, is charged to a
  candidate slot, so the blocks held number at most the charges;
* the charges number at most `n·(τ + 1)` a round, over the rounds from
  the horizon to `W` above the top (`Bounded`).

Statements only; the proof is `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Storage

/-- **The blocks a node holds**: its store's and its pending ones, by
identifier. -/
def held {Validator BlockId Payload : Type} [LinearOrder BlockId]
    (s : State Validator BlockId Payload) : Finset BlockId :=
  s.store.ids ∪ (s.pending.map Prod.fst).toFinset

/-- **The storage bound**: with rate limiting, the blocks a node holds
number at most its charges, and its charges at most `n·(τ + 1)` a round
from its horizon to `W` above its top. -/
def Bounded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)) (τ W : ℕ), cfg.limit = some (τ, W) →
    let s := (run cfg (State.init cfg) is).1
    (held s).card ≤ s.owner.length ∧
      s.owner.length ≤ Fintype.card Validator * (τ + 1) * (s.top.getD 0 + W + 1 - s.store.base)

/-- Storage under rate limiting. -/
def Statement : Prop := Bounded

end Storage

end Node

end LeanDag
