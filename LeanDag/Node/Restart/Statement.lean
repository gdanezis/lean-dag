import LeanDag.Node.Model.Run
/-!
# A node across a crash — statement

`docs/validator.md` §5, V5. A crash keeps what the node persisted
(`State.persisted`): its accepted blocks from the horizon up, the
horizon, the next undecided slot and its own top block. At every state a
run reaches, **resuming from what was persisted gives the state the
restart input recovers** (`Resumes`): the same blocks, read alike, at the
same horizon, and the recovered state's next slot, top and own block, its
top round's timer fired, and nothing pending or asked for. The restart
input keeps the store as it is (`State.recover`), so the claims over
traces cover crashes as restart inputs. A crash falls between steps:
the node's storage writes the state a step leaves at once, before any of
its outputs takes effect.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Restart

/-- **Resuming gives the recovered state**, with its store rebuilt from
the persisted window and read alike. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let s := (run cfg (State.init cfg) is).1
    ∃ s', resume cfg s.persisted = some s' ∧
      s'.store.ids = s.store.ids ∧ s'.store.base = s.store.base ∧
      s'.store.junk = s.store.junk ∧
      (∀ j ∈ s.store.ids, s'.store.map.getD j s'.store.junk = s.store.map.getD j s.store.junk) ∧
      s' = { s.recover with store := s'.store }

/-- A node across a crash. -/
def Statement : Prop := Resumes

end Restart

end Node

end LeanDag
