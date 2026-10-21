import LeanDag.Node.Storage.Statement
import LeanDag.Node.Helpers.Storage
/-!
# Rate limiting bounds what a node holds — proof

The storage invariant `Lim` holds of the initial state and every step
keeps it (`Lim.run`); a state it holds of is bounded (`Lim.bound`).
-/

namespace LeanDag

namespace Node

namespace Storage

theorem bounded : Bounded := by
  intro Validator BlockId Payload _ _ _ cfg is ρ W hl
  exact (Lim.run hl is Lim.init).bound

theorem holds : Statement := bounded

end Storage

end Node

end LeanDag
