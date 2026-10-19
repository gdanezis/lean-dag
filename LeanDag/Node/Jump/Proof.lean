import LeanDag.Node.Jump.Statement
import LeanDag.Node.Helpers.Jumps
/-!
# Safe Skip — proof

A derived block is one the jump message denotes on the receiver's store,
the message one the sender sent, and the blocks it denotes on the
sender's store its own; the two stores hold what the two nodes knew, so
under the hash they read alike above the sender's last block and denote
the same blocks (`derived_persisted`).
-/

namespace LeanDag

namespace Node

namespace Jump

theorem derives : Derives := by
  intro Validator BlockId Payload _ _ _ cfg H ins hJ hinj v hv x hx hc
  exact derived_persisted hJ hinj hv hx hc

theorem holds : Statement := derives

end Jump

end Node

end LeanDag
