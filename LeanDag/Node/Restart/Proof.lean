import LeanDag.Node.Restart.Statement
import LeanDag.Node.Helpers.Resume
/-!
# A node across a crash — proof

Every state a run reaches holds its top and its default block (`Held`),
which is what resuming reads (`resume_persisted`).
-/

namespace LeanDag

namespace Node

namespace Restart

theorem resumes : Resumes := by
  intro Validator BlockId Payload _ _ _ cfg is
  exact resume_persisted (Held.run is Held.init)

theorem holds : Statement := resumes

end Restart

end Node

end LeanDag
