import LeanDag.Steelhead.Replay.Statement
import LeanDag.Steelhead.Helpers.Replay
/-!
# The replay — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Replay.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U wa I
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro candidates scores current epsilon hc
    exact select_mem candidates scores current epsilon hc
  · intro candidates scores current epsilon
    exact select_score_le candidates scores current epsilon
  · intro A I r w a hw
    exact ⟨certified_of_commits U A I r w a, not_certified_of_skips U A I r w a hw⟩
  · intro A hA T r hwa hcard hr hpop3 hpopd
    exact window_count hA hwa hcard hr hpop3 hpopd

end Replay

end Steelhead

end LeanDag
