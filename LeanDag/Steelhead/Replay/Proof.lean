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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro candidates scores current epsilon hc
    exact select_mem candidates scores current epsilon hc
  · intro candidates scores current epsilon
    exact select_score_le candidates scores current epsilon
  · intro A I r w a hw
    exact ⟨certified_of_commits U A I r w a, not_certified_of_skips U A I r w a hw⟩
  · intro A hA T r hwa hcard hr hpop3 hpopd
    exact window_count hA hwa hcard hr hpop3 hpopd
  · intro E C period r hws hwa hr
    exact bounded_timingAt (probeRate_fst_le E C period) hws hwa r hr
  · intro E C period r hws hlt hb hr hdec hcons
    exact async_term_bound hws hlt hb hr hdec hcons
  · intro A I r w a h
    exact commits_sound h
  · intro C candidates epsilon K j k A out hK hc h1 hk
    exact failover_anchorUpdate_range C candidates epsilon A out hK hc h1 hk
  · intro A hA r hwa hr
    exact commitWeight_eq_commitProb hwa hA hr
  · intro E C period hcop hp hws hwin
    exact probe_exists hcop hp hws hwin

end Replay

end Steelhead

end LeanDag
