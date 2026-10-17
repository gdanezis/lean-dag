import LeanDag.Scheme.Reactive.Statement
import LeanDag.Scheme.Helpers.ReactiveMysticeti
/-!
# The family, run reactively — proof

The wait clauses certify (`Helpers/Reactive.lean`), which is the support's
precondition; the generic `LeaderCommits` then applies. Reactive Mysticeti
converts (`Helpers/ReactiveMysticeti.lean`). Inclusion is the generic
`committed_of_correct_block` over the reactive `LeaderCommits`.
-/

namespace LeanDag

namespace Scheme

namespace ReactiveRun

open Properties

theorem certifies : Certifies := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ S U T N R q rs k L hc hTh hq hgst
    hto hR hN hlead hL
  exact rs.certifies hc.1 hc.2 hTh hq hgst hto hR hN hlead hL

theorem live : Live := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ Hon rel S U V T lo K hc h
  exact live_of_reactiveLive hc.1 hc.2 h

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ Hon rel hc hcm
  exact leaderCommits_reactive hc.1 hc.2 hcm

theorem includes : Includes := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ Hon rel hP hsub hc hcm S T hT fair m v
    hv
  exact includes_reactive hP hsub hc.1 hc.2 hcm S hT fair m hv

theorem ofMysticeti : OfMysticeti := by
  intro Validator BlockId Payload _ _ F _ _ S σ U T N hT rm
  exact ⟨ofReactiveM σ hT rm⟩

theorem holds : Statement := ⟨certifies, live, commits, includes, ofMysticeti⟩

end ReactiveRun

end Scheme

end LeanDag
