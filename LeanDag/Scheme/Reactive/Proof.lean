import LeanDag.Scheme.Reactive.Statement
import LeanDag.Scheme.Helpers.ReactiveMysticeti
/-!
# The family, run reactively — proof

The wait clauses certify (`Helpers/Reactive.lean`), which is the support's
precondition; the generic `LeaderCommits` then applies. Reactive Mysticeti
converts (`Helpers/ReactiveMysticeti.lean`).
-/

namespace LeanDag

namespace Scheme

namespace ReactiveRun

open Properties

theorem certifies : Certifies := by
  intro Validator BlockId Payload _ _ F _ P _ honest p σ S U T N R rs k L hw hcv hTh hcard hgst
    hto hR hN hlead hL
  exact rs.certifies hw hcv hTh hcard hgst hto hR hN hlead hL

theorem live : Live := by
  intro Validator BlockId Payload _ _ F _ P _ honest p σ Hon S U V T lo K hw hcv h
  exact live_of_reactiveLive hw hcv h

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ F _ P _ honest p σ Hon hw hcv hcm
  exact leaderCommits_reactive hw hcv hcm

theorem ofMysticeti : OfMysticeti := by
  intro Validator BlockId Payload _ _ F _ S σ U T N hT rm
  exact ⟨ofReactiveM σ hT rm⟩

theorem holds : Statement := ⟨certifies, live, commits, ofMysticeti⟩

end ReactiveRun

end Scheme

end LeanDag
