import LeanDag.KPartialDag.Live.Statement
import LeanDag.KPartialDag.Helpers.Live
/-!
# Liveness — proof

A leader in `T` commits by `nodeDecided_of_leader_mem`; a committed run
decides below it by `nodeDecided_below`; what a node needs is held by
correct nodes by `delivered`; and the schedule's run past any slot and round
(`Slots.exists_run_past`) decides every slot up to its end by
`nodeDecided_of_run`.
-/

namespace LeanDag

namespace KPartialDag

namespace Live

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S K U H T R k hcard hs hR hlead hpop hH
  exact nodeDecided_of_leader_mem hcard hs hR hlead hpop hH

theorem descends : Descends := by
  intro Validator BlockId Payload _ _ _ _ S K U H b n hH hbn hspan hav hrun
  exact nodeDecided_below hH hbn hspan hav hrun

theorem delivered : Delivered := by
  intro Validator BlockId Payload _ _ _ _ _ K U T lo hi n hT
  exact KPartialDag.delivered hT

theorem progress : Progress := by
  intro Validator BlockId Payload _ _ _ _ S K T c hcard hc hspan fair R k
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  exact ⟨b, hkb, hRb, fun U hs hpop H hH hheld =>
    nodeDecided_of_run hcard hs hH hc hspan hRb hrun hpop hheld⟩

theorem holds : Statement := ⟨commits, descends, delivered, progress⟩

end Live

end KPartialDag

end LeanDag
