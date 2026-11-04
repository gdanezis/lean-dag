import LeanDag.KPartialDag.Live.Statement
import LeanDag.KPartialDag.Helpers.Live
/-!
# Liveness — proof

A leader in `T` commits by `nodeDecided_of_leader_mem`; a committed run
decides below it by `nodeDecided_below`; and the schedule's run past any
slot and round (`Slots.exists_run_past`) decides every slot up to its end by
`nodeDecided_of_run`.
-/

namespace LeanDag

namespace KPartialDag

namespace Live

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S U K H T R k ⟨hcard, hs, hpop⟩ hR hlead hH
  exact nodeDecided_of_leader_mem hcard hs hR hlead (fun r h1 h2 => hpop r (by omega) h2) hH

theorem descends : Descends := by
  intro Validator BlockId Payload _ _ _ _ S U K H b n hH hbn hspan hav hrun
  exact nodeDecided_below hH hbn hspan hav hrun

theorem progress : Progress := by
  intro Validator BlockId Payload _ _ _ _ S K T c hc hspan fair R k
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  exact ⟨b, hkb, hRb, fun U ⟨hcard, hs, hpop⟩ H hH hheld =>
    nodeDecided_of_run hcard hs hH hc hspan hRb hrun
      (fun r h1 h2 => hpop r (le_trans hRb h1) h2) hheld⟩

theorem holds : Statement := ⟨commits, descends, progress⟩

end Live

end KPartialDag

end LeanDag
