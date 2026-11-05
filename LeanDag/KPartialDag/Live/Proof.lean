import LeanDag.KPartialDag.Live.Statement
import LeanDag.KPartialDag.Helpers.Live
/-!
# Liveness — proof

Synchrony implies responsiveness by `respondsFrom_of_syncFrom`; a responsive
slot commits by `nodeDecided_of_responds`; a committed run decides below it
by `nodeDecided_below`; and the schedule's run past any slot and round
(`Slots.exists_run_past`), which responds by `responds_of_run`, decides every
slot up to its end by `nodeDecided_of_run`.
-/

namespace LeanDag

namespace KPartialDag

namespace Live

theorem weaker : Weaker := by
  intro Validator BlockId Payload _ _ _ _ S U T R N h
  exact respondsFrom_of_syncFrom h

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S U K H T R k h hR hlead hH
  exact nodeDecided_of_responds h.1 (h.2 k hR le_rfl hlead) hH

theorem descends : Descends := by
  intro Validator BlockId Payload _ _ _ _ S U K H b n hH hbn hspan hav hrun
  exact nodeDecided_below hH hbn hspan hav hrun

theorem progress : Progress := by
  intro Validator BlockId Payload _ _ _ _ S K T c hc hspan fair R k
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  exact ⟨b, hkb, hRb, fun U h H hH hheld =>
    nodeDecided_of_run h.1 hH hc hspan (responds_of_run hc hRb hrun h) hheld⟩

theorem holds : Statement := ⟨weaker, commits, descends, progress⟩

end Live

end KPartialDag

end LeanDag
