import LeanDag.KPartialDag.Live.Statement
import LeanDag.KPartialDag.Helpers.Live
/-!
# Liveness — proof

Each result is a helper of `Helpers/Live.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Live

theorem weaker : Weaker := by
  intro Validator BlockId Payload _ _ _ _ _ S U T R N h
  exact respondsFrom_of_syncFrom h

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ _ S p U K H T R k hrow hlive h hR hlead hH
  exact nodeDecided_of_responds hrow hlive h.1 (h.2 k hR le_rfl hlead) hH

theorem descends : Descends := by
  intro Validator BlockId Payload _ _ _ _ _ S p U K H b n hrow hH hbn hspan hav hrun
  exact nodeDecided_below hrow hH hbn hspan hav hrun

theorem progress : Progress := by
  intro Validator BlockId Payload _ _ _ _ _ S p K T c hrow hlive hc hspan fair R k
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  exact ⟨b, hkb, hRb, fun U h H hH hheld =>
    nodeDecided_of_run hrow hlive h.1 hH hc hspan (responds_of_run hc hRb hrun h) hheld⟩

theorem holds : Statement := ⟨weaker, commits, descends, progress⟩

end Live

end KPartialDag

end LeanDag
