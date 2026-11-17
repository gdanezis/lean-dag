import LeanDag.KPartialSparse.Live.Statement
import LeanDag.KPartialSparse.Helpers.Live
/-!
# Sparse K-partial DAG — liveness, proof

Each result is a helper of `Helpers/Live.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Live

theorem weaker : Weaker := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U T R N h
  exact respondsFrom_of_syncFrom h

theorem backable : Backable := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U T H R N k t L h hR hN hk hL ht hLH hH
  exact backs_of_syncFrom h hR hN hk hL ht hLH hH

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K H T R k hlive h hR hlead hH
  exact nodeDecided_of_responds hlive h.1 (h.2 k hR le_rfl hlead) hH

theorem descends : Descends := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K H b n hbn hspan hav hrun
  exact nodeDecided_below hbn hspan hav hrun

theorem progress : Progress := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p K T c hlive hc hspan fair R k
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  exact ⟨b, hkb, hRb, fun U h H hheld =>
    nodeDecided_of_run hlive h.1 hc hspan (responds_of_run hc hRb hrun h) hheld⟩

theorem holds : Statement := ⟨weaker, backable, commits, descends, progress⟩

end Live

end KPartialSparse

end LeanDag
