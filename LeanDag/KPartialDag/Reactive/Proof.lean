import LeanDag.KPartialDag.Reactive.Statement
import LeanDag.KPartialDag.Helpers.Reactive
/-!
# Reactive nodes in time — proof

Persisting the last round built avoids equivocation by `Persists.eq_of_round`.
Every round is built by `ReactiveRules.exists_builtBy`; nodes behind catch
up by `ReactiveRules.builtBy_of_behind`, and a reactive run starts by
`ReactiveRules.exists_run`. Each round is built within `δ + max τ μ` by
`ReactiveRules.builtBy_succ`, and within `δ + max γ μ` under correct leaders by
`ReactiveRun.builtBy_succ_fast`; the run is responsive by
`ReactiveRun.respondsFrom`, and a slot led by correct validators commits
within `3δ + 2 max γ μ` by `ReactiveRun.nodeDecided_fast`; the run is
synchronous by `ReactiveRun.syncFrom`.
-/

namespace LeanDag

namespace KPartialDag

namespace Reactive

theorem persisted : Persisted := by
  intro Validator BlockId Payload _ _ _ _ _ ids block order stored h i hi j hj hc hij hr
  exact h.eq_of_round hi hj hc hij hr

theorem built : Built := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h s hs hsN
  exact h.exists_builtBy hs hsN

theorem catchesUp : CatchesUp := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h s t A hs hsN hG hA hcard hb
  exact h.builtBy_of_behind hs hsN hG hA hcard hb

theorem starts : Starts := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h
  exact h.exists_run

theorem slow : Slow := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h s t hs hsN hb
  exact h.builtBy_succ hs hsN (by have := h.le_of_builtBy hs hb; omega) hb

theorem fast : Fast := by
  intro Validator BlockId Payload _ _ _ _ S U tl G δ τ γ μ R N h hτ s t hs hsN hlead hb
  exact h.builtBy_succ_fast hτ hs hsN hb hlead

theorem responsive : Responsive := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h hτ
  exact h.respondsFrom hτ

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S U tl G δ τ γ μ R K N h hτ k t hk hN hlead hb v hv
  exact h.nodeDecided_fast hτ K hk hN hlead hb hv

theorem synchronised : Synchronised := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h hγ hγτ
  exact h.syncFrom hγ hγτ

theorem holds : Statement :=
  ⟨persisted, built, catchesUp, starts, slow, fast, responsive, commits, synchronised⟩

end Reactive

end KPartialDag

end LeanDag
