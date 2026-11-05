import LeanDag.KPartialDag.Reactive.Statement
import LeanDag.KPartialDag.Helpers.Reactive
/-!
# Reactive nodes in time — proof

Every round is built by `ReactiveRules.exists_builtBy`; nodes behind catch
up by `ReactiveRules.builtBy_of_behind`, and a reactive run starts by
`ReactiveRules.exists_run`. Each round is built within `δ + τ` by
`ReactiveRules.builtBy_succ`, and within `δ` under correct leaders by
`ReactiveRun.builtBy_succ_fast`; the run is responsive by
`ReactiveRun.respondsFrom`, and a slot led by correct validators commits
within `3δ` by `ReactiveRun.nodeDecided_fast`.
-/

namespace LeanDag

namespace KPartialDag

namespace Reactive

theorem built : Built := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ R N h s hs hsN
  exact h.exists_builtBy hs hsN

theorem catchesUp : CatchesUp := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ R N h s t A hs hsN hG hA hcard hb
  exact h.builtBy_of_behind hs hsN hG hA hcard hb

theorem starts : Starts := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ R N h
  exact h.exists_run

theorem slow : Slow := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ R N h s t hs hsN hb
  exact h.builtBy_succ hs hsN (by have := h.le_of_builtBy hs hb; omega) hb

theorem fast : Fast := by
  intro Validator BlockId Payload _ _ _ _ S U tl G δ τ R N h hτ s t hs hsN hlead hb
  exact h.builtBy_succ_fast hτ hs hsN hb hlead

theorem responsive : Responsive := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ R N h hτ
  exact h.respondsFrom hτ

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S U tl G δ τ R K N h hτ k t hk hN hlead hb v hv
  exact h.nodeDecided_fast hτ K hk hN hlead hb hv

theorem holds : Statement := ⟨built, catchesUp, starts, slow, fast, responsive, commits⟩

end Reactive

end KPartialDag

end LeanDag
