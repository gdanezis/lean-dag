import LeanDag.KPartialDag.Reactive.Statement
import LeanDag.KPartialDag.Helpers.Reactive
/-!
# Reactive nodes in time — proof

Persisting the last round built avoids equivocation by `Persists.eq_of_round`.
Operations resume by `NodeRules.exists_resumed`. Every round is reached by
`ReactiveRules.exists_reachedBy`; nodes behind catch up by
`NodeRules.reachedBy_of_behind`, and a reactive run starts by
`ReactiveRules.exists_run`. In a run no correct node skips a round
(`ReactiveRun.builtBy_of_reachedBy`); each round is built within
`δ + max τ μ` by `NodeRules.reachedBy_succ`, and within `δ + max γ μ` under
correct leaders by `ReactiveRun.builtBy_succ_fast`; the run is responsive by
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

theorem resumes : Resumes := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h b hb hbc hbG hRb
  exact h.exists_resumed hb hbc hbG hRb

theorem built : Built := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h s hs hsN
  exact h.exists_reachedBy hs hsN

theorem catchesUp : CatchesUp := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h s t A hs hsN hA hcard hb
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  obtain ⟨b₀, -, -, -, hG, ht⟩ := hb v hv
  refine h.reachedBy_of_behind hs hsN (hG.trans ht) hA hcard fun v hv => ?_
  obtain ⟨b, hb, hbv, hbr, hGb, hbt⟩ := hb v hv
  have hbc : (U.block b).creator ∈ (Correct : Finset Validator) := hbv ▸ hA hv
  exact ⟨_, hbc, b, h.mono _ hbc _ _ hGb hbt (h.own b hb hbc), hbv, hbr⟩

theorem starts : Starts := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h
  exact h.exists_run

theorem slow : Slow := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h hδ hγτ s t hs hsN hb
  exact h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega)
    (h.reachedBy_succ hs hsN (by have := h.le_of_reachedBy hs hb; omega) hb)

theorem fast : Fast := by
  intro Validator BlockId Payload _ _ _ _ S U tl G δ τ γ μ R N h hτ hδ hγτ s t hs hsN hlead hb
  exact h.builtBy_succ_fast hτ hδ hγτ hs hsN hb hlead

theorem responsive : Responsive := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h hτ hδ hγτ
  exact h.respondsFrom hτ hδ hγτ

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S U tl G δ τ γ μ R K N h hτ hδ hγτ k t hk hN hlead hb
    v hv
  exact h.nodeDecided_fast hτ hδ hγτ K hk hN hlead hb hv

theorem synchronised : Synchronised := by
  intro Validator BlockId Payload _ _ _ _ _ U tl G δ τ γ μ R N h hγ hδ hγτ
  exact h.syncFrom hγ hδ hγτ

theorem holds : Statement :=
  ⟨persisted, resumes, built, catchesUp, starts, slow, fast, responsive, commits, synchronised⟩

end Reactive

end KPartialDag

end LeanDag
