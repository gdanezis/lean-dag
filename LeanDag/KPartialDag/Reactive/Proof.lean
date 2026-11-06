import LeanDag.KPartialDag.Reactive.Statement
import LeanDag.KPartialDag.Helpers.Reactive
/-!
# Reactive nodes in time — proof

Each result is a helper of `Helpers/Reactive.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Reactive

theorem persisted : Persisted := by
  intro Validator BlockId Payload _ _ _ _ _ ids block order next h i hi j hj hc hij hr
  exact h.eq_of_round hi hj hc hij hr

theorem onDisk : OnDisk := by
  intro Validator BlockId Payload _ _ _ _ _ ids block tl h
  exact h.persists

theorem resumes : Resumes := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h b hb hbc hbG hRb
  exact h.exists_resumed hb hbc hbG hRb

theorem built : Built := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h s hs hsN
  exact h.exists_reachedBy hs hsN

theorem catchesUp : CatchesUp := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h s t A hs hsN hG hA hcard hb
  refine h.reachedBy_of_behind hs hsN hG hA hcard fun v hv => ?_
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  have hbT : (U.block b).creator ∈ T := hbv ▸ hA hv
  exact ⟨_, hbT, b, h.own hb (h.stable hbT) hbt, hbv, hbr⟩

theorem starts : Starts := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h
  exact h.exists_run

theorem slow : Slow := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h hδ hγτ s t hs hsN hb
  exact h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega)
    (h.reachedBy_succ hs hsN (by have := h.le_of_reachedBy hs hb; omega) hb)

theorem fast : Fast := by
  intro Validator BlockId Payload _ _ _ _ S U tl T G δ τ γ μ R N h hτ hδ hγτ s t hs hsN hlead hb
  exact h.builtBy_succ_fast hτ hδ hγτ hs hsN hb hlead

theorem responsive : Responsive := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h hτ hδ hγτ
  exact h.respondsFrom hτ hδ hγτ

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ S p U tl T G δ τ γ μ R K N hrow hlive h hτ hδ hγτ k t hk
    hN hlead hb v hv
  exact h.nodeDecided_fast hrow hlive hτ hδ hγτ K hk hN hlead hb hv

theorem synchronised : Synchronised := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T G δ τ γ μ R N h hγ hδ hγτ
  exact h.syncFrom hγ hδ hγτ

theorem durable : Durable := by
  intro Validator BlockId Payload _ _ _ _ _ U tl T K hT hTq hK A hA hV z hz
  exact exists_disk_of_avail hT hTq hK hA hV hz

theorem ledger : Ledger := by
  intro Validator BlockId Payload _ _ _ _ S p U tl T G δ τ γ μ R N K D Δ c hrow hlive h hτ hδ hγτ hF
    hc hspan fair k
  exact h.exists_ledger hrow hlive hτ hδ hγτ D hF hc hspan fair k

theorem holds : Statement :=
  ⟨persisted, onDisk, resumes, built, catchesUp, starts, slow, fast, responsive, commits,
    synchronised, durable, ledger⟩

end Reactive

end KPartialDag

end LeanDag
