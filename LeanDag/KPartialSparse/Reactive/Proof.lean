import LeanDag.KPartialSparse.Reactive.Statement
import LeanDag.KPartialSparse.Helpers.Reactive
/-!
# Sparse K-partial DAG — nodes in time, proof

Each result is a helper of `Helpers/Reactive.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Reactive

theorem built : Built := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h s hs hsN
  exact h.exists_reachedBy hs hsN

theorem catchesUp : CatchesUp := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h s t u hs hsN hG hu hQ
  exact h.reachedBy_of_quorumIn hs hsN hG hu hQ

theorem slow : Slow := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h hδ hγτ s t hs hsN hb
  exact h.builtBy_succ_slow hδ hγτ hs hsN hb

theorem fast : Fast := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h hτ hδ hγτ s t hs hsN hlead
    hb
  exact h.builtBy_succ_fast hτ hδ hγτ hs hsN hb hlead

theorem synchronised : Synchronised := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h hτ hδ hγτ
  exact h.syncFrom hτ hδ hγτ

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U tl T G δ τ γ R K N hlive h hτ hδ hγτ k t hk
    hN hlead hb v hv
  exact h.nodeDecided_fast hlive hτ hδ hγτ K hk hN hlead hb hv

theorem starts : Starts := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h
  exact h.exists_run

theorem resumes : Resumes := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h b hb hbc hbG hRb
  exact h.exists_resumed hb hbc hbG hRb

theorem durable : Durable := by
  intro Validator BlockId Payload _ _ _ _ _ _ U tl T K hT hTq hK A hA hV z hz
  exact exists_disk_of_avail hT hTq hK hA hV hz

theorem checked : Checked := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U tl K t hids h
  exact checks_of_buildsChecked (buildsChecked_of_timed hids h)

theorem unblocked : Unblocked := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U tl K t v s b h hv hb hbc
  exact referenceable_of_held h hv hb hbc

theorem claimable : Claimable := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N k t c L h hτ hδ hγτ ht hk
    hN hlead hc hcT hcr hL
  exact h.backs_of_leader hτ hδ hγτ ht hk hN hlead hc hcT hcr hL

theorem holds : Statement :=
  ⟨built, catchesUp, slow, fast, synchronised, commits, starts, resumes, durable, checked,
    unblocked, claimable⟩

end Reactive

end KPartialSparse

end LeanDag
