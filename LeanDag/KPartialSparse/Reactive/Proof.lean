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
  intro Validator BlockId Payload _ _ _ _ _ _ _ U tl K t v s b hids h hv hb hbc
  exact referenceable_of_held hids h hv hb hbc

theorem claimable : Claimable := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N k t c L h hτ hδ hγτ ht hk
    hN hlead hc hcT hcr hL
  exact h.backs_of_leader hτ hδ hγτ ht hk hN hlead hc hcT hcr hL

theorem chained : Chained := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h hd
  exact chains_of_selfRef h.self_ref hd

theorem buildable : Buildable := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U H r v pay
  refine ⟨fun hH hq => exists_dense_block hH hq v pay, fun hH hv hvl ho hL => ?_,
    fun tl T G δ τ γ R N c h hγ hδ hγτ hr hrN hc hcT hcr =>
      h.exists_valid_block hγ hδ hγτ hr hrN hc hcT hcr pay⟩
  obtain ⟨o, ho, hoc, hor⟩ := ho
  obtain ⟨L, hL, hLc, hLl, hLr⟩ := hL
  exact exists_sparse_block hH hv hvl ho hoc hor hL hLc hLl hLr pay

theorem covered : Covered := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ U tl T G δ τ γ R N h hγ hδ hγτ hsl
  exact h.coversFrom hγ hδ hγτ hsl

theorem ledger : Ledger := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U tl T G δ τ γ R N K D Δ c hrow hlink hI hlive
    h hτ hδ hγτ hF hc hspan fair k
  exact h.exists_ledger hrow hlink hI hlive hτ hδ hγτ D hF hc hspan fair k

theorem recovers : Recovers := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U tl T G δ τ γ R N K D Δ c hrow hlink hI hlive
    h hτ hδ hγτ hF hc hspan fair b₀ hb₀ hb₀c hb₀G hRb₀ k
  exact h.exists_recovered hrow hlink hI hlive hτ hδ hγτ D hF hc hspan fair hb₀ hb₀c hb₀G hRb₀ k

theorem holds : Statement :=
  ⟨built, catchesUp, slow, fast, synchronised, commits, starts, resumes, durable, checked,
    unblocked, claimable, chained, buildable, covered, ledger, recovers⟩

end Reactive

end KPartialSparse

end LeanDag
