import LeanDag.Scheme.AsyncLive.Statement
import LeanDag.Scheme.Helpers.AsyncLive
import LeanDag.Scheme.AtomicBroadcast.Proof
import LeanDag.Scheme.Rows.Proof
import LeanDag.Scheme.Table.Proof
/-!
# The asynchronous rows across waves — proof

Steelhead's block count at the safe sets (`Helpers/AsyncLive.lean`), with
the floors of the counts.
-/

namespace LeanDag

namespace Scheme

namespace AsyncLive

theorem tail : Tail := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest p σ U T N qp ap S₀ hS dflt s₀ d M c
    hc hcm hq hd hspan hN hfloor
  exact undecided_le σ ap S₀ hS dflt hc hcm hq hd hspan hN hfloor

theorem vanishes : Vanishes := by
  intro Validator _ _ c d hc
  classical
  exact badBlockBound_tendsto_zero hc

theorem live : Live := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f b p σ U T N ap S₀ hS dflt s₀ d M
    hf hp hq hd hspan hN
  have hc := hp.2.2.1
  have hcm : p.commitThreshold ≤ T.card := le_trans hp.2.2.2 hq
  have hvw := Params.voteOffset_le hc.1
  have hfl : ∀ s, s₀ ≤ s → s < s₀ + M * d → _ := fun s _ hs =>
    floors (p := p) (r := S₀.slotRound s) ap hf hp hq
      (by have := S₀.mono (show s ≤ s₀ + M * d by omega); omega)
  refine ⟨fun hb => undecided_le σ ap S₀ hS dflt hc hcm hq hd hspan hN
      fun s h1 h2 => (hfl s h1 h2).1 hb,
    fun hb => undecided_le σ ap S₀ hS dflt hc hcm hq hd hspan hN
      fun s h1 h2 => (hfl s h1 h2).2.1 hb,
    fun hb hTh c hn hqn => undecided_le σ ap S₀ hS dflt hc hcm hq hd hspan hN
      fun s h1 h2 => (hfl s h1 h2).2.2 hb hTh c hn hqn⟩

/-- **An asynchronous row is ready for the count** at its parent quorum. -/
theorem asyncRow_ready {p : Params} {n f c b : ℕ} (h : p.AsyncRow n f c b) :
    p.AsyncReady n f (n - f - c) b := by
  have hr := Rows.asyncRows n f c
  rcases h with ⟨rfl, hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, hn, rfl, rfl⟩ |
    ⟨hn, rfl, rfl⟩ | ⟨hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, hn, rfl, rfl⟩
  · simpa using (hr.1 hn).1
  · simpa using (hr.1 hn).2.1
  · simpa using (hr.1 hn).2.2
  · simpa using hr.2.1 hn
  · exact hr.2.2.1 hn
  · exact (hr.2.2.2.2 hn).1
  · exact (hr.2.2.2.2 hn).2
  · simpa using hr.2.2.2.1 hn

/-- **An asynchronous row is covered** at its parent quorum. -/
theorem asyncRow_covered {p : Params} {n f c b : ℕ} (h : p.AsyncRow n f c b) :
    p.Covered n f (n - f - c) := by
  have hc := Table.rowsCovered n f c
  rcases h with ⟨rfl, hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, hn, rfl, rfl⟩ |
    ⟨hn, rfl, rfl⟩ | ⟨hn, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, hn, rfl, rfl⟩
  · simpa using (hc.1 hn).2.1 4 (by norm_num)
  · simpa using (hc.1 hn).2.1 5 (by norm_num)
  · simpa using (hc.1 hn).2.2.2
  · simpa using (hc.2.1 hn).2
  · exact (hc.2.2.1 hn).2
  · exact (hc.2.2.2.1 hn).2 4 (by norm_num)
  · exact (hc.2.2.2.1 hn).2 5 (by norm_num)
  · simpa using (hc.2.2.2.2 hn).2

theorem asyncRow_buffer {p : Params} {n f c b : ℕ} (h : p.AsyncRow n f c b) : 1 ≤ b := by
  rcases h with ⟨-, -, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ |
    ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, -, -, rfl⟩ <;> omega

theorem rowsValidity : RowsValidity := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p f c b _ hrow hhon σ wk U T N ap built S₀ hS
    dflt s₀ d M hTh hqT hd hspan hN hwr hbuilt P_k m t hk hm hmc hmr hheld hr2
  have hp := asyncRow_ready hrow
  have hc := hp.2.2.1
  have hvw := Params.voteOffset_le hc.1
  have hb := asyncRow_buffer hrow
  have hq2 := hp.1
  exact AtomicBroadcast.validityAsyncWeak Validator BlockId Payload P
    (Fintype.card Validator - f - c) honest f p σ wk U T N (Fintype.card Validator - f - c) ap
    built S₀ hS dflt s₀ d M 1 ⟨hhon, by omega, asyncRow_covered hrow⟩ hc (le_trans hp.2.2.2 hqT)
    hqT hTh (by omega) hd hspan hN
    (fun s _ hs => (floors (p := p) (r := S₀.slotRound s) ap hhon hp hqT
      (by have := S₀.mono (show s ≤ s₀ + M * d by omega); omega)).1 hb)
    hwr hbuilt P_k m t hk hm hmc hmr hheld hr2

theorem rowsValidityOne : RowsValidityOne := by
  intro Validator BlockId Payload _ _ _ _ d ε hε
  have h := (ENNReal.tendsto_nhds_zero.mp (vanishes Validator 1 d one_pos)) ε hε
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨M₀, fun M hM P _ honest p f c b _ hrow hhon σ wk U T N ap built S₀ hS dflt s₀ hTh hqT hd
    hspan hN hwr hbuilt P_k m t hk hm hmc hmr hheld hr2 => ?_⟩
  exact le_trans (rowsValidity Validator BlockId Payload P honest p f c b hrow hhon σ wk U T N ap
    built S₀ hS dflt s₀ d M hTh hqT hd hspan hN hwr hbuilt P_k m t hk hm hmc hmr hheld hr2)
    (hM₀ M hM)

theorem holds : Statement := ⟨tail, vanishes, live, rowsValidity, rowsValidityOne⟩

end AsyncLive

end Scheme

end LeanDag
