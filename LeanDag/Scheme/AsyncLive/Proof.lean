import LeanDag.Scheme.AsyncLive.Statement
import LeanDag.Scheme.Helpers.AsyncLive
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

theorem holds : Statement := ⟨tail, vanishes, live⟩

end AsyncLive

end Scheme

end LeanDag
