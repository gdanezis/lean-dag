import LeanDag.Scheme.Async.Statement
import LeanDag.Scheme.Helpers.AsyncCoin
import LeanDag.Scheme.Helpers.Starve
/-!
# The asynchronous rows — proof

The count is the common core at a general quorum and two double counts
(`Helpers/Async.lean`); the tight case is a starving execution
(`Helpers/Starve.lean`); the coin is Steelhead's counts
(`Helpers/AsyncCoin.lean`).
-/

namespace LeanDag

namespace Scheme

namespace Async

open Filter Topology
open scoped ENNReal

theorem commonCore : CommonCore := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f U r c₀ hf hq2 hc₀ hc₀r
  exact exists_commonCore hf hq2 hc₀ hc₀r

theorem safeNonempty : SafeNonempty := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p U r T hf hq2 hvo hT hpop2
  exact safeAt_nonempty hf hq2 hvo hT hpop2

theorem safeCard : SafeCard := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p U r T hf hq2 hvo hT hpop3
  exact le_card_safeAt hf hq2 hvo hT hpop3

theorem safeCount : SafeCount := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p U r T hf hvo hTh hpop1 hnq
  exact card_safeAt_count hf hvo hTh hpop1 hnq

theorem multiLeader : MultiLeader := by
  intro Validator BlockId Payload _ _ _ P _ honest p S U r M hM hcard
  exact exists_safe_leader hM hcard

theorem bufferTight : BufferTight := by
  intro n f q N p hfq hqn hvo hN
  exact ⟨_, Starve.record (f := f) hqn N, Starve.starvePace N,
    Starve.card_compl_honestSet (by omega), fun r hr => Starve.populated_record hr,
    fun b hb => Starve.refs_starve_eq_held hb rfl, Starve.card_safeAt_starve hvo hN hfq⟩

theorem coinCommit : CoinCommit := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p U r T hf hq2 hT
  refine ⟨fun hvo hpop2 => ?_, fun hvo hpop3 => ?_⟩
  · obtain ⟨v, hv⟩ := safeAt_nonempty hf hq2 hvo hT hpop2
    exact_mod_cast floor_le_coin (G := safeAt p U r) (c := 1) (Finset.card_pos.mpr ⟨v, hv⟩)
  · exact floor_le_coin (by have := le_card_safeAt (p := p) hf hq2 hvo hT hpop3; omega)

theorem coinTail : CoinTail := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p U r₀ c
  exact ⟨fun m hc => noHit_le (fun i : Fin m => safeAt p U (r₀ + i)) hc,
    fun hc hcn => noHit_tendsto_zero hc hcn⟩

theorem holds : Statement :=
  ⟨commonCore, safeNonempty, safeCard, safeCount, multiLeader, bufferTight, coinCommit,
    coinTail⟩

end Async


end Scheme

end LeanDag
