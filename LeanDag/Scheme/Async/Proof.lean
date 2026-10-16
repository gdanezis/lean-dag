import LeanDag.Scheme.Async.Statement
import LeanDag.Scheme.Helpers.AsyncCoin
/-!
# The asynchronous rows — proof

The count is the common core at a general quorum and two double counts
(`Helpers/Async.lean`); liveness under the clause is the good leader's
direct commit and the descent below a run; the coin is Steelhead's counts
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

theorem safeGood : SafeGood := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest p σ U r L T hw hcv hpop hcm hL hLr hLc hs
  exact mem_goodAt_of_safe σ hw hcv hpop hcm hL hLr hLc hs

theorem goodNonempty : GoodNonempty := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ U r T hf hq2 hw hcv hvo hT hpop2
    hpop hcm
  exact goodAt_nonempty σ hf hq2 hw hcv hvo hT hpop2 hpop hcm

theorem goodCard : GoodCard := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ U r T hf hq2 hw hcv hvo hT hpop3
    hpop hcm
  exact le_card_goodAt σ hf hq2 hw hcv hvo hT hpop3 hpop hcm

theorem goodCount : GoodCount := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ U r T hf hw hcv hvo hTh hpop1 hpop
    hcm hnq
  exact card_goodAt_count σ hf hw hcv hvo hTh hpop1 hpop hcm hnq

theorem multiLeader : MultiLeader := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U r M hM hcard
  exact exists_good_leader σ hM hcard

theorem goodCommits' : GoodCommits := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V k hk hV
  exact goodCommits σ hk hV

theorem commitsWithin' : CommitsWithin := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V c N hU hV k hk
  exact commitsWithin σ hU hV hk

theorem allDecidedBelow' : AllDecidedBelow := by
  intro Validator BlockId Payload _ _ _ P _ honest p σ S U V c d N hd hspan hU hV k hk
  exact allDecidedBelow σ hd hspan hU hV hk

theorem coinCommit : CoinCommit := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ U r T hf hq2 hw hcv hT hpop hcm
  refine ⟨fun hvo hpop2 => ?_, fun hvo hpop3 => ?_⟩
  · obtain ⟨v, hv⟩ := goodAt_nonempty σ hf hq2 hw hcv hvo hT hpop2 hpop hcm
    exact_mod_cast floor_le_coin (G := goodAt p σ U r) (c := 1)
      (Finset.card_pos.mpr ⟨v, (Finset.mem_inter.mp hv).1⟩)
  · have h := le_card_goodAt σ hf hq2 hw hcv hvo hT hpop3 hpop hcm
    exact floor_le_coin (le_trans (by omega)
      (Finset.card_le_card (Finset.inter_subset_left (s₁ := goodAt p σ U r) (s₂ := honest))))

theorem coinTail : CoinTail := by
  intro Validator BlockId Payload _ _ _ _ P honest p σ U r₀ c
  exact ⟨fun m hc => noHit_le (fun i : Fin m => goodAt p σ U (r₀ + i)) hc,
    fun hc hcn => noHit_tendsto_zero hc hcn⟩

theorem holds : Statement :=
  ⟨commonCore, safeGood, goodNonempty, goodCard, goodCount, multiLeader, goodCommits',
    commitsWithin', allDecidedBelow', coinCommit, coinTail⟩

end Async

end Scheme

end LeanDag
