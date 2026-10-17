import LeanDag.Scheme.AsyncLocal.Statement
import LeanDag.Scheme.Helpers.AsyncPace
/-!
# The asynchronous rows on a validator's own view — proof

Finitely many eventual holdings are eventually held together, which gives
delivery and production; on the delivered view a safe leader's slot
commits directly, and the coin names a safe leader with the counts' floors
(`Helpers/AsyncPace.lean`).
-/

namespace LeanDag

namespace Scheme

namespace AsyncLocal

theorem coinLive : CoinLive := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ U T N ap elect b r k hf hp hq
    helect hN
  exact ap.coin_eventuallyCommits σ hf hp hq elect helect hN

theorem delivered : Delivered := by
  intro Validator BlockId Payload _ _ _ P honest U T N qp ap
  exact ap.delivered

theorem populated : Populated := by
  intro Validator BlockId Payload _ _ _ P honest U T N qp ap hq
  exact ap.populated hq

theorem safeCommits : SafeCommits := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest p σ S U T N qp ap k hc hcm hq hN hk
  exact ap.decided_of_safe σ hc hcm hq hN hk

theorem commitsWithin : CommitsWithin := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest p σ S U T N qp ap c hc hcm hq hU
  exact ap.commitsWithin σ hc hcm hq hU

theorem allDecidedBelow : AllDecidedBelow := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest p σ S U T N qp ap c d hd hc hcm hq
    hspan hU
  exact ap.allDecidedBelow σ hd hc hcm hq hspan hU

theorem ofPaceCore : OfPaceCore := by
  intro Validator BlockId Payload _ _ _ _ P honest U T N qp pc hadv
  exact ⟨AsyncPace.ofPaceCore pc hadv⟩

theorem holds : Statement :=
  ⟨coinLive, delivered, populated, safeCommits, commitsWithin, allDecidedBelow, ofPaceCore⟩

end AsyncLocal

end Scheme

end LeanDag
