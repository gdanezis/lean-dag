import LeanDag.Scheme.Loop.Statement
import LeanDag.Scheme.Helpers.Order
import LeanDag.Scheme.Helpers.Ledger
/-!
# The commit loop — proof

Soundness by induction down the scan, completeness by induction on a
bounded derivation (`Helpers/TryDecide.lean`); prefix comparability and
completeness use the laws of `Helpers/Sufficiency.lean`; the restart,
the order and the ledger are `Helpers/Restart.lean`, `Helpers/Order.lean`
and `Helpers/Ledger.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Loop

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V lo N hl hc hlo
  exact tryDecide_sound hl hc hlo

theorem prefixComparable : PrefixComparable := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V₁ V₂ lo N₁ N₂
    ht h₁ h₂
  obtain ⟨hl, -, hc, hlaws⟩ := coveredLaws σ ht
  exact tryDecide_prefix hl hc hlaws trivial h₁ h₂ V₁ V₂

theorem complete : Complete := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V k v ht hd
  obtain ⟨hl, hcm, hc, hlaws⟩ := coveredLaws σ ht
  exact decisionAt_eventually hl hcm hc hlaws trivial hd

theorem outputComplete : OutputComplete := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V lo k ht
    hlok hall
  obtain ⟨hl, hcm, hc, hlaws⟩ := coveredLaws σ ht
  exact tryDecide_eventually hl hcm hc hlaws trivial hlok hall

theorem restart : Restart := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V lo lo' N hlo hlo'
  exact tryDecide_restart hlo hlo'

theorem resume : Resume := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V₁ V₂ lo N₁ N₂
    ht hsub hN
  obtain ⟨hl, hcm, hc, hlaws⟩ := coveredLaws σ ht
  exact tryDecide_resume hl hcm hc hlaws trivial hsub hN

theorem repeated : Repeated := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U lo W N
    ht hW hN
  obtain ⟨hl, hcm, hc, hlaws⟩ := coveredLaws σ ht
  exact consumed_eq hl hcm hc hlaws trivial hW hN

theorem order : Order := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V per m rLast rHigh hp hm h
  exact schemeTryDecide_eq hp hm h

theorem orderUniform : OrderUniform := by
  intro Validator per m rLast rHigh hp hm elect hblock
  exact schemeOrder_uniform hp hm

theorem restartRound : RestartRound := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V₁ V₂ per m rLast rHigh₁
    rHigh₂ k v ht hsub hp hm h₁ hH hlast
  obtain ⟨hl, hcm, hc, hlaws⟩ := coveredLaws σ ht
  exact schemeTryDecide_restartRound hl hcm hc hlaws trivial hsub hp hm h₁ hH hlast

theorem ledger : Ledger := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V N hl hc
  exact ledger_read hl hc N

theorem ledgerAgree : LedgerAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V₁ V₂ N₁ N₂
    ht
  obtain ⟨hl, -, hc, hlaws⟩ := coveredLaws σ ht
  exact ledger_agree hl hc hlaws trivial V₁ V₂ N₁ N₂

theorem holds : Statement :=
  ⟨sound, prefixComparable, complete, outputComplete, restart, resume, repeated, order,
    orderUniform, restartRound, ledger, ledgerAgree⟩

end Loop

end Scheme

end LeanDag
