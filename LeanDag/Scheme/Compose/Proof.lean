import LeanDag.Scheme.Compose.Statement
import LeanDag.Scheme.Crash.Proof
import LeanDag.Integration.SchemeCheckpoint
import LeanDag.Scheme.Schedules.Proof
import LeanDag.Barnacle.Aimd.Proof
import LeanDag.Adaptive.Score.Proof
/-!
# The mechanisms composed — proof

The checkpoint bridge (`Integration.liveCommitFinalized_scheme`) needs the
wave of the slot populated and its candidates certified by the validators
following the signing rule; the responsive precondition gives both
(`live_of_reactiveLive`), and the crash precondition is the responsive one
(`Crash.live`). A configuration run with crashes is run responsively past
`max gst tr` (`CrashRun.toReactive`), so scheduling with crashes is
scheduling over responsive runs, and the runs it gives on every signer's
view feed the checkpoint bridge over scheduling runs
(`Integration.commitFinalized_barnacle_scheme`).
-/

namespace LeanDag

namespace Scheme

namespace Compose

theorem checkpointsResponsive : CheckpointsResponsive := by
  intro Validator BlockId Payload Value _ _ _ _ P _ honest p σ q f _ M E vm rel ht hc hcm S U Pr V
    slot hlive hcov hlead
  obtain ⟨hq, N, -, -, hall⟩ := live_of_reactiveLive hc.1 hc.2 hlive
  obtain ⟨hpop, hcert⟩ := hall slot (le_refl _) (Nat.lt_succ_self _) hlead
  exact Integration.liveCommitFinalized_scheme M E vm ht hcm S Pr hq hpop hcert hcov hlead

theorem checkpointsCrash : CheckpointsCrash := by
  intro Validator BlockId Payload Value _ _ _ _ P _ honest p σ q f _ M E vm rel ht hc hcm S U Pr V
    slot hlive hcov hlead
  exact checkpointsResponsive Validator BlockId Payload Value P honest p σ q f M E vm rel ht hc hcm
    S U Pr V slot (Crash.live Validator BlockId Payload P honest p σ rel S U V M.alive slot
      (slot + 1) hlive) hcov hlead

/-- A configuration run with crashes is run responsively past `max gst tr`. -/
theorem reactiveGood_of_crashGood {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Nonempty Validator] [LinearOrder BlockId]
    {P : Validity Validator BlockId Payload} [P.Mechanised] {honest : Finset Validator}
    {p : Params} {σ : VoteSel Validator BlockId Payload P honest} {rel : Reliability Validator}
    {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest} {Rnd N : ℕ}
    (h : crashGood p σ rel S U Rnd N) : reactiveGood p σ rel S U Rnd N := by
  obtain ⟨T, hq, hTh, N', cr, hgst, hto, hW⟩ := h
  exact ⟨T, hq, hTh, N', cr.toReactive, hgst, hto, hW⟩

theorem scheduledCrash : ScheduledCrash := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ rel B Bd upd C₀ Q c δ hRE h₀ hQ₀ U V N
    hcov hgood K hK
  exact hRE h₀ hQ₀ U V N hcov
    (fun K Rn hQ => (hgood K Rn hQ).imp reactiveGood_of_crashGood id) K hK

theorem hammerHeadComposed : HammerHeadComposed := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel M E vm ht hc hsch
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro B score C₀ δ hkeep hQ h₀ hC₀ U C Pr N hcov hgood K hK
  have hRE := Schedules.hammerHeadReactive n hn BlockId Payload P q honest f p σ rel ht hc hsch
    B score C₀ δ hkeep hQ
  have hrun : ∀ v, Nonempty (Barnacle.Run (schemeLiveReactive p σ rel).toBaseRule B
      Barnacle.Boundary.atThreshold (Adaptive.rule score) C₀ U (Pr.view v) K) := fun v =>
    scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE h₀ hC₀ U
      (Pr.view v) N (hcov v) (hgood v) K hK
  refine ⟨fun v => (hrun v).some, fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  exact Integration.commitFinalized_barnacle_scheme M E vm ht (Adaptive.Score.rule_anchored score)
    Pr (fun v => (hrun v).some) hk hcfg h hlo hhi

theorem aimdComposed : AimdComposed := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel M E vm ht hc hsch
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro B Bd lead hl hlead C₀ δ h₀ hC₀ U C Pr N hcov hgood K hK
  have hRE := Schedules.aimdReactive n hn BlockId Payload P q honest f p σ rel ht hc hsch
    B Bd lead hl hlead C₀ δ
  have hrun : ∀ v, Nonempty (Barnacle.Run (schemeLiveReactive p σ rel).toBaseRule B Bd
      (Barnacle.Aimd.rule _ B lead hl) C₀ U (Pr.view v) K) := fun v =>
    scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE h₀ hC₀ U
      (Pr.view v) N (hcov v) (hgood v) K hK
  refine ⟨fun v => (hrun v).some, fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  exact Integration.commitFinalized_barnacle_scheme M E vm ht
    (Barnacle.Aimd.holds _ _ _ _ B lead hl).2.2.2.2
    Pr (fun v => (hrun v).some) hk hcfg h hlo hhi

theorem holds : Statement :=
  ⟨checkpointsResponsive, checkpointsCrash, scheduledCrash, hammerHeadComposed, aimdComposed⟩

end Compose

end Scheme

end LeanDag
