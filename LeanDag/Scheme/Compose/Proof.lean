import LeanDag.Scheme.Compose.Statement
import LeanDag.Scheme.Crash.Proof
import LeanDag.Integration.SchemeCheckpoint
import LeanDag.Scheme.Schedules.Proof
import LeanDag.Barnacle.Aimd.Proof
import LeanDag.Adaptive.Score.Proof
import LeanDag.Scheme.Helpers.CoinHeads
import LeanDag.Scheme.Helpers.AsyncPace
import LeanDag.Scheme.Helpers.Validity
import LeanDag.Scheme.Helpers.Deliver
import LeanDag.Barnacle.Ledger.Proof
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

theorem asyncComposed : AsyncComposed := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel Ms E vm J M c dflt ht hc hcm
  haveI : Nonempty (Fin n) := ⟨dflt⟩
  intro B Bd lead hl hlead C₀ hC₀ U T Nr qp ac hq hTh hqp N hN C Pr hcov hNJ hfloor K hK
  refine le_trans (MeasureTheory.measure_mono fun g hg => ?_) (windowsFail_le (safeAt p U) hfloor)
  simp only [Set.mem_setOf_eq] at hg ⊢
  intro hwin
  apply hg
  have hrun : ∀ v, Nonempty (Barnacle.Run
      (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B Bd
      (Barnacle.Aimd.rule _ B (lead (coinHead dflt g)) (hl _)) (C₀ (coinHead dflt g)) U
      (Pr.view v) K) := fun v =>
    Schedules.asyncAimdRuns n hn BlockId Payload P q honest f p σ rel
      (2 * (M * (p.waveLength - 1 + 1))) ht hc hcm B Bd (lead (coinHead dflt g)) (hl _)
      (coinHead dflt g) (hlead _) (C₀ (coinHead dflt g)) (hC₀ _).1 (hC₀ _).2 U (Pr.view v) N T
      hq hTh (fun r hr => ac.toAsyncPace.populated hqp r (le_trans hr hN))
      (safeHeadRuns_of_windows p U rfl dflt id (safeAt p U) (fun _ _ h => h) g hNJ hwin) (hcov v) K hK
  refine ⟨fun v => (hrun v).some, fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  exact Integration.commitFinalized_barnacle_scheme Ms E vm ht
    (Barnacle.Aimd.holds _ _ _ _ B _ (hl _)).2.2.2.2
    Pr (fun v => (hrun v).some) hk hcfg h hlo hhi

open scoped ENNReal in
theorem asyncHammerHeadComposed : AsyncHammerHeadComposed := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel Ms E vm J M m k e s dflt Tbls ht hc
    hcm hsup
  haveI : Nonempty (Fin m) := ⟨dflt⟩
  intro B score C₀ hkeep hQ hC₀ U T Nr qp ac hq hTh hqp N hN C Pr hcov hNJ hfloor K hK
  let Sr : (Fin m → Fin n) → ℕ → Finset (Fin m) := fun tbl r =>
    Finset.univ.filter fun j => tbl j ∈ safeAt p U r
  have hsub : {g : Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin m | ¬ ∃ Rn : ∀ v,
        Barnacle.Run (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
          Barnacle.Boundary.atThreshold (Adaptive.rule (score (coinHead dflt g)))
          (C₀ (coinHead dflt g)) U (Pr.view v) K,
        ∀ (k' : ℕ), k' < K → ∀ (v₀ : Fin n), (Rn v₀).cfg k' = C →
          ∀ (κ : ℕ) (L : BlockId), (Rn v₀).vdct k' κ = some L →
            (Rn v₀).start k' < C.roundOf κ → C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor k') →
            Nonempty (Checkpoint.SigningFaults.Execution.FinalityQC Ms E
              (vm.checkpointAfterCommit κ L))} ⊆
      ⋃ tbl ∈ Tbls, {g | ¬ ∀ j : Fin J, ∃ m' : Fin M, ∀ i : Fin (p.waveLength - 1 + 1),
        g ⟨j * M + m', blk_lt j.isLt m'.isLt⟩ i ∈
          Sr tbl ((j * M + m') * (p.waveLength - 1 + 1) + i)} := by
    intro g hg
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hno
    apply hg
    have hrun : ∀ v, Nonempty (Barnacle.Run
        (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
        Barnacle.Boundary.atThreshold (Adaptive.rule (score (coinHead dflt g)))
        (C₀ (coinHead dflt g)) U (Pr.view v) K) := fun v =>
      Schedules.asyncHammerHeadRuns n hn BlockId Payload P q honest f p σ rel
        (2 * (M * (p.waveLength - 1 + 1))) m (coinHead dflt g) Tbls ht hc hcm B
        (score (coinHead dflt g)) (C₀ (coinHead dflt g)) (hkeep _) (hQ _) (hC₀ _).1 (hC₀ _).2
        U (Pr.view v) N T hq hTh (fun r hr => ac.toAsyncPace.populated hqp r (le_trans hr hN))
        (fun tbl htbl => safeHeadRuns_of_windows p U rfl dflt tbl (Sr tbl)
          (fun r x hx => (Finset.mem_filter.mp hx).2) g hNJ (hno tbl htbl))
        (hcov v) K hK
    refine ⟨fun v => (hrun v).some, fun k' hk v₀ hcfg κ L h hlo hhi => ?_⟩
    exact Integration.commitFinalized_barnacle_scheme Ms E vm ht
      (Adaptive.Score.rule_anchored (score (coinHead dflt g)))
      Pr (fun v => (hrun v).some) hk hcfg h hlo hhi
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_biUnion_finset_le _ _) ?_)
  calc ∑ tbl ∈ Tbls, (PMF.uniformOfFintype _).toOuterMeasure
          {g : Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin m |
            ¬ ∀ j : Fin J, ∃ m' : Fin M, ∀ i : Fin (p.waveLength - 1 + 1),
              g ⟨j * M + m', blk_lt j.isLt m'.isLt⟩ i ∈
                Sr tbl ((j * M + m') * (p.waveLength - 1 + 1) + i)}
        ≤ ∑ _tbl ∈ Tbls, (J : ℝ≥0∞) *
            Steelhead.Coin.badBlockBoundAt (Fin m) (e * (k + s - n)) (p.waveLength - 1 + 1) ^ M :=
          Finset.sum_le_sum fun tbl htbl => windowsFail_le (Sr tbl) fun r hr => by
            have := card_hits_ge (hsup tbl htbl) (hfloor r hr)
            simpa only [Fintype.card_fin] using this
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem scheduledIntegrity : ScheduledIntegrity := by
  intro Validator BlockId Payload _ _ _ P _ honest p σ Par B upd C₀ U V K Rn wk K'
  obtain ⟨h1, h2⟩ := deliverLeaders_nodup (U := U) (wk := wk) (Rn.ledgerUpto K')
  exact ⟨h1, h2, fun b hb => (mem_deliverLeaders hb).1⟩

/-- Two scheduled runs' ledgers, to heights each has closed, are
prefix-comparable. -/
theorem ledger_comparable {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    [P.Mechanised] {q : ℕ} [P.Quorate q] {honest : Finset Validator} {f : ℕ} {p : Params}
    {σ : VoteSel Validator BlockId Payload P honest} {Par : Barnacle.Params}
    {B : Barnacle.Boundary Validator}
    {upd : Barnacle.UpdateRule (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl))}
    {C₀ : Barnacle.Config Validator} (ht : p.Tolerates honest f q)
    (hanc : Barnacle.Anchored (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) upd)
    {U : BlockRecord Validator BlockId Payload P honest} {V₁ V₂ : U.View} {K₁ K₂ : ℕ}
    (R₁ : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀
      U V₁ K₁)
    (R₂ : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀
      U V₂ K₂)
    {K'₁ K'₂ : ℕ} (h₁ : K'₁ ≤ K₁) (h₂ : K'₂ ≤ K₂) (h : K'₁ ≤ K'₂) :
    R₁.ledgerUpto K'₁ <+: R₂.ledgerUpto K'₂ := by
  obtain ⟨hag, hpre, -⟩ := Barnacle.Ledger.holds _ _ _ _ (Scheme.agree ht) Scheme.commitsCandidate
    Par B upd C₀ hanc
  rw [(hag U V₁ V₂ K₁ K₂ R₁ R₂).2 K'₁ (by omega)]
  exact hpre U V₂ K₂ R₂ K'₁ K'₂ h

theorem scheduledAgreed : ScheduledAgreed := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ Par B upd C₀ ht hanc U V₁ V₂ K₁ K₂
    R₁ R₂ wk K'₁ K'₂ h₁ h₂
  have hc : runDeliver R₁ wk K'₁ <+: runDeliver R₂ wk K'₂ ∨
      runDeliver R₂ wk K'₂ <+: runDeliver R₁ wk K'₁ := by
    rcases le_total K'₁ K'₂ with h | h
    · exact Or.inl (deliverLeaders_prefix (ledger_comparable ht hanc R₁ R₂ h₁ h₂ h))
    · exact Or.inr (deliverLeaders_prefix (ledger_comparable ht hanc R₂ R₁ h₂ h₁ h))
  have hn₁ := (deliverLeaders_nodup (U := U) (wk := wk) (R₁.ledgerUpto K'₁)).2
  have hn₂ := (deliverLeaders_nodup (U := U) (wk := wk) (R₂.ledgerUpto K'₂)).2
  refine ⟨fun x y h => h.not_swap hc hn₁ hn₂, fun x y h hy => h.of_comparable hc hn₁ hy,
    fun h b hb => ?_⟩
  exact (deliverLeaders_prefix (ledger_comparable ht hanc R₁ R₂ h₁ h₂ h)).subset hb

theorem scheduledValidity : ScheduledValidity := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest p σ Par B upd C₀ U V K Rn wk T holds built
    hTh hqT hwr hmono hbuilt m t K' hm hmT hmr hheld hA
  obtain ⟨A, hA, hAU, hAr⟩ := hA
  exact mem_deliverLeaders_of hA hm
    (reachesW_of_weakRule hqT hwr hmono hbuilt hmr hheld A hAU hAr) (hTh hmT)

theorem anchorLedger : AnchorLedger := by
  intro Validator BlockId Payload _ _ _ P _ honest p σ Par upd C₀ U V K Rn k hk
  -- starts grow by at least one per configuration
  have hstart : ∀ j, j ≤ K → j ≤ Rn.start j := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih =>
      intro hj
      have hs := Rn.start_succ j (by omega)
      have hthr := (Rn.anchor_commits j (by omega)).2
      have hpos := (Rn.bounds j).2.1
      have := ih (by omega)
      change Rn.start (j + 1) = (Rn.cfg j).roundOf (Rn.anchor j) at hs
      omega
  obtain ⟨⟨A, hA⟩, hthr⟩ := Rn.anchor_commits k hk
  have hdec := Rn.closed k hk (Rn.anchor k) (by omega) le_rfl
  rw [hA] at hdec
  obtain ⟨hAU, hAr, -⟩ := Scheme.commitsCandidate _ _ _ _ _ hdec
  have hs := Rn.start_succ k hk
  change Rn.start (k + 1) = (Rn.cfg k).roundOf (Rn.anchor k) at hs
  have hk' := hstart k (by omega)
  refine ⟨A, ?_, hAU, ?_⟩
  · refine List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
    unfold Barnacle.Run.rangeLedger Barnacle.ledgerOf
    refine List.mem_filterMap.mpr ⟨Rn.anchor k, List.mem_range'_1.mpr ⟨?_, ?_⟩, hA⟩
    · exact (Rn.cfg k).cum_le_iff_le_roundOf.mpr (by omega)
    · rw [hs]
      have h1 := (Rn.cfg k).lt_cum_iff_roundOf_lt.mpr
        (show (Rn.cfg k).roundOf (Rn.anchor k) < (Rn.cfg k).roundOf (Rn.anchor k) + 1 by omega)
      have h2 : (Rn.cfg k).cum (Rn.start k + 1) ≤ Rn.anchor k :=
        (Rn.cfg k).cum_le_iff_le_roundOf.mpr (by omega)
      omega
  · change (U.block A).round = (Rn.cfg k).sched.slotRound (Rn.anchor k) at hAr
    rw [hAr, Barnacle.Config.sched_slotRound]
    omega

theorem holds : Statement :=
  ⟨checkpointsResponsive, checkpointsCrash, scheduledCrash, hammerHeadComposed, aimdComposed,
    asyncComposed, asyncHammerHeadComposed, scheduledIntegrity, scheduledAgreed, scheduledValidity,
    anchorLedger⟩

end Compose

end Scheme

end LeanDag
