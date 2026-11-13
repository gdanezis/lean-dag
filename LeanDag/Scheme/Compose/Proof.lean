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
import LeanDag.Barnacle.Helpers.Chains
import LeanDag.Barnacle.Chains.Proof
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
(`Integration.commitFinalized_barnacle_scheme`). Theorem 2 reads Integrity
and Agreement off the ledger, and Validity off a commit each configuration
makes inside its own range (`Barnacle.ledger_commit_of_window`), placed
under the coverage horizon by the start bound the run comes with.
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
    let ⟨Rn, _⟩ := scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE h₀
      hC₀ U (Pr.view v) N (hcov v) (hgood v) K hK
    ⟨Rn⟩
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
    let ⟨Rn, _⟩ := scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE h₀
      hC₀ U (Pr.view v) N (hcov v) (hgood v) K hK
    ⟨Rn⟩
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
      (safeHeadRuns_of_windows p U rfl dflt id (safeAt p U) (fun _ _ h => h) g hNJ hwin) (hcov v)
      K hK
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

theorem composedValidity : ComposedValidity := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ rel Par B upd C₀ U V K c δ Rn wk T
    holds built m t ht hTh hqT hwr hmono hbuilt hm hmT hmr hheld hK hδ hint hlive hgood hcov
  obtain ⟨κ, L, hκ, hdec, hL⟩ := Barnacle.ledger_commit_of_window (Scheme.agree ht) Rn hK hlive
    hgood hcov hδ hint le_rfl
  obtain ⟨hLU, hLr, -⟩ := Scheme.commitsCandidate _ _ _ _ _ hdec
  have hst := Barnacle.le_start Rn (t + 2) (by omega)
  change (U.block L).round = (Rn.cfg (t + 2)).sched.slotRound κ at hLr
  rw [Barnacle.Config.sched_slotRound] at hLr
  exact scheduledValidity Validator BlockId Payload P q honest p σ Par B upd C₀ U V K Rn wk T
    holds built hTh hqT hwr hmono hbuilt m t K hm hmT hmr hheld ⟨L, hL, hLU, by omega⟩

/-- Responsive goodness up to a round holds up to any earlier round. -/
theorem reactiveGood_mono {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Nonempty Validator] [LinearOrder BlockId]
    {P : Validity Validator BlockId Payload} [P.Mechanised] {honest : Finset Validator}
    {p : Params} {σ : VoteSel Validator BlockId Payload P honest} {rel : Reliability Validator}
    {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest} {Rnd N N' : ℕ}
    (h : reactiveGood p σ rel S U Rnd N) (hN : N' ≤ N) : reactiveGood p σ rel S U Rnd N' := by
  obtain ⟨T, hq, hTh, N'', rs, hgst, hto, hW⟩ := h
  exact ⟨T, hq, hTh, N'', rs, hgst, hto, le_trans hN hW⟩

/-- **Responsive scheduled runs broadcast atomically** when each
configuration from the third on is live, good through its validity window,
and covered there. -/
theorem broadcasts_of {Validator BlockId Payload ι : Type} [Fintype Validator]
    [DecidableEq Validator] [Nonempty Validator] [LinearOrder BlockId]
    {P : Validity Validator BlockId Payload} [P.Mechanised] {q : ℕ} [P.Quorate q]
    {honest : Finset Validator} {f : ℕ} {p : Params}
    {σ : VoteSel Validator BlockId Payload P honest} {rel : Reliability Validator}
    {Par : Barnacle.Params} {B : Barnacle.Boundary Validator}
    {upd : Barnacle.UpdateRule (schemeLiveReactive p σ rel).toBaseRule}
    {C₀ : Barnacle.Config Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : ι → U.View} {K c δ : ℕ} (ht : p.Tolerates honest f q)
    (hanc : Barnacle.Anchored (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) upd)
    (Rn : ∀ i, Barnacle.Run (schemeLiveReactive p σ rel).toBaseRule Par B upd C₀ U (V i) K)
    (wk : BlockId → Finset BlockId) {T : Finset Validator}
    {holds : Validator → ℕ → Finset BlockId} {built : Validator → ℕ → ℕ}
    (hTh : T ⊆ honest) (hqT : Fintype.card Validator < q + T.card)
    (hwr : WeakRule U wk T holds built) (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (hbuilt : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v →
      (U.block b).round ≤ built v (U.block b).round) (hδ : 1 ≤ δ)
    (hwin : ∀ i t, t + 2 < K → δ + c ≤ ((Rn i).cfg (t + 2)).interval ∧
      (schemeLiveReactive p σ rel).LiveOn ((Rn i).cfg (t + 2)).sched c ∧
      reactiveGood p σ rel ((Rn i).cfg (t + 2)).sched U ((Rn i).start (t + 2) + δ)
        ((Rn i).start (t + 2) + δ + c + (p.waveLength - 1 + 1)) ∧
      (schemeLiveReactive p σ rel).toBaseRule.CoversUpto U (V i)
        ((Rn i).start (t + 2) + δ + c + (p.waveLength - 1 + 1))) :
    Broadcasts Rn wk T holds := by
  refine ⟨fun i K' => scheduledIntegrity Validator BlockId Payload P honest p σ Par B upd C₀ U
      (V i) K (Rn i) wk K',
    fun i j K₁ K₂ h₁ h₂ => scheduledAgreed Validator BlockId Payload P q honest f p σ Par B upd C₀
      ht hanc U (V i) (V j) K K (Rn i) (Rn j) wk K₁ K₂ h₁ h₂,
    fun i m t hm hmT hmr hheld hK => ?_⟩
  obtain ⟨hint, hlive, hgood, hcov⟩ := hwin i t hK
  exact composedValidity Validator BlockId Payload P q honest f p σ rel Par B upd C₀ U (V i) K c δ
    (Rn i) wk T holds built m t ht hTh hqT hwr hmono hbuilt hm hmT hmr hheld hK hδ hint hlive
    hgood hcov

theorem hammerHeadBroadcast : HammerHeadBroadcast := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel M E vm ht hc hsch
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro B score C₀ δ hkeep hQ h₀ hC₀ hδ hint U C Pr N hcov hall wk T holds built hTh hqT hwr
    hmono hbuilt K hK
  have hRE := Schedules.hammerHeadReactive n hn BlockId Payload P q honest f p σ rel ht hc hsch
    B score C₀ δ hkeep hQ
  have hrun := fun v => scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE
    h₀ hC₀ U (Pr.view v) N (hcov v) (fun K' Rn hQ' => Or.inl (hall v K' Rn K' le_rfl hQ')) K
    (by omega)
  let Rn := fun v => (hrun v).choose
  obtain ⟨hcert, hlv, hbound⟩ := hsch
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hD := Schedules.reactiveDescends (Fin n) BlockId Payload P honest p σ rel
    (by rw [hcard]; exact hc) (by rw [hcard]; exact hlv)
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by have := hc.1; omega
  have hbase : ∀ T : Finset (Fin n), Fintype.card (Fin n) ≤ T.card + rel.slack →
      Barnacle.HeadsRun (Barnacle.roundRobin n hn) T (schemeLiveReactive p σ rel).waveLength
        (n + p.waveLength - 1) := fun T hT => by
    have := Barnacle.roundRobin_headsRun n hn T _ (schemeLiveReactive p σ rel).waveLength
      (by simpa using hT) (by rw [hwl]; exact hbound)
    rwa [hwl] at this ⊢
  have hw0 : 0 < (schemeLiveReactive p σ rel).waveLength := by rw [hwl]; have := hc.1; omega
  have hkI : ∀ C' b U' V' v A, (Adaptive.rule score C' b U' V' v A).1.interval = C'.interval := by
    intro C' b U' V' v A
    unfold Adaptive.rule
    split
    · exact (hkeep _ _ _ _).2
    · rfl
  refine ⟨Rn, broadcasts_of (c := n + p.waveLength - 1) ht (Adaptive.Score.rule_anchored score)
      Rn wk hTh
      (by rw [hcard]; exact hqT) hwr hmono hbuilt hδ fun i t ht2 => ?_,
    fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  · have hperm := Barnacle.cfg_keeps (Rn i) (Adaptive.Score.rule_keeps score _ hQ) hC₀ (t + 2)
      (by omega)
    obtain ⟨π, hπ⟩ := hperm
    have hst := Barnacle.start_mono (Rn i) (show t + 2 ≤ K by omega) le_rfl
    have hsK := (hrun i).choose_spec.1
    have hmx := le_max_right (B.maxInterval + 1) δ
    unfold Barnacle.horizonFrom at hK
    refine ⟨by rw [Barnacle.interval_eq (Rn i) hkI _ (by omega)]; exact hint,
      Barnacle.liveOn_of_permuted_heads _ hD hw0 hbase π hπ,
      reactiveGood_mono (reactiveGood_of_crashGood
        (hall i K (Rn i) (t + 2) (by omega) ⟨π, hπ⟩)) ?_, fun b hb hr => hcov i b hb ?_⟩
    · change _ ≤ _ + _ + _ + (p.waveLength - 1 + 1)
      omega
    · change (U.block b).round ≤ _ at hr
      change Barnacle.Run.start (Rn i) K ≤ _ at hsK
      change _ + _ + (p.waveLength - 1 + 1) + δ ≤ N at hK
      show (U.block b).round ≤ N
      omega
  · exact Integration.commitFinalized_barnacle_scheme M E vm ht
      (Adaptive.Score.rule_anchored score) Pr Rn hk hcfg h hlo hhi

theorem aimdBroadcast : AimdBroadcast := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel M E vm ht hc hsch
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro B Bd lead hl hlead C₀ δ h₀ hC₀ hδ hint U C Pr N hcov hall wk T holds built hTh hqT hwr
    hmono hbuilt K hK
  have hRE := Schedules.aimdReactive n hn BlockId Payload P q honest f p σ rel ht hc hsch
    B Bd lead hl hlead C₀ δ
  have hrun := fun v => scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE
    h₀ hC₀ U (Pr.view v) N (hcov v) (fun K' Rn hQ' => Or.inl (hall v K' Rn K' le_rfl hQ')) K
    (by omega)
  let Rn := fun v => (hrun v).choose
  obtain ⟨hcert, hlv, hbound⟩ := hsch
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hD := Schedules.reactiveDescends (Fin n) BlockId Payload P honest p σ rel
    (by rw [hcard]; exact hc) (by rw [hcard]; exact hlv)
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by have := hc.1; omega
  have hbase : ∀ T : Finset (Fin n), Fintype.card (Fin n) ≤ T.card + rel.slack →
      Barnacle.HeadsRun (Barnacle.roundRobin n hn) T (schemeLiveReactive p σ rel).waveLength
        (n + p.waveLength - 1) := fun T hT => by
    have := Barnacle.roundRobin_headsRun n hn T _ (schemeLiveReactive p σ rel).waveLength
      (by simpa using hT) (by rw [hwl]; exact hbound)
    rwa [hwl] at this ⊢
  have hw0 : 0 < (schemeLiveReactive p σ rel).waveLength := by rw [hwl]; have := hc.1; omega
  have hkeep : Barnacle.UpdKeeps (Barnacle.Aimd.rule (schemeLiveReactive p σ rel).toBaseRule B
      lead hl) (fun C => C.head = Barnacle.roundRobin n hn) := by
    intro C' b U' V' v A _
    funext ρ
    exact hlead ρ
  have hkI : ∀ C' b U' V' v A, Barnacle.Config.interval
      (Barnacle.Aimd.rule (schemeLiveReactive p σ rel).toBaseRule B lead hl C' b U' V' v A).1 =
        C'.interval := fun _ _ _ _ _ _ => rfl
  refine ⟨Rn, broadcasts_of (c := n + p.waveLength - 1) ht
      (Barnacle.Aimd.holds _ _ _ _ B lead hl).2.2.2.2 Rn wk hTh
      (by rw [hcard]; exact hqT) hwr hmono hbuilt hδ fun i t ht2 => ?_,
    fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  · have hhd := Barnacle.cfg_keeps (Rn i) hkeep hC₀ (t + 2) (by omega)
    have hst := Barnacle.start_mono (Rn i) (show t + 2 ≤ K by omega) le_rfl
    have hsK := (hrun i).choose_spec.1
    have hmx := le_max_right (B.maxInterval + 1) δ
    unfold Barnacle.horizonFrom at hK
    refine ⟨by rw [Barnacle.interval_eq (Rn i) hkI _ (by omega)]; exact hint,
      Barnacle.liveOn_of_headsRun _ hD hw0 (by rw [hhd]; exact hbase),
      reactiveGood_mono (reactiveGood_of_crashGood
        (hall i K (Rn i) (t + 2) (by omega) hhd)) ?_, fun b hb hr => hcov i b hb ?_⟩
    · change _ ≤ _ + _ + _ + (p.waveLength - 1 + 1)
      omega
    · change (U.block b).round ≤ _ at hr
      change Barnacle.Run.start (Rn i) K ≤ _ at hsK
      change _ + _ + (p.waveLength - 1 + 1) + δ ≤ N at hK
      show (U.block b).round ≤ N
      omega
  · exact Integration.commitFinalized_barnacle_scheme M E vm ht
      (Barnacle.Aimd.holds _ _ _ _ B lead hl).2.2.2.2 Pr Rn hk hcfg h hlo hhi

/-- Asynchronous goodness from a round to another holds over any smaller
window. -/
theorem asyncGood_mono {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    {honest : Finset Validator} {p : Params} {σ : VoteSel Validator BlockId Payload P honest}
    {rel : Reliability Validator} {c₀ : ℕ} {S : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {Rnd Rnd' N N' : ℕ}
    (h : asyncGood p σ rel c₀ S U Rnd N) (hR : Rnd ≤ Rnd') (hN : N' ≤ N) :
    asyncGood p σ rel c₀ S U Rnd' N' := by
  obtain ⟨T, hq, hTh, hpop, hh⟩ := h
  exact ⟨T, hq, hTh, fun r hr => hpop r (le_trans hr hN),
    fun r hr hrN => hh r (le_trans hR hr) (by omega)⟩

/-- **Asynchronous scheduled runs broadcast atomically**: when every
configuration the rule keeps is good from round `0` to `N` and its interval
holds a round and the gap, runs of height `K` exist on every view and
satisfy `Broadcasts`. -/
theorem asyncBroadcastRuns {Validator BlockId Payload ι : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    [P.Mechanised] {q : ℕ} [P.Quorate q] {honest : Finset Validator} {f : ℕ} {p : Params}
    {σ : VoteSel Validator BlockId Payload P honest} {rel : Reliability Validator} {c₀ : ℕ}
    (ht : p.Tolerates honest f q) (hc : p.CertFits q)
    (hcm : p.commitThreshold ≤ Fintype.card Validator - rel.slack)
    {B : Barnacle.Params} {Bd : Barnacle.Boundary Validator}
    {upd : Barnacle.UpdateRule (schemeLiveAsync p σ rel c₀).toBaseRule}
    {C₀ : Barnacle.Config Validator} {Q : Barnacle.Config Validator → Prop}
    (hbnd : Barnacle.UpdBounded B upd) (hkeep : Barnacle.UpdKeeps upd Q)
    (hkI : ∀ C b U' V' v A, (upd C b U' V' v A).1.interval = C.interval)
    (hanc : Barnacle.Anchored (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) upd)
    (h₀ : C₀.InBounds B) (hQ₀ : Q C₀) (hint : 1 + c₀ ≤ C₀.interval)
    {U : BlockRecord Validator BlockId Payload P honest} {V : ι → U.View} {N : ℕ}
    (hcov : ∀ i, (schemeLiveAsync p σ rel c₀).toBaseRule.CoversUpto U (V i) N)
    (hgood : ∀ C : Barnacle.Config Validator, C.InBounds B → Q C →
      asyncGood p σ rel c₀ C.sched U 0 N)
    (wk : BlockId → Finset BlockId) {T : Finset Validator}
    {holds : Validator → ℕ → Finset BlockId} {built : Validator → ℕ → ℕ}
    (hTh : T ⊆ honest) (hqT : Fintype.card Validator < q + T.card)
    (hwr : WeakRule U wk T holds built) (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (hbuilt : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v →
      (U.block b).round ≤ built v (U.block b).round)
    (K : ℕ) (hK : Barnacle.horizon B (schemeLiveAsync p σ rel c₀) c₀ K + 1 ≤ N) :
    ∃ Rn : ∀ i, Barnacle.Run (schemeLiveAsync p σ rel c₀).toBaseRule B Bd upd C₀ U (V i) K,
      Broadcasts Rn wk T holds := by
  have hlive := fun C => (Schedules.asyncConfigLive Validator BlockId Payload P q honest p σ rel c₀
    hc hcm C).1
  have hrun := fun i => Barnacle.everyHeight_bound (Q := Q) (B := Bd) (Scheme.agree ht) hbnd hkeep
    (fun C _ _ => hlive C) h₀ hQ₀ (hcov i) hgood (Nat.zero_le 1) K (by omega)
  let Rn := fun i => (hrun i).choose
  refine ⟨Rn, fun i K' => scheduledIntegrity Validator BlockId Payload P honest p σ B Bd upd C₀ U
      (V i) K (Rn i) wk K',
    fun i j K₁ K₂ h₁ h₂ => scheduledAgreed Validator BlockId Payload P q honest f p σ B Bd upd C₀
      ht hanc U (V i) (V j) K K (Rn i) (Rn j) wk K₁ K₂ h₁ h₂,
    fun i m t hm hmT hmr hheld hK2 => ?_⟩
  have hQt := Barnacle.cfg_keeps (Rn i) hkeep hQ₀ (t + 2) (by omega)
  have hst := Barnacle.start_mono (Rn i) (show t + 2 ≤ K by omega) le_rfl
  have hsK := (hrun i).choose_spec.1
  unfold Barnacle.horizon at hK
  have hM : (Rn i).start (t + 2) + 1 + c₀ + (schemeLiveAsync p σ rel c₀).waveLength ≤ N := by
    change Barnacle.Run.start (Rn i) K ≤ _ at hsK
    omega
  obtain ⟨κ, L, hκ, hdec, hL⟩ := Barnacle.ledger_commit_of_window (Scheme.agree ht) (Rn i)
    (show t + 2 < K by omega) (hlive _)
    (asyncGood_mono (hgood _ ((Rn i).bounds (t + 2)) hQt) (Nat.zero_le _) hM)
    (fun b hb hr => hcov i b hb (le_trans hr hM)) le_rfl
    (by rw [Barnacle.interval_eq (Rn i) hkI _ (by omega)]; exact hint) le_rfl
  obtain ⟨hLU, hLr, -⟩ := Scheme.commitsCandidate _ _ _ _ _ hdec
  have hst' := Barnacle.le_start (Rn i) (t + 2) (by omega)
  change (U.block L).round = ((Rn i).cfg (t + 2)).sched.slotRound κ at hLr
  rw [Barnacle.Config.sched_slotRound] at hLr
  exact scheduledValidity Validator BlockId Payload P q honest p σ B Bd upd C₀ U (V i) K (Rn i) wk
    T holds built hTh hqT hwr hmono hbuilt m t K hm hmT hmr hheld ⟨L, hL, hLU, by omega⟩

open scoped ENNReal in
theorem asyncBroadcast : AsyncBroadcast := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel Ms E vm J M c dflt ht hc hcm
  haveI : Nonempty (Fin n) := ⟨dflt⟩
  intro B Bd lead hl hlead C₀ hC₀ hint U T Nr qp ac hq hTh hqp N hN C Pr hcov hNJ hfloor wk Tr
    holds built hTrh hqTr hwr hmono hbuilt K hK
  refine le_trans (MeasureTheory.measure_mono fun g hg => ?_) (windowsFail_le (safeAt p U) hfloor)
  simp only [Set.mem_setOf_eq] at hg ⊢
  intro hwin
  apply hg
  have hsafe := safeHeadRuns_of_windows p U rfl dflt id (safeAt p U) (fun _ _ h => h) g hNJ hwin
  have hkeep : Barnacle.UpdKeeps (Barnacle.Aimd.rule
      (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
      (lead (coinHead dflt g)) (hl _))
      (fun C => C.head = coinHead dflt g) := by
    intro C' b U' V' v A _
    funext ρ
    exact hlead _ ρ
  have hanc : Barnacle.Anchored (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl))
      (Barnacle.Aimd.rule (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
        (lead (coinHead dflt g)) (hl _)) :=
    (Barnacle.Aimd.holds _ _ _ _ B _ (hl (coinHead dflt g))).2.2.2.2
  obtain ⟨Rn, hRn⟩ := asyncBroadcastRuns (V := Pr.view) ht hc hcm (Bd := Bd)
    (Q := fun C => C.head = coinHead dflt g)
    (fun C b U V v A hC => ⟨fun _ => Barnacle.Aimd.count_le _ _ _ _, hC.2⟩) hkeep
    (fun _ _ _ _ _ _ => rfl) hanc (hC₀ _).1 (hC₀ _).2 (hint _) hcov
    (fun C' _ hCh => ⟨T, hq, hTh, fun r hr => ac.toAsyncPace.populated hqp r (le_trans hr hN),
      fun r hr hrN => by
        obtain ⟨ρ, h1, h2, h3⟩ := hsafe r hr hrN
        refine ⟨ρ, h1, h2, fun i hi κ hκ hfirst => ?_⟩
        rw [Barnacle.eq_cum_of_first C' hκ hfirst, Barnacle.Config_leader_head, hCh]
        exact h3 i hi⟩)
    wk hTrh (by rw [Fintype.card_fin]; exact hqTr) hwr hmono hbuilt K hK
  refine ⟨Rn, hRn, fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  exact Integration.commitFinalized_barnacle_scheme Ms E vm ht hanc Pr Rn hk hcfg h hlo hhi

open scoped ENNReal in
theorem asyncHammerHeadBroadcast : AsyncHammerHeadBroadcast := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel Ms E vm J M m k e s dflt Tbls ht hc
    hcm hsup
  haveI : Nonempty (Fin m) := ⟨dflt⟩
  intro B score C₀ hkeep hQ hC₀ hint U T Nr qp ac hq hTh hqp N hN C Pr hcov hNJ hfloor wk Tr
    holds built hTrh hqTr hwr hmono hbuilt K hK
  let Sr : (Fin m → Fin n) → ℕ → Finset (Fin m) := fun tbl r =>
    Finset.univ.filter fun j => tbl j ∈ safeAt p U r
  have hsub : {g : Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin m | ¬ ∃ Rn : ∀ v,
        Barnacle.Run (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
          Barnacle.Boundary.atThreshold (Adaptive.rule (score (coinHead dflt g)))
          (C₀ (coinHead dflt g)) U (Pr.view v) K,
        Broadcasts Rn wk Tr holds ∧
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
    have hsafe := fun tbl htbl => safeHeadRuns_of_windows p U rfl dflt tbl (Sr tbl)
      (fun r x hx => (Finset.mem_filter.mp hx).2) g hNJ (hno tbl htbl)
    have hkI : ∀ C' b U' V' v A,
        (Adaptive.rule (score (coinHead dflt g)) C' b U' V' v A).1.interval = C'.interval := by
      intro C' b U' V' v A
      unfold Adaptive.rule
      split
      · exact (hkeep _ _ _ _ _).2
      · rfl
    have hanc := Adaptive.Score.rule_anchored (score (coinHead dflt g))
    obtain ⟨Rn, hRn⟩ := asyncBroadcastRuns (V := Pr.view) ht hc hcm
      (Bd := Barnacle.Boundary.atThreshold)
      (Q := fun C => ∃ tbl ∈ Tbls, C.head = fun ρ => tbl (coinHead dflt g ρ))
      (Adaptive.Score.rule_bounded B _ (hkeep _)) (Adaptive.Score.rule_keeps _ _ (hQ _))
      hkI hanc (hC₀ _).1 (hC₀ _).2 (hint _) hcov
      (fun C' _ ⟨tbl, htbl, hCh⟩ => ⟨T, hq, hTh,
        fun r hr => ac.toAsyncPace.populated hqp r (le_trans hr hN), fun r hr hrN => by
          obtain ⟨ρ, h1, h2, h3⟩ := hsafe tbl htbl r hr hrN
          refine ⟨ρ, h1, h2, fun i hi κ hκ hfirst => ?_⟩
          rw [Barnacle.eq_cum_of_first C' hκ hfirst, Barnacle.Config_leader_head, hCh]
          exact h3 i hi⟩)
      wk hTrh (by rw [Fintype.card_fin]; exact hqTr) hwr hmono hbuilt K hK
    refine ⟨Rn, hRn, fun k' hk v₀ hcfg κ L h hlo hhi => ?_⟩
    exact Integration.commitFinalized_barnacle_scheme Ms E vm ht hanc Pr Rn hk hcfg h hlo hhi
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

theorem chainsBroadcast : ChainsBroadcast := by
  intro n hn BlockId Payload Value _ P _ q _ honest f p σ rel M E vm ht hc hcm
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro B Bd upd Q C₀ δ c₀ hanc hbnd hkeep hkI hC h₀ hQ₀ hδ hint U C Pr N hcov hall wk T holds
    built hTh hqT hwr hmono hbuilt K hK
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hRE := Schedules.chainsReactive (Fin n) BlockId Payload P q honest f p σ rel c₀ ht
    (by rw [hcard]; exact hc) (by rw [hcard]; exact hcm) B Bd upd Q hbnd hkeep
    (fun C hQ => hC C hQ) C₀ δ
  have hrun := fun v => scheduledCrash (Fin n) BlockId Payload P honest p σ rel B _ _ C₀ _ _ δ hRE
    h₀ hQ₀ U (Pr.view v) N (hcov v) (fun K' Rn hQ' => Or.inl (hall v K' Rn K' le_rfl hQ')) K
    (by omega)
  let Rn := fun v => (hrun v).choose
  have hD := Schedules.reactiveDescends (Fin n) BlockId Payload P honest p σ rel
    (by rw [hcard]; exact hc) (by rw [hcard]; exact hcm)
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by have := hc.1; omega
  refine ⟨Rn, broadcasts_of (c := c₀ + 2 * p.waveLength) ht hanc Rn wk hTh
      (by rw [hcard]; exact hqT) hwr hmono hbuilt hδ fun i t ht2 => ?_,
    fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  · have hQt := Barnacle.cfg_keeps (Rn i) hkeep hQ₀ (t + 2) (by omega)
    have hst := Barnacle.start_mono (Rn i) (show t + 2 ≤ K by omega) le_rfl
    have hsK := (hrun i).choose_spec.1
    have hmx := le_max_right (B.maxInterval + 1) δ
    unfold Barnacle.horizonFrom at hK
    refine ⟨by rw [Barnacle.interval_eq (Rn i) hkI _ (by omega)]; exact hint,
      Barnacle.liveOn_of_boundedChains _ hD.indirect hD.decisive
        (by rw [hwl]; exact hC _ hQt) (by rw [hwl]),
      reactiveGood_mono (reactiveGood_of_crashGood
        (hall i K (Rn i) (t + 2) (by omega) hQt)) ?_, fun b hb hr => hcov i b hb ?_⟩
    · change _ ≤ _ + _ + _ + (p.waveLength - 1 + 1)
      omega
    · change (U.block b).round ≤ _ at hr
      change Barnacle.Run.start (Rn i) K ≤ _ at hsK
      change _ + _ + (p.waveLength - 1 + 1) + δ ≤ N at hK
      show (U.block b).round ≤ N
      omega
  · exact Integration.commitFinalized_barnacle_scheme M E vm ht hanc Pr Rn hk hcfg h hlo hhi

/-- **Scheduled runs broadcast atomically when their ledgers reach late
enough leaders**: Integrity and Agreement off the ledger, and Validity for
`t + 2 < K` from a ledger leader of round `t + 2` or later. -/
theorem broadcasts_of_ledger {Validator BlockId Payload ι : Type} [Fintype Validator]
    [DecidableEq Validator] [Nonempty Validator] [LinearOrder BlockId]
    {P : Validity Validator BlockId Payload} [P.Mechanised] {q : ℕ} [P.Quorate q]
    {honest : Finset Validator} {f : ℕ} {p : Params}
    {σ : VoteSel Validator BlockId Payload P honest} {rel : Reliability Validator}
    {Par : Barnacle.Params} {B : Barnacle.Boundary Validator}
    {upd : Barnacle.UpdateRule (schemeLiveReactive p σ rel).toBaseRule}
    {C₀ : Barnacle.Config Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : ι → U.View} {K : ℕ} (ht : p.Tolerates honest f q)
    (hanc : Barnacle.Anchored (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) upd)
    (Rn : ∀ i, Barnacle.Run (schemeLiveReactive p σ rel).toBaseRule Par B upd C₀ U (V i) K)
    (wk : BlockId → Finset BlockId) {T : Finset Validator}
    {holds : Validator → ℕ → Finset BlockId} {built : Validator → ℕ → ℕ}
    (hTh : T ⊆ honest) (hqT : Fintype.card Validator < q + T.card)
    (hwr : WeakRule U wk T holds built) (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (hbuilt : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v →
      (U.block b).round ≤ built v (U.block b).round)
    (hled : ∀ i t, t + 2 < K →
      ∃ A ∈ (Rn i).ledgerUpto K, A ∈ U.ids ∧ t + 2 ≤ (U.block A).round) :
    Broadcasts Rn wk T holds :=
  ⟨fun i K' => scheduledIntegrity Validator BlockId Payload P honest p σ Par B upd C₀ U
      (V i) K (Rn i) wk K',
    fun i j K₁ K₂ h₁ h₂ => scheduledAgreed Validator BlockId Payload P q honest f p σ Par B upd C₀
      ht hanc U (V i) (V j) K K (Rn i) (Rn j) wk K₁ K₂ h₁ h₂,
    fun i m t hm hmT hmr hheld hK => scheduledValidity Validator BlockId Payload P q honest p σ
      Par B upd C₀ U (V i) K (Rn i) wk T holds built hTh hqT hwr hmono hbuilt m t K hm hmT hmr
      hheld (hled i t hK)⟩

open MeasureTheory in
open scoped ENNReal in
theorem shuffleBroadcast : ShuffleBroadcast := by
  intro n BlockId Payload Value _ P _ q _ honest f p σ rel M E vm J Mb dflt ht hc hcm hwn
  haveI : Nonempty (Fin n) := ⟨dflt⟩
  intro B Bd upd C₀ δ hanc hbnd hkeep hkI h₀ hδ hint U C Pr N hN hcov hall wk T holds built hTh
    hqT hwr hmono hbuilt K hK
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hw0 : 0 < p.waveLength := by have := hc.1; omega
  have hbound := Barnacle.Chains.shuffleChains (Fin n) p.waveLength J Mb rel.slack rel.slack dflt
    hw0 (by rw [hcard]; exact hwn) N (by rw [hcard]; exact hN)
  simp only [hcard] at hbound
  refine le_trans (measure_mono fun g hg => ?_) hbound
  simp only [Set.mem_setOf_eq] at hg ⊢
  intro hB
  apply hg
  -- the runs, on the rule read up to the horizon
  have hD := Schedules.reactiveDescends (Fin n) BlockId Payload P honest p σ rel
    (by rw [hcard]; exact hc) (by rw [hcard]; exact hcm)
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by omega
  have hwR : 0 < (schemeLiveReactive p σ rel).waveLength := by rw [hwl]; exact hw0
  have hwu : ((schemeLiveReactive p σ rel).upTo N).waveLength =
      (schemeLiveReactive p σ rel).waveLength := rfl
  have hBC : ∀ C' : Barnacle.Config (Fin n), C'.head = Barnacle.blockHead dflt g →
      C'.BoundedChainsUpto rel.slack rel.slack (schemeLiveReactive p σ rel).waveLength
        (2 * (Mb * n)) N := by
    intro C' hC'
    rw [hwl]
    exact hB C' (fun ρ => by rw [hC'])
  have hcg : 2 * (Mb * n) + 2 * (schemeLiveReactive p σ rel).waveLength ≤
      2 * (Mb * n) + 2 * p.waveLength := by rw [hwl]
  have hrun : ∀ v, ∃ Rn : Barnacle.Run ((schemeLiveReactive p σ rel).upTo N).toBaseRule B Bd
      (upd g) (C₀ g) U (Pr.view v) K,
      Rn.start K ≤ K * (max (B.maxInterval + 1) δ + (2 * (Mb * n) + 2 * p.waveLength)) ∧
        (Rn.cfg K).head = Barnacle.blockHead dflt g := fun v =>
    Barnacle.everyHeight_from (R := (schemeLiveReactive p σ rel).upTo N)
      (Q := fun C' => C'.head = Barnacle.blockHead dflt g)
      (Scheme.agree ht) (hbnd g) (hkeep g)
      (fun C' _ hQ => Barnacle.liveOn_upTo_of_boundedChainsUpto C' hD.indirect hD.decisive
        (hBC C' hQ) hcg)
      (fun C' _ hQ => Barnacle.settlesBelow_upTo_of_boundedChainsUpto C' hD.indirect hD.decisive
        hwR (hBC C' hQ) hcg)
      (h₀ g).1 (h₀ g).2 (hcov v)
      (fun K' Rn hQ hst hhor => Or.inl ⟨reactiveGood_of_crashGood
        (hall g v K' Rn K' le_rfl hQ), by
          unfold Barnacle.horizonFrom at hhor
          rw [Nat.succ_mul] at hhor
          have := le_max_left (B.maxInterval + 1) δ
          change _ + _ + 2 * _ + (p.waveLength - 1 + 1) ≤ N
          change _ + _ + (p.waveLength - 1 + 1) ≤ N at hhor
          omega⟩)
      K (by unfold Barnacle.horizonFrom at hK ⊢; rw [hwu]; omega)
  let Rn := fun v => (hrun v).choose
  refine ⟨Rn, broadcasts_of_ledger ht (hanc g) Rn wk hTh (by rw [hcard]; exact hqT) hwr hmono
      hbuilt fun i t ht2 => ?_, fun k hk v₀ hcfg κ L h hlo hhi => ?_⟩
  · have hQt := Barnacle.cfg_keeps (Rn i) (hkeep g) (h₀ g).2 (t + 2) (by omega)
    have hst := Barnacle.start_mono (Rn i) (show t + 2 ≤ K by omega) le_rfl
    have hsK := (hrun i).choose_spec.1
    have hmx := le_max_right (B.maxInterval + 1) δ
    unfold Barnacle.horizonFrom at hK
    have hwin : (Rn i).start (t + 2) + δ + (2 * (Mb * n) + 2 * p.waveLength) +
        (schemeLiveReactive p σ rel).waveLength ≤ N := by
      change Barnacle.Run.start (Rn i) K ≤ _ at hsK
      change _ + _ + (p.waveLength - 1 + 1) + δ ≤ N at hK
      rw [hwl]; omega
    obtain ⟨κ, L, hκ, hdec, hL⟩ := Barnacle.ledger_commit_of_window
      (R := (schemeLiveReactive p σ rel).upTo N)
      (Scheme.agree ht) (Rn i) (k := t + 2) (by omega)
      (Barnacle.liveOn_upTo_of_boundedChainsUpto _ hD.indirect hD.decisive (hBC _ hQt) hcg)
      ⟨reactiveGood_mono (reactiveGood_of_crashGood (hall g i K (Rn i) (t + 2) (by omega) hQt))
        (by change _ ≤ _ + _ + _ + (p.waveLength - 1 + 1); omega), hwin⟩
      (fun b hb hr => hcov i b hb (le_trans hr hwin)) hδ
      (by rw [Barnacle.interval_eq (Rn i) (hkI g) _ (by omega)]; exact hint g) (by rw [hwu])
    obtain ⟨hLU, hLr, -⟩ := Scheme.commitsCandidate _ _ _ _ _ hdec
    have hst' := Barnacle.le_start (Rn i) (t + 2) (by omega)
    change (U.block L).round = ((Rn i).cfg (t + 2)).sched.slotRound κ at hLr
    rw [Barnacle.Config.sched_slotRound] at hLr
    exact ⟨L, hL, hLU, by omega⟩
  · exact Integration.commitFinalized_barnacle_scheme M E vm ht (hanc g) Pr Rn hk hcfg h hlo hhi

theorem holds : Statement :=
  ⟨checkpointsResponsive, checkpointsCrash, scheduledCrash, hammerHeadComposed, aimdComposed,
    asyncComposed, asyncHammerHeadComposed, scheduledIntegrity, scheduledAgreed, scheduledValidity,
    anchorLedger, composedValidity, hammerHeadBroadcast, aimdBroadcast,
    asyncBroadcast, asyncHammerHeadBroadcast, chainsBroadcast, shuffleBroadcast⟩

end Compose

end Scheme

end LeanDag
