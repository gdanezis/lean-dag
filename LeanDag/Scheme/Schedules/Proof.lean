import LeanDag.Scheme.Schedules.Statement
import LeanDag.Scheme.Properties
import LeanDag.Barnacle.Agreement.Proof
import LeanDag.Barnacle.Ledger.Proof
import LeanDag.Barnacle.Live.Proof
import LeanDag.Adaptive.Score.Proof
import LeanDag.Barnacle.Helpers.Skips
import LeanDag.Scheme.Helpers.Reactive
import LeanDag.Barnacle.Helpers.Progress
import LeanDag.Scheme.Helpers.FullRun
import LeanDag.Scheme.Helpers.AsyncPace
import LeanDag.Scheme.Helpers.CoinHeads
import LeanDag.Steelhead.Helpers.Coin
import LeanDag.Scheme.Responsive.Proof
/-!
# The decider under Barnacle and HammerHead schedules — proof

Barnacle's and HammerHead's generic theorems, at the decider's agreement
(`Scheme.agree`), candidate law and descent laws (`Timed.descent_of_support`).
-/

namespace LeanDag

namespace Scheme

namespace Schedules

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} [P.Mechanised] {honest : Finset Validator}

theorem waveLength_eq {p : Scheme.Params} {σ : VoteSel Validator BlockId Payload P honest}
    {rel : Reliability Validator} (hw : 1 ≤ p.waveLength) :
    (schemeLive p σ rel).waveLength = p.waveLength :=
  show p.waveLength - 1 + 1 = p.waveLength by omega

theorem waves_of_tolerates {p : Scheme.Params} {f q : ℕ} (ht : p.Tolerates honest f q) :
    2 ≤ p.waveLength ∧ (p.voteIsCert = false → 3 ≤ p.waveLength) := by
  rcases ht.2.2 with ⟨hv, hw, -⟩ | ⟨-, hw, -⟩ | ⟨hv, hw, -⟩ | ⟨-, hw, -⟩
  · exact ⟨hw, fun h => by simp [hv] at h⟩
  · exact ⟨by omega, fun _ => hw⟩
  · exact ⟨hw, fun h => by simp [hv] at h⟩
  · exact ⟨by omega, fun _ => hw⟩

theorem safe : Safe := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ rel ht B Bd upd C₀
  have hagree : Properties.Agree (schemeLive p σ rel).toBaseRule.toDagRule := Scheme.agree ht
  exact ⟨Agreement.holds _ _ _ _ hagree B Bd upd C₀,
    Ledger.holds _ _ _ _ hagree Scheme.commitsCandidate B Bd upd C₀⟩

theorem descends : Descends := by
  intro Validator BlockId Payload _ _ _ P _ honest p σ rel hsub hw hw3 hcert hlive
  exact LiveRule.Descent.ofProperties (fun _ => rfl)
    (Timed.descent_of_support _ _ _ (familySupport p σ)
      (familySupport_ofCoverage hsub hw hw3 hcert) (familySupport_commits hlive) Scheme.indirect
      (fun _ => Nat.le_succ _) (fun _ _ _ h => h))

theorem runsExist : RunsExist := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ rel c₀ head ht hsub hcert hlive
    hheads B Bd upd hbnd hkeep C₀ hC₀
  obtain ⟨hw, hw3⟩ := waves_of_tolerates ht
  have hwl := waveLength_eq (σ := σ) (rel := rel) (by omega : 1 ≤ p.waveLength)
  exact Live.holds _ _ _ (schemeLive p σ rel) rel.slack c₀ head (Scheme.agree ht)
    (descends _ _ _ P honest p σ rel hsub hw hw3 hcert hlive) (by omega)
    (by rw [hwl]; exact hheads) B Bd upd hbnd hkeep C₀ hC₀

theorem aimd : Aimd := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel ht hsub ⟨hcert, hlive, hbound⟩ B Bd lead
    hl hlead C₀ hC₀
  obtain ⟨hw, hw3⟩ := waves_of_tolerates ht
  have hwl := waveLength_eq (σ := σ) (rel := rel) (by omega : 1 ≤ p.waveLength)
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hD := descends _ _ _ P honest p σ rel hsub hw hw3 (by rw [hcard]; exact hcert)
    (by rw [hcard]; exact hlive)
  have hbnd : UpdBounded B (Aimd.rule (schemeLive p σ rel).toBaseRule B lead hl) := by
    intro C b U V v A hC
    exact ⟨fun _ => Aimd.count_le _ _ _ _, hC.2⟩
  have hkeep : UpdKeeps (Aimd.rule (schemeLive p σ rel).toBaseRule B lead hl)
      (fun C => C.head = roundRobin n hn) := by
    intro C b U V v A _
    funext ρ
    exact hlead ρ
  have h := Live.runsExist_roundRobin hn (schemeLive p σ rel) (Scheme.agree ht) hD (by omega)
    (by rw [hwl]; exact hbound) B Bd _ hbnd hkeep C₀ hC₀
  rwa [hwl] at h

theorem hammerHead : HammerHead := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel ht B score C₀
  have hagree : Properties.Agree (schemeLive p σ rel).toBaseRule.toDagRule := Scheme.agree ht
  have hA := Adaptive.Score.rule_anchored score
  obtain ⟨hl1, hl2, hl3⟩ := Ledger.holds _ _ _ _ hagree Scheme.commitsCandidate B
    Boundary.atThreshold (Adaptive.rule score) C₀ hA
  refine ⟨⟨Agreement.holds _ _ _ _ hagree B _ _ C₀, hl1, hl2, hl3⟩, ?_⟩
  intro hsub ⟨hcert, hlive, hbound⟩ hkeep hQ hC₀ h₀
  obtain ⟨hw, hw3⟩ := waves_of_tolerates ht
  have hwl := waveLength_eq (σ := σ) (rel := rel) (by omega : 1 ≤ p.waveLength)
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hD := descends _ _ _ P honest p σ rel hsub hw hw3 (by rw [hcard]; exact hcert)
    (by rw [hcard]; exact hlive)
  have hbase : ∀ T : Finset (Fin n), Fintype.card (Fin n) ≤ T.card + rel.slack →
      HeadsRun (roundRobin n hn) T (schemeLive p σ rel).waveLength
        (n + (schemeLive p σ rel).waveLength - 1) := fun T hT =>
    roundRobin_headsRun n hn T _ _ (by simpa using hT) (by rw [hwl]; exact hbound)
  have hev := (Progress.holds _ _ _ (schemeLive p σ rel) hagree B Boundary.atThreshold
    (Adaptive.rule score) (Adaptive.Score.rule_bounded B score hkeep) C₀ (PermRR hn)
    (Adaptive.Score.rule_keeps score _ hQ) (n + (schemeLive p σ rel).waveLength - 1)).2
    (fun C _ ⟨π, hπ⟩ => liveOn_of_permuted_heads C hD (by omega) hbase π hπ) h₀ hC₀
  intro U V Rnd N hg
  have := hev U V Rnd N (fun C hC _ => hg C hC)
  rwa [hwl] at this

theorem rowsScheduled : RowsScheduled := by
  intro n f c
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  simp only [Scheme.Params.Scheduled, Scheme.Params.mysticeti, Scheme.Params.cordialMinersPS,
    Scheme.Params.blueBottlePS, Scheme.Params.orcaella, Scheme.Params.nemoNemo,
    Scheme.Params.hybridMysticeti] <;> omega

theorem silentDescends : SilentDescends := by
  intro Validator BlockId Payload _ _ _ P _ honest p σ rel fb hsub hw hw3 hcert hlive
  have hcov := familySupport_ofCoverage (σ := σ) hsub hw hw3 hcert
  have hlc := familySupport_commits (σ := σ) (rel := rel) hlive
  have hwl : (schemeLiveSilent p σ rel fb).waveLength = p.waveLength - 1 + 1 := rfl
  refine ⟨LiveRule.Descent.ofProperties
    (G := Timed.SilentGood (schemeAnchored p σ).toDagRule rel fb) (fun _ => rfl)
    (Timed.descent_of_support _ _ _ (familySupport p σ) hcov hlc Scheme.indirect
      (fun _ => Nat.le_succ _) (fun _ _ _ h => h.good)), fun hv hskip => ?_⟩
  intro S U Rnd N ⟨T, Z, hq, hs, hpop, hsil, hcard⟩
  have hcom : ∀ (S : Slots Validator) (V : (schemeLiveSilent p σ rel fb).View U) (κ : ℕ),
      (schemeLiveSilent p σ rel fb).toBaseRule.CoversUpto U V N → Rnd ≤ S.slotRound κ →
      S.slotRound κ + (schemeLiveSilent p σ rel fb).waveLength ≤ N → S.leader κ ∈ T →
      ∃ L, (schemeLiveSilent p σ rel fb).Decided S V κ (some L) := by
    intro S V κ hV hRnd hN hl
    obtain ⟨L, hL⟩ := Timed.exists_decided_of_coverage (familySupport p σ) hcov hlc hq hs hpop
      S V κ hV hRnd (fun j hj => by
        have := S.mono hj
        change S.slotRound j + (p.waveLength - 1) ≤ N
        omega) hl
    exact ⟨L, hL.2.1⟩
  refine ⟨T, T ∪ Z, Finset.subset_union_left, by have := hq.2; omega, hcard, hcom S,
    fun V κ hV hRnd hN hl => ?_⟩
  rcases Finset.mem_union.mp hl with hT | hZ
  · obtain ⟨L, hL⟩ := hcom S V κ hV hRnd hN hT
    exact ⟨some L, hL⟩
  · have hN' : S.slotRound κ + (p.waveLength - 1 + 1) ≤ N := hN
    refine ⟨none, Scheme.skipsUnsupported (σ := σ) hv S U V T κ (le_trans hskip hq.2)
      (fun v hvT => ?_) (fun c _ _ _ L hL _ => ?_)⟩
    · obtain ⟨b, hb, hbc, hbr⟩ := hpop (S.slotRound κ + 1) (by omega) (by omega) v hvT
      have hbr' : (U.block b).round = S.slotRound κ + 1 := hbr
      exact ⟨b, hV b hb (by change (U.block b).round ≤ N; omega), hbc, hbr⟩
    · obtain ⟨hLU, hLr, hLc⟩ := hL
      have hLc' : (U.block L).creator = S.leader κ := hLc
      have hLr' : (U.block L).round = S.slotRound κ := hLr
      have := hsil L hLU (by change (U.block L).creator ∈ Z; rw [hLc']; exact hZ)
      change (U.block L).round < Rnd at this
      omega

theorem silentLive : SilentLive := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel fb ht hsub ⟨hcert, hlive, hskip, hv,
    hbound⟩ B Bd upd hbnd hkeep C₀ hC₀ h₀
  obtain ⟨hw, hw3⟩ := waves_of_tolerates ht
  have hwl : (schemeLiveSilent p σ rel fb).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by omega
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  obtain ⟨hD, hK⟩ := silentDescends _ _ _ P honest p σ rel fb hsub hw hw3
    (by rw [hcard]; exact hcert) (by rw [hcard]; exact hlive)
  have hK := hK hv (by rw [hcard]; exact hskip)
  have hev := (Progress.holds _ _ _ (schemeLiveSilent p σ rel fb) (Scheme.agree ht) B Bd upd
    hbnd C₀ (SinglePermRR hn) hkeep (n + (schemeLiveSilent p σ rel fb).waveLength - 1)).2
    (fun C _ ⟨h1, π, hπ⟩ => liveOn_of_skipRun C hD hK (by omega)
      fun T D _ hT hDc => skipRun_perm_roundRobin hn C h1 π hπ T D rel.slack fb _ (by omega)
        (by simpa using hT) (by simpa using hDc) (by rw [hwl]; exact hbound)) h₀ hC₀
  intro U V Rnd N hg
  have := hev U V Rnd N (fun C hC _ => hg C hC)
  rwa [hwl] at this

theorem hammerHeadSilent : HammerHeadSilent := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel fb ht hsub hsch B score C₀ hkeep hQ
    hC₀ h₀
  obtain ⟨hcert, hlive, hskip, hv, hbound⟩ := hsch
  obtain ⟨hw, hw3⟩ := waves_of_tolerates ht
  have hwl : (schemeLiveSilent p σ rel fb).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by omega
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  obtain ⟨hD, hK⟩ := silentDescends _ _ _ P honest p σ rel fb hsub hw hw3
    (by rw [hcard]; exact hcert) (by rw [hcard]; exact hlive)
  have hK := hK hv (by rw [hcard]; exact hskip)
  have hQ' : ∀ U V v C, SinglePermRR hn C → SinglePermRR hn (score U V v C) :=
    fun U V v C ⟨h1, hp⟩ => ⟨fun r => by rw [(hkeep U V v C).1]; exact h1 r, hQ U V v C hp⟩
  have hev := (Progress.holds _ _ _ (schemeLiveSilent p σ rel fb) (Scheme.agree ht) B
    Boundary.atThreshold (Adaptive.rule score) (Adaptive.Score.rule_bounded B score hkeep) C₀
    (SinglePermRR hn) (Adaptive.Score.rule_keeps score _ hQ')
    (n + (schemeLiveSilent p σ rel fb).waveLength - 1)).2
    (fun C _ ⟨h1, π, hπ⟩ => liveOn_of_skipRun C hD hK (by omega)
      fun T D _ hT hDc => skipRun_perm_roundRobin hn C h1 π hπ T D rel.slack fb _ (by omega)
        (by simpa using hT) (by simpa using hDc) (by rw [hwl]; exact hbound)) h₀ hC₀
  intro U V Rnd N hg
  have := hev U V Rnd N (fun C hC _ => hg C hC)
  rwa [hwl] at this

theorem rowsSkipScheduled : RowsSkipScheduled := by
  intro n f c
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  simp [Scheme.Params.SkipScheduled, Scheme.Params.voteOffset, Scheme.Params.mysticeti,
    Scheme.Params.blueBottlePS, Scheme.Params.orcaella, Scheme.Params.hybridMysticeti] <;> omega

attribute [local instance] noFaults in
theorem reactiveDescends : ReactiveDescends := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ rel hc hcm
  refine ⟨?_, fun S U V i j A hij hj hmid => Scheme.indirect.decided S V hij hj hmid⟩
  rintro S U Rnd N ⟨T, hq, hTh, N', rs, hgst, hto, hW⟩
  refine ⟨T, by have := hq.2; omega, fun V κ hcov hRnd hN hlead => ?_⟩
  have hNw : S.slotRound κ + (p.waveLength - 1) ≤ rs.waits := by
    have : S.slotRound κ + (p.waveLength - 1 + 1) ≤ N := hN
    omega
  obtain ⟨L, hL⟩ := familySupport_commits (σ := σ) (rel := rel) hcm S V T κ hq
    (fun n _ h2 => rs.toAsyncPace.populated hq.2 n
      (le_trans h2 (le_trans hNw rs.waits_le)))
    (fun L ⟨hLmem, hLr, hLc⟩ => rs.certifies (S := S) hc.1 hc.2 hTh hq.2 hgst hto hRnd hNw hlead
      ⟨hLmem, hLr, hLc⟩)
    (fun b hb hr => hcov b hb (by
      change (U.block b).round ≤ S.slotRound κ + (p.waveLength - 1) at hr
      change (U.block b).round ≤ N
      have : S.slotRound κ + (p.waveLength - 1 + 1) ≤ N := hN
      omega))
    hlead
  exact ⟨L, hL.2.1⟩

theorem runsExistReactive : RunsExistReactive := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ rel c₀ head ht hc hcm hheads B Bd
    upd hbnd hkeep C₀ δ
  have hD := reactiveDescends Validator BlockId Payload P honest p σ rel hc hcm
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by have := hc.1; omega
  exact Live.holdsFrom _ _ _ (schemeLiveReactive p σ rel) rel.slack c₀ head (Scheme.agree ht)
    hD (by rw [hwl]; have := hc.1; omega) (by rw [hwl]; exact hheads) B Bd upd hbnd hkeep C₀ δ

theorem aimdReactive : AimdReactive := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel ht hc ⟨hcert, hlive, hbound⟩ B Bd lead
    hl hlead C₀ δ
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hD := reactiveDescends (Fin n) BlockId Payload P honest p σ rel (by rw [hcard]; exact hc)
    (by rw [hcard]; exact hlive)
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by have := hc.1; omega
  have hbnd : UpdBounded B (Aimd.rule (schemeLiveReactive p σ rel).toBaseRule B lead hl) := by
    intro C b U V v A hC
    exact ⟨fun _ => Aimd.count_le _ _ _ _, hC.2⟩
  have hkeep : UpdKeeps (Aimd.rule (schemeLiveReactive p σ rel).toBaseRule B lead hl)
      (fun C => C.head = roundRobin n hn) := by
    intro C b U V v A _
    funext ρ
    exact hlead ρ
  have h := Live.holdsFrom _ _ _ (schemeLiveReactive p σ rel) rel.slack
    (n + (schemeLiveReactive p σ rel).waveLength - 1) (roundRobin n hn) (Scheme.agree ht) hD
    (by rw [hwl]; have := hc.1; omega) (fun T hT => roundRobin_headsRun n hn T _ _ (by simpa using hT)
      (by rw [hwl]; exact hbound)) B Bd _ hbnd hkeep C₀ δ
  rwa [hwl] at h

theorem hammerHeadReactive : HammerHeadReactive := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel ht hc ⟨hcert, hlive, hbound⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro B score C₀ δ hkeep hQ h₀ hQ₀ U V N hcov hgood K hK
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hD := reactiveDescends (Fin n) BlockId Payload P honest p σ rel (by rw [hcard]; exact hc)
    (by rw [hcard]; exact hlive)
  have hwl : (schemeLiveReactive p σ rel).waveLength = p.waveLength :=
    show p.waveLength - 1 + 1 = p.waveLength by have := hc.1; omega
  have hbase : ∀ T : Finset (Fin n), Fintype.card (Fin n) ≤ T.card + rel.slack →
      HeadsRun (roundRobin n hn) T (schemeLiveReactive p σ rel).waveLength
        (n + p.waveLength - 1) := fun T hT => by
    have := roundRobin_headsRun n hn T _ (schemeLiveReactive p σ rel).waveLength
      (by simpa using hT) (by rw [hwl]; exact hbound)
    rwa [hwl] at this ⊢
  have hw0 : 0 < (schemeLiveReactive p σ rel).waveLength := by rw [hwl]; have := hc.1; omega
  obtain ⟨Rn, -, -⟩ := everyHeight_from (Q := PermRR hn) (Scheme.agree ht)
    (Adaptive.Score.rule_bounded B score hkeep) (Adaptive.Score.rule_keeps score _ hQ)
    (fun C _ ⟨π, hπ⟩ => liveOn_of_permuted_heads C hD hw0 hbase π hπ)
    (fun C _ ⟨π, hπ⟩ => settlesBelow_of_permuted_heads C hD hw0 hbase π hπ)
    h₀ hQ₀ hcov hgood K hK
  exact ⟨Rn⟩

attribute [local instance] noFaults in
theorem reactiveGoodInhabited : ReactiveGoodInhabited := by
  intro n _ p f c hrow rel hq σ N
  have hqn : n - f - c ≤ n := by omega
  refine ⟨Full.record hqn N, fun r hr v => ⟨toLex (r, v), Full.mem_record_ids.mpr
    (by simpa using hr), by simp, by simp⟩, fun S Rnd => ?_⟩
  exact ⟨Finset.univ, hq, Finset.subset_univ _, N,
    Full.run (S := S) (Fintype.card (Fin n) - rel.slack) p (Responsive.psRow_cert_le hrow) σ,
    Nat.zero_le _, fun _ _ => by simp, le_refl N⟩

theorem asyncConfigLive : AsyncConfigLive := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest p σ rel c₀ hc hcm C
  have hw : 0 < (schemeLiveAsync p σ rel c₀).waveLength := Nat.succ_pos _
  have hind : (schemeLiveAsync p σ rel c₀).Indirect :=
    fun S U V i j A hij hj hmid => Scheme.indirect.decided S V hij hj hmid
  have key : ∀ (U : (schemeLiveAsync p σ rel c₀).Universe)
      (V : (schemeLiveAsync p σ rel c₀).View U) (Rnd N : ℕ),
      (schemeLiveAsync p σ rel c₀).Good C.sched U Rnd N →
      (schemeLiveAsync p σ rel c₀).toBaseRule.CoversUpto U V N →
      (∀ κ, Rnd ≤ C.sched.slotRound κ →
        C.sched.slotRound κ + c₀ + (schemeLiveAsync p σ rel c₀).waveLength ≤ N →
        ∃ v, (schemeLiveAsync p σ rel c₀).Decided C.sched V κ v) ∧
      (∀ r, Rnd ≤ r → r + c₀ + (schemeLiveAsync p σ rel c₀).waveLength ≤ N →
        ∃ κ, r ≤ C.sched.slotRound κ ∧ C.sched.slotRound κ ≤ r + c₀ ∧
          ∃ L, (schemeLiveAsync p σ rel c₀).Decided C.sched V κ (some L)) ∧
      (∀ κ, C.sched.slotRound κ < Rnd → Rnd + c₀ + (schemeLiveAsync p σ rel c₀).waveLength ≤ N →
        ∃ v, (schemeLiveAsync p σ rel c₀).Decided C.sched V κ v) :=
    fun U V Rnd N hg hcov => by
      obtain ⟨T, hq, hTh, hpop, hheads⟩ := hg
      have hcmT : p.commitThreshold ≤ T.card := le_trans hcm hq.2
      exact clauses_of_committingHeads C hind hw V
        (fun ρ => C.sched.leader (C.cum ρ) ∈ safeAt p U ρ)
        (fun ρ _ hρN hGd => by
          letI : Slots Validator := C.sched
          have hsafe : C.sched.leader (C.cum ρ) ∈ LeanDag.Scheme.safe p U (C.cum ρ) := by
            unfold LeanDag.Scheme.safe; rw [Config_slotRound_head]; exact hGd
          obtain ⟨L, -, hL⟩ := decided_of_safe_of_round (q := q)
            σ hc.1 hc.2 hcmT
            (hpop _ (by rw [Config_slotRound_head]; change ρ + (p.waveLength - 1 + 1) ≤ N at hρN
                        omega)) hsafe
            (V := V) fun b hb hbr => hcov b hb (by
              change (U.block b).round ≤ N
              rw [hbr, Config_slotRound_head]
              change ρ + (p.waveLength - 1 + 1) ≤ N at hρN
              omega)
          exact ⟨L, hL⟩)
        (fun r hr hrN => by
          obtain ⟨ρ, h1, h2, h3⟩ := hheads r hr hrN
          exact ⟨ρ, h1, h2, fun i hi => h3 i hi (C.cum (ρ + i)) (Config_slotRound_head C _)
            (fun κ' h => Config_slotRound_lt_of_lt_head C h)⟩)
  exact ⟨fun U V Rnd N hg hcov => ⟨(key U V Rnd N hg hcov).1, (key U V Rnd N hg hcov).2.1⟩,
    fun U V Rnd N hg hcov => (key U V Rnd N hg hcov).2.2⟩

theorem asyncAimdRuns : AsyncAimdRuns := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel c₀ ht hc hcm B Bd lead hl h hlead C₀ h₀
    hC₀ U V N T hq hTh hpop hsafe hcov K hK
  have hbnd : UpdBounded B (Aimd.rule (schemeLiveAsync p σ rel c₀).toBaseRule B lead hl) := by
    intro C b U V v A hC
    exact ⟨fun _ => Aimd.count_le _ _ _ _, hC.2⟩
  have hkeep : UpdKeeps (Aimd.rule (schemeLiveAsync p σ rel c₀).toBaseRule B lead hl)
      (fun C => C.head = h) := by
    intro C b U V v A _
    funext ρ
    exact hlead ρ
  exact everyHeight (Q := fun C => C.head = h) (Scheme.agree ht) hbnd hkeep
    (fun C _ _ => (asyncConfigLive (Fin n) BlockId Payload P q honest p σ rel c₀ hc hcm C).1)
    h₀ hC₀ hcov
    (fun C _ hCh => ⟨T, hq, hTh, hpop, fun r hr hrN => by
      obtain ⟨ρ, h1, h2, h3⟩ := hsafe r hr hrN
      refine ⟨ρ, h1, h2, fun i hi κ hκ hfirst => ?_⟩
      rw [eq_cum_of_first C hκ hfirst, Config_leader_head, hCh]
      exact h3 i hi⟩)
    (Nat.zero_le 1) K hK

open scoped ENNReal in
attribute [local instance] noFaults in
theorem asyncAimdLive : AsyncAimdLive := by
  intro n hn BlockId Payload _ P _ q _ honest f p σ rel J M c dflt ht hc hcm
  haveI : Nonempty (Fin n) := ⟨dflt⟩
  intro B Bd lead hl hlead C₀ hC₀ U V N T hq hTh hpop hcov hNJ hfloor K hK
  -- the blocks of window `j`, and the safe sets of their rounds
  let H : Fin J → Finset (Fin (J * M)) := fun j =>
    (Finset.univ : Finset (Fin M)).map
      ⟨fun (m : Fin M) => (⟨j * M + m, blk_lt j.isLt m.isLt⟩ : Fin (J * M)),
        fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa using this)⟩
  let G : Fin (J * M) → Fin (p.waveLength - 1 + 1) → Finset (Fin n) := fun k i =>
    safeAt p U (k * (p.waveLength - 1 + 1) + i)
  have hG : ∀ k i, c ≤ (G k i).card := fun k i => hfloor _ (by
    have h1 := Nat.mul_le_mul_right (p.waveLength - 1 + 1) (show (k : ℕ) + 1 ≤ J * M from k.isLt)
    have h2 := i.isLt
    have : (J * M) * (p.waveLength - 1 + 1) = J * (M * (p.waveLength - 1 + 1)) := by ring
    nlinarith)
  -- a draw with a block of safe heads in every window has runs of every height
  have hsub : {g : Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin n | IsEmpty (Barnacle.Run
        (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B Bd
        (Barnacle.Aimd.rule _ B (lead (coinHead dflt g)) (hl _)) (C₀ (coinHead dflt g)) U V K)} ⊆
      ⋃ j, {g | ∀ k ∈ H j, ∃ i, g k i ∉ G k i} := by
    intro g hg
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_forall, not_not] at hno
    have hwin : ∀ j : Fin J, ∃ m : Fin M, ∀ i : Fin (p.waveLength - 1 + 1),
        g ⟨j * M + m, blk_lt j.isLt m.isLt⟩ i ∈
          safeAt p U ((j * M + m) * (p.waveLength - 1 + 1) + i) := by
      intro j
      obtain ⟨k, hk, hall⟩ := hno j
      obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hk
      exact ⟨m, fun i => hall i⟩
    obtain ⟨Rn⟩ := asyncAimdRuns n hn BlockId Payload P q honest f p σ rel
      (2 * (M * (p.waveLength - 1 + 1))) ht hc hcm B Bd (lead (coinHead dflt g)) (hl _)
      (coinHead dflt g) (hlead _) (C₀ (coinHead dflt g)) (hC₀ _).1 (hC₀ _).2 U V N T hq hTh hpop
      (safeHeadRuns_of_windows p U rfl dflt g hNJ hwin) hcov K hK
    exact hg.false Rn
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_)
  calc ∑ j : Fin J, (PMF.uniformOfFintype _).toOuterMeasure
          {g : Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin n | ∀ k ∈ H j, ∃ i, g k i ∉ G k i}
        ≤ ∑ _j : Fin J, Steelhead.Coin.badBlockBoundAt (Fin n) c (p.waveLength - 1 + 1) ^ M := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := Steelhead.no_good_block_prob_le (H j) G hG
          rw [Finset.card_map, Finset.card_univ] at this
          simpa only [Fintype.card_fin, Steelhead.Coin.badBlockBoundAt] using this
      _ = (J : ℝ≥0∞) * Steelhead.Coin.badBlockBoundAt (Fin n) c (p.waveLength - 1 + 1) ^ M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem holds : Statement :=
  ⟨safe, descends, runsExist, aimd, hammerHead, rowsScheduled, silentDescends, silentLive,
    hammerHeadSilent, rowsSkipScheduled, reactiveDescends, runsExistReactive, aimdReactive,
    hammerHeadReactive, reactiveGoodInhabited, asyncConfigLive, asyncAimdRuns, asyncAimdLive⟩

end Schedules

end Scheme

end LeanDag
