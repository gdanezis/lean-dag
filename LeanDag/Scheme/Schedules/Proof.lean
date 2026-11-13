import LeanDag.Scheme.Schedules.Statement
import LeanDag.Scheme.Properties
import LeanDag.Barnacle.Agreement.Proof
import LeanDag.Barnacle.Ledger.Proof
import LeanDag.Barnacle.Live.Proof
import LeanDag.Adaptive.Score.Proof
import LeanDag.Barnacle.Helpers.Skips
import LeanDag.Scheme.Helpers.Reactive
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

theorem holds : Statement :=
  ⟨safe, descends, runsExist, aimd, hammerHead, rowsScheduled, silentDescends, silentLive,
    hammerHeadSilent, rowsSkipScheduled, reactiveDescends⟩

end Schedules

end Scheme

end LeanDag
