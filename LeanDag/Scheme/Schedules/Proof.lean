import LeanDag.Scheme.Schedules.Statement
import LeanDag.Scheme.Properties
import LeanDag.Barnacle.Agreement.Proof
import LeanDag.Barnacle.Ledger.Proof
import LeanDag.Barnacle.Live.Proof
import LeanDag.Adaptive.Score.Proof
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
  exact Timed.descent_of_support _ _ _ (familySupport p σ)
    (familySupport_ofCoverage hsub hw hw3 hcert) (familySupport_commits hlive) Scheme.indirect
    (fun _ => Nat.le_succ _) (fun _ _ _ h => h)

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
  rwa [hwl] at hev

theorem rowsScheduled : RowsScheduled := by
  intro n f c
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  simp only [Scheme.Params.Scheduled, Scheme.Params.mysticeti, Scheme.Params.cordialMinersPS,
    Scheme.Params.blueBottlePS, Scheme.Params.orcaella, Scheme.Params.nemoNemo,
    Scheme.Params.hybridMysticeti] <;> omega

theorem holds : Statement := ⟨safe, descends, runsExist, aimd, hammerHead, rowsScheduled⟩

end Schedules

end Scheme

end LeanDag
