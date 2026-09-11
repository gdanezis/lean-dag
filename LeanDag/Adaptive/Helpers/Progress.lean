import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Model.Live
import LeanDag.Barnacle.Helpers.DagRule
/-!
# Segmented progress helpers

Not part of the audit surface. Barnacle's progress helpers at a run with
two bounds (`Model/Segment.lean`): the height-`0` run, the extension by
one configuration, and the induction to every height.

The construction is where the two bounds show. Barnacle takes the
anchor's round as the next start; here the next start is
`start K + (cfg K).interval`, fixed before the anchor is looked for, and
the anchor is whatever committed slot lies past it. The new run's
`closed` therefore reaches the anchor's round and not the boundary,
which is where the chosen verdicts of the rounds between come from.

The horizon is unchanged. The anchor sits within the commit gap of the
boundary, and the boundary sits within `maxInterval` of the previous
one, so `Barnacle.horizon` bounds the same heights it bounded before —
and the new start is bounded more tightly, by `maxInterval` rather than
by `maxInterval + 1 + c`.
-/

namespace LeanDag

namespace Adaptive

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Progress

variable {R : LiveRule Validator BlockId Payload} {P : Params}
variable {upd : UpdateRule R.toBaseRule} {C₀ : Config Validator}
variable {Q : Config Validator → Prop} {U : R.Universe}

/-- The height-`0` run: `init` only. -/
def SegRun.zero (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) (h₀ : C₀.InBounds P)
    (U : R.Universe) (V : R.View U) :
    SegRun R P upd C₀ U V 0 where
  start := fun _ => 0
  cfg := fun _ => C₀
  backoff := fun _ => 0
  anchor := fun _ => 0
  vdct := fun _ _ => none
  init := ⟨rfl, rfl, rfl⟩
  bounds := fun _ => h₀
  closed := fun _ h => absurd h (Nat.not_lt_zero _)
  anchor_commits := fun _ h => absurd h (Nat.not_lt_zero _)
  anchor_least := fun _ h => absurd h (Nat.not_lt_zero _)
  start_succ := fun _ h => absurd h (Nat.not_lt_zero _)
  update := fun _ h => absurd h (Nat.not_lt_zero _)

open Classical in
/-- **Configuration progress, with the bound on the new start.** -/
theorem progress_exists (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    (hupdh : UpdKeeps upd Q) {c K Rnd N : ℕ}
    {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (Rn : SegRun R.toBaseRule P upd C₀ U V K)
    (hlive : R.LiveOn (Rn.cfg K).sched c) (hQK : Q (Rn.cfg K))
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ Rn.start K + 1)
    (hN : Rn.start K + P.maxInterval + 1 + 2 * c + R.waveLength ≤ N) :
    ∃ Rn' : SegRun R.toBaseRule P upd C₀ U V (K + 1),
      Rn'.start (K + 1) ≤ Rn.start K + P.maxInterval ∧ Q (Rn'.cfg (K + 1)) := by
  obtain ⟨h1, h2⟩ := hlive U V Rnd N hgood hcov
  have hIle := (Rn.bounds K).2.2
  -- Clause 1 with the rounds read off the configuration.
  have h1' : ∀ κ, Rnd ≤ (Rn.cfg K).roundOf κ →
      (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N → ∃ v, R.Decided (Rn.sched K) V κ v := by
    intro κ a b
    exact h1 κ (by simpa using a) (by simpa using b)
  -- The verdicts of the new range, chosen from clause 1; `none` off the good rounds.
  let v : ℕ → Option BlockId := fun κ =>
    if h : Rnd ≤ (Rn.cfg K).roundOf κ ∧
        (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N then
      Classical.choose (h1' κ h.1 h.2) else none
  have hv : ∀ κ, Rnd ≤ (Rn.cfg K).roundOf κ →
      (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N →
      R.Decided (Rn.sched K) V κ (v κ) := by
    intro κ a b
    simp only [v, dif_pos (And.intro a b)]
    exact Classical.choose_spec (h1' κ a b)
  -- Clause 2 at the threshold round: a committed slot within `c`.
  obtain ⟨κ₀, hκ₀, hκ₀', L₀, hL₀⟩ :=
    h2 (Rn.start K + (Rn.cfg K).interval + 1) (by omega) (by omega)
  simp only [Config.sched_slotRound] at hκ₀ hκ₀'
  -- Its chosen verdict is that commit, by agreement.
  have hvκ₀ : v κ₀ = some L₀ :=
    hR _ _ _ κ₀ _ _ (hv κ₀ (by omega) (by omega)) hL₀
  -- The anchor: the least committed slot past the threshold.
  have hex : ∃ κ, Rn.start K + (Rn.cfg K).interval < (Rn.cfg K).roundOf κ ∧
      ∃ L, v κ = some L := ⟨κ₀, by omega, L₀, hvκ₀⟩
  obtain ⟨a, ha_spec, ha_min, ha_le⟩ : ∃ a,
      (Rn.start K + (Rn.cfg K).interval < (Rn.cfg K).roundOf a ∧ ∃ L, v a = some L) ∧
      (∀ κ, κ < a → ¬ (Rn.start K + (Rn.cfg K).interval < (Rn.cfg K).roundOf κ ∧
        ∃ L, v κ = some L)) ∧
      a ≤ κ₀ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun κ hκ => Nat.find_min hex hκ,
      Nat.find_min' hex ⟨by omega, L₀, hvκ₀⟩⟩
  have ha_round : (Rn.cfg K).roundOf a ≤ Rn.start K + P.maxInterval + 1 + c := by
    have := le_trans ((Rn.cfg K).roundOf_mono ha_le) hκ₀'
    omega
  -- The next configuration, by the rule at the anchor block.
  let next : Config Validator × ℕ :=
    (v a).elim (Rn.cfg K, Rn.backoff K) (fun A => upd (Rn.cfg K) (Rn.backoff K) U V A)
  have hnext : next.1.InBounds P := by
    obtain ⟨_, A, hA⟩ := ha_spec
    simp only [next, hA, Option.elim_some]
    exact hupd _ _ _ _ _ (Rn.bounds K)
  have hnexth : Q next.1 := by
    obtain ⟨_, A, hA⟩ := ha_spec
    simp only [next, hA, Option.elim_some]
    exact hupdh _ _ _ _ _ hQK
  refine ⟨{
    start := fun k => if k ≤ K then Rn.start k else Rn.start K + (Rn.cfg K).interval
    cfg := fun k => if k ≤ K then Rn.cfg k else next.1
    backoff := fun k => if k ≤ K then Rn.backoff k else if k = K + 1 then next.2 else 0
    anchor := fun k => if k = K then a else Rn.anchor k
    vdct := fun k κ => if k = K then v κ else Rn.vdct k κ
    init := by simp only [Nat.zero_le, if_true]; exact Rn.init
    bounds := ?_
    closed := ?_
    anchor_commits := ?_
    anchor_least := ?_
    start_succ := ?_
    update := ?_ }, ?_, ?_⟩
  · intro k
    by_cases hkK : k ≤ K
    · simp only [hkK, if_true]; exact Rn.bounds k
    · simp only [hkK, if_false]; exact hnext
  · -- closed
    intro k hkK1 κ hlo hhi
    by_cases hkK : k = K
    · subst hkK
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, if_true, hk1, if_false] at hlo hhi ⊢
      have hround : Rnd ≤ (Rn.cfg k).roundOf κ := by omega
      have hround' : (Rn.cfg k).roundOf κ + c + R.waveLength ≤ N := by omega
      exact hv κ hround hround'
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      simp only [hkK', hk1, hkK, if_true, if_false] at hlo hhi ⊢
      exact Rn.closed k (by omega) κ hlo hhi
  · -- anchor_commits
    intro k hkK1
    by_cases hkK : k = K
    · subst hkK
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, if_true, hk1, if_false]
      exact ⟨ha_spec.2, ha_spec.1⟩
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      simp only [hkK', hk1, hkK, if_true, if_false]
      exact Rn.anchor_commits k (by omega)
  · -- anchor_least
    intro k hkK1 κ hκ hthr
    by_cases hkK : k = K
    · subst hkK
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, if_true, hk1, if_false] at hκ hthr ⊢
      have := ha_min κ hκ
      cases hvκ : v κ with
      | none => rfl
      | some L => exact absurd ⟨hthr, L, hvκ⟩ this
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      simp only [hkK', hk1, hkK, if_true, if_false] at hκ hthr ⊢
      exact Rn.anchor_least k (by omega) κ hκ hthr
  · -- start_succ
    intro k hkK1
    by_cases hkK : k = K
    · subst hkK
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, if_true, hk1, if_false]
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      simp only [hkK', hk1, hkK, if_true, if_false]
      exact Rn.start_succ k (by omega)
  · -- update
    intro k hkK1 A hA
    by_cases hkK : k = K
    · subst hkK
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, if_true, hk1, if_false] at hA ⊢
      simp only [next, hA, Option.elim_some]
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      have hk1' : k + 1 ≠ K + 1 := by omega
      simp only [hkK', hk1, hkK, if_true, if_false] at hA ⊢
      exact Rn.update k (by omega) A hA
  · -- the bound on the new start: the boundary, known before the anchor
    have hk1 : ¬ (K + 1 ≤ K) := by omega
    simp only [hk1, if_false]
    exact Nat.add_le_add_left hIle _
  · -- the new configuration is one the rule emits
    have hk1 : ¬ (K + 1 ≤ K) := by omega
    simp only [hk1, if_false]
    exact hnexth

theorem progress (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    {c K Rnd N : ℕ}
    {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (Rn : SegRun R.toBaseRule P upd C₀ U V K)
    (hlive : R.LiveOn (Rn.cfg K).sched c)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ Rn.start K + 1)
    (hN : Rn.start K + P.maxInterval + 1 + 2 * c + R.waveLength ≤ N) :
    Nonempty (SegRun R.toBaseRule P upd C₀ U V (K + 1)) :=
  let ⟨Rn', _⟩ := progress_exists (Q := fun _ => True) hR hupd (fun _ _ _ _ _ _ => trivial)
    hcov Rn hlive trivial hgood hRnd hN
  ⟨Rn'⟩

/-- (D) -/
theorem everyHeight_bound (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    (hupdh : UpdKeeps upd Q) {c : ℕ}
    (hlive : ∀ C : Config Validator, C.InBounds P → Q C → R.LiveOn C.sched c)
    (h₀ : C₀.InBounds P) (hQ₀ : Q C₀)
    {Rnd N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ 1) :
    ∀ K, horizon P R c K ≤ N →
      ∃ Rn : SegRun R.toBaseRule P upd C₀ U V K,
        Rn.start K ≤ K * (P.maxInterval + 1 + c) ∧ Q (Rn.cfg K)
  | 0, _ => ⟨SegRun.zero _ P upd C₀ h₀ U V, Nat.zero_le _, hQ₀⟩
  | K + 1, hN => by
    have hN' : (K + 1) * (P.maxInterval + 1 + c) + c + R.waveLength ≤ N := hN
    rw [Nat.succ_mul] at hN'
    have hhor : horizon P R c K ≤ N := by unfold horizon; omega
    obtain ⟨Rn, hstart, hhead⟩ :=
      everyHeight_bound hR hupd hupdh hlive h₀ hQ₀ hcov hgood hRnd K hhor
    obtain ⟨Rn', hstart', hhead'⟩ := progress_exists hR hupd hupdh hcov Rn
      (hlive (Rn.cfg K) (Rn.bounds K) hhead) hhead
      hgood (by omega) (by omega)
    exact ⟨Rn', by rw [Nat.succ_mul]; omega, hhead'⟩

theorem everyHeight (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    (hupdh : UpdKeeps upd Q) {c : ℕ}
    (hlive : ∀ C : Config Validator, C.InBounds P → Q C → R.LiveOn C.sched c)
    (h₀ : C₀.InBounds P) (hQ₀ : Q C₀)
    {Rnd N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ 1) (K : ℕ)
    (hK : horizon P R c K ≤ N) :
    Nonempty (SegRun R.toBaseRule P upd C₀ U V K) :=
  let ⟨Rn, _⟩ := everyHeight_bound hR hupd hupdh hlive h₀ hQ₀ hcov hgood hRnd K hK
  ⟨Rn⟩


end Progress

end Adaptive

end LeanDag
