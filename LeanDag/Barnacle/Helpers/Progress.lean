import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Model.Live
import LeanDag.Barnacle.Helpers.Schedule
/-!
# Progress helpers

Not part of the audit surface. The height-`0` run; the extension of a
run by one configuration, returning the new start's bound (`Nonempty`
would lose it, and the induction to every height needs it); and that
induction.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Progress

variable {R : LiveRule Validator BlockId Payload} {P : Params} {B : Boundary Validator}
variable {upd : UpdateRule R.toBaseRule} {C₀ : Config Validator}
variable {Q : Config Validator → Prop} {U : R.Universe}

/-- The height-`0` run: `init` only. -/
def Run.zero (R : BaseRule Validator BlockId Payload) (P : Params)
    (B : Boundary Validator) (upd : UpdateRule R) (C₀ : Config Validator)
    (h₀ : C₀.InBounds P) (U : R.Universe) (V : R.View U) :
    Run R P B upd C₀ U V 0 where
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
/-- **Configuration progress, with the bound on the new start.** The
current configuration's schedule is good from `Rnd`; the slots of its range
below `Rnd` are decided by `hbelow`, which a range starting at `Rnd` or
later has for nothing and `LiveRule.SettlesBelow` gives otherwise. The
anchor is looked for from the later of the threshold and `Rnd`. -/
theorem progress_exists (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    (hupdh : UpdKeeps upd Q) {c K Rnd N : ℕ}
    {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (Rn : Run R.toBaseRule P B upd C₀ U V K)
    (hlive : R.LiveOn (Rn.cfg K).sched c) (hQK : Q (Rn.cfg K))
    (hgood : R.Good (Rn.cfg K).sched U Rnd N)
    (hbelow : ∀ κ, Rn.start K < (Rn.cfg K).roundOf κ → (Rn.cfg K).roundOf κ < Rnd →
      ∃ v, R.Decided (Rn.sched K) V κ v)
    (hN : max (Rn.start K + P.maxInterval + 1) Rnd + 2 * c + R.waveLength ≤ N) :
    ∃ Rn' : Run R.toBaseRule P B upd C₀ U V (K + 1),
      Rn'.start (K + 1) ≤ max (Rn.start K + P.maxInterval + 1) Rnd + c ∧
        Q (Rn'.cfg (K + 1)) := by
  obtain ⟨h1, h2⟩ := hlive U V Rnd N hgood hcov
  have hIle := (Rn.bounds K).2.2
  -- Clause 1 with the rounds read off the configuration.
  have h1' : ∀ κ, Rnd ≤ (Rn.cfg K).roundOf κ →
      (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N → ∃ v, R.Decided (Rn.sched K) V κ v := by
    intro κ a b
    exact h1 κ (by simpa using a) (by simpa using b)
  -- The verdicts of the new range: from clause 1 on the good rounds, from
  -- `hbelow` on the range's rounds below them; `none` elsewhere.
  let v : ℕ → Option BlockId := fun κ =>
    if h : Rnd ≤ (Rn.cfg K).roundOf κ ∧
        (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N then
      Classical.choose (h1' κ h.1 h.2)
    else if h' : Rn.start K < (Rn.cfg K).roundOf κ ∧ (Rn.cfg K).roundOf κ < Rnd then
      Classical.choose (hbelow κ h'.1 h'.2)
    else none
  have hv : ∀ κ, Rnd ≤ (Rn.cfg K).roundOf κ →
      (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N →
      R.Decided (Rn.sched K) V κ (v κ) := by
    intro κ a b
    simp only [v, dif_pos (And.intro a b)]
    exact Classical.choose_spec (h1' κ a b)
  have hvb : ∀ κ, Rn.start K < (Rn.cfg K).roundOf κ → (Rn.cfg K).roundOf κ < Rnd →
      R.Decided (Rn.sched K) V κ (v κ) := by
    intro κ a b
    have hn : ¬ (Rnd ≤ (Rn.cfg K).roundOf κ ∧ (Rn.cfg K).roundOf κ + c + R.waveLength ≤ N) :=
      fun h => absurd h.1 (by omega)
    simp only [v, dif_neg hn, dif_pos (And.intro a b)]
    exact Classical.choose_spec (hbelow κ a b)
  -- Clause 2 from the later of the threshold round and `Rnd`: a committed
  -- slot within `c`.
  obtain ⟨κ₀, hκ₀, hκ₀', L₀, hL₀⟩ :=
    h2 (max (Rn.start K + (Rn.cfg K).interval + 1) Rnd) (by omega) (by omega)
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
  have ha_round : (Rn.cfg K).roundOf a ≤ max (Rn.start K + P.maxInterval + 1) Rnd + c := by
    have := le_trans ((Rn.cfg K).roundOf_mono ha_le) hκ₀'
    omega
  -- The next configuration, by the rule at the anchor block.
  let next : Config Validator × ℕ :=
    (v a).elim (Rn.cfg K, Rn.backoff K) (fun A => upd (Rn.cfg K) (Rn.backoff K) U V
      (spanVdct (Rn.cfg K) (Rn.start K) (B.next (Rn.cfg K) (Rn.start K) a) v) A)
  have hnext : next.1.InBounds P := by
    obtain ⟨_, A, hA⟩ := ha_spec
    simp only [next, hA, Option.elim_some]
    exact hupd _ _ _ _ _ _ (Rn.bounds K)
  have hnexth : Q next.1 := by
    obtain ⟨_, A, hA⟩ := ha_spec
    simp only [next, hA, Option.elim_some]
    exact hupdh _ _ _ _ _ _ hQK
  refine ⟨{
    start := fun k => if k ≤ K then Rn.start k else B.next (Rn.cfg K) (Rn.start K) a
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
      have hround' : (Rn.cfg k).roundOf κ + c + R.waveLength ≤ N := by omega
      by_cases hround : Rnd ≤ (Rn.cfg k).roundOf κ
      · exact hv κ hround hround'
      · exact hvb κ hlo (by omega)
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      simp only [hkK', hk1, hkK, if_true, if_false] at hlo hhi ⊢
      exact Rn.closed k (by omega) κ hlo hhi
  · -- anchor_commits
    intro k hkK1
    by_cases hkK : k = K
    · subst hkK
      simp only [le_refl, if_true]
      exact ⟨ha_spec.2, ha_spec.1⟩
    · have hkK' : k ≤ K := by omega
      simp only [hkK', hkK, if_true, if_false]
      exact Rn.anchor_commits k (by omega)
  · -- anchor_least
    intro k hkK1 κ hκ hthr
    by_cases hkK : k = K
    · subst hkK
      simp only [le_refl, if_true] at hκ hthr ⊢
      have := ha_min κ hκ
      cases hvκ : v κ with
      | none => rfl
      | some L => exact absurd ⟨hthr, L, hvκ⟩ this
    · have hkK' : k ≤ K := by omega
      simp only [hkK', hkK, if_true, if_false] at hκ hthr ⊢
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
  · -- the bound on the new start: at or below the anchor's round, wherever
    -- the boundary falls
    have hk1 : ¬ (K + 1 ≤ K) := by omega
    simp only [hk1, if_false]
    exact le_trans (B.le_anchor _ _ _ ha_spec.1) ha_round
  · -- the new configuration is one the rule emits
    have hk1 : ¬ (K + 1 ≤ K) := by omega
    simp only [hk1, if_false]
    exact hnexth

theorem progress (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    {c K Rnd N : ℕ}
    {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (Rn : Run R.toBaseRule P B upd C₀ U V K)
    (hlive : R.LiveOn (Rn.cfg K).sched c)
    (hgood : R.Good (Rn.cfg K).sched U Rnd N) (hRnd : Rnd ≤ Rn.start K + 1)
    (hN : Rn.start K + P.maxInterval + 1 + 2 * c + R.waveLength ≤ N) :
    Nonempty (Run R.toBaseRule P B upd C₀ U V (K + 1)) :=
  let ⟨Rn', _⟩ := progress_exists (Q := fun _ => True) hR hupd (fun _ _ _ _ _ _ _ => trivial)
    hcov Rn hlive trivial hgood (fun _ h1 h2 => absurd h2 (by omega)) (by omega)
  ⟨Rn'⟩

/-- (D) -/
theorem everyHeight_bound (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    (hupdh : UpdKeeps upd Q) {c : ℕ}
    (hlive : ∀ C : Config Validator, C.InBounds P → Q C → R.LiveOn C.sched c)
    (h₀ : C₀.InBounds P) (hQ₀ : Q C₀)
    {Rnd N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : ∀ C : Config Validator, C.InBounds P → Q C → R.Good C.sched U Rnd N)
    (hRnd : Rnd ≤ 1) :
    ∀ K, horizon P R c K ≤ N →
      ∃ Rn : Run R.toBaseRule P B upd C₀ U V K,
        Rn.start K ≤ K * (P.maxInterval + 1 + c) ∧ Q (Rn.cfg K)
  | 0, _ => ⟨Run.zero _ P B upd C₀ h₀ U V, Nat.zero_le _, hQ₀⟩
  | K + 1, hN => by
    have hN' : (K + 1) * (P.maxInterval + 1 + c) + c + R.waveLength ≤ N := hN
    rw [Nat.succ_mul] at hN'
    have hhor : horizon P R c K ≤ N := by unfold horizon; omega
    obtain ⟨Rn, hstart, hhead⟩ :=
      everyHeight_bound hR hupd hupdh hlive h₀ hQ₀ hcov hgood hRnd K hhor
    obtain ⟨Rn', hstart', hhead'⟩ := progress_exists hR hupd hupdh hcov Rn
      (hlive (Rn.cfg K) (Rn.bounds K) hhead) hhead
      (hgood (Rn.cfg K) (Rn.bounds K) hhead) (fun _ h1 h2 => absurd h2 (by omega)) (by omega)
    exact ⟨Rn', by rw [Nat.succ_mul]; omega, hhead'⟩

theorem everyHeight (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd)
    (hupdh : UpdKeeps upd Q) {c : ℕ}
    (hlive : ∀ C : Config Validator, C.InBounds P → Q C → R.LiveOn C.sched c)
    (h₀ : C₀.InBounds P) (hQ₀ : Q C₀)
    {Rnd N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : ∀ C : Config Validator, C.InBounds P → Q C → R.Good C.sched U Rnd N)
    (hRnd : Rnd ≤ 1) (K : ℕ)
    (hK : horizon P R c K ≤ N) :
    Nonempty (Run R.toBaseRule P B upd C₀ U V K) :=
  let ⟨Rn, _⟩ := everyHeight_bound hR hupd hupdh hlive h₀ hQ₀ hcov hgood hRnd K hK
  ⟨Rn⟩

/-- **Every height, each configuration's schedule good from `δ` past its
start**, up to the round its step needs, unless the run has already moved
past it. -/
theorem everyHeight_from (hR : Properties.Agree R.toBaseRule.toDagRule)
    (hupd : UpdBounded P upd) (hupdh : UpdKeeps upd Q) {c δ : ℕ}
    (hlive : ∀ C : Config Validator, C.InBounds P → Q C → R.LiveOn C.sched c)
    (hset : ∀ C : Config Validator, C.InBounds P → Q C → R.SettlesBelow C.sched c)
    (h₀ : C₀.InBounds P) (hQ₀ : Q C₀)
    {N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : ∀ K (Rn : Run R.toBaseRule P B upd C₀ U V K), Q (Rn.cfg K) →
      R.Good (Rn.cfg K).sched U (Rn.start K + δ)
          (Rn.start K + max (P.maxInterval + 1) δ + 2 * c + R.waveLength) ∨
        ∃ Rn' : Run R.toBaseRule P B upd C₀ U V (K + 1),
          Rn'.start (K + 1) ≤ Rn.start K + max (P.maxInterval + 1) δ + c ∧
            Q (Rn'.cfg (K + 1))) :
    ∀ K, horizonFrom P R c δ K ≤ N →
      ∃ Rn : Run R.toBaseRule P B upd C₀ U V K,
        Rn.start K ≤ K * (max (P.maxInterval + 1) δ + c) ∧ Q (Rn.cfg K)
  | 0, _ => ⟨Run.zero _ P B upd C₀ h₀ U V, Nat.zero_le _, hQ₀⟩
  | K + 1, hN => by
    have hN' : (K + 1) * (max (P.maxInterval + 1) δ + c) + c + R.waveLength ≤ N := hN
    rw [Nat.succ_mul] at hN'
    have hhor : horizonFrom P R c δ K ≤ N := by unfold horizonFrom; omega
    obtain ⟨Rn, hstart, hhead⟩ :=
      everyHeight_from hR hupd hupdh hlive hset h₀ hQ₀ hcov hgood K hhor
    rcases hgood K Rn hhead with hg | ⟨Rn', hstart', hhead'⟩
    · -- the step's own horizon, under `N`
      have hcovK : R.toBaseRule.CoversUpto U V
          (Rn.start K + max (P.maxInterval + 1) δ + 2 * c + R.waveLength) :=
        fun b hb hr => hcov b hb (by omega)
      obtain ⟨Rn', hstart', hhead'⟩ := progress_exists hR hupd hupdh hcovK Rn
        (hlive (Rn.cfg K) (Rn.bounds K) hhead) hhead hg
        (fun κ h1 h2 => hset (Rn.cfg K) (Rn.bounds K) hhead U V _ _ hg hcovK κ
          (by simpa using h2) (by omega))
        (by omega)
      exact ⟨Rn', by rw [Nat.succ_mul]; omega, hhead'⟩
    · exact ⟨Rn', by rw [Nat.succ_mul]; omega, hhead'⟩

end Progress

end Barnacle

end LeanDag
