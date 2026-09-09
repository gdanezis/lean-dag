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

variable {R : LiveRule Validator BlockId Payload} {P : Params}
variable {getLeader : ℕ → Validator} {hk : Keyed getLeader P.maxLeaders}
variable {upd : UpdateRule R.toBaseRule} {U : R.Universe}

/-- The height-`0` run: `init` only. -/
def PartialRun.zero (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R) (U : R.Universe) (V : R.View U) :
    PartialRun R P getLeader hk upd U V 0 where
  start := fun _ => 0
  count := fun _ => 1
  backoff := fun _ => 0
  anchor := fun _ => 0
  vdct := fun _ _ => none
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => P.max_pos
  closed := fun _ h => absurd h (Nat.not_lt_zero _)
  anchor_commits := fun _ h => absurd h (Nat.not_lt_zero _)
  anchor_least := fun _ h => absurd h (Nat.not_lt_zero _)
  start_succ := fun _ h => absurd h (Nat.not_lt_zero _)
  update := fun _ h => absurd h (Nat.not_lt_zero _)

open Classical in
/-- **Configuration progress, with the bound on the new start.** -/
theorem progress_exists (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd) {c K Rnd N : ℕ}
    {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (Rn : PartialRun R.toBaseRule P getLeader hk upd U V K)
    (hlive : R.LiveOn (Sched getLeader hk (Rn.count K) (Rn.count_pos K) (Rn.count_le K)) c)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ Rn.start K + 1)
    (hN : Rn.start K + P.interval + 1 + 2 * c + P.gap + R.waveLength ≤ N) :
    ∃ Rn' : PartialRun R.toBaseRule P getLeader hk upd U V (K + 1),
      Rn'.start (K + 1) ≤ Rn.start K + P.interval + 1 + c + P.gap := by
  obtain ⟨h1, h2⟩ := hlive U V Rnd N hgood hcov
  -- Clause 1 with the rounds read as quotients.
  have h1' : ∀ κ, Rnd ≤ κ / Rn.count K → κ / Rn.count K + c + R.waveLength ≤ N →
      ∃ v, R.Decided (Rn.sched K) V κ v := by
    intro κ a b
    exact h1 κ (by simpa using a) (by simpa using b)
  -- The verdicts of the new range, chosen from clause 1; `none` off the good rounds.
  let v : ℕ → Option BlockId := fun κ =>
    if h : Rnd ≤ κ / Rn.count K ∧ κ / Rn.count K + c + R.waveLength ≤ N then
      Classical.choose (h1' κ h.1 h.2) else none
  have hv : ∀ κ, Rnd ≤ κ / Rn.count K → κ / Rn.count K + c + R.waveLength ≤ N →
      R.Decided (Rn.sched K) V κ (v κ) := by
    intro κ a b
    simp only [v, dif_pos (And.intro a b)]
    exact Classical.choose_spec (h1' κ a b)
  -- Clause 2 at the threshold round: a committed slot within `c`.
  obtain ⟨κ₀, hκ₀, hκ₀', L₀, hL₀⟩ :=
    h2 (Rn.start K + P.interval + 1) (by omega) (by omega)
  simp only [Sched_slotRound] at hκ₀ hκ₀'
  -- Its chosen verdict is that commit, by agreement.
  have hvκ₀ : v κ₀ = some L₀ :=
    hR _ _ _ κ₀ _ _ (hv κ₀ (by omega) (by omega)) hL₀
  -- The anchor: the least committed slot past the threshold.
  have hex : ∃ κ, Rn.start K + P.interval < κ / Rn.count K ∧ ∃ L, v κ = some L :=
    ⟨κ₀, by omega, L₀, hvκ₀⟩
  obtain ⟨a, ha_spec, ha_min, ha_le⟩ : ∃ a,
      (Rn.start K + P.interval < a / Rn.count K ∧ ∃ L, v a = some L) ∧
      (∀ κ, κ < a →
        ¬ (Rn.start K + P.interval < κ / Rn.count K ∧ ∃ L, v κ = some L)) ∧
      a ≤ κ₀ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun κ hκ => Nat.find_min hex hκ,
      Nat.find_min' hex ⟨by omega, L₀, hvκ₀⟩⟩
  have ha_round : a / Rn.count K ≤ Rn.start K + P.interval + 1 + c :=
    le_trans (Nat.div_le_div_right ha_le) hκ₀'
  -- The next configuration, by the rule at the anchor block.
  let next : ℕ × ℕ := (v a).elim (1, 0) (fun A => upd (Rn.count K) (Rn.backoff K) U V A)
  have hnext : 0 < next.1 ∧ next.1 ≤ P.maxLeaders := by
    obtain ⟨_, A, hA⟩ := ha_spec
    simp only [next, hA, Option.elim_some]
    exact hupd _ _ _ _ _
  refine ⟨{
    start := fun k => if k ≤ K then Rn.start k else a / Rn.count K + P.gap
    count := fun k => if k ≤ K then Rn.count k else if k = K + 1 then next.1 else 1
    backoff := fun k => if k ≤ K then Rn.backoff k else if k = K + 1 then next.2 else 0
    anchor := fun k => if k = K then a else Rn.anchor k
    vdct := fun k κ => if k = K then v κ else Rn.vdct k κ
    init := by simp only [Nat.zero_le, if_true]; exact Rn.init
    count_pos := ?_
    count_le := ?_
    closed := ?_
    anchor_commits := ?_
    anchor_least := ?_
    start_succ := ?_
    update := ?_ }, ?_⟩
  · intro k
    by_cases hkK : k ≤ K
    · simp only [hkK, if_true]; exact Rn.count_pos k
    · by_cases hk1 : k = K + 1
      · subst hk1; simp only [hkK, if_false, if_true]; exact hnext.1
      · simp only [hkK, hk1, if_false]; exact Nat.one_pos
  · intro k
    by_cases hkK : k ≤ K
    · simp only [hkK, if_true]; exact Rn.count_le k
    · by_cases hk1 : k = K + 1
      · subst hk1; simp only [hkK, if_false, if_true]; exact hnext.2
      · simp only [hkK, hk1, if_false]; exact P.max_pos
  · -- closed
    intro k hkK1 κ hlo hhi
    by_cases hkK : k = K
    · subst hkK
      have hk1 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, if_true, hk1, if_false] at hlo hhi ⊢
      have hround : Rnd ≤ κ / Rn.count k := by omega
      have hround' : κ / Rn.count k + c + R.waveLength ≤ N := by omega
      have hd := hv κ hround hround'
      rwa [PartialRun.sched, Sched_congr getLeader hk (show Rn.count k = Rn.count k from rfl)
        (Rn.count_pos k) (Rn.count_le k)] at hd
    · have hkK' : k ≤ K := by omega
      have hk1 : k + 1 ≤ K := by omega
      simp only [hkK', hk1, hkK, if_true, if_false] at hlo hhi ⊢
      have hd := Rn.closed k (by omega) κ hlo hhi
      rwa [Sched_congr getLeader hk (show Rn.count k = Rn.count k from rfl)
        (Rn.count_pos k) (Rn.count_le k)] at hd
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
  · -- the bound on the new start
    have hk1 : ¬ (K + 1 ≤ K) := by omega
    simp only [hk1, if_false]
    omega

theorem progress (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd) {c K Rnd N : ℕ}
    {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (Rn : PartialRun R.toBaseRule P getLeader hk upd U V K)
    (hlive : R.LiveOn (Sched getLeader hk (Rn.count K) (Rn.count_pos K) (Rn.count_le K)) c)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ Rn.start K + 1)
    (hN : Rn.start K + P.interval + 1 + 2 * c + P.gap + R.waveLength ≤ N) :
    Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V (K + 1)) :=
  let ⟨Rn', _⟩ := progress_exists hR hupd hcov Rn hlive hgood hRnd hN
  ⟨Rn'⟩

/-- (D) -/
theorem everyHeight_bound (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd) {c : ℕ}
    (hlive : ∀ m (hm : 0 < m) (hmax : m ≤ P.maxLeaders),
      R.LiveOn (Sched getLeader hk m hm hmax) c)
    {Rnd N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ 1) :
    ∀ K, horizon P R c K ≤ N →
      ∃ Rn : PartialRun R.toBaseRule P getLeader hk upd U V K,
        Rn.start K ≤ K * (P.interval + 1 + c + P.gap)
  | 0, _ => ⟨PartialRun.zero _ P getLeader hk upd U V, Nat.zero_le _⟩
  | K + 1, hN => by
    have hN' : (K + 1) * (P.interval + 1 + c + P.gap) + c + R.waveLength ≤ N := hN
    rw [Nat.succ_mul] at hN'
    have hhor : horizon P R c K ≤ N := by unfold horizon; omega
    obtain ⟨Rn, hstart⟩ := everyHeight_bound hR hupd hlive hcov hgood hRnd K hhor
    obtain ⟨Rn', hstart'⟩ := progress_exists hR hupd hcov Rn
      (hlive (Rn.count K) (Rn.count_pos K) (Rn.count_le K)) hgood (by omega) (by omega)
    exact ⟨Rn', by rw [Nat.succ_mul]; omega⟩

theorem everyHeight (hR : Properties.Agree R.toBaseRule.toDagRule) (hupd : UpdBounded P upd) {c : ℕ}
    (hlive : ∀ m (hm : 0 < m) (hmax : m ≤ P.maxLeaders),
      R.LiveOn (Sched getLeader hk m hm hmax) c)
    {Rnd N : ℕ} {V : R.View U} (hcov : R.toBaseRule.CoversUpto U V N)
    (hgood : R.Good U Rnd N) (hRnd : Rnd ≤ 1) (K : ℕ)
    (hK : horizon P R c K ≤ N) :
    Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V K) :=
  let ⟨Rn, _⟩ := everyHeight_bound hR hupd hlive hcov hgood hRnd K hK
  ⟨Rn⟩

end Progress

end Barnacle

end LeanDag
