import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Helpers.Schedule
import Mathlib.Data.Finset.Prod

/-!
# Heads helpers

Not part of the audit surface. The head arithmetic under `Sched m`; the
stretch descent from `indirect` alone; a slot is decided once the head
a wave above it is committed; heads decide the rounds below them; the
liveness clause from a run of heads; the pigeonhole for round-robin;
and round-robin's liveness.
-/

namespace LeanDag

namespace Barnacle

section HeadArith

variable {Validator : Type} (C : Config Validator)

/-- The head of round `ρ` is slot `C.cum ρ`. -/
theorem Config_slotRound_head (ρ : ℕ) : C.sched.slotRound (C.cum ρ) = ρ := by
  rw [Config.sched_slotRound, Config.roundOf_cum]

/-- The head of round `ρ` is led by `C.head ρ`, whatever the widths. -/
theorem Config_leader_head (ρ : ℕ) : C.sched.leader (C.cum ρ) = C.head ρ :=
  C.sched_leader_cum ρ

/-- A slot below the head of `ρ` sits at a round below `ρ`. -/
theorem Config_slotRound_lt_of_lt_head {κ ρ : ℕ} (h : κ < C.cum ρ) :
    C.sched.slotRound κ < ρ := by
  rw [Config.sched_slotRound]; exact C.lt_cum_iff_roundOf_lt.1 h

/-- A slot at a round below `ρ` sits below the head of `ρ`. -/
theorem Config_lt_head_of_slotRound_lt {κ ρ : ℕ} (h : C.sched.slotRound κ < ρ) :
    κ < C.cum ρ := by
  rw [Config.sched_slotRound] at h; exact C.lt_cum_iff_roundOf_lt.2 h

end HeadArith

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Heads

variable {R : LiveRule Validator BlockId Payload} {slack : ℕ}

/-- **BN9a, the stretch descent.** -/
theorem stretchDescent (hD : R.Descent slack) (S : Slots Validator) {U : R.Universe}
    (V : R.View U) {b top : ℕ}
    (hspan : ∀ i, i < b → S.slotRound i + R.waveLength ≤ S.slotRound top)
    (hdec : ∀ j, b ≤ j → j ≤ top → ∃ v, R.Decided S V j v)
    (htop : ∃ B, R.Decided S V top (some B)) :
    ∀ i, i < b → ∃ v, R.Decided S V i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, R.Decided S V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, S.slotRound i + R.waveLength ≤ S.slotRound j ∧
          ∃ B, R.Decided S V j (some B) := ⟨top, hspan i hi, htop⟩
      have hle : Nat.find hex ≤ top := Nat.find_min' hex ⟨hspan i hi, htop⟩
      obtain ⟨hgap, B, hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          S.slotRound i + R.waveLength ≤ S.slotRound i' → R.Decided S V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, R.Decided S V i' (some C) := fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hdec' : ∃ v, R.Decided S V i' v := by
          by_cases hi'b : i' < b
          · exact ih i' hi'b (by omega)
          · exact hdec i' (by omega) (by omega)
        obtain ⟨v, hv⟩ := hdec'
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      exact hD.indirect S V i (Nat.find hex) B hgap hB hmid
  intro i hi
  exact key (b - i) i hi (le_refl _)

variable (C : Config Validator)

/-- A slot is decided once the head a wave above it is committed: the intermediates are
vacuous. From `indirect` alone. -/
theorem decided_of_head_committed (hD : R.Descent slack)
    {U : R.Universe} (V : R.View U) (κ : ℕ)
    (hhead : ∃ L, R.Decided C.sched V
      (C.cum (C.sched.slotRound κ + R.waveLength)) (some L)) :
    ∃ v, R.Decided C.sched V κ v := by
  obtain ⟨L, hL⟩ := hhead
  refine hD.indirect _ V κ _ L ?_ hL ?_
  · rw [Config_slotRound_head]
  · intro i' _ hi' hle
    have := Config_slotRound_lt_of_lt_head C hi'
    omega

/-- **BN9b.** Heads of rounds `ρ + w, …, ρ + 2w − 1` `T`-led (with `T` from `goodLeaders`)
and their waves under `N`: every slot at rounds `[ρ, ρ + w)` is decided and the head of `ρ + w`
is committed, on the view `V` the caller supplies. -/
theorem headsDecide (hD : R.Descent slack) (hw : 0 < R.waveLength)
    {U : R.Universe} (V : R.View U) {Rnd N : ℕ} {T : Finset Validator}
    (hT : ∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L))
    (ρ : ℕ) (hRnd : Rnd ≤ ρ + R.waveLength)
    (hN : ρ + R.waveLength + R.waveLength + R.waveLength ≤ N + 1)
    (hheads : ∀ i, i < R.waveLength → C.head (ρ + R.waveLength + i) ∈ T) :
    (∀ κ, ρ ≤ C.sched.slotRound κ → C.sched.slotRound κ < ρ + R.waveLength →
      ∃ v, R.Decided C.sched V κ v) ∧
    ∃ L, R.Decided C.sched V (C.cum (ρ + R.waveLength)) (some L) := by
  -- the head of any round `ρ + w + i`, `i < w`, is committed
  have hhead : ∀ i, i < R.waveLength →
      ∃ L, R.Decided C.sched V (C.cum (ρ + R.waveLength + i)) (some L) := by
    intro i hi
    refine hT _ _ ?_ ?_ ?_
    · rw [Config_slotRound_head]; omega
    · rw [Config_slotRound_head]; omega
    · rw [Config_leader_head]; exact hheads i hi
  refine ⟨?_, by simpa using hhead 0 hw⟩
  intro κ hlo hhi
  apply decided_of_head_committed C hD
  have := hhead (C.sched.slotRound κ - ρ) (by omega)
  rwa [show ρ + R.waveLength + (C.sched.slotRound κ - ρ)
    = C.sched.slotRound κ + R.waveLength by omega] at this


/-- **BN9b′, subtraction-free.** Heads of rounds `ρ, …, ρ + w − 1` `T`-led, waves under `N`:
every slot at a round `r` with `r < ρ ≤ r + w` is decided, and the head of `ρ` is committed. -/
theorem headsDecide_at (hD : R.Descent slack) (hw : 0 < R.waveLength)
    {U : R.Universe} (V : R.View U) {Rnd N : ℕ} {T : Finset Validator}
    (hT : ∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L))
    (ρ : ℕ) (hRnd : Rnd ≤ ρ) (hN : ρ + R.waveLength + R.waveLength ≤ N + 1)
    (hheads : ∀ i, i < R.waveLength → C.head (ρ + i) ∈ T) :
    (∀ κ, C.sched.slotRound κ < ρ → ρ ≤ C.sched.slotRound κ + R.waveLength →
      ∃ v, R.Decided C.sched V κ v) ∧
    ∃ L, R.Decided C.sched V (C.cum ρ) (some L) := by
  have hhead : ∀ i, i < R.waveLength →
      ∃ L, R.Decided C.sched V (C.cum (ρ + i)) (some L) := by
    intro i hi
    refine hT _ _ ?_ ?_ ?_
    · rw [Config_slotRound_head]; omega
    · rw [Config_slotRound_head]; omega
    · rw [Config_leader_head]; exact hheads i hi
  refine ⟨?_, by simpa using hhead 0 hw⟩
  intro κ hlo hhi
  apply decided_of_head_committed C hD
  have := hhead (C.sched.slotRound κ + R.waveLength - ρ) (by omega)
  rwa [show ρ + (C.sched.slotRound κ + R.waveLength - ρ)
    = C.sched.slotRound κ + R.waveLength by omega] at this

/-- **BN9c′ at gap `c₀`**: `HeadsRun` called at `r + 1`. -/
theorem liveOn_of_headsRun (hD : R.Descent slack) (hw : 0 < R.waveLength)
    (hheads : ∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun C.head T R.waveLength c₀) :
    R.LiveOn C.sched c₀ := by
  intro U V Rnd N hgood hcov
  obtain ⟨T, hcardT, hT0⟩ := hD.goodLeaders U Rnd N hgood
  have hT : ∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ →
      S.slotRound κ + R.waveLength ≤ N → S.leader κ ∈ T →
      ∃ L, R.Decided S V κ (some L) :=
    fun S κ h1 h2 h3 => hT0 S V κ hcov h1 h2 h3
  have hrun := hheads T hcardT
  refine ⟨?_, ?_⟩
  · intro κ hRnd hN
    obtain ⟨ρ', hρ'lo, hρ'hi, hled⟩ := hrun (C.sched.slotRound κ + 1)
    obtain ⟨hdec, htop⟩ := headsDecide_at C hD hw V hT ρ' (by omega) (by omega) hled
    by_cases hcase : ρ' ≤ C.sched.slotRound κ + R.waveLength
    · exact hdec κ (by omega) hcase
    · refine stretchDescent hD C.sched V (b := C.cum (ρ' - R.waveLength))
        (top := C.cum ρ') ?_ ?_ htop κ ?_
      · intro i hi
        have := Config_slotRound_lt_of_lt_head C hi
        rw [Config_slotRound_head]
        omega
      · intro j hlo hhi
        rcases Nat.lt_or_eq_of_le hhi with hlt | heq
        · refine hdec j (Config_slotRound_lt_of_lt_head C hlt) ?_
          have : ρ' - R.waveLength ≤ C.sched.slotRound j := by
            rw [Config.sched_slotRound]; exact (C.cum_le_iff_le_roundOf).1 hlo
          omega
        · subst heq; obtain ⟨L, hL⟩ := htop; exact ⟨some L, hL⟩
      · exact Config_lt_head_of_slotRound_lt C (by omega)
  · intro r hRnd hN
    obtain ⟨ρ', hρ'lo, hρ'hi, hled⟩ := hrun r
    refine ⟨C.cum ρ', ?_, ?_, ?_⟩
    · rw [Config_slotRound_head]; exact hρ'lo
    · rw [Config_slotRound_head]; omega
    · refine hT _ _ ?_ ?_ ?_
      · rw [Config_slotRound_head]; omega
      · rw [Config_slotRound_head]; omega
      · rw [Config_leader_head]; simpa using hled 0 hw

#print axioms liveOn_of_headsRun

end Heads

/-- **The pigeonhole.** If no window of `g` consecutive residues starting
in a cycle lay inside `T`, choosing for each start a residue outside `T`
within its window would inject `Fin n` into `Fin g × Tᶜ`. -/
theorem roundRobin_headsRun (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)) (slack g : ℕ)
    (hT : n ≤ T.card + slack) (hbound : g * slack + 1 ≤ n) :
    HeadsRun (roundRobin n hn) T g (n + g - 1) := by
  intro r
  by_contra hcon
  push Not at hcon
  have hwin : ∀ x : Fin n, ∃ i, i < g ∧ roundRobin n hn (r + x + i) ∉ T := by
    intro x
    obtain ⟨i, hi, hiT⟩ := hcon (r + x) (by omega) (by omega)
    exact ⟨i, hi, hiT⟩
  choose k hk using hwin
  let φ : Fin n → Fin g × Fin n := fun x => (⟨k x, (hk x).1⟩, roundRobin n hn (r + x + k x))
  have hmaps : Set.MapsTo φ ↑(Finset.univ : Finset (Fin n))
      ↑((Finset.univ : Finset (Fin g)) ×ˢ Tᶜ) := by
    intro x _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and,
      Finset.mem_compl]
    exact (hk x).2
  have hinj : Set.InjOn φ ↑(Finset.univ : Finset (Fin n)) := by
    intro x _ y _ hxy
    simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at hxy
    obtain ⟨hkxy, hres⟩ := hxy
    have hres' : (r + x + k x) % n = (r + y + k y) % n := congrArg Fin.val hres
    rw [hkxy] at hres'
    have h2 : (↑x : ℕ) % n = ↑y % n :=
      Nat.ModEq.add_left_cancel' r (Nat.ModEq.add_right_cancel' (k y) hres')
    rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h2
    exact Fin.ext h2
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_compl, Fintype.card_fin] at hcard
  have hcompl : n - T.card ≤ slack := by omega
  have := Nat.mul_le_mul_left g hcompl
  omega


/-- **Round-robin is live** at every count, with gap `n + waveLength − 1`. -/
theorem liveOn_roundRobin {n : ℕ} (hn : 0 < n) {BlockId : Type} [DecidableEq BlockId]
    {Payload : Type} (R : LiveRule (Fin n) BlockId Payload) {slack : ℕ} (hD : R.Descent slack)
    (hw : 0 < R.waveLength) (hbound : R.waveLength * slack + 1 ≤ n)
    (C : Config (Fin n)) (hhead : C.head = roundRobin n hn) :
    R.LiveOn C.sched (n + R.waveLength - 1) :=
  liveOn_of_headsRun C hD hw fun T hT => by
    rw [hhead]
    exact roundRobin_headsRun n hn T slack R.waveLength (by simpa using hT) hbound

end Barnacle

end LeanDag
