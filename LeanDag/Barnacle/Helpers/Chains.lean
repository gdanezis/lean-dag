import LeanDag.Barnacle.Model.Chains
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Skips
/-!
# Barnacle: liveness from bounded anchor chains

A scan that ends decides what it passes: if a committed slot lies a wave
or more above slot `i`, and every slot from a wave above `i` up to it is
decided, then `i` is decided (`decided_of_scan`, the indirect law). A scan
that ends by a round under the horizon reaches a committed slot and decides
every slot before it (`scan_of_chainEnds`, by induction on `ChainEnds`).
Hence a configuration with bounded anchor chains is live, and settles the
slots below where its schedule turns good (`liveOn_of_boundedChains`,
`settlesBelow_of_boundedChains`). Runs of heads and runs of decided rounds
are bounded anchor chains (`boundedChains_of_headsRun`,
`boundedChains_of_skipRun`).
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

variable (C : Config Validator)

/-- The first slot of round `x` is at or below slot `j` exactly when `j`'s
round is `x` or later. -/
theorem Config_cum_le_iff {x j : ℕ} : C.cum x ≤ j ↔ x ≤ C.sched.slotRound j := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have := Config_lt_head_of_slotRound_lt C hlt
    omega
  · intro h
    by_contra hlt
    push Not at hlt
    have := Config_slotRound_lt_of_lt_head C hlt
    omega

variable {R : LiveRule Validator BlockId Payload}

/-- **A scan that ends decides its slot**: a committed slot at or after the
first slot a wave above `i`, every slot from there to it decided. -/
theorem decided_of_scan (hD : R.Indirect) {U : R.Universe} (V : R.View U) {i top : ℕ}
    (hle : C.cum (C.sched.slotRound i + R.waveLength) ≤ top)
    (htop : ∃ L, R.Decided C.sched V top (some L))
    (hmid : ∀ j, C.cum (C.sched.slotRound i + R.waveLength) ≤ j → j < top →
      ∃ v, R.Decided C.sched V j v) :
    ∃ v, R.Decided C.sched V i v := by
  classical
  have hex : ∃ j, C.cum (C.sched.slotRound i + R.waveLength) ≤ j ∧
      ∃ L, R.Decided C.sched V j (some L) := ⟨top, hle, htop⟩
  have hfle : Nat.find hex ≤ top := Nat.find_min' hex ⟨hle, htop⟩
  obtain ⟨hp, B, hB⟩ := Nat.find_spec hex
  refine hD C.sched V i (Nat.find hex) B ((Config_cum_le_iff C).1 hp) hB fun i' _ h2 h3 => ?_
  have hpi' : C.cum (C.sched.slotRound i + R.waveLength) ≤ i' := (Config_cum_le_iff C).2 h3
  obtain ⟨v, hv⟩ := hmid i' hpi' (by omega)
  cases v with
  | none => exact hv
  | some L => exact absurd ⟨hpi', L, hv⟩ (Nat.find_min hex h2)

/-- **A scan that ends by `H` reaches a committed slot and decides every slot
before it**, when the slots of `T` commit and those of `D` are decided from
round `Rnd` while their waves fit under `N ≥ H + w`. -/
theorem scan_of_chainEnds (hD : R.Indirect) {U : R.Universe} (V : R.View U)
    {T D : Finset Validator} {H Rnd N : ℕ}
    (hT : ∀ κ, Rnd ≤ C.sched.slotRound κ → C.sched.slotRound κ + R.waveLength ≤ N →
      C.sched.leader κ ∈ T → ∃ L, R.Decided C.sched V κ (some L))
    (hDd : ∀ κ, Rnd ≤ C.sched.slotRound κ → C.sched.slotRound κ + R.waveLength ≤ N →
      C.sched.leader κ ∈ D → ∃ v, R.Decided C.sched V κ v)
    (hH : H + R.waveLength ≤ N) :
    ∀ p, C.ChainEnds T D R.waveLength H p → Rnd ≤ C.sched.slotRound p →
      ∃ top, p ≤ top ∧ C.sched.slotRound top ≤ H ∧ (∃ L, R.Decided C.sched V top (some L)) ∧
        ∀ j, p ≤ j → j < top → ∃ v, R.Decided C.sched V j v := by
  intro p h
  induction h with
  | mk p top hle hHt hTl _ ih =>
    intro hRnd
    have hmono : ∀ j, p ≤ j → C.sched.slotRound p ≤ C.sched.slotRound j :=
      fun j hj => C.sched.mono hj
    refine ⟨top, hle, hHt, hT top (le_trans hRnd (hmono top hle)) (by omega) hTl,
      fun j h1 h2 => ?_⟩
    have hjt : C.sched.slotRound j ≤ C.sched.slotRound top := C.sched.mono (le_of_lt h2)
    by_cases hjD : C.sched.leader j ∈ D
    · exact hDd j (le_trans hRnd (hmono j h1)) (by omega) hjD
    · obtain ⟨top', hle', -, htop', hmid'⟩ := ih j h1 h2 hjD (by
        rw [Config_slotRound_head]; have := hmono j h1; omega)
      exact decided_of_scan C hD V hle' htop' hmid'

/-- **The descent laws decide what they commit**: the committing set is
decisive with itself as the decided set. -/
theorem LiveRule.Descent.decisive {slack : ℕ} (hD : R.Descent slack) : R.Decisive slack slack :=
  fun S U Rnd N hg =>
    let ⟨T, hT, hc⟩ := hD.goodLeaders S U Rnd N hg
    ⟨T, T, subset_rfl, hT, hT, hc, fun V κ hcov h1 h2 h3 =>
      let ⟨L, hL⟩ := hc V κ hcov h1 h2 h3; ⟨some L, hL⟩⟩

/-- **A configuration with bounded anchor chains is live**, at any gap of at
least `c₀ + 2w`. -/
theorem liveOn_of_boundedChains {slack fb c₀ c : ℕ} (hD : R.Indirect) (hK : R.Decisive slack fb)
    (hC : C.BoundedChains slack fb R.waveLength c₀) (hc : c₀ + 2 * R.waveLength ≤ c) :
    R.LiveOn C.sched c := by
  intro U V Rnd N hgood hcov
  obtain ⟨T, D, hTD, hT, hDc, hcom, hdec⟩ := hK C.sched U Rnd N hgood
  have hscan : ∀ x, Rnd ≤ x → x + c₀ + R.waveLength ≤ N →
      ∃ top, C.cum x ≤ top ∧ C.sched.slotRound top ≤ x + c₀ ∧
        (∃ L, R.Decided C.sched V top (some L)) ∧
        ∀ j, C.cum x ≤ j → j < top → ∃ v, R.Decided C.sched V j v := fun x hx hN =>
    scan_of_chainEnds C hD V (fun κ h1 h2 h3 => hcom V κ hcov h1 h2 h3)
      (fun κ h1 h2 h3 => hdec V κ hcov h1 h2 h3) hN (C.cum x) (hC T D hTD hT hDc x)
      (by rw [Config_slotRound_head]; exact hx)
  refine ⟨fun κ hR hN => ?_, fun r hR hN => ?_⟩
  · obtain ⟨top, hle, -, htop, hmid⟩ := hscan (C.sched.slotRound κ + R.waveLength) (by omega)
      (by omega)
    exact decided_of_scan C hD V hle htop hmid
  · obtain ⟨top, hle, hHt, htop, -⟩ := hscan r hR (by omega)
    exact ⟨top, (Config_cum_le_iff C).1 hle, by omega, htop⟩

/-- **A configuration with bounded anchor chains settles the slots below
the round its schedule turns good**, at any gap of at least `c₀ + 2w`. -/
theorem settlesBelow_of_boundedChains {slack fb c₀ c : ℕ} (hD : R.Indirect)
    (hK : R.Decisive slack fb) (hw : 0 < R.waveLength)
    (hC : C.BoundedChains slack fb R.waveLength c₀) (hc : c₀ + 2 * R.waveLength ≤ c) :
    R.SettlesBelow C.sched c := by
  intro U V Rnd N hgood hcov κ hκ hN
  obtain ⟨T, D, hTD, hT, hDc, hcom, hdec⟩ := hK C.sched U Rnd N hgood
  have hscan : ∀ x, Rnd ≤ x → x + c₀ + R.waveLength ≤ N →
      ∃ top, C.cum x ≤ top ∧ C.sched.slotRound top ≤ x + c₀ ∧
        (∃ L, R.Decided C.sched V top (some L)) ∧
        ∀ j, C.cum x ≤ j → j < top → ∃ v, R.Decided C.sched V j v := fun x hx hN =>
    scan_of_chainEnds C hD V (fun κ h1 h2 h3 => hcom V κ hcov h1 h2 h3)
      (fun κ h1 h2 h3 => hdec V κ hcov h1 h2 h3) hN (C.cum x) (hC T D hTD hT hDc x)
      (by rw [Config_slotRound_head]; exact hx)
  -- the scan from `Rnd + w − 1` reaches a committed slot
  obtain ⟨top, hle, -, htop, hmid⟩ := hscan (Rnd + R.waveLength - 1) (by omega) (by omega)
  have htopr := (Config_cum_le_iff C).1 hle
  refine stretchDescent hD C.sched V (b := C.cum Rnd) (top := top) (fun i hi => ?_)
    (fun j hj1 hj2 => ?_) htop κ (Config_lt_head_of_slotRound_lt C hκ)
  · have := Config_slotRound_lt_of_lt_head C hi
    omega
  · rcases Nat.lt_or_eq_of_le hj2 with hlt | rfl
    · by_cases hjx : C.cum (Rnd + R.waveLength - 1) ≤ j
      · exact hmid j hjx hlt
      · -- a slot at a round in `[Rnd, Rnd + w − 1)`: its own scan ends
        have hjr : C.sched.slotRound j < Rnd + R.waveLength - 1 :=
          Config_slotRound_lt_of_lt_head C (by omega)
        have hjR : Rnd ≤ C.sched.slotRound j := (Config_cum_le_iff C).1 hj1
        obtain ⟨top', hle', -, htop', hmid'⟩ := hscan (C.sched.slotRound j + R.waveLength)
          (by omega) (by omega)
        exact decided_of_scan C hD V hle' htop' hmid'
    · obtain ⟨L, hL⟩ := htop
      exact ⟨some L, hL⟩

/-- **Runs of heads are bounded anchor chains**: if from every round, within
`c₀` rounds, `g` consecutive heads are `T`-led for every `T` missing at most
`slack` validators, the scan from every round's first slot ends within
`c₀` rounds. -/
theorem boundedChains_of_headsRun {slack fb g c₀ : ℕ} (hg : 0 < g)
    (hrun : ∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun C.head T g c₀) :
    C.BoundedChains slack fb g c₀ := by
  intro T D _ hT _ x
  obtain ⟨ρ, hρ, hρc, hheads⟩ := hrun T hT x
  -- every scan starting from a round in `[x, ρ + g)` ends at a head of the run
  have key : ∀ d y, x ≤ y → y < ρ + g → ρ + g - y ≤ d → C.ChainEnds T D g (x + c₀) (C.cum y) := by
    intro d
    induction d with
    | zero => intro y _ hy hd; omega
    | succ d ih =>
      intro y hxy hy hd
      by_cases hyρ : ρ ≤ y
      · have hh := hheads (y - ρ) (by omega)
        rw [show ρ + (y - ρ) = y by omega] at hh
        exact .mk _ _ le_rfl (by rw [Config_slotRound_head]; omega)
          (by rw [Config_leader_head]; exact hh) fun j h1 h2 _ => absurd h1 (by omega)
      · refine .mk _ (C.cum ρ) ((Config_cum_le_iff C).2 (by rw [Config_slotRound_head]; omega))
          (by rw [Config_slotRound_head]; omega)
          (by rw [Config_leader_head]; simpa using hheads 0 hg) fun j h1 h2 _ => ?_
        have hjy : y ≤ C.sched.slotRound j := (Config_cum_le_iff C).1 h1
        have hjρ : C.sched.slotRound j < ρ := Config_slotRound_lt_of_lt_head C h2
        exact ih _ (by omega) (by omega) (by omega)
  exact key (ρ + g - x) x le_rfl (by omega) le_rfl

/-- **Runs of decided rounds are bounded anchor chains**: from every round,
within `c₀` rounds, `g − 1` rounds holding only `D`-led slots followed by a
`T`-led head, for every split. -/
theorem boundedChains_of_skipRun {slack fb g c₀ : ℕ} (hg : 0 < g)
    (hrun : ∀ T D : Finset Validator, T ⊆ D → Fintype.card Validator ≤ T.card + slack →
      Fintype.card Validator ≤ D.card + fb → SkipRun C T D g c₀) :
    C.BoundedChains slack fb g c₀ := by
  intro T D hTD hT hDc x
  obtain ⟨ρ, hρ, hρc, hDl, hTl⟩ := hrun T D hTD hT hDc x
  have key : ∀ d y, x ≤ y → y ≤ ρ + g - 1 → ρ + g - 1 - y ≤ d →
      C.ChainEnds T D g (x + c₀) (C.cum y) := by
    intro d
    induction d with
    | zero =>
      intro y _ hy hd
      refine .mk _ _ le_rfl (by rw [Config_slotRound_head]; omega)
        (by rw [Config_leader_head, show y = ρ + g - 1 by omega]; exact hTl)
        fun j h1 h2 _ => absurd h1 (by omega)
    | succ d ih =>
      intro y hxy hy hd
      refine .mk _ (C.cum (ρ + g - 1)) ((Config_cum_le_iff C).2 (by
          rw [Config_slotRound_head]; omega))
        (by rw [Config_slotRound_head]; omega) (by rw [Config_leader_head]; exact hTl)
        fun j h1 h2 hjD => ?_
      have hjy : y ≤ C.sched.slotRound j := (Config_cum_le_iff C).1 h1
      have hjt : C.sched.slotRound j < ρ + g - 1 := Config_slotRound_lt_of_lt_head C h2
      by_cases hjρ : ρ ≤ C.sched.slotRound j
      · exact absurd (hDl j hjρ (by omega)) hjD
      · exact ih _ (by omega) (by omega) (by omega)
  exact key (ρ + g - 1 - x) x le_rfl (by omega) le_rfl

end Barnacle

end LeanDag
