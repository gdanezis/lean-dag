import LeanDag.Barnacle.Helpers.Heads
/-!
# Barnacle: runs of decided rounds

A sharper form of the heads argument. Where the slots a set `D` leads are
decided, a slot is decided once it lies below `w − 1` rounds of `D`-led
slots followed by a committed head: the stretch descent applies to the
whole run (`liveOn_of_skipRun`). On one slot per round, under a
permutation of round-robin, such runs exist once
`(w − 1)·fb + slack + 1 ≤ n`, `fb` bounding the validators outside `D`
and `slack` those outside `T` (`skipRun_perm_roundRobin`).
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Run

variable {R : LiveRule Validator BlockId Payload} {slack' slack fb c₀ : ℕ}
variable (C : Config Validator)

/-- **A configuration with runs of decided rounds is live**, at the run's gap. -/
theorem liveOn_of_skipRun (hD : R.Descent slack') (hK : R.Decisive slack fb)
    (hw : 0 < R.waveLength)
    (hrun : ∀ T D : Finset Validator, T ⊆ D → Fintype.card Validator ≤ T.card + slack →
      Fintype.card Validator ≤ D.card + fb → SkipRun C T D R.waveLength c₀) :
    R.LiveOn C.sched c₀ := by
  intro U V Rnd N hgood hcov
  obtain ⟨T, D, hTD, hT, hDc, hcom, hdec⟩ := hK C.sched U Rnd N hgood
  have hr := hrun T D hTD hT hDc
  have htop : ∀ ρ, Rnd ≤ ρ → ρ + R.waveLength ≤ N → C.head ρ ∈ T →
      ∃ L, R.Decided C.sched V (C.cum ρ) (some L) := fun ρ h1 h2 h3 =>
    hcom V (C.cum ρ) hcov (by rw [Config_slotRound_head]; exact h1)
      (by rw [Config_slotRound_head]; exact h2) (by rw [Config_leader_head]; exact h3)
  refine ⟨fun κ hRnd hN => ?_, fun r hRnd hN => ?_⟩
  · obtain ⟨ρ, hlo, hhi, hDl, hTl⟩ := hr (C.sched.slotRound κ + 1)
    refine stretchDescent hD C.sched V (b := C.cum ρ) (top := C.cum (ρ + R.waveLength - 1))
      (fun i hi => ?_) (fun j hj1 hj2 => ?_) (htop _ (by omega) (by omega) hTl) κ
      (Config_lt_head_of_slotRound_lt C (by omega))
    · have := Config_slotRound_lt_of_lt_head C hi
      rw [Config_slotRound_head]; omega
    · have hjr : ρ ≤ C.sched.slotRound j := by
        rw [Config.sched_slotRound]; exact (C.cum_le_iff_le_roundOf).1 hj1
      rcases Nat.lt_or_eq_of_le hj2 with hlt | rfl
      · have := Config_slotRound_lt_of_lt_head C hlt
        exact hdec V j hcov (by omega) (by omega) (hDl j hjr (by omega))
      · obtain ⟨L, hL⟩ := htop _ (by omega) (by omega) hTl
        exact ⟨some L, hL⟩
  · obtain ⟨ρ, hlo, hhi, -, hTl⟩ := hr r
    refine ⟨C.cum (ρ + R.waveLength - 1), ?_, ?_, htop _ (by omega) (by omega) hTl⟩ <;>
      rw [Config_slotRound_head] <;> omega

end Run

/-- **On one slot per round, every slot is its round's head.** -/
theorem sched_leader_of_single (C : Config Validator) (h1 : ∀ r, C.slotsAt r = 1) (κ : ℕ) :
    C.sched.leader κ = C.head (C.sched.slotRound κ) := by
  have := C.pos_lt_slotsAt κ
  rw [h1] at this
  rw [Config.sched_leader, Config.sched_slotRound, Config.head, show κ - C.cum (C.roundOf κ) = 0
    by omega]

/-- Distinct positions of one cycle have distinct round-robin residues. -/
theorem roundRobin_inj {n : ℕ} (hn : 0 < n) (c : ℕ) {x y : Fin n}
    (h : roundRobin n hn (c + x) = roundRobin n hn (c + y)) : x = y := by
  have h2 := congrArg Fin.val h
  simp only [roundRobin] at h2
  have := Nat.ModEq.add_left_cancel' c h2
  rw [Nat.ModEq, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at this
  exact Fin.ext this

/-- **A cycle of a permuted round-robin holds a decided run**: some position
whose head is `T`-led, with `D`-led heads at the `g − 1` positions before it,
at `(g − 1)·fb + slack + 1 ≤ n`. -/
theorem exists_run_perm_roundRobin {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n))
    (T D : Finset (Fin n)) (slack fb g c : ℕ) (hc : g - 1 ≤ c) (hT : n ≤ T.card + slack)
    (hD : n ≤ D.card + fb) (hbound : (g - 1) * fb + slack + 1 ≤ n) :
    ∃ x : Fin n, π (roundRobin n hn (c + x)) ∈ T ∧
      ∀ i : Fin (g - 1), π (roundRobin n hn (c + x - (i + 1))) ∈ D := by
  classical
  by_contra hcon
  push Not at hcon
  set A : Finset (Fin n) := Finset.univ.filter fun x => π (roundRobin n hn (c + x)) ∉ T
  have hA : A.card ≤ Tᶜ.card := by
    refine Finset.card_le_card_of_injOn (fun x => π (roundRobin n hn (c + x))) (fun x hx => ?_)
      (fun x _ y _ h => roundRobin_inj hn c (π.injective h))
    simpa [A] using hx
  have hnot : ∀ x ∈ Aᶜ, ∃ i : Fin (g - 1), π (roundRobin n hn (c + x - (i + 1))) ∉ D := by
    intro x hx
    have hxT : π (roundRobin n hn (c + x)) ∈ T := by simpa [A] using hx
    exact hcon x hxT
  have hB : Aᶜ.card ≤ (g - 1) * Dᶜ.card := by
    rcases Nat.eq_zero_or_pos (g - 1) with h0 | hpos
    · rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun x hx => by
        obtain ⟨i, -⟩ := hnot x hx
        exact absurd i.isLt (by omega))]
      exact Nat.zero_le _
    haveI : Nonempty (Fin (g - 1)) := ⟨⟨0, hpos⟩⟩
    choose! k hk using hnot
    have := Finset.card_le_card_of_injOn
      (fun x => (k x, π (roundRobin n hn (c + x - (k x + 1)))))
      (t := (Finset.univ : Finset (Fin (g - 1))) ×ˢ Dᶜ) (fun x hx => by
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ,
          true_and, Finset.mem_compl]
        exact hk x hx) (fun x _ y _ h => by
        simp only [Prod.mk.injEq] at h
        obtain ⟨hk', hv⟩ := h
        rw [hk'] at hv
        have hle := (k y).isLt
        have e1 : c + x - (k y + 1) = (c - (k y + 1)) + x := by omega
        have e2 : c + y - (k y + 1) = (c - (k y + 1)) + y := by omega
        rw [e1, e2] at hv
        exact roundRobin_inj hn _ (π.injective hv))
    rwa [Finset.card_product, Finset.card_univ, Fintype.card_fin] at this
  have hsplit := Finset.card_add_card_compl A
  rw [Fintype.card_fin] at hsplit
  have hTc : Tᶜ.card ≤ slack := by rw [Finset.card_compl, Fintype.card_fin]; omega
  have hDc : Dᶜ.card ≤ fb := by rw [Finset.card_compl, Fintype.card_fin]; omega
  have := Nat.mul_le_mul_left (g - 1) hDc
  omega

/-- **A permuted round-robin on one slot per round has runs of decided
rounds**, at `(g − 1)·fb + slack + 1 ≤ n`, with gap `n + g − 1`. -/
theorem skipRun_perm_roundRobin {n : ℕ} (hn : 0 < n) (C : Config (Fin n))
    (h1 : ∀ r, C.slotsAt r = 1) (π : Equiv.Perm (Fin n))
    (hC : C.head = fun ρ => π (roundRobin n hn ρ)) (T D : Finset (Fin n)) (slack fb g : ℕ)
    (hg : 0 < g) (hT : n ≤ T.card + slack) (hD : n ≤ D.card + fb)
    (hbound : (g - 1) * fb + slack + 1 ≤ n) :
    SkipRun C T D g (n + g - 1) := by
  intro r
  obtain ⟨x, hxT, hxD⟩ := exists_run_perm_roundRobin hn π T D slack fb g (r + g - 1) (by omega)
    hT hD hbound
  have hx := x.isLt
  refine ⟨r + x, by omega, by omega, fun κ h1' h2' => ?_, ?_⟩
  · rw [sched_leader_of_single C h1, hC]
    have := hxD ⟨r + g - 1 + x - 1 - C.sched.slotRound κ, by omega⟩
    rwa [show r + g - 1 + x - ((r + g - 1 + x - 1 - C.sched.slotRound κ : ℕ) + 1) =
      C.sched.slotRound κ by omega] at this
  · rw [hC, show r + x + g - 1 = r + g - 1 + x by omega]; exact hxT

end Barnacle

end LeanDag
