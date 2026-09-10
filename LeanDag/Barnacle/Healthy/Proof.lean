import LeanDag.Barnacle.Healthy.Statement
/-!
# BN12 — proof

Generated proof layer; not part of the audit surface. The scoring slots
of the window are the interval `Ico (cum (r − interval)) (cum (r −
waveLength + 1))`, of cardinality `expected`; each lies in the filtered
interval `observed` counts, so the count dominates it. The rule's
threshold test then passes by monotonicity.
-/

namespace LeanDag

namespace Barnacle

namespace Healthy

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R P lead hl hcd
  have hcount : Counted R := by
    intro C U A hA hwi hint hH
    set r := (R.block U A).round with hr
    -- the scoring slots, as an interval of slot indices
    set W : Finset ℕ := Finset.Ico (C.cum (r - C.interval)) (C.cum (r - R.waveLength + 1))
      with hW
    have hcard : W.card = expected R C r := by
      rw [hW, Nat.card_Ico, expected]
    have hsub : W ⊆ (Finset.Ico (C.cum (r - C.interval)) (C.cum (r + 1))).filter
        (fun κ => R.SlotDirect C.sched U (R.historyView U A hA) κ) := by
      intro κ hκ
      rw [hW, Finset.mem_Ico] at hκ
      obtain ⟨hlo, hhi⟩ := hκ
      -- the round of `κ` lies in the scoring band
      have hd₁ : r - C.interval ≤ C.roundOf κ := (C.cum_le_iff_le_roundOf).1 hlo
      have hd₂ : C.roundOf κ < r - R.waveLength + 1 := by
        by_contra hcon
        exact absurd (C.cum_mono (Nat.le_of_not_lt hcon))
          (Nat.not_le.2 (lt_of_le_of_lt (C.cum_roundOf_le κ) hhi))
      have hi : κ - C.cum (C.roundOf κ) < C.slotsAt (C.roundOf κ) := C.pos_lt_slotsAt κ
      have hidx : C.index (C.roundOf κ) (κ - C.cum (C.roundOf κ)) = κ := by
        rw [Config.index]
        have := C.cum_roundOf_le κ
        omega
      have hsub' : r - (r - C.roundOf κ) = C.roundOf κ := by omega
      refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hlo, ?_⟩, ?_⟩
      · exact lt_of_lt_of_le hhi (C.cum_mono (by omega))
      · have := hH (r - C.roundOf κ) (by omega) (by omega)
          (κ - C.cum (C.roundOf κ)) (by rw [hsub']; exact hi)
        rw [hsub', hidx] at this
        exact this
    have hle : W.card ≤ observed R C U A := by
      rw [observed, dif_pos hA]
      exact Finset.card_le_card hsub
    omega
  refine ⟨hcount, ?_, ?_⟩
  · intro C U A hA backoff V hnd hwi hint hH
    have hge : expected R C (R.block U A).round ≤ observed R C U A := hcount C U A hA hwi hint hH
    have htest : P.num * expected R C (R.block U A).round ≤ P.den * observed R C U A :=
      le_trans (Nat.mul_le_mul_right _ hnd) (Nat.mul_le_mul_left _ hge)
    simp only [Aimd.rule, decide_eq_true htest, if_pos]
  · -- BN12c: each counted slot is a commit verdict, by `CommitsDirect`.
    intro C U A hA hH d hlo hhi i hi
    obtain ⟨L, hLids, hLb, hdc⟩ := hH d hlo hhi i hi
    exact ⟨L, hcd _ U _ _ L hLb hdc⟩

end Healthy

end Barnacle

end LeanDag
