import LeanDag.RedSnapper.Helpers.Counting
import LeanDag.RedSnapper.Helpers.Certificates

/-!
# Quorum propagation

Generated: the general form of the paper's certificate-propagation
argument — any property held by a quorum of one round's blocks lies in
the causal history of every block above that round, because every
block's parent quorum meets the property's author quorum in a correct
validator whose block at that round is unique. RS2's `CertPropagation`
is the instance at `IsFastCert`. Nothing here is part of the audit
surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {U : Universe Validator BlockId Tx Obj}

/-- A nonempty threshold has a witness. -/
theorem exists_of_atLeast {k : ℕ} {s : Finset BlockId} {P : BlockId → Prop}
    (hk : 0 < k) (h : AtLeast U k s P) : ∃ b ∈ s, P b := by
  obtain ⟨t, hts, hP, hcard⟩ := h
  have hne : t.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    simp [authorsOf] at hcard
    omega
  obtain ⟨b, hb⟩ := hne
  exact ⟨b, hts hb, hP b hb⟩

/-- Thresholds are monotone in the block set. -/
theorem atLeast_mono {k : ℕ} {s s' : Finset BlockId} {P : BlockId → Prop}
    (hs : s ⊆ s') (h : AtLeast U k s P) : AtLeast U k s' P := by
  obtain ⟨t, hts, hP, hcard⟩ := h
  exact ⟨t, fun b hb => hs (hts hb), hP, hcard⟩

/-- **Quorum propagation**: a property held by a quorum of round-`r`
blocks lies in the causal history of every block above `r`. -/
theorem quorum_propagation {P : BlockId → Prop} {r : ℕ}
    (hq : AtLeast U (quorum Validator) (blocksAt U r) P) :
    ∀ b ∈ U.ids, r < (U.block b).round → ∃ C ∈ U.ids, P C ∧ Reaches U b C := by
  intro b hb hr
  obtain ⟨n, hn⟩ : ∃ n, (U.block b).round = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing b with
  | _ n ih =>
      subst hn
      by_cases hcase : (U.block b).round = r + 1
      · obtain ⟨v, hcorv, ⟨p, hpmem, hap, -⟩, ⟨c, hcmem, hac, hPc⟩⟩ :=
          exists_correct_of_atLeast (atLeast_parents_true hb (by omega)) hq
            quorum_add_quorum
        have hpid : p ∈ U.ids := U.complete b hb p hpmem
        have hcid : c ∈ U.ids := mem_ids_of_mem_blocksAt hcmem
        have hpr := round_of_mem_parents hb hpmem
        have hcr : (U.block c).round = r := (Finset.mem_filter.mp hcmem).2
        have hpc : p = c :=
          U.no_equivocation p hpid c hcid (hap.symm ▸ hcorv) (hap.trans hac.symm)
            (by omega)
        exact ⟨c, hcid, hPc, hpc ▸ Reaches.single hpmem⟩
      · have hpos : 0 < (U.block b).round := by omega
        have hq0 := (U.valid b hb).quorum hpos
        have hne : (U.block b).parents.Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          rw [authors, authorsOf, hemp] at hq0
          simp at hq0
          have := quorum_pos (Validator := Validator)
          omega
        obtain ⟨j, hj⟩ := hne
        have hjid := U.complete b hb j hj
        have hjr := round_of_mem_parents hb hj
        obtain ⟨C, hCid, hPC, hCr⟩ := ih (U.block j).round (by omega) j hjid (by omega) rfl
        exact ⟨C, hCid, hPC, Reaches.of_mem_parents hj hCr⟩

end RedSnapper

end LeanDag
