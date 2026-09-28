import LeanDag.RedSnapper.CertificateExclusion.Statement
import LeanDag.RedSnapper.Helpers.Counting
import LeanDag.RedSnapper.Helpers.Exclusion
import LeanDag.RedSnapper.Helpers.Certificates

/-!
# Certificate exclusion — proof

Generated proof layer; not part of the audit surface. Each exclusivity
claim intersects its two `AtLeast` witnesses (`Helpers/Counting.lean`)
and lands the pair of votes on one correct author, where the cores of
`Helpers/Exclusion.lean` close it; propagation is a strong induction on
the round, meeting the certifying quorum in a correct author at the
first step and descending through any parent above.
-/

namespace LeanDag

namespace RedSnapper

namespace CertificateExclusion

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

theorem certPropagation : CertPropagation U := by
  intro r tx hq b hb hr
  obtain ⟨n, hn⟩ : ∃ n, (U.block b).round = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing b with
  | _ n ih =>
      subst hn
      by_cases hcase : (U.block b).round = r + 1
      · obtain ⟨v, hcorv, ⟨p, hpmem, hap, -⟩, ⟨c, hcmem, hac, hcert⟩⟩ :=
          exists_correct_of_atLeast (atLeast_parents_true hb (by omega)) hq
            quorum_add_quorum
        have hpid : p ∈ U.ids := U.complete b hb p hpmem
        have hcid : c ∈ U.ids := mem_ids_of_mem_blocksAt hcmem
        have hpr := round_of_mem_parents hb hpmem
        have hcr : (U.block c).round = r := (Finset.mem_filter.mp hcmem).2
        have hpc : p = c :=
          U.no_equivocation p hpid c hcid (hap.symm ▸ hcorv) (hap.trans hac.symm)
            (by omega)
        exact ⟨c, hcid, hcert, hpc ▸ Reaches.single hpmem⟩
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
        obtain ⟨C, hCid, hCcert, hCr⟩ := ih (U.block j).round (by omega) j hjid (by omega) rfl
        exact ⟨C, hCid, hCcert, Reaches.of_mem_parents hj hCr⟩

theorem honestSingleAck (hdisc : StanceDiscipline U) : HonestSingleAck U := by
  intro b hb b' hb' hcor ha tx tx' hconf hv hv'
  exact no_conflicting_fast_votes hdisc hcor ha hconf hv hv'

theorem certUniqueness (hdisc : StanceDiscipline U) : CertUniqueness U := by
  intro C hC C' hC' tx tx' hconf hcert hcert'
  obtain ⟨v, hcorv, ⟨c, hcmem, hac, hvc⟩, ⟨c', hcmem', hac', hvc'⟩⟩ :=
    exists_correct_of_atLeast hcert.2 hcert'.2 quorum_add_quorum
  exact no_conflicting_fast_votes hdisc (hac.symm ▸ hcorv) (hac'.trans hac.symm)
    hconf hvc hvc'

theorem ackSkipExclusion (hdisc : StanceDiscipline U) : AckSkipExclusion U := by
  intro C hC C' hC' tx hcert hskip
  obtain ⟨v, hcorv, ⟨c, hcmem, hac, hvc⟩, ⟨d, hdmem, had, hsd⟩⟩ :=
    exists_correct_of_atLeast hcert.2 hskip quorum_add_half
  exact no_fast_vote_and_skip_vote hdisc (U.complete C hC c hcmem)
    (U.complete C' hC' d hdmem) (hac.symm ▸ hcorv) (had.trans hac.symm) hvc hsd

theorem ackUnlockExclusionBelow (hdisc : StanceDiscipline U) :
    AckUnlockExclusionBelow U := by
  intro C hC C' hC' tx hcert hunlock hround
  obtain ⟨v, hcorv, ⟨c, hcmem, hac, hvc⟩, ⟨d, hdmem, had, hsd⟩⟩ :=
    exists_correct_of_atLeast hcert.2 hunlock quorum_add_half
  have h1 := round_of_mem_parents hC hcmem
  have h2 := round_of_mem_parents hC' hdmem
  exact no_fast_vote_and_bot_below hdisc (U.complete C hC c hcmem)
    (U.complete C' hC' d hdmem) (hac.symm ▸ hcorv) (had.trans hac.symm) (by omega)
    hvc hsd.1

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ U
  exact ⟨certPropagation, fun hdisc =>
    ⟨honestSingleAck hdisc, certUniqueness hdisc, ackSkipExclusion hdisc,
      ackUnlockExclusionBelow hdisc⟩⟩

end CertificateExclusion

end RedSnapper

end LeanDag
