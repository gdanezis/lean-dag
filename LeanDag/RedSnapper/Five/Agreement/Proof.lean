import LeanDag.RedSnapper.Five.Agreement.Statement
import LeanDag.RedSnapper.Five.RecoverySafety.Proof
import LeanDag.RedSnapper.Five.FullCertSafety.Proof

/-!
# 5f+1 agreement — proof

Generated proof layer; not part of the audit surface. Route-pair
analysis, as in Theorem safety-5f: the certificate pairs close by RS6
(`FullCertSafety.commitExcludesUnlock`, `fullCertUniqueness`); the
certificate-versus-recovery pairs by RS7's reflection (the round
condition of the paper's miscited step — finding 9 — never arises,
because the reflection claim is round-unconditional); the
recovery-versus-unlock pair by RS7's `no_unlock_of_eligible`; the
recovery pairs by resolution uniqueness and antisymmetry. The two drops
of `FinalizeOnCommitTX`'s first loop close the same way: beside a
certified rival, by certificate uniqueness or by the reflection claim,
which makes the rival the only eligible transaction; above a resolution
not won, by the reflection claim, which would have made a certified
transaction the winner, or by resolution uniqueness. The two
certificate routes share their evidence (`evidence_of_final`), so the
pair analysis never distinguishes an owned from a mixed transaction.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveAgreement

open RecoverySafety FullCertSafety

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj} {A : Anchors U}

omit [DecidableEq BlockId] in
/-- What a finalising route rests on: a full certificate somewhere in
the universe (`fullFinal`, `mixedFinal`), or a recovery win. -/
private theorem evidence_of_final {V : View U} {prio : Tx → Tx → Prop} {tx : Tx}
    (h : VerdictFive U A V prio tx Fate.finalized) :
    (∃ C ∈ U.ids, IsFullCert U C tx) ∨
      ∃ (i j : ℕ) (aₖ a : BlockId), ResolvesFiveAt U A (T.input tx) i j ∧
        A.seq[i]? = some aₖ ∧ A.seq[j]? = some a ∧ EligibleFive U aₖ a (T.input tx) tx ∧
        ∀ tx', EligibleFive U aₖ a (T.input tx) tx' → prio tx tx' := by
  cases h with
  | fullFinal _ hC hcert => exact Or.inl ⟨_, V.subset_ids hC, hcert⟩
  | mixedFinal _ _ _ hC _ hcert => exact Or.inl ⟨_, hC, hcert⟩
  | recoveryFinal hres hlk hla helig hmin => exact Or.inr ⟨_, _, _, _, hres, hlk, hla, helig, hmin⟩

omit [DecidableEq BlockId] in
/-- No transaction is both finalised and dropped. -/
private theorem fate_exclusive {V V' : View U} {prio : Tx → Tx → Prop}
    (hord : IsLinearOrder Tx prio) (hfive : Five Validator) (hmove : MoveDiscipline U)
    (hfd : FreezeDiscipline U) {tx : Tx}
    (h₁ : VerdictFive U A V prio tx Fate.finalized)
    (h₂ : VerdictFive U A V' prio tx Fate.dropped) : False := by
  rcases evidence_of_final h₁ with ⟨C, hC, hcert⟩ | ⟨i, j, aₖ, a, hres, hlk, hla, helig, hmin⟩
  · cases h₂ with
    | fullUnlockDrop hC₂ hunlock hb hcand =>
        exact commitExcludesUnlock hmove _ hC _ (V'.subset_ids hC₂) tx hcert hunlock
    | recoveryDropLoser hres hlk hla hcand helig' hmin' hne' =>
        obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
          rfl ⟨C, hC, hcert⟩
        exact hne' (huniq _ helig').symm
    | recoveryDropBot hres hlk hla hcand hempty =>
        obtain ⟨helig, -⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
          rfl ⟨C, hC, hcert⟩
        exact hempty tx helig
    | observedRivalDrop _ _ hconf _ hC' hcert' =>
        exact fullCertUniqueness hmove _ hC _ (V'.subset_ids hC') _ _ hconf hcert hcert'
    | certifiedRivalDrop _ _ hconf hC' _ hcert' =>
        exact fullCertUniqueness hmove _ hC _ hC' _ _ hconf hcert hcert'
    | resolvedDrop hres hlk hlj _ _ _ hnw =>
        -- the certificate makes tx the unique eligible one, hence the winner
        obtain ⟨helig, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hlj
          rfl ⟨C, hC, hcert⟩
        haveI := hord
        exact hnw ⟨helig, fun tx' h' => huniq tx' h' ▸ refl_of prio tx⟩
  · cases h₂ with
    | fullUnlockDrop hC₂ hunlock hb hcand =>
        exact no_unlock_of_eligible hmove hfd (anchor_mem hla) helig
          _ (V'.subset_ids hC₂) hunlock
    | recoveryDropLoser hres' hlk' hla' hcand helig' hmin' hne' =>
        obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
          _ _ _ _ _ hres hres'
        subst hi
        subst hj
        rw [hlk] at hlk'
        rw [hla] at hla'
        rw [← Option.some.inj hlk', ← Option.some.inj hla'] at helig' hmin'
        haveI := hord
        exact hne' (antisymm (hmin' _ helig) (hmin _ helig')).symm
    | recoveryDropBot hres' hlk' hla' hcand hempty =>
        obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
          _ _ _ _ _ hres hres'
        subst hi
        subst hj
        rw [hlk] at hlk'
        rw [hla] at hla'
        rw [← Option.some.inj hlk', ← Option.some.inj hla'] at hempty
        exact hempty tx helig
    | observedRivalDrop _ _ hconf _ hC' hcert' =>
        -- the rival's certificate makes the rival the unique eligible one
        obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
          hconf.2.symm ⟨_, V'.subset_ids hC', hcert'⟩
        exact hconf.1 (huniq _ helig)
    | certifiedRivalDrop _ _ hconf hC' _ hcert' =>
        obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
          hconf.2.symm ⟨_, hC', hcert'⟩
        exact hconf.1 (huniq _ helig)
    | resolvedDrop hres' hlk' hlj' _ _ _ hnw =>
        obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
          _ _ _ _ _ hres hres'
        subst hi
        subst hj
        rw [hlk] at hlk'
        rw [hla] at hlj'
        rw [← Option.some.inj hlk', ← Option.some.inj hlj'] at hnw
        exact hnw ⟨helig, hmin⟩

omit [DecidableEq BlockId] in
theorem verdictAgreement {prio : Tx → Tx → Prop} (hord : IsLinearOrder Tx prio)
    (hfive : Five Validator) (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U) :
    VerdictAgreement U A prio := by
  intro V V' tx f f' h h'
  cases f <;> cases f'
  · rfl
  · exact absurd (fate_exclusive hord hfive hmove hfd h h') id
  · exact absurd (fate_exclusive hord hfive hmove hfd h' h) id
  · rfl

omit [DecidableEq BlockId] in
theorem noConflictingFinal {prio : Tx → Tx → Prop} (hord : IsLinearOrder Tx prio)
    (hfive : Five Validator) (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U) :
    NoConflictingFinal U A prio := by
  intro V V' tx tx' hconf h₁ h₂
  rcases evidence_of_final h₁ with ⟨C, hC, hcert⟩ | ⟨i, j, aₖ, a, hres, hlk, hla, helig, hmin⟩
  · rcases evidence_of_final h₂ with
      ⟨C', hC', hcert'⟩ | ⟨i', j', aₖ', a', hres', hlk', hla', helig', hmin'⟩
    · exact fullCertUniqueness hmove _ hC _ hC' tx tx' hconf hcert hcert'
    · obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres' hlk' hla'
        hconf.2 ⟨C, hC, hcert⟩
      exact hconf.1 (huniq _ helig').symm
  · rcases evidence_of_final h₂ with
      ⟨C', hC', hcert'⟩ | ⟨i', j', aₖ', a', hres', hlk', hla', helig', hmin'⟩
    · obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
        hconf.2.symm ⟨C', hC', hcert'⟩
      exact hconf.1 (huniq _ helig)
    · rw [← hconf.2] at hres' helig' hmin'
      obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
        _ _ _ _ _ hres hres'
      subst hi
      subst hj
      rw [hlk] at hlk'
      rw [hla] at hla'
      rw [← Option.some.inj hlk', ← Option.some.inj hla'] at helig' hmin'
      haveI := hord
      exact hconf.1 (antisymm (hmin _ helig') (hmin' _ helig))

omit [DecidableEq BlockId] in
theorem mixedViaAnchor {prio : Tx → Tx → Prop} : MixedViaAnchor U A prio := by
  intro V tx hmix h
  cases h with
  | fullFinal hown _ _ => exact absurd hmix hown
  | mixedFinal _ hlk hcand hC hr hcert =>
      exact ⟨_, _, hlk, hcand, Or.inl ⟨_, hC, hr, hcert⟩⟩
  | recoveryFinal hres hlk hla helig _ =>
      exact ⟨_, _, hla, helig.1, Or.inr ⟨_, _, hres, hlk, helig⟩⟩

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U A prio
  exact ⟨fun hord hfive hmove hfd =>
    ⟨verdictAgreement hord hfive hmove hfd, noConflictingFinal hord hfive hmove hfd⟩,
    mixedViaAnchor⟩

end FiveAgreement

end RedSnapper

end LeanDag
