import LeanDag.RedSnapper.Five.Termination.Statement
import LeanDag.RedSnapper.Five.RecoveryTermination.Proof

/-!
# Termination at 5f+1 — proof

Generated proof layer; not part of the audit surface. The cases of
`ConflictDecides`, followed for one transaction. A full unlock
certificate drops it as a candidate of its anchor. A full certificate on
the object is its own — final on observation if owned, under the anchor
the premise supplies if mixed — or a rival's: an owned rival's is in the
view and `observedRivalDrop` fires at the transaction's anchor; a mixed
rival's lies under an anchor, and the later of that anchor and the
transaction's holds both. With no certificate anywhere the ordered rival
and the transaction are both candidates of the later of their anchors,
which therefore sees the conflict; RS9b gives the trigger and the
resolution; at or below the resolving anchor the transaction is one of
its candidates and `RecoveryDecides` applies, and above it the
transaction either won — eligibility carries candidacy at the resolving
anchor — or is dropped by `resolvedDrop`.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveTermination

open RecoveryTermination

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj} {A : Anchors U}

omit [DecidableEq BlockId] in
theorem decided : Decided U A := by
  intro prio hord V tx m a hfull hm hcand hC5 hrest
  classical
  have ha : a ∈ U.ids := anchor_mem hm
  by_cases hun : ∃ C ∈ U.ids, IsFullUnlockCert U C (T.input tx)
  · -- a full unlock certificate: the view drops the candidate
    obtain ⟨C, hC, hunl⟩ := hun
    exact Or.inr (.fullUnlockDrop (hfull hC) hunl (hfull ha) hcand)
  by_cases hce : ∃ tx', T.input tx' = T.input tx ∧ ∃ C ∈ U.ids, IsFullCert U C tx'
  · obtain ⟨tx', ho, C, hC, hcert⟩ := hce
    by_cases heq : tx' = tx
    · -- its own certificate
      left
      have hcert' : IsFullCert U C tx := heq ▸ hcert
      by_cases hmix : T.Mixed tx
      · obtain ⟨k, a', hk, hr⟩ := hC5 tx hmix rfl C hC hcert'
        exact .mixedFinal hmix hk (isCandidate_mono hr (isCandidate_of_fullCert hcert'))
          hC hr hcert'
      · exact .fullFinal hmix (hfull hC) hcert'
    · -- a rival's certificate
      right
      have hconf' : Conflict tx tx' := ⟨fun h => heq h.symm, ho.symm⟩
      by_cases hmix' : T.Mixed tx'
      · -- mixed: the later of the two anchors holds both
        obtain ⟨k, a', hk, hr⟩ := hC5 tx' hmix' ho C hC hcert
        rcases Nat.le_total k m with hkm | hmk
        · exact .certifiedRivalDrop hm hcand hconf' hC
            ((anchor_reaches hkm hk hm).trans hr) hcert
        · exact .certifiedRivalDrop hk (isCandidate_mono (anchor_reaches hmk hm hk) hcand)
            hconf' hC hr hcert
      · -- owned: observed, as its finalization is
        exact .observedRivalDrop hm hcand hconf' hmix' (hfull hC) hcert
  · -- no certificate anywhere: trigger, resolution, decision
    have hnoun : ∀ C ∈ U.ids, ¬ IsFullUnlockCert U C (T.input tx) :=
      fun C hC h => hun ⟨C, hC, h⟩
    have hnoce : ∀ tx', T.input tx' = T.input tx → ∀ C ∈ U.ids, ¬ IsFullCert U C tx' :=
      fun tx' ho C hC h => hce ⟨tx', ho, C, hC, h⟩
    obtain ⟨⟨k, a', tx', hk, hcand', hne⟩, hmarkers⟩ := hrest hnoun hnoce
    -- the later of the two anchors sees the conflict
    obtain ⟨i, aᵢ, hi, hconf⟩ : ∃ i aᵢ, A.seq[i]? = some aᵢ ∧ Conflicted U aᵢ (T.input tx) := by
      rcases Nat.le_total k m with hkm | hmk
      · exact ⟨m, a, hm, tx, tx', hcand,
          isCandidate_mono (anchor_reaches hkm hk hm) hcand', fun h => hne h.symm⟩
      · exact ⟨k, a', hk, tx, tx',
          isCandidate_mono (anchor_reaches hmk hm hk) hcand, hcand', fun h => hne h.symm⟩
    obtain ⟨i', -, htrig⟩ := triggerExists (T.input tx) i aᵢ hi hconf hnoun hnoce
    obtain ⟨aₖ, hlkₖ, -⟩ := htrig.1
    obtain ⟨hnopre, j, a'', hla', hfroz⟩ := hmarkers i' aₖ htrig hlkₖ
    obtain ⟨j', -, -, hres⟩ :=
      resolutionExists (T.input tx) i' j aₖ a'' htrig hlkₖ hla' hnopre hfroz
    obtain ⟨-, aⱼ, -, hlaⱼ, -⟩ := hres.2.2.1
    rcases Nat.lt_or_ge j' m with hjm | hmj
    · -- above the resolving anchor: the winner, or dropped
      by_cases hw : EligibleFive U aₖ aⱼ (T.input tx) tx ∧
          ∀ tx', EligibleFive U aₖ aⱼ (T.input tx) tx' → prio tx tx'
      · exact Or.inl (.recoveryFinal hres hlkₖ hlaⱼ hw.1 hw.2)
      · exact Or.inr (.resolvedDrop hres hlkₖ hlaⱼ hm hjm hcand hw)
    · -- at or below it: one of its candidates
      exact recoveryDecides prio hord V (T.input tx) i' j' aⱼ tx hres hlaⱼ
        (isCandidate_mono (anchor_reaches hmj hm hlaⱼ) hcand)

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U A
  exact decided

end FiveTermination

end RedSnapper

end LeanDag
