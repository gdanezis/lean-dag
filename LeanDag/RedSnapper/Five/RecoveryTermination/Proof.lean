import LeanDag.RedSnapper.Five.RecoveryTermination.Statement
import LeanDag.RedSnapper.Helpers.Coin
import LeanDag.RedSnapper.Helpers.Liveness

/-!
# Recovery termination — proof

Generated proof layer; not part of the audit surface. The two existence
claims are `Nat.find` on the trigger and quorum predicates — the
certificate-free hypothesis makes the given anchor trigger, full marker
visibility makes the given anchor carry a correct quorum, and the least
such indices are the trigger and resolution. The decision claim picks
the `prio`-minimal eligible transaction with `exists_prio_min` over the
anchor's carried transactions (`txsIn`), and lands in the matching
verdict constructor.
-/

namespace LeanDag

namespace RedSnapper

namespace RecoveryTermination

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj} {A : Anchors U}

omit [DecidableEq BlockId] in
theorem triggerExists : TriggerExists U A := by
  intro o i a hlk hconf hnounlock hnocert
  have htrig : Triggers U a o := by
    refine ⟨hconf, ?_, ?_⟩
    · rintro ⟨b, hb, -, hcert⟩
      exact hnounlock b hb hcert
    · rintro ⟨tx, hcand, b, hb, -, hcert⟩
      exact hnocert tx hcand.2.1 b hb hcert
  classical
  have hex : ∃ i', ∃ a', A.seq[i']? = some a' ∧ Triggers U a' o := ⟨i, a, hlk, htrig⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨a, hlk, htrig⟩,
    Nat.find_spec hex, fun j hj a'' hl ht => ?_⟩
  exact absurd ⟨a'', hl, ht⟩ (Nat.find_min hex hj)

omit [DecidableEq BlockId] in
theorem resolutionExists : ResolutionExists U A := by
  intro o i j aₖ a htrig hlk hla hnopre hfrozen
  classical
  have hq : FreezeQuorum U aₖ o a :=
    ⟨(Correct : Finset Validator), fun v hv => hfrozen v hv, quorum_le_card_correct⟩
  have hex : ∃ j', ∃ a', A.seq[j']? = some a' ∧ FreezeQuorum U aₖ o a' := ⟨j, a, hla, hq⟩
  obtain ⟨a₀, hla₀, hq₀⟩ := Nat.find_spec hex
  have hj₀j : Nat.find hex ≤ j := Nat.find_min' hex ⟨a, hla, hq⟩
  have hij₀ : i < Nat.find hex := by
    by_contra hle
    push Not at hle
    exact hnopre (Nat.find hex) hle a₀ hla₀ hq₀
  refine ⟨Nat.find hex, hij₀, hj₀j,
    htrig, hij₀, ⟨aₖ, a₀, hlk, hla₀, hq₀⟩, ?_⟩
  intro j' hj' aₖ' a' hlk' hla' hq'
  rw [hlk] at hlk'
  rw [← Option.some.inj hlk'] at hq'
  exact absurd ⟨a', hla', hq'⟩ (Nat.find_min hex hj')

omit [DecidableEq BlockId] in
theorem recoveryDecides : RecoveryDecides U A := by
  intro prio hord V o i j a tx hres hla hcand
  classical
  have ho : T.input tx = o := hcand.2.1
  subst ho
  obtain ⟨htrig, hij, ⟨aₖ, a', hlk, hla', hq⟩, hleast⟩ := hres
  rw [hla] at hla'
  obtain rfl := Option.some.inj hla'
  have ha : a ∈ U.ids := anchor_mem hla
  have hres' : ResolvesFiveAt U A (T.input tx) i j :=
    ⟨htrig, hij, ⟨aₖ, a, hlk, hla, hq⟩, hleast⟩
  by_cases helig : ∃ tx', EligibleFive U aₖ a (T.input tx) tx'
  · obtain ⟨tx₀, htx₀⟩ := helig
    have hmemE : ∀ tx', EligibleFive U aₖ a (T.input tx) tx' → tx' ∈ txsIn U a := by
      intro tx' h'
      exact (mem_txsIn_iff ha).mpr h'.1.2.2
    have hE : ((txsIn U a).filter
        (fun tx' => EligibleFive U aₖ a (T.input tx) tx')).Nonempty :=
      ⟨tx₀, Finset.mem_filter.mpr ⟨hmemE tx₀ htx₀, htx₀⟩⟩
    haveI := hord
    obtain ⟨m, hmE, hmin⟩ := exists_prio_min (r := prio)
      (fun x y => total_of prio x y)
      (fun hab hbc => trans_of prio hab hbc) hE
    have hmelig : EligibleFive U aₖ a (T.input tx) m := (Finset.mem_filter.mp hmE).2
    have hminall : ∀ tx', EligibleFive U aₖ a (T.input tx) tx' → prio m tx' :=
      fun tx' h' => hmin tx' (Finset.mem_filter.mpr ⟨hmemE tx' h', h'⟩)
    by_cases htxm : tx = m
    · subst htxm
      exact Or.inl (.recoveryFinal hres' hlk hla hmelig hminall)
    · exact Or.inr (.recoveryDropLoser hres' hlk hla hcand hmelig hminall htxm)
  · push Not at helig
    exact Or.inr (.recoveryDropBot hres' hlk hla hcand helig)

omit [DecidableEq BlockId] in
theorem conflictDecides : ConflictDecides U A := by
  intro prio hord V o i a hfull hlk hconf hmixed hmarkers
  classical
  have ha : a ∈ U.ids := anchor_mem hlk
  by_cases hun : ∃ C ∈ U.ids, IsFullUnlockCert U C o
  · -- a full unlock certificate: the view drops a candidate of the anchor
    obtain ⟨C, hC, hunl⟩ := hun
    obtain ⟨tx, -, hc, -, -⟩ := hconf
    obtain rfl : T.input tx = o := hc.2.1
    exact ⟨tx, rfl, Or.inr (.fullUnlockDrop (hfull hC) hunl (hfull ha) hc)⟩
  by_cases hce : ∃ tx, T.input tx = o ∧ ∃ C ∈ U.ids, IsFullCert U C tx
  · -- a full certificate: final on observation if owned, under an anchor if mixed
    obtain ⟨tx, rfl, C, hC, hcert⟩ := hce
    refine ⟨tx, rfl, Or.inl ?_⟩
    by_cases hm : T.Mixed tx
    · obtain ⟨i', a', hlk', hr⟩ := hmixed tx hm rfl C hC hcert
      exact .mixedFinal hm hlk' (isCandidate_mono hr (isCandidate_of_fullCert hcert))
        hC hr hcert
    · exact .fullFinal hm (hfull hC) hcert
  · -- neither, anywhere: trigger, resolution, decision
    have hnoun : ∀ C ∈ U.ids, ¬ IsFullUnlockCert U C o := fun C hC h => hun ⟨C, hC, h⟩
    have hnoce : ∀ tx, T.input tx = o → ∀ C ∈ U.ids, ¬ IsFullCert U C tx :=
      fun tx ho C hC h => hce ⟨tx, ho, C, hC, h⟩
    obtain ⟨i', -, htrig⟩ := triggerExists o i a hlk hconf hnoun hnoce
    obtain ⟨aₖ, hlkₖ, htr⟩ := htrig.1
    obtain ⟨hnopre, j, a', hla', hfroz⟩ := hmarkers hnoun hnoce i' aₖ htrig hlkₖ
    obtain ⟨j', hij', -, hres⟩ :=
      resolutionExists o i' j aₖ a' htrig hlkₖ hla' hnopre hfroz
    obtain ⟨-, a'', -, hla'', -⟩ := hres.2.2.1
    -- the trigger's own candidates are candidates of the later resolving anchor
    obtain ⟨c, -, hcc, -, -⟩ := htr.1
    have hcand : IsCandidate U a'' o c :=
      isCandidate_mono (anchor_reaches (Nat.le_of_lt hij') hlkₖ hla'') hcc
    exact ⟨c, hcc.2.1, recoveryDecides prio hord V o i' j' a'' c hres hla'' hcand⟩

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U A
  exact ⟨triggerExists, resolutionExists, recoveryDecides, conflictDecides⟩

end RecoveryTermination

end RedSnapper

end LeanDag
