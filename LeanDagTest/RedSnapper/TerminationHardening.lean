import LeanDagTest.RedSnapper.Coin
import LeanDag.RedSnapper.Five.Agreement.Proof
import LeanDag.RedSnapper.Five.RecoveryTermination.Proof
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness hardening: recovery termination

Adopted from the Phase 9 vacuity audit: `ResolutionExists` without the
no-quorum-below premise is false (on `U6RecPre`, where the markers sit
in the trigger's own history and the paper-exact one-shot refuses every
index); RS8's hypotheses are co-inhabited with a derivable verdict on
`U6Rec`, where agreement then refutes the dropped side; and `Triggers`'
certificate-absence conjuncts discriminate against a conflict-only
mutant.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### No-quorum-below necessity; disjunct correspondence; the tie -/

/-! ## G: ResolutionExists' no-quorum-below premise is load-bearing -/

-- The trigger sits at 1, anchor 17 sits later at 2 ...
example : TriggerAt U6RecPre ARecPre 0 1 := triggerAt_iff.mpr (by decide)
example : (ARecPre.seq)[1]? = some 6 ∧ (ARecPre.seq)[2]? = some 17 ∧ (1 : ℕ) < 2 := by
  decide

-- ... every correct validator's marker is visible at it ...
private theorem pre_frozen_all : ∀ v ∈ (Correct : Finset (Fin 6)),
    FrozenDec U6RecPre 6 v 0 17 := by decide
example : ∀ v ∈ (Correct : Finset (Fin 6)), Frozen U6RecPre 6 v 0 17 :=
  fun v hv => (frozen_iff (by decide)).mpr (pre_frozen_all v hv)

-- ... but the dropped premise is false — a quorum already at the
-- trigger itself ...
example : FreezeQuorum U6RecPre 6 0 6 := (freezeQuorum_iff (by decide)).mpr (by decide)

-- ... and the conclusion FAILS: no index in (1, 2] resolves.
example : ¬ ∃ j', 1 < j' ∧ j' ≤ 2 ∧ ResolvesFiveAt U6RecPre ARecPre 0 1 j' := by
  rintro ⟨j', h1, h2, hres⟩
  have hj : j' = 2 := by omega
  subst hj
  exact absurd (resolvesFiveAt_iff.mp hres) (by decide)

/-! ## H: RS8's hypotheses are co-inhabited with a derivable verdict -/

-- On `U6Rec` the order, the committee bound and both disciplines hold
-- together with the committed `recoveryFinal` pin, so verdict agreement
-- applies to real data: the winner has no dropped verdict.
example : ¬ VerdictFive U6Rec ARec (View.full U6Rec) (· ≤ ·) 0 Fate.dropped := fun h =>
  absurd
    (FiveAgreement.verdictAgreement (U := U6Rec) (A := ARec)
      (prio := (· ≤ ·)) inferInstance (inferInstance : Five (Fin 6))
      (moveDiscipline_iff.mpr (by decide)) (freezeDiscipline_iff.mpr (by decide))
      (View.full U6Rec) (View.full U6Rec) 0 Fate.finalized Fate.dropped
      (.recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
        (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
        ((eligibleFive_iff (by decide)).mpr (by decide))
        (fun _ _ => Fin.zero_le _))
      h)
    (by decide)

/-! ### Arc audit: `Triggers`' certificate-absence conjuncts are never negatively
discriminated: a conflict-only mutant passes the committed suite. -/

/-- The mutant: `Triggers` reduced to its conflict conjunct. -/
def TriggersMut {Validator BlockId Tx Obj : Type*} [Fintype Validator]
    [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj]
    [Faults Validator] [T : Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (a : BlockId) (o : Obj) : Prop :=
  ∃ tx ∈ candidates U a o, ∃ tx' ∈ candidates U a o, tx ≠ tx'

instance {Validator BlockId Tx Obj : Type*} [Fintype Validator]
    [DecidableEq Validator] [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj]
    [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (a : BlockId) (o : Obj) :
    Decidable (TriggersMut U a o) := by
  unfold TriggersMut; infer_instance

-- Missing witness 1: anchor 17 of U6RecFull has the full certificate
-- (block 12) in its history, so it does NOT trigger — the mutant says
-- it does.
example : ¬ Triggers U6RecFull 17 0 := fun h =>
  absurd ((triggers_iff (by decide)).mp h) (by decide)
example : TriggersMut U6RecFull 17 0 := by decide

-- Missing witness 2: block 17 of U6Frag IS a full unlock certificate
-- (reflexive Reaches), so it does not trigger — the mutant says it does.
example : ¬ Triggers U6Frag 17 0 := fun h =>
  absurd ((triggers_iff (by decide)).mp h) (by decide)
example : TriggersMut U6Frag 17 0 := by decide

end RedSnapper

end LeanDagTest
