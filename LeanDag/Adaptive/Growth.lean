import LeanDag.Adaptive.Run
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
/-!
# The fixpoint under growth of the DAG

`run_agree` is agreement over one universe; this composes `Persist`
with the fixpoint to ask whether a validator's run at `U` is the prefix
of another's at `U' ⊇ U`. One clause is owed by the policy alone:
`adapted` quantifies views over *one* universe, so a policy reading the
size of the universe could reassign differently at `U'` — `Policy.Stable`
rules this out. The argument is `partialRun_agree`'s induction with one
extra step per epoch: the smaller run's verdict is carried to the
larger view by `Persist`, and the two agree by `Agree`.
-/

namespace LeanDag

namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **Stability under extension.** The rule returns the same leader for
the same verdicts on an extended universe. -/
def Policy.Stable {R : DagRule Validator BlockId Payload} (P : Policy R) : Prop :=
  ∀ (U U' : R.Universe), Extends R U U' → ∀ (V : R.View U) (V' : R.View U')
    (v : ℕ → Option BlockId) (k : ℕ), P.pick U V v k = P.pick U' V' v k

/-- The constant policy is stable. -/
theorem Policy.const_stable {R : DagRule Validator BlockId Payload} (W : ℕ) (hW : 0 < W)
    (hinj : Function.Injective S.slotRound) : (Policy.const (R := R) W hW hinj).Stable :=
  fun _ _ _ _ _ _ _ => rfl

section Growth

variable {R : DagRule Validator BlockId Payload} {P : Policy R}
variable (ha : Agree R) (hp : Persist R) (hst : P.Stable)
include ha hp hst

variable {U U' : R.Universe} {V : R.View U} {V' : R.View U'}

/-- **Partial runs agree across growth.** A run on `U` and a run on an
extension `U'`, from views one contained in the other, agree on the
verdicts of their common epochs. -/
theorem partialRun_agree_extends (hext : Extends R U U')
    (hsub : R.viewIds V ⊆ R.viewIds V') {E E' : ℕ}
    (A : PartialRun P U V E) (A' : PartialRun P U' V' E') :
    ∀ k, epochOf P.W k < min E E' → A.vdct k = A'.vdct k := by
  suffices main : ∀ e k, epochOf P.W k = e → epochOf P.W k < min E E' →
      A.vdct k = A'.vdct k by
    intro k hk; exact main _ k rfl hk
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro k hke hk
    -- The assignments agree below this epoch's window: `Stable` carries
    -- the smaller run's rule to `U'`, `adapted` the verdicts.
    have hassign : ∀ m, m < P.W * (epochOf P.W k + 2) → A.assign m = A'.assign m := by
      intro m hm
      have hme : epochOf P.W m < epochOf P.W k + 2 := (epochOf_lt_iff P.W_pos).mpr hm
      rw [A.coherent m (by omega), A'.coherent m (by omega), hst U U' hext V V' A.vdct m]
      refine P.adapted U' V' V' A.vdct A'.vdct m (fun j hj => ?_)
      exact ih (epochOf P.W j) (by omega) j rfl (by omega)
    -- The smaller run's verdict, persisted to the larger view.
    have h₁ : R.Decided (slotsOfKeyed A.assign A.keyed) V' k (A.vdct k) :=
      hp _ U U' hext V V' hsub k _ (A.closed k (by omega)).toDecided
    -- The larger run's verdict, transported to the smaller run's schedule.
    have h₂ : R.Decided (slotsOfKeyed A.assign A.keyed) V' k (A'.vdct k) :=
      ((A'.closed k (by omega)).reschedule (S' := slotsOfKeyed A.assign A.keyed) rfl
        (fun m hm => hassign m hm)).toDecided
    exact ha _ V' V' k _ _ h₁ h₂

/-- Assignments agree across growth wherever the common verdicts
determine them. -/
theorem partialRun_assign_agree_extends (hext : Extends R U U')
    (hsub : R.viewIds V ⊆ R.viewIds V') {E E' : ℕ}
    (A : PartialRun P U V E) (A' : PartialRun P U' V' E') :
    ∀ m, epochOf P.W m < min E E' + 1 → A.assign m = A'.assign m := by
  intro m hm
  rw [A.coherent m (by omega), A'.coherent m (by omega), hst U U' hext V V' A.vdct m]
  refine P.adapted U' V' V' A.vdct A'.vdct m (fun j hj => ?_)
  exact partialRun_agree_extends ha hp hst hext hsub A A' j (by omega)

/-- **The fixpoint is a prefix of the fixpoint on any extension.** Two
total runs, on a universe and an extension of it, hold the same
verdicts and run the same schedule. -/
theorem run_agree_extends (hext : Extends R U U')
    (hsub : R.viewIds V ⊆ R.viewIds V') (A : Run P U V) (A' : Run P U' V') :
    (∀ k, A.vdct k = A'.vdct k) ∧ (∀ m, A.assign m = A'.assign m) := by
  constructor
  · intro k
    exact partialRun_agree_extends ha hp hst hext hsub
      (A.toPartial (epochOf P.W k + 1)) (A'.toPartial (epochOf P.W k + 1)) k (by omega)
  · intro m
    exact partialRun_assign_agree_extends ha hp hst hext hsub
      (A.toPartial (epochOf P.W m + 1)) (A'.toPartial (epochOf P.W m + 1)) m (by omega)

end Growth

end Adaptive

end LeanDag
