import LeanDag.Adaptive.Policy
import LeanDag.Properties.Derived.Bounded
/-!
# The adaptive run, and safety as uniqueness of the fixpoint

A `Run` is a schedule-and-verdict pair coherent with a policy: every
slot's verdict is derivable with anchors inside its epoch window,
against the schedule the policy computes from the verdicts themselves.
Uniqueness (`run_agree`) is a strong induction on epochs: verdict
agreement below an epoch forces the two assignments to agree through it
(`adapted`), which forces verdict agreement at the epoch itself
(`DecidedBelow.reschedule`, then `Agree`) — with no fairness, synchrony
or view hypothesis, for arbitrary, even adversarial, policies.

Everything is stated over a `Properties.DagRule` and `Agree`; no
protocol is named. The induction runs over *partial* runs, closed up to
an epoch height, so two validators that have not decided equally far
still agree on their common prefix; total runs are the special case at
every height. `Policy.const_run_decided` anchors the definitions: under
the constant policy a run's verdicts are ordinary `Decided` verdicts of
the base schedule.
-/

namespace LeanDag

namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable [S : Slots Validator]

/-- A run closed up to epoch height `E`: verdicts derived for every slot
of epochs `< E`, the schedule coherent as far as those derivations read
it (epochs `< E + 1`). What a validator holds mid-execution. -/
structure PartialRun (P : Policy R) (U : R.Universe) (V : R.View U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- **The assignment is a lawful schedule.** Under one leader per
  round the rounds separate slots whatever the assignment names, and
  this is free; under multiple leaders a run must exhibit an assignment
  that does not collide two slots of one round onto one validator. -/
  keyed : ∀ k₁ k₂, S.slotRound k₁ = S.slotRound k₂ → assign k₁ = assign k₂ → k₁ = k₂
  /-- Every slot of a closed epoch is decided inside its window: anchors
  strictly below the start of epoch `e + 2`. -/
  closed : ∀ k, epochOf P.W k < E →
    DecidedBelow R (slotsOfKeyed assign keyed) (P.W * (epochOf P.W k + 2)) V k (vdct k)
  /-- The assignment is the policy's, computed on this view, as far as
  the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U V vdct m

/-- A total run: the adaptive fixpoint itself. -/
structure Run (P : Policy R) (U : R.Universe) (V : R.View U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- **The assignment is a lawful schedule.** Under one leader per
  round the rounds separate slots whatever the assignment names, and
  this is free; under multiple leaders a run must exhibit an assignment
  that does not collide two slots of one round onto one validator. -/
  keyed : ∀ k₁ k₂, S.slotRound k₁ = S.slotRound k₂ → assign k₁ = assign k₂ → k₁ = k₂
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, DecidedBelow R (slotsOfKeyed assign keyed)
    (P.W * (epochOf P.W k + 2)) V k (vdct k)
  /-- The assignment is the policy's, computed on this view, everywhere. -/
  coherent : ∀ m, assign m = P.pick U V vdct m

variable {P : Policy R} {U : R.Universe}

/-- A total run is partial at every height. -/
def Run.toPartial {V : R.View U} (A : Run P U V) (E : ℕ) : PartialRun P U V E where
  assign := A.assign
  vdct := A.vdct
  keyed := A.keyed
  closed := fun k _ => A.closed k
  coherent := fun m _ => A.coherent m

section Agreement

variable (ha : Agree R)
include ha

/-- **The master agreement lemma**: two partial runs over one universe,
whatever views and heights, agree on the verdicts of their common
epochs — the strong induction the module docstring describes. -/
theorem partialRun_agree {V₁ V₂ : R.View U} {E₁ E₂ : ℕ}
    (A₁ : PartialRun P U V₁ E₁) (A₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → A₁.vdct k = A₂.vdct k := by
  -- Strong induction on the epoch of the slot.
  suffices main : ∀ e k, epochOf P.W k = e → epochOf P.W k < min E₁ E₂ →
      A₁.vdct k = A₂.vdct k by
    intro k hk; exact main _ k rfl hk
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro k hke hk
    -- The assignments agree below this epoch's window.
    have hassign : ∀ m, m < P.W * (epochOf P.W k + 2) →
        A₁.assign m = A₂.assign m := by
      intro m hm
      have hme : epochOf P.W m < epochOf P.W k + 2 :=
        (epochOf_lt_iff P.W_pos).mpr hm
      rw [A₁.coherent m (by omega), A₂.coherent m (by omega)]
      refine P.adapted U V₁ V₂ A₁.vdct A₂.vdct m (fun j hj => ?_)
      exact ih (epochOf P.W j) (by omega) j rfl (by omega)
    -- Both derivations live in one instance; agreement is `Agree`.
    have h₁ := A₁.closed k (by omega)
    have h₂ := A₂.closed k (by omega)
    exact DecidedBelow.agree ha (h₁.reschedule (S' := slotsOfKeyed A₂.assign A₂.keyed) rfl
      (fun m hm => (hassign m hm).symm)) h₂

/-- Assignments agree wherever the common verdicts determine them. -/
theorem partialRun_assign_agree {V₁ V₂ : R.View U} {E₁ E₂ : ℕ}
    (A₁ : PartialRun P U V₁ E₁) (A₂ : PartialRun P U V₂ E₂) :
    ∀ m, epochOf P.W m < min E₁ E₂ + 1 → A₁.assign m = A₂.assign m := by
  intro m hm
  rw [A₁.coherent m (by omega), A₂.coherent m (by omega)]
  refine P.adapted U V₁ V₂ A₁.vdct A₂.vdct m (fun j hj => ?_)
  exact partialRun_agree ha A₁ A₂ j (by omega)

/-- **Safety: the adaptive fixpoint is unique.** Two total runs over one
universe, from any two views and with no synchrony or fairness
hypothesis, hold the same verdicts and run the same schedule. -/
theorem run_agree {V₁ V₂ : R.View U} (A₁ : Run P U V₁) (A₂ : Run P U V₂) :
    (∀ k, A₁.vdct k = A₂.vdct k) ∧ (∀ m, A₁.assign m = A₂.assign m) := by
  constructor
  · intro k
    exact partialRun_agree ha (A₁.toPartial (epochOf P.W k + 1))
      (A₂.toPartial (epochOf P.W k + 1)) k (by omega)
  · intro m
    exact partialRun_assign_agree ha (A₁.toPartial (epochOf P.W m + 1))
      (A₂.toPartial (epochOf P.W m + 1)) m (by omega)

/-- **AL6 — the adaptive ledger is agreed.** The commit sequence read
off any two total runs is the same list, at every length. -/
theorem run_commitSeq_agree (ha : Agree R) {V₁ V₂ : R.View U}
    (A₁ : Run P U V₁) (A₂ : Run P U V₂) (n : ℕ) :
    commitSeq A₁.vdct n = commitSeq A₂.vdct n := by
  rw [funext (run_agree ha A₁ A₂).1]

end Agreement

/-- **Conservativity.** Under the constant policy a run's verdicts are
ordinary `Decided` verdicts of the base schedule. -/
theorem Policy.const_run_decided
    {W : ℕ} {hW : 0 < W} {hinj : Function.Injective S.slotRound} {V : R.View U}
    (A : Run (Policy.const (R := R) W hW hinj) U V) (k : ℕ) :
    R.Decided S V k (A.vdct k) := by
  have h := (A.closed k).reschedule (S' := slotsOf hinj S.leader) rfl
    (fun m _ => (A.coherent m).symm)
  rw [slotsOf_base hinj] at h
  exact h.toDecided

end Adaptive

end LeanDag
