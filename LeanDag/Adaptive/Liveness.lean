import LeanDag.Adaptive.Run
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Derived.Descent
/-!
# Liveness: the adaptive fixpoint exists

Safety (`run_agree`) is uniqueness of the run; this file is existence,
from the two liveness properties of `Properties/Commit.lean` — a
reliable leader's slot commits (`LeaderCommits`), a committed run
decides everything below it (`Descends`) — plus the one clause that
prices the policy's choices: `PlacesRuns`, the adaptive counterpart of
`FairRunOn`. Every assignment the policy can emit must contain, in each
epoch after the first, `c` consecutive `T`-led slots. Hammerhead's
purpose lands on this clause: a policy that reacts to observed skips
satisfies it by construction where a blind rotation satisfies it by
assumption — but which validators are reliable is not the designer's to
know, so it remains a joint condition exactly as P10 is.

The construction is by strong recursion on epochs, one application of
`LeaderCommits` per run slot and nothing counted anew. The run that
`PlacesRuns` puts in epoch `e + 1` commits, `Descends` decides every
slot below the run with anchors under the run's top, strictly inside
epoch `e`'s window, and `Bounded.mono` relaxes to the window. Partial
runs at every height glue into a total run along the diagonal, with
`partialRun_agree` supplying the coherence that the stage-by-stage
choices need not.

**The precondition is staged.** `Live` is the protocol's liveness
precondition, indexed by the schedule and by a slot window, and the
existence theorems ask for it at every height `E`, under the schedule
the policy computes from any height-`E` partial run's verdicts, over the
slots `[W, W·(E+2))` that schedule has determined. For the timed core
the precondition reads no leader and the staged form follows from the
usual global one (`Adaptive/Mysticeti.lean`); for a reactive execution
the staging is the honest statement, since its clauses hold only under
the schedule the validators actually followed.
-/

namespace LeanDag

namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **The adaptive fairness clause.** Every assignment the policy can
emit places, in each epoch past the base prefix, a run of `c`
consecutive `T`-led slots. The clause liveness prices and safety never
sees: `run_agree` holds for policies that violate it. -/
def PlacesRuns {R : DagRule Validator BlockId Payload} (P : Policy R)
    (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (v : ℕ → Option BlockId) (e : ℕ),
    ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → P.pick U V v (b + i) ∈ T

/-- **A rule's descent, at every induced schedule.** The indirect
property is stated over the round structure alone, which reassignment
fixes, so a spanning clause at the base schedule gives the descent at
each induced one. -/
theorem descends_slotsOf {R : DagRule Validator BlockId Payload} {wave : ℕ}
    (hind : Indirect R (fun sr i j => sr i + wave + 1 ≤ sr j))
    {c : ℕ} (hc : 0 < c) (hspans : SpansEligibleAt (S := S) wave c)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator) :
    Descends R (slotsOf hinj a) c :=
  Descends.of_indirect hind hc fun b i hi =>
    (eligibleAt_iff (S := slotsOf hinj a)).mp (spansEligible_slotsOf hinj a hspans b i hi)

section Existence

variable {R : DagRule Validator BlockId Payload} {P : Policy R}
variable {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop}
variable {T : Finset Validator} {c : ℕ} {U : R.Universe}

/-- **One epoch closes.** Against the schedule an arbitrary verdict
function induces, with the protocol's precondition over the slots that
schedule determines, every slot of epoch `E` is decided inside its
window: the run `PlacesRuns` puts in epoch `E + 1` commits, and the
descent clears everything below it. -/
theorem epoch_closes (hlc : LeaderCommits R Live)
    (hd : ∀ a : ℕ → Validator, Descends R (slotsOf P.inj a) c)
    (hruns : PlacesRuns P T c)
    (V : R.View U) (v : ℕ → Option BlockId) (E : ℕ)
    (hlive : Live (slotsOf P.inj (fun m => P.pick U V v m)) V T P.W (P.W * (E + 2))) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedBelow R (slotsOf P.inj (fun m => P.pick U V v m))
        (P.W * (E + 2)) V k w := by
  obtain ⟨b, hb1, hb2, hbT⟩ := hruns U V v E
  have hWpos := P.W_pos
  -- Every run slot is committed, inside the run's bound.
  have hrun : ∀ j, b ≤ j → j < b + c →
      ∃ L, DecidedBelow R (slotsOf P.inj (fun m => P.pick U V v m)) (b + c) V j (some L) := by
    intro j hj1 hj2
    have hlead : (slotsOf P.inj (fun m => P.pick U V v m)).leader j ∈ T := by
      have := hbT (j - b) (by omega)
      have hjb : b + (j - b) = j := by omega
      rw [hjb] at this
      exact this
    have hWle : P.W ≤ j := by
      have h1 : P.W * 1 ≤ P.W * (E + 1) := Nat.mul_le_mul_left P.W (by omega)
      omega
    obtain ⟨L, hL⟩ := hlc _ V T P.W (P.W * (E + 2)) hlive j hWle (by omega) hlead
    exact ⟨L, hL.mono (by omega)⟩
  -- The descent clears everything below the run — all of epoch `E`.
  have hbelow := hd (fun m => P.pick U V v m) V b hrun
  intro k hk
  have hkb : k < b :=
    lt_of_lt_of_le ((epochOf_lt_iff hWpos).mp hk) hb1
  obtain ⟨w, hw⟩ := hbelow k hkb
  exact ⟨w, hw.mono hb2⟩

/-- **Partial runs exist at every height** — the witnessable, finite-
horizon form of existence, by induction on the height: each stage
re-reads the schedule off the verdicts so far and closes one more
epoch, under the precondition for that stage's schedule. -/
theorem exists_partialRun (hlc : LeaderCommits R Live)
    (hd : ∀ a : ℕ → Validator, Descends R (slotsOf P.inj a) c)
    (hruns : PlacesRuns P T c) (V : R.View U) (E : ℕ)
    (hlive : ∀ (E' : ℕ), E' < E → ∀ (A : PartialRun P U V E'),
      Live (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E' + 2))) :
    Nonempty (PartialRun P U V E) := by
  classical
  induction E with
  | zero =>
      exact ⟨{ assign := fun m => P.pick U V (fun _ => none) m
               vdct := fun _ => none
               closed := fun k hk => absurd hk (by omega)
               coherent := fun _ _ => rfl }⟩
  | succ E ih =>
      obtain ⟨A₀⟩ := ih (fun E' hE' A => hlive E' (by omega) A)
      have hclose := epoch_closes hlc hd hruns V A₀.vdct E (hlive E (by omega) A₀)
      -- The new verdicts: epoch `E` freshly decided, everything below kept.
      set v' : ℕ → Option BlockId := fun k =>
        if h : epochOf P.W k = E then (hclose k (by omega)).choose
        else A₀.vdct k with hv'
      -- The new verdicts agree with the old below epoch `E`.
      have hagree : ∀ j, epochOf P.W j < E → v' j = A₀.vdct j := by
        intro j hj
        simp only [hv', dif_neg (by omega : ¬ epochOf P.W j = E)]
      -- The two induced schedules agree below epoch `E + 2`.
      have hsched : ∀ m, m < P.W * (E + 2) →
          P.pick U V A₀.vdct m = P.pick U V v' m := by
        intro m hm
        refine P.adapted U V V A₀.vdct v' m (fun j hj => ?_)
        have hjE : epochOf P.W j < E := by
          have := (epochOf_lt_iff P.W_pos).mpr hm
          omega
        exact (hagree j hjE).symm
      refine ⟨{ assign := fun m => P.pick U V v' m
                vdct := v'
                closed := ?_
                coherent := fun _ _ => rfl }⟩
      intro k hk
      by_cases hkE : epochOf P.W k = E
      · -- The fresh epoch: transport its derivation across the schedules.
        have hspec := (hclose k (by omega)).choose_spec
        have : v' k = (hclose k (by omega)).choose := by
          simp only [hv', dif_pos hkE]
        rw [this, hkE]
        exact hspec.reschedule (S' := slotsOf P.inj (fun m => P.pick U V v' m)) rfl
          (fun m hm => (hsched m hm).symm)
      · -- An old epoch: transport the old derivation.
        have hkE' : epochOf P.W k < E := by omega
        have hold := A₀.closed k hkE'
        have hsched' : ∀ m, m < P.W * (epochOf P.W k + 2) →
            A₀.assign m = P.pick U V v' m := by
          intro m hm
          have hmE : epochOf P.W m < epochOf P.W k + 2 :=
            (epochOf_lt_iff P.W_pos).mpr hm
          rw [A₀.coherent m (by omega)]
          refine P.adapted U V V A₀.vdct v' m (fun j hj => ?_)
          exact (hagree j (by omega)).symm
        have := hold.reschedule (S' := slotsOf P.inj (fun m => P.pick U V v' m)) rfl
          (fun m hm => (hsched' m hm).symm)
        rw [hagree k hkE']
        exact this

/-- **The adaptive fixpoint exists.** Under a policy that places runs,
with the protocol's precondition at every height, a total adaptive run
exists — partial runs at every height glued along the diagonal,
`partialRun_agree` making the stage-by-stage choices cohere. With
`run_agree` it is THE fixpoint. -/
theorem run_exists (ha : Agree R) (hlc : LeaderCommits R Live)
    (hd : ∀ a : ℕ → Validator, Descends R (slotsOf P.inj a) c)
    (hruns : PlacesRuns P T c) (V : R.View U)
    (hlive : ∀ (E : ℕ) (A : PartialRun P U V E),
      Live (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E + 2))) :
    Nonempty (Run P U V) := by
  classical
  -- A partial run at every height, chosen arbitrarily.
  have hex : ∀ E, Nonempty (PartialRun P U V E) := fun E =>
    exists_partialRun hlc hd hruns V E (fun E' _ A => hlive E' A)
  set As : ∀ E, PartialRun P U V E := fun E => (hex E).some with hAs
  -- The diagonal: each slot's verdict read from the first height above it.
  set vd : ℕ → Option BlockId := fun k => (As (epochOf P.W k + 1)).vdct k with hvd
  -- Any stage's verdicts agree with the diagonal on the epochs it closed.
  have hdiag : ∀ E j, epochOf P.W j < E → (As E).vdct j = vd j := by
    intro E j hj
    exact partialRun_agree ha (As E) (As (epochOf P.W j + 1)) j (by omega)
  refine ⟨{ assign := fun m => P.pick U V vd m
            vdct := vd
            closed := ?_
            coherent := fun _ => rfl }⟩
  intro k
  have hclosed := (As (epochOf P.W k + 1)).closed k (by omega)
  refine hclosed.reschedule (S' := slotsOf P.inj (fun m => P.pick U V vd m)) rfl (fun m hm => ?_)
  have hmE : epochOf P.W m < epochOf P.W k + 2 := (epochOf_lt_iff P.W_pos).mpr hm
  change P.pick U V vd m = (As (epochOf P.W k + 1)).assign m
  rw [(As (epochOf P.W k + 1)).coherent m (by omega)]
  refine (P.adapted U V V (As (epochOf P.W k + 1)).vdct vd m (fun j hj => ?_)).symm
  exact hdiag _ j (by omega)

/-! ## What the run commits

Existence says every slot has a verdict. The two theorems below say
which verdicts are commits: at a reliable-led slot inside a live window
the run's verdict is `some L`, by `LeaderCommits` and `Agree` through
`Bounded`, and under `PlacesRuns` every epoch past the first holds `c`
consecutive commits. The precondition is asked for at the run's own
schedule; `Run.live_of_staged` obtains it from the staged form. -/

/-- The run's schedule is the policy's, as a function. -/
theorem Run.assign_eq {V : R.View U} (A : Run P U V) :
    (fun m => P.pick U V A.vdct m) = A.assign :=
  funext fun m => (A.coherent m).symm

/-- The staged precondition, read at a total run's own schedule. -/
theorem Run.live_of_staged {V : R.View U} (A : Run P U V)
    (hlive : ∀ (E : ℕ) (A' : PartialRun P U V E),
      Live (slotsOf P.inj (fun m => P.pick U V A'.vdct m)) V T P.W (P.W * (E + 2)))
    (e : ℕ) : Live (slotsOf P.inj A.assign) V T P.W (P.W * (e + 2)) := by
  have h := hlive e (A.toPartial e)
  change Live (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (e + 2)) at h
  rwa [A.assign_eq] at h

/-- **A reliable leader's slot commits in the run.** -/
theorem Run.commits (ha : Agree R) (hlc : LeaderCommits R Live)
    {V : R.View U} (A : Run P U V) {lo K : ℕ}
    (hlive : Live (slotsOf P.inj A.assign) V T lo K) {k : ℕ} (hlo : lo ≤ k) (hK : k < K)
    (hlead : A.assign k ∈ T) : ∃ L, A.vdct k = some L := by
  obtain ⟨L, hL⟩ := hlc (slotsOf P.inj A.assign) V T lo K hlive k hlo hK hlead
  exact ⟨L, DecidedBelow.agree ha (A.closed k) hL⟩

/-- **Every epoch past the first carries `c` consecutive commits.** -/
theorem Run.commits_in_epoch (ha : Agree R) (hlc : LeaderCommits R Live) (hruns : PlacesRuns P T c) {V : R.View U} (A : Run P U V)
    (e : ℕ) (hlive : Live (slotsOf P.inj A.assign) V T P.W (P.W * (e + 2))) :
    ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → ∃ L, A.vdct (b + i) = some L := by
  obtain ⟨b, hb1, hb2, hbT⟩ := hruns U V A.vdct e
  refine ⟨b, hb1, hb2, fun i hi => ?_⟩
  have hlead : A.assign (b + i) ∈ T := by rw [A.coherent (b + i)]; exact hbT i hi
  have hWle : P.W ≤ b + i := by
    have := Nat.mul_le_mul_left P.W (show 1 ≤ e + 1 by omega)
    omega
  exact A.commits ha hlc hlive hWle (by omega) hlead

end Existence

end Adaptive

end LeanDag
