import LeanDag.Common.Schedule
import LeanDag.Common.Anchored.Bounded
/-!
# Adaptive leaders: epochs and induced schedules

The groundwork for the adaptive-leaders arc (`adaptive-leaders.md`): a
Hammerhead-style schedule recomputes the leaders ahead from the agreed
prefix, and the question is whether safety and liveness survive.

This file holds the two notions that belong to no protocol: the epoch
structure, and `slotsOf`, the `Slots` instance a leader assignment
induces over a fixed round structure. One leader per round —
`slotRound` injective — is assumed for the whole arc: it makes the
`keyed` clause a lemma, where under multi-leader rounds a reassignment
could collide two slots of one round onto one validator and the policy
would owe the distinctness clause itself.

The bounded decision relation the fixpoint needs is a *property of the
protocol* — `Properties/Bounded.lean` states it, `MysticetiProperties`
proves it for the core — and the mechanism reads only the property.
-/

namespace LeanDag

variable {Validator : Type*}

/-- The epoch of slot `k` at width `W`: epoch `e` is slots
`[W·e, W·(e+1))`. -/
def epochOf (W k : ℕ) : ℕ := k / W

theorem epochOf_lt_iff {W k e : ℕ} (hW : 0 < W) :
    epochOf W k < e ↔ k < W * e := by
  unfold epochOf
  rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]

theorem epochOf_mono (W : ℕ) {j k : ℕ} (h : j ≤ k) :
    epochOf W j ≤ epochOf W k :=
  Nat.div_le_div_right h

/-- **Epoch alignment.** When a base slot is a whole number of epochs,
a numbering that starts there is the original shifted by a constant,
and every epoch window corresponds. This is what a cut must respect
under an adaptive schedule: a joiner's slot `k` is the network's
`d + k`, so the two agree about which epoch a slot belongs to only when
`d` falls on an epoch boundary. -/
theorem epochOf_add_of_dvd {W d : ℕ} (hW : 0 < W) (hdvd : W ∣ d) (k : ℕ) :
    epochOf W (d + k) = d / W + epochOf W k := by
  obtain ⟨c, rfl⟩ := hdvd
  unfold epochOf
  rw [Nat.mul_div_cancel_left c hW, Nat.mul_add_div hW]

/-- Without alignment the correspondence fails: at `W = 2, d = 1` the
first two slots of the new numbering straddle an epoch boundary of the
old. -/
example : epochOf 2 (1 + 1) ≠ 1 / 2 + epochOf 2 1 := by decide

section Slots

variable [S : Slots Validator]

/-- The `Slots` instance a leader assignment induces: the base round
structure, the given leaders. `keyed` is where one-leader-per-round
enters: with `slotRound` injective, distinct slots differ in round
whatever the assignment names. -/
@[reducible] def slotsOf (hinj : Function.Injective S.slotRound) (a : ℕ → Validator) :
    Slots Validator where
  slotRound := S.slotRound
  leader := a
  mono := S.mono
  unbounded := S.unbounded
  keyed := fun _ _ h => hinj (congrArg Prod.fst h)

@[simp] theorem slotsOf_slotRound (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).slotRound k = S.slotRound k := rfl

@[simp] theorem slotsOf_leader (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).leader k = a k := rfl

/-- The base schedule is its own induced instance — the anchor for
conservativity: a constant policy reassigns nothing. -/
theorem slotsOf_base (hinj : Function.Injective S.slotRound) :
    slotsOf hinj S.leader = S := by
  cases S; rfl

/-! ## What an induced schedule keeps

Reassignment fixes the round structure, so eligibility and the spanning
clause transfer to every induced schedule, and a bounded verdict
transfers between assignments agreeing below its bound. -/

/-- The spanning clause transfers to every induced schedule, at any wave. -/
theorem spansEligible_slotsOf (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    {wave c : ℕ} (h : SpansEligibleAt (S := S) wave c) :
    SpansEligibleAt (S := slotsOf hinj a) wave c := h

/-- **Congruence below the bound**, at two induced schedules: two
assignments agreeing below `B` derive the same bounded verdicts. -/
theorem AnchoredRule.decidedWithin_slotsOf_congr [Fintype Validator] [DecidableEq Validator]
    {BlockId Payload : Type*} [DecidableEq BlockId]
    {P : Validity Validator BlockId Payload} {honest : Finset Validator}
    {R : AnchoredRule Validator BlockId Payload P honest}
    {I : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hl : R.Laws I) {hinj : Function.Injective S.slotRound} {a₁ a₂ : ℕ → Validator}
    {U : BlockRecord Validator BlockId Payload P honest} (hI : I (slotsOf hinj a₁) U)
    {V : U.View} {B k : ℕ} {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : R.DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    R.DecidedWithin (S := slotsOf hinj a₂) U V B k v :=
  AnchoredRule.decidedWithin_congr_of_slotRound hl hI (S₁ := slotsOf hinj a₁)
    (S₂ := slotsOf hinj a₂) rfl ha h

end Slots

end LeanDag
