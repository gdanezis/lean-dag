import LeanDag.Steelhead.Model.Decision
/-!
# Steelhead — the control verdict

A committed asynchronous slot does not decide the synchronous slots
below it: the anchor search of Algorithm 1 stops at an undecided slot,
and under asynchrony an adversary who knows the leader keeps every
synchronous slot undecided at no cost (`steelhead.md` §4, whose witness
arrives with the period). So the interval's anchor, the agreed event the
period update reads, cannot come from the output. It comes from the
**control verdict**: the asynchronous rule read with the coin leader on
the **control slots**, the rounds that carry a coin, anchored on control
commits only, so that no known-leader slot lies on the chain and nothing
the adversary can hold undecided blocks it. Control verdicts are never
sequenced or output; they drive the period update, which the next
development of the arc states.

**Which rounds carry a coin is fixed by rule, per scan.** A coin exists
on the asynchronous rounds alone, and above the interval under scan the
period is not yet known. The control rounds of the scan of interval `j`
are therefore the asynchronous rounds of its own period `k` up to its
boundary `(j + 1) · I`, and above it the multiples of the period bound
`K`: the implementation's candidate periods all divide `K`, so those
rounds are asynchronous whatever the scan fixes. The arc's update rule
is any function and the coin is a map on every round, so no claim here
needs that divisibility. Each scan has its own control set, so the
verdicts are stated per scan and never compared across scans. This is
the reference implementation's reading (`committer.rs`,
`is_control_round`, `compute_chain`); a round without a coin reads there
as a skip, which the anchor search and the scan pass over exactly as
they pass over a round that is no slot.

**The control reading is the Mahi-Mahi arc at a sub-schedule.** The
control rounds of a scan in order, each led by its coin, wave `wa`: the
relation is Mahi-Mahi's `Decided wa` at `controlSlots coin I K j k`,
nothing new. Its agreement is MM1c; its liveness is MM3 with the
unpredictable-leader clause at that schedule, a run of `wa` consecutive
control slots settling everything below it, since consecutive slots of
any schedule lie at least one round apart. The **coin schedule**
`chainSlots coin`, one slot per round led by the coin, every slot
asynchronous, is the output schedule at period `1` (SH9b, SH11h) and the
schedule a run of good rounds is read at (SH7c).

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The coin schedule**: one slot per round, led by `coin r`, the
coin-elected leader of round `r`, every slot of the asynchronous kind.
The output schedule at period `1`, and the schedule a run of good rounds
is read at. The coin is modelled by its effect, as in the Mahi-Mahi arc:
`coin` is any map, and the unpredictability clause of the liveness
statements is what a coin revealed after the votes makes true. -/
abbrev chainSlots (coin : ℕ → Validator) : Slots Validator :=
  { Slots.identity coin with kind := fun _ => 1 }

/-- **The coin verdict** at wave `wa` under the coin `coin`: Mahi-Mahi's
relation at the coin schedule. `ChainDecided wa coin U V r v` is the
verdict `v` of round `r`, read from the view `V`. -/
abbrev ChainDecided (wa : ℕ) (coin : ℕ → Validator)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  MahiMahi.Decided (S := chainSlots coin) wa U V

/-- **The round of control slot `i`** in the scan of interval `j` at period `k` and period bound
`K`: the multiples of `k` up to the interval's boundary `(j + 1) · I`, then the multiples of `K`
above it. Round `0` and the multiples of `k` below the interval are slots too; the implementation
never evaluates them, and no verdict at or above the interval reads them, since the indirect rule
looks upward only. At `k = 0` Lean's `n / 0 = 0` leaves round `0` the only slot up to the
boundary, as `r % 0 = 0` makes it the only asynchronous round (`periodicKind`). -/
def controlRound (I K j k i : ℕ) : ℕ :=
  if i ≤ (j + 1) * I / k then i * k else ((j + 1) * I / K + (i - (j + 1) * I / k)) * K

/-- **The first control round of interval `j` at period `k`**: the least multiple of `k` above
`j · I`, which lies in the interval once `k ≤ I`. The place the coin's liveness claims name
(SH14c). -/
def firstControlRound (I j k : ℕ) : ℕ := (j * I / k + 1) * k

/-- **The control schedule** of the scan of interval `j` at period `k`: the control rounds in
order, each led by its coin, every slot of the asynchronous kind. `K` is positive, as the
implementation's `max_period` is; the rounds are then strictly increasing, which is the
schedule's three laws. -/
@[reducible]
def controlSlots (coin : ℕ → Validator) (I K j k : ℕ) [NeZero K] : Slots Validator := by
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hmono : StrictMono (controlRound I K j k) := by
    intro i i' h
    unfold controlRound
    split_ifs with hi hi'
    · -- both up to the boundary: k is positive, since i < i' ≤ b / k
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at hi'; omega
        · exact hk
      exact Nat.mul_lt_mul_of_pos_right h hk
    · -- i up to the boundary, i' above it: i · k ≤ b < (b / K + 1) · K
      calc i * k ≤ (j + 1) * I / k * k := Nat.mul_le_mul_right k hi
        _ ≤ (j + 1) * I := Nat.div_mul_le_self _ _
        _ < (j + 1) * I / K * K + K := Nat.lt_div_mul_add hK
        _ = ((j + 1) * I / K + 1) * K := (Nat.succ_mul _ _).symm
        _ ≤ ((j + 1) * I / K + (i' - (j + 1) * I / k)) * K :=
            Nat.mul_le_mul_right K (by omega)
    · omega
    · exact Nat.mul_lt_mul_of_pos_right (by omega) hK
  exact
    { slotRound := controlRound I K j k
      leader := fun i => coin (controlRound I K j k i)
      kind := fun _ => 1
      mono := hmono.monotone
      unbounded := fun n => ⟨(j + 1) * I / k + n + 1, by
        unfold controlRound
        rw [if_neg (by omega), Nat.add_assoc, Nat.add_sub_cancel_left]
        calc n ≤ (j + 1) * I / K + (n + 1) := le_trans (Nat.le_succ n) (Nat.le_add_left _ _)
          _ ≤ ((j + 1) * I / K + (n + 1)) * K := Nat.le_mul_of_pos_right _ hK⟩
      keyed := fun _ _ h => hmono.injective (congrArg Prod.fst h) }

/-- **The control verdict** of slot `i` of the scan of interval `j` at period `k`, at wave `wa`
under the coin `coin`: Mahi-Mahi's relation at the control schedule. `ControlDecided I K wa coin
j k U V i v` is the verdict `v` of the slot, read from the view `V`. -/
abbrev ControlDecided (I K wa : ℕ) [NeZero K] (coin : ℕ → Validator) (j k : ℕ)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  MahiMahi.Decided (S := controlSlots coin I K j k) wa U V

end Steelhead

end LeanDag
