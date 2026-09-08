import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic

/-!
# The slot schedule

Which validator proposes at which round, as a class so that a schedule
is fixed once per development and every rule reads the same one. Stated
here, below every protocol, because every protocol runs on it: the
core, Odontoceti, Mahi-Mahi, Nemo, Orcaella, FinWhale, Hydrozoan and
Optimal-Hydrozoan all take `[S : Slots Validator]`.
-/

namespace LeanDag

/-- The leader schedule: which validator proposes at which round, as a
sequence of slots. Slots need not be three rounds apart — under
pipelining they are one round apart, and under multiple leaders per
round they share one — so `slotRound` need only be monotone, and the
separation M4's commit half needs is required instead at `Eligible`
below. `unbounded` is assumed, not derivable from `mono` alone. `keyed`
is a real condition once several leaders share a round: without it one
block would be the candidate for two slots, and the ledger would
deliver it twice. -/
class Slots (Validator : Type*) where
  /-- The round at which slot `k` is proposed. -/
  slotRound : ℕ → ℕ
  /-- The validator whose block is the slot-`k` candidate. -/
  leader : ℕ → Validator
  /-- Slots are enumerated in round order. -/
  mono : Monotone slotRound
  /-- Slot rounds are unbounded. -/
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  /-- Distinct slots differ in round or in leader. -/
  keyed : Function.Injective (fun k => (slotRound k, leader k))


/-! ## Schedule constructors

Stated here, below every protocol, so that a rule's grounding witness can
take a concrete schedule without importing the core. -/

/-- **A fair schedule offers runs**: past any slot, `c` consecutive `T`-led
slots. An assumption about the schedule, not a theorem: `leader` may
name faulty validators for ever. -/
def FairRunOn {Validator : Type*} [S : Slots Validator] (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T

namespace Slots

variable {Validator : Type*}

/-- **The uniform schedule**: `m` leaders in every `p`-th round, slot `k`
proposed by `elect k`. `hblock` is the one real condition — the `m`
proposers of a round are distinct validators — which round-robin
satisfies whenever `m ≤ n`. -/
@[reducible]
def uniform (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (elect : ℕ → Validator)
    (hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂) :
    Slots Validator where
  slotRound k := p * (k / m)
  leader k := elect k
  mono := fun _ _ hab => Nat.mul_le_mul_left p (Nat.div_le_div_right hab)
  unbounded := fun n => ⟨m * n, by
    rw [Nat.mul_div_cancel_left n hm]
    exact Nat.le_mul_of_pos_left n hp⟩
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    exact hblock k₁ k₂ (Nat.eq_of_mul_eq_mul_left hp h.1) h.2

section

variable {p m : ℕ} {hp : 0 < p} {hm : 0 < m} {elect : ℕ → Validator}
  {hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂}

@[simp]
theorem uniform_slotRound (k : ℕ) :
    (uniform p m hp hm elect hblock).slotRound k = p * (k / m) := rfl

@[simp]
theorem uniform_leader (k : ℕ) :
    (uniform p m hp hm elect hblock).leader k = elect k := rfl

end

/-- With one leader per round the distinctness condition is vacuous: slots in
a round are the round, so no two of them share it. -/
theorem one_hblock (elect : ℕ → Validator) :
    ∀ k₁ k₂ : ℕ, k₁ / 1 = k₂ / 1 → elect k₁ = elect k₂ → k₁ = k₂ :=
  fun _ _ h _ => by simpa using h

/-- **One leader every `p` rounds.** `p = 3` is the schedule the development
had before pipelining; `p = 1` is pipelined single-leader. -/
@[reducible]
def uniformSingle (p : ℕ) (hp : 0 < p) (elect : ℕ → Validator) : Slots Validator :=
  uniform p 1 hp Nat.one_pos elect (one_hblock elect)

@[simp]
theorem uniformSingle_slotRound {p : ℕ} {hp : 0 < p} {elect : ℕ → Validator} (k : ℕ) :
    (uniformSingle p hp elect).slotRound k = p * k := by
  simp

/-- **Fairness places a run past any slot and any round.** -/
theorem exists_run_past [S : Slots Validator] {T : Finset Validator} {c : ℕ}
    (fair : FairRunOn T c) (k R : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧ ∀ i, i < c → S.leader (b + i) ∈ T := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨b, hb, hlead⟩ := fair (max k k₀)
  exact ⟨b, le_trans (le_max_left _ _) hb,
    le_trans hk₀ (S.mono (le_trans (le_max_right _ _) hb)), hlead⟩

end Slots

/-- **The identity schedule** with a given leader map: one slot per round.
The three laws are immediate. -/
@[reducible]
def Slots.identity {Validator : Type*} (leader : ℕ → Validator) : Slots Validator :=
  ⟨id, leader, fun _ _ h => h, fun n => ⟨n, le_rfl⟩, fun _ _ h => congrArg Prod.fst h⟩

/-- **The wave-aligned round-robin schedule** on `n` validators:
pipelined, with the leader holding for a whole wave of three slots
before the rotation advances. A `def`, not an `instance` — a second
`Slots` instance would make synthesis ambiguous — so every use passes
`(S := waveRobin n hn)` explicitly. -/
@[reducible]
def waveRobin (n : ℕ) (hn : 0 < n) : Slots (Fin n) where
  slotRound k := k
  leader k := ⟨k / 3 % n, Nat.mod_lt _ hn⟩
  mono := fun _ _ h => h
  unbounded := fun m => ⟨m, le_refl m⟩
  keyed := fun _ _ h => congrArg Prod.fst h

/-- The schedule is pipelined: slot `k` is proposed at round `k`. -/
@[simp]
theorem waveRobin_slotRound {n : ℕ} {hn : 0 < n} (k : ℕ) :
    (waveRobin n hn).slotRound k = k := rfl

/-- The leader holds for a wave: slots `3v, 3v+1, 3v+2` of each rotation
cycle are led by validator `v`. -/
theorem waveRobin_leader_val {n : ℕ} {hn : 0 < n} (k : ℕ) :
    ((waveRobin n hn).leader k).val = k / 3 % n := rfl

end LeanDag
