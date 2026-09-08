import LeanDag.Barnacle.Model.Rule
import LeanDag.Common.Schedule
/-!
# Barnacle: the schedule of a configuration

The paper's slot `(r, l)` is led by `GetLeader(r + l)` (`barnacle.md`
§3); the leader function is fixed across configurations, only which
slots exist changes. `Sched` is one configuration's `Slots` instance,
`m` leaders per pipelined round, built from `Slots.uniform`; `Keyed` is
the leader-distinctness obligation that construction needs, implied by
injectivity of `getLeader` on every window of `maxLeaders` consecutive
rounds (`Helpers/Schedule.lean`), which round-robin has whenever
`maxLeaders ≤ n`. `Sched` is a `def`, never an instance: several
schedules coexist on one validator type, and every use names its own.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type}

/-- **The leaders of a round are distinct**, at every count `m` up to
`w` — exactly `Slots.uniform`'s `hblock` obligation, and so
`Slots.keyed` for the schedule below. -/
def Keyed (getLeader : ℕ → Validator) (w : ℕ) : Prop :=
  ∀ m, 0 < m → m ≤ w → ∀ κ₁ κ₂, κ₁ / m = κ₂ / m →
    getLeader (κ₁ / m + κ₁ % m) = getLeader (κ₂ / m + κ₂ % m) → κ₁ = κ₂

/-- **The schedule of a configuration with `m` leaders**: slot `κ` is
proposed at round `κ / m`, led by `getLeader (κ / m + κ % m)` —
`Slots.uniform` at period one. Reducible, so `simp` reads `slotRound`
through `Slots.uniform_slotRound`. -/
@[reducible] def Sched (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) : Slots Validator :=
  Slots.uniform 1 m Nat.one_pos hm (fun κ => getLeader (κ / m + κ % m)) (hk m hm hmax)

/-- Round-robin over `n` validators: slot `(r, l)` led by `(r + l) % n`
— the paper's `GetLeader`, and the arc's witness schedule. -/
def roundRobin (n : ℕ) (hn : 0 < n) : ℕ → Fin n :=
  fun r => ⟨r % n, Nat.mod_lt r hn⟩

end Barnacle

end LeanDag
