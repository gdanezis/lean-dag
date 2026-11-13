import LeanDag.Barnacle.Model.Heads
/-!
# Barnacle: bounded anchor chains

The schedule property liveness needs at any number of leaders per round.
A slot is decided indirectly by scanning the slots from a wave above it, in
decision order, to the first committed one; a skipped slot is passed over
and an undecided one stops the scan. With `T` the validators whose slots
commit and `D ⊇ T` those whose slots are decided directly (a crashed
leader's slot is skipped), only a slot led outside `D` can stop a scan, and
it is decided once its own scan, a wave above it, ends.

* `Config.ChainEnds C T D g H p`: the scan from slot `p` reaches a `T`-led
  slot by round `H`, and every slot before it led outside `D` has its own
  scan, from `g` rounds above it, end by `H` too.
* `Config.BoundedChains C slack fb g c₀`: for every split into `T ⊆ D`
  missing at most `slack` and `fb` validators, the scan from every round's
  first slot ends within `c₀` rounds. We call such a schedule one with
  **bounded anchor chains**.

Definitions only.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]

/-- **The scan from slot `p` ends by round `H`**: some `T`-led slot `top ≥ p`
lies at a round up to `H`, and every slot from `p` before `top` led outside
`D` has its own scan, from `g` rounds above it, end by `H`. -/
inductive Config.ChainEnds (C : Config Validator) (T D : Finset Validator) (g H : ℕ) : ℕ → Prop
  | mk (p top : ℕ) : p ≤ top → C.sched.slotRound top ≤ H → C.sched.leader top ∈ T →
      (∀ j, p ≤ j → j < top → C.sched.leader j ∉ D →
        Config.ChainEnds C T D g H (C.cum (C.sched.slotRound j + g))) →
      Config.ChainEnds C T D g H p

/-- **Bounded anchor chains**: for every split into `T ⊆ D` missing at most
`slack` and `fb` validators, the scan from the first slot of every round `x`
ends by round `x + c₀`. -/
def Config.BoundedChains (C : Config Validator) (slack fb g c₀ : ℕ) : Prop :=
  ∀ T D : Finset Validator, T ⊆ D → Fintype.card Validator ≤ T.card + slack →
    Fintype.card Validator ≤ D.card + fb → ∀ x, C.ChainEnds T D g (x + c₀) (C.cum x)

end Barnacle

end LeanDag
