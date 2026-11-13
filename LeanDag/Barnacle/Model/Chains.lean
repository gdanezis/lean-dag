import LeanDag.Barnacle.Model.Heads
import Mathlib.Probability.Distributions.Uniform
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
  **bounded anchor chains**; `Config.BoundedChainsUpto` the same for the
  rounds under a horizon `Nmax`;
* `LiveRule.upTo R Nmax`: `R` with its DAGs good only up to `Nmax`;
* `blockHead dflt g`: heads drawn in blocks of `L` rounds, block `k` being
  `g k`; `PrefixIn T w`: the blocks whose first `w` heads lie in `T`;
* `shuffle`: a uniformly random ordering of the validators.

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

/-- **Bounded anchor chains up to a horizon**: the same, for the rounds `x`
whose scan and a wave above it fit under `Nmax`. -/
def Config.BoundedChainsUpto (C : Config Validator) (slack fb g c₀ Nmax : ℕ) : Prop :=
  ∀ T D : Finset Validator, T ⊆ D → Fintype.card Validator ≤ T.card + slack →
    Fintype.card Validator ≤ D.card + fb → ∀ x, x + c₀ + g ≤ Nmax →
      C.ChainEnds T D g (x + c₀) (C.cum x)

/-- **Heads drawn in blocks**: `J · M` blocks of `L` rounds; the head of round
`ρ` is entry `ρ mod L` of block `ρ / L`, and `dflt` past the blocks. -/
def blockHead {J M L : ℕ} (dflt : Validator) (g : Fin (J * M) → Fin L → Validator) (ρ : ℕ) :
    Validator :=
  if h : ρ / L < J * M ∧ 0 < L then g ⟨ρ / L, h.1⟩ ⟨ρ % L, Nat.mod_lt _ h.2⟩ else dflt

/-- **A block opens with `w` heads from `T`.** -/
def PrefixIn {L : ℕ} (T : Finset Validator) (w : ℕ) : Set (Fin L → Validator) :=
  {b | ∀ i : Fin L, (i : ℕ) < w → b i ∈ T}

/-- **A random ordering of the validators**: a uniformly random bijection
from the `n` positions to the validators, read as the heads of a block of
`n` rounds. -/
noncomputable def shuffle (Validator : Type) [Fintype Validator] [DecidableEq Validator] :
    PMF (Fin (Fintype.card Validator) → Validator) :=
  haveI : Nonempty (Fin (Fintype.card Validator) ≃ Validator) :=
    ⟨(Fintype.equivFin Validator).symm⟩
  PMF.map (fun e : Fin (Fintype.card Validator) ≃ Validator => ⇑e) (PMF.uniformOfFintype _)

variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A live rule read up to a horizon**: its DAGs good only up to `Nmax`.
Its base rule, and so its runs, are the rule's own. -/
def LiveRule.upTo (R : LiveRule Validator BlockId Payload) (Nmax : ℕ) :
    LiveRule Validator BlockId Payload :=
  { R with Good := fun S U Rnd N => R.Good S U Rnd N ∧ N ≤ Nmax }

end Barnacle

end LeanDag
