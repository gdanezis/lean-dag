import LeanDag.Steelhead.Model.Chain
/-!
# Steelhead — the period sequence

The adaptive protocol (`steelhead.md` §5) groups rounds into intervals
of `I` rounds and decides each interval under one period. The period of
interval `j + 1` is fixed by the scan of interval `j`: the interval's
**anchor** is its earliest asynchronous round whose chain verdict is a
commit, every asynchronous round of the interval below it chain-skipped;
the next period is a deterministic function of the anchor block and the
current period, and an interval without an anchor keeps the period. A
validator whose scan meets a chain-undecided round waits there, which the
relational form records as the absence of a derivation.

**Definitions only.** The update rule is any function of the interval
index, the anchor block and the current period: the paper's replay is
one, and every result here holds for all of them. Interval boundaries
are fixed by `I` alone, so the round at which a period takes effect is
common to every validator by construction; what the theorems in
`Period/Statement.lean` add is that the periods are too.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The interval of a round**: rounds `j·I + 1` to `(j + 1)·I` form interval `j`, as the
paper numbers them; round `0` falls in interval `0`. -/
def intervalOf (I r : ℕ) : ℕ := (r - 1) / I

/-- **The update rule**: the next period from the interval index, the anchor block and the
period in force. Any deterministic function; the paper's counterfactual replay reads the
anchor's causal history, which the block id determines within one universe. -/
abbrev UpdateRule (BlockId : Type) := ℕ → BlockId → ℕ → ℕ

/-- **The chain anchor of interval `j` under period `k`**, read from the view `V`: round `r` of
the interval is asynchronous under `k` and chain-committed on `A`, and every asynchronous round of
the interval below it is chain-skipped. -/
structure IntervalAnchor (I wa : ℕ) (coin : ℕ → Validator)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (j k r : ℕ) (A : BlockId) : Prop where
  /-- The anchor lies in the interval. -/
  mem : intervalOf I r = j
  /-- It is an asynchronous round under the interval's period. -/
  async : IsAsync k r
  /-- Its chain verdict is a commit. -/
  commit : ChainDecided wa coin U V r (some A)
  /-- Every asynchronous round of the interval below it is chain-skipped. -/
  below : ∀ r', intervalOf I r' = j → IsAsync k r' → r' < r → ChainDecided wa coin U V r' none

/-- **No anchor**: every asynchronous round of the interval is chain-skipped. -/
def NoAnchor (I wa : ℕ) (coin : ℕ → Validator) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (j k : ℕ) : Prop :=
  ∀ r, intervalOf I r = j → IsAsync k r → ChainDecided wa coin U V r none

/-- **The period sequence**, as a validator holding `V` derives it: `PeriodAt … j k` says
interval `j` is decided under period `k`. Interval `0` runs at `k₀`; interval `j + 1` runs at the
update of interval `j`'s anchor, or at `j`'s period when `j` has none. *Waiting* is the absence of
a derivation. -/
inductive PeriodAt (I wa : ℕ) (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → ℕ → Prop
  /-- The first interval runs at the initial period. -/
  | zero : PeriodAt I wa coin upd k₀ U V 0 k₀
  /-- An interval with an anchor hands the next interval the updated period. -/
  | anchor {j k r : ℕ} {A : BlockId} :
      PeriodAt I wa coin upd k₀ U V j k → IntervalAnchor I wa coin U V j k r A →
      PeriodAt I wa coin upd k₀ U V (j + 1) (upd j A k)
  /-- An interval without an anchor keeps the period. -/
  | keep {j k : ℕ} :
      PeriodAt I wa coin upd k₀ U V j k → NoAnchor I wa coin U V j k →
      PeriodAt I wa coin upd k₀ U V (j + 1) k

/-- **The adaptive wavelength**: the periodic wavelength of each round's interval, for a period
sequence `per`. What a validator that derived `per` runs the output relation at. -/
def adaptiveWave (ws wa I : ℕ) (per : ℕ → ℕ) : ℕ → ℕ :=
  fun r => periodic ws wa (per (intervalOf I r)) r

end Steelhead

end LeanDag
