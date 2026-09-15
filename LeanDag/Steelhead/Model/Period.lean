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
index, the anchor block, what the anchor's window output, and the
current period: the paper's replay is one, and every result here holds
for all of them. The output is handed to the rule, not read by it: the
model computes it from the anchor's causal history (`windowOutput`), so
the failover the liveness argument needs is a clause on the rule's
answer to an empty output alone. Interval boundaries are fixed by `I`
alone, so the round at which a period takes effect is common to every
validator by construction; what the theorems in `Period/Statement.lean`
add is that the periods are too.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The interval of a round**: rounds `j·I + 1` to `(j + 1)·I` form interval `j`, as the
paper numbers them; round `0` falls in interval `0`. -/
def intervalOf (I r : ℕ) : ℕ := (r - 1) / I

/-- **The update rule**: the next period from the interval index, the anchor block, the leaders
the anchor's window output, and the period in force. Any deterministic function; the paper's
counterfactual replay reads the anchor's causal history, which the block id determines within one
universe, and its failover reads the output. -/
abbrev UpdateRule (BlockId : Type) := ℕ → BlockId → Finset BlockId → ℕ → ℕ

/-- **The first round of an anchor's window**: the window is the anchor's causal history over the
last `I` rounds, round `0` excluded, so it starts at `round A + 1 − I` and no lower than `1`. -/
def windowBottom (U : BlockUniverse Validator BlockId Payload) (A : BlockId) (I : ℕ) : ℕ :=
  max 1 ((U.block A).round + 1 - I)

open scoped Classical in
/-- **What the anchor's window output**, read in the anchor's causal history at the wavelength
`w`: the leaders that history commits at slots of the window with every slot below them decided,
which is what the sequenced output releases. What the validator that scanned the anchor hands the
update rule beside the anchor, as the paper's Algorithm 2 hands its replay the window's verdicts.
The test reads the window, not the anchor's own interval: a history holds no decision round of the
slots within a wave below its block, so an anchor at the start of its interval shows nothing of
that interval whatever was output, and a test on the interval would find every anchored interval
of a healthy network empty at period `1`. The test is a proposition on verdicts, so the filter is
classical. -/
noncomputable def windowOutput [S : Slots Validator] (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ → ℕ) (I : ℕ) (A : BlockId) (hA : A ∈ U.ids) : Finset BlockId :=
  (history U A).filter fun L => ∃ s, windowBottom U A I ≤ S.slotRound s ∧
    Decided w U (U.historyView A hA) s (some L) ∧
    ∀ s' < s, ∃ v, Decided w U (U.historyView A hA) s' v

/-- **The update rule fails over to period `1` when handed an empty output.** The clause the
liveness argument reads off the update rule, in place of Theorem 3's premise that a window without
a synchronous commit maps to `k = 1` (`steelhead.md` §7). A clause on `upd` alone: the output it
is handed is the model's (`windowOutput`), not the rule's own reading of the history, so the rule
has no verdict of its own to disagree with. On the window a healthy network commits the lowest
slots with everything below them decided, the output is nonempty, and the rule's own answer
stands: period `1` is not absorbing. -/
def ResetsOnNoOutput (upd : UpdateRule BlockId) : Prop :=
  ∀ (j : ℕ) (A : BlockId) (k : ℕ), upd j A ∅ k = 1

/-- **The failover wrapped around an update rule**: `1` when handed an empty output, the rule's
own answer elsewhere. The rule it wraps is any function, the paper's replay among them. It
satisfies `ResetsOnNoOutput` outright (SH10h). -/
def failover (upd : UpdateRule BlockId) : UpdateRule BlockId :=
  fun j A out k => if out = ∅ then 1 else upd j A out k

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

/-- **The period sequence**, as a validator holding `V` derives it, handing the update rule the
output `out A` of each anchor `A`: `PeriodAt … j k` says interval `j` is decided under period `k`.
Interval `0` runs at `k₀`; interval `j + 1` runs at the update of interval `j`'s anchor, or at
`j`'s period when `j` has none. *Waiting* is the absence of a derivation. The output is a
parameter, so that the agreement claims hold for any handover; the liveness claims instantiate it
with what the anchor's window output at the validator's own wavelength (`adaptiveOutput`). -/
inductive PeriodAt (I wa : ℕ) (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (out : BlockId → Finset BlockId) : ℕ → ℕ → Prop
  /-- The first interval runs at the initial period. -/
  | zero : PeriodAt I wa coin upd k₀ U V out 0 k₀
  /-- An interval with an anchor hands the next interval the updated period. -/
  | anchor {j k r : ℕ} {A : BlockId} :
      PeriodAt I wa coin upd k₀ U V out j k → IntervalAnchor I wa coin U V j k r A →
      PeriodAt I wa coin upd k₀ U V out (j + 1) (upd j A (out A) k)
  /-- An interval without an anchor keeps the period. -/
  | keep {j k : ℕ} :
      PeriodAt I wa coin upd k₀ U V out j k → NoAnchor I wa coin U V j k →
      PeriodAt I wa coin upd k₀ U V out (j + 1) k

/-- **The adaptive wavelength**: the periodic wavelength of each round's interval, for a period
sequence `per`. What a validator that derived `per` runs the output relation at. -/
def adaptiveWave (ws wa I : ℕ) (per : ℕ → ℕ) : ℕ → ℕ :=
  fun r => periodic ws wa (per (intervalOf I r)) r

/-- **The output a validator hands the update rule**: what each anchor's window output in the
anchor's causal history, read at the adaptive wavelength of the period sequence `per` the
validator derived and on the schedule it runs; empty for a block outside the record. What the
liveness claims instantiate `PeriodAt`'s `out` with. -/
noncomputable def adaptiveOutput [S : Slots Validator] (ws wa I : ℕ) (per : ℕ → ℕ)
    (U : BlockUniverse Validator BlockId Payload) : BlockId → Finset BlockId :=
  fun A => if hA : A ∈ U.ids then windowOutput U (adaptiveWave ws wa I per) I A hA else ∅

/-- **The adaptive schedule**: one slot per round, led by the coin at the rounds the period
sequence `per` makes asynchronous and by the known schedule `known` elsewhere. What a validator
that derived `per` runs the output relation on; the liveness claims that relate a schedule to the
coin one clause at a time (SH14) take this one as their instance. -/
abbrev adaptiveSlots (coin known : ℕ → Validator) (I : ℕ) (per : ℕ → ℕ) : Slots Validator :=
  Slots.identity fun r => if IsAsync (per (intervalOf I r)) r then coin r else known r

end Steelhead

end LeanDag
