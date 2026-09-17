import LeanDag.Steelhead.Model.Chain
/-!
# Steelhead — the period sequence

The adaptive protocol (`steelhead.md` §5) groups rounds into intervals
of `I` rounds and decides each interval under one period. The period of
interval `j + 1` is fixed by the scan of interval `j`, as the reference
implementation's `complete_scans` runs it: the interval's **anchor** is
its earliest round whose chain verdict is a commit, every round of the
interval below it chain-skipped; a validator whose scan meets a
chain-undecided round waits there, which the relational form records as
the absence of a derivation; an interval without an anchor keeps the
period. At an anchored interval the validator first extends the
**agreed output**, the output rule read on the anchor's causal history
and continued from where the previous anchor's left it
(`advance_agreed_output`), and falls over to period `1` when that output
committed no slot within the last `I` rounds below the anchor
(`apply_period_update`); otherwise the next period is the update rule's
answer, the replay of the anchor's window.

**Definitions only.** The update rule is any function of the anchor
block and the current period: the paper's replay is one, and every
result here holds for all of them. Interval boundaries are fixed by `I`
alone, so the round at which a period takes effect is common to every
validator by construction; what the theorems in `Period/Statement.lean`
add is that the periods, and the agreed output, are too.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The interval of a round**: rounds `j·I + 1` to `(j + 1)·I` form interval `j`, as the
paper numbers them. The arithmetic leaves round `0` in interval `0`; the scan never reads it,
which the anchor predicates below state, as `complete_scans` starts at the interval's first
round. -/
def intervalOf (I r : ℕ) : ℕ := (r - 1) / I

/-- **The update rule**: the next period from the anchor block and the period in force. Any
deterministic function; the paper's counterfactual replay reads the anchor's causal history,
which the block id determines within one universe. -/
abbrev UpdateRule (BlockId : Type) := BlockId → ℕ → ℕ

/-- **The first round of an anchor's window**: the window is the anchor's causal history at the
rounds `round A − I` and above, round `0` excluded, as `collect_window` takes it; so it starts at
`round A − I` and no lower than `1`, and holds `I + 1` rounds once the anchor is high enough. -/
def windowBottom (U : BlockUniverse Validator BlockId Payload) (A : BlockId) (I : ℕ) : ℕ :=
  max 1 ((U.block A).round - I)

/-- **The chain anchor of interval `j`**, read from the view `V`: round `r` of the interval, at
round `1` or above, is chain-committed on `A`, and every round of the interval below it, round
`0` excluded, is chain-skipped. Every round carries a chain verdict, so the anchor does not depend
on the period in force. -/
structure IntervalAnchor (I wa : ℕ) (coin : ℕ → Validator)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (j r : ℕ) (A : BlockId) : Prop where
  /-- The anchor is a scanned round, round `0` never being one. -/
  pos : 1 ≤ r
  /-- It lies in the interval. -/
  mem : intervalOf I r = j
  /-- Its chain verdict is a commit. -/
  commit : ChainDecided wa coin U V r (some A)
  /-- Every scanned round of the interval below it is chain-skipped. -/
  below : ∀ r', 1 ≤ r' → intervalOf I r' = j → r' < r → ChainDecided wa coin U V r' none

/-- **No anchor**: every scanned round of the interval, round `0` excluded, is chain-skipped. -/
def NoAnchor (I wa : ℕ) (coin : ℕ → Validator) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (j : ℕ) : Prop :=
  ∀ r, 1 ≤ r → intervalOf I r = j → ChainDecided wa coin U V r none

/-- **The state a scan carries**: the period in force at the interval, the agreed output's next
slot, and the round of its last committed leader, `0` before any. The implementation's
`period_schedule`, `agreed_next` and `agreed_last_commit_round`. -/
structure ScanState where
  /-- The period in force. -/
  period : ℕ
  /-- The next slot of the agreed output. -/
  next : ℕ
  /-- The round of the agreed output's last committed leader. -/
  lastCommit : ℕ
  deriving DecidableEq, Repr

section Slots

variable [S : Slots Validator]

/-- **The agreed output advances over an anchor's history**, read at the wavelength `w`: the slots
from `next` up to `next'` are decided in the anchor's causal history, `next'` is not, and `last'`
is the round of the last leader committed among them, or `last` when none is. The prefix is what
the sequenced output releases, so a slot the history leaves undecided stops it. -/
structure AgreedAdvance (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (A : BlockId)
    (hA : A ∈ U.ids) (next next' last last' : ℕ) : Prop where
  /-- The cursor does not move back. -/
  le : next ≤ next'
  /-- Every slot from the cursor up to the new one is decided in the history. -/
  decided : ∀ s, next ≤ s → s < next' → ∃ v, Decided w U (U.historyView A hA) s v
  /-- The new cursor is not. -/
  stuck : ∀ v, ¬ Decided w U (U.historyView A hA) next' v
  /-- The last commit does not move back. -/
  last_ge : last ≤ last'
  /-- It lies at or above every commit of the consumed prefix. -/
  last_le : ∀ (s : ℕ) (L : BlockId), next ≤ s → s < next' →
    Decided w U (U.historyView A hA) s (some L) → S.slotRound s ≤ last'
  /-- And it is the old one or the round of a commit of the consumed prefix. -/
  last_mem : last' = last ∨ ∃ (s : ℕ) (L : BlockId), next ≤ s ∧ s < next' ∧
    Decided w U (U.historyView A hA) s (some L) ∧ S.slotRound s = last'

/-- **The period sequence**, as a validator holding `V` derives it, its agreed output read at the
wavelength `w`: `PeriodAt … j st` says interval `j` is decided under the state `st`. Interval `0`
runs at `k₀` with the agreed output at slot `1` and no commit; interval `j + 1` runs at the
failover's or the update rule's answer when `j` has an anchor, the agreed output advanced over the
anchor's history, and at `j`'s state when `j` has none. *Waiting* is the absence of a derivation.
The wavelength is a parameter, so that the agreement claims hold for any reading; the liveness
claims instantiate it with the adaptive wavelength of the sequence the validator derives. -/
inductive PeriodAt (I wa : ℕ) (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (w : ℕ → ℕ) : ℕ → ScanState → Prop
  /-- The first interval runs at the initial period, the agreed output at slot `1`. -/
  | zero : PeriodAt I wa coin upd k₀ U V w 0 ⟨k₀, 1, 0⟩
  /-- An interval with an anchor advances the agreed output over the anchor's history and hands
  the next interval period `1` when that output committed nothing within `I` rounds below the
  anchor, and the update rule's answer otherwise. -/
  | anchor {j r next' last' : ℕ} {st : ScanState} {A : BlockId} {hA : A ∈ U.ids} :
      PeriodAt I wa coin upd k₀ U V w j st → IntervalAnchor I wa coin U V j r A →
      AgreedAdvance U w A hA st.next next' st.lastCommit last' →
      PeriodAt I wa coin upd k₀ U V w (j + 1)
        ⟨if last' + I < r then 1 else upd A st.period, next', last'⟩
  /-- An interval without an anchor keeps the state. -/
  | keep {j : ℕ} {st : ScanState} :
      PeriodAt I wa coin upd k₀ U V w j st → NoAnchor I wa coin U V j →
      PeriodAt I wa coin upd k₀ U V w (j + 1) st

end Slots

/-- **The adaptive wavelength**: the periodic wavelength of each round's interval, for a period
sequence `per`. What a validator that derived `per` runs the output relation at. -/
def adaptiveWave (ws wa I : ℕ) (per : ℕ → ℕ) : ℕ → ℕ :=
  fun r => periodic ws wa (per (intervalOf I r)) r

/-- **The adaptive schedule**: one slot per round, led by the coin at the rounds the period
sequence `per` makes asynchronous and by the known schedule `known` elsewhere. What a validator
that derived `per` runs the output relation on; the liveness claims that relate a schedule to the
coin one clause at a time (SH14) take this one as their instance. -/
abbrev adaptiveSlots (coin known : ℕ → Validator) (I : ℕ) (per : ℕ → ℕ) : Slots Validator :=
  Slots.identity fun r => if IsAsync (per (intervalOf I r)) r then coin r else known r

end Steelhead

end LeanDag
