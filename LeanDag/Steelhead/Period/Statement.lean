import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# The period sequence — statement

What the adaptive protocol's period does across views and over time
(`steelhead.md` §5). Four claims:

* **SH10a, agreement of the period** — Theorem 4: two views that derive
  a period for interval `j` derive the same one, under any update rule,
  with no synchrony, fairness or view hypothesis;
* **SH10b, agreement of the output under the adaptive wavelength** — the
  consequence the paper draws: two validators running the output
  relation at their own derived period sequences never disagree on a
  slot, since the sequences coincide and SH2 applies at the common
  wavelength. The periods are asked for below the record's top round and
  no further: a record holds finitely many blocks, so above its top
  round no chain verdict is derivable and no period beyond it is either,
  and a claim quantified over the whole sequence would hold only where
  the period reaches `0`;
* **SH10c, the scan ends** — once every asynchronous round of an
  interval has a chain verdict in a view, that view derives the next
  interval's period: either the least chain-committed round is the
  anchor, or every round is chain-skipped;
* **SH10d, the period advances under the clause** — Theorem 3 (i): under
  the run form of the unpredictable-leader clause at the chain schedule,
  a view caught up to the horizon derives a period for every interval
  whose rounds lie far enough below it, by SH7a and SH10c.

SH10a and SH10b assume `3 ≤ wa` (and `3 ≤ ws`), as SH5 and SH2 do, and
SH10b a round `N` the record does not reach past; SH10c assumes nothing;
SH10d assumes `1 ≤ wa`, as SH7a does, and a positive interval, without
which every round lies in interval `0`. None of the four assumes
`0 < k` of a period: SH10a to SH10c hold at every period, and SH10d
constrains the interval `I` rather than the period.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Period

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH10a, agreement of the period.** -/
def PeriodAgreement (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (j k₁ k₂ : ℕ),
    3 ≤ wa →
    PeriodAt I wa coin upd k₀ U V₁ j k₁ → PeriodAt I wa coin upd k₀ U V₂ j k₂ → k₁ = k₂

/-- **SH10b, agreement of the output under the adaptive wavelength.** -/
def AdaptiveAgreement (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ N : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (per₁ per₂ : ℕ → ℕ) (k : ℕ)
    (v₁ v₂ : Option BlockId),
    3 ≤ ws → 3 ≤ wa →
    -- the record reaches no higher than round N, and the slot is proposed at or below it
    (∀ b ∈ U.ids, (U.block b).round ≤ N) → S.slotRound k ≤ N →
    -- each view derived the period of every interval those rounds fall in
    (∀ j, j ≤ intervalOf I N → PeriodAt I wa coin upd k₀ U V₁ j (per₁ j)) →
    (∀ j, j ≤ intervalOf I N → PeriodAt I wa coin upd k₀ U V₂ j (per₂ j)) →
    -- and decided slot k at its own adaptive wavelength
    Decided (adaptiveWave ws wa I per₁) U V₁ k v₁ →
    Decided (adaptiveWave ws wa I per₂) U V₂ k v₂ →
    v₁ = v₂

/-- **SH10c, the scan ends.** -/
def ScanEnds (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j k : ℕ),
    PeriodAt I wa coin upd k₀ U V j k →
    -- every asynchronous round of the interval has a chain verdict in V
    (∀ r, intervalOf I r = j → IsAsync k r → ∃ v, ChainDecided wa coin U V r v) →
    -- then V derives the next interval's period
    ∃ k', PeriodAt I wa coin upd k₀ U V (j + 1) k'

/-- **SH10d, the period advances under the clause.** -/
def PeriodOfClause (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (c N : ℕ),
    1 ≤ wa → 0 < I →
    -- the run form of the clause at the chain schedule
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- for every interval whose window decides below the horizon ...
    ∀ j, MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N →
      -- ... the view derives the next interval's period
      ∃ k, PeriodAt I wa coin upd k₀ U V (j + 1) k

/-- The period sequence, over every fault configuration, schedule, block universe, interval,
wavelength pair and update rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ),
    PeriodAgreement U I wa ∧ AdaptiveAgreement U ws wa I ∧ ScanEnds U I wa ∧
      PeriodOfClause U I wa

end Period

end Steelhead

end LeanDag
