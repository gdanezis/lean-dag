import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# The period sequence — statement

What the adaptive protocol's period does across views and over time
(`steelhead.md` §5). Seven claims:

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
  whose rounds lie far enough below it, by SH7a and SH10c;
* **SH10e, the period reaches `1`**: Theorem 3 (i)'s last clause. Under
  the paper's premise that the update rule maps a window without a
  synchronous commit to `1` (`ResetsOnStall`, `Model/Period.lean`), and
  with no synchronous slot of the interval holding a certified candidate
  (SH8's adversary, within the interval), an interval that finds an
  anchor hands the next interval period `1`. That an anchor exists is the
  almost-sure half, stated with the coin;
* **SH10f, two asynchronous rounds per interval**: the adaptive
  section's structural fact behind `I ≥ 2 · maxPeriod`. At any period
  `k ≥ 1` with `2 k ≤ I`, every interval holds two asynchronous rounds to
  scan;
* **SH10g, the period stays in range**: if the initial period lies in
  `[1, K]` and the update rule keeps a period there, so does every
  derived period.

SH10a and SH10b assume `3 ≤ wa` (and `3 ≤ ws`), as SH5 and SH2 do, and
SH10b a round `N` the record does not reach past; SH10c assumes nothing;
SH10d assumes `1 ≤ wa`, as SH7a does, and a positive interval, without
which every round lies in interval `0`; SH10e assumes nothing of the
waves; SH10f and SH10g read no record. SH10a to SH10c and SH10e hold at
every period, `0` included, and SH10d constrains the interval `I` rather
than the period; SH10f asks `1 ≤ k`, since at `k = 0` only round `0` is
asynchronous, and SH10g concludes `1 ≤ k` from the same bound on the
initial period and the update rule.

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

/-- **SH10e, the period reaches `1` after an anchored interval.** -/
def PeriodOne (U : BlockUniverse Validator BlockId Payload) (ws I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j k r : ℕ) (A : BlockId),
    -- the update rule resets on a window without a synchronous commit
    ResetsOnStall U ws I upd →
    -- no synchronous slot of the interval has a certified candidate (SH8's adversary, in the
    -- interval)
    (∀ (s : ℕ) (L : BlockId), intervalOf I (S.slotRound s) = j → ¬ IsAsync k (S.slotRound s) →
      IsLeaderBlock U s L → MahiMahi.certificates U ws L (S.slotRound s) = ∅) →
    -- interval j runs at k and V finds it an anchor
    PeriodAt I wa coin upd k₀ U V j k → IntervalAnchor I wa coin U V j k r A →
    -- then interval j + 1 runs at period 1
    PeriodAt I wa coin upd k₀ U V (j + 1) 1

/-- **SH10f, every interval holds two asynchronous rounds.** -/
def TwoAsyncRounds (I : ℕ) : Prop :=
  ∀ j k, 1 ≤ k → 2 * k ≤ I →
    ∃ r₁ r₂, r₁ < r₂ ∧ intervalOf I r₁ = j ∧ IsAsync k r₁ ∧ intervalOf I r₂ = j ∧ IsAsync k r₂

/-- **SH10g, the period stays in range.** -/
def PeriodInRange (U : BlockUniverse Validator BlockId Payload) (I wa K : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j k : ℕ),
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K) →
    -- then so does every derived period
    PeriodAt I wa coin upd k₀ U V j k → 1 ≤ k ∧ k ≤ K

/-- The period sequence, over every fault configuration, schedule, block universe, interval,
wavelength pair, period bound and update rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ),
    PeriodAgreement U I wa ∧ AdaptiveAgreement U ws wa I ∧ ScanEnds U I wa ∧
      PeriodOfClause U I wa ∧ PeriodOne U ws I wa ∧ TwoAsyncRounds I ∧ PeriodInRange U I wa K

end Period

end Steelhead

end LeanDag
