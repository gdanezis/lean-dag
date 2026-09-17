import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# The period sequence — statement

What the adaptive protocol's period does across views and over time
(`steelhead.md` §5). Thirteen claims:

* **SH10a, agreement of the period** — Theorem 4: two views that derive
  a state for interval `j` derive the same one, period, agreed output
  and last commit alike, under any update rule, with no synchrony,
  fairness or view hypothesis;
* **SH10b, agreement of the output under the adaptive wavelength** — the
  consequence the paper draws, and Theorem 4 as each validator reads it:
  two validators running the output relation at their own derived period
  sequences derive the same sequence and never disagree on a slot, since
  the sequences coincide by strong induction on the interval and SH2
  applies at the common wavelength. The periods are asked for below the record's top round and
  no further: a record holds finitely many blocks, so above its top
  round no chain verdict is derivable and no period beyond it is either,
  and a claim quantified over the whole sequence would hold only where
  the period reaches `0`;
* **SH10c, the scan ends** — once every round of an interval has a chain
  verdict in a view, that view derives the next interval's state: either
  the least chain-committed round is the anchor, or every round is
  chain-skipped;
* **SH10d, the period advances under the clause** — Theorem 3 (i): under
  the run form of the unpredictable-leader clause at the chain schedule,
  a view caught up to the horizon derives a state for every interval
  whose rounds lie far enough below it, by SH7a and SH10c;
* **SH10e, the failover**: Theorem 3 (i)'s last clause, as
  `apply_period_update` has it: an interval that finds an anchor below
  which the agreed output, advanced over the anchor's history, committed
  nothing within `I` rounds hands the next interval period `1`, whatever
  the update rule would answer;
* **SH10f, two asynchronous rounds per interval**: the adaptive
  section's structural fact behind `I ≥ 2 · maxPeriod`. At any period
  `k ≥ 1` with `2 k ≤ I`, every interval holds two asynchronous rounds;
* **SH10g, the period stays in range**: if the initial period lies in
  `[1, K]` and the update rule keeps a period there, so does every
  derived period, the failover's `1` included;
* **SH10i, the agreed output is a prefix of the output**: every slot the
  agreed output consumed is decided in the view that derived it, since
  the anchors' histories lie inside that view; what
  `assert_agreed_prefix` checks in the implementation's tests;
* **SH10j, the output stalls below an undecided slot**: a slot the view
  leaves undecided is never consumed, so the agreed output's cursor and
  last commit stay at or below it, in every state the view derives;
* **SH10k, a window resolves an asynchronous slot of every candidate**:
  at `I ≥ K + wa − 2`, the window of an anchor at or above round `I`
  holds, for every period in `[1, K]`, an asynchronous round whose
  decision round it retains; `I ≥ 2K` alone does not give this;
* **SH14, output liveness under the failover**: Theorem 3 (ii) and the
  asynchronous half of Definition 1's validity, deterministic given two
  events the coin supplies almost surely. With the coin leading every
  round the derived period makes asynchronous, in a view that derived
  every state up to a run's last round, if some interval at least two
  past a slot's finds an anchor and above that interval the coin names a
  committed candidate at `wa` consecutive rounds, then the slot is
  decided once the view holds the run's decision rounds. An anchor two
  intervals up lies more than `I` rounds above the slot, so while the
  slot waits the agreed output's last commit lies below it (SH10j), the
  failover fires at each such anchor and the period is `1` from the
  first, where the run decides everything below it (SH9);
* **SH14b, every slot is decided under the clauses**: SH14 with its two
  events read off Mahi-Mahi's run clause at the chain schedule, with runs
  of `K` good coins. A run of `K` consecutive rounds inside the second
  interval after the slot's, every chain verdict of the interval settled
  by SH7a, gives the interval its anchor; the run in the next interval is
  the one SH14 needs. Every slot three intervals and a window below the
  horizon is then decided, in a view caught up to the horizon that
  derived every state below it;
* **SH14c, output liveness from a good coin and a good run**: SH14 with
  its two events named by the coin alone: a good coin opening an
  interval at least two past the slot's chain-commits its first round,
  and `wa` good coins above that interval settle every chain verdict
  below them (SH7c), so the interval has its anchor and the run is
  SH14's. The form the coin's almost-sure half consumes (SH15): two
  events at named places, each of a fixed positive probability.

The scan reads rounds `1` and above, as `complete_scans` starts at the
interval's first round: round `0`, which `intervalOf` leaves in interval
`0`, is never an anchor and is asked for no verdict, so SH10c's premise
and the anchor predicates exclude it. SH10a, SH10c, SH10d and SH10g hold
for whatever wavelength the agreed
output is read at, SH10a for the same wavelength on both sides; SH10b,
SH10i, SH10j and SH14 to SH14c read it at the adaptive wavelength of the
validator's own sequence. SH10j and SH14 to SH14c speak of slots at
round one or above: the agreed output starts at slot `1`, as the
implementation's does, since round `0` is never output. SH10a assumes
`3 ≤ wa`, as SH5 does, and SH10b `3 ≤ ws` and `3 ≤ wa` and a round `N`
the record does not reach past; SH10c, SH10i and SH10j assume `2 ≤ w r`,
what the laws need to carry a verdict from the anchor's history into the
view and to keep a verdict off the slots above the anchor; SH10d assumes
`1 ≤ wa`, as SH7a does, `2 ≤ w r`, and a positive interval, without which
every round lies in interval `0`; SH10e and SH10g read no record; SH14
assumes `2 ≤ ws ≤ wa` and `3 ≤ wa`, as SH10a does, one slot per round and
a positive interval; SH14b adds `wa ≤ K`, so that a run of `K` holds a
run of `wa`, and `c + K ≤ I`, so that a window and a run fit inside an
interval. No claim here needs the period to stay in range: every round
carries a chain verdict, so an interval's anchor exists whatever period
is in force. SH10f asks `1 ≤ k`, since at `k = 0` only round `0` is
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
    (V₁ V₂ : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st₁ st₂ : ScanState),
    3 ≤ wa →
    PeriodAt I wa coin upd k₀ U V₁ w j st₁ → PeriodAt I wa coin upd k₀ U V₂ w j st₂ → st₁ = st₂

/-- **SH10b, agreement of the output under the adaptive wavelength.** -/
def AdaptiveAgreement (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ N : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (per₁ per₂ : ℕ → ℕ) (k : ℕ)
    (v₁ v₂ : Option BlockId),
    3 ≤ ws → 3 ≤ wa →
    -- the record reaches no higher than round N, and the slot is proposed at or below it
    (∀ b ∈ U.ids, (U.block b).round ≤ N) → S.slotRound k ≤ N →
    -- each view derived the state of every interval those rounds fall in, reading its agreed
    -- output at its own adaptive wavelength
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V₁ (adaptiveWave ws wa I per₁) j st ∧ per₁ j = st.period) →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V₂ (adaptiveWave ws wa I per₂) j st ∧ per₂ j = st.period) →
    -- and decided slot k at its own adaptive wavelength
    Decided (adaptiveWave ws wa I per₁) U V₁ k v₁ →
    Decided (adaptiveWave ws wa I per₂) U V₂ k v₂ →
    -- then the two derived sequences agree on those intervals, and so do the verdicts
    (∀ j, j ≤ intervalOf I N → per₁ j = per₂ j) ∧ v₁ = v₂

/-- **SH10c, the scan ends.** -/
def ScanEnds (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st : ScanState),
    (∀ r, 2 ≤ w r) →
    PeriodAt I wa coin upd k₀ U V w j st →
    -- every scanned round of the interval has a chain verdict in V
    (∀ r, 1 ≤ r → intervalOf I r = j → ∃ v, ChainDecided wa coin U V r v) →
    -- then V derives the next interval's state
    ∃ st', PeriodAt I wa coin upd k₀ U V w (j + 1) st'

/-- **SH10d, the period advances under the clause.** -/
def PeriodOfClause (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (c N : ℕ),
    1 ≤ wa → 0 < I → (∀ r, 2 ≤ w r) →
    -- the run form of the clause at the chain schedule
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- for every interval whose window decides below the horizon ...
    ∀ j, MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N →
      -- ... the view derives the next interval's state
      ∃ st, PeriodAt I wa coin upd k₀ U V w (j + 1) st

/-- **SH10e, the failover.** -/
def PeriodOne (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j r next' last' : ℕ) (st : ScanState)
    (A : BlockId) (hA : A ∈ U.ids),
    -- interval j runs at st, V finds it an anchor at round r, and the agreed output advanced
    -- over the anchor's history committed nothing within I rounds below the anchor ...
    PeriodAt I wa coin upd k₀ U V w j st → IntervalAnchor I wa coin U V j r A →
    AgreedAdvance U w A hA st.next next' st.lastCommit last' → last' + I < r →
    -- ... then interval j + 1 runs at period 1
    PeriodAt I wa coin upd k₀ U V w (j + 1) ⟨1, next', last'⟩

/-- **SH10f, every interval holds two asynchronous rounds.** -/
def TwoAsyncRounds (I : ℕ) : Prop :=
  ∀ j k, 1 ≤ k → 2 * k ≤ I →
    ∃ r₁ r₂, r₁ < r₂ ∧ intervalOf I r₁ = j ∧ IsAsync k r₁ ∧ intervalOf I r₂ = j ∧ IsAsync k r₂

/-- **SH10g, the period stays in range.** -/
def PeriodInRange (U : BlockUniverse Validator BlockId Payload) (I wa K : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st : ScanState),
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K →
    (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- then so does every derived period
    PeriodAt I wa coin upd k₀ U V w j st → 1 ≤ st.period ∧ st.period ≤ K

/-- **SH10i, the agreed output is a prefix of the output.** -/
def AgreedPrefix (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st : ScanState),
    (∀ r, 2 ≤ w r) →
    PeriodAt I wa coin upd k₀ U V w j st →
    -- every slot the agreed output consumed is decided in V
    ∀ s, 1 ≤ s → s < st.next → ∃ v, Decided w U V s v

/-- **SH10j, the output stalls below an undecided slot.** -/
def StalledBelowUndecided (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j s : ℕ) (st : ScanState),
    (∀ r, 2 ≤ w r) →
    -- one slot per round
    (∀ t, S.slotRound t = t) →
    PeriodAt I wa coin upd k₀ U V w j st →
    -- a slot at round one or above that V leaves undecided ...
    1 ≤ s → (∀ v, ¬ Decided w U V s v) →
    -- ... is never consumed, and the last commit lies at or below it
    st.next ≤ s ∧ st.lastCommit ≤ s

/-- **SH10k, a window resolves an asynchronous slot of every candidate.** -/
def WindowResolves (I wa K : ℕ) : Prop :=
  ∀ k top, 1 ≤ k → k ≤ K → 1 ≤ wa → K + wa - 2 ≤ I → I ≤ top →
    ∃ r, top - I ≤ r ∧ r + wa - 1 ≤ top ∧ IsAsync k r

/-- **SH14, output liveness under the failover.** -/
def OutputLiveness (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j₁ r₁ b : ℕ) (A : BlockId),
    -- the synchronous wave is at least two rounds and no longer than the asynchronous one
    2 ≤ ws → ws ≤ wa → 3 ≤ wa →
    -- one slot per round, and a positive interval
    (∀ t, S.slotRound t = t) → 0 < I →
    -- V derived the state of every interval up to the run's last round, reading its agreed
    -- output at the wavelength it runs
    (∀ j, j ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) j st ∧ per j = st.period) →
    -- the coin leads every round the derived period makes asynchronous
    (∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) →
    -- the slot lies at round one or above, and an interval at least two past its own, so that
    -- its anchor lies more than I rounds above the slot, finds an anchor in V ...
    1 ≤ s → intervalOf I s + 1 < j₁ → IntervalAnchor I wa coin U V j₁ r₁ A →
    -- ... and above that interval the coin names a committed candidate at wa consecutive
    -- rounds, in a view holding their decision rounds
    (j₁ + 1) * I < b →
    (∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i)) →
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1)) →
    -- then the slot is decided in V
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v

/-- **SH14b, every slot is decided under the clauses.** -/
def AllDecided (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (c N : ℕ),
    2 ≤ ws → ws ≤ wa → 3 ≤ wa → (∀ t, S.slotRound t = t) → 0 < I →
    -- the coin leads every round the derived period makes asynchronous
    (∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) →
    -- a run of K holds a run of wa, and a window of c rounds plus a run of K fit in an interval
    wa ≤ K → c + K ≤ I →
    -- the run form of the clause at the chain schedule, with runs of K good coins
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c K N →
    -- the view holds every block up to the horizon and derived every state below it, reading
    -- its agreed output at the wavelength it runs
    V.CoversUpto N →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) j st ∧ per j = st.period) →
    -- then every slot at round one or above and three intervals and a window below the horizon
    -- is decided
    ∀ s, 1 ≤ s → MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + c + K) ≤ N →
      ∃ v, Decided (adaptiveWave ws wa I per) U V s v

/-- **SH14c, output liveness from a good coin and a good run.** -/
def OutputLivenessOfRuns (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j b : ℕ),
    2 ≤ ws → ws ≤ wa → 3 ≤ wa → (∀ t, S.slotRound t = t) → 0 < I →
    -- the coin leads every round the derived period makes asynchronous
    (∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) →
    -- V derived the state of every interval up to the run's last round, reading its agreed
    -- output at the wavelength it runs
    (∀ j', j' ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I wa coin upd k₀ U V (adaptiveWave ws wa I per) j' st ∧ per j' = st.period) →
    -- the slot lies at round one or above; at least two intervals past its own, interval j
    -- opens with a good coin ...
    1 ≤ s → intervalOf I s + 1 < j → coin (j * I + 1) ∈ MahiMahi.goodAt U wa (j * I + 1) →
    -- ... and above interval j the coin names a committed candidate at wa consecutive rounds,
    -- in a view holding their decision rounds
    (j + 1) * I < b → (∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i)) →
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1)) →
    -- then the slot is decided in V
    ∃ v, Decided (adaptiveWave ws wa I per) U V s v

/-- The period sequence, over every fault configuration, schedule, block universe, interval,
wavelength pair, period bound and update rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ),
    PeriodAgreement U I wa ∧ AdaptiveAgreement U ws wa I ∧ ScanEnds U I wa ∧
      PeriodOfClause U I wa ∧ PeriodOne U I wa ∧ TwoAsyncRounds I ∧
      PeriodInRange U I wa K ∧ AgreedPrefix U I wa ∧ StalledBelowUndecided U I wa ∧
      WindowResolves I wa K ∧ OutputLiveness U ws wa I ∧
      AllDecided U ws wa I K ∧ OutputLivenessOfRuns U ws wa I

end Period

end Steelhead

end LeanDag
