import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# The period sequence — statement

What the adaptive protocol's period does across views and over time
(`steelhead.md` §5). Sixteen claims:

* **SH10a, agreement of the period** — Theorem 4: two views that derive
  a state for interval `j` derive the same one, period, agreed output
  and last commit alike, under any update rule, with no synchrony,
  fairness or view hypothesis. Induction on the interval: the periods
  agree, so the scans read one control schedule, whose verdicts agree
  (SH10m), so the anchors agree, and the next state is a function of the
  anchor's history;
* **SH10b, agreement of the output under the adaptive kinds** — the
  consequence the paper draws, and Theorem 4 as each validator reads it:
  two validators running the output relation at their own derived period
  sequences, each on the schedule its own sequence names, every slot of
  the kind its period assigns, the coin at the rounds it makes
  asynchronous and the known leader elsewhere (`adaptiveSlots`), derive
  the same sequence and never disagree on a
  slot, since the sequences coincide by strong induction on the interval,
  the state of an interval reading the sequence below that interval only,
  and SH2 applies at the common wavelength and schedule. The periods are
  asked for below the record's top round and no further: a record holds
  finitely many blocks, so above its top round no control verdict is
  derivable and no period beyond it is either, and a claim quantified
  over the whole sequence would hold only where the period reaches `0`;
* **SH10c, the scan ends** — once every control slot of an interval, at
  the interval's period, has a verdict in a view, that view derives the
  next interval's state: either the least committed control slot is the
  anchor, or every one is skipped;
* **SH10d, the period advances under the clause** — Theorem 3 (i): under
  the run form of the unpredictable-leader clause at every control
  schedule the period can name, a view caught up to the horizon derives a
  state for every interval whose control slots lie far enough below it,
  by SH7a at the interval's own schedule and SH10c. The period is kept
  in range so that the schedules are finitely many, since the control
  set is a function of the period;
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
  derived period, the failover's `1` and the warm-up's included;
* **SH10i, the agreed output is a prefix of the output**: every slot the
  agreed output consumed is decided in the view that derived it, since
  the anchors' histories lie inside that view; what
  `assert_agreed_prefix` checks in the implementation's tests;
* **SH10j, the output stalls below an undecided slot**: a slot the view
  leaves undecided is never consumed, so the agreed output's cursor and
  last commit stay at or below it, in every state the view derives;
* **SH10k, a window resolves an asynchronous slot of every candidate**:
  at `I ≥ K + wa − 2`, the window of an anchor above round `I`, the
  `I + 1` rounds from `round A − I` up as `windowBottom` has it, holds,
  for every period in `[1, K]`, an asynchronous round whose decision
  round it retains; `I ≥ 2K` alone does not give this, and neither does
  an anchor at round `I` itself, whose window starts at round `1` and is
  one round short;
* **SH10l, the control schedule enumerates the control rounds**: the
  rounds of `controlSlots coin I K j k` are exactly the multiples of `k`
  up to the interval's boundary and the multiples of `K` above it, the
  implementation's `is_control_round` for the scan of interval `j`;
* **SH10m, control verdicts agree per scan**: two views agree on the
  control verdict of every slot of one scan's schedule, under any coin,
  MM1c at that schedule. Verdicts of different scans are never compared,
  a round above the boundary reading differently in the scan of the next
  interval, whose control set is its own;
* **SH10n, the first interval keeps its period**: the warm-up of
  `apply_period_update`, since the window of the first interval's anchor
  holds the start-up rounds: at an anchor of interval `0` the next
  interval runs at the initial period, the agreed output advanced all
  the same. The failover cannot fire there, the anchor lying at round `I`
  or below and the output's last commit at `0` or above;
* **SH14, output liveness under the failover**: Theorem 3 (ii) and the
  asynchronous half of Definition 1's validity, deterministic given two
  events the coin supplies almost surely. With the coin leading every
  round the derived period makes asynchronous, in a view that derived
  every state up to a run's last round, if some interval at least two
  past a slot's finds an anchor under the period the view derived for it
  and above that interval the coin names a committed candidate at `wa`
  consecutive rounds, then the slot is decided once the view holds the
  run's decision rounds. An anchor two intervals up lies more than `I`
  rounds above the slot, so while the slot waits the agreed output's
  last commit lies below it (SH10j), the failover fires at each such
  anchor and the period is `1` from the first, where the run decides
  everything below it (SH9);
* **SH14b, every slot is decided under the clause**: SH14 with its two
  events read off Mahi-Mahi's run clause at every control schedule the
  period can name, with `c + wa` control slots fitting in an interval at
  every period up to `K`. A run of `wa` good control slots inside the
  second interval after the slot's commits its first slot and settles
  every control slot below it (SH7a), so the interval has an anchor at or
  below that slot; at period `1`, which the failover has fixed, the
  control schedule of the next interval is every round up to its
  boundary, so the run the clause places there is the run of rounds SH14
  needs. Every slot three intervals and a window below the horizon is
  then decided, in a view caught up to the horizon that derived every
  state below it;
* **SH14c, output liveness from a good coin and a good run**: SH14 with
  its two events named by the coin alone: a good coin at the first
  control round of an interval at least two past the slot's, under the
  period the view derived for it, commits that control slot, below which
  the interval holds no other, so the interval has its anchor; and `wa`
  good coins above that interval are SH14's run. The form the coin's
  almost-sure half consumes (SH15): two events at named places, each of
  a fixed positive probability, a block of `K` good coins from the
  interval's first round covering its first control round at every
  period up to `K`.

The scan reads rounds `1` and above, as `complete_scans` starts at the
interval's first round: round `0`, which `intervalOf` leaves in interval
`0`, is never an anchor and is asked for no verdict, so SH10c's premise
and the anchor predicates exclude it. The period bound `K` is positive
throughout, as the implementation's `max_period` is, which the control
schedule needs to be unbounded. SH10a, SH10c, SH10d and SH10g hold for
whatever wavelength the agreed output is read at, SH10a for the same
wavelength on both sides; SH10b, SH10i, SH10j and SH14 to SH14c read it
at the pair's, `wavelength ws wa`, on a schedule whose kinds are the
validator's own sequence's (`adaptiveKind`). SH10j and SH14 to SH14c
speak of slots at round one or above: the agreed output starts at slot
`1`, as the implementation's does, since round `0` is never output.
SH10a assumes `3 ≤ wa`, as SH5 and SH10m do, and SH10b `3 ≤ ws` and
`3 ≤ wa` and a round `N` the record does not reach past; SH10c, SH10i and
SH10j assume `2 ≤ w κ`, what the laws need to carry a verdict from the
anchor's history into the view and to keep a verdict off the slots above
the anchor; SH10d assumes `1 ≤ wa`, as SH7a does, `2 ≤ w κ`, a positive
interval, without which every round lies in interval `0`, and the period
in range, SH10g's hypotheses; SH10n assumes a positive interval too, so
that interval `0` ends at round `I`; SH10e, SH10g and SH10l read no
record; SH14 assumes `2 ≤ ws ≤ wa` and `3 ≤ wa`, as SH10a does, one slot
per round and a positive interval; SH14b adds the period in range and
`(c + wa) · K ≤ I`, so that a window and a run of control slots fit
inside an interval at every period; SH14c asks the derived period of the
anchoring interval to lie in `[1, I]`, so that the interval holds its
first control round. SH10f asks `1 ≤ k`, since at `k = 0` only round `0`
is asynchronous, and SH10g concludes `1 ≤ k` from the same bound on the
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
def PeriodAgreement (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st₁ st₂ : ScanState),
    3 ≤ wa →
    PeriodAt I K wa coin upd k₀ U V₁ w j st₁ → PeriodAt I K wa coin upd k₀ U V₂ w j st₂ →
    st₁ = st₂

/-- **SH10b, agreement of the output under the adaptive kinds.** -/
def AdaptiveAgreement (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin known : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ N : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (per₁ per₂ : ℕ → ℕ) (k : ℕ)
    (v₁ v₂ : Option BlockId),
    3 ≤ ws → 3 ≤ wa →
    -- the record reaches no higher than round N, and the slot is proposed at or below it
    (∀ b ∈ U.ids, (U.block b).round ≤ N) → k ≤ N →
    -- each view derived the state of every interval those rounds fall in, reading its agreed
    -- output on its own adaptive schedule, every slot of the kind its own sequence assigns, the
    -- coin at the rounds that sequence makes asynchronous and the known leader elsewhere
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₁) I K wa coin upd k₀ U V₁
        (wavelength ws wa) j st ∧ per₁ j = st.period) →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₂) I K wa coin upd k₀ U V₂
        (wavelength ws wa) j st ∧ per₂ j = st.period) →
    -- and decided slot k on its own adaptive schedule
    Decided (S := adaptiveSlots coin known I per₁) (wavelength ws wa) U V₁ k v₁ →
    Decided (S := adaptiveSlots coin known I per₂) (wavelength ws wa) U V₂ k v₂ →
    -- then the two derived sequences agree on those intervals, and so do the verdicts
    (∀ j, j ≤ intervalOf I N → per₁ j = per₂ j) ∧ v₁ = v₂

/-- **SH10c, the scan ends.** -/
def ScanEnds (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st : ScanState),
    (∀ κ, 2 ≤ w κ) →
    PeriodAt I K wa coin upd k₀ U V w j st →
    -- every scanned control slot of the interval, at the interval's period, has a verdict in V
    (∀ i, 1 ≤ controlRound I K j st.period i → intervalOf I (controlRound I K j st.period i) = j →
      ∃ v, ControlDecided I K wa coin j st.period U V i v) →
    -- then V derives the next interval's state
    ∃ st', PeriodAt I K wa coin upd k₀ U V w (j + 1) st'

/-- **SH10d, the period advances under the clause.** -/
def PeriodOfClause (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (c N : ℕ),
    1 ≤ wa → 0 < I → (∀ κ, 2 ≤ w κ) →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the run form of the clause at every control schedule a period in range names: in every
    -- window of c control slots below the horizon, wa consecutive ones whose coins are committed
    -- candidates
    (∀ j k, 1 ≤ k → k ≤ K →
      MahiMahi.UnpredictableRunWithin (S := controlSlots coin I K j k) U wa c wa N) →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- for every interval whose control slots, and the window above them, decide below the
    -- horizon ...
    ∀ j, MahiMahi.decisionRoundAt wa ((j + 1) * I + (c + wa) * K) ≤ N →
      -- ... the view derives the next interval's state
      ∃ st, PeriodAt I K wa coin upd k₀ U V w (j + 1) st

/-- **SH10e, the failover.** -/
def PeriodOne (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j i next' last' : ℕ) (st : ScanState)
    (A : BlockId) (hA : A ∈ U.ids),
    -- interval j runs at st, V finds it an anchor at control slot i, and the agreed output
    -- advanced over the anchor's history committed nothing within I rounds below the anchor ...
    PeriodAt I K wa coin upd k₀ U V w j st → IntervalAnchor I K wa coin U V j st.period i A →
    AgreedAdvance U w A hA st.next next' st.lastCommit last' →
    last' + I < controlRound I K j st.period i →
    -- ... then interval j + 1 runs at period 1
    PeriodAt I K wa coin upd k₀ U V w (j + 1) ⟨1, next', last'⟩

/-- **SH10f, every interval holds two asynchronous rounds.** -/
def TwoAsyncRounds (I : ℕ) : Prop :=
  ∀ j k, 1 ≤ k → 2 * k ≤ I →
    ∃ r₁ r₂, r₁ < r₂ ∧ intervalOf I r₁ = j ∧ IsAsync k r₁ ∧ intervalOf I r₂ = j ∧ IsAsync k r₂

/-- **SH10g, the period stays in range.** -/
def PeriodInRange (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st : ScanState),
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K →
    (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- then so does every derived period
    PeriodAt I K wa coin upd k₀ U V w j st → 1 ≤ st.period ∧ st.period ≤ K

/-- **SH10i, the agreed output is a prefix of the output.** -/
def AgreedPrefix (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j : ℕ) (st : ScanState),
    (∀ κ, 2 ≤ w κ) →
    PeriodAt I K wa coin upd k₀ U V w j st →
    -- every slot the agreed output consumed is decided in V
    ∀ s, 1 ≤ s → s < st.next → ∃ v, Decided w U V s v

/-- **SH10j, the output stalls below an undecided slot.** -/
def StalledBelowUndecided (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (j s : ℕ) (st : ScanState),
    (∀ κ, 2 ≤ w κ) →
    -- one slot per round
    (∀ t, S.slotRound t = t) →
    PeriodAt I K wa coin upd k₀ U V w j st →
    -- a slot at round one or above that V leaves undecided ...
    1 ≤ s → (∀ v, ¬ Decided w U V s v) →
    -- ... is never consumed, and the last commit lies at or below it
    st.next ≤ s ∧ st.lastCommit ≤ s

/-- **SH10k, a window resolves an asynchronous slot of every candidate.** -/
def WindowResolves (I wa K : ℕ) : Prop :=
  ∀ k top, 1 ≤ k → k ≤ K → 1 ≤ wa → K + wa - 2 ≤ I →
    -- the anchor lies above round I, so its window holds the full I + 1 rounds
    I < top →
    -- then the window, from max 1 (top − I) to top as `windowBottom` has it, holds an
    -- asynchronous round of period k whose decision round it retains
    ∃ r, max 1 (top - I) ≤ r ∧ r + wa - 1 ≤ top ∧ IsAsync k r

/-- **SH10l, the control schedule enumerates the control rounds.** -/
def ControlRounds (I K : ℕ) : Prop :=
  ∀ j k r, (∃ i, controlRound I K j k i = r) ↔
    (r ≤ (j + 1) * I ∧ r % k = 0) ∨ ((j + 1) * I < r ∧ r % K = 0)

/-- **SH10m, control verdicts agree per scan.** -/
def ControlAgreement (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (j k : ℕ) (V₁ V₂ : View Validator BlockId Payload U) (i : ℕ)
    (v₁ v₂ : Option BlockId),
    3 ≤ wa →
    ControlDecided I K wa coin j k U V₁ i v₁ → ControlDecided I K wa coin j k U V₂ i v₂ →
    v₁ = v₂

/-- **SH10n, the first interval keeps its period.** -/
def WarmUp (U : BlockUniverse Validator BlockId Payload) (I K wa : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (w : ℕ → ℕ) (i next' last' : ℕ) (st : ScanState)
    (A : BlockId) (hA : A ∈ U.ids),
    -- the interval is positive, interval 0 runs at st, V finds it an anchor at control slot i, and
    -- the agreed output advances over the anchor's history ...
    0 < I →
    PeriodAt I K wa coin upd k₀ U V w 0 st → IntervalAnchor I K wa coin U V 0 st.period i A →
    AgreedAdvance U w A hA st.next next' st.lastCommit last' →
    -- ... then interval 1 runs at the same period, the output advanced
    PeriodAt I K wa coin upd k₀ U V w 1 ⟨st.period, next', last'⟩

/-- **SH14, output liveness under the failover.** -/
def OutputLiveness (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j₁ i₁ b : ℕ) (A : BlockId),
    -- the synchronous wave is at least two rounds and no longer than the asynchronous one
    2 ≤ ws → ws ≤ wa → 3 ≤ wa →
    -- one slot per round, of the kind the derived period assigns it, and a positive interval
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- V derived the state of every interval up to the run's last round, reading its agreed
    -- output on the schedule it runs
    (∀ j, j ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j st ∧ per j = st.period) →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- the slot lies at round one or above, and an interval at least two past its own, so that
    -- its anchor lies more than I rounds above the slot, finds an anchor in V under the period
    -- the view derived for it ...
    1 ≤ s → intervalOf I s + 1 < j₁ → IntervalAnchor I K wa coin U V j₁ (per j₁) i₁ A →
    -- ... and above that interval the coin names a committed candidate at wa consecutive
    -- rounds, in a view holding their decision rounds
    (j₁ + 1) * I < b →
    (∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i)) →
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1)) →
    -- then the slot is decided in V
    ∃ v, Decided (wavelength ws wa) U V s v

/-- **SH14b, every slot is decided under the clause.** -/
def AllDecided (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (c N : ℕ),
    2 ≤ ws → ws ≤ wa → 3 ≤ wa → (∀ t, S.slotRound t = t) →
    (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- a window of c control slots plus a run of wa fit in an interval at every period up to K
    (c + wa) * K ≤ I →
    -- the run form of the clause at every control schedule a period in range names, with runs
    -- of wa good coins
    (∀ j k, 1 ≤ k → k ≤ K →
      MahiMahi.UnpredictableRunWithin (S := controlSlots coin I K j k) U wa c wa N) →
    -- the view holds every block up to the horizon and derived every state below it, reading
    -- its agreed output on the schedule it runs
    V.CoversUpto N →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j st ∧ per j = st.period) →
    -- then every slot at round one or above and three intervals and a window below the horizon
    -- is decided
    ∀ s, 1 ≤ s → MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + c + wa) ≤ N →
      ∃ v, Decided (wavelength ws wa) U V s v

/-- **SH14c, output liveness from a good coin and a good run.** -/
def OutputLivenessOfRuns (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ)
    [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j b : ℕ),
    2 ≤ ws → ws ≤ wa → 3 ≤ wa → (∀ t, S.slotRound t = t) →
    (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- V derived the state of every interval up to the run's last round, reading its agreed
    -- output on the schedule it runs
    (∀ j', j' ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K wa coin upd k₀ U V (wavelength ws wa) j' st ∧ per j' = st.period) →
    -- the slot lies at round one or above; at least two intervals past its own, interval j
    -- runs at a period that puts its first control round inside it, and the coin there is
    -- good ...
    1 ≤ s → intervalOf I s + 1 < j → 1 ≤ per j → per j ≤ I →
    coin (firstControlRound I j (per j)) ∈ MahiMahi.goodAt U wa (firstControlRound I j (per j)) →
    -- ... and above interval j the coin names a committed candidate at wa consecutive rounds,
    -- in a view holding their decision rounds
    (j + 1) * I < b → (∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i)) →
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1)) →
    -- then the slot is decided in V
    ∃ v, Decided (wavelength ws wa) U V s v

/-- The period sequence, over every fault configuration, schedule, block universe, interval,
wavelength pair, positive period bound and update rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K],
    PeriodAgreement U I K wa ∧ AdaptiveAgreement U ws wa I K ∧ ScanEnds U I K wa ∧
      PeriodOfClause U I K wa ∧ PeriodOne U I K wa ∧ TwoAsyncRounds I ∧
      PeriodInRange U I K wa ∧ AgreedPrefix U I K wa ∧ StalledBelowUndecided U I K wa ∧
      WindowResolves I wa K ∧ ControlRounds I K ∧ ControlAgreement U I K wa ∧
      WarmUp U I K wa ∧ OutputLiveness U ws wa I K ∧
      AllDecided U ws wa I K ∧ OutputLivenessOfRuns U ws wa I K

end Period

end Steelhead

end LeanDag
