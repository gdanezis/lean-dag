import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# The period sequence — statement

What the adaptive protocol's period does across views and over time
(`steelhead.md` §5). Eleven claims:

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
* **SH10e, the period reaches `1`**: Theorem 3 (i)'s last clause, under
  the failover in place of the paper's premise on the update rule
  (`ResetsOnNoOutput`, `Model/Period.lean`): an interval that finds an
  anchor whose window the view did not output, since every slot of the
  window the view commits sits above one the view leaves undecided,
  hands the next interval period `1`, because what the validator hands
  the rule as the window's output (`adaptiveOutput`) is then empty. That
  an anchor exists is the almost-sure half, stated with the coin;
* **SH10f, two asynchronous rounds per interval**: the adaptive
  section's structural fact behind `I ≥ 2 · maxPeriod`. At any period
  `k ≥ 1` with `2 k ≤ I`, every interval holds two asynchronous rounds to
  scan;
* **SH10g, the period stays in range**: if the initial period lies in
  `[1, K]` and the update rule keeps a period there, so does every
  derived period;
* **SH10h, the failover satisfies its clause**: any update rule wrapped
  in the failover (`failover`, `Model/Period.lean`) answers `1` to an
  empty output, by construction, so the paper's replay with the agreed
  failover is a rule the liveness claims apply to;
* **SH14, output liveness under the failover**: Theorem 3 (ii) and the
  asynchronous half of Definition 1's validity, deterministic given two
  events the coin supplies almost surely. Under the failover, with the
  coin leading every round the derived period makes asynchronous, in a
  view that derived every period up to a run's last round, if some
  interval at least two past a slot's finds an anchor and above that
  interval the coin names a committed candidate at `wa` consecutive
  rounds, then the slot is decided once the view holds the run's decision
  rounds. The window of an anchor two intervals up lies wholly above the
  slot, so a slot the view leaves undecided sits below every commit of
  every such window, the failover fires at each anchored one and the
  period is `1` from the first, where the run decides everything below
  it (SH9);
* **SH14b, every slot is decided under the clauses**: SH14 with its two
  events read off Mahi-Mahi's run clause at the chain schedule, with runs
  of `K` good coins, `K` the bound the periods stay within (SH10g). A run
  of `K` consecutive rounds inside the second interval after the slot's
  hits an asynchronous round under whatever period is in force, whose
  chain commit, every chain verdict of the interval settled by SH7a,
  gives the interval its anchor; the run in the next interval is the one
  SH14 needs. Every slot three intervals and a window below the horizon
  is then decided, in a view caught up to the horizon that derived every
  period below it;
* **SH14c, output liveness from two good runs**: SH14 with its two
  events named as runs of the coin alone: `K` good coins opening an
  interval at least two past the slot's hit an asynchronous round under
  whatever period is in force, and `wa` good coins above that interval
  settle every chain verdict below them (SH7c), so the interval has its
  anchor and the run is SH14's. The form the coin's almost-sure half
  consumes (SH15): two runs at named places, each of a fixed positive
  probability.

SH10a, SH10c, SH10d and SH10g hold for whatever output the validators
hand the rule, SH10a for the same handover on both sides; SH10b, SH10e
and SH14 to SH14c hand it what the window output at the validator's own
wavelength. SH10a and SH10b assume `3 ≤ wa` (and `3 ≤ ws`), as SH5 and
SH2 do, and SH10b a round `N` the record does not reach past, below
which the windows of the anchors lie and the two handovers agree; SH10c
assumes nothing;
SH10d assumes `1 ≤ wa`, as SH7a does, and a positive interval, without
which every round lies in interval `0`; SH10e assumes `2 ≤ ws` and
`2 ≤ wa`, what the laws need to carry a verdict from the anchor's history
into the view; SH10f and SH10g read no record; SH14 assumes `2 ≤ ws ≤ wa`
and `3 ≤ wa`, as SH10a does, one slot per round and a positive interval;
SH14b adds `wa ≤ K`, so that a run of `K` holds a run of `wa`, and
`c + K ≤ I`, so that a window and a run fit inside an interval; SH14c
asks `K ≤ I`, so that a block of `K` rounds fits.
SH10a to SH10c and SH10e hold at every period, `0` included, and SH10d
constrains the interval `I` rather than the period; SH10f asks `1 ≤ k`,
since at `k = 0` only round `0` is asynchronous, and SH10g concludes
`1 ≤ k` from the same bound on the initial period and the update rule.

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
    (V₁ V₂ : View Validator BlockId Payload U) (out : BlockId → Finset BlockId) (j k₁ k₂ : ℕ),
    3 ≤ wa →
    PeriodAt I wa coin upd k₀ U V₁ out j k₁ → PeriodAt I wa coin upd k₀ U V₂ out j k₂ → k₁ = k₂

/-- **SH10b, agreement of the output under the adaptive wavelength.** -/
def AdaptiveAgreement (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ N : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (per₁ per₂ : ℕ → ℕ) (k : ℕ)
    (v₁ v₂ : Option BlockId),
    3 ≤ ws → 3 ≤ wa →
    -- the record reaches no higher than round N, and the slot is proposed at or below it
    (∀ b ∈ U.ids, (U.block b).round ≤ N) → S.slotRound k ≤ N →
    -- each view derived the period of every interval those rounds fall in, handing the rule
    -- what each anchor's window output at its own wavelength
    (∀ j, j ≤ intervalOf I N →
      PeriodAt I wa coin upd k₀ U V₁ (adaptiveOutput ws wa I per₁ U) j (per₁ j)) →
    (∀ j, j ≤ intervalOf I N →
      PeriodAt I wa coin upd k₀ U V₂ (adaptiveOutput ws wa I per₂ U) j (per₂ j)) →
    -- and decided slot k at its own adaptive wavelength
    Decided (adaptiveWave ws wa I per₁) U V₁ k v₁ →
    Decided (adaptiveWave ws wa I per₂) U V₂ k v₂ →
    v₁ = v₂

/-- **SH10c, the scan ends.** -/
def ScanEnds (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (out : BlockId → Finset BlockId) (j k : ℕ),
    PeriodAt I wa coin upd k₀ U V out j k →
    -- every asynchronous round of the interval has a chain verdict in V
    (∀ r, intervalOf I r = j → IsAsync k r → ∃ v, ChainDecided wa coin U V r v) →
    -- then V derives the next interval's period
    ∃ k', PeriodAt I wa coin upd k₀ U V out (j + 1) k'

/-- **SH10d, the period advances under the clause.** -/
def PeriodOfClause (U : BlockUniverse Validator BlockId Payload) (I wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (out : BlockId → Finset BlockId) (c N : ℕ),
    1 ≤ wa → 0 < I →
    -- the run form of the clause at the chain schedule
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- for every interval whose window decides below the horizon ...
    ∀ j, MahiMahi.decisionRoundAt wa ((j + 1) * I + 1 + c + wa - 1) ≤ N →
      -- ... the view derives the next interval's period
      ∃ k, PeriodAt I wa coin upd k₀ U V out (j + 1) k

/-- **SH10e, the period reaches `1` after an anchor whose window was not output.** -/
def PeriodOne (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (j k r : ℕ) (A : BlockId),
    2 ≤ ws → 2 ≤ wa →
    -- the update rule fails over on an empty output
    ResetsOnNoOutput upd →
    -- interval j runs at k, the rule handed what each anchor's window output at the wavelength
    -- the validator runs, and V finds it an anchor ...
    PeriodAt I wa coin upd k₀ U V (adaptiveOutput ws wa I per U) j k →
    IntervalAnchor I wa coin U V j k r A →
    -- ... and V output nothing of the anchor's window: every slot of the window it commits sits
    -- above one it leaves undecided
    (∀ (s : ℕ) (L : BlockId), windowBottom U A I ≤ S.slotRound s →
      Decided (adaptiveWave ws wa I per) U V s (some L) →
      ∃ s', s' < s ∧ ∀ v, ¬ Decided (adaptiveWave ws wa I per) U V s' v) →
    -- then interval j + 1 runs at period 1
    PeriodAt I wa coin upd k₀ U V (adaptiveOutput ws wa I per U) (j + 1) 1

/-- **SH10f, every interval holds two asynchronous rounds.** -/
def TwoAsyncRounds (I : ℕ) : Prop :=
  ∀ j k, 1 ≤ k → 2 * k ≤ I →
    ∃ r₁ r₂, r₁ < r₂ ∧ intervalOf I r₁ = j ∧ IsAsync k r₁ ∧ intervalOf I r₂ = j ∧ IsAsync k r₂

/-- **SH10g, the period stays in range.** -/
def PeriodInRange (U : BlockUniverse Validator BlockId Payload) (I wa K : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (out : BlockId → Finset BlockId) (j k : ℕ),
    -- the initial period lies in [1, K], and the update rule keeps a period there, whatever
    -- output it is handed
    1 ≤ k₀ → k₀ ≤ K →
    (∀ j A out k, 1 ≤ k → k ≤ K → 1 ≤ upd j A out k ∧ upd j A out k ≤ K) →
    -- then so does every derived period
    PeriodAt I wa coin upd k₀ U V out j k → 1 ≤ k ∧ k ≤ K

/-- **SH10h, the failover satisfies its clause.** -/
def FailoverResets (BlockId : Type) [LinearOrder BlockId] : Prop :=
  ∀ upd : UpdateRule BlockId, ResetsOnNoOutput (failover upd)

/-- **SH14, output liveness under the failover.** -/
def OutputLiveness (U : BlockUniverse Validator BlockId Payload) (ws wa I : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j₁ r₁ b : ℕ) (A : BlockId),
    -- the synchronous wave is at least two rounds and no longer than the asynchronous one
    2 ≤ ws → ws ≤ wa → 3 ≤ wa →
    -- one slot per round, and a positive interval
    (∀ t, S.slotRound t = t) → 0 < I →
    -- the update rule fails over on an empty output
    ResetsOnNoOutput upd →
    -- V derived the period of every interval up to the run's last round, handing the rule what
    -- each anchor's window output at the wavelength it runs
    (∀ j, j ≤ intervalOf I (b + wa - 1) →
      PeriodAt I wa coin upd k₀ U V (adaptiveOutput ws wa I per U) j (per j)) →
    -- the coin leads every round the derived period makes asynchronous
    (∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) →
    -- an interval at least two past the slot's, so that its anchor's window lies wholly above
    -- the slot, finds an anchor in V ...
    intervalOf I s + 1 < j₁ → IntervalAnchor I wa coin U V j₁ (per j₁) r₁ A →
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
    -- the periods stay in [1, K], and a window of c rounds plus a run of K fit in an interval
    1 ≤ k₀ → k₀ ≤ K →
    (∀ j A out k, 1 ≤ k → k ≤ K → 1 ≤ upd j A out k ∧ upd j A out k ≤ K) →
    wa ≤ K → c + K ≤ I →
    -- the update rule fails over on an empty output
    ResetsOnNoOutput upd →
    -- the run form of the clause at the chain schedule, with runs of K good coins: one hits
    -- an asynchronous round of any interval under any period in force
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c K N →
    -- the view holds every block up to the horizon and derived every period below it, handing
    -- the rule what each anchor's window output at the wavelength it runs
    V.CoversUpto N →
    (∀ j, j ≤ intervalOf I N →
      PeriodAt I wa coin upd k₀ U V (adaptiveOutput ws wa I per U) j (per j)) →
    -- then every slot three intervals and a window below the horizon is decided
    ∀ s, MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + c + K) ≤ N →
      ∃ v, Decided (adaptiveWave ws wa I per) U V s v

/-- **SH14c, output liveness from two good runs.** -/
def OutputLivenessOfRuns (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j b : ℕ),
    2 ≤ ws → ws ≤ wa → 3 ≤ wa → (∀ t, S.slotRound t = t) → 0 < I →
    -- the coin leads every round the derived period makes asynchronous
    (∀ r, IsAsync (per (intervalOf I r)) r → S.leader r = coin r) →
    -- the periods stay in [1, K], and K rounds fit in an interval
    1 ≤ k₀ → k₀ ≤ K →
    (∀ j A out k, 1 ≤ k → k ≤ K → 1 ≤ upd j A out k ∧ upd j A out k ≤ K) → K ≤ I →
    -- the update rule fails over on an empty output
    ResetsOnNoOutput upd →
    -- V derived the period of every interval up to the run's last round, handing the rule what
    -- each anchor's window output at the wavelength it runs
    (∀ j', j' ≤ intervalOf I (b + wa - 1) →
      PeriodAt I wa coin upd k₀ U V (adaptiveOutput ws wa I per U) j' (per j')) →
    -- at least two intervals past the slot's, interval j opens with K good coins ...
    intervalOf I s + 1 < j →
    (∀ i, i < K → coin (j * I + 1 + i) ∈ MahiMahi.goodAt U wa (j * I + 1 + i)) →
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
      PeriodOfClause U I wa ∧ PeriodOne U ws wa I ∧ TwoAsyncRounds I ∧
      PeriodInRange U I wa K ∧ FailoverResets BlockId ∧ OutputLiveness U ws wa I ∧
      AllDecided U ws wa I K ∧ OutputLivenessOfRuns U ws wa I K

end Period

end Steelhead

end LeanDag
