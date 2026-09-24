import LeanDag.Steelhead.Model.Chain
import LeanDag.Steelhead.Model.Reactive
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# The `3f + 1` pair's liveness — statement

The liveness claims at the Mysticeti and Mahi-Mahi pair, read at a
wavelength function `w`: `steelheadAnchored w`, Mahi-Mahi's rule at the
wave of each slot's kind. A claim numbered like one of the generic
statements of `Liveness/Statement.lean` is that statement at this rule,
with the clauses of `Model/Clauses.lean` discharged by Mahi-Mahi's
certificates; a claim with no generic counterpart is this pair's alone.

What the rule decides under synchrony, what the chain decides under the
unpredictable-leader clause, and what the output does *not* decide under
the paper's asynchronous adversary (`steelhead.md` §4–6). Seventeen
claims:

* **SH-MM6a, a reliable leader commits under coverage** — Theorem 2's
  per-slot half: on a DAG a reliable quorum has synchronised and
  populated through the slot's decision round, a reliably led slot
  commits in every view caught up to that round, by the direct rule, at
  whichever wave the slot's kind carries;
* **SH-MM6b, everything below a fair run is decided** — the core's L10 at
  the wavelength function: past any slot the schedule offers a run of
  reliably led slots, and once the DAG is covered through the run's
  decision rounds every slot below the run is decided;
* **SH-MM6c, a crashed leader is skipped** — Theorem 2's "crashed-led
  skips from `n − f` blames": a slot whose leader has no block at its
  round is directly skipped in every view holding its vote round, once a
  reliable quorum populates that round, at whichever wave the round
  carries;
* **SH-MM6d, partial dissemination does not defer** — Theorem 2's remark:
  a candidate that one reliable block references one round up, the
  leader's only block at that round, is directly committed in every view
  holding its decision round, once the quorum is synchronised from that
  round and populates the wave. The leader need not be reliable: it may
  be Byzantine, so long as it did not equivocate;
* **SH-MM6e, a reliable slot above the floor decides the slot** — Theorem
  2's Byzantine-led clause, as the anchor rule has it: under synchrony a
  slot is decided once every slot from its floor up to some reliably led
  slot is decided, whatever led them. The reliably led slot commits
  directly (SH-MM6a), so the earliest commit at or above the floor is the
  anchor, and every slot between, decided but not committed, is a skip
  the search passes over. An undecided slot at the floor, one led by an
  equivocating Byzantine validator, is what the hypothesis excludes;
* **SH-MM6f, the floor chain decides** — Theorem 2's chain of floors as a
  theorem: hop from a slot to the first slot at or above its floor that
  the view does not skip, and again from there; if the chain reaches a
  reliably led landing in `h` hops, the slot it started from is decided.
  Downward induction on the chain: the last landing commits (SH-MM6a), and
  a landing whose own floor chain has committed is decided (SH-MM6e's
  argument) and not skipped, so it commits too and anchors the landing
  below it. The hops are a hypothesis, so the claim is a round count
  rather than a count of Byzantine validators: what bounds the chain is
  SH-MM6g;
* **SH-MM6g, the round-robin schedule offers a reliable run** — what the
  implementation's known schedule gives, and what SH-MM6b asks for: at
  `leader r = r mod n`, a validator outside `T` spoils at most `c` of
  the `n` windows of `c` consecutive rounds a cycle holds, so at
  `c · (n − |T|) < n` some window is wholly `T`-led, and the schedule
  repeats it past every round. At `c = 3` and `n = 3f + 1` every correct
  quorum qualifies, which discharges SH-MM6b's fairness hypothesis at the
  constant wave three; at `c = wa` it does not, so the asynchronous
  rounds rest on the coin (SH-MM7, SH14a) and not on the schedule. The
  second half bounds the wait for one reliable leader by `n − |T|`
  rounds, which with SH-MM6e is Theorem 2's Byzantine-led clause as a round
  count: the floor chain reaches a reliably led slot at most `w + b + c`
  rounds above the floor, where the paper counts `b` hops;
* **SH-MM6h, the floor chain reaches a reliably led landing** — Theorem 2's
  hop count: at the round-robin schedule and the constant synchronous
  wave, if `ws · (n − |T|) < n` then one of the chain's first `n − |T|`
  landings is reliably led, which with SH-MM6f decides the slot the chain
  started from within that many hops. Two landings at one residue would
  bound a whole number of cycles, each holding `|T|` reliably led rounds,
  and every one of those would have to fall in the `ws − 1` rounds a hop
  leaves free, since a reliably led round commits (SH-MM6a) and a view
  decides a slot one way, so it is never one of the skips the hop passes
  over; counting the two against each other gives `n ≤ ws · (n − |T|)`.
  So the landings' residues are distinct and only `n − |T|` are left
  free;
* **SH-MM6i, the floor chain reaches a reliably led landing within `b`
  hops** — Theorem 2's count as the paper states it, `b` the Byzantine
  validators: SH-MM6h once every validator outside `T` that is not
  Byzantine has crashed, having no block from the synchronised round on.
  A crashed leader's slot is directly skipped once the reliable set
  populates its vote round (SH-MM6c), and a landing is a slot the view does
  not skip, so every landing led from outside `T` is Byzantine-led; the
  landings' residues are distinct (SH-MM6h's count), and the Byzantine
  validators hold only `b` of them, so one of the first `b + 1` landings
  is reliably led. The chain's own start is asked not to be skipped
  either, which an undecided slot is not;
* **SH-MM6j, the floor chain decides within `(b + 1) · (ws + f)` rounds** —
  Theorem 2's round count above a synchronous floor, at the round-robin
  schedule with SH-MM6i's crashed validators: a reliably led round lies
  within `n − |T|` rounds above any floor (SH-MM6g), it commits (SH-MM6a) and
  so is not passed over, so each hop lands within `ws + (n − |T|)`
  rounds of the slot below it; one of the first `b + 1` landings is
  reliably led (SH-MM6i); and its commit decides the chain's start (SH-MM6f).
  A view holding `(b + 1) · (ws + (n − |T|))` rounds above an unskipped
  slot therefore decides it, the paper's `(b + 1)(ws + f)` at
  `f = n − |T|`;
* **SH-MM6m, a committed landing decides the chain's start** — SH-MM6f with
  its last landing's reliable leader weakened to a commit, whoever led
  it. The chain is what the anchor search walks, and a commit is all the
  descent needs at the top of it; a reliable leader was only ever the
  way SH-MM6f came by one. With the commit given, the claim asks for no
  quorum, no synchrony and no horizon: it is the descent alone. This is
  what lets the chain stop at a slot the coin decided rather than the
  schedule;
* **SH-MM6n, the periodic round robin offers a reliable synchronous round**
  — SH-MM6g's second half at a period. Every window of `n` rounds holds one
  round of each residue, so `T.card` of them are reliably led where the
  leader is known; at most `⌈n / p⌉` carry a coin instead, so past every
  round a reliable synchronous round lies within `n − 1` rounds once
  `⌈n / p⌉ < |T|`. The bound is `n − 1` and not SH-MM6g's `n − |T|`: a
  reliable residue may fall on a coin round, and the schedule cannot say
  which;
* **SH-MM6o, the floor chain reaches a reliably led or committed landing at
  a period** — SH-MM6h at the paper's dial rather than at a constant wave,
  which is where the wavelength function stops being a formality. Two
  things change. A landing may be a slot no coin governs and no schedule
  names, so the claim asks that every asynchronous slot above the chain's
  start be decided, which is what SH-MM7a gives and what the schedule
  cannot; such a landing is then committed, since a landing is by
  definition unskipped, and the chain stops there. And SH-MM6h's count
  loses the coin's rounds: it counts, over a span of whole cycles, the
  rounds the round robin leads from `T`, and a coin round is led by
  nobody the schedule knows, so at most `⌈n / p⌉` of every `n` rounds
  drop out of the count and the bound becomes
  `ws · (n − |T|) + ws · ⌈n / p⌉ < n`. ⚠ At `ws = 3`, `n = 3f + 1` and a
  bare reliable quorum `|T| = n − f` this is `3f + 3⌈n / p⌉ < 3f + 1`,
  false for every period, so the claim is empty there and the coin, not
  the schedule, carries the asynchronous slots; it holds as soon as
  fewer than `f` validators lie outside `T`, or the committee has slack
  (`LeanDagTest/Steelhead/Counterexamples/PeriodicFairness.lean`);
* **SH-MM6p, the floor chain decides within `(b + 1) · (ws + W)` rounds at
  a period** — SH-MM6j's round count at the dial, `W` the wait for a
  reliably led synchronous round rather than the `n − |T|` of SH-MM6g. The
  paper writes `(b + 1)(ws + f)`; at a period `f` is the wrong second
  factor, because a reliable residue may land on a coin round, and SH-MM6n
  supplies `n − 1` in its place. Everything else is SH-MM6j's argument with
  SH-MM6o for the hop count and SH-MM6m for the descent;
* **SH-MM6k, a reliable leader commits under the reactive discipline** —
  SH-MM6a with the execution discipline named rather than assumed: a
  reactive schedule never waits past its timeout, and at the round above
  a reliable leader of a round that carries the leader wait, a
  synchronous slot or a canary round, a block either votes or its
  builder waited the timeout out and votes for what it holds. The wait
  is asked at those rounds alone, since nobody waits for the hidden
  leader of an asynchronous slot, and the claim is stated for a slot at
  such a round. At a wave of four rounds or more that is all it takes,
  the votes reaching the certifiers through the DAG; at the wave of
  three a certifier must reference the votes themselves, which is
  `ReactiveS`'s one added clause, the vote wait the paper's pacing
  states, and `LeanDagTest/Steelhead/Reactive.lean` inhabits the structure. `SynchronisedOn` appears nowhere: a reactive builder omits what
  has not arrived, so it is false by design in such an execution;
* **SH-MM6l, a reliable leader commits under the timed discipline** — the
  other route to SH-MM6a's hypothesis: a `ViewPace` whose timeout grows at
  a rate that clears the delay synchronises the reliable set from
  `max (2Δ + proc, gst)`, and SH-MM6a takes it from there. The claim is
  worth exactly what the core's `ViewPace` is, which is a question about
  that structure and not about this arc;
* **SH-MM7a, chain liveness** — MM3c at any schedule whose rounds strictly
  increase, the coin schedule and every control schedule among them: a
  run of `wa` consecutive commits, which the clause promises in every
  window, decides every verdict below it. Consecutive slots lie at least
  one round apart, so `wa` of them span the wave, which is all the
  descent asks of a schedule;
* **SH-MM7b, the chain under synchrony** — L10 at any such schedule: past
  any slot the coin names reliable leaders at `wa` consecutive slots,
  and once the DAG is covered through that run's decision rounds every
  verdict below it is settled, with no clause;
* **SH-MM7c, one run settles the chain below it** — the step SH-MM7a takes
  once per round, on its own: `wa` consecutive rounds whose coins name
  committed candidates settle every chain verdict below the first, in
  any view holding their decision rounds. The form the coin's almost-sure
  half consumes (SH15), which asks for one run, not one in every window;
* **SH-MM8, the stall** — at a period `k ≥ ws` and one slot per round, if
  no synchronous candidate is ever certified and no synchronous slot is
  directly skipped, then no slot at a round `≡ k − 1 (mod k)` is ever
  decided, in any view, whatever the asynchronous slots do. The paper's
  own adversary — the leader block delivered to exactly `f + 1`
  validators before the vote — produces these hypotheses at every
  synchronous slot, so the output stalls at every period `k ≥ ws`.
  This is the paper's "Why the chain, and not the output" as
  a theorem, for every period rather than the one it walks through
  (`steelhead.md` §4; the DAG is `LeanDagTest/Steelhead/Counterexamples/Stall.lean`);
* **SH-MM9a, the drain** — Theorem 3 (ii): at any wavelength function
  bounded by `wa` and one slot per round, `wa` consecutive committed
  slots decide every slot below them, whatever wave those slots carry.
  Once the period is `1` and Mahi-Mahi's run clause supplies the run,
  the slots an earlier period left undecided are finished by it;
* **SH-MM9b, at period one every slot is decided**: Theorem 3 (ii) as one
  statement. With every slot of the asynchronous kind, as period one
  has it, under the run clause at the output
  schedule, past every round whose window decides below the horizon
  there is a slot below which every slot is decided, in any view caught
  up to the horizon, so the settled prefix and with it the ledger (SH13)
  extend as far as the horizon and the clause reach;
* **SH-MM9c, the cost of an asynchronous slot**: the protocol section's
  healthy-network arithmetic. An asynchronous slot decides `wa − ws`
  rounds later than a synchronous slot would, and the synchronous slot
  `i` rounds above it is decided at most `max(0, wa − ws − i)` rounds
  before it, so the successor waits at most `wa − ws − 1` rounds for
  causal ordering and the wait is nonincreasing in `i`: delays never
  compound.

SH-MM6a, SH-MM6b, SH-MM6e, SH-MM6f and SH-MM6m assume `3 ≤ w κ` everywhere, as the
safety claims do, and SH-MM6e, SH-MM6f and SH-MM6m one slot per round; SH-MM6g and
SH-MM6n read no DAG at
all, only the schedule, and SH-MM6h, SH-MM6i and SH-MM6j, which read both, fix the wave at
the constant `ws` the round-robin count needs, while SH-MM6o and SH-MM6p read
it at `wavelength ws wa` under the kinds a period assigns; SH-MM6c assumes nothing of the wave, and
SH-MM6d `4 ≤ w κ` at the slot's kind, so that the vote round lies two
rounds up, where synchrony has carried the candidate. Neither asks the
quorum to be correct: SH-MM6c reads blames, which need no vote, and SH-MM6d
reads votes for a candidate its leader did not equivocate on. SH-MM7a and SH-MM7c
assume `1 ≤ wa`, as MM3c does, and SH-MM7b `4 ≤ wa`, as MM5 does; SH-MM8 assumes
`2 ≤ ws ≤ k` and nothing of `wa`; SH-MM9a assumes `1 ≤ w κ ≤ wa`; SH-MM9b
assumes `1 ≤ wa`, as SH-MM7a does; SH-MM9c assumes `1 ≤ ws ≤ wa`. SH-MM8, SH-MM9b
and SH-MM9c read the period through the schedule's kinds, `periodicKind k`
at the slot's round, every slot asynchronous at period one; the paper's
`w(r)` is that reading at `wavelength ws wa` (SH4).

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH-MM6a, a reliable leader commits under coverage.** -/
def CommitsOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N k : ℕ),
    (∀ κ, 3 ≤ w κ) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the slot lies at or past R, and every slot up to it decides at or below N
    R ≤ S.slotRound k →
    (∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    -- the view holds every block up to N
    V.CoversUpto N →
    -- and the slot's leader is reliable
    S.leader k ∈ T →
    -- then the slot commits its candidate in that view, by the direct rule
    ∃ L, IsLeaderBlock U k L ∧
      MahiMahi.DirectCommitIn U V (w (S.kind k)) L (S.slotRound k) ∧ Decided w U V k (some L)

/-- **SH-MM6b, everything below a fair run is decided.** The run is named by
the schedule alone, before any DAG is mentioned, so the horizon cannot
cap how far fairness reaches. -/
def AllDecidedBelowOfSynchrony (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (c : ℕ),
    (∀ κ, 3 ≤ w κ) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- a run of c slots spans eligibility, each slot at the wave of its own round
    (steelheadAnchored Validator BlockId Payload w).SpansEligible c →
    -- past any slot the schedule offers c consecutive T-led slots
    FairRunOn T c →
    -- then past any slot k and any round R there is a slot b ...
    ∀ (R k : ℕ), ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      -- ... below which every slot is decided, on any DAG T has synchronised
      -- from R and populated through the run's decision rounds, in any view
      -- covering them
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N →
        (∀ j, j < b + c → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, Decided w U V i v

/-- **SH-MM6c, a crashed leader is skipped.** -/
def SkipsCrashed (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (k : ℕ),
    -- T is a quorum
    quorumCard Validator ≤ T.card →
    -- the leader has no block at the slot's round
    (∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k) →
    -- T populates the vote round, which the view holds
    PopulatedOn U T (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k)) →
    V.CoversUpto (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k)) →
    -- then the slot is skipped in that view
    Decided w U V k none

/-- **SH-MM6d, partial dissemination does not defer.** -/
def CommitsOfDissemination (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (k : ℕ) (L q : BlockId),
    4 ≤ w (S.kind k) →
    -- T is a quorum
    quorumCard Validator ≤ T.card →
    -- L is the slot's candidate, and its leader's only block at the slot's round
    IsLeaderBlock U k L →
    (∀ L' ∈ U.ids, (U.block L').round = S.slotRound k → (U.block L').creator = S.leader k →
      L' = L) →
    -- one reliable block one round up references it ...
    q ∈ U.ids → (U.block q).round = S.slotRound k + 1 → (U.block q).creator ∈ T →
    L ∈ (U.block q).refs →
    -- ... T is synchronised from that round and populates it through the decision round ...
    SynchronisedOn U T (S.slotRound k + 1) →
    (∀ r, S.slotRound k + 1 ≤ r →
      r ≤ MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k) → PopulatedOn U T r) →
    -- ... and the view holds the decision round
    V.CoversUpto (MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k)) →
    -- then the slot commits its candidate in that view
    Decided w U V k (some L)

/-- **SH-MM6e, a reliable slot above the floor decides the slot.** -/
def DecidedOfReliableAboveFloor (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N k a : ℕ),
    (∀ κ, 3 ≤ w κ) →
    -- one slot per round
    (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the slot lies at or past R
    R ≤ k →
    -- slot a lies at or above k's floor, read at k's kind, and is reliably led
    k + w (S.kind k) ≤ a → S.leader a ∈ T →
    -- every slot from the floor up to a is decided in V
    (∀ j, k + w (S.kind k) ≤ j → j < a → ∃ v, Decided w U V j v) →
    -- every slot up to a decides at or below N, which the view holds
    (∀ j, j ≤ a → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    V.CoversUpto N →
    -- then the slot is decided in V
    ∃ v, Decided w U V k v

/-- **SH-MM6f, the floor chain decides.** -/
def FloorChainDecides (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N h : ℕ) (x : ℕ → ℕ),
    (∀ κ, 3 ≤ w κ) →
    -- one slot per round, as Theorem 2 reads the chain
    (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the chain starts at or past R and hops h times, each to the first slot at or above the
    -- landing's floor that the view does not skip
    R ≤ x 0 → (∀ i, i < h → FloorHop w U V (x i) (x (i + 1))) →
    -- its last landing is reliably led, and every slot up to it decides at or below N
    S.leader (x h) ∈ T →
    (∀ j, j ≤ x h → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    V.CoversUpto N →
    -- then the slot the chain started from is decided
    ∃ v, Decided w U V (x 0) v

/-- **SH-MM6g, the round-robin schedule offers a reliable run.** -/
def RoundRobinFairRun : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)),
    -- past every round the schedule leads c consecutive rounds from T, once the validators
    -- outside T, which spoil at most c windows each, cannot spoil all n windows of a cycle
    (∀ c, c * (n - T.card) < n →
      FairRunOn (S := Slots.identity fun r => (⟨r % n, Nat.mod_lt r hn⟩ : Fin n)) T c) ∧
    -- and at or above every round it leads one within n − |T| rounds
    (T.Nonempty → ∀ r, ∃ a, r ≤ a ∧ a ≤ r + (n - T.card) ∧
      (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T)

/-- **SH-MM6h, the floor chain reaches a reliably led landing.** -/
def FloorChainReachesReliable (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (x : ℕ → ℕ),
    -- the constant synchronous wave and one slot per round, as Theorem 2 reads the chain
    (∀ κ, w κ = ws) → 3 ≤ ws → (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- the schedule is the implementation's, one validator a round in rotation
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- the validators outside T are few enough for the synchronous wave
    ws * (n - T.card) < n →
    -- the chain starts at or past R, hops that many times, and decides at or below the horizon
    R ≤ x 0 → (∀ i, i < n - T.card → FloorHop w U V (x i) (x (i + 1))) →
    (∀ j, j ≤ x (n - T.card) →
      (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    -- then one of those landings is reliably led, so the chain reaches one within n − |T| hops
    ∃ i, i ≤ n - T.card ∧ S.leader (x i) ∈ T

/-- **SH-MM6i, the floor chain reaches a reliably led landing within `b` hops.** -/
def FloorChainReachesReliableWithinByzantine (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (x : ℕ → ℕ),
    -- the constant synchronous wave and one slot per round, as Theorem 2 reads the chain
    (∀ κ, w κ = ws) → 3 ≤ ws → (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- every validator outside T that is not Byzantine has crashed: it has no block from R on
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v) →
    -- the schedule is the implementation's, one validator a round in rotation
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- the validators outside T are few enough for the synchronous wave
    ws * (n - T.card) < n →
    -- the chain starts at or past R at a slot the view does not skip, hops once per Byzantine
    -- validator, and decides at or below the horizon
    R ≤ x 0 → ¬ Decided w U V (x 0) none →
    (∀ i, i < F.byzantine.card → FloorHop w U V (x i) (x (i + 1))) →
    (∀ j, j ≤ x F.byzantine.card →
      (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    -- then one of those landings is reliably led, so the chain reaches one within b hops
    ∃ i, i ≤ F.byzantine.card ∧ S.leader (x i) ∈ T

/-- **SH-MM6j, the floor chain decides within `(b + 1) · (ws + f)` rounds.** -/
def FloorChainDecidesWithinRounds (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (k : ℕ),
    -- the constant synchronous wave and one slot per round, as Theorem 2 reads the chain
    (∀ κ, w κ = ws) → 3 ≤ ws → (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- every validator outside T that is not Byzantine has crashed: it has no block from R on
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v) →
    -- the schedule is the implementation's, one validator a round in rotation
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- the validators outside T are few enough for the synchronous wave
    ws * (n - T.card) < n →
    -- the slot lies at or past R, the view does not skip it, and the horizon reaches
    -- (b + 1) · (ws + (n − |T|)) rounds above it
    R ≤ k → ¬ Decided w U V k none →
    k + (F.byzantine.card + 1) * (ws + (n - T.card)) ≤ N →
    -- then the slot is decided
    ∃ v, Decided w U V k v

/-- **SH-MM6m, a committed landing decides the chain's start.** -/
def FloorChainDecidesFromCommit (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (h : ℕ) (x : ℕ → ℕ),
    (∀ κ, 3 ≤ w κ) →
    -- one slot per round, as Theorem 2 reads the chain
    (∀ t, S.slotRound t = t) →
    -- the chain hops h times and its last landing is committed, whoever led it
    (∀ i, i < h → FloorHop w U V (x i) (x (i + 1))) →
    (∃ A, Decided w U V (x h) (some A)) →
    -- then the slot the chain started from is decided
    ∃ v, Decided w U V (x 0) v

/-- **SH-MM6n, the periodic round robin offers a reliable synchronous round.** -/
def PeriodicRoundRobinReliableSync : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (T : Finset (Fin n)),
    -- the coin's rounds are too few to hide every reliable residue
    0 < p → (n + p - 1) / p < T.card →
    -- past every round the schedule leads a synchronous round from T within n − 1 rounds
    ∀ r, ∃ a, r ≤ a ∧ a ≤ r + (n - 1) ∧ periodicKind p a ≠ 1 ∧
      (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T

/-- **SH-MM6o, the floor chain reaches a reliably led or committed landing at a period.** -/
def FloorChainReachesAtPeriod (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N ws wa p n : ℕ)
    (hn : 0 < n) (lead : Fin n → Validator) (x : ℕ → ℕ),
    3 ≤ ws → 3 ≤ wa → 0 < p →
    -- one slot per round, of the paper's periodic kind, led by the round robin at the rounds
    -- whose leader is known
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = periodicKind p t) →
    (∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    Function.Bijective lead →
    -- the validators outside T are few enough for the synchronous wave once the coin's rounds
    -- are deducted: at most `⌈n / p⌉` of every `n` rounds carry one, and the count that bounds
    -- the chain reads no leader at those
    ws * (n - T.card) + ws * ((n + p - 1) / p) < n →
    -- every asynchronous slot at or above the chain's start is decided, which is the coin's
    -- business (SH-MM7a) and not the schedule's
    (∀ t, x 0 ≤ t → S.kind t = 1 → ∃ v, Decided (wavelength ws wa) U V t v) →
    -- the chain starts at or past R at a slot the view does not skip, hops that many times, and
    -- decides at or below the horizon
    R ≤ x 0 → ¬ Decided (wavelength ws wa) U V (x 0) none →
    (∀ i, i < n - T.card → FloorHop (wavelength ws wa) U V (x i) (x (i + 1))) →
    (∀ j, j ≤ x (n - T.card) →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound j ≤ N) →
    -- then one of those landings is reliably led, or committed outright
    ∃ i, i ≤ n - T.card ∧
      (S.leader (x i) ∈ T ∨ ∃ A, Decided (wavelength ws wa) U V (x i) (some A))

/-- **SH-MM6p, the floor chain decides within `(b + 1) · (ws + W)` rounds at a period.** -/
def FloorChainDecidesWithinRoundsAtPeriod (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N ws wa p n W : ℕ)
    (hn : 0 < n) (lead : Fin n → Validator) (k : ℕ),
    3 ≤ ws → 3 ≤ wa → 0 < p →
    -- one slot per round, of the paper's periodic kind, led by the round robin where known
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = periodicKind p t) →
    (∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- every validator outside T that is not Byzantine has crashed: it has no block from R on
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v) →
    Function.Bijective lead →
    -- the count that bounds the chain, with the coin's rounds deducted
    ws * (n - T.card) + ws * ((n + p - 1) / p) < n →
    -- past every round the schedule leads a synchronous round from T within W rounds, which
    -- SH-MM6n supplies as `n − 1`; at a constant wave this is the `n − |T|` of SH-MM6g
    (∀ r, ∃ a, r ≤ a ∧ a ≤ r + W ∧ S.kind a = 0 ∧ S.leader a ∈ T) →
    -- every asynchronous slot at or above the slot is decided
    (∀ t, k ≤ t → S.kind t = 1 → ∃ v, Decided (wavelength ws wa) U V t v) →
    -- the slot lies at or past R, the view does not skip it, and the horizon reaches
    -- (b + 1) · (ws + W) rounds above it, plus the one asynchronous wave a decision round in
    -- that range may carry
    R ≤ k → ¬ Decided (wavelength ws wa) U V k none →
    k + (F.byzantine.card + 1) * (ws + W) + wa ≤ N →
    -- then the slot is decided
    ∃ v, Decided (wavelength ws wa) U V k v

/-- **SH-MM6k, a reliable leader commits under the reactive discipline.** -/
def CommitsOfReactivePace (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (N R k : ℕ)
    (waits : ℕ → Prop) (rs : ReactiveS U T N w waits),
    (∀ κ, 3 ≤ w κ) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the reactive schedule is past GST from R, where its timeout clears the delay
    rs.gst ≤ R → (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    -- the slot lies at or past R, its round carries the leader wait, a synchronous slot or a
    -- canary round, and its decision round lies within the schedule's horizon
    R ≤ S.slotRound k → waits (S.slotRound k) → S.slotRound k + (w (S.kind k) - 1) ≤ N →
    -- and the view holds that round
    V.CoversUpto (S.slotRound k + (w (S.kind k) - 1)) →
    -- then a reliably led slot commits its candidate in that view, by the direct rule
    S.leader k ∈ T → ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L)

/-- **SH-MM6l, a reliable leader commits under the timed discipline.** -/
def CommitsOfViewPace (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (N k : ℕ)
    (vp : ViewPace U T N),
    (∀ κ, 3 ≤ w κ) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the timeout grows at a rate that clears the delay, which is what the core's Q3 asks
    Rated vp.timeout →
    -- the slot lies at or past the round the rate names, and decides below the horizon N'
    ∀ N' : ℕ, max (2 * vp.delay + vp.proc) vp.gst ≤ S.slotRound k →
      (∀ r, max (2 * vp.delay + vp.proc) vp.gst ≤ r → r ≤ N' → PopulatedOn U T r) →
      (∀ j, j ≤ k →
        (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N') →
      V.CoversUpto N' → S.leader k ∈ T →
      ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L)

/-- **SH-MM7a, chain liveness.** -/
def ChainAllDecidedBelow (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (S' : Slots Validator) (V : View Validator BlockId Payload U) (c N : ℕ),
    1 ≤ wa →
    -- the schedule's rounds strictly increase, as the coin schedule's and every control
    -- schedule's do
    StrictMono S'.slotRound →
    -- the run form of the clause at that schedule: in every window of c slots below the
    -- horizon, wa consecutive slots whose leaders are committed candidates
    MahiMahi.UnpredictableRunWithin (S := S') U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every slot k whose window decides below the horizon ...
    ∀ k, MahiMahi.decisionRoundAt wa (S'.slotRound (k + c + wa - 1)) ≤ N →
      -- ... there is a slot b at or past k below which every verdict is settled
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, MahiMahi.Decided (S := S') wa U V i v

/-- **SH-MM7b, the chain under synchrony.** The run is named by the coin
alone, so the horizon cannot cap how far it reaches. -/
def ChainAllDecidedBelowOfSynchrony (wa : ℕ) : Prop :=
  ∀ (S' : Slots Validator) (T : Finset Validator),
    4 ≤ wa →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the schedule's rounds strictly increase, and past any slot it names T-leaders at wa
    -- consecutive slots
    StrictMono S'.slotRound → FairRunOn (S := S') T wa →
    -- then past any slot k and any round R there is a slot b ...
    ∀ (R k : ℕ), ∃ b, k ≤ b ∧ R ≤ S'.slotRound b ∧
      -- ... below which every verdict is settled, on any DAG T has synchronised from R and
      -- populated through the run's decision round
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → MahiMahi.decisionRoundAt wa (S'.slotRound (b + wa - 1)) ≤ N →
        ∀ i, i < b → ∃ v, MahiMahi.Decided (S := S') wa U V i v

/-- **SH-MM7c, one run settles the chain below it.** -/
def ChainAllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (b : ℕ),
    1 ≤ wa →
    -- wa consecutive rounds from b whose coins name committed candidates ...
    (∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i)) →
    -- ... in a view holding their decision rounds
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1)) →
    -- then every chain verdict below b is settled
    ∀ i, i < b →
        ∃ v, ChainDecided (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa) coin U V i v

/-- **SH-MM8, the stall.** -/
def Stall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (ws wa k : ℕ),
    -- a synchronous wave of at least two rounds, no longer than the period
    2 ≤ ws → ws ≤ k →
    -- one slot per round, of the kind the period assigns its round
    (∀ s, S.slotRound s = s) → (∀ s, S.kind s = periodicKind k s) →
    -- no synchronous candidate is ever certified ...
    (∀ (j : ℕ) (L : BlockId), S.kind j = 0 → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅) →
    -- ... and no synchronous slot is directly skipped in V
    (∀ j, S.kind j = 0 → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j) →
    -- then no slot at a round ≡ k − 1 (mod k) is ever decided in V
    ∀ i, i % k = k - 1 → ∀ v, ¬ Decided (wavelength ws wa) U V i v

/-- **SH-MM9a, the drain.** -/
def AllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (wa : ℕ) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (b : ℕ),
    -- every wave lies between one round and wa
    (∀ κ, 1 ≤ w κ) → (∀ κ, w κ ≤ wa) →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- wa consecutive slots from b are committed in V
    (∀ i, i < wa → ∃ L, Decided w U V (b + i) (some L)) →
    -- then every slot below b is decided in V
    ∀ i, i < b → ∃ v, Decided w U V i v

/-- **SH-MM9b, at period one every slot is decided.** -/
def AllDecidedBelowAtPeriodOne (U : BlockUniverse Validator BlockId Payload) (ws wa : ℕ) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (c N : ℕ),
    1 ≤ wa →
    -- one slot per round, every slot of the asynchronous kind, as period one has it
    (∀ s, S.slotRound s = s) → (∀ s, S.kind s = 1) →
    -- the run form of the clause at the output schedule: in every window of c slots below
    -- the horizon, wa consecutive slots whose leaders are committed candidates
    MahiMahi.UnpredictableRunWithin (S := S) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every round r whose window decides below the horizon ...
    ∀ r, MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N →
      -- ... there is a slot b at or past r below which every slot is decided at period 1
      ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, Decided (wavelength ws wa) U V i v

/-- **SH-MM9c, the cost of an asynchronous slot.** -/
def AsyncSlotCost (ws wa k : ℕ) : Prop :=
  -- one slot per round, of the kind the period assigns its round, the synchronous wave no longer
  -- than the asynchronous one
  (∀ s, S.slotRound s = s) → (∀ s, S.kind s = periodicKind k s) → 1 ≤ ws → ws ≤ wa →
  ∀ r, S.kind r = 1 →
    -- the asynchronous slot decides wa − ws rounds later than a synchronous slot there would ...
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound r =
      (steelheadAnchored Validator BlockId Payload (fun _ => ws)).decisionRound r + (wa - ws) ∧
    -- ... and the synchronous slot i rounds above it is decided at most max(0, wa − ws − i)
    -- rounds before it, so waits that long for it and no longer; the bound is nonincreasing in i
    ∀ i, 1 ≤ i → i < k →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound r ≤
        (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound (r + i) +
          (wa - ws - i)

/-- Liveness at a wavelength function, over every fault configuration,
schedule, block universe, wavelength function, wavelength pair and period
the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (ws wa k : ℕ),
    CommitsOfSynchrony U w ∧
      AllDecidedBelowOfSynchrony (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) w ∧
      SkipsCrashed U w ∧ CommitsOfDissemination U w ∧ DecidedOfReliableAboveFloor U w ∧
      FloorChainDecides U w ∧ RoundRobinFairRun ∧ FloorChainReachesReliable U w ∧
      FloorChainReachesReliableWithinByzantine U w ∧ FloorChainDecidesWithinRounds U w ∧
      FloorChainDecidesFromCommit U w ∧ PeriodicRoundRobinReliableSync ∧
      FloorChainReachesAtPeriod U ∧ FloorChainDecidesWithinRoundsAtPeriod U ∧
      CommitsOfReactivePace U w ∧ CommitsOfViewPace U w ∧
      ChainAllDecidedBelow U wa ∧
      ChainAllDecidedBelowOfSynchrony (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) wa ∧
      ChainAllDecidedBelowOfRun U wa ∧
      Stall U ∧ AllDecidedBelowOfRun U w wa ∧ AllDecidedBelowAtPeriodOne U ws wa ∧
      AsyncSlotCost (Validator := Validator) (BlockId := BlockId) (Payload := Payload) ws wa k

end Liveness

end MahiMahiPair

end Steelhead

end LeanDag
