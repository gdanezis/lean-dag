import LeanDag.Steelhead.Model.Chain
import LeanDag.Steelhead.Model.Reactive
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# Liveness at a wavelength function — statement

What the rule decides under synchrony, what the chain decides under the
unpredictable-leader clause, and what the output does *not* decide under
the paper's asynchronous adversary (`steelhead.md` §4–6). Seventeen
claims:

* **SH6a, a reliable leader commits under coverage** — Theorem 2's
  per-slot half: on a DAG a reliable quorum has synchronised and
  populated through the slot's decision round, a reliably led slot
  commits in every view caught up to that round, by the direct rule, at
  whichever wave the slot's round carries;
* **SH6b, everything below a fair run is decided** — the core's L10 at
  the wavelength function: past any slot the schedule offers a run of
  reliably led slots, and once the DAG is covered through the run's
  decision rounds every slot below the run is decided;
* **SH6c, a crashed leader is skipped** — Theorem 2's "crashed-led
  skips from `n − f` blames": a slot whose leader has no block at its
  round is directly skipped in every view holding its vote round, once a
  reliable quorum populates that round, at whichever wave the round
  carries;
* **SH6e, partial dissemination does not defer** — Theorem 2's remark:
  a candidate that one reliable block references one round up, the
  leader's only block at that round, is directly committed in every view
  holding its decision round, once the quorum is synchronised from that
  round and populates the wave. The leader need not be reliable: it may
  be Byzantine, so long as it did not equivocate;
* **SH6f, a reliable slot above the floor decides the slot** — Theorem
  2's Byzantine-led clause, as the anchor rule has it: under synchrony a
  slot is decided once every slot from its floor up to some reliably led
  slot is decided, whatever led them. The reliably led slot commits
  directly (SH6a), so the earliest commit at or above the floor is the
  anchor, and every slot between, decided but not committed, is a skip
  the search passes over. An undecided slot at the floor, one led by an
  equivocating Byzantine validator, is what the hypothesis excludes;
* **SH6g, the floor chain decides** — Theorem 2's chain of floors as a
  theorem: hop from a slot to the first slot at or above its floor that
  the view does not skip, and again from there; if the chain reaches a
  reliably led landing in `h` hops, the slot it started from is decided.
  Downward induction on the chain: the last landing commits (SH6a), and
  a landing whose own floor chain has committed is decided (SH6f's
  argument) and not skipped, so it commits too and anchors the landing
  below it. The hops are a hypothesis, so the claim is a round count
  rather than a count of Byzantine validators: what bounds the chain is
  SH6h;
* **SH6h, the round-robin schedule offers a reliable run** — what the
  implementation's known schedule gives, and what SH6b asks for: at
  `leader r = r mod n`, a validator outside `T` spoils at most `c` of
  the `n` windows of `c` consecutive rounds a cycle holds, so at
  `c · (n − |T|) < n` some window is wholly `T`-led, and the schedule
  repeats it past every round. At `c = 3` and `n = 3f + 1` every correct
  quorum qualifies, which discharges SH6b's fairness hypothesis at the
  constant wave three; at `c = wa` it does not, so the asynchronous
  rounds rest on the coin (SH7, SH14) and not on the schedule. The
  second half bounds the wait for one reliable leader by `n − |T|`
  rounds, which with SH6f is Theorem 2's Byzantine-led clause as a round
  count: the floor chain reaches a reliably led slot at most `w + b + c`
  rounds above the floor, where the paper counts `b` hops;
* **SH6i, the floor chain reaches a reliably led landing** — Theorem 2's
  hop count: at the round-robin schedule and the constant synchronous
  wave, if `ws · (n − |T|) < n` then one of the chain's first `n − |T|`
  landings is reliably led, which with SH6g decides the slot the chain
  started from within that many hops. Two landings at one residue would
  bound a whole number of cycles, each holding `|T|` reliably led rounds,
  and every one of those would have to fall in the `ws − 1` rounds a hop
  leaves free, since a reliably led round commits (SH6a) and a view
  decides a slot one way, so it is never one of the skips the hop passes
  over; counting the two against each other gives `n ≤ ws · (n − |T|)`.
  So the landings' residues are distinct and only `n − |T|` are left
  free;
* **SH6j, a reliable leader commits under the reactive discipline** —
  SH6a with the execution discipline named rather than assumed: a
  reactive schedule never waits past its timeout, and at the round above
  a reliable leader a block either votes or its builder waited the
  timeout out and votes for what it holds. At a wave of four rounds or
  more that is all it takes, the votes reaching the certifiers through
  the DAG; at the wave of three a certifier must reference the votes
  themselves, which is `ReactiveS`'s one added clause. `SynchronisedOn`
  appears nowhere: a reactive builder omits what has not arrived, so it
  is false by design in such an execution;
* **SH6k, a reliable leader commits under the timed discipline** — the
  other route to SH6a's hypothesis: a `ViewPace` whose timeout grows at
  a rate that clears the delay synchronises the reliable set from
  `max (2Δ + proc, gst)`, and SH6a takes it from there. The claim is
  worth exactly what the core's `ViewPace` is, which is a question about
  that structure and not about this arc;
* **SH7a, chain liveness** — MM3c at the chain schedule: a run of `wa`
  consecutive chain commits, which the clause promises in every window,
  decides every chain verdict below it;
* **SH7b, the chain under synchrony** — L10 at the chain schedule: past
  any round the coin names reliable leaders at `wa` consecutive rounds,
  and once the DAG is covered through that run's decision rounds every
  chain verdict below it is settled, with no clause;
* **SH7c, one run settles the chain below it** — the step SH7a takes
  once per round, on its own: `wa` consecutive rounds whose coins name
  committed candidates settle every chain verdict below the first, in
  any view holding their decision rounds. The form the coin's almost-sure
  half consumes (SH15), which asks for one run, not one in every window;
* **SH8, the stall** — at a period `k ≥ ws` and one slot per round, if
  no synchronous candidate is ever certified and no synchronous slot is
  directly skipped, then no slot at a round `≡ k − 1 (mod k)` is ever
  decided, in any view, whatever the asynchronous slots do. The paper's
  own adversary — the leader block delivered to exactly `f + 1`
  validators before the vote — produces these hypotheses at every
  synchronous slot, so the output stalls at every period `k ≥ ws`.
  This is the paper's "Why the chain, and not the output" as
  a theorem, for every period rather than the one it walks through
  (`steelhead.md` §4; the DAG is `LeanDagTest/Steelhead/Stall.lean`);
* **SH9, the drain** — Theorem 3 (ii): at any wavelength function
  bounded by `wa` and one slot per round, `wa` consecutive committed
  slots decide every slot below them, whatever wave those slots carry.
  Once the period is `1` and Mahi-Mahi's run clause supplies the run,
  the slots an earlier period left undecided are finished by it;
* **SH9b, at period one every slot is decided**: Theorem 3 (ii) as one
  statement. At `periodic ws wa 1`, under the run clause at the output
  schedule, past every round whose window decides below the horizon
  there is a slot below which every slot is decided, in any view caught
  up to the horizon, so the settled prefix and with it the ledger (SH13)
  extend as far as the horizon and the clause reach;
* **SH9c, the cost of an asynchronous slot**: the protocol section's
  healthy-network arithmetic. An asynchronous slot decides `wa − ws`
  rounds later than a synchronous slot would, and the synchronous slot
  `i` rounds above it is decided at most `max(0, wa − ws − i)` rounds
  before it, so the successor waits at most `wa − ws − 1` rounds for
  causal ordering and the wait is nonincreasing in `i`: delays never
  compound.

SH6a, SH6b, SH6f and SH6g assume `3 ≤ w r` everywhere, as the safety
claims do, and SH6f and SH6g one slot per round; SH6h reads no DAG at
all, only the schedule, and SH6i, which reads both, fixes the wave at
the constant `ws` the round-robin count needs; SH6c assumes nothing of the wave, and
SH6e `4 ≤ w r` at the slot's round, so that the vote round lies two
rounds up, where synchrony has carried the candidate. Neither asks the
quorum to be correct: SH6c reads blames, which need no vote, and SH6e
reads votes for a candidate its leader did not equivocate on. SH7a and SH7c
assume `1 ≤ wa`, as MM3c does, and SH7b `4 ≤ wa`, as MM5 does; SH8 assumes
`2 ≤ ws ≤ k` and nothing of `wa`; SH9 assumes `1 ≤ w r ≤ wa`; SH9b
assumes `1 ≤ wa`, as SH7a does; SH9c assumes `1 ≤ ws ≤ wa`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH6a, a reliable leader commits under coverage.** -/
def CommitsOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N k : ℕ),
    (∀ r, 3 ≤ w r) →
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
      MahiMahi.DirectCommitIn U V (w (S.slotRound k)) L (S.slotRound k) ∧ Decided w U V k (some L)

/-- **SH6b, everything below a fair run is decided.** The run is named by
the schedule alone, before any DAG is mentioned, so the horizon cannot
cap how far fairness reaches. -/
def AllDecidedBelowOfSynchrony (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (c : ℕ),
    (∀ r, 3 ≤ w r) →
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

/-- **SH6c, a crashed leader is skipped.** -/
def SkipsCrashed (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (k : ℕ),
    -- T is a quorum
    quorumCard Validator ≤ T.card →
    -- the leader has no block at the slot's round
    (∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k) →
    -- T populates the vote round, which the view holds
    PopulatedOn U T (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k)) →
    V.CoversUpto (MahiMahi.votingRound (w (S.slotRound k)) (S.slotRound k)) →
    -- then the slot is skipped in that view
    Decided w U V k none

/-- **SH6e, partial dissemination does not defer.** -/
def CommitsOfDissemination (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (k : ℕ) (L q : BlockId),
    4 ≤ w (S.slotRound k) →
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
      r ≤ MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k) → PopulatedOn U T r) →
    -- ... and the view holds the decision round
    V.CoversUpto (MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k)) →
    -- then the slot commits its candidate in that view
    Decided w U V k (some L)

/-- **SH6f, a reliable slot above the floor decides the slot.** -/
def DecidedOfReliableAboveFloor (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N k a : ℕ),
    (∀ r, 3 ≤ w r) →
    -- one slot per round
    (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R and populates every round from R to the horizon N
    SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the slot lies at or past R
    R ≤ k →
    -- slot a lies at or above k's floor and is reliably led
    k + w k ≤ a → S.leader a ∈ T →
    -- every slot from the floor up to a is decided in V
    (∀ j, k + w k ≤ j → j < a → ∃ v, Decided w U V j v) →
    -- every slot up to a decides at or below N, which the view holds
    (∀ j, j ≤ a → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
    V.CoversUpto N →
    -- then the slot is decided in V
    ∃ v, Decided w U V k v

/-- **SH6g, the floor chain decides.** -/
def FloorChainDecides (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N h : ℕ) (x : ℕ → ℕ),
    (∀ r, 3 ≤ w r) →
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

/-- **SH6h, the round-robin schedule offers a reliable run.** -/
def RoundRobinFairRun : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)),
    -- past every round the schedule leads c consecutive rounds from T, once the validators
    -- outside T, which spoil at most c windows each, cannot spoil all n windows of a cycle
    (∀ c, c * (n - T.card) < n →
      FairRunOn (S := Slots.identity fun r => (⟨r % n, Nat.mod_lt r hn⟩ : Fin n)) T c) ∧
    -- and at or above every round it leads one within n − |T| rounds
    (T.Nonempty → ∀ r, ∃ a, r ≤ a ∧ a ≤ r + (n - T.card) ∧
      (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T)

/-- **SH6i, the floor chain reaches a reliably led landing.** -/
def FloorChainReachesReliable (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (x : ℕ → ℕ),
    -- the constant synchronous wave and one slot per round, as Theorem 2 reads the chain
    (∀ r, w r = ws) → 3 ≤ ws → (∀ t, S.slotRound t = t) →
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

/-- **SH6j, a reliable leader commits under the reactive discipline.** -/
def CommitsOfReactivePace (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (N R k : ℕ)
    (rs : ReactiveS U T N w),
    (∀ r, 3 ≤ w r) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the reactive schedule is past GST from R, where its timeout clears the delay
    rs.gst ≤ R → (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    -- the slot lies at or past R, its decision round within the schedule's horizon
    R ≤ S.slotRound k → S.slotRound k + (w (S.slotRound k) - 1) ≤ N →
    -- and the view holds that round
    V.CoversUpto (S.slotRound k + (w (S.slotRound k) - 1)) →
    -- then a reliably led slot commits its candidate in that view, by the direct rule
    S.leader k ∈ T → ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L)

/-- **SH6k, a reliable leader commits under the timed discipline.** -/
def CommitsOfViewPace (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (N k : ℕ)
    (vp : ViewPace U T N),
    (∀ r, 3 ≤ w r) →
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

/-- **SH7a, chain liveness.** -/
def ChainAllDecidedBelow (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (c N : ℕ),
    1 ≤ wa →
    -- the run form of the clause at the chain schedule: in every window of c
    -- rounds below the horizon, wa consecutive rounds whose coin leaders are
    -- committed candidates
    MahiMahi.UnpredictableRunWithin (S := chainSlots coin) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every round r whose window decides below the horizon ...
    ∀ r, MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N →
      -- ... there is a round b at or past r below which every chain verdict is settled
      ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v

/-- **SH7b, the chain under synchrony.** The run is named by the coin
alone, so the horizon cannot cap how far it reaches. -/
def ChainAllDecidedBelowOfSynchrony (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (T : Finset Validator),
    4 ≤ wa →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- past any round the coin names T-leaders at wa consecutive rounds
    FairRunOn (S := chainSlots coin) T wa →
    -- then past any round k and any round R there is a round b ...
    ∀ (R k : ℕ), ∃ b, k ≤ b ∧ R ≤ b ∧
      -- ... below which every chain verdict is settled, on any DAG T has
      -- synchronised from R and populated through the run's decision round
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → MahiMahi.decisionRoundAt wa (b + wa - 1) ≤ N →
        ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v

/-- **SH7c, one run settles the chain below it.** -/
def ChainAllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (b : ℕ),
    1 ≤ wa →
    -- wa consecutive rounds from b whose coins name committed candidates ...
    (∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i)) →
    -- ... in a view holding their decision rounds
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1)) →
    -- then every chain verdict below b is settled
    ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v

/-- **SH8, the stall.** -/
def Stall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (ws wa k : ℕ),
    -- a synchronous wave of at least two rounds, no longer than the period
    2 ≤ ws → ws ≤ k →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- no synchronous candidate is ever certified ...
    (∀ (j : ℕ) (L : BlockId), ¬ IsAsync k j → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅) →
    -- ... and no synchronous slot is directly skipped in V
    (∀ j, ¬ IsAsync k j → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j) →
    -- then no slot at a round ≡ k − 1 (mod k) is ever decided in V
    ∀ i, i % k = k - 1 → ∀ v, ¬ Decided (periodic ws wa k) U V i v

/-- **SH9, the drain.** -/
def AllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload) (w : ℕ → ℕ) (wa : ℕ) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (b : ℕ),
    -- every wave lies between one round and wa
    (∀ r, 1 ≤ w r) → (∀ r, w r ≤ wa) →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- wa consecutive slots from b are committed in V
    (∀ i, i < wa → ∃ L, Decided w U V (b + i) (some L)) →
    -- then every slot below b is decided in V
    ∀ i, i < b → ∃ v, Decided w U V i v

/-- **SH9b, at period one every slot is decided.** -/
def AllDecidedBelowAtPeriodOne (U : BlockUniverse Validator BlockId Payload) (ws wa : ℕ) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (c N : ℕ),
    1 ≤ wa →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- the run form of the clause at the output schedule: in every window of c slots below
    -- the horizon, wa consecutive slots whose leaders are committed candidates
    MahiMahi.UnpredictableRunWithin (S := S) U wa c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every round r whose window decides below the horizon ...
    ∀ r, MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N →
      -- ... there is a slot b at or past r below which every slot is decided at period 1
      ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, Decided (periodic ws wa 1) U V i v

/-- **SH9c, the cost of an asynchronous slot.** -/
def AsyncSlotCost (ws wa k : ℕ) : Prop :=
  -- one slot per round, the synchronous wave no longer than the asynchronous one
  (∀ s, S.slotRound s = s) → 1 ≤ ws → ws ≤ wa →
  ∀ r, IsAsync k r →
    -- the asynchronous slot decides wa − ws rounds later than a synchronous slot there would ...
    (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound r =
      (steelheadAnchored Validator BlockId Payload (fun _ => ws)).decisionRound r + (wa - ws) ∧
    -- ... and the synchronous slot i rounds above it is decided at most max(0, wa − ws − i)
    -- rounds before it, so waits that long for it and no longer; the bound is nonincreasing in i
    ∀ i, 1 ≤ i → i < k →
      (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound r ≤
        (steelheadAnchored Validator BlockId Payload (periodic ws wa k)).decisionRound (r + i) +
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
      CommitsOfReactivePace U w ∧ CommitsOfViewPace U w ∧
      ChainAllDecidedBelow U wa ∧
      ChainAllDecidedBelowOfSynchrony (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) wa ∧
      ChainAllDecidedBelowOfRun U wa ∧
      Stall U ∧ AllDecidedBelowOfRun U w wa ∧ AllDecidedBelowAtPeriodOne U ws wa ∧
      AsyncSlotCost (Validator := Validator) (BlockId := BlockId) (Payload := Payload) ws wa k

end Liveness

end Steelhead

end LeanDag
