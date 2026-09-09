# lean-dag — Composing adaptive leaders with adaptive counts: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** §2, §3, §4.3, §4.4 and §5's first item are
> built and on this branch; §4.1, §4.2, §4.5, §4.6 and §4.7 remain. The
> composition on branches `compose-barnacle-hammerhead` and
> `compose-cadence` is superseded, and retained only for the proofs §5
> names.

This document plans the composition of Barnacle (`docs/barnacle.md`),
which sets how many leaders a round has, with the adaptive leader
schedule (`docs/adaptive-leaders.md`), which sets who they are.

## 1. Two numberings, and the remedy taken

Barnacle sets how many leaders a round has. Under `Sched getLeader hk m`
slot `κ` is proposed at round `κ / m`, so a change of `m` at round `r`
renumbers every slot at and above `r`. Barnacle never changes the rounds:
round `r` is round `r` at every count.

The adaptive arc indexes both its epochs and its verdicts by slot
number, and `Policy.adapted` states its lag in that numbering. A
composition must therefore relate a configuration's numbering to the one
the policy reads. On `compose-barnacle-hammerhead` that relation is
`base`, `width`, `flat`, `flat_eq`, `base_eq`, `base_det`, `flat_det` and
`dvd_base`, with the restriction `OneEpoch` — every configuration is
exactly `W` slots — and its consequences `count_dvd`, `span_eq` and
`count_interval`. `OneEpoch` forces Barnacle's configuration length to
equal the policy's epoch length, so the two mechanisms cannot be tuned
independently.

Two remedies were available: give the composition one numbering, or
state the policy in coordinates a renumbering does not disturb. §2 and §3
take the first. The second — restating the adaptive arc in rounds — is
**not needed** and is not planned; §3.3 records what it would still be
worth, which is a question about meaning rather than about proof.

## 2. The band bounds the rounds it reads

`Banded` (`Properties/Band.lean`) transports a decided verdict to
another schedule. Its leader clause was already local to the band; its
round clause was not, so nothing related two schedules differing in
`slotRound` anywhere. The round clause now carries the same restriction.

No protocol owes anything new. `BandLaws` states each clause pointwise at
a slot, with the round correspondence as a hypothesis there; none reads a
global one. Four of the five protocols discharge `Banded` by delegation
in one line and are unchanged, and consumers are unchanged because a
weaker hypothesis on `S'` makes the property stronger. The work was
confined to `banded_aux`, the single generic transport.

`Properties.exists_roundLocal` is the consequence: every decided slot has
a round bound below which the schedule settles it, and any schedule
agreeing there, on the rounds as well as the leaders, decides it the same
way.

`Barnacle.sched_frame_local` is that read at Barnacle's schedule, and
states what the arc had been assuming. `PartialRun.closed` records a
configuration's verdicts as decided against
`Sched getLeader hk (count k)` — the uniform schedule at that count,
extended to every round — which is not the schedule that runs once the
count changes. The arc is sound because a configuration's verdicts are
settled within its own rounds; that is now a theorem.

## 3. One numbering: the frame

    structure Frame where
      width : ℕ → ℕ
      width_pos : ∀ r, 0 < width r

`Frame.cum r` is the slots below round `r`, `Frame.roundOf g` the round
index `g` falls in, `Frame.index r i` the index of position `i` of round
`r`, and `Frame.toSlots` the `Slots` a frame and an assignment make,
enumerating slots in round order. `constFrame m` is the constant frame,
and `Barnacle.Sched_eq_frame` says Barnacle's schedule at count `m` is
exactly that.

`Properties.DecidedFrameBelow R F a B V g v` says the schedule below
round `B` decides slot `g` and nothing above `B` changes that;
`decided_of_frame_agree` produces one from `Banded`.

### 3.1 Safety over a varying frame

`Integration.frameRun_agree` (`Integration/AdaptiveFrame.lean`). A `FrameRun` carries a
frame, an assignment by round and position, and verdicts by global slot
index. Two such runs over one universe and view have the same verdicts.

The whole of what the varying widths cost is one hypothesis:

    hwd : ∀ r, (∀ j, epochOf W j + 2 ≤ epochOf W (Rn.F.cum r) →
      Rn.vdct j = Rn'.vdct j) → Rn'.F.width r = Rn.F.width r

This is `Policy.adapted` read of the widths rather than the leaders: the
width of round `r` is a function of the verdicts of epochs at least two
behind the epoch `r`'s slots begin in. The induction needs it for the
same reason it needs `adapted` — deciding an epoch reads the schedule two
epochs ahead, and what it reads there must already be settled. At epoch
`e` the step reads the widths at every round below the one holding slot
`W * (e + 2)`.

### 3.2 What is not owed

No alignment between a width change and an epoch boundary. No
divisibility of a width into the epoch length. No `OneEpoch`. And no
change to the coordinates the policy reads: a frame has one numbering,
nothing is renumbered when a width changes, and the translation those
restrictions came from does not arise.

### 3.3 What round coordinates would still be worth

Under a frame an epoch is `W` slots and so spans a variable number of
rounds. Making it a fixed span of rounds is a statement about what an
epoch should mean — how far back a reputation window reaches in time
rather than in leader opportunities — and it is now separable from the
composition. It is not planned here.

## 4. What remains, and what is uncertain in it

In rough order of how much is unknown.

### 4.1 Barnacle must supply `hwd`, and cannot today

Barnacle sets the count of configuration `k + 1` from the anchor that
closes configuration `k`, and it takes effect at the next round: a lag of
zero epochs where `hwd` asks for two. **Barnacle must delay installing a
new count until two epochs after the anchor that computed it.** That is a
change to the control loop, not to the composition — the rule reacts
later — and it is the outstanding design decision.

Uncertain: which of `Barnacle/`'s 2986 lines survive the delay.
Agreement (BN3) is a determinism argument and a delay should not disturb
it. Progress and liveness (BN8, BN10, BN11) carry horizon arithmetic
keyed to `start_succ = anchor / count`, which the delay changes, and the
size of that is not assessed. The latency cost of the delay is also not
quantified.

### 4.2 Liveness over a frame is not attempted

`frameRun_agree` is safety alone. `Closes`, `extend`, `genesis` and
`every_height` exist only in the superseded `OneEpoch` shape. Removing
the alignment restrictions should make them easier rather than harder,
since the anchor is no longer required to arrive inside a fixed window,
but none of it is proved.

### 4.3 `FrameRun` and `PartialRun` are two run notions — settled

They are, and neither subsumes the other, by §4.4. `FrameRun` is not a
second run of the adaptive arc but the run of a mechanism that varies the
widths, so it lives in `Integration/AdaptiveFrame.lean`;
`Adaptive/Run.lean` keeps the general run over a fixed `Slots`.

### 4.4 A frame cannot represent every schedule — settled

`Frame` asks `0 < width r` at every round, so it cannot express a
schedule that skips rounds. `Slots.uniform p m` at period `p > 1` does
skip them, and the witnesses use it: `uniformSingle 3` in
`LeanDagTest/Mysticeti/Model.lean`, `Quantitative.lean` and
`Growth.lean`, `uniformSingle 2` in `LeanDagTest/Hybrid/Tight.lean`, and
`uniformSingle 3` in `LeanDagTest/Hydrozoan/LivenessHardening.lean`.

Admitting empty rounds was considered and rejected. `Frame.cum` is then
only monotone, and `frameRun_agree` needs it strictly monotone at exactly
the boundary: a run of empty rounds below the window's end leaves the
widths there to be settled by verdicts the induction is deciding.
Leaving them unconstrained is not available either, since a width at an
empty round shifts the numbering above it.

So `Frame` is the presentation of a schedule with a leader in every
round, which is what a width-varying mechanism produces, and `Slots`
remains the general notion.

### 4.5 Is `FrameRun.closed` satisfiable?

It asks `DecidedFrameBelow` at bound `F.roundOf (W * (epoch + 2))`.
`decided_of_frame_agree` supplies *some* bound; nothing yet says a
protocol's is small enough. `LeaderCommits` gives a verdict at slot bound
`κ + 1` and `Descends` at `b + c`, and both would have to be converted to
round bounds and the commit gap shown to fit inside two epochs. That is
the adaptive arc's standing assumption, so it should hold, but it is
unproved in this setting.

### 4.6 The bridge to Barnacle's numbering

`FrameRun` names no Barnacle. Connecting them means relating Barnacle's
per-configuration slot numbering to the frame's global one through
`Frame.index`. The facility exists; the bridge does not. The alternative,
restating Barnacle over the frame, is three times the size of restating
the adaptive arc and is not proposed.

### 4.7 The joiner and conservativity

`epochOf_add_of_dvd` states that a numbering starting at an aligned
offset agrees with the original about epochs, and `Adaptive/Joiner.lean`
uses it for a validator that joins mid-execution; under a frame the
offset is a slot offset into varying widths, and whether the lemma
survives is not assessed. `Policy.const_run_decided` anchors the
definitions and must still collapse correctly at the constant frame.

## 5. Carried over from the superseded branches

Proved, and to be reused rather than reproved:

* **Done.** `PickKeyed`, `Policy.keyed`, `slotsOfKeyed` — `Policy.inj`
  stated one leader per round, which the composition contradicts. Carried
  over across `Adaptive/{Basic,Policy,Run,Liveness,Growth,Joiner}.lean`,
  `Integration/Joiner.lean` and the witness.
* `config_det`, `anchor_det` — the configuration data and the anchor are
  functions of the verdicts below them.
* `extend`, `genesis`, `every_height` — the liveness shape, less the
  divisibility conditions, which came from `OneEpoch`.
* `Closes` — what a configuration owes on the schedule the composition
  computes for it, asked at the reassignment rather than the rotation.

Superseded, and not to be carried: `base`, `width`, `flat`, `flat_eq`,
`base_eq`, `base_det`, `width_det`, `flat_det`, `dvd_base`, `OneEpoch`,
`count_dvd`, `span_eq`, `count_interval`, `EpochAligned`,
`epochAligned_sum`, `rangeSlots`, `roundUp`, `dvd_roundUp`,
`le_roundUp`, `roundUp_lt`, `delay_lt`, `UpdDivides`, `mixLeader` and its
laws.

## 6. Labels

The AL labels of `docs/adaptive-leaders.md` are preserved where the
statement is preserved. Composition results are `I`-labelled, as in
`docs/integration.md`.

## 7. Order of work

1. **Done.** §2: the band's round clause, `exists_roundLocal`,
   `sched_frame_local`.
2. **Done.** §3: `Frame`, `decided_of_frame_agree`, `frameRun_agree`.
3. **Done.** §4.4 and §4.3: a frame gives every round a leader, and a
   frame's run lives in `Integration/`.
4. **Done.** §5's `keyed`, `slotsOfKeyed`, `PickKeyed`.
5. §4.1: the delayed Barnacle, and the measurement of what the delay
   costs the rest of the arc. This is the design decision, and it gates
   the rest.
6. §4.2 and §4.6: liveness over the frame, and the bridge to Barnacle's
   numbering. §4.5 and §4.7 are to be settled as they are met.
