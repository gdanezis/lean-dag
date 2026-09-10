# lean-dag — Composing adaptive leaders with adaptive counts: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** §2 to §5, §6.2, §6.3 and §6.4 are built or
> settled on this branch. §6.1 is built but for the joint fixpoint of
> §10's last item, which is what stands between `Progresses` as a
> hypothesis and `Progresses` as a theorem. The composition on branches
> `compose-barnacle-hammerhead` and `compose-cadence` is superseded, and
> retained only for the proofs §8 names.

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
take the first, and §4 is what Barnacle owes it. The second — restating
the adaptive arc in rounds — is
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

## 4. The gap: what Barnacle owes `hwd`

Barnacle set the count of configuration `k + 1` from the anchor that
closes configuration `k`, effective at the next round: a lag of zero
epochs where §3.1 asks for two. `Params` therefore gains a `gap`, the
rounds between an anchor and the count it computes taking effect, and

    start_succ : ∀ k, k < K → start (k + 1) = anchor k / count k + P.gap

`gap = 0` is Barnacle as it was, and is what the witnesses use, so this
generalises the arc rather than replacing it.

**Sizing.** At epoch length `W` the gap wanted is `2 * W` rounds. The
gap's rounds run at the old count, so they hold at least `gap` slots
whatever the count is, and a round-valued parameter therefore suffices —
it need not depend on the count.

**Cost to the arc.** About fifty lines across nine files. Agreement (BN3)
is untouched in substance: three bounds move from equalities to
inequalities and `omega` closes them, and it still depends on `propext`
and `Quot.sound` alone. Progress (BN8) carries the rest, because a
configuration's range now extends over the gap and the slots there must
be decided, so the horizon grows by the gap at each configuration:

    horizon P R c K = K * (P.interval + 1 + c + P.gap) + c + R.waveLength

with `ProgressStmt`'s bound and `everyHeight_bound`'s invariant
following. BN14 is restated in terms of the anchor's round rather than
`start (k + 1)`, which it happened to equal at `gap = 0`; its docstring
already read "two rounds below the anchor".

**Cost to a deployment.** Each configuration is `gap` rounds longer, so
the update rule reacts that much later. `W` small keeps `2 * W` small,
and the choice is a tuning question rather than a structural one.

## 5. Several leaders per round

`Policy.inj` stated that the base schedule places one leader per round,
and `Slots.keyed` then held whatever the policy did, because the rounds
separated the slots by themselves. A composition with a count-varying
mechanism contradicts that, so the clause the reassignment owes is now
explicit, as `Policy.keyed`, with `slotsOfKeyed` the induced schedule
under it and `PickKeyed` the same law at every count up to a bound.
Carried across `Adaptive/{Basic,Policy,Run,Liveness,Growth,Joiner}.lean`,
`Integration/Joiner.lean` and the witness.

## 6. What remains

### 6.1 Liveness over a frame

`Composed.genesis` is a composed run of height zero: one leader in every
round, nothing decided, no configuration closed, and the assignment the
policy's by definition. So `Composed` is inhabited outright and
`Composed.agree` is not a theorem about an empty family.

`Closes P F vdct start` is what a configuration owes: some slot at or
past the threshold commits, the threshold being the slot form of §6.2's.
`anchorOf` is the least such slot and `anchorOf_commits` and
`anchorOf_least` are `CompRun`'s two anchor clauses, so a closing
configuration names its anchor and nothing further is owed about it.

`Frame.extend` fixes the widths above a round, and
`Composed.reframe` is what makes that harmless: a run of height `K`
survives its frame being extended past `start K`. The horizon condition
is what does it — every slot the run speaks of lies in an epoch below
`H + 1`, hence below `W * (H + 1) ≤ F.cum (start K)`, hence at a round
below `start K`, where the frame does not move. `reframe`'s one new
obligation is `hkeyed`: the assignment must be lawful at the extended
count too, which is what a count-varying mechanism owes at every count it
can reach.

`Composed.extend` is progress: a run whose current configuration closes
extends by one. The frame is extended past the run's last start at the
count in force there, `reframe` carries the old configurations across it,
and the new configuration's clauses are the anchor `Closes` names. The
verdicts and the assignment are not extended at all — they are total
functions of which the shorter run said nothing above `F.cum (start K)`,
so the extension adds clauses rather than data.

`Progresses` is what the recursion consumes — a run that has reached its
horizon extends to one that has — and `Composed.every_height` iterates
it: from a run that has closed one configuration, a run of every height
exists that has. `Composed.extend` is how a protocol discharges
`Progresses`, since `extend`'s hypotheses are exactly what a
configuration owes.

`closes_of_leaderCommits` derives the first of `extend`'s clauses from
the protocol: a configuration closes when a reliable leader is scheduled
past its threshold. `LeaderCommits` is what the rule supplies and `Agree`
identifies that commit with the run's own verdict; the fairness consumed
is the existence of the slot, which is the reassignment's obligation and
not the rule's. `closed_of_settles` (§6.3) derives the third clause the
same way.

`Composed.toPartialRun` reads a composed run as an
`Adaptive.PartialRun` over its own schedule: the configuration data fixes
the frame, the frame and the assignment make a `Slots`, and what the
composed run says of its verdicts is what the arc's run asks. So the
arc's own results apply to it — `partialRun_agree` for the verdicts,
`partialRun_assign_agree` for the leaders, and the liveness of
`Adaptive/Liveness.lean` for its existence — rather than being restated.

`Properties.decidedBelow_of_decidedFrameBelow` is what that turns on. The
arc bounds a verdict by slot index and holds the round structure fixed; a
frame bounds it by round and lets the widths move above. The second is
the stronger clause, and this is the reading of it the arc consumes: a
schedule with the frame's rounds and agreeing leaders is the frame's own
schedule at a reassigned leader function.

`extend` takes the assignment and the verdicts of the run it builds
rather than carrying the shorter run's, which a run of height `K`
constrains nowhere above `F.cum (start K)`. So `coherent` is immediate —
define the assignment as the policy's reading of the verdicts at the new
frame and it is `rfl` — and `hag`, that the two assignments agree below,
follows from `adapted` once the verdicts do.

`extend`'s agreement clause now asks what the arc can supply.
`Adaptive.partialRun_agree` gives agreement on the epochs two runs have
both closed, so `hvd` reads `epochOf W g < H` rather than a bound in
slots — and `anchor_closed`, that a closed configuration's anchor is a
slot of a closed epoch, is what makes the three places `extend` reads a
verdict fall inside it. Without that clause a run could name an anchor
past everything it has decided, and nothing it says would settle that
anchor's verdict.

`vdct_agree_of_partialRun` discharges `hvd` from the arc: whatever
`Adaptive.exists_partialRun` produces already agrees with the shorter run
where `extend` reads it, so the next configuration's verdicts need no
reconciliation by hand. `anchor_decided` is the fact underneath
`anchor_closed` — the commit a configuration acts on is one the run has
settled, which it has to be, since the configuration reads that block to
compute the next count.

`Composed.step` is the whole of it: given an adaptive run over the
extended frame — what `Adaptive.exists_partialRun` produces — a composed
run of height `K` that has reached its horizon extends to one of height
`K + 1` that has. Nothing is reconciled across the boundary. The
agreement `extend` asks is `partialRun_agree`'s, `anchor_closed` puts the
anchors it consults inside that range, and the assignment it replaces
wholesale. `step` discharges `Progresses`, which `every_height` iterates.

**What is left is that the protocol decides the new configuration's
slots**, which is `Decided` at the composed schedule. The adaptive arc's
own construction supplies it, and applies here unchanged:
`Adaptive.descends_slotsOf` and `Adaptive.epoch_closes` are generic in
the round structure, and a frame's schedule is a `Slots` like any other.

The one thing a frame has to supply is the spanning clause — that the
last of `c` consecutive slots is eligible for everything below the first
— since at a frame `c` slots need not span any rounds at all.
`Frame.spansEligible_toSlots` supplies it from bounded widths, at
`c ≥ M * (wave + 1)`, and a count-varying mechanism bounds its widths by
its own bound on the count. `descends_frame` is the arc's descent read at
a frame, and it is `descends_slotsOf` applied, not restated.

`placesRuns_const_of_headsRun` connects the two arcs' fairness notions
where they meet. `HeadsRun` says Barnacle's rotation has a stretch of `c`
reliable leaders within `c₀` of every round; `PlacesRuns` asks for a
stretch of `c` reliable slots inside every epoch. At one leader per round
those are the same stretch, and the epoch has room for it as soon as
`c₀ ≤ W`. So the clause the adaptive arc prices is one Barnacle already
pays, and the composition is no less live than the schedule it starts
from.

Beyond one leader per round the two part company: `HeadsRun` gives a run
of consecutive *rotation indices*, and at count `m` a round's slots take
`m` consecutive indices while the next round restarts them, so a run of
slots crossing a round boundary is not a run of indices. Barnacle's own
`LiveOnOfHeads` is where that is handled at each count, and the composed
form of `PlacesRuns` above the base prefix remains an assumption — the
one liveness prices, and the one a reputation scheme owes.

### 6.2 The bridge to Barnacle's numbering — built

`Integration/BarnacleFrame.lean` crosses between the two indexings:
`cfgAt` and `frameOf` build the frame a Barnacle run induces, and
`frameOf_width_eq` is the crossing, a round of configuration `k` being
that configuration's count wide. `anchor_two_epochs_below` is what
`Params.gap` is for, and it settles §11's first entry: `Frame.cum_gap` says
`g` rounds hold at least `g` slots because every round holds one, and
`epochOf_add_two` says `2 * W` slots are two epochs, so the round-valued
parameter is the right shape and need not depend on the count.

`Integration/CompRun.lean` is the run of both mechanisms: Barnacle's
configuration data and a frame, with one numbering throughout — anchors
are global slot indices and `cnt_eq` is the bridge. `anchor_below` is
`anchor_two_epochs_below` at the run's own frame, `cnt_det` derives the
widths from the configurations, and `anchor_det` derives the anchor from
the verdicts.

The chain that discharges `hwd` is `config_det`: verdicts agreeing at the
anchors below a configuration give agreeing anchors (`anchor_det`), hence
agreeing starts (`start_succ_det`), hence agreeing counts, hence agreeing
widths (`cnt_agree_upto`). It is proved.

What unblocked it is the threshold. Barnacle states it as a round —
`start k + interval < anchor k / count k` — and reading a round of a slot
needs the widths below it, which is what would not have been available.
`Frame.cum_le_iff_le_roundOf` says a slot is at or past a round exactly
when it is at or past that round's first slot, so the same threshold is
`F.cum (start k + P.interval + 1) ≤ anchor k`: a *slot*, fixed by the
widths below the threshold rather than below the anchor. The two runs
therefore agree about it well inside both configurations, long before
they agree about where those configurations end. The reformulation is
equivalent, not weaker.

`width_det` is `hwd` at a run of both mechanisms, and it is proved. The
count of configuration `k` — which is what the width of its rounds is —
follows from `config_det`, since the anchor that set it is the anchor of
configuration `k - 1` and lies two epochs below by `anchor_below`. What
needed more is the other run's *extent*: reading its width through
`cnt_eq` asks `r ≤ Rn'.start (k + 1)`, which configuration `k`'s own
anchor settles, and that anchor is not two epochs below `r`. It is
refuted rather than proved: were the other run's configuration to end
before `r`, its anchor would lie two epochs below after all, so the two
anchors would agree and the two configurations would end together.

`frameRun_agree`'s `hwd` is correspondingly restricted to the rounds it
reads, `r < F.roundOf (W * (H + 1))`, which is what `width_det` supplies
and all the induction ever consulted.

`Composed` extends `CompRun` with the adaptive side — `asg`, `keyed`,
`coherent`, `closed` — and `toFrameRun` reads it as a `FrameRun`.
`Composed.agree` is then the composition's safety theorem: two composed
runs over one universe and view have the same verdicts. Barnacle's counts
and the policy's leaders are both functions of the verdicts, and
`Params.gap` is what puts the counts far enough back to be read where
they are needed.

Its one side condition is that the run reaches the horizon, and
`cover_of_horizon` states that in slots — the run's configurations hold
at least `W * (H + 1)` of them, which is what an epoch height `H` asks —
so `agree` is applied to a run that has gone far enough rather than to a
hypothesis about rounds.

### 6.3 What `FrameRun.closed` asks — named

`SettlesInTwoEpochs R W F a hk V` is that clause, named: every verdict
the schedule reaches is settled by it below the round at which the slot's
epoch-plus-two begins. `closed_of_settles` derives `FrameRun.closed` from
it and the rule's decisions.

`Banded` gives every verdict *some* round below which it is settled
(`decided_of_frame_agree`), so the clause is not unreachable; what it
adds is that the round is soon enough.

**At the slots a rule decides directly it is a theorem.**
`AnchoredRule.banded_direct` says a direct commit or a direct skip has a
band whose top is exactly the slot's round plus a wave — `banded_aux`
computes that top from the derivation, and a direct derivation reads the
slot's own wave and nothing above it. `decidedFrameBelow_direct` reads
that as a bound in rounds, so a schedule agreeing that far, its widths as
well as its leaders, decides the slot the same way. That is
`SettlesInTwoEpochs` at those slots, once the wave fits in the epoch
window.

What is not a theorem is the indirect case, where the band's top is the
anchor's and the anchor is existential in the derivation. `Decided` is an
opaque field, so nothing in `Properties/` bounds how far an indirect
derivation reaches; a rule that settles indirect verdicts within a wave
of the anchor would have to say so. This is the remaining content of the
assumption, and it is the same shape in the adaptive arc, which asserts
its bound of a run rather than proving it of every verdict.

### 6.4 The joiner and conservativity — settled

Neither is disturbed. `Adaptive/` names `Frame` nowhere: the frame is a
presentation used in `Integration/`, and the adaptive arc keeps its run
over a fixed `Slots` (§7). So `epochOf_add_of_dvd`,
`Adaptive/Joiner.lean`'s `joiner_run_decided_agree` and
`Policy.const_run_decided` stand unchanged, and each still depends on
`propext` and `Quot.sound` alone.

A joiner *of a composed run*, and conservativity of a composed run at the
unit frame, would be new results rather than repairs, and neither is
attempted.

### 6.5 What a composed run inherits from Barnacle

A composed run is not a `Barnacle.PartialRun` and cannot be one: that
structure's `closed` asks for decisions against `Sched getLeader`, the
rotation, and a composed run decides against the reassignment. So
Barnacle's theorems do not transfer by instantiation, and what the
composition needs of them is restated instead.

Most of it already was. `config_det` with `anchor_det` is BN3's content —
two runs agree on the configuration data and the anchors — and
`Composed.agree` supplies the verdicts BN3 also claims. `Composed.extend`
is BN8's. `count_le` and `cnt_le` are BN7's bound, and `cnt_le` is what
`Composed.descends` reads, so the bounded widths the descent needs now
come from the structure rather than from a hypothesis.
`anchor_isCandidate` is what BN14 turns on: the block a configuration
commits is a candidate of its anchor's slot, so it sits at the anchor's
round, and the delivery law places a good author's blocks below that
round in its history exactly as `Barnacle/Validity` has it.

What is not restated is the ledger — `Barnacle/Ledger`'s account of the
committed sequence — and the AIMD arc's own theorems about how the count
moves. Neither is consumed by safety or liveness of the composition.

### 6.6 Witnesses

`LeanDagTest.Barnacle.run1g` is `run1` at `P.gap = 1`: configuration `0`
still closes at the anchor of round `2`, but the count it sets takes
effect after round `3`, so the range runs a round further and that round
is decided too — by a direct skip, since `U7` commits nothing at it. A
gap of two does not fit on `U7`, which has no skip at round `4`; that
would want a taller universe.

`LeanDagTest.Barnacle.compGenesis` is `Composed.genesis` at Mysticeti's
rule, with the AIMD update and the arc's own leader function. The
composed structure is therefore inhabited at a rule this development has,
not only generically.

`LeanDagTest.Composition.cRun` is a composed run of height one over
`Ugrow`, whose height is a parameter: the fixed `Fin n` models run out of
rounds before a two-epoch window closes. Its frame holds one slot per
round, so slot `k` sits at round `k`; validator `1` leads every slot and
is correct. Configuration `0` closes at slot `2`, the least committed
slot at or past its threshold, and the next configuration begins at round
`10`. Epoch `0` is closed: each of its four slots is decided, by any
schedule agreeing with the run's below round `8`.

What makes the epoch closable is that `decided_of_correct_leader` is
stated over the ambient schedule rather than a fixed one, so it applies
at the frame's own `toSlots` and not only at the uniform schedule
`Ugrow`'s other theorems use. The candidate it produces is existential;
`leaderBlock_eq` pins it to `4 * r + 1`, which `Ugrow`'s layout forces.

`cRun_horizon` is what `Composed.every_height` consumes, so the run is a
base case for the recursion and not only an inhabitant.

`mRun` closes two configurations and five epochs, at `W = 2` and a gap of
four. Configuration `0` runs at one leader a round and closes at slot
`2`; configuration `1` runs at two, closes at slot `9`, and sets the
width from round `7` on. Epochs `0` to `4` are all closed, and epoch `3`
straddles the change: slot `6` is the only slot of round `6`, slot `7`
the first of two at round `7`, and both slots of round `7` are decided,
under validators `1` and `2`.

Two things make `mRun` short. Its verdicts are read off the frame —
`vdctOf` names the block `Ugrow` puts at a slot's round under that slot's
leader — and its policy hands back the frame's own leader, so `coherent`
holds wherever the frame does and `closed` reduces to
`decidedFrameBelow_of_asg` at every slot. What is left to check by cases
is only which round each slot of a closed epoch sits at, which is
`mF_bound`.

`mRun_extends` turns the recursion: `mRun` has closed two configurations
and reached its horizon, so `Composed.extend` gives a run of height three
over eleven epochs that has reached its own. Its third configuration
closes at slot `21`, at round `14`, and `horizon_ext` is the clause that
makes it a base for the next turn. This is the first application of
`extend` to a run rather than to a hypothesis.

The extended frame adds no width here — `mRun`'s last configuration
already runs at two leaders a round, so `mFe` has `mF`'s widths at every
round — and `mFe_width`, `mFe_cum` and `mFe_roundOf` are what carry the
frame's arithmetic across `Frame.extend`.

Two general facts remove the case analysis both runs would otherwise
need. `roundOf_lt_of_width_le` says a round holding at most `m` slots
cannot hold both `g` and `g + m + 1`, so a slot of a closed epoch lies
below the round its window ends at whatever the frame; `frame_roundOf_le`
bounds a round by its own first slot, which is what puts the certificate
rounds under the universe's height.

`Progresses` itself is still not discharged: it quantifies over every
run, and `extend`'s hypotheses at an arbitrary run are the two
assumptions of §6.1 and §6.3. What `mRun_extends` settles is that those
hypotheses are satisfiable together, at a rule this development has.

### 6.7 Liveness of the composition

`Composed.commits` is `Adaptive.Run.commits` at a composed run: a slot
led by a reliable validator commits, because the rule supplies the commit
and `Agree` identifies it with the run's own verdict, which the run has
because the slot lies in an epoch it has closed.

`Composed.commits_in_epoch` is the composition's liveness. Every epoch a
composed run has closed carries `c` consecutive commits, and the clause
it prices is the arc's own — `Adaptive.PlacesRuns` at a policy whose
leaders the run's are, related by `sched_leader_eq`, which reads
`coherent` at a slot rather than at a round and a position. Nothing about
the count enters: a configuration may change the width anywhere in the
epoch, since the verdict is read at the run's own schedule whatever the
widths do.

`mPol` is that policy for `mRun` — the composed schedule read back as a
reassignment rule — and `mPol_placesRuns` holds on the data, every slot
of `mRun` being led by validator `1` or `2` and both correct.
`mRun_commits_in_epoch` is the theorem applied: every epoch `mRun` has
closed carries two consecutive commits, with the rule's agreement and
leader-commits law discharged at Mysticeti's own. What is left as a
hypothesis is `certLive`, the rule's liveness precondition, which every
other liveness result in this development takes and which is not the
composition's to supply.

## 7. Questions settled, and how

**A frame gives every round a leader.** Admitting empty rounds was
considered and rejected: `Frame.cum` is then only monotone, and
`frameRun_agree` needs it strictly monotone at exactly the boundary,
where a run of empty rounds below the window's end would leave the widths
there to be settled by verdicts the induction is deciding. Leaving them
unconstrained is not available either, since a width at an empty round
shifts the numbering above it.

So a frame does not present a schedule that skips rounds, and
`Slots.uniform p m` at period `p > 1` does — the witnesses use it:
`uniformSingle 3` in `LeanDagTest/Mysticeti/{Model,Quantitative,Growth}`,
`uniformSingle 2` in `LeanDagTest/Hybrid/Tight.lean`, and
`uniformSingle 3` in `LeanDagTest/Hydrozoan/LivenessHardening.lean`.
`Slots` remains the general notion.

**`FrameRun` and `PartialRun` are two run notions, and neither subsumes
the other**, by the paragraph above. `FrameRun` is not a second run of
the adaptive arc but the run of a mechanism that varies the widths, so it
lives in `Integration/AdaptiveFrame.lean`; `Adaptive/Run.lean` keeps the
general run over a fixed `Slots`.

## 8. Carried over from the superseded branches

Reused rather than reproved:

* **Done.** `PickKeyed`, `Policy.keyed`, `slotsOfKeyed` — §5.
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

## 9. Labels

The AL labels of `docs/adaptive-leaders.md` are preserved where the
statement is preserved. Composition results are `I`-labelled, as in
`docs/integration.md`.

## 10. Order of work

1. **Done.** §2: the band's round clause, `exists_roundLocal`,
   `sched_frame_local`.
2. **Done.** §3: `Frame`, `decided_of_frame_agree`, `frameRun_agree`.
3. **Done.** §7's two questions.
4. **Done.** §5: `keyed`, `slotsOfKeyed`, `PickKeyed`.
5. **Done.** §4: `Params.gap`, and the arc's absorption of it.
6. **Done.** §6.2: the bridge, `Params.gap` discharging `hwd`, and
   `Composed.agree`.
7. **Done.** §6.3 and §6.4, and §6.1 but for its last item:
   `Composed.genesis`, `extend`, `every_height`, `closes_of_leaderCommits`
   and `closed_of_settles`.
8. **Done.** `extend` takes the assignment and the verdicts of the run it
   builds, rather than carrying the shorter run's. A run of height `K`
   constrains neither above `F.cum (start K)`, so each step chooses them
   afresh for its own frame, and the recursion is local. What was going to
   be a joint fixpoint is not one.

## 11. What could still go wrong

**Settled.** §4's sizing argument was prose and is now
`Frame.cum_gap` with `epochOf_add_two`; the gap is round-valued and does
not depend on the count.

**The assembly inside a configuration may want more than a lag.** §6.2's
open step compares two runs' anchors while their configurations' extents
are still unknown. If neither route there works, the structure would have
to fix a configuration's extent independently of its anchor, which is a
restriction of the kind §3.2 records the composition as not needing.

**Liveness may ask what safety did not.** §3.2 records that safety needs
no alignment between a width change and an epoch boundary. `Closes` asks
a configuration to decide its own range, and whether that range interacts
with the epoch grid is not established; §6.1 and §6.3 are where it would
appear.
