# An honest validator for the scheme

This document describes a Lean program that acts as an honest validator
of the partially synchronous rows of the scheme (`docs/scheme.md`), and
the proofs that it conforms to the scheme. The program lives in
`LeanDag/Node`, namespace LeanDag.Node. Names in backticks are existing
declarations.

## 1. Scope

The program is parametrised by a row `p : Params` and the quorum `q`. It
covers the six partially synchronous rows: Cordial Miners PS, Mysticeti,
Blue Bottle PS, Orcaella, Nemo-Nemo and Hybrid Mysticeti. The
asynchronous rows, the coin and `AsyncPace` are out of scope.

The program is the scheme's consensus core: it builds blocks, receives
them, fetches the histories it lacks, and decides. It keeps every block
it accepts, and restarts after a crash from the state it persisted
(§3.6). Garbage collection, checkpoints, bootstrap, rate limiting and
the exclusion of equivocators are not part of it; a version with all of
them is on branch `scheme-validator`. Liveness across crashes is planned
(§9).

Out of scope as well: stake weights, a mempool (the payload comes from a
configured source), execution, and an implementation of hashing and
signatures. Identifiers are the environment's hash, assumed injective
on the blocks of a run. Blocks are signed by their author, and the
proofs assume what the signatures give (authentication); the
executables check no signature and trust their inputs. Efficient
synchronisation is out of scope too: the program's fetch (§3.4) asks one
peer and is answered with whole histories, and the liveness claim
assumes of the network that a reliable node receives the history of
each reliable block it receives (§5.1).

## 2. Interface

The program is a pure, total transition function

> `step` : `Config` → `State` → `Input` → `State` × List `Output`

wrapped by two executables: one reading inputs and writing outputs as
JSON lines (`lake exe node`), and a simulator running `n` instances over
a seeded network (`lake exe sim`).

**Configuration** (`Config`). The row `p`, the bounds `f` (Byzantine)
and `c` (crash-prone), the quorum `q`, the validator's own identity, the
schedule (`per` rounds between slot rounds, `m` leaders a slot round,
`elect`), the timeout per round, the vote rule `σ`, the hash `idOf`,
and the payload source. A configuration is admissible (`Admissible`)
when the row is covered at the committee's size, `f` and `q`
(`Params.Covered`), its certificates fit the quorum
(`Params.CertFits`), its commit threshold is within `n − f − c`, and
`0 < q ≤ n`; all of it is decidable, and the program does not start
otherwise.

**Validity.** Every row uses `ValidAt q Clause.distinct`: references one
round below from `q` distinct authors, no author twice. It is decidable
(`ValidAt.decidable`) and mechanised (`ValidAt.mechanised`), and quorate
and distinct by `Validity.Quorate.of_validAt` and
`Validity.Distinct.of_validAt`. A reference to the author's own previous
block is the build rule (§3.2, §8), not a validity clause.

**State** (`State`). The accepted blocks (`store`), the blocks received
whose references are not all accepted (`pending`), the top round and
the node's own block there, the rounds whose timer fired, the next
undecided slot `lo`, the blocks asked for, each with the block whose
history needed it, and the decisions output, the latest first.

**Inputs** (`Input`): a start, which builds the genesis block; a
delivered block, with its identifier; a timer for round `r` that fired;
a request from a peer at round `r` for some blocks and their histories;
and a restart after a crash (§3.6).

**Outputs** (`Output`): persist one of its own blocks, before it is
broadcast; broadcast a block; set a timer for round `r`; commit slot `k`
with a decision `Option BlockId`; ask a peer for some blocks and their
histories, stating the node's top round; and send a block to one peer.

Time is discrete (`ℕ`).

## 3. The program

### 3.1 The store

The store is an ordered map from identifiers to blocks (Std.TreeMap),
with the accepted identifiers (`Store`). A received block whose
identifier is not `idOf` of its content, or which is the node's own, is
dropped, so that an identifier denotes one block. Otherwise it is
pending until its references are accepted, one round below it, and it
is valid at the row (`ready`), and is then accepted (`accept`, `flush`).
A Byzantine block that is never valid stays pending.

The accepted set is closed under references, every reference one round
below its referrer, so it is a `BlockRecord.View` (`Store.toRecord`,
`Store.view`); this is the view the decider reads. Byzantine twins are
accepted, since their votes count.

Beside the accepted identifiers `ids`, a `Finset`, the store keeps three
indexes, each a field with an invariant that ties it to `ids`:

* the map's keys are the accepted identifiers (`mem_map`), so that
  `j ∈ ids` is decided by a lookup in the map (`Store.has`, `has_iff`);
  the instances `Store.decMem` and `Store.decSubset` decide membership
  in `ids` and inclusion in `ids` this way, and the model's tests read
  `∈ ids` and `⊆ ids` unchanged;
* `topRound` is the highest round of an accepted block (`topRound_eq`:
  it equals `ids.sup` of the rounds);
* `byRound` maps each round to the accepted identifiers of that round;
  `Store.atRound st r` reads it, and equals `blocksAt st.toRecord r`
  (`atRound_eq`), and `Store.authorsAt st r`, the authors of those
  blocks, equals `authorsIn st.toRecord st.ids r` (`authorsAt_eq`).

`Store.insert` maintains the three: it adds the identifier to `ids` with
`Finset.cons`, which needs no membership test since the identifier is
new (`insert_ids` gives `ids` as `insert id ids`), takes the maximum of
`topRound` and the block's round, and adds the identifier to the
block's round in `byRound`. The builder reads `atRound` in `refsFor`
and `refsAt`, in its reach and certificate tests through
`leaderBlocks` (§3.2), and `authorsAt` for its quorum; the decider
reads `byRound` through the window (§3.3); the answer to a fetch reads
`atRound` in `coreSets`. The proofs read `blocksAt`, `authorsIn`
and `ids.sup` through these equalities.

### 3.2 The builder

The program builds round `r + 1` above its top `r` when its store holds
blocks of `q` distinct authors of round `r` and, for the slots whose
wave is in progress, either

* the block it would build reaches the slot's leader block, at each round
  from the one above the proposal to the vote round (`reachReady`), and
  certifies it at the decision round of a three-round row
  (`certReady`); or
* the timer for round `r` has fired.

Both tests read a slot's leader blocks off the round index:
`Store.leaderBlocks st k` is the set of blocks of `atRound` at the
slot's round whose author is the slot's leader, and it equals the
scheme's `candidatesIn` on the store's view (`leaderBlocks_eq`), which
the proofs read.

These are the clauses `advancesAt`, `reach_or_wait` and `cert_or_wait`
of the scheme's reactive run (`SchemeReactive`), written as a rule the
program runs, so the liveness argument's wait clauses hold by
construction (§5.3). The rule is reactive: the program builds as soon as
what the decider counts has arrived, and the timer is only the fallback
for a leader block, or for votes, that do not arrive.

The new block references one accepted block per round-`r` author: its
own block of round `r` for itself, and the least identifier between
twins otherwise (`refsFor`). Where these would wait, and a held
round-`r + 1` block of another author has references that would not, it
builds on those instead, with its own block for itself (`refsAt`,
`lent`), provided the block they make is valid (`buildable`). Without
this a Byzantine author could show one twin, through which the leader
block is reached, to the nodes ahead and the other to a node behind: the
node behind holds both once it receives the history of a block built on
the first, but the least identifier may be the second, and it then waits
its timer where its peers did not, by a timeout at each round the attack
repeats. The program builds rounds in sequence. It persists the block,
then broadcasts it, then sets the timer for round `r + 1`.

### 3.3 The decider

After each change to its state the program runs `tryDecide p σ W V lo N`,
where `lo` is its next undecided slot, `N` the last slot at a round its
store holds (`decidable`), as the scheme's TryDecide scans to the
highest round, `W` the store's window at the round `R` of slot `lo`
(`Store.window`) and `V` the view of all its blocks
(`Store.windowView`), and outputs the new decisions (`decideStep`).

The window holds the store's blocks at rounds `R` and above, gathered
from `byRound` at the rounds `R … topRound`. A block at round `R` is
read without its references, so that the window is closed under
references; a block above `R` is read as stored, and its references lie
one round below it, at `R` or above. The decisions on the window are
those on the store's view. Every set the loop counts from slot `lo` on
lies at or above `R`: the candidates at a slot's round, the blamers and
certificates above it, a vote's slot at it, a certificate's votes one
round below it, and a link's certificates, which the anchor reaches
through blocks above them; for a wave of two rounds or more, which an
admissible row has, the references of blocks at `R` are never read
(`ViewsAbove.tryDecide_eq`). At the bounded vote, a vote reads only the
voter's history down to the slot's round, so the store's view and the
window agree from `R` up (`ViewsAbove.window`), and the two give the
same decisions (`tryDecide_window`). The proofs rewrite the decision
step with this equality and reason about the store's view.

Over successive views this is `consumed`. A slot can be
skipped directly once its voting round holds `skipThreshold` blamers,
before its decision round.

### 3.4 Fetching missing blocks

A node accepts a block only once it holds the block's references. When
an equivocator sends one twin to some nodes and the other twin to the
rest, a node holding only one twin cannot complete the history of a
block referencing the other; the program fetches what it lacks.

**The rule.** After a block `h` arrives, the node walks `h`'s references
down through its pending blocks and collects those it neither stores
nor holds pending: the missing part of `h`'s history (`walkLevel`,
`missing`). It asks `h`'s author for them in one `fetch` output, which
carries the asker's top round `r` (`0` before the start), and records
each with `h`, so as to ask for a block at most once on account of each
block that needs it. A node asked for blocks sends the asker each one
its store holds, and their histories in its store less the blocks the
asker holds already (`answerIds`, `answer`). If `h`'s author is honest,
it accepted all of `h`'s history before building `h`, so it holds
everything asked for, and answers.

**The pruned answer.** Let `n` be the committee's size and
`T = n − q + f + 1` (`coreThreshold`). For `r ≥ 1` the answering node
sweeps its store from its round-`(r − 1)` blocks downwards and records,
for each block `i` it meets, a set of authors of round-`(r − 1)` blocks
that reach `i` (`coreSets`, `coreFrom`, `coreLevel`). The sweep starts
by giving each round-`(r − 1)` block its own author, passes the set of a
block to each of its references, and stops at a level whose blocks all
have sets of at least `T` authors. The histories are then walked in the
store with every reference to a block of `T` or more recorded authors
removed (`pruned`); for `r = 0` nothing is removed.

**Why the pruned answer is sound.** A node at top round `r ≥ 1` holds
round-`(r − 1)` blocks of at least `q` distinct authors, since it built
on them (`Quorate`). Let `i` be a block with a set `A` of `T` or more
recorded authors, and let at most `f` nodes be Byzantine. Then at least
`n − q + 1` authors in `A` are honest, so `A` and the asker's quorum
share an honest author `a`. An honest author has one block in round
`r − 1`, so the asker holds the round-`(r − 1)` block of `a` that
reaches `i` in the answering node's store; its store is closed under
references, so it holds `i` and the history of `i`. A block of the asked
history is therefore either sent or reached from a block the asker
holds. The sweep follows the store's references only, so the answering
node computes the sets once per request, from its own store.

**Why histories.** The walk sees a missing block only once the block
that references it has arrived. Asked for the missing blocks alone, a
history `d` levels deep arrives in `d` round trips. Answered with
histories, it arrives in one, whatever its depth.

**Why the author.** A fetch asked of every peer is answered `n − 1`
times. A Byzantine author that does not answer stalls nothing: a later
honest block needing the same blocks is asked of its own author.

**Why per referrer.** Asking for a block at most once lets a Byzantine
node stall an honest node `v`: it sends `v` a block referencing a block
`x` no one else has seen, so that `v` asks for `x` and nobody can
answer; then it reveals `x` to the others, who build on it; `v`, having
asked once, never asks again. The simulator's withholding attack
(`--withhold z,v,R`) does this; under the per-referrer rule `v` asks
again on account of the honest blocks and keeps pace.

### 3.5 Settling

A step that changes the state (the start, a delivery acted on, a timer)
ends by settling: the node builds, decides and flushes its pending
blocks in passes, until a pass changes none of its top, its pending
blocks and its next undecided slot (`settle`, `quiesce`). The passes are
bounded by the state (`passes`), and with `2 ≤ q` a settle ends settled
(`Settled`, `settle_settled`): nothing more can be built, no pending
block is ready, and nothing more can be decided. So none of the node's
moves that what it holds allows is left for a later event.

### 3.6 Restart and resending

The environment persists the state a step leaves, atomically, before any
of the step's outputs take effect. A crash loses the timers set and not
fired, the outputs of the last step that have not taken effect, and the
messages that arrive while the node is down; the state survives. On a
restart (`Input.restart`) the state is unchanged, and the node resends
(`resend`): it broadcasts its block at its top round, sets that round's
timer, and asks again for the missing history of each pending block
(`refetch`), since a request or its answer may have been lost. A block is persisted before it is broadcast, so
a restarted node never builds a second block at a round it built. A
decision whose output was lost is in the persisted `decided`.

When the timer of the node's top round fires and the node does not
build, it resends in the same way. Lost messages are not sent again
otherwise, and without this a crash can stall the reliable nodes. At `n = 4`, `f = 1`, `q = 3`, with node `3` silent, node `2`
crashes at round `t` before it receives the round-`t` blocks of nodes
`0` and `1`. They build round `t + 1` on its round-`t` block and wait
for its round-`t + 1` block, while node `2` restarts at round `t` without
a quorum. With resending, nodes `0` and `1` send their round-`t + 1`
blocks again each timeout; node `2` fetches their histories, builds
round `t + 1`, and the three go on. In `LeanDagTest/Node/Step.lean`,
with node `2` down from time `20`, nodes `0` and `1` stop at round `5`
after four decisions; with node `2` restarting at time `60`, after 400
inputs the three are at round `30` with 28 decisions each, alike.

Asking again matters as much as sending again. At Nemo-Nemo with
`n = 3`, `c = 1`, node `2` silent and node `0` down from time `150` to
`260`, node `0` held node `1`'s round-`16` block pending and had asked
for its missing round-`15` block; the answer arrived while it was down.
Node `1`, stalled at round `16`, sends that block again each timeout,
but node `0` drops a block it holds pending, so without `refetch` the
two waited for each other for good. The re-request is tied to the timer,
not to the repeated delivery: an answer to a request can itself carry
the asker's pending blocks, and asking again on each of them would loop.

A restarted node builds each round it missed, on lent references (§3.2)
or on its timer, so its own blocks still form a chain (§8). It needs no
bootstrap, since no block is collected.

## 4. Conformance

| | Claim | Proof |
|---|---|---|
| V1 | Over any input sequence: the node's own blocks, those it persists, are its own and identified by their hash; they lie at strictly increasing rounds; each references only blocks it knew, and is valid at the row under every block map agreeing with what it knew; it broadcasts each block it persists, and only blocks it persists; it keeps the decisions it outputs, which are slots `0 … lo − 1`. | `Node.Local.OneEach`, `Authored`, `Sends`, `ValidOut`, `Decisions` (proved, `Local/Proof.lean`) |
| V2 | **The decisions are the scheme's**: at the bounded vote, a decision step outputs what `Scheme.tryDecide` decides on any record and view holding the store's blocks, read alike; over successive views this is the scheme's loop. | `Node.Local.DecidesOnView` (proved): `Node.tryDecide_window`, `Node.ViewsAbove.window`, `Node.ViewsAbove.of_store`, `Node.ViewsAbove.tryDecide_eq` |
| V3 | **Safety**: over a trace with timely authentication of blocks, an injective hash and `Params.Tolerates`, the blocks the honest nodes knew form a `BlockRecord` at quorum `q` of which every honest store is a cut, and any two honest nodes' decisions are prefix-comparable. | `Node.Runs.Safety` (proved): `Node.globalRecord`, `Node.ground`, `Node.CommitInv.run`, `Scheme.Loop.resume`, `Scheme.Loop.prefixComparable` |
| V3′ | **Convergence**: over a trace with delivery, timely authentication and an injective hash, with at most `f` nodes outside the honest set, every block an honest node broadcast, with its history, ends in every honest node's store. The fault bound makes the pruned answer (§3.4) sound: a block left out of an answer is reached from a round-`(r − 1)` block of an honest author in the asker's quorum. | `Node.Converge.Converges` (proved): `Node.walk_reaches`, `Node.flush_no_ready`, `Node.Converge.chain`, `Node.Quorate.run`, `Node.mem_coreSets`, `Node.pruned_chain`, `Node.eq_of_persists` |
| V8 | The claims are about the program that runs: its store is the ordered map, its vote the bounded one, and compiled code departs from the definitions only by proved `@[csimp]` equalities; on the scheme's hand-built records its commits are those the scheme's tests record, and on random records its decided prefix is the least vote's, the scheme's loop's in its own order, and the same run a round at a time. | by construction: `historyUptoFrom_eq_levels` (`@[csimp]`), `boundedSel_sel_eq`; `check-arc-holes` forbids `implemented_by` and `extern`; tests `LeanDagTest/Node/Replay.lean`, `LeanDagTest/Node/Differential.lean` (§6) |
| V11 | **Liveness**: over a timed trace with delivery within `Δ` and synchronisation within `Δₛ` past GST, timers on time and timeouts above `2(Δ + Δₛ)`, the reliable nodes produce a round per timeout, and a run of reliably led slots past a round they built within `Δ + Δₛ` of each other is decided by all of them `Δ + Δₛ` after they reach its last decision round, and within a bound of the sum of the timeouts from that round. | `Node.Live.Progresses` (proved, §5): `Live.produces`, `Live.decides`, `Live.decidesBy` |

Every claim depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`; `LeanDagTest/Node/Axioms.lean`).

**Equivalence with the scheme.** V1, V2 and V11 together relate the
program to the scheme. The blocks it builds are valid at the row and
follow the scheme's build rule, its own block of the round below
referenced (V1, §3.2). The decisions it outputs are the scheme's decider
on its store's view (V2). A timed run of the program gives the scheme's
`WaveFacts`, the production, arrival and wait clauses the scheme's wave
argument reads, so the scheme's liveness argument applies to it (V11,
§5.3).

**The transfer.** The program decides on its own store, a record of its
own; the run's claims are about a view of the run's record. The decider
reads a view and the block map on it alone, so the two give the same
decisions when the store's identifiers are the view's and its block map
agrees on them (`ViewsAbove.of_store`, `ViewsAbove.tryDecide_eq`, for
the bounded vote, which reads only histories). The decision step runs
on the store's window, which decides as the store's view
(`tryDecide_window`, §3.3).

**Authentication.** A block delivered to an honest node in an honest
author's name was broadcast by that author earlier in the trace
(`Converge.TimelyAuthentic`); at the end of the trace this gives
`Node.Authentic` (`Node.authentic_of_timely`). The program broadcasts
exactly the blocks it persists (`Node.Local.Sends`), so such a block is
one of the author's own, one a round. A block a peer sends in answer to
a fetch is covered, since its author broadcast it.

**One run model.** Every claim about many nodes is stated over a trace
(`Model/Trace.lean`), which orders all nodes' inputs in one list. An
honest node changes state only by `step` on its own events. The network
and the adversary choose the events, so a Byzantine node's blocks enter
as delivered blocks, valid or not, since the program checks validity
itself. The reliable set `T` of the liveness claim is the honest
validators that do not crash.

**The run's record is a construction.** The proofs build the run's
record from what the honest nodes knew over the whole trace
(`knownAll`): every block delivered to them with its hash, and every
block of their own. A known block belongs to the record when its
references are known and belong to it, and it is valid at quorum `q`
(`Node.Real`, an inductive predicate); a Byzantine block whose
references never arrive does not. The record's block map is what the
honest nodes knew under each identifier (`content`), one block by the
injective hash, so the record is closed and valid by construction
(`Node.globalRecord`). It grounds what each honest node knows: a known
block valid over blocks of the record is the record's block
(`Node.ground`). Every honest store, at every event, is a cut of it,
its blocks the record's and read alike (`Node.IsCut`, `Node.cut_before`),
and every decision a node outputs is a verdict on a view of it
(`Node.Verdict`). No node computes the record; it exists to state the
claims.

Two hypotheses belong to the environment, not the program: the hash is
injective on the blocks of a trace, and the network meets the delivery
assumptions.

## 5. Liveness (V11)

### 5.1 Timed traces

A timed trace is a trace with a time for each event (`Model/Timed.lean`).
Read off it, for a node `v` and a time `t`: the events at or before `t`
(`eventsBy`), `v`'s state after them (`stateAt`), its top round
(`topAt`), the decisions it output by then (`decisionsBy`), and the
time at which `v` built its round-`n` block (`builtAt`). V11 makes these
assumptions up to a time `t₁`, over a reliable set `T ⊆ H` of at least
`q` and at least `n − f − c` nodes, with `2 ≤ q`:

* **times do not decrease** (`TimeMono`);
* **delivery** (`DeliveredWithin`): a message one reliable node sends
  another at time `t` arrives by `max t gst + Δ`;
* **timers** (`TimersOnTime`): a timer a reliable node sets at time `t`
  for `a` ticks fires at `t + a`, and none fires earlier;
* **synchronisation** (`SyncedWithin`): a reliable node that receives a
  reliable node's block at time `t` receives after it, by
  `max t gst + Δₛ`, every block the honest nodes know that the block
  reaches through blocks they know (`Live.knownBlock`) and that it did
  not make. This is assumed of the network, not proved of the program's
  fetch (§3.4), since efficient synchronisation is out of scope (§1);
  the fetch meets it with `Δₛ = 2Δ` when the block's author answers;
* every reliable node **starts** by GST (`StartedBy`);
* timely authentication of blocks, a block hash injective on every
  block, so no stored block has the identifier of the node's next one
  (`fresh_before`), and `2 (Δ + Δₛ) < timeout r` at every round.

A step takes no time; the time it costs a node to act on what it holds is
the catch-up bound below, not a processing constant.

### 5.2 What the run gives

Let `A = Δ + Δₛ`: a reliable block built at `s` past GST is delivered to
every reliable node by `max s gst + Δ`, and its history arrives `Δₛ`
later, so every other reliable node holds it by `max s gst + A`,
whatever round it is at (`arrival_of_delivered`, `Helpers/Arrive.lean`).
The argument below reads the run only through this arrival (`Arrival`),
through the timer of a node's top round firing within its timeout
(`TopTimerBy`), through timers set past GST firing (`TimersFireFrom`),
and through timers firing no earlier than set (`TimersAfterSet`); the
assumptions of §5.1 give all four at GST (`TopTimerBy.of_fire`,
`TimersFireFrom.of_fire`). The
claim has three parts.

* **Production** (`Produces`): past GST, once every reliable node is at
  round `n` or above at `s`, every reliable node is above `n` at
  `s + timeout n`. A reliable node still at round `n` then is settled
  (`settled_before`), the round's timer has fired and stays so
  (`fired_stays`), and it holds every reliable round-`n` block, so a
  quorum of round `n` (`round_arrives`), and no block with the
  identifier of its next one; so it builds (`tryBuild_isSome`), against
  its being settled.
* **Decision** (`Decides`): a node outputs a slot's decision only once
  every slot below it is decided, so the claim is about runs. Suppose
  the reliable nodes built a round `n₀` between `s ≥ gst` and `s + A`
  (the synchronisation point, §5.3), and slots `b … b + c − 1`, at or
  above `n₀`, are led by reliable nodes with `c` spanning the rule's
  eligibility (`SpansEligible c`). Once every reliable node is at the
  decision round of slot `b + c − 1`, at `t`, every reliable node has
  output by `t + A` the decisions of every slot below `b + c` (§5.4).
* **The time bound** (`DecidesBy`): from the synchronisation point the
  reliable nodes gain a round a timeout, so they have output those
  decisions by `s + A + Σ timeout r + A`, the sum over the rounds from
  `n₀` to below the decision round of slot `b + c − 1`.

### 5.3 Drift and the wave facts

The family's argument (`Scheme/Helpers/Reactive.lean`) reads, of a run,
production, arrival after a wait, and the wait clauses (`WaveFacts`);
`reaches`, `votes` and `certifies` read only these. The program meets
the wait clauses by its build rule (`reach_or_wait_node`,
`cert_or_wait_node`, `Helpers/Live.lean`), read over the run's record
from `reachReady` and `certReady` on the store's record and from the
timer.

**Drift.** Let `drift n` be the spread of the reliable nodes' build times
of round `n`. Past GST, `drift (n + 1) ≤ max (drift n) A`. Let `u` be
the first reliable node to build round `n + 1`, at `t`. By `t + A` every
reliable node `v` holds `u`'s block and its history, so a quorum of
round `n`. If `u` built on the reach and certificate tests, `v` passes
them with `u`'s references (`ready_transfer`), which it can build on
with its own block for its own (`lent_buildable`), and builds by
`t + A`. If `u` built on its timer, which fired at `u`'s build of round
`n` plus the timeout, `v`'s fires at most `drift n` later. So the drift
never grows past `A` once it is there (`catches_up`, `drift`,
`Helpers/Drift.lean`), and arrival follows: a node that waited the
timeout at round `n` holds every reliable round-`n` block, built at most
`A` after its own and held `A` after that, when `2A < timeout`
(`waited_holds`, `Helpers/Wave.lean`).

A node that fell behind before GST pays every timer round again, gaining
on its peers only a round time per round built on the tests, so its
drift shrinks at a rate no bound in `Δ` and the timeout controls. The
decision part therefore starts from a synchronisation point, and
production, which needs no drift bound, holds from GST.

### 5.4 From verdicts to the node's decisions

The family's results conclude `Decided` on a view holding every block up
to a round (`CoversUpto`), Byzantine blocks included, which a node's
store need not hold. A direct commit needs only the reliable
decision-round blocks (`decided_of_safe_of_holds`), and the prefix needs
only the run's (`decided_below_of_run`), so the node's view, which holds
every reliable block it has received (`reliable_held`), suffices. The
decision step reads the store as `tryDecide` on a view of the run's
record (V2), and `tryDecide` outputs every slot decided on its view once
its scan reaches far enough (`tryDecide_within`): a verdict derived
within a bound `B` is output by a scan reaching `B − 1`, and the node's
scan reaches every slot at a round its store holds (§3.3).

### 5.5 The timing check

The scheme's liveness structures are hypotheses, and their witnesses
hand-built records. Read against the program:

| Clause | Met by the program? |
|---|---|
| `SchemeReactive.advancesAt` | yes, once the round's timer fires: the timer stays fired, so a quorum arriving later builds at once |
| `SchemeReactive.reach_or_wait`, `cert_or_wait` | yes, by the build rule (§3.2) |
| `PaceCore.holds_mono` | yes: the store only grows (`Grows`) |
| `ReactiveCore.built_lt` | no: build times strictly increase, but one step may build several rounds at once, when a lagging node catches up; the node supplies `WaveFacts`, which does not ask it |
| `PaceCore.catchup` | no: a node holding a reliable block of a later round must build there within `proc`, while `reach_or_wait` makes it wait the timer at each round in between whose leader block its block would not reach; the drift argument (§5.3) replaces it |

## 6. Testing

1. **Agreement with the model** (`LeanDagTest/Node/Replay.lean`). A
   hand-built record of the scheme's tests goes through the program's
   store path (`flush`) into an empty store, and one decision step
   (`decideStep`) runs on it. Its commits are those the scheme's tests
   record for `tryDecide`: slots `0`, `1` and `2` of Mahi-Mahi's `full4`
   at the Mahi-Mahi row of wave four, and slots `0`, indirectly, and `1`
   of Mysticeti's `U7` at the Mysticeti row.
2. **Differential tests** (`LeanDagTest/Node/Differential.lean`). A
   seeded generator draws records of eight rounds over four validators,
   with an absent validator and an equivocator at random. On forty
   records at five configurations (Mysticeti, Mahi-Mahi at wave four,
   Cordial Miners and Bluestreak's partially synchronous row with one
   leader a round, and Mysticeti with two), four computations give one
   decided prefix: the program's decision step at the bounded vote; the
   same at the least vote, which searches the voter's whole history; the
   scheme's TryDecide in its own order, rounds from the top down; and
   the program as it runs, a decision step after each round arrives. In
   all 200 runs they agree, deciding 1,327 commits and 143 skips.
3. **The simulator** (`LeanDagSim/Net.lean`, `lake exe sim`). `n`
   programs over a seeded network: before GST a message takes up to
   `preMax` ticks, after it between `delayMin` and `delayMax`; nodes
   crash at given times and stay down, or are down for an outage, losing
   what is sent to them and the timers they set before, and restart
   (`Scenario.outages`, `--outage`); equivocators are two copies of
   the program with one identity and different payloads, each copy
   sending to half the nodes. It reports the rounds reached, the slots
   decided and skipped, whether two honest nodes that decide a slot
   decide it alike, whether their decisions are prefix-comparable, and
   whether every honest block above round `0` is valid under the blocks
   the nodes made. One scenario per row runs in the build
   (`LeanDagTest/Node/Sim.lean`). `lake exe node` runs one node over
   JSON lines.

   Outages (§3.6), swept over the six rows with three seeds each: one
   node down for 10 to 850 ticks, before, across and after GST; `f` (and
   `c`) nodes silent and one more down; every node down at once, or in a
   staggered way; more than `f` nodes down overlapping; and one node down
   three times. In all 234 runs agreement, prefix-comparability and
   validity hold, every node up ends five rounds or more above the top
   round at the last restart, the restarted node builds above that round,
   and an honest node decides again, within 43 ticks of the restart.
   The restarted node reaches the top round within 4 to 11 ticks after a
   350-tick outage at Blue Bottle and Orcaella, where it builds the rounds
   it missed on lent references (§3.2); where it waits timers instead,
   catch-up grows with the outage: at Mysticeti with `n = 4`, 155 missed
   rounds take about 335 ticks, a timeout at each round the restarted
   node's block reaches no leader block (§5.3). Catch-up is costly to
   compute: the restarted node asks for the missing history on account of
   every block it receives (§3.4), so a 250-tick outage at Orcaella with
   `n = 9` takes 197,365 inputs and 1,317 fetches, against 20,033 inputs
   without it. Three outage scenarios run in the build
   (`LeanDagTest/Node/Sim.lean`).

   An equivocator's copies each drop blocks that claim their identity,
   so neither copy accepts blocks built on its twin: it stops building
   and its pending blocks grow. From `byzUntil` on it therefore acts on
   nothing.
4. **Attacks** (`LeanDagTest/Node/Adversary.lean`, `--adv` and
   `--attacks` of `lake exe sim`). An attacker runs the honest program
   and also mounts attacks: `invalidBlocks` (with each block it
   broadcasts one without references, one referencing a block that does
   not exist, and one under an identifier that is not its hash),
   `forgedAuthor` (with each block it broadcasts one in the next node's
   name), and `twinSplit` (it shows each other node its own twin of each
   block). The network checks signatures (`Scenario.verify`): a block in
   an honest author's name must be one that author made, which is what
   the claims over traces assume (`TimelyAuthentic`). At the Mysticeti
   row with `n = 4`, every attack leaves agreement,
   prefix-comparability and validity intact. Under `twinSplit` every
   round waits for its timer. Without the checks, blocks forged in node
   `0`'s name are accepted by its peers, and their later blocks reference
   them; node `0` drops every block in its own name, so it never holds
   their histories and stays at round `2`, while agreement,
   prefix-comparability and validity still hold.

## 7. Tooling and cost

* The model's functions run under `#eval`. `historyUptoFrom` is
  computed a level at a time (`historyLevels`, proved equal and marked
  `@[csimp]` in `Common/Causality.lean`), which removes its exponential
  cost. The vote rule is `boundedSel`, the least vote searched only as
  deep as the slot, a `VoteSel` that selects what `leastSel` selects at
  every block of a record (`boundedSel_sel_eq`); for that the store's
  record carries `stored`, references one round below. The store's
  block map is an ordered map rather than a chain of updates.
* `scripts/check-arc-holes.py` forbids `partial`, `unsafe`,
  `implemented_by` and `extern` in the arcs it lists, `LeanDag/Node`
  among them, so compiled code departs from the definitions only by
  proved `@[csimp]` equalities; the executables' input loops, outside
  the library, run on fuel.
* The executables are `[[lean_exe]]` targets of `lakefile.toml`, not
  default targets, so `lake build` and the audits are unchanged.
* **Cost.** The store keeps every block. Membership in the accepted
  identifiers costs a lookup in the map, logarithmic in the number `N`
  of accepted blocks; the top round is read off a field; the blocks and the
  authors of a round cost a lookup in `byRound` and the size of the
  round. The scheme's functions (`Scheme.tryDecide`, `candidatesIn`,
  the votes) take any record and view, and read a round by filtering
  the record's identifiers. The builder's reach and certificate tests
  read the leader blocks off `byRound` (`leaderBlocks`), and the
  decider runs on the window at the round of the next undecided slot
  (§3.3), whose identifiers are gathered from `byRound`; the decider's
  scans therefore cost time in the number of blocks at and above that
  round, not in `N`. An answer to a fetch sends the history of each
  block asked for, less the blocks the asker holds. Four nodes at the
  Mysticeti row reach round 440 over 1,000 ticks, in 8,696 inputs and
  0.2 seconds, the largest store holding 1,761 blocks; over 2,000
  ticks they reach round 880 in 20,445 inputs and 1.8 seconds, the
  largest store holding 3,522; over 4,000 ticks round 1,755 in 37,525
  inputs and 2.5 seconds, the largest store holding 7,020. A profile of
  an 8,000-tick run (4.4 seconds) places about half of its time in
  answering fetches (`answerIds`) and about a fifth in the decider.

## 8. Self-parent as a build rule

The row's validity does not ask a block to reference a block by its own
author. No safety argument reads this. Liveness reads it once, for
inclusion (`SelfParent.reaches_of_creator`): a reliable author's
committed leader block reaches each earlier block of that author, by
walking the author's chain down. The shared layer's `SelfParent` takes
a reliability and a round `R₀`: every block by a reliable author above
`R₀` references a block by its author, and the chain walk and inclusion
(`mem_history_of_decided_commit`, `includes_of_leads`,
`committed_of_correct_block`, `Support.inclusion`, `Support.liveness`)
cover reliable blocks above `R₀`. The program meets it by its build
rule: it references its own block of the round below, and builds rounds
in sequence (§3.2), so a reliable node's chain is unbroken from its
genesis block.

## 9. Next: liveness across crashes

The restart and resending are in the program (§3.6), and V1, V2, V3,
V3′ and V11 hold over traces with restarts. V3′ and V11 assume every
message sent reaches its receiver, so they cover crashes that lose
timers but not messages. The decisions taken: a restarted node builds
every round it missed; it resends its top block on restart; liveness is
to hold for crashes before GST and for crashes and recoveries after it;
the state that only grows (`requested`, `pending`, `fired`) stays
unbounded.

**V11 with crashes.** A timed trace gives each node's down intervals;
delivery, timers and synchronisation are assumed only of a receiver that
stays up. Let `T` be at least `q` and at least `n − f − c` honest nodes,
each up from a time `t_r ≥ gst` on, and restarted after its last crash.
Then the conclusions of V11 hold with GST replaced by `t_r + X`, for `X`
a timeout of the top round plus `Δ + Δₛ` plus the timeouts of the rounds
the slowest node rebuilds: production resumes, and decisions follow from
a synchronisation point as in §5.2. Crashes before GST are the case
`t_r = gst`. The proof replaces the arrival lemmas (`block_arrives`,
`round_arrives`, `Helpers/Arrive.lean`), through which every use of
delivery and synchronisation passes, by their versions after `t_r + X`.

The phases left:

1. The timed model with down intervals, the arrival lemmas after
   recovery, and V11 with crashes.
2. The simulator: crash and recovery scenarios, among them the stall of
   §3.6 and its restart, and the catch-up time measured.
3. This document: §5 for crashes.
