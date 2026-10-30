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
them, syncs the histories it lacks, and decides. It keeps every block
it accepts, and restarts after a crash from the state it persisted
(§3.6). It convicts an author whose twins it accepts, or whom evidence in
a block it accepts names; it then takes no announcement from the author
and answers none of its requests, and its blocks reference no author they
expose (§3.4). Once every honest block of a round exposes the authors it
convicted, its disk holds at most `n + |D|` blocks of each later round
(V13). Garbage collection, checkpoints, bootstrap and rate
limiting are not part of it. Liveness holds across crashes (§5.6).

Out of scope as well: stake weights, a mempool (the payload comes from a
configured source), execution, and an implementation of hashing and
signatures. Identifiers are the environment's hash, assumed injective
on the blocks of a run. Blocks are signed by their author, and the
proofs assume what the signatures give (authentication); the
executables check no signature and trust their inputs. The links are
authenticated: an input from a peer names the peer. Synchronisation
follows the Sync model (`docs/sync.md`): one sync for each peer, which
asks the peer for a block's history above the node's frontier and takes
the part of the answer in that history in only if the block is then
held (§3.4). The program proves that the syncs
complete (V3′), not how fast; the liveness claim assumes of the network
and the syncs together that a reliable block given to a reliable node is
on its disk within `Δₛ` past GST (§5.1).

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
what payloads say of equivocation (`xp`: the evidence a payload carries,
each an author with two of its blocks, and the authors its block
exposes), and the payload source, which takes the evidence to carry and
the authors to expose. The source is faithful (`Faithful`) when a payload
reads back what was put in; the liveness claims assume it. A configuration is admissible (`Admissible`)
when the row is covered at the committee's size, `f` and `q`
(`Params.Covered`), its certificates fit the quorum
(`Params.CertFits`), its commit threshold is within `n − f − c`, and
`0 < q ≤ n`; all of it is decidable, and the program does not start
otherwise.

**Validity.** Every row uses `rowValid q E`: references one round below
from `q` distinct authors, no author twice, and the exposure clause
(`Clause.exposes`): the block exposes the authors its evidence names and
those its references expose, and references none of them. The clause
reads only the references, as the quorum does, so the node checks it in
memory as on disk. The record of the run (§4) is at `ValidAt q
Clause.none`, which the scheme's results read. A reference to the author's own previous
block is the build rule (§3.2, §8), not a validity clause.

**State** (`State`). The accepted blocks, on disk (`disk`), and those
from a round `floor` up in memory (`memory`, `floor`), with the proof
that the memory is the disk's window there (`mirrors`, §3.1); the syncs,
at most one for each peer, each with the peer, its block the node lacks
and the identifiers asked for by name (`syncs`, §3.4); the evidence the
node holds (`evidence`) and the authors it convicted (`detected`); the top
round and
the node's own block there, the rounds whose timer fired, the next
undecided slot `lo`, the decisions output, the latest first, and the
round whose timer is set (`armed`). A timer drops the fired rounds below
the top, which the node no longer reads (`fire`).

**Inputs** (`Input`): a start, which builds the genesis block; a block a
peer announced, with its identifier (`deliver`); a stream piece from a
peer (`stream`); a timer for round `r` that fired; a request from a peer
for the history of a block, with the peer's frontier and the identifiers
it asks for by name (`syncRequest`); a request from a peer for the node's
block of a round (`ask`); and a restart after a crash (§3.6).

**Outputs** (`Output`): persist one of its own blocks, before it is
broadcast; broadcast a block; set a timer for round `r`; commit slot `k`
with a decision `Option BlockId`; a request to a peer for the history of
a block, with the node's frontier and the identifiers it asks for by
name (`sync`); a stream piece to a peer (`stream`); a request to every
peer for its block of a round (`ask`); and one of the node's own blocks to
one peer (`send`).

Time is discrete (`ℕ`).

## 3. The program

### 3.1 The disk and the memory

A store is an ordered map from identifiers to blocks (Std.TreeMap),
with the accepted identifiers (`Store`). The node keeps two. The disk
(`State.disk`) holds every block it accepted, and is what it answers
requests from (§3.4) and resends from (§3.6). The memory
(`State.memory`) holds the disk's blocks at rounds `floor` and above,
those at `floor` without their references (`Store.Mirrors`), and is
what it builds, decides and arms its timers on (§3.2, §3.3). A received
block whose identifier is not `idOf` of its content, which is the
node's own, or which is on disk, is dropped, so that an identifier
denotes one block. A block is accepted once its references are
accepted, one round below it, and it is valid at the row (`ready`,
`accept`); one that is not is synced (§3.4) or dropped. Accepting a
block keeps the evidence it gives and convicts the authors it names
(§3.4).

Each store is closed under references, every reference one round below
its referrer, so it is a `BlockRecord.View` (`Store.toRecord`,
`Store.view`). Byzantine twins are accepted, since their votes count.

**Keeping a block.** An accepted block goes to the disk and, if its round
is `floor` or above, to the memory, without its references at `floor`
(`keep`, `Store.put`, `Mirrors.put`). A block is checked in memory when
its round is above `floor`, since its references then lie at `floor` or
above, and on disk otherwise; the two checks agree (`Store.pick`,
`Mirrors.checks_pick`), so the node accepts what a node reading its disk
alone would accept (`ready_eq`, `accept_disk`, `absorb_disk`,
`flushSyncs_eq`), and the proofs read the disk alone (`readyOn`,
`acceptOn`). The test that a block is new reads the disk's
identifiers.

**Releasing memory.** The node reads its memory at the round of its
next undecided slot and up (§3.3), and from `voteOffset` below its top
up (§3.2). This round is `floorOf`. When it builds or decides a slot, it
releases the memory below `floorOf` (`release`, `Store.above`,
`Mirrors.above`); a pass that builds and decides nothing releases
nothing. The floor never passes `floorOf`, since the next undecided slot
and the top only rise (`Inv.floor`). The memory therefore holds the
blocks from the lower of the round of the next undecided slot and
`voteOffset` below the top, up to the highest round the disk holds.

**Reading memory as the disk.** From `floor` up the memory holds the
disk's blocks at each round, with their rounds and authors, and their
references above `floor` (`Mirrors.atRound_eq`, `Mirrors.authorsAt_eq`,
`Mirrors.refs`). The builder's reads, at its top `r` with `floor` at
most `r − voteOffset`, are therefore those on the disk
(`Mirrors.build_reads`, at the bounded vote, where a vote reads only the
voter's history down to the slot's round), and the decisions on the
memory's window are those on the disk's view (`tryDecide_memory`). The
proofs rewrite the node's reads with these equalities and reason about
the disk. After a restart the memory is the disk's window at `floor`,
which the disk and `floor` determine.

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
block's round in `byRound`. `Store.above` keeps them for the blocks it
keeps. The builder reads the memory's `atRound` in `refsFor` and
`refsAt`, in its reach and certificate tests through `leaderBlocks`
(§3.2), and `authorsAt` for its quorum; the decider reads the memory's
`byRound` through the window (§3.3); the frontier of a request reads the
disk's `authorsAt` from round `0` up (`gapOf`). The proofs read
`blocksAt`, `authorsIn` and `ids.sup` through these equalities.

### 3.2 The builder

The program builds round `r + 1` above its top `r` when its memory holds
blocks of `q` distinct authors of round `r` and, for the slots whose
wave is in progress, either

* the block it would build reaches the slot's leader block, at each round
  from the one above the proposal to the vote round (`reachReady`), and
  certifies it at the decision round of a three-round row
  (`certReady`); or
* the timer for round `r` has fired; or
* the memory holds round-`r + 1` blocks of `f + 1` authors (`behind`):
  at most `f` of them are Byzantine, so an honest node built the round,
  and a node behind builds it without waiting. With a valid block of a
  round in hand, whose history holds `q` authors of each round below, a
  node thus builds every round below it at once. The liveness argument
  traces that honest author's block back to a timer armed with a quorum
  of the round, or to the tests (§5.3).

Both tests read a slot's leader blocks off the round index:
`Store.leaderBlocks st k` is the set of blocks of `atRound` at the
slot's round whose author is the slot's leader, and it equals the
scheme's `candidatesIn` on the store's view (`leaderBlocks_eq`), which
the proofs read.

The first two are the clauses `advancesAt`, `reach_or_wait` and
`cert_or_wait` of the scheme's reactive run (`SchemeReactive`), written
as a rule the program runs; the third is a form of its catch-up rule
(`PaceCore.catchup`). A single block of round `r + 1` would not do: a
Byzantine node can build one on `q` round-`r` blocks without the
leader's, as soon as they exist, and prompt correct nodes to build round
`r + 1` before the leader's block arrives, so that it gets no votes. The rule is reactive: the program builds as soon as
what the decider counts has arrived, and the timer is only the fallback
for a leader block, or for votes, that do not arrive.

The new block references one accepted block per round-`r` author it does
not leave out: its own block of round `r` for itself, and the least
identifier between twins otherwise (`refsFor`). It leaves out the
authors its evidence names and those a round-`r` block it holds exposes
(`excluded`), so its block names no author it exposes (§3.4). Its
payload carries the node's evidence against the authors it does not
reference, and the authors it then exposes: those that evidence names and
those its references expose (`payloadFor`). Where these references would
wait, and a held round-`r + 1` block of another author has references that
would not, it builds on those instead (`refsAt`, `lent`), provided they
make a valid block (`buildable`) and reference no author it leaves out
(`lents`). Both tests pass a slot whose leader the node leaves out
(`excluded`), so it never waits for a convicted leader's block. It does the same where leaving authors
out leaves fewer than `q`: a valid block of round `r + 1` names `q`
authors and none it exposes, so its references make a valid block for the
node. Without
this a Byzantine author could show one twin, through which the leader
block is reached, to the nodes ahead and the other to a node behind: the
node behind holds both once it receives the history of a block built on
the first, but the least identifier may be the second, and it then waits
its timer where its peers did not, by a timeout at each round the attack
repeats. When it builds on being behind and the tests fail, it builds on
`refsFor`'s references if it can, and on a lent set otherwise. The
program builds rounds in sequence. It
persists the block, then broadcasts it, then sets the retry timer: the
timer of round `r`, for twice its timeout (§3.6).

The timer of round `r + 1` is set once the memory holds `q` authors of
that round (`arm`), not at the build. A node that builds ahead of a
quorum, on the tests or on being behind, starts waiting only once the
quorum is there, so a node that waited the timeout held a quorum of the
round a timeout before (§5.3).

### 3.3 The decider

After each change to its state the program runs `tryDecide p σ W V lo N`,
where `lo` is its next undecided slot, `N` the last slot at a round its
disk holds (`decidable`), as the scheme's TryDecide scans to the
highest round, `W` the memory's window at the round `R` of slot `lo`
(`Store.window`) and `V` the view of all its blocks
(`Store.windowView`), and outputs the new decisions (`decideStep`). It
does so only when the memory holds round `R`, which it always does
(§3.1); when it decides a slot it releases the memory below `floorOf`.

The window holds a store's blocks at rounds `R` and above, gathered
from `byRound` at the rounds `R … topRound`. A block at round `R` is
read without its references, so that the window is closed under
references; a block above `R` is read as the store reads it, and its
references lie one round below it, at `R` or above. The decisions on the window are
those on the store's view. Every set the loop counts from slot `lo` on
lies at or above `R`: the candidates at a slot's round, the blamers and
certificates above it, a vote's slot at it, a certificate's votes one
round below it, and a link's certificates, which the anchor reaches
through blocks above them; for a wave of two rounds or more, which an
admissible row has, the references of blocks at `R` are never read
(`ViewsAbove.tryDecide_eq`). At the bounded vote, a vote reads only the
voter's history down to the slot's round, so the store's view and the
window agree from `R` up (`ViewsAbove.window`), and the two give the
same decisions (`tryDecide_window`); so do the memory and the disk from
`floor` up (`Mirrors.viewsAbove`), and the decisions on the memory's
window are those on the disk's view (`tryDecide_memory`). The proofs
rewrite the decision step with this equality and reason about the
disk's view.

Over successive views this is `consumed`. A slot can be
skipped directly once its voting round holds `skipThreshold` blamers,
before its decision round.

### 3.4 Syncing missing blocks

A node accepts a block only once it holds the block's references. When
an equivocator sends one twin to some nodes and the other twin to the
rest, a node holding only one twin cannot complete the history of a
block referencing the other; a node that was down lacks what was sent
meanwhile. The node syncs what it lacks, as in the Sync model
(`docs/sync.md` §2), with one sync for each peer.

**Announcements.** A peer's broadcast of its own block is an
announcement (`Input.deliver`, which names the peer). It is dropped
unless the block is the peer's, the peer is neither the node nor
detected, the identifier is the block's hash, and the block is not on
disk. A block ready on arrival is accepted. Otherwise, if its round is
`0` or it references `q` blocks, and it lies above the block of the
node's sync with the peer, it becomes the block of that sync, with no
name asked for yet, and the node sends the peer a request (`request`).
So the node holds at most one sync for each other node, `n − 1` at
most (V1).

**Requests and streams.** A request names the sync's block `t`, the
node's frontier and the identifiers asked for by name. The frontier
gives, for each author, the least round at which the disk holds no block
of the author, and `0` for a detected author (`frontierOf`, `gapOf`):
below it the node holds a block of the author at every round. The peer answers with the blocks of its
disk in `t`'s history that are `t`, are asked for, or lie at or above
their author's frontier, reached from `t` through such blocks, in order
of round (`streamOf`), and with nothing if it holds none.

**Taking a stream in, header first.** Of a stream piece from a peer with
which it has a sync, the node reads the blocks of the piece under their
hash reached from the sync's block through such blocks, other than its
own (`hashed`, `inHistory`). It takes them in, in order of round, each
accepted if it is ready then (`absorb`), only if the sync's block is
then held; otherwise it takes none of them (`takeIn`).
So a block of a stream enters the disk only with the whole history of
the sync's block, every block of which passes the checks: a block that
breaks the exposure rule keeps out the blocks below it in the piece,
which check on arrival would have taken in first. The node then drops
the syncs whose block it holds or whose peer it has convicted (`tidy`).
If the sync stays, the references of its block and of the piece's blocks
that neither the disk nor the piece holds are added to the names asked
for (`missingIn`), and if a name was added, the node asks again. A piece
that adds nothing asks nothing, so streams cannot make two nodes loop.
After each step the node accepts the syncs' blocks that have become
ready, in passes (`flushSyncs`).

**Why names.** The frontier says which rounds of an author the node
holds, not which blocks. A block below its author's frontier is left out
of the stream; a streamed block that references it then has a reference
neither held nor streamed, and the node asks for it by name. An honest
peer holds the history of every block it holds, so it streams the block
asked for. If `v` never held honest `u`'s top block, the last request of
`v`'s sync for it was answered with a piece that was not taken in and
asked nothing. The piece's part in the block's history is valid, in
order of round, so some reference of
it is neither held by `v` nor in it (`foldl_all`); that reference was
asked for by name, so the piece holds it, in the part (V3′).

**Conviction.** Accepting a second block of an author at one round gives
evidence of the author: the two blocks (`evidenceOf`). The evidence a
block carries in its payload is kept too, and the node convicts the
authors its evidence names (`State.evidence`, `State.detected`). It then
takes no announcement from a convicted author, drops its sync with it,
answers none of its requests, and leaves it out of its references
(§3.2). A convicted author's blocks still arrive in the streams of other
syncs, while honest blocks still reference them. Evidence travels in
blocks: a block exposes the authors its evidence names and those its
references expose, and is valid only if it references none of them
(`Clause.exposes`), so once every honest block of a round exposes an
author, no later block references it (`exposed_of_correct_exposed`). An
honest node never convicts an honest one (`Converge.not_detected`): twins
of an honest author do not exist, and evidence against one does not
either, which is what signed headers give and the claims assume
(`EvidenceAuthentic`). Ignoring a convicted peer's requests matters: an
equivocator's copy that rejects every block built on its twin keeps a
low frontier, and each of its requests would stream the history above
it. At Orcaella with `n = 9` and an equivocator, the honest nodes
streamed 411,549 blocks in 200 ticks to its copies before this rule, and
181 to all nodes in 1,000 ticks with it.

**Asking authors.** When its retry timer fires and it does not build,
the node asks every peer for its block of the node's top round (`ask`),
and a peer it has not convicted answers with its own block of that round
(`send`). A node short of authors it does not leave out thus gets the
blocks of the authors that hold theirs. The liveness argument does not
need this; it reads the lent references (§3.2).

**The blocks a node holds a round.** A node takes a block of an author
in the author's own name, as an announcement or as the block of the
author's sync, only while it has not convicted the author; the other
blocks of a stream piece it takes in are each referenced by a block
taken in with them, since the walk through the piece goes only through
blocks under their hash (`hashed`). So each step adds at most one block
of an author that no block of the disk references, and none of a
convicted author; and two blocks of an author at one round convict it.
Along a trace each author other than the node therefore has at most two
blocks a round on the disk that no block of it references, and one if
not convicted (`steady_before`). Once every honest block of round `m + 1`
on the disk exposes the convicted authors, no block of the disk from
round `m + 2` on references one, since each references an honest block
one round below when fewer than `q` nodes are not honest (D17); so the
disk holds at most `n + |D|` blocks of each round from `m + 1` on, for
`D` the authors convicted (V13). Were the walk to go through blocks
under another identifier too, a peer could list any valid block as a
reference of such a block, and have it taken in.

**Withholding.** A Byzantine node that shows one node `v` a block
referencing a block it reveals only to the others stalls nothing: the
honest peers that built on the revealed block hold it in the history of
their blocks, which `v` syncs. The simulator's withholding attack
(`--withhold z,v,R`) runs in the build (`LeanDagTest/Node/Sim.lean`).

### 3.5 Settling

A step that changes the state (the start, an announcement or a stream
piece acted on, a timer) ends by settling: the node builds, decides and
accepts the syncs' blocks that are ready, in passes, until a pass changes
none of its top, the number of its syncs and its next undecided slot
(`settle`, `quiesce`). The passes are bounded by the state (`passes`),
and with `2 ≤ q` a settle ends settled (`Settled`, `settle_settled`):
nothing more can be built, no sync's block is ready, and nothing more
can be decided. So none of the node's
moves that what it holds allows is left for a later event.

### 3.6 Restart and resending

The environment persists the state a step leaves, atomically, before any
of the step's outputs take effect. A crash loses the timers set and not
fired, the outputs of the last step that have not taken effect, and the
messages that arrive while the node is down; the state survives. On a
restart (`Input.restart`) the node resends (`resend`): it broadcasts its
block at its top round, sets the retry timer again, asks every peer for
its block of that round (§3.4), and asks again in every sync (`resync`),
since a request or its answer may have been lost. It also sets the timer of its top round
again if it had set it (`rearm`). It then marks itself recovering
(`State.recovering`) and settles. A block is persisted before it is
broadcast, so a restarted node never builds a second block at a round it
built. A decision whose output was lost is in the persisted `decided`.

When the retry timer, or the timer of its top round, fires and the node
does not build, it resends in the same way. The retry timer is the timer
of the round below the top, set at the build for twice that round's
timeout. A node with a quorum of its round builds within its timeout of
the quorum's arrival, before the retry timer fires, so it resends only
when it is stuck; at one timeout the retry timer would fire first in
every round that waits its timer. Lost messages are not sent again
otherwise, and without this a crash can stall the reliable nodes. At
`n = 4`, `f = 1`, `q = 3`, with node `3` silent, node `2`
crashes at round `t` before it receives the round-`t` blocks of nodes
`0` and `1`. They build round `t + 1` on its round-`t` block and wait
for its round-`t + 1` block, while node `2` restarts at round `t` without
a quorum. With resending, nodes `0` and `1` send their round-`t + 1`
blocks again every two timeouts; node `2` syncs their histories,
builds round `t + 1`, and the three go on. In
`LeanDagTest/Node/Step.lean`, with node `2` down from time `20`, nodes
`0` and `1` stop at round `5` after four decisions; with node `2`
restarting at time `60`, after 400 inputs the three are at round `28`
with 28 decisions each, alike.

Asking again matters as much as sending again: a request, or its answer,
lost while the node was down is not sent again otherwise. The node asks
again in every sync on its restart and when its retry timer fires; it
does not ask again on a stream piece that gains nothing, which keeps two
nodes from asking each other in a loop. At Nemo-Nemo with `n = 3`,
`c = 1`, node `2` silent and node `0` down from time `150` to `260`, node
`1` alone stalls at round `16` and sends its top block again every two
timeouts; once node `0` is back, the block brings it a sync of the
rounds it missed, and it builds above round `16` at `266`.

A recovering node, one that restarted and has since neither built nor
had a timer fire, does not build the rounds it missed. It jumps: it
builds above the highest round `r` above its top at which its memory
holds `q` authors and is behind (`jumpRound`), on the round-`r` blocks of
the other authors, with no block of its own among the references, once
no sync's block lies above round `r + 1` (`syncTop`) and the references
pass the reach and certificate tests (`tryBuild`). Waiting for the
syncs' blocks keeps the node from jumping to a round that the history it
is still syncing would raise. Without a round to jump to, it builds
above its top once no sync's block lies above the round it builds, and
the first build or timer ends the recovery. The jump is safe because no
claim reads a node's reference to its own block (§8). A recovering node
jumps only if the history it syncs arrives before a timer fires. At
Mysticeti with `n = 4`, node `3` down from tick `200` to `900` and a
horizon of `1500` ticks, node `3` restarts at round `85`; its top round's
timer, set again at the restart, fires at tick `910`, before the stream
of the rounds it missed, which ends the recovery, and once the stream is
in it builds each round from `86` to `178` in one step. The nodes end at
round `435`, and the largest disk holds 1,740 blocks, four fewer than
four a round. It needs no bootstrap, since no block is collected.

## 4. Conformance

| | Claim | Proof |
|---|---|---|
| V1 | Over any input sequence: the node's own blocks, those it persists, are its own and identified by their hash; they lie at strictly increasing rounds; each references only blocks it knew, and is valid at the row under every block map agreeing with what it knew; it broadcasts each block it persists, and only blocks it persists; it keeps the decisions it outputs, which are slots `0 … lo − 1`; it holds at most `n − 1` syncs. | `Node.Local.OneEach`, `Authored`, `Sends`, `ValidOut`, `Decisions`, `SyncsBound` (proved, `Local/Proof.lean`): `Node.syncsOn_run`, `Node.syncs_length_le` |
| V2 | **The decisions are the scheme's**: at the bounded vote, a decision step of a node whose memory holds the round of its next undecided slot, as it always does (§3.1), outputs what `Scheme.tryDecide` decides on any record and view holding the disk's blocks, read alike; over successive views this is the scheme's loop. | `Node.Local.DecidesOnView` (proved): `Node.tryDecide_memory`, `Node.Store.Mirrors.viewsAbove`, `Node.tryDecide_window`, `Node.ViewsAbove.of_store`, `Node.ViewsAbove.tryDecide_eq` |
| V3 | **Safety**: over a trace with timely authentication of blocks, an injective hash and `Params.Tolerates`, the blocks the honest nodes knew form a `BlockRecord` at quorum `q` of which every honest disk is a cut, and any two honest nodes' decisions are prefix-comparable. | `Node.Runs.Safety` (proved): `Node.globalRecord`, `Node.ground`, `Node.CommitInv.run`, `Scheme.Loop.resume`, `Scheme.Loop.prefixComparable` |
| V3′ | **Convergence**: over a trace with delivery, timely authentication, an injective hash, and authentic evidence, every block in the history of an honest node's own block at its top at the end is on every honest node's disk at the end. No fault bound is needed: an honest node given the block has a sync for it until it holds it, and the answer to the sync's last request leads to no request, which it would if the node still lacked the block (§3.4). | `Node.Converge.Converges` (proved): `Node.Converge.sync_made`, `Node.Converge.sync_stays`, `Node.Converge.last_ask`, `Node.step_stream_stuck`, `Node.foldl_all`, `Node.Converge.not_detected`, `Node.eq_of_persists` |
| V13 | **The blocks a node holds a round**: over a trace with timely authentication and an injective hash, with fewer than `q` nodes outside the honest set, if every block of an honest author at round `m + 1` on an honest node's disk exposes every author the node convicted, its disk holds at most `n + |D|` blocks of each round from `m + 1` on, for `D` the authors it convicted: one of each author not convicted and two of each convicted. Under spread evidence (§5.1) for a set `D` and a round `n_E`, at the bounded vote of an admissible configuration with a faithful payload source and at most `f` nodes outside the honest set, the premise holds at `m = n_E`, so the bound holds from round `n_E + 1`: an honest block above `n_E` references no author of `D` and its payload names them. | `Node.Bound.Bounded`, `Node.Bound.Spreads` (proved, §3.4): `Node.steady_before`, `Node.Steady.step`, `Node.takeIn_referenced`, `not_mem_creators_refs_of_correct_exposed`, `Node.own_known`, `Node.Bound.exposes_spread`, `Node.refs_avoid_spread` |
| V8 | The claims are about the program that runs: its disk and memory are ordered maps, its vote the bounded one, and compiled code departs from the definitions only by proved `@[csimp]` equalities; on the scheme's hand-built records its commits are those the scheme's tests record, and on random records its decided prefix is the least vote's, the scheme's loop's in its own order, and the same run a round at a time. | by construction: `historyUptoFrom_eq_levels` (`@[csimp]`), `boundedSel_sel_eq`; `check-arc-holes` forbids `implemented_by` and `extern`; tests `LeanDagTest/Node/Replay.lean`, `LeanDagTest/Node/Differential.lean` (§6) |
| V11 | **Liveness**: over a timed trace with delivery within `Δ` and synchronisation within `Δₛ` past GST, reliable nodes that do not restart, their timers on time, no honest node's timer early, timeouts above `2(Δ + Δₛ)`, authentic evidence, a faithful payload source, and evidence that has spread by a round every reliable node is at by GST, the reliable nodes produce a round per timeout and `Δ + Δₛ`, and a run of reliably led slots from a round that every reliable node was below at GST is decided by all of them `Δ + Δₛ` after they reach its last decision round, and within a bound of the sum of a timeout and `Δ + Δₛ` per round. The honest nodes outside the reliable set need meet no other timing assumption. | `Node.Live.Progresses` (proved, §5): `Live.produces`, `Live.decides`, `Live.decidesBy`, `Node.held_before` |
| V11′ | **Liveness across crashes**: if the reliable nodes stay up from `t_r` to the horizon `t₁`, with delivery, synchronisation and timers assumed only from then on, and timers lost only to a restart, with authentic evidence, a faithful payload source, and evidence that has spread by a round every reliable node is at by `max t_r gst`, the conclusions of V11 hold with GST replaced by `max t_r gst + W`, for `W` twice the largest timeout of the round below the one a reliable node is at by `max t_r gst`. Crashes before GST are the case `t_r ≤ gst`. The honest nodes outside the reliable set may keep crashing and restarting; with every honest node reliable, after every node crashed and restarted, the nodes decide again. | `Node.Live.Recovers` (proved, §5.6): `Node.arrival_of_recovered`, `Node.sends_again`, `Node.retry_last`, `Node.recovered_by`, `Node.topTimerBy_of_up`, `Node.top_arrives`, `Node.quorum_below` |
| V12 | **Refinement**: for an admissible configuration at the bounded vote, over a trace with timely authentication, an injective hash and at most `f` nodes outside the honest set, there is a `BlockRecord` at quorum `q` of which every honest disk, before every event, is a cut; every honest node's decisions are none or `Scheme.tryDecide` from slot `0` on a view of it that the node's disk holds. Under the assumptions of V11 (no timer need fire) or of V11′, it has the scheme's `WaveFacts` over every window of rounds from one above every reliable node's round at GST, and every slot of a reliably led run is decided by every reliable node to a leader block. | `Node.Refines.HasRecord` (proved, §5.7): `Node.commitInv_before`, `Node.waveFacts_of_run`, `Node.run_commits`, `Refines.waves_leads` |

Every claim depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`; `LeanDagTest/Node/Axioms.lean`).

**Equivalence with the scheme.** V12 states the relation in one
theorem at the scheme's interfaces. The run's record is a `BlockRecord`,
the scheme's universe. The program's decisions are the scheme's loop on a
view of it (V2, V3). A timed run gives the scheme's `WaveFacts`, the
clauses the scheme's wave argument reads, so the scheme's liveness
argument applies to it (V11, §5.3), and each slot of a reliably led run
is decided to a leader block. The parts V1, V2, V3 and V11 prove
separately. The scheme's inclusion of an author's earlier blocks is not
claimed (§8).

**The transfer.** The program decides on its own disk, a record of its
own; the run's claims are about a view of the run's record. The decider
reads a view and the block map on it alone, so the two give the same
decisions when the disk's identifiers are the view's and its block map
agrees on them (`ViewsAbove.of_store`, `ViewsAbove.tryDecide_eq`, for
the bounded vote, which reads only histories). The decision step runs
on the memory's window, which decides as the disk's view
(`tryDecide_memory`, §3.1, §3.3).

**Authentic evidence.** No block the honest nodes knew carries evidence
naming an honest author with two distinct blocks
(`Converge.EvidenceAuthentic`). An honest node carries only evidence it
holds of twins, so this is assumed of the other nodes' blocks: what
signed headers give. V3′, V11, V11′ and V12's timed parts assume it, so
that no honest node convicts an honest one or leaves it out.

**Authentication.** A block delivered to an honest node in an honest
author's name was broadcast by that author earlier in the trace
(`Converge.TimelyAuthentic`); at the end of the trace this gives
`Node.Authentic` (`Node.authentic_of_timely`). The program broadcasts
exactly the blocks it persists (`Node.Local.Sends`), so such a block is
one of the author's own, one a round. A block in a stream piece is
covered, since its author broadcast it. The links are authenticated as
well: an announcement names its sender, and the node takes an announced
block only from its author (§3.4).

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
(`Node.ground`). Every honest disk, at every event, is a cut of it,
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
* **timers** (`TimersFire`, `TimersAfterSet`): a timer a reliable node
  sets at time `t` for `a` ticks fires at `t + a`, and no honest node's
  timer fires earlier than its delay after it was set;
* **synchronisation** (`SyncedWithin`): a reliable node given a reliable
  node's block at time `t` holds it on its disk by `max t gst + Δₛ`,
  having synced its history. This is assumed of the network and the
  syncs together, not proved: the program proves that the syncs
  complete (V3′), not how fast. A sync completes in one request and
  answer when no gap occurs (§3.4), so `Δₛ = 2Δ` then;
* every reliable node **starts** by GST (`StartedBy`) and does not
  **restart** by `t₁` (`UpFrom T tr time 0 t₁`), so none jumps (§3.6);
* timely authentication of blocks, a block hash injective on every
  block, so no block on its disk has the identifier of the node's next one
  (`fresh_before`), and `2 (Δ + Δₛ) < timeout r` at every round;
* authentic evidence (`EvidenceAuthentic`, §4), so no reliable author is
  left out of a reference set, and a faithful payload source
  (`Faithful`, §2), so the node's block carries the evidence and the
  exposure the builder put in it;
* **the evidence spreads** (`Spread`), for a set `D` and a round `n_E`
  every reliable node is at by GST: every author that evidence in a block
  the honest nodes knew names, or with two blocks of a round among those
  blocks, is in `D`, and an honest node that persists a block above `n_E`
  has convicted every author of `D` before that event. An honest block
  above `n_E` then references no author of `D` (`refs_avoid_spread`), so a
  node that is behind can build on the references of an honest block of
  the round above (`lent_avoids_before`).

A step takes no time; the time it costs a node to act on what it holds is
the catch-up bound below, not a processing constant.

### 5.2 What the run gives

Let `A = Δ + Δₛ`: a reliable block built at `s` past GST is delivered to
every reliable node by `max s gst + Δ`, and its history arrives `Δₛ`
later, so every other reliable node holds it by `max s gst + A`,
whatever round it is at (`arrival_of_delivered`, `Helpers/Arrive.lean`).
The argument below reads the run only through this arrival, and only for
blocks at their author's round at GST or above (`Arrival`): a node's top
block past GST (`top_arrives`), and blocks above every reliable node's
round at GST. It also reads the run through the armed timer of a node's top round firing within its timeout
(`TopTimerBy`, `Helpers/Armed.lean`), and through timers firing no
earlier than set (`TimersAfterSet`); the assumptions of §5.1 give the
first two at GST (`TopTimerBy.of_fire`). The claim has three parts.

* **Production** (`Produces`): past GST, once every reliable node is at
  round `n` or above at `s`, every reliable node is above `n` at
  `s + A + timeout n`. By `s + A` a reliable node at round `n` holds
  every reliable node's top block at `s` (`top_arrives`). If one is above
  round `n`, its history holds `q` authors of round `n`
  (`quorum_below`); otherwise they are all of round `n`. So the node holds
  a quorum of the round, and has armed the round's timer
  (`armed_before`), which fires by
  `s + A + timeout n`. A node still at round `n` then is settled
  (`settled_before`), the round's timer has fired and stays so
  (`fired_stays`), and it holds no block with the identifier of its next
  one; so it builds (`tryBuild_isSome`), against its being settled.
* **Decision** (`Decides`): a node outputs a slot's decision only once
  every slot below it is decided, so the claim is about runs. Suppose
  every reliable node is below a round `n₀` at GST, and slots
  `b … b + c − 1`, at or above `n₀`, are led by reliable nodes with `c`
  spanning the rule's eligibility (`SpansEligible c`). Once every
  reliable node is at the decision round of slot `b + c − 1`, at `t`,
  every reliable node has output by `t + A` the decisions of every slot
  below `b + c` (§5.3, §5.4).
* **The time bound** (`DecidesBy`): if every reliable node is at round
  `n₁` or above at `s ≥ gst`, the reliable nodes gain a round every
  timeout and `A`, so they have output those decisions by
  `s + Σ (timeout r + A) + A`, the sum over the rounds from `n₁` to below
  the decision round of slot `b + c − 1`.

### 5.3 Catch-up and the wave facts

The family's argument (`Scheme/Helpers/Reactive.lean`) reads, of a run,
production, and that each reliable block of a wave reaches or certifies
the leader block, or references the leader's block of the round below,
or every reliable vote (`WaveFacts`); `reaches`, `votes` and `certifies`
read only these. A reactive execution supplies the references by arrival
after a wait. The program supplies them from round `n₀` on
(`reach_or_refs_node`, `cert_or_refs_node`, `Helpers/Wave.lean`): a
block built on the tests reaches or certifies the leader block; one
built on the timer references every reliable block of the round below,
which its builder holds (`waited_holds`); and one built on being behind
does too (`refs_all`). The argument is about time, over every honest
builder, reliable or not (`held_before`): when an honest block of round
`n + 1` that did not pass the tests is built, every reliable block of
round `n` has already reached every reliable node. If it was built on
the timer, its builder armed the timer with a quorum of round `n` a
timeout before, and `2A` after that every reliable node holds the
reliable blocks of the round. If it was built on being behind, its
builder holds an earlier honest block of the round (`behind_honest`),
which did not pass the tests either, or the references it lends would
have and the node would have built on those (`ready_transfer`): above
`n_E` they reference no author the node leaves out (`Spread`,
`refs_avoid_spread`), so the node may build on them. The claim follows by
induction on the event that built it. A reliable node
building on the timer or behind therefore holds, and references, every
reliable block of the round below: its builder leaves out no reliable
author (`not_excluded`), so the references it would lend are not taken
while its own set is buildable.

This needs of an honest node outside the reliable set only that its
timers do not fire early. Without it the claim fails: at Orcaella with
`n = 9`, `f = 1` and `c = 1`, a Byzantine node and an honest node
whose round timer fires at once can build the vote round before a
reliable leader's block reaches three reliable nodes, which are then
behind and build without it; with the other four voting, the slot has
neither the seven votes a commit needs nor the seven blamers a skip
needs, and the same at every slot leaves every slot undecided.

**The armed timer.** A node sets the timer of its top round only once
its memory holds `q` authors of the round (`arm`, `Armed`), which it
does once its disk does, since the memory holds the top round
(`Converge.floor_before`), and each
timer it sets is at or below its top, one of its top round above `0`
only so (`TimersSet`, `timersSet_before`). A node that built round
`n + 1 > n₀` on the timer of round `n` therefore set it past GST, at an
event at which it held `q` authors of round `n`, a timeout before it
fired (`timer_set`, `Helpers/Armed.lean`). Those authors are reliable but
for the at most `f + c` validators outside the reliable set, and
`2f + c + 1 ≤ q` on every admissible row, from its commit threshold and
its link or certificate inequality (`two_f_c_lt_q`), so `f + 1` of them
are reliable (`quorum_reliable`). The same holds of an honest node
outside the reliable set, given that its timers do not fire early.

**Catch-up.** Past GST, once `f + 1` reliable nodes are at round `n` or
above at `τ`, every reliable node is at `n` or above at `τ + A`
(`catches_up`, `Helpers/Catch.lean`). A node at a lower round `m` at
`τ + A` holds the top blocks of those nodes. If they are all of round
`m + 1`, they are `f + 1` authors of that round; if one is above it, its
history holds `q` of them (`quorum_below`). Either way the node is behind
round `m + 1` and holds `q` authors of round `m`; settled, it would
build, on the references of a held round-`m + 1` block if fewer than `q`
of its authors are left out of nothing (`lent_buildable`). So once an honest node armed
round `n`'s timer, every reliable node holds every reliable round-`n`
block `2A` later: every reliable node is at round `n` `A` after the timer
was armed, and its block arrives `A` after that, before the timer fires,
when `2A < timeout` (`waited_holds`).

No bound on how far apart the reliable nodes build is needed, so the
decision part starts from any round `n₀` above the reliable nodes'
rounds at GST, and production holds from GST. Setting the timer at the
build would not do: a node could build on the tests, with blocks of
Byzantine authors in its quorum, ahead of some reliable nodes, and its
timer of the next round could fire before their blocks of that round
arrive.

### 5.4 From verdicts to the node's decisions

The family's results conclude `Decided` on a view holding every block up
to a round (`CoversUpto`), Byzantine blocks included, which a node's
disk need not hold. A direct commit needs only the reliable
decision-round blocks (`decided_of_safe_of_holds`), and the prefix needs
only the run's (`decided_below_of_run`), so the node's view, which holds
every reliable block it has received (`reliable_held`), suffices. The
decision step reads the disk as `tryDecide` on a view of the run's
record (V2), and `tryDecide` outputs every slot decided on its view once
its scan reaches far enough (`tryDecide_within`): a verdict derived
within a bound `B` is output by a scan reaching `B − 1`, and the node's
scan reaches every slot at a round its disk holds (§3.3).

### 5.5 The timing check

The scheme's liveness structures are hypotheses, and their witnesses
hand-built records. Read against the program:

| Clause | Met by the program? |
|---|---|
| `SchemeReactive.advancesAt` | yes, once the round's timer fires: the timer stays fired while the node is at the round, so a quorum arriving later builds at once |
| `SchemeReactive.reach_or_wait`, `cert_or_wait` | yes, by the build rule (§3.2) |
| `PaceCore.holds_mono` | yes: the disk only grows (`Grows`) |
| `ReactiveCore.built_lt` | no: build times strictly increase, but one step may build several rounds at once, when a lagging node catches up; the node supplies `WaveFacts`, which does not ask it |
| `PaceCore.catchup` | in part: a node holding round-`n` blocks of `f + 1` authors builds round `n` at once (`behind`), so once `f + 1` reliable nodes are at a round every reliable node is there `A` later (`catches_up`); one reliable block does not suffice, since the node cannot tell which are reliable (§3.2) |

### 5.6 Crashes (V11′)

Reliable nodes may crash and restart until a time `t_r`, and stay up from
`t_r` to `t₁` (`UpFrom`: no reliable node restarts at or after `t_r` and
at or before `t₁`). A crash loses the messages sent to the node while it
is down and the timers it set before, so delivery and synchronisation are assumed only
for what is sent from `t_r` on (`DeliveredFrom`, `SyncedFrom`), and a
timer fires on time unless its node restarts before (`TimersFireUp`);
timers fire no earlier than set (`TimersAfterSet`), and every reliable
node starts by GST. Before `t_r` nothing is assumed: messages may be
lost and nodes down. Let `t₀ = max t_r gst` and `W` twice the largest
timeout of the round below the one a reliable node is at by `t₀`, the
delay of its retry timer. Then the three conclusions of V11 hold with GST
replaced by `G = t₀ + W` (`Recovers`). The proof supplies the premises of
the argument of §5.2–5.4 at `G`:

* **The top round's timer** (`armed_last`, `topTimerBy_of_up`,
  `Helpers/Armed.lean`). A node at round `n` with `n` armed set the
  round's timer at a last event, from which on it is at `n` with `n`
  armed; a restart after it would have set it again (`rearm`), so past
  `t_r` it is followed by no restart and the timer fires a timeout after
  it.
* **Arrival** (`arrival_of_recovered`). A block built from `t_r` on is
  delivered and synchronised as without crashes. A block a reliable node
  `u` built before `t_r` may have been lost; but by `t₀ + W` the node
  broadcasts again a block of its own at its round at `t₀` or above
  (`sends_again`): when its retry timer fires it builds above that round
  or resends its top block, or it built above before, and the retry
  timer cannot have fired by `t₀`, since then it would have been set
  again later (`retry_last`). The argument reads only blocks at their
  author's round at `G` or above (`Arrival`). A lost block of that round
  lies at the node's round at `t₀` and at `G`, so the block sent again
  is of its round and, an honest node having one block a round
  (`eq_of_persists`), is that block; it reaches every other reliable node
  with its history by `t₀ + W + Δ + Δₛ`, whatever round that node is at
  (`arrives`). The argument reads no reference of a node to its own
  blocks.
* **No jump past `G`** (`recovered_by`, `Arrival.no_jump`). The wave
  facts need a block of every reliable node at every round of the wave,
  so the argument needs that no reliable node jumps from `G` on. A node
  recovers until it builds or a timer fires; its retry timer, set again
  at its last restart, before `t_r`, fires by `t₀ + W`, so from `G` on no
  reliable node is recovering (`Arrival.recovered`), and none restarts
  (`Arrival.up`). A node that does not recover builds each round above
  its top in turn (`built_by`).

Restarts after `t₁` are not read, so the claims hold over each interval
from `t_r` to `t₁` in which no node of `T` restarts. A node that
restarts at a time `t` is in `T` for an interval that ends before `t`,
and for an interval that starts at its restart or later; between them
it is one of the at most `f + c` nodes outside `T`
(`n − f − c ≤ |T|`), with the Byzantine nodes.

The decision part needs no synchronisation point (§5.3), so after a
recovery the reliable nodes decide every reliably led run of slots from
a round that every reliable node was below at `G`, whatever the honest
nodes outside the reliable set do, provided their timers do not fire
early. Where every honest node is reliable: after every node crashed and
restarted, the chain decides again.

### 5.7 Refinement (V12)

The record is the run's (`globalRecord`). Its holdings are `cut_before`,
and the loop is `CommitInv.run` read before each event
(`commitInv_before`).

Over a timed trace, delivery and synchronisation give arrival within `A`
(`arrival_of_delivered`; with crashes, `arrival_of_recovered` from
`max t_r gst + W`). Arrival gives the wave facts (`waveFacts_of_run`).
On a reliable node's view `A` after the last decision round, each slot of
the run commits a leader block `L` (`run_commits`). By V11 the node has
output a decision `d` for the slot. That decision is a verdict on some
view of the record (`cut_before`), and verdicts on one slot agree
(`AnchoredRule.decided_unique`), so `d = some L`.

## 6. Testing

1. **Agreement with the model** (`LeanDagTest/Node/Replay.lean`). A
   hand-built record of the scheme's tests goes, in order of round,
   through the program's acceptance path (`absorb`) into an empty disk
   and memory, and one decision step (`decideStep`) runs on it. Its commits are those the scheme's tests
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
   node down for 10 to 850 ticks, with GST at `0` or after the restart;
   two nodes down at staggered times; every node down at once, or in a
   staggered way; `f + c + 1` nodes down overlapping; one node down three
   times; and `f + c` nodes silent and one more down. In all 288 runs
   agreement, prefix-comparability and validity hold; every node up ends
   108 rounds or more above the top round at the last restart, and 44 or
   more with `f + c` nodes silent; the restarted node builds above that
   round within 30 ticks of the restart when it restarts past GST and
   within 56 ticks before GST; and an honest node decides again within 21
   ticks past GST and 49 before. Catch-up is cheap: over 650 ticks at
   Orcaella with `n = 9`, a 250-tick outage takes 17,194 inputs and 296
   requests, 90 of them naming blocks, against 21,114 inputs and 339
   requests without it, and an 850-tick outage over 1,250 ticks takes 3.5
   seconds to simulate. Three outage scenarios run in the build
   (`LeanDagTest/Node/Sim.lean`).

   An equivocator's copies each drop blocks in their own name, so neither
   copy accepts blocks built on its twin, and it stops building. The
   honest nodes that accept both twins convict it, put the evidence in
   their next block, and leave it out of their references; the others
   convict it on that evidence. The tests then pass its slots without its
   blocks (§3.2): at the Mysticeti row with `n = 4` the honest nodes reach
   round 53 in 150 ticks, deciding 52 slots, 13 of them skips. Over 1,000
   ticks at Orcaella with `n = 9`, they reach round 349 with 38 skips,
   and the streams carry 558 blocks in all (§3.4). From `byzUntil` on it acts
   on nothing.

   The simulator reports the most blocks of one round on an honest disk,
   and of those the most by other authors. Without faults it is `n`. Under
   `invalidBlocks` and `twinSplit` at Mysticeti with `n = 4` over 1,000
   ticks it is 5 and 6, with 2 and 3 by the attacker, all below round 5;
   from round 5 on each honest disk holds the 3 honest blocks of each
   round and no block of the attacker. With an equivocator at Orcaella
   with `n = 9` it is 10, 2 by the equivocator, and 8 from round 5 on.
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
   prefix-comparability and validity intact. A node that accepts two
   blocks of the attacker at one round convicts it, under `twinSplit` and
   under `invalidBlocks`, whose block without references at round `0` is
   a twin of the attacker's genesis block. It then takes no announcement
   from the attacker, whose blocks reach it only in streams, and the
   honest nodes build 52 to 56 rounds in 150 ticks, against 66 under
   `forgedAuthor`. Without the checks, the blocks forged in node `0`'s
   name still reach no node: a node takes an announced block only from
   its author, and the attacker streams only blocks it holds.

## 7. Tooling and cost

* The model's functions run under `#eval`. `historyUptoFrom` is
  computed a level at a time (`historyLevels`, proved equal and marked
  `@[csimp]` in `Common/Causality.lean`), which removes its exponential
  cost. The vote rule is `boundedSel`, the least vote searched only as
  deep as the slot, a `VoteSel` that selects what `leastSel` selects at
  every block of a record (`boundedSel_sel_eq`); for that a store's
  record carries `stored`, references one round below. A store's
  block map is an ordered map rather than a chain of updates.
* `scripts/check-arc-holes.py` forbids `partial`, `unsafe`,
  `implemented_by` and `extern` in the arcs it lists, `LeanDag/Node`
  among them, so compiled code departs from the definitions only by
  proved `@[csimp]` equalities; the executables' input loops, outside
  the library, run on fuel.
* The executables are `[[lean_exe]]` targets of `lakefile.toml`, not
  default targets, so `lake build` and the audits are unchanged.
* **Cost.** The disk keeps every block, and the memory the blocks from
  the floor up (§3.1). Membership in the accepted identifiers costs a
  lookup in the map, logarithmic in the number `N` of blocks in the map; the
  top round is read off a field; the blocks and the authors of a round
  cost a lookup in `byRound` and the size of the round. Releasing the
  memory rebuilds it from the blocks it keeps, in time linear in its
  size. The scheme's functions (`Scheme.tryDecide`, `candidatesIn`,
  the votes) take any record and view, and read a round by filtering
  the record's identifiers. The builder's reach and certificate tests
  read the leader blocks off `byRound` (`leaderBlocks`), and the
  decider runs on the window at the round of the next undecided slot
  (§3.3), whose identifiers are gathered from `byRound`; the decider's
  scans therefore cost time in the number of blocks at and above that
  round, not in `N`. A stream sends the blocks of a block's history
  above the asker's frontier, those asked for by name, and the block.
  The frontier scans the disk's rounds from `0` for each author
  (`gapOf`); the executables read it once a request. Four nodes at the
  Mysticeti row reach round 435 over 1,000 ticks, the largest disk
  holding 1,740 blocks and each memory at most 10 at the end; over 4,000
  ticks round 1,736, the largest disk holding 6,945 and each memory at
  most 10. With GST at 300, a node down from the start or for 250 ticks,
  an attacker sending invalid blocks or showing each node its own twins,
  or an equivocator, each memory holds at most 10 blocks at the end; at
  Orcaella with `n = 9`, after a node is down for 350 ticks, at most 12,
  against 2,880 on disk. A node holds at most 3 syncs at `n = 4` and 8 at
  `n = 9`. An 8,000-tick run takes 14 seconds, about nine tenths of it
  computing frontiers.

## 8. Self-references

The row's validity does not ask a block to reference a block by its own
author, and no claim of the program reads such a reference: not safety
(V1–V3, V12's holdings and loop), nor liveness without or with crashes
(V11, V11′, §5.6). The build rule references one block of each author of
the round below (§3.2), the node's own among them when it holds one, but
nothing depends on it.

The shared layer's `SelfParent` gives inclusion: a reliable author's
committed leader block reaches each earlier block of that author, by
walking the author's chain down (`SelfParent.reaches_of_creator`,
`mem_history_of_decided_commit`, `includes_of_leads`,
`committed_of_correct_block`, `Support.inclusion`). The program claims
no inclusion, so a node need not reference its own blocks.

## 9. Next

The restart, resending and liveness across crashes are done, including
decisions resuming after every node crashed (§3.6, §5.6), and the syncs
of `docs/sync.md` on the node (§3.4), the evidence, conviction and
exclusion of equivocators (§3.2, §3.4), Stages 1 and 2 of
`docs/node-sync.md`, header-first admission of streams (§3.4), Stage 3,
and the bound on the blocks a node holds a round (V13), Stage 4. Open:

* the disk and the decisions grow with the chain, which they record;
  and the memory holds every block of its rounds, so an equivocator can
  grow it by its twins;
* the frontier costs a scan of the disk's rounds for each author at each
  request (§7); and an author whose blocks skip a round below its
  latest, as a node that jumped, keeps its frontier at that round, so
  each stream carries its blocks above that round in the history of the
  stream's block, as it does a detected author's, whose frontier is `0`;
* V11, V11′, V12 and V13's bound from `n_E + 1` assume that the evidence
  spreads (§5.1): `n_E` is a round from which every honest builder has
  convicted every author the honest nodes saw equivocate. Nothing bounds
  `n_E`, since an author may equivocate first at any time, and the
  premise is not proved of the network for the honest nodes outside the
  reliable set;
* the record V12 builds is at `ValidAt q Clause.none`, not at the
  exposure clause the node checks;
* a node answers every request of a peer it has not convicted, so before
  conviction a node can be made to stream any amount;
* a piece has no size limit. The frontier is an author's least round not
  held, so after a restart's jump every stream carries the restarted
  author's blocks from the jump up: at Mysticeti with `n = 4` and node 2
  down from tick 100 to 250, the longest piece an honest node receives
  is 65 blocks over 400 ticks and 586 over 1,600, against 4 with no
  outage;
* a piece not taken in is streamed again whole with the names it lacked,
  since the node keeps no part of it;
* a recovering node jumps only if the history it syncs arrives before a
  timer fires (§3.6);
* only a node that restarted jumps: a node that falls behind without
  crashing builds each round it missed, on being behind (§3.2);
* a node of `T` that restarts between `t_r` and `t₁` falls outside the
  claims for that interval, since a jump leaves it without a block at
  the rounds it jumped over, which the wave facts read (§5.6). A claim
  for each slot whose rounds no node of `T` jumped over would admit
  restarts at any time; the production and catch-up arguments run
  forward from one time `G` and would have to start again at each
  recovery.
