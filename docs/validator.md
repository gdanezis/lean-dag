# An honest validator for the scheme

This document plans a Lean program that acts as an honest validator of
the partially synchronous rows of the scheme (`docs/scheme.md`), and the
proofs that it conforms to the scheme. The program lives in
`LeanDag/Node`, namespace LeanDag.Node; steps 0 to 7 are built, and
part of step 10 (§7). Names
in backticks are existing declarations; names in italics are planned.

## 1. Scope

The program is parametrised by a row `p : Params` and the quorum `q`. It
covers the six partially synchronous rows: Cordial Miners PS, Mysticeti,
Blue Bottle PS, Orcaella, Nemo-Nemo and Hybrid Mysticeti. The
asynchronous rows, the coin and `AsyncPace` are out of scope.

It integrates these mechanisms:

* **garbage collection**, with crash persistence and restart;
* **Safe Skip**, the one-message return after downtime, built in step 6
  and taken out again in step 7.1, where a node resumes by building
  above the highest round it holds a quorum at (§11);
* **rate limiting**, the novelty budget on acceptance;
* **bootstrap**, the return of a validator down past the horizon, from
  the attested base;
* **checkpoints**, certificates of the decided prefix by a quorum, which
  bound the horizon and give a bootstrapped node the decisions below it
  (§3.8, step 7.3).

Two of these rest on results stated on the core's universe only, which
are lifted to block records at quorum `q` first (§8).

Out of scope: stake weights, a mempool (the payload comes from a
configured source), execution (a checkpoint certifies decisions, not an
executed state, and `DeterministicVM` appends a decision), and an
implementation of hashing and signatures. Identifiers are the
environment's hash, assumed injective on the blocks of a run. Blocks,
base offers and checkpoint proposals are signed by their source, and the
proofs assume what the signatures give (authentication); the
executables check no signature and trust their inputs, so a deployable
node would verify each of these signatures on receipt.

## 2. Interface

The program is a pure, total transition function

> *step* : *Config* → *State* → *Input* → *State* × List *Output*

wrapped by two executables: one reading inputs and writing outputs as
JSON lines, and a simulator running `n` instances over a seeded network.

**Configuration.** The row `p`, the quorum `q`, the validator's own
identity, the schedule `Slots`, the timeout per round, the vote rule
(`leastSel` first, `votedBlock` with the stored reference order
second), the hash *idOf*, the horizon lag `Λ`, the novelty budget `τ`,
and the payload source. At start the program checks that the row is
covered and live at the configured `n`, `f`, `c` and `q`
(`Params.Covered` and `Params.CertFits`, with the commit threshold
within `n − f − c` and `f < q`, all decidable) and refuses a
configuration that is not. `f < q` puts a node that is not Byzantine in
every quorum of signers (§3.8).

**Validity.** Every row uses `ValidAt q Clause.distinct`: references
one round below from `q` distinct authors, no author twice. It is
decidable (`ValidAt.decidable`) and mechanised (`ValidAt.mechanised`),
and quorate and distinct by `Validity.Quorate.of_validAt` and
`Validity.Distinct.of_validAt`. A reference to the author's own
previous block is the build rule (§3.2, §11).

**Inputs.**

* a start, with no persisted state: the program builds its genesis
  block;
* a delivered block: identifier, round, author, ordered references,
  payload;
* a timer for round `r` that fired;
* a crash and restart: the node keeps only what it persisted (§5.1);
* a base offer from a peer: its round-`G` blocks and its window above
  them (§3.6);
* a base request from a peer;
* a request from a peer for some blocks (§3.7);
* a peer's signed proposal of its decisions below a height, and a peer's
  certificate (§3.8).

**Outputs.**

* persist one of its own blocks, emitted before the block is broadcast;
* broadcast a block;
* set a timer for round `r`;
* commit slot `k` with a decision `Option BlockId`;
* prune below the horizon `G`;
* request the base from the peers;
* serve the base and window to a peer;
* ask every peer for some blocks (§3.7);
* send a block to one peer;
* sign and send every peer a proposal of its decisions below a height,
  and send its certificate to a peer (§3.8).

Time is discrete (`ℕ`), as in `PaceCore`.

## 3. The program

### 3.1 The store

The store is an ordered map from identifiers to blocks
(Std.TreeMap), with the accepted identifiers and the horizon (§3.4).
A received block whose identifier is not *idOf* of its content is
dropped, so that an identifier denotes one block. Otherwise it passes
through three stages.

1. **Pending**: some parent is missing. The block waits.
2. **Held**: its parents are held and it satisfies the row's validity
   `ValidAt q C`, which is decidable.
3. **Accepted**: its novelty, the blocks of its history not yet
   accepted, is at most `τ` (`UniformBudget`). Otherwise it is deferred
   until the accepted set has grown.

The accepted set is closed under references, so it is a
`BlockRecord.View`; this is the view the decider reads. Byzantine
twins are accepted, since their votes count. Blocks below the horizon
`G` are dropped, and round-`G` blocks are read without references.

The physical store shrinks when the program prunes; the holdings the
proofs read (`PaceCore.holds`) are the logical ones, every block
accepted so far, which only grow. V4 relates the two.

### 3.2 The builder

The program builds round `r + 1` when it holds `q` distinct authors of
round `r` and, for the slots whose wave is in progress, either

* the block it would build reaches the slot's leader block, at each round
  from the one above the proposal to the vote round, and certifies it at
  the decision round of a three-round row; or
* the timer for round `r` has fired.

A step that changes the store (a delivery acted on, a timer, the start)
ends by flushing the pending blocks, so no pending block is left ready
after any step; a block built or a horizon raised can make one ready.

These are the clauses `advancesAt`, `reach_or_wait` and `cert_or_wait`
of `SchemeReactive`, written as a rule the program runs, so the liveness
hypotheses hold by construction.

The rule is reactive: the program builds as soon as what the decider
counts has arrived, and the timer is only the fallback for a leader
block, or for votes, that do not arrive. Once its block would reach the
leader block, and at a three-round row's decision round certify it, the
program builds without waiting further. After GST the round time then
tracks the actual delivery delay rather than the timeout; the core shows
this at the Mysticeti row (`ReactivePace.built_succ_le_of_fast`,
`ReactivePace.no_timeout_of_fast`), and its analogue for the family is
part of step 11. The full-timeout discipline (`ViewPace`), in which a
validator waits the timeout every round, is not used.

The new block references one accepted block per round-`r` author,
its own block of round `r` for itself if it built one, and the least
identifier between twins otherwise (`refsFor`). The validity it must
meet is `ValidAt q Clause.distinct`: references one round below, from
`q` distinct authors, none twice. Referencing its own previous block is
the build rule, not a validity clause (§11). The program builds rounds
in sequence and skips them only by resuming (§3.5) or by bootstrapping
(§3.6). It persists the block, then broadcasts it, then sets the timer
for round `r + 1`.

### 3.3 The decider

After each step the program runs `tryDecide p σ U V lo N` on its view,
where `lo` is the slot after the last decision output and `N` the last
slot whose decision round it holds, and outputs the new decisions. Over
successive views this is `consumed`.

### 3.4 Garbage collection

The horizon is `G = min(F, t) − Λ`, where `t` is the node's round and
`F` the round of the first slot that is not both decided and certified:
the slot round of the lesser of the next undecided slot and the height
of the node's certificate (§3.8). This is the depth rule of
`garbage.md` §6, with the frontier certified.
Below `Λ = 2` the attested base can miss blocks a joiner needs; safety
holds at every `G`. After each decision step the horizon rises to `G`
if that is higher: the store drops the blocks below `G`, reads those at
`G` without references, and keeps absolute rounds; pending blocks and
timers below `G` are dropped, and the node outputs `prune G`. A block
received at the horizon is kept without its references, as the cut
keeps it; one below it is dropped.

The decider then runs on the original schedule. Every slot it still
decides lies at `F` or above, and its decision reads only rounds from
the slot's round up, all above the horizon.

### 3.5 Resuming after a restart

A restarted node is recovering until it resumes (`tryResume`). Let `t`
be its top. It resumes at the highest round `R > t` at which its store
holds `q` authors (`quorumRound`), if it has no block of its own at `t`,
or if `R ≥ t + 2`; with its own block at `t` and `R = t + 1` it builds
`t + 1` on that block as usual. Its top becomes `R`, with no block of
its own there, the timer of round `R` counts as fired, and it builds
`R + 1` by the rule of §3.2. Resuming sends nothing, and the next block
is an ordinary one, valid at the row.

A node that is not recovering never resumes. A reliable node's own
blocks therefore reference each other round by round from its first
round on, which is what the inclusion argument reads (§11).

Safe Skip, the scheme's jump over a downtime with filled blocks, is not
part of the program. Its results stay in the shared layer
(`SafeSkip/Jump.lean`), with L0.

### 3.6 Bootstrap

A validator whose last own block lies below its peers' horizons cannot
rejoin from its window, because the blocks its window references are
pruned. A restarted node asks every peer for its base. It asks again
whenever a delivered block lies `Λ + 2` rounds above the one it last
asked on. A peer answers with its horizon and its store
(`State.window`), and with its certificate if it holds one.

The node keeps each base offered, one per peer (`State.offers`). A block
is attested at round `G` when `f + 1` distinct peers offered it at that
round, a presenter's attestation being its own offer (G10, `garbage.md`
§7; `baseAt`). The node bootstraps at the highest offered horizon above
its top that has an attested block and an offered certificate reaching
`G` (`bootRound`, `tryBoot`):

* it prunes its store to `G` and keeps the attested blocks there;
* its top moves to `G`, with no block of its own there, and the timer of
  round `G` counts as fired;
* it takes the offered blocks above `G`, and its own pending blocks at or
  above it, as pending;
* it takes an offered certificate whose height `k` has its slot round at
  or above `G` (`certFor`), outputs the certified decisions of the slots
  from its next slot up to `k`, and moves its next slot up to `k`.

It builds `G + 1` on the base by the rule of §3.2, a block valid at the
row; a peer holds it pending until it holds the base blocks it
references. The node stays recovering, so it resumes once its store
holds a quorum above `G` (§3.5). Its decisions have no gap: the slots
below the certificate's height are the certified ones, and it decides
the rest from its new base (V9).

### 3.7 Fetching missing blocks

A node accepts a block only once it holds the block's references. When
an equivocator sends one twin to some nodes and the other twin to the
rest, a node holding only one twin cannot complete the history of a
block referencing the other. The liveness structures assume that every
reliable node's holdings reach every reliable node (`converges`); the
program makes that true by fetching what it lacks.

**The rule.** After a block `h` arrives, the node walks `h`'s references
down through its pending blocks and collects those it neither stores
nor holds pending, at or above the horizon: the missing part of `h`'s
history (`missing`). It asks every peer for them in one *fetch* output,
and records each with `h` and its round, so as to ask for a block at
most once on account of each block that needs it, and so that garbage
collection drops the records with the rest. A node asked for blocks
*send*s the asker each one its store holds (`answer`). If `h`'s author
is honest, it accepted all of `h`'s history before building `h`, so it
holds everything asked for, and answers.

**Why per referrer.** A first rule asked for a block at most once. A
Byzantine node then stalls an honest node `v`: it sends `v` a block
referencing a block `x` no one else has seen, so that `v` asks for `x`
and nobody can answer; then it reveals `x` to the others, who build on
it; `v`, having asked once, never asks again, and never accepts their
blocks. The simulator's withholding attack (`--withhold z,v,R`) does
this, and stalled `v` under the first rule; under this one `v` asks
again on account of the honest blocks and keeps pace.

**What it gives** (`Node.Converge.Converges`, proved). Over a trace of
honest nodes and an adversary in which every message an honest node
sends another reaches it later (*delivery*), a block delivered with an
honest author's identity and its hash was broadcast by that author
earlier (*timely authentication*), the hash is injective on the blocks
honest nodes knew, and no horizon rises: every block an honest node
broadcast, with its history, is in every honest node's store at the
end. Suppose a node `v` lacks part of such a block `h`'s history. Then
`h` is pending at `v`, and below it a chain of pending blocks leads to
a block `z` that `v` lacks (no pending block is ever left ready). The
last of the chain's pending blocks to arrive arrived after `h` was
broadcast, with the rest pending; its walk reached `z`, which `v` had
not yet asked for on its account; `h`'s author, holding `h`'s history
since it built `h`, answered; and `z` arrived, after which it stays
pending or stored. Timely authentication is needed: without it the
adversary could deliver a copy of an honest block before its author
built it, `v` would ask on its account when nobody could answer, and
drop the genuine delivery as already pending.

It does not give `converges` as the pacing structures state it, every
block some honest node holds: a Byzantine block an honest node received
too late to build on may be referenced by no honest block, and then
nothing brings it to the others. The liveness arguments read the
reliable nodes' blocks and their histories, which is the form §9.1
item 4 restates.

**Cost.** The walk visits pending blocks, which nothing yet bounds; a
node fed blocks it can never accept pays for them on every delivery.
Bounding the pending blocks belongs to rate limiting (step 9).

### 3.8 Checkpoints

* **Proposals.** After a decision step whose decided frontier reaches a
  multiple `k` of `m` slots above the height it last proposed, the node
  signs and sends every peer a proposal of its decisions of slots
  `0 … k − 1` (`proposeAt`). The node keeps the decisions it outputs
  (`State.decided`); an implementation sends a hash chain of them, and
  the model compares them by equality, as the checkpoint model of
  `LeanDag/Checkpoint` does.
* **Certificates.** The node keeps each peer's latest proposal, its own
  included (`record`). `q` distinct signers of one height and one list
  of decisions make a certificate (`certify`), and the node keeps the
  highest. Every proposal is signed, so a certificate carries the signed
  proposals of its signers.
* **Garbage collection.** The horizon rises to `Λ` below the slot round
  of the lesser of the decided and the certified frontiers (§3.4), so
  every slot below a node's horizon is certified by the certificate it
  holds. The horizon therefore waits for checkpoints: without a signing
  quorum it stops rising, and the store grows.
* **Bootstrap.** A peer serves its certificate with its base. The joiner
  adopts a certificate with `q` distinct signers, its decisions those of
  slots `0 … k − 1` in order, and its height's slot round at or above the
  new horizon (`validCert`), outputs the certified decisions it lacks,
  and decides from there on (§3.6). Its decisions have no gap.

**Why one honest signer is enough.** `f < q`, so a certificate's `q`
distinct signers include an honest one. An honest node proposes a
prefix of its own decisions (`Node.Local.Decisions`), and those are
verdicts on views of the run's record (V9's induction). So every
certified decision is one, and V12 holds without the quorum intersection
of the checkpoint model (`checkpointQC_eq_of_same_height`): two
certificates at one height agree because honest nodes' decisions are
prefix-comparable. Finality certificates and the recovery epochs of
`RecoverySpec` are not used.

The certificate grounds the decisions below the horizon, not the blocks
at it; those rest on an honest presenter's store, earlier in the trace.

## 4. Conformance

| | Claim | Route |
|---|---|---|
| V1 | Every block of the program's own, those it persists, satisfies `ValidAt q Clause.distinct`; they lie at strictly increasing rounds, across restarts, resumes and bootstraps; it references only what it knew; the blocks it broadcasts are those it persists; it keeps the decisions it outputs, slots `0 … lo − 1` in order, and every proposal it signs is a prefix of them; its accepted set is a view. | `Node.Local.OneEach`, `Node.Local.Authored`, `Node.Local.Sends`, `Node.Local.Decisions`, `Node.Local.ValidOut` (proved, restarts, resumes and bootstraps included) |
| V2 | The commit outputs are `consumed` over the successive views. | `Node.Local.DecidesOnView`, `Node.ViewsAbove.tryDecide_eq` (proved); `consumed` over the run's record in step 4 |
| V3 | Over a trace, the blocks the honest nodes knew form a `BlockRecord` at quorum `q` whose honest set is the honest nodes, and every honest store is a cut of it; with timely authentication of blocks, an injective hash and `Params.Tolerates`, and no honest node given a base offer or a certificate, any two honest nodes' commit sequences are prefix-comparable, whatever horizons they raise and whenever they restart and resume. | `Node.Runs.Safety` (proved): `Node.authentic_of_timely`, `Node.hashInjective_of_trace`, `Node.globalRecord`, `Node.ground`, `Node.CommitInv.run`, `Scheme.Loop.resume`, `Scheme.Loop.prefixComparable` |
| V3′ | Over a trace with delivery, timely authentication and an injective hash, with no horizon raised, no honest node restarting and none given a base offer or a certificate, every block an honest node broadcast, with its history, ends in every honest node's store. | `Node.Converge.Converges` (proved): `Node.walk_reaches`, `Node.flush_no_ready`, `Node.Converge.chain` |
| V4 | The decisions a store pruned at `G` gives from a slot at or above `G` equal those of every view holding its blocks from `G` up, read at `G`: the loop reads nothing below the slot's round. | `Node.Local.DecidesOnView`, `Node.ViewsAbove.tryDecide_eq`, `Node.ViewsAbove.of_store` (proved) |
| V5 | At every state a run reaches, resuming from what the node persisted gives the state its restart recovers: the same blocks, read alike, at the same horizon, the same next slot, top and own block, its top round's timer fired, and nothing pending or asked for. | `Node.Restart.Resumes` (proved): `Node.resume_persisted`, `Node.State.recover` |
| V6 | Retired: Safe Skip is not part of the program (§3.5). L0, the self-referencing filled block valid at any quorum, stays in the shared layer. | `BlockRecord.selfBlock_valid` (proved) |
| V7 | Rate limiting does not make a validator decide wrongly. | `decided_mono_of_banded` |
| V8 | The efficient store and decider compute the reference program's values. | one equality per function |
| V9 | Over a trace with timely authentication of blocks, base offers and checkpoint proposals, an injective hash and `Params.Tolerates`, every honest store is a cut of the run's record and every honest decision a verdict on a view of it, bootstraps and adopted certificates included; a node's decisions are slots `0, 1, …`; so any two honest nodes' decisions are prefix-comparable. The fetch bound is step 8's. | `Node.Boot.Agrees` (proved): `Node.IsCut.bootFrom`, `Node.IsCut.step`, `Node.verdict_decideStep`, `Node.propose_prefix`, `Node.prefix_of_slots`, `AnchoredRule.decided_agree`; G10 soundness lifted (`exists_honest_attester_of_mem_base`) |
| V10 | Under the novelty budget, every honest block is eventually accepted, and an honest validator's store, with garbage collection, has a size independent of the runtime. | lifted C3 and B4 (§8), `card_retained_le` |
| V12 | Every certificate with `q` distinct signers given to an honest node certifies a prefix of an honest node's decisions, with timely signed proposals and `f < q`. | `Node.Boot.Certified` (proved): `Node.propose_prefix`, `Node.commits_prefix`, `Node.Local.Decisions` |
| V11 | A timed run past GST, with timeouts of at least `2Δ + proc`, gives a `SchemeReactive` and the delivery obligation `DeliversOn`; the mechanisms compose (`Stack.safe_and_live`), and every slot commits. | field by field from the run, V10 |

**The transfer.** The program decides on its own store, a record of its
own; the run's claims are about a view of the run's record. The decider
reads a view and the block map on it alone, so the two give the same
decisions when the store's identifiers are the view's and its block map
agrees on them. This is a lemma about `tryDecide` and the vote rule (for
`leastSel` and `votedBlockSel`, which read only histories), proved in
step 2; `View.toRecord` is the record a view gives.

**Authentication.** A block delivered or offered to an honest node in
an honest author's name was broadcast by that author earlier in the
trace (`Converge.TimelyAuthentic`); at the end of the trace this gives
`Node.Authentic` (`Node.authentic_of_timely`). The program broadcasts
exactly the blocks it persists (`Node.Local.Sends`), so such a block is
one of the author's own, one a round. A block a peer forwards is
covered, since its author broadcast it.

**One run model.** Every claim about many nodes is stated over a trace
(`Model/Trace.lean`), which orders all nodes' inputs in one list. The
order is what bootstrap needs. Without it, two honest nodes could each
bootstrap on the other's offer, made after its own bootstrap, and
nothing would ground the base. Over a trace, by induction, every honest
store is a cut of the run's record. A node bootstraps only at a round
with a block that `f + 1` distinct peers offered, so one of them is
honest. That peer's offer was its store when it served it, earlier in
the trace, and that store was a cut of the record then. So the record
reaches the round, which keeps the node's new base blocks of the record.
Each decision it takes from a certificate is an honest signer's, made
earlier in the trace, so by the same induction it is a verdict too. Each
decision is then a verdict on a view of the record (`Loop.sound`), and
two verdicts on one slot agree. A node's decisions are slots `0, 1, …`,
the certified ones included, so two nodes' decisions are
prefix-comparable (V9). V3 is the case without bootstraps, with fewer
assumptions.

**The run's record is a construction.** The proofs build the run's
record from what the honest nodes knew over the whole trace (`knownOf`):
every block delivered or offered to them with its hash, and every block
of their own, pruned ones included. It is not the union of the honest
stores at any event, and no node computes it; it exists to state the
claims. Each honest store, at each event, is a cut of it.

**The run's record under garbage collection.** A node keeps a block at
its horizon without checking its references (§3.4), so a Byzantine block
there may reference blocks no honest node holds, and the union of the
honest stores is not closed. The run's record (`Node.globalRecord`)
holds the blocks the honest nodes knew at rounds their knowledge reaches:
round `0`, and a round holding a real block, one whose references are
known and which is valid at quorum `q` above such a round
(`Node.Real`, `Node.Lives`). A real block is read as known; another keeps
its round, author and payload and takes the references of a real block
of its round. The record is at `ValidAt q Clause.none`, which reads
neither the self-parent nor the distinctness clause. Every honest store
along every run is a cut of it (`Node.IsCut`): its blocks are the
record's, read without references at the store's horizon. The record
reaches every honest store's horizon (`Node.IsCut.spans`): the store
holds a block at or above the node's top, and the horizon lies at or
below the top (`Node.Held`). Decisions read nothing
below the slot's round (V4), so the loop on a store decides as on a view
of the record, and V3 holds as horizons rise.

**Traces.** A trace is a list of events, each an input to one node. An
honest node changes state only by *step* on its own events. The network
and the adversary choose the events, so a Byzantine node's blocks enter
as delivered blocks, valid or not, since the program checks validity
itself. A crash is the restart input, which keeps what the node
persisted (§5). The trace has no clock; the timed claims of step 11 add
times to its events. The reliable set `T` of a liveness claim is the honest validators
that do not crash over the claim's window. FinWhale's `Run` collects an
execution as an assumed structure; here the run is generated by the
program, and the structures the theorems read (`BlockRecord`, `PaceCore`,
`Delivery`) are built from it.

Three hypotheses belong to the environment, not the program: the hash
is injective on the blocks of a trace, the network meets the delivery
assumptions, and a node's storage writes the state a step leaves at
once, before any of the step's outputs takes effect (§5.1).

## 5. Crashes

### 5.1 What survives

The last own block is not enough. Suppose a Byzantine author sends `X`
to `v` alone, `v` accepts it, builds `B` referencing it, broadcasts `B`
and crashes before any peer has fetched `X`. No correct validator holds
`X`, so none can complete `B`'s history: an honest block is lost, which
breaks `converges` and `holds_mono` of `PaceCore`.

The program therefore persists every block not yet in the common core,
that is, every accepted block from the horizon `G` up, which includes its
own blocks (`State.persisted`). After GST, whatever a correct validator holds by round `m`
every correct store holds by `m + 1` (`viewUpto_subset_viewUpto_succ`),
so a peer can serve whatever lies below the horizon
(`pruned_subset_peer_store`). It also persists `G`, so as not to accept
blocks below it again, `lo` and its decisions, so as not to repeat
commits and to propose them, the height it last proposed and its
certificate, and its top round with its own block there, if any, from
which it resumes building; repeated commits would be identical, since
the loop's restart is idempotent (`Restart`).

A block is persisted before it is broadcast. Otherwise a crash between
the two lets the restarted validator build a different block at the same
round, which is an equivocation.

The model persists the whole state a step leaves, at once, and a crash
falls only between steps. This is an assumption on the node's storage:
it writes the state a step leaves (`State.persisted`) in one atomic
write, as a write-ahead log does, before it sends any of the step's
messages or acts on its other outputs. "Persist before broadcast" is then
the order of a step's outputs. A crash after the write and before a
broadcast loses only the message: the block is in the restarted node's
store, and peers fetch it when the node's next block references it.
Crash points between one step's writes are not modelled. They would
admit a restart that persisted a block but not the top above it, and so
built a second block at that round.

Pending and deferred blocks are not persisted: no own block references
them, and their authors or other peers can serve them again.

With garbage collection the persisted window has a size independent of
the runtime (`card_retained_le`, G6).

### 5.2 What this gives

A crash loses the pending blocks, the timers and the requests, and keeps
the store, the horizon, the next slot and the top. In a trace a
crash is the restart input, which keeps the store as it is and empties
the rest (`State.recover`); `resume` rebuilds a state from what was
persisted, and V5 shows that it gives the same state, its store read
alike. So V1, V3 and V4 cover runs with crashes. The restarted node
counts its downtime as its top round's timer firing, so it builds as
soon as its store allows.

Convergence (V3′) is stated for nodes that do not restart, the reliable
set of the liveness claims: a restart drops the pending blocks, and
nothing asks for them again until a later block needs them. Such nodes
never resume or bootstrap, and V3′ assumes that no honest node is given
a base offer.

A node down long enough that its peers' horizons pass the rounds it
missed cannot catch up by fetching. Its fetches go one round down per
request. Its peers' horizons rise one round per round. The simulator
shows this at `Λ = 2` after six ticks down (§6). Resuming covers the
downtime itself: on restart the node keeps its window, and once its
store holds a quorum two rounds or more above its last own block, it
builds above that round (§3.5). A node down past its peers' horizons
rejoins by bootstrap (§3.6).

## 6. Testing

1. **Agreement with the model.** `#guard` checks in
   `LeanDagTest/Node/` that the program's commits on the scheme's
   hand-built records match those the scheme's tests record.
2. **Differential tests.** The efficient program against the reference
   program on random records of a few rounds.
3. **The simulator** (`LeanDagSim/Net.lean`, `lake exe sim`). `n`
   programs over a seeded network: before GST a message takes up to
   *preMax* ticks, after it between *delayMin* and *delayMax*; crashes
   at given times, and restarts after a downtime; and equivocators, each two copies of the program
   with one identity and different payloads, each copy sending to half
   the nodes. It reports the rounds reached, the slots decided and
   skipped, whether two honest nodes that decide a slot decide it alike,
   whether their decisions are prefix-comparable, whether every honest
   block above round `0` is valid under the blocks the nodes made, and
   the skips and bootstraps the honest nodes made. One
   scenario per row runs in the build (`LeanDagTest/Node/Sim.lean`).
   Compiled, four nodes over 2,000 ticks (874 rounds) run in half a
   second. `lake exe node` runs one node over JSON lines.

   **What it found.** With an equivocator, an honest node that received
   only one twin stalled: the others' blocks referenced the twin it never
   received, and nothing fetched it. Fetching (§3.7) removed the stall.
   An equivocator here is two copies of the honest program, and a copy
   drops blocks that claim its identity, so neither copy accepts blocks
   built on its twin: it stops building and its pending blocks grow.
   From *byzUntil* on it therefore acts on nothing.

   A node down for six ticks restarts and catches up at `Λ = 6` by
   fetching, but not at `Λ = 2`. It asks for the rounds it missed one
   round down per request, and its peers' horizons pass them before it
   gets there. A node that lags leads slots it has not built, and each
   costs the others a timeout, so its rejoining matters to the network,
   not only to itself.

   With resuming (§3.5), bootstrap (§3.6) and checkpoints (§3.8) the
   restarted node rejoins. Over five seeds each, at `Λ` = 2, 6 and 20
   and after 6, 20 and 50 ticks down, it ends within one round of its
   peers, and at most one slot behind them, in all 45 runs; agreement,
   prefix-comparability and validity hold in every run. It resumes in 38
   runs. Bootstraps fall as `Λ` grows: 8 runs at `Λ = 2`, 5 at `Λ = 6`
   and none at `Λ = 20`. The horizon now waits for certificates, which
   lag the decided frontier, so a short downtime is more often caught up
   by fetching alone. Asking for the bases once, at the restart, was not
   enough: in 5 of 15 runs at `Λ = 2` the peers' horizons were not yet
   above the node's top when they answered, and by the time fetching had
   failed the node had nothing to ask on. It asks again as delivered
   blocks rise. Without checkpoints, a bootstrapped node's decisions
   skipped the slots below its new horizon; with them it outputs the
   certified decisions, and its decisions are a prefix of its peers' or
   extend them.
4. **Attacks** (`LeanDagTest/Node/Adversary.lean`, `--adv` and
   `--attacks` of `lake exe sim`). An attacker runs the honest program
   and also mounts attacks:
   - `fakeBase`: it answers base requests with a fabricated base, five
     rounds above its top, of reference-free blocks in every node's name;
   - `splitBase`: as `fakeBase`, with a different base for each requester;
   - `fakeCert`: it serves a certificate of fabricated decisions, every
     slot skipped, listing every node as a signer;
   - `conflictProposals`: it signs two proposals at each height and sends
     each to half the nodes;
   - `invalidBlocks`: with each block it broadcasts one without
     references, one referencing a block that does not exist, and one
     under an identifier that is not its hash;
   - `forgedAuthor`: with each block it broadcasts one in the next node's
     name.

   The network checks signatures (`Scenario.verify`), which is what the
   claims over traces assume (`TimelyAuthentic`, `TimelyOffers`,
   `TimelyCerts`): a block in an honest author's name must be one that
   author made, a certificate's honest signers must have signed its
   decisions at its height, and a message's sender is the node that sent
   it.

   **What it found.** At the Mysticeti row with `n = 4`, node `3`
   attacking, five seeds each, with node `1` down from tick 40 to tick 90,
   down from 40 to 46, or not at all, and the checks on, every attack
   leaves agreement, prefix-comparability and validity intact in all 15
   runs. A fabricated base is never attested, since one presenter is not
   `f + 1`. Conflicting proposals are never certified, since only the
   honest nodes' agree. Invalid blocks cost the attacker its own
   progress: it sends a second genesis block without references, which
   honest nodes keep at the horizon as the cut does, and some of them
   reference it; the attacker drops blocks claiming its identity, never
   completes those histories, and stops building. The others then
   progress as with one crashed node, round for round.

   Without the checks, the assumptions do work the program cannot do.
   A certificate of fabricated decisions is adopted by the joiner in 2 of
   15 runs, and its decisions then disagree with its peers'. Blocks in an
   honest node's name halt that node in all 15 runs, for the same reason
   the attacker halts itself above, and the honest blocks referencing the
   forged ones are invalid under the blocks the nodes made.

   The check that honest blocks are valid reads every block a node made
   or broadcast in its own name under its hash, since an honest block
   may reference an attacker's block that the attacker broadcast but did
   not keep.
5. **Optionally**, replaying records through the Rust decider of the
   Mysticeti codebase, where the scheme's table comes from.

## 7. Steps

| Step | Content |
|---|---|
| 0 | This document; the interface types, all mechanisms' inputs and outputs included (built) |
| 1 | Reference program without mechanisms: *step* over a `Finset` store calling the model's functions; `#guard_msgs` tests (built) |
| 2 | V1 and V2, with the transfer; the timing check (§9) (built) |
| 3 | Simulator and JSON executable (built) |
| 4 | The run model; V3 and convergence of honest blocks and their histories under fetching (§3.7), both without garbage collection (built) |
| 5 | Garbage collection: V4, and V3 with horizons rising; persistence and restart: V5 (built) |
| 6 | Safe Skip: the fill's validity at the program's validity (§8, L0); V6 (built) |
| 7 | Bootstrap in the program: V9 over a trace; G10's soundness lifted to block records (§8, L1) (built) |
| 7.1 | Self-parent as a build rule, not a validity clause (§11): the shared inclusion argument reads it for reliable authors from a round on; the program's validity drops it; a recovering node resumes above the highest round it holds a quorum at; Safe Skip leaves the program; bootstrap needs no reference-free block; block authentication back to a block its author broadcast (built) |
| 7.2 | One run model: V3 proved over a trace, and the model without time retired (§4, *One run model*); the atomic write of a step's state stated as an assumption on the node's storage (§5.1); the run's record described as the proof's construction, not the union of the honest stores (§4) (built) |
| 7.3 | Checkpoints (§3.8): signed proposals of the decided prefix and certificates of `q` of them; the horizon bounded by the certified frontier; bootstrap adopting the certified prefix; V12, and V9 restated as prefix-comparability (built) |
| 7.4 | Adversarial simulation (§6, item 4): Byzantine nodes that send fabricated or inconsistent bases, fabricated certificates, conflicting signed proposals, invalid blocks and blocks in another node's name, with the network's signature checks on and off; each scenario checks agreement, prefix-comparability and validity (built) |
| 8 | Lift the rate-limiting results to block records (§8, L2), and with them the rest of L1: completeness (G10, G11), the bounded fetch (G6b) and the relay obligation (G7), which rest on the same delivery model and novelty budget |
| 9 | Rate limiting in the program: V7, V10; the novelty budget also bounds what a Byzantine node can add to an honest node's pending blocks and requests |
| 10 | Efficient store and decider (history by levels, the bounded vote and the map-backed store built): V8; differential tests; agreement with the model (§6, item 1): the program's commits on the scheme's hand-built records |
| 11 | Liveness: V11, and the fast path: round time bounded by the delivery delay after GST; first, the decisions of §9.1, including the liveness of recovery, of checkpointing and of convergence under garbage collection and rejoin |

Steps 7.1 to 7.4 follow from what steps 5 to 7 found. The self-parent
clause is what made a restarted or bootstrapped node unable to build,
and no safety argument reads it. A run without time cannot ground a
bootstrap. A bootstrapped node's decisions have a gap below its horizon,
which certified checkpoints close. The simulator's adversary has only
equivocated and withheld, while the new messages give it more to forge.

The order proves safety and local conformance of every mechanism before
the two large steps, so that step 10 refines the complete program once
and step 11 proves liveness once, against it. The model's own functions
are too slow to run beyond a few rounds (`historyUptoFrom` recurses
without sharing), which is why step 10 exists. Steps 7 and 8 change the
shared layer and are recorded among the shared-layer steps of
`docs/target-properties.md`.

## 8. Lifting to block records

One small result was missing at the program's validity, and is proved:

* **L0, the fill**: the self-referencing fill block, the donor's
  references plus one self reference, is valid at every predicate
  equivalent to `ValidAt q (Clause.distinct.and Clause.selfParent)`, at
  any quorum (`BlockRecord.selfBlock_valid`, `Record/Fill.lean`). The
  core's fill calls it at `ValidWrt.iff_validAt`.

Two groups of results the program needs are stated on the core's
universe, at `n = 3f + 1` and quorum `quorumCard`, and so hold at the
Mysticeti and Cordial Miners PS rows only. Each is lifted to block
records at a quorum `q` with `2q ≥ n + f + 1`, as `exists_commonCore`
was, with the core's statement kept as the corollary at `q = n − f`.

* **L1, bootstrap**: the attested base and its soundness and
  completeness (G10), window completeness (G11), the bounded fetch
  (G6b), the joiner's view (G12) and the relay obligation (G7), from
  `GC/AttestedBase.lean` and `GC/Bootstrap.lean`, with the depth rule
  (`viewUpto_subset_viewUpto_succ`, `pruned_subset_peer_store`) they rest
  on. The attested base and its soundness are lifted
  (`exists_honest_attester_of_mem_base`, any record with at most `f`
  validators outside its honest set). The rest reads the delivery model
  and the novelty budget, and is lifted with L2 in step 8. The program's
  safety (V9) needs none of it; it rests on the run's record.
* **L2, rate limiting**: the delivery model of `Network/Delivery.lean`
  (`Delivery`, `EventuallyDelivers`), the novelty budget (`UniformBudget`,
  `ByzBudget`), the liveness half (C3) and linear storage (B4) of
  `DoS/Novelty.lean`, and the coverage witness of `DoS/Delivers.lean`.

Step 8 runs in sub-steps, each with the build green: **8.0** a
`Validity.SelfParent` class, which the novelty telescope reads (built);
**8.1** the delivery layer on any record, with `EventuallyDeliversOn D T
R` (built); **8.2** the budgets, C3, B3′ and B4 of `DoS/Novelty.lean` (built);
**8.3** the transfer lemmas of `GC/Chop.lean`, G6 (`card_retained_le`)
and the depth rule (G8, G9) (built); **8.4** the backbone
(`mem_history_of_correct`), G10 completeness, G11, G6b, G12 and G7;
**8.5** the coverage witness of `DoS/Delivers.lean`. The rate-limiting
half needs no quorum: only the honest set, the bound `honestᶜ.card ≤ f`
and the self-parent clause. Completeness needs `q ≤ T.card` and
`n + f + 1 ≤ 2q`, which give `f + 1 ≤ T.card`.

**The delivery assumption** (`EventuallyDeliversOn D T R`): after `R`,
the blocks of every honest author reach every receiver in `T`. A block a
crash-prone validator made before it crashed still reaches the
validators that stay up; so the attestation threshold stays `f + 1`, and
the bounded fetch (G6b) and the Byzantine budget keep their core form.

The hybrid rows have `c` crash-prone validators besides the `f`
Byzantine ones. Crash-prone validators are honest (they do not
equivocate), so the attestation threshold stays `f + 1`; what changes is
that a crashed validator neither presents nor serves, which the lifted
statements take as the reliable set `T` rather than the honest set.

## 9. The timing check

The liveness structures were written as hypotheses, and their witnesses
are hand-built records, not runs of a program. Read against the
program's build rule (§3.2), clause by clause:

| Clause | Met by the program? |
|---|---|
| `SchemeReactive.advancesAt` | yes, once the round's timer fires: the timer stays fired, so a quorum arriving later builds at once; this needs the environment to deliver timer callbacks |
| `SchemeReactive.reach_or_wait`, `cert_or_wait` | yes: the program builds early only when its block reaches, or certifies, a leader block, and otherwise after the timer, referencing every author's block it holds, which includes a reliable leader's or voter's single block |
| `PaceCore.refs_held`, `holds_own`, `holds_closed` | yes, reading `holds` as the accepted blocks |
| `ReactiveCore.deadline` | no: at every round, not only after GST, it asks the next block within `timeout n`; a node holding fewer than `q` authors of round `n` when its timer fires cannot build |
| `ReactiveCore.built_lt` | no: build times strictly increase, but one step may build several rounds at once, when a lagging node catches up |
| `PaceCore.catchup` | no: a node holding a reliable block of a later round must build there within `proc`, while `reach_or_wait` makes it wait the timer at each round in between whose leader block its block would not reach |
| `PaceCore.holds_mono`, `converges` | not under garbage collection: the store shrinks, and a reliable block arriving below a node's horizon is never accepted; logical holdings, everything ever accepted, keep `holds_mono` but not `converges` |

The first three rows are what the liveness proofs consume of the build
rule, and they hold by construction. The last four are idealisations of
time and delivery.

### 9.1 Decisions for step 11

Each of these changes the shared pacing structures (`Mysticeti/ViewPace.lean`,
`Reactive/Basic.lean`) or adds a node-side variant of them, and each
needs the reactive liveness proof checked for where it reads the clause.
They are to be decided at the start of step 11.

1. **`deadline`**: assert it from a round past GST only, as `converges`
   is; before GST no bound on round time is claimed.
2. **`catchup`**: assert it from a round past GST, and let it fall back
   to the timer at a round whose leader block the node does not hold;
   check that drift (`driftOn_of_catchup`) survives the fallback, or
   bound it from `deadline` instead.
3. **`built_lt`**: weaken it to `≤`, if `le_built` is the only reader and
   tolerates it, or charge each build its processing time so that a step
   building several rounds spreads them over time.
4. **Convergence under garbage collection**: read `holds` as the
   accepted blocks above the node's horizon, and state `converges` for
   blocks above the receiver's horizon, as the garbage-collection arc's
   induced delivery does (`garbage.md` §5, G13 and G14). V3′ today
   excludes raised horizons, restarts and base offers; the version
   liveness reads must admit all three.
5. **Recovery**: a restarted node rejoins, by building above a quorum it
   holds (§11) or by bootstrapping. The bootstrap trigger and its
   re-request (§3.6) are tuned in the simulator, not proved; liveness
   needs a bound on when a restarted reliable node builds again, from
   delivery after GST.
6. **Checkpointing**: once the horizon waits on the certified frontier
   (§3.8), garbage collection, storage (V10) and bootstrap all rest on
   certificates forming. Liveness needs that a signing quorum certifies
   every decided prefix within a bound after GST.
7. **Skipping rounds**: the build rule of step 7.1 builds above the
   highest round a node holds a quorum at, which is what `catchup` (item
   2) asks; check whether it meets `catchup` outright.

## 10. Tooling

* The model's functions run under `#eval`. Four changes make them fast
  enough to run the node. `historyUptoFrom` is computed a level at a
  time (`historyLevels`, proved equal and marked `@[csimp]` in
  `Common/Causality.lean`, `docs/target-properties.md` §11.52), which
  removes the exponential cost. The vote rule is `boundedSel`, the least
  vote searched only as deep as the slot, a `VoteSel` that selects what
  `leastSel` selects at every block of a record (`boundedSel_sel_eq`);
  for that the store's record carries `stored`, references one round
  below. The store's block map is an ordered map rather than a chain of
  updates, and garbage collection keeps the store a few rounds deep.
  Four nodes over 16,000 inputs (1,000 rounds) run in about five
  seconds, a third of a millisecond an input, and the cost of an input no
  longer grows with the run; with the model's functions as they were, 60
  inputs was the limit.
* `scripts/check-arc-holes.py` forbids `partial` and `unsafe` in the
  arcs it lists. The directory `LeanDag/Node` is added to its list,
  and the executables' input loops, outside the library, run on fuel.
* The executables are `[[lean_exe]]` targets of `lakefile.toml`, not
  default targets, so `lake build` and the audits are unchanged.

## 11. Self-parent as a build rule (step 7.1, built)

**Why.** The row's validity asks every non-genesis block to reference a
block by its own author. No safety argument reads this: the run's record
already drops it (§4). Liveness reads it once, for inclusion
(`SelfParent.reaches_of_creator`): a reliable author's committed leader
block reaches each earlier block of that author, by walking the author's
chain down. As a validity clause it stopped a node that missed rounds
from building: Safe Skip had to fill the missed rounds with blocks of
its own, and a bootstrapped node, whose own blocks lie below its
horizon, had to start again with a reference-free block invalid at the
row. Both cost more than inclusion needs. Inclusion walks one reliable
author's chain from a committed block down to an earlier one, so it needs
the clause only for reliable authors, and only above the round from which
their chains are unbroken. A node that restarted or bootstrapped is not
reliable across its gap anyway.

**The work.**

1. **The shared layer** (a §11.x step of `docs/target-properties.md`).
   `SelfParent` takes a reliability and a round `R₀`: every block by a
   reliable author above `R₀` references a block by its author. The
   chain walk (`reaches_of_creator`) runs above `R₀`, and inclusion
   (`mem_history_of_decided_commit`, `includes_of_leads`,
   `committed_of_correct_block`, `Support.inclusion`, `Support.liveness`)
   covers reliable blocks above `R₀`. The rules whose validity keeps the
   clause, the core and the rows built on it, prove the new property at
   every reliability and every `R₀` from their validity, so their
   statements are corollaries at `R₀ = 0`. About twenty-five files read
   the property; most only produce it.
2. **Validity.** The node's validity becomes `ValidAt q Clause.distinct`:
   references one round below, from `q` distinct authors, none twice.
   Every block the node builds is valid at the row again, the genesis
   included (V1 as first stated).
3. **The build rule.** A node references its own block of the round
   below when it has one, which is the self-parent rule for honest
   nodes. A node that is not recovering builds rounds in sequence. A
   recovering node resumes at the highest round above its top at which
   its store holds `q` authors, two rounds or more above it if it holds
   its own block at its top, and builds the round above (§3.5); a
   reliable node never resumes, so its chain is unbroken. The node's
   state allows a top without an own block there; `Held` keeps instead
   that the store holds a block at or above the top, which is what
   `Spans` needs. Building above a later quorum is also what the pacing
   clause `catchup` asks (§9), so the rule bears on decision 2 of §9.1.
4. **Safe Skip leaves the program.** The jump input and output, the
   fill derivation (`jumpFills`, `lineDown`, `fillUp`, `insertAll`,
   `tryJump`, `jumpIn`), what jump messages give (`received`,
   `derived`), `Helpers/Fills.lean`, `Helpers/Jumps.lean`, `Node/Jump/`,
   `Runs.AuthenticJumps` and `Boot.TimelyJumps` are deleted. The
   scheme's Safe Skip results and L0 stay in the shared layer; V6 is no
   longer a claim about the program.
5. **Bootstrap without re-genesis.** After pruning to `G` and keeping the
   attested base, the node's top is `G` with no own block there, and it
   builds `G + 1` on the base by the rule of item 3. Its first block after
   a bootstrap is valid at the row, so peers below `G` accept it once they
   hold the base blocks it references.
6. **Authentication.** Every block of a node's own is broadcast and
   signed, so block authentication reads broadcasts, and the program
   broadcasts exactly the blocks it persists (`Node.Local.Sends`).
7. **Simulator.** The simulator has no jump messages; it reports skips
   (a recovering node resuming) and bootstraps, and the recovery sweep of
   §6 is rerun.

**What it gives up.** Inclusion for a node's blocks below a gap in its
chain. Those blocks may still be included through other authors' blocks;
they are no longer guaranteed through their author's own.
