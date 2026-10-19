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

It integrates three mechanisms:

* **garbage collection**, with crash persistence and restart;
* **Safe Skip**, the one-message return after downtime;
* **rate limiting**, the novelty budget on acceptance;
* **bootstrap**, the return of a validator down past the horizon, from
  the attested base.

Two of these rest on results stated on the core's universe only, which
are lifted to block records at quorum `q` first (§8).

Out of scope: stake weights, a mempool (the payload comes from a
configured source), and an implementation of hashing (identifiers are
the environment's hash, assumed injective on the blocks of a run).

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
(`Params.Covered` and `Params.CertFits`, with the commit threshold within `n − f − c`, all decidable) and
refuses a configuration that is not.

**Validity.** Every row uses `ValidAt q (Clause.distinct.and
Clause.selfParent)`: references one round below from `q` distinct
authors, no author twice, and a reference to the author's own previous
block. It is decidable (`ValidAt.decidable`) and mechanised
(`ValidAt.mechanised`), and quorate and distinct by
`Validity.Quorate.of_validAt` and `Validity.Distinct.of_validAt`. The
self-parent clause is what Safe Skip's fill reads (§3.5).

**Inputs.**

* a start, with no persisted state: the program builds its genesis
  block;
* a delivered block: identifier, round, author, ordered references,
  payload;
* a delivered jump message (`JumpMsg`);
* a timer for round `r` that fired;
* a crash and restart: the node keeps only what it persisted (§5.1);
* a base offer from a peer: its round-`G` blocks and its window above
  them (§3.6);
* a base request from a peer;
* a request from a peer for some blocks (§3.7).

**Outputs.**

* persist one of its own blocks, emitted before the block is broadcast,
  and for a filled block before the jump message;
* broadcast a block;
* broadcast a jump message;
* set a timer for round `r`;
* commit slot `k` with a decision `Option BlockId`;
* prune below the horizon `G`;
* request the base from the peers;
* serve the base and window to a peer;
* ask every peer for some blocks (§3.7);
* send a block to one peer.

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
including the validator's own previous block, choosing the least
identifier between twins. The program builds rounds in sequence and
skips them only by jumping (§3.5) or by bootstrapping (§3.6). It persists the block and the accepted blocks of the
window it references, then broadcasts it, then sets the timer for round
`r + 1`.

### 3.3 The decider

After each step the program runs `tryDecide p σ U V lo N` on its view,
where `lo` is the slot after the last decision output and `N` the last
slot whose decision round it holds, and outputs the new decisions. Over
successive views this is `consumed`.

### 3.4 Garbage collection

The horizon is `G = min(F, t) − Λ`, where `F` is the decided frontier,
the round of the first undecided slot, below which every slot is
decided, and `t` the node's round (the depth rule of `garbage.md` §6).
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

### 3.5 Safe Skip

After a restart whose downtime the network has moved past, the program
sends one jump message `(v1, B1, v2, B2)` instead of building every
missed round (`tryJump`). A restarted node jumps once, when its own
block `B1` lies at its top round `r0` and the store's top round `R` is
at least `r0 + 2`. The donor `B2` is the least block at `R` by another
author. The line runs down from `B2` along references by `B2`'s author,
the least where there are several (`lineDown`). Each round `k` with
`r0 < k ≤ R` gets a filled block by `v1` (`jumpFills`, `fillUp`): the
references and payload of the line's round-`k` block, plus `v1`'s block
of round `k − 1`, which is `B1` at the bottom. Its identifier is its hash.
The node accepts the filled blocks in turn, each checked as a built
block is (`insertAll`), and persists them; then it sends the message.
Its top becomes `R`, and the timer of round `R` counts as fired.

A receiver takes the filled blocks from its own store (`jumpIn`). It
needs `B1` at or above its horizon and the line above `B1`'s round, and
it accepts the blocks as it accepts delivered ones. A receiver that
lacks the line fetches the filled blocks as it fetches any missing
block, and the jumping node answers from its store. Where both stores
hold a block above `B1`'s round, they hold the same block under its hash,
so the receiver derives the blocks the sender made (V6). The core proves
this on universes (`JumpMsg`, SS10 of `SafeSkip/Jump.lean`).

### 3.6 Bootstrap

A validator whose last own block lies below its peers' horizons cannot
rejoin from its window, because the blocks its window references are
pruned. A restarted node asks every peer for its base. It asks again
whenever a delivered block lies `Λ + 2` rounds above the one it last
asked on. A peer answers with its horizon and its store
(`State.window`).

The node keeps each base offered, one per peer (`State.offers`). A block
is attested at round `G` when `f + 1` distinct peers offered it at that
round, a presenter's attestation being its own offer (G10, `garbage.md`
§7; `baseAt`). The node bootstraps at the highest offered horizon above
its top that has an attested block (`bootRound`, `tryBoot`):

* it prunes its store to `G` and keeps the attested blocks there;
* it restarts its own chain with a reference-free block at `G`, which it
  persists and broadcasts, as the core's re-genesis does
  (`Integration/ReGenesis.lean`);
* it takes the offered blocks above `G`, and its own pending blocks at or
  above it, as pending;
* it moves its next slot up to the first at or above `G`.

The node stays recovering, so it jumps from its new chain once it holds
a line above it (§3.5). A peer at a lower horizon rejects the
reference-free block until its own horizon reaches `G`, as the core's
re-genesis requires. The node decides no slot below `G`, so its
decisions have a gap and need not be a prefix of another node's. What
holds is that two honest nodes that decide a slot decide it alike (V9).

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

## 4. Conformance

| | Claim | Route |
|---|---|---|
| V1 | Every block of the program's own, those it persists, filled blocks included, with references satisfies `ValidAt q C`; one without is a genesis or a bootstrap's; they lie at strictly increasing rounds, across restarts, jumps and bootstraps; it references only what it knew; its accepted set is a view. | `Node.Local.OneEach`, `Node.Local.Authored`, `Node.Local.ValidOut`, `Node.Local.Shape` (proved, restarts, jumps and bootstraps included) |
| V2 | The commit outputs are `consumed` over the successive views. | `Node.Local.DecidesOnView`, `Node.ViewsAbove.tryDecide_eq` (proved); `consumed` over the run's record in step 4 |
| V3 | In a run of honest nodes over any inputs, the blocks the honest nodes knew form a `BlockRecord` at quorum `q` whose honest set is the honest nodes, and every store along every run is a cut of it; under authentication of blocks and of jump messages, an injective hash and `Params.Tolerates`, with no honest node given a base offer, any two honest nodes' commit sequences are prefix-comparable, whatever horizons they raise and whenever they jump. | `Node.Runs.Safety` (proved): `Node.globalRecord`, `Node.ground`, `Node.CommitInv.run`, `Scheme.Loop.resume`, `Scheme.Loop.prefixComparable` |
| V3′ | Over a trace with delivery, timely authentication and an injective hash, with no horizon raised, no honest node restarting and none given a jump message or a base offer, every block an honest node broadcast, with its history, ends in every honest node's store. | `Node.Converge.Converges` (proved): `Node.walk_reaches`, `Node.flush_no_ready`, `Node.Converge.chain` |
| V4 | The decisions a store pruned at `G` gives from a slot at or above `G` equal those of every view holding its blocks from `G` up, read at `G`: the loop reads nothing below the slot's round. | `Node.Local.DecidesOnView`, `Node.ViewsAbove.tryDecide_eq`, `Node.ViewsAbove.of_store` (proved) |
| V5 | At every state a run reaches, resuming from what the node persisted gives the state its restart recovers: the same blocks, read alike, at the same horizon, the same next slot, top and own block, its top round's timer fired, and nothing pending or asked for. | `Node.Restart.Resumes` (proved): `Node.resume_persisted`, `Node.State.recover` |
| V6 | Under authenticated jump messages and an injective hash, every block an honest node derived from a jump message in an honest node's name is one of that node's own; the self-referencing filled block is valid at the program's validity at any quorum (L0). | `Node.Jump.Derives` (proved): `Node.derived_persisted`, `Node.jumpFills_congr`; `BlockRecord.selfBlock_valid` (proved) |
| V7 | Rate limiting does not make a validator decide wrongly. | `decided_mono_of_banded` |
| V8 | The efficient store and decider compute the reference program's values. | one equality per function |
| V9 | Over a trace with timely authentication of blocks, jump messages and base offers, an injective hash and `Params.Tolerates`, every honest store is a cut of the run's record, bootstraps included, so two honest nodes that decide a slot decide it alike. The fetch bound is step 8's. | `Node.Boot.Agrees` (proved): `Node.IsCut.boot`, `Node.IsCut.step`, `Node.verdict_decideStep`, `AnchoredRule.decided_agree`; G10 soundness lifted (`exists_honest_attester_of_mem_base`) |
| V10 | Under the novelty budget, every honest block is eventually accepted, and an honest validator's store, with garbage collection, has a size independent of the runtime. | lifted C3 and B4 (§8), `card_retained_le` |
| V11 | A timed run past GST, with timeouts of at least `2Δ + proc`, gives a `SchemeReactive` and the delivery obligation `DeliversOn`; the mechanisms compose (`Stack.safe_and_live`), and every slot commits. | field by field from the run, V10 |

**The transfer.** The program decides on its own store, a record of its
own; the run's claims are about a view of the run's record. The decider
reads a view and the block map on it alone, so the two give the same
decisions when the store's identifiers are the view's and its block map
agrees on them. This is a lemma about `tryDecide` and the vote rule (for
`leastSel` and `votedBlockSel`, which read only histories), proved in
step 2; `View.toRecord` is the record a view gives.

**Jumps in the run's record.** What an honest node knew includes the
blocks its jump messages gave it (`derived`). These need no assumption
of their own. A jump message in an honest node's name is one that node
sent (`AuthenticJumps`). The receiver's store and the sender's then read
alike above the sender's last block, so a derived block is one the
sender made (V6). The filled blocks are therefore blocks of the record
like any other, one per round of their author, and the record needs no
before and after the fill. The scheme's statements about the fill as an
extension (`decided_fill_of_persist`, `decided_none_of_novel`) are not
needed at the node, and the prompt skip of a slot that the jumping node
leads at a filled round is not proved there. Authentication covers a
filled block that a peer forwards (`Authentic` reads the author's own
blocks, not its broadcasts), as a signed later block of its author
would, through the hash.

**Bootstraps need time.** A run without time cannot order a bootstrap
after the offers it rests on. Two honest nodes could each bootstrap on
the other's offer, made after its own bootstrap, and nothing would ground
the base. V3 is therefore stated for runs in which no honest node is
given a base offer, and V9 over a trace. There, by induction over the
trace, every honest store is a cut of the run's record. A node
bootstraps only at a round with a block that `f + 1` distinct peers
offered, so one of them is honest. That peer's offer was its store when
it served it, earlier in the trace, and that store was a cut of the
record then. So the record reaches the round, which is what keeps the
node's new base, and its reference-free block there, blocks of the
record. Each decision is then a verdict on a view of the record
(`Loop.sound`), and two verdicts on one slot agree.

**The run's record under garbage collection.** A node keeps a block at
its horizon without checking its references (§3.4), so a Byzantine block
there may reference blocks no honest node holds, and the union of the
honest stores is not closed. The run's record (`Node.globalRecord`)
holds the blocks the honest nodes knew at rounds their knowledge reaches:
round `0`, and a round holding a real block, one whose references are
known and which is valid at quorum `q` above such a round
(`Node.Real`, `Node.Lives`). A real block is read as known; another keeps
its round, author and payload and takes the references of a real block
of its round. The record is at `ValidAt q Clause.none`, without the
self-parent clause, which only Safe Skip reads. Every honest store along
every run is a cut of it (`Node.IsCut`): its blocks are the record's,
read without references at the store's horizon. A block at a horizon
always has a real block of its round, the node's own, since the horizon
lies at or below the node's round (`Node.Held`). Decisions read nothing
below the slot's round (V4), so the loop on a store decides as on a view
of the record, and V3 holds as horizons rise.

**Runs.** A run is a sequence of timestamped events over a global state:
the honest validators' states, the messages in flight, and the
adversary's blocks. An honest validator changes state only by *step*; a
Byzantine one injects any block, valid or not, since the program checks
validity itself; a crash discards a validator's state but its persisted
part. The reliable set `T` of a liveness claim is the honest validators
that do not crash over the claim's window. FinWhale's `Run` collects an
execution as an assumed structure; here the run is generated by the
program, and the structures the theorems read (`BlockRecord`, `PaceCore`,
`Delivery`) are built from it.

Two hypotheses belong to the environment, not the program: the hash is
injective on the blocks of a run, and the network meets the delivery
assumptions.

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
blocks below it again, `lo`, so as not to repeat commits, and its own
block at its top round, from which it resumes building; repeated commits
would be identical, since the loop's restart is idempotent (`Restart`).

A block is persisted before it is broadcast. Otherwise a crash between
the two lets the restarted validator build a different block at the same
round, which is an equivocation.

Pending and deferred blocks are not persisted: no own block references
them, and their authors or other peers can serve them again.

With garbage collection the persisted window has a size independent of
the runtime (`card_retained_le`, G6).

### 5.2 What this gives

A crash loses the pending blocks, the timers and the requests, and keeps
the store, the horizon, the next slot and the top. In the run model a
crash is the restart input, which keeps the store as it is and empties
the rest (`State.recover`); `resume` rebuilds a state from what was
persisted, and V5 shows that it gives the same state, its store read
alike. So V1, V3 and V4 cover runs with crashes. The restarted node
counts its downtime as its top round's timer firing, so it builds as
soon as its store allows.

Convergence (V3′) is stated for nodes that do not restart, the reliable
set of the liveness claims: a restart drops the pending blocks, and
nothing asks for them again until a later block needs them. Such nodes
never jump, and V3′ assumes that no honest node is given a jump message.

A node down long enough that its peers' horizons pass the rounds it
missed cannot catch up by fetching. Its fetches go one round down per
request. Its peers' horizons rise one round per round. The simulator
shows this at `Λ = 2` after six ticks down (§6). Safe Skip covers the
downtime itself: on restart the validator is at its last own block `B1`
with its window intact, and once it holds a block two rounds or more
above it, with that block's line, it jumps there. A validator down past
its peers' horizons never holds the line, and rejoins by bootstrap
(§3.6).

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
   block with references is valid under the blocks the nodes made, and
   the jump messages and bootstraps the honest nodes made. One
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

   A node down for six ticks restarts and catches up at `Λ = 6`, but not
   at `Λ = 2`. It asks for the rounds it missed one round down per
   request, and its peers' horizons pass them before it gets there.
   With Safe Skip the restarted node jumps once it has fetched a line,
   and every node reaches more rounds by tick 150:

   | Λ | ticks down | rounds, no jump | rounds, with jump |
   |---|---|---|---|
   | 6 | 6 | 57 | 63–64 |
   | 6 | 20 | 51 | 58 |
   | 20 | 50 | 37 | 44 |

   The gain is the network's, not only the restarted node's. A node that
   lags leads slots it has not built, and each costs the others a
   timeout. At `Λ = 2` nothing changes: the node never holds the line.

   With bootstrap the restarted node rejoins at `Λ = 2` as well. Over
   five seeds each, at `Λ = 2` and `Λ = 6` and after 6, 20 and 50 ticks
   down, it ends within a round of its peers in all 30 runs. Agreement
   and validity hold in every run. Asking for the bases once, at the
   restart, was not enough: in 5 of 15 runs at `Λ = 2` the peers'
   horizons were not yet above the node's top when they answered, and by
   the time fetching had failed the node had nothing to ask on. It now
   asks again as delivered blocks rise, which gave 15 of 15. A
   bootstrapped node's decisions skip the slots below its new horizon,
   so they are not a prefix of its peers'; the simulator therefore checks
   agreement slot by slot.
4. **Optionally**, replaying records through the Rust decider of the
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
| 8 | Lift the rate-limiting results to block records (§8, L2), and with them the rest of L1: completeness (G10, G11), the bounded fetch (G6b) and the relay obligation (G7), which rest on the same delivery model and novelty budget |
| 9 | Rate limiting in the program: V7, V10 |
| 10 | Efficient store and decider (history by levels, the bounded vote and the map-backed store built): V8; differential tests |
| 11 | Liveness: V11, and the fast path: round time bounded by the delivery delay after GST; first, the decisions of §9.1 |

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
   induced delivery does (`garbage.md` §5, G13 and G14).

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
