# Sync by causal streams

## 1. Scope

This document describes a model of a sync mechanism for the node of
`docs/validator.md`, in `LeanDag/Node/Sync`. The model sits beside the
node's program and is not part of it: the program fetches missing
histories through `missing` and the pruned answer (section 3.4 of
`docs/validator.md`), and keeps every received block whose references it lacks in
`pending`, which has no bound.

In the model, a node runs one sync for each other node. The sync's
target is the highest block that node announced and the requester does
not hold. The requester asks the target's creator, which streams the
target's missing history in order of round. A node that has detected an
equivocator syncs no block of it.

Four claims are proved (§4). The time a block takes to reach the honest
nodes is studied with a simulation (§5), `scripts/sync-prefeed.py`.

Blocks are named by identifier, and a single function `blk` gives what
each identifier denotes: the hash is taken to be injective. Signatures
are not modelled; an announced block whose creator is not the announcer
is ignored.

## 2. One sync

`LeanDag/Node/Sync/Model/Stream.lean`.

**The request.** The requester holds the blocks `S` and has detected the
authors `D`. It sends the target `t`, the identifiers `X` it asks for by
name, and its frontier (`frontierOf`): for each author `a ∉ D`, the
least round `k` at which `S` holds no block of `a` (`frontier`), and `0`
for `a ∈ D`. Below its frontier for `a`, `S` holds a block of `a` at
every round (`frontier_sound`).

**The stream.** A responder holding `R` streams the blocks of `R` in the
history of `t` that are `t`, are in `X`, or lie at or above their
author's frontier (`streamed`), in order of round (`stream`).

**Taking a stream in.** The requester accepts each streamed block whose
references it holds, one round below it, and drops the others (`Ready`,
`absorb`). Nothing is kept pending.

**Gaps.** The frontier says which rounds of an author the requester
holds, not which blocks. A block of `a` below `a`'s frontier is left out
of the stream; if the requester holds a different block of `a` at that
round, a streamed block that references the left-out one is not ready on
arrival. This is a gap, and it occurs only at a twin: two distinct
blocks of one author at one round (`Twins`).

**Passes.** A pass requests, takes the stream in, records the authors of
streamed blocks that have a twin among the blocks held (`exposes`), and
records the references of streamed blocks that are still missing
(`missing`), which the next pass asks for by name (`pass`).

## 3. The node and the network

`LeanDag/Node/Sync/Model/Net.lean`.

**A node** (`State`) holds its blocks, the authors it has detected, and
for each other node the target of its sync. Its inputs (`Input`) are an
announcement of a node's latest block, a piece of a node's stream, and a
block it builds itself (`step`):

* an announced block becomes the target of the announcer's sync if the
  announcer is another node, is not detected, created the block, and the
  block is not held and lies above the current target;
* a piece of a stream is taken in by `absorb`; the authors it exposes are
  detected, and the targets of detected authors and the targets now held
  are dropped;
* a block the node builds is its own and ready.

**Pending blocks** are the targets (`pending`).

**A trace** (`Trace`, `stateBefore`) lists the events, each a node and its
input. Honest nodes stream only what they hold (`Faithful`).
`fromOutside` counts the blocks honest nodes receive from nodes outside
the honest set `H`, and `RateBounded` caps at `k` the blocks an honest
node receives from one node outside `H` at one time.

## 4. Claims

| | Claim | Lean |
|---|---|---|
| S1 | **A sync completes.** From a responder whose blocks are closed under references, each one round below its referrer, a sync of a block it holds leaves the block held within `2e + 1` passes, for `e` the equivocators of the responder's blocks against the requester's (`equivocators`). With no equivocator, one pass suffices. | `Node.Sync.Completes` (proved): `Node.Sync.absorb_all`, `Node.Sync.exists_unstreamed`, `Node.Sync.detects_next`, `Node.Sync.card_ge_of_fails` |
| S2 | **Pending is bounded.** Under any inputs, a node's pending blocks are at most one for each other node it has not detected. | `Node.Sync.PendingBounded` (proved): `Node.Sync.run_clean`, `Node.Sync.pending_subset` |
| S3 | **No amplification.** Over a trace in which honest nodes stream only what they hold, the blocks of authors outside `H` on an honest node's disk number at most the blocks honest nodes received from nodes outside `H`. | `Node.Sync.NoAmplification` (proved): `Node.Sync.entry`, `Node.Sync.card_outside_le` |
| S4 | **The rate bound.** If moreover an honest node receives at most `k` blocks at a time from each node outside `H`, then by time `t` the blocks of authors outside `H` on an honest disk number at most `|H| · |Hᶜ| · k · (t + 1)`. | `Node.Sync.RateBound` (proved): `Node.Sync.fromOutside_le` |

`Node.Sync.holds` proves the four together, with the standard axioms.

**Why a sync completes.** A stream in order of round, each of whose
blocks has its references held or streamed, is taken in whole
(`absorb_all`). If the target is not taken in, some streamed block has a
reference `y` neither held nor streamed (`exists_unstreamed`). Then `y`
lies below its author's frontier, so the requester holds a twin of `y`,
and `y`'s author is not detected. The next pass asks for `y` by name, and
the pass after it receives `y` and detects its author (`detects_next`).
So each failing pass adds an equivocator to the detected authors within
two passes, and there are `e` of them.

**Why there is no amplification.** A block enters a disk only from a
stream or by the node's own build (`step_disk`). An honest node streams
only blocks on its disk. So a block of an author outside `H` on an honest
disk was first received by some honest node from a node outside `H`
(`entry`).

## 5. Latency: the prefeed attack

S4 bounds the rate at which blocks of authors outside `H` reach honest
disks. It does not bound how many of them one honest block brings into
the histories at once, and that number decides how long the other
honest nodes take to accept the block.

**The attack.** A node downloads a history over many rounds, and
references a block only in the round in which the block's last
missing blocks arrive. Let `X` and `Y` be Byzantine.

* `X` makes a fresh chain of its own blocks down to round `1`, one per
  round, each referencing honest blocks of the round below, so each is
  valid at the row.
* `Y` streams to one honest node `w`, and to nobody else. `Y`'s blocks
  reference `Y`'s previous block, so a chain referenced by one `Y` block
  lies in the history of every later one.
* `w` downloads the chain in the background, and references the first
  `Y` block whose history it holds whole. `w`'s next block then carries
  the whole chain.
* Every other honest node must fetch the chain through `w`'s stream
  before it can accept `w`'s block. At `n = 7`, `q = 5`, with `X` and `Y`
  sending nothing else, a quorum needs `w`'s block.

`Y` never equivocates, so it is never detected, and `X`'s twins on
`w`'s disk do not stop the attack. The first chain is valid under the
`DoS` arc's `DoSValid`: no block holding it in its history holds a twin
of `X`. The later releases of the simulation are not, since `Y`'s later
blocks hold two chains of `X` and reference `X`. Under `DoSValid` a block
that references a block of `X` holds no twin of `X` in its history, and a
valid block references honest blocks of the round below; so once one
chain of `X` is in the honest nodes' histories, no valid block brings in
a second, and each Byzantine author serves for one chain. The delay of
that one release still grows with the round at which it comes.

**The simulation** (`scripts/sync-prefeed.py`) runs five honest nodes
building a round once they hold `q` authors of the round below, one sync
per peer streaming `k = 8` blocks a tick with one tick of delay, over
3,000 ticks. `X`'s chain is renewed every 40 rounds.

| | Rounds | Longest round | Blocks on `w`'s disk | On another honest disk |
|---|---|---|---|---|
| No attack | 1,500 | 2 ticks | 9,003 | 9,001 |
| Prefeed | 1,145 | 82 ticks | 19,287 | 11,831 |
| Prefeed, budget `τ = 14` | 1,500 | 2 ticks | 26,703 | 7,542 |

Under the prefeed, the round after a release at round `r` takes about
`r/k` ticks: 7 at round 43, 39 at round 299, 81 at round 640. The delay
grows with the run. It ends after round 642 only because `Y`'s blocks
carry every chain `X` made, so `w` falls behind on `Y`'s stream for good;
an attacker that drops old chains keeps it going.

**The budget.** In the last row an honest node references a block only
if the block's history adds at most `τ` blocks to the history of the
node's own last block. This is the `DoS` arc's `UniformBudget`, measured
against the blocks the node has referenced rather than the blocks it
holds. `w` then never references a `Y` block after the first chain, and
the rounds keep their pace; `w`'s disk still takes `Y`'s stream, as S4
allows. With `τ` from 7 to 14 no round takes more than 2 ticks; with
`τ = 50` the first chain, 42 blocks, passes, and its round takes 7
ticks. With or without the attack, a budget of `7` or `14` excludes no
honest block.

## 6. Open

* **The budget is not modelled in Lean.** An honest block then adds at
  most `1 + (n − 1)·τ` blocks to its author's last block's history, which
  is immediate. That honest blocks always pass the budget is the hard
  half, as in the `DoS` arc (`card_novelty_le_viewGap_add_one`); it needs
  a bound on what one honest node holds that another has not received.
* **Liveness.** The node's V11 assumes synchronisation of the network
  (`SyncedWithin`, section 5.1 of `docs/validator.md`); deriving it from these
  syncs, with the budget, is open.
* **Answers.** The cost of answering requests from nodes outside `H` is
  not bounded.
