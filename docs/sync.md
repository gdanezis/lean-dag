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

Five claims are proved (§4). The time a block takes to reach the honest
nodes is studied with a simulation (§5), `scripts/sync-prefeed.py`,
reference budgets with another (§6), `scripts/sync-budget.py`, and the
blocks a node processes after GST with equivocation reports with a third
(§7), `scripts/sync-reports.py`.

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

`LeanDag/Node/Sync/Model/Check.lean`, `LeanDag/Node/Sync/Model/Net.lean`.

**Checks.** A block carries evidence: pairs of identifiers its payload
names as twins, read by a function `ev`. A block exposes `X` when its
history holds twins by `X`, or a block carrying evidence against `X`
(`Exposes`). A block passes the checks when its references sit one round
below it, name a quorum of `n − f` authors unless it is at round `0`, and
name no author it exposes (`Checks`): the quorum of block validity and
`DoSValid` of the `DoS` arc, with evidence counted as exposure. A target is
admitted when every block of its history passes the checks (`Admits`): a
pass over the headers before the stream. The authors a set of blocks
catches are those with twins in it and those its blocks carry evidence
against (`caught`).

**A node** (`State`) holds its blocks, the authors it has detected, and
for each other node the target of its sync. Its inputs (`Input`) are an
announcement of a node's latest block, a piece of a node's stream, a block
it builds itself, and a report of twins (`step`):

* an announced block becomes the target of the announcer's sync if the
  announcer is another node, is not detected, created the block, and the
  block is not held, lies above the current target and is admitted;
* a piece of a stream is taken in by `absorb`, keeping only blocks of the
  history of the sender's target; the authors it exposes and the authors
  the disk catches are detected, and the targets of detected authors and
  the targets now held are dropped (`settle`);
* a block the node builds is its own, ready, and passes the checks; the
  authors the disk then catches are detected;
* a report of two blocks that are twins detects their author.

A stream from an honest node for an admitted target holds only blocks of
the target's history, so the filter removes nothing from it, and S1
describes such a sync unchanged.

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
| S5 | **The exposure bound.** Let `|Hᶜ| ≤ f < n/2`, let honest authors have no twins, and let every honest admitted block of round `m + 1` expose every author an honest node `v` has detected. Then `v` holds at most `n + |D|` blocks of each round from `m + 1` on, for `D` the authors it has detected: at most one of each author not detected, and at most two of each detected author. | `Node.Sync.ExposureBound` (proved): `Node.Sync.run_good`, `Node.Sync.eq_of_mem_admitted`, `Node.Sync.run_count`, `Node.Sync.card_round_le` |

`Node.Sync.holds` proves the five together, with the standard axioms.

**Why a sync completes.** A stream in order of round, each of whose
blocks has its references held or streamed, is taken in whole
(`absorb_all`). If the target is not taken in, some streamed block has a
reference `y` neither held nor streamed (`exists_unstreamed`). Then `y`
lies below its author's frontier, so the requester holds a twin of `y`,
and `y`'s author is not detected. The next pass asks for `y` by name, and
the pass after it receives `y` and detects its author (`detects_next`).
So each failing pass adds an equivocator to the detected authors within
two passes, and there are `e` of them.

**Why the exposure bound holds.** Two blocks of one author at one round
on the disk are caught, so their author is detected; an author not
detected holds at most one block a round. An admitted history is closed
under references (`causalStructure_historyFrom`), and its blocks are
quorate and name no author they expose. Every block references a block of
an honest author one round below, so once every honest block of round
`m + 1` exposes `X`, so does every block from round `m + 2` on, and none of
them names `X` (D17, `exposed_of_correct_exposed`). A block of an admitted
history other than its top is named by a block one round above it, so no
such block of round `m + 1` or above is by `X` (D27,
`creator_ne_of_correct_exposed`). A stream is taken in only from the
history of the sender's target, so it brings at most the target itself
among the blocks of `X` from round `m + 1` on, and only while `X`, its
author, is not detected. A second block of `X` at one round detects `X`,
after which `X` has no target: two blocks a round at most.

The premise is what reports supply after GST. A node that detects `X`
reports the twins to every honest node and carries the evidence in its
blocks, so once the reports have arrived, every honest block built after
exposes `X`. S5 does not model time: the delivery of reports and the
round from which the premise holds are argued in §7, and studied there by
simulation.

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

## 6. Budgets and catch-up

A budget must never stop a node referencing the honest blocks it needs
for a quorum. The simulation `scripts/sync-budget.py` tries three rules,
each comparing a candidate block's history with the history of the
node's own last block: at most `τ` new blocks (`plain`); at most `τ` new
blocks of each author (`per-author`); at most `τ` new blocks reached by
held blocks of at most `f` authors (`vouched`). Over 600 ticks, with
`τ = 14`, in rounds reached and the longest round in ticks:

| Scenario | No budget | `plain` | `per-author` | `vouched` |
|---|---|---|---|---|
| No attack | 300, 2 | 300, 2 | 300, 2 | 300, 2 |
| Prefeed (§5) | 256, 28 | 300, 2 | 300, 2 | 300, 2 |
| `Y` names a fresh chain of depth 13 each round | 243, 3 | **17** | 243, 3 | 243, 3 |
| `X` and `Y` each show node 0 a private chain of depth 13 | 281, 5 | **21** | 281, 5 | **21** |
| Node 4 slow until tick 200, `Y` applying the rule | 300 | 300 | 300 | 300 |
| Node 4 slow until tick 200, `Y` relaying | 300 | **141** | **141** | **141** |

In the bold cells every honest node stops. Chain depth 13 makes `Y`'s
block add exactly `τ` blocks at its client, so the client's next block
adds `τ + 1` everywhere else and is refused; with two private chains the
client's block holds `2τ` blocks reached by two authors each.

**Catch-up.** A node that falls behind builds every round it missed,
each block referencing its own block of the round below, so its next
block at the frontier carries a chain of its own blocks, one a round,
that no other node referenced. This is the shape of a prefeed. In the
last two rows node 4 falls 140 rounds behind and catches up. With `Y`
applying the rule, the other nodes never reference node 4's blocks
again (no reference after tick 250, against 800 without a budget). With
`Y` referencing node 4's catch-up block, `Y`'s block carries the chain
too; nodes 0 to 3 refuse both and hold only four authors, and every
node stops at round 141.

So no rule that refuses a prefeed chain admits the catch-up chain of an
honest node that fell as far behind, and the lemma that a reliable node
always admits the reliable blocks it needs is false for all three rules.
Rounds have no least duration, so a reliable node can fall arbitrarily
far behind its peers in rounds within `Δ`.

## 7. Processing after GST: equivocation reports

S4 bounds the Byzantine blocks on an honest disk by a rate, which grows
with time. After GST a bound per round holds instead, independent of time,
if detection spreads to every honest node.

**The rule.** A node that holds twins of `X`, or a block carrying evidence
against `X`, convicts `X`: it reports the pair to every honest node and
carries the evidence in its next blocks. It builds no block within `Δ` of a
conviction, so its blocks exposing `X` reach other honest nodes after the
report does. From GST + `Δ` on, a target whose history exposes an author
the node has not convicted cannot be an honest block, so the node ends the
sync from that peer. An honest node never refuses to build on a history
that contains twins, which would stop the protocol, since honest nodes
that referenced different twins before anyone noticed must be merged.

**Why it gives S5's premise.** A report reaches every honest node within
`Δ` after GST, and every honest block built after it exposes `X`. So the
premise of S5 holds from one round above the highest round an honest node
built at before every honest node held the report. There are at most `f`
equivocators, so at most `f` such rounds; before each, S4's rate bound
holds.

**The simulation** (`scripts/sync-reports.py`) runs the honest nodes of
`n = 7, f = 2` and `n = 10, f = 3` over 900 ticks, GST at tick 200,
`Δ = 3`, horizon `L = 20`, with three rules: none, `DoSValid` alone, and
`DoSValid` with reports (`rep`). The table gives the blocks a node
processes per round between ticks 400 and 900, all / Byzantine, at
`n = 10, f = 3`, for the node that processes most:

| Attack | No rule | `DoSValid` | Reports |
|---|---|---|---|
| No attack | 6.1 / 0 | 6.1 / 0 | 6.1 / 0 |
| `X` chain to node 0 every 40 rounds | 9.5 / 3.0 | 9.5 / 3.0 | 9.5 / 3.0 |
| `Y` carries a fresh `X` chain each round | 20.1 / 14.0 | 6.0 / 0 | 6.0 / 0 |
| `Y` announces a tree of twins each round | 69.1 / 63.0 | 6.0 / 0 | 6.0 / 0 |
| a tree of twins for each node, each round | 454.3 / 447.4 | 6.0 / 0 | 6.0 / 0 |
| fresh chains of length 5 from every Byzantine author | 137.2 / 130.9 | 6.0 / 0 | 6.0 / 0 |
| `X` gives each node its own twin, `Y` relays one | 15.1 / 8.0 | 8.2 / 2.0 | 6.0 / 0 |

With reports, a node processes the other honest blocks of each round and
no Byzantine block, except in the first row, where each Byzantine author
holds one block a round and none equivocates within the horizon: the
`n − |D|` of S5. `DoSValid` alone fails on the last row: no single history
holds both twins of `X`, so `X` is never exposed, and `Y`'s blocks carry a
block of `X` into honest histories every round. No honest node stops: the
rounds reached match the run without attack, and no node ends a sync from
an honest peer. `n = 7, f = 2` gives the same picture.

## 8. Open

* **A budget that admits honest blocks.** §6 rules out the three rules
  tried as they stand. The catch-up chain reaches the frontier block only
  through the node's references to its own blocks.
* **The premise of S5 in time.** The rounds from which every honest
  admitted block exposes the detected authors are argued in §7, not
  proved; the model has no clock.
* **Liveness.** The node's V11 assumes synchronisation of the network
  (`SyncedWithin`, section 5.1 of `docs/validator.md`); deriving it from these
  syncs, with the budget, is open.
* **Answers.** The cost of answering requests from nodes outside `H` is
  not bounded.
