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

Eight claims are proved (§4). The time a block takes to reach the honest
nodes is studied with a simulation (§5), `scripts/sync-prefeed.py`,
reference budgets with another (§6), `scripts/sync-budget.py`, and the
blocks a node processes after GST with equivocation reports with a third
(§7), `scripts/sync-reports.py`, and waiting before building with a
fourth (§8), `scripts/sync-wait.py`.

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
history holds a block carrying evidence against `X` (`Exposes`). A block
passes the checks when its references sit one round below it, name a
quorum of `n − f` authors unless it is at round `0`, and name no author it
exposes (`Checks`): the quorum of block validity and the condition of the
`DoS` arc (`DoSValidOn`), with exposure read from evidence alone. The
authors a block exposes are those its references expose and those its own
payload names, at most `f`, so a check needs no walk of the history. A
target is admitted when every block of its history passes the checks
(`Admits`): a pass over the headers before the stream. The authors a set
of blocks catches are those with twins in it and those its blocks carry
evidence against (`caught`).

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
* a block the node builds is its own, ready, passes the checks, and
  carries evidence against every author the node has detected; the
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
| S6 | **Detection in time.** At each event a node reports to the other nodes a pair of twins of each author it detects there (`reports`). Let times be nondecreasing along the trace, and let the reports of an honest node reach every other honest node within `Δ` (`ReportsDelivered`). An author an honest node detects at time `t` is detected by every honest node at every event after `t + Δ`. A node builds only blocks that carry evidence against every author it has detected, so every block an honest node builds after `t + Δ` exposes the author. | `Node.Sync.DetectsInTime` (proved): `Node.Sync.exists_reports`, `Node.Sync.reportsWithin_of_delivered`, `Node.Sync.detected_after`, `Node.Sync.convicts_of_builtAt`, `Node.Sync.exposes_after` |
| S7 | **The exposure bound in time.** Under the premises of S6 and of S5 on the fault model, let every block of an honest author be built by that author (`Authentic`, `BuiltAt`), let the node `v` detect every author it detects by `T`, and let every block an honest node builds by `T + Δ` lie at round `m` or below. Then `v` holds at most `n + |D|` blocks of each round from `m + 1` on. | `Node.Sync.ExposureInTime` (proved): `Node.Sync.exposes_in_time`, `Node.Sync.card_round_le` |
| S8 | **The history bound in time.** Under the premises of S7, the history of every block on `v`'s disk, `v`'s own blocks among them, holds at most `n + |D|` blocks of each round from `m + 1` on. | `Node.Sync.HistoryInTime` (proved): `Node.Sync.run_closed`, `Node.Sync.card_history_round_le` |

`Node.Sync.holds` proves the eight together, with the standard axioms.

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
exposes `X`. S5 does not model time; S6 and S7 give its premise in time
from reports within `Δ`.

**Why the premise holds in time.** A node detects an author at an event
of its own, through a stream that exposes a twin of a held block, a disk
that then holds twins or a block carrying evidence, or a report; in each
case the event shows a pair of twins of the author, which the node
reports (`exists_reports`). A report of twins detects their author, and a
node never forgets a detection, so the report that reaches an honest node
`w` within `Δ` of a detection at `t` makes the author detected at every
event of `w` after `t + Δ` (`detected_after`). A block
`w` puts on its disk then carries evidence against the author, since the
build step takes only such a block (`convicts_of_builtAt`), and lies in
its own history, so it exposes the author (`exposes_after`). An honest block of
round `m + 1` is built by its author (`Authentic`) after `T + Δ`, since
every honest block built by then lies at round `m` or below, so it exposes
every author `v` detected by `T` (`exposes_in_time`): the premise of S5.

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
the rule with reports (`rep`). The table gives the blocks a node processes
per round between ticks 400 and 900, all / Byzantine, at `n = 10, f = 3`,
for the node that processes most:

| Attack | No rule | `DoSValid` | Reports |
|---|---|---|---|
| No attack | 6.1 / 0 | 6.1 / 0 | 6.1 / 0 |
| `X` chain to node 0 every 40 rounds | 9.5 / 3.0 | 9.5 / 3.0 | 9.5 / 3.0 |
| `Y` carries a fresh `X` chain each round | 20.1 / 14.0 | 6.0 / 0 | 6.0 / 0 |
| `Y` announces a tree of twins each round | 69.1 / 63.0 | 6.0 / 0 | 6.1 / 0 |
| a tree of twins for each node, each round | 454.3 / 447.4 | 6.0 / 0 | 6.1 / 0 |
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

Exposure in the rule with reports is read from evidence alone, as in the
checks of §3. Before the first conviction this costs more than counting
twins in the history too, since a block carrying a tree of twins passes
until its twins have been seen: under the tree attack a node processes 66
Byzantine blocks in all, against 6 under `DoSValid`. The rate per round
after GST is the same.

## 8. Waiting before building

**The history bound** (S8, `HistoryInTime`, proved). A disk holds the
references of its blocks (`run_closed`), so it holds the history of each
of them. Under the premises of S7, the history of every block on an
honest node's disk, its own blocks among them, holds at most `n + |D|`
blocks of each round from `m + 1` on. The bound needs no wait. Below
round `m + 1` only S4 bounds the disk: an honest block built before its
author detected anything carries no evidence, and can carry a chain of a
Byzantine author that never equivocates, one block a round (§5).

**The rules simulated** (`scripts/sync-wait.py`). The network is that of
§7, synchronous from the start (`Δ = 3`), with the exclusion of `rep`.
The novelty of a set of references is the blocks their histories add to
the node's history. The rules are: `react`, the first block held of each
author; `min`, the blocks of least novelty; `wait`, which waits once for
each equivocating block in the novelty and then builds as `min`; and
`size`, which builds as `min` and, when the novelty holds more than `τ`
blocks not yet waited for, first waits `w`. No rule refuses a block. The
share of a node is the least fraction of the other honest nodes' blocks
from round 30 on that reference a block of one honest node.

**Findings.**

* Under the attacks of §5 and §7 the exclusion keeps the Byzantine blocks
  of honest histories near one per round under every rule. `size` matches
  `min` there with at most three waits, and `min` costs rounds under
  `edge`.
* **Late injection** (`inject`). X is detected at round 20. At round 40,
  Z makes a binary tree of X twins of depth `d` below round 16, on honest
  blocks that carry no evidence, and a chain of its own up to Y's block.
  With exposure read from evidence alone, the tree enters every honest
  history under every rule: `2^d + 1` blocks of one round. `wait` fails
  because a node puts the tree in the set of blocks it waited for, and
  its next build takes Y's following block, which carries it. With
  exposure read from twins as well, the chain fails the checks and the
  tree stays out.
* **A rule that only delays cannot keep a block out while the honest
  nodes are a bare quorum.** At `n = 10, f = 3`, `size` halves what
  `inject` puts in at depths 4 and 6, and at depth 8 the tree enters every
  honest history. A node that lacks an honest block after its wait takes
  Y's block with the tree; the others, taking least novelty, leave that
  node's blocks out, so each of them lacks an honest block in turn.
* **Twin checks do not bound histories by the shape alone** (`nest`).
  The Byzantine authors are silent until round 40. At round `40 + s`, for
  `s < f`, each honest node is shown its own family of stage `s`,
  back-dated `depth` rounds: a chain of `BYZ[k]` adopts, in its last `k`
  rounds, a fresh family of each `BYZ[i]` with `i < k`, so it carries
  `2^k` chains. A block may have twins in its history, but no block
  references an author with twins in its history. An honest node
  that takes the stages has `2^f − 1` chains in its history, the count
  that freshness allows (`docs/dos-equivocation-and-growth.md` §5).
  Evidence comes too late, so evidence-only checks give the same rows.

With no horizon over seeds 1 to 5, each cell gives the range of rounds
reached, the blocks of Byzantine authors in honest histories (mean, with
the maximum in brackets), the largest number in one round, and the least
share. Without the attack every rule reaches 54 rounds at `n = 10` and 53
at `n = 13`.

| `n, f` | `depth` | `react` | `min` | `size` |
|---|---|---|---|---|
| 10, 3 | 4 | 55–56, 178, 49, 0.89 | 55–56, 122 (133), 37, 0.90 | 53–54, 78 (98), 29, 0.93 |
| 10, 3 | 13 | 52–53, 619, 49, 0.88 | 53–54, 242 (303), 24, 0.93 | 50–54, 169 (239), 19, 0.96 |
| 10, 3 | 39 | 43–44, 1893, 49, 0.81 | 47–48, 518 (696), 18, 0.94 | 42–54, 170 (308), 8, 0.99 |
| 13, 4 | 4 | 53–54, 391, 135, 0.84 | 54–55, 234 (255), 92, 0.89 | 50–52, 187 (216), 82, 0.90 |
| 13, 4 | 13 | 48–49, 1606, 135, 0.80 | 50–51, 591 (774), 66, 0.90 | 51–52, 49 (91), 7, 0.96 |
| 13, 4 | 39 | 42–43, 4847 (5116), 135, 0.72 | 44, 2012 (2978), 79, 0.89 | 42–51, 244 (906), 24, 0.98 |

Under `react` a round holds `(n − f)(2^f − 1)` blocks of Byzantine
authors, 49 at `f = 3` and 135 at `f = 4`, against the ceiling
`n + (n − 1)·f^f` of Theorem A, 253 and 3085: below the ceiling, and
exponential in `f`. `size` admits on average 4% to 44% of what `react`
admits and leaves no honest node out, but one seed at `n = 13,
depth = 39` admits 906 blocks, the cascade of `inject`.

## 9. Open

The plan to run these syncs and checks on the node is `docs/node-sync.md`.

* **A budget that admits honest blocks.** §6 rules out the three rules
  tried as they stand. The catch-up chain reaches the frontier block only
  through the node's references to its own blocks.
* **Delivery.** S6 assumes of the network that the reports of an honest
  node reach every other honest node within `Δ` (`ReportsDelivered`),
  from the start: synchrony, with no GST.
* **The round `m` of S7.** It is the highest round an honest node builds
  at by `T + Δ`. Rounds have no least duration, so it is not bounded by
  the time `T`.
* **Honest histories below round `m + 1`** (§8): the checks read exposure
  from evidence alone, and a late injection then enters every honest
  history. Reading exposure from twins in the history as well stops the
  injection in the simulation. It is not in the model, and it does not
  stop `nest`, whose blocks reference no author with twins in their
  histories.
* **Liveness.** The node's V11 assumes synchronisation of the network
  (`SyncedWithin`, section 5.1 of `docs/validator.md`); deriving it from these
  syncs, with the budget, is open.
* **Answers.** The cost of answering requests from nodes outside `H` is
  not bounded.
