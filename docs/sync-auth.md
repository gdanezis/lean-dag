# Certified joins of twins

This note records a simulation of one rule, `scripts/sync-auth.py`. Under
the rule, a block that brings twins together in its history carries a
certificate signed by a quorum. The question is whether the rule stops
Byzantine nodes from building large structures of twins without the honest
nodes knowing. The network, the honest rules `react` and `min`, and the
attacks are those of `docs/sync.md` §8. There `n = 10`, `f = 3`, the system
is synchronous from the start (`Δ = 3`), and there is no horizon.

## 1. The rule

A block `b` *joins* a twin pair `{x, x′}` when both are in its history and
in the history of no single reference of `b`. A block that joins pairs is
valid only with a certificate. The certificate holds the round of `b` and a
set `E` of pairs that contains every pair `b` joins. It is signed by at
least `q = n − f` nodes, and it is evidence against the authors of `E`.

An honest node prefers references that join nothing. When it must join, it
sends `(r, E)` to every node, and it builds once `q` nodes have signed.

A node that receives `(r, E)` learns `E` and convicts its authors. It
refuses to sign, and sends the block back, when it holds a block of round
`r` whose history contains no pair of `E`. This is the rule `clean`.
Byzantine nodes refuse every honest request. They request only when they
would succeed, and their request reaches every node.

## 2. Results

Each cell gives the rounds reached, the blocks of Byzantine authors in
honest histories (all / largest in one round), the least share, the most
failed requests of one node, and the largest `E`. The checks are evidence
only, twins as well, or certificates under `clean`. The rule is `react`.

| Attack | Evidence | Twins | Certificates |
|---|---|---|---|
| No attack | 54, 3 / 3 | 54, 3 / 3 | 54, 3 / 3, 0, 0 |
| `edge` | 53, 46 / 3 | 55, 32 / 3 | 55, 32 / 3, 0, 78 |
| `split` | 55, 18 / 14 | 54, 18 / 14 | 53, 18 / 14, 0, 42 |
| `isolate` | 55, 24 / 21 | 55, 24 / 21 | 53, 24 / 21, 0, 63 |
| `inject`, `d = 8` | 147, 686 / 257 | 79, 44 / 3 | 78, 44 / 3, 0, 1 |
| `nest`, `depth = 13` | 52, 619 / 49 | 52, 619 / 49 | 52, 224 / 17, 0, 512 |
| `nest`, `depth = 39` | 43, 1893 / 49 | 43, 1893 / 49 | 50, 744 / 19, 0, 1842 |
| `bulk`, `depth = 39` | 54, 156 / 4 | 54, 156 / 4 | 54, 156 / 4, 0, 38 |
| `force` | 53, 70 / 4 | 53, 70 / 4 | 53, 70 / 4, 0, 1 |

Under `min` with certificates, `nest` admits 26 / 2 at `depth = 13` and
78 / 2 at `depth = 39`, against 303 / 24 and 387 / 10 with twin checks.
The other rows are as under twin checks. Every share is at least 0.79, and
no request fails, under any attack.

## 3. Findings

* **No join is silent.** Every pair of twins in a valid history is in
  the set `E` of a certificate of the round of the block that joins it.
  Every node received `E` before that block existed.
* **Joins are not back-dated.** Signers hold their own blocks of past
  rounds, and those blocks contain no pair of the request. So no
  certificate is granted for a join below the rounds the honest nodes
  have built. `inject` fails as under twin checks, and so does every
  level of the doubling family of `nest` that joins twins inside the
  family.
* **The mass is not bounded.** What remains of `nest` is twin-free
  chains, dated back, which each honest node adopts on its own.
  The honest nodes then join them in public, at the current round, under
  certificates that name up to 1842 pairs. `bulk` is one Byzantine
  certificate for a join at the current round, of 38 pairs. The rule
  makes the mass known; it does not price it.
* **A cap on `E` breaks liveness.** When signers refuse an `E` of more
  than `2n` pairs, `split`, `filler` and `isolate` stall the system at
  round 2 or 3. The adversary shows each honest node different twins, and
  the honest requests that follow exceed the cap.
* **The signing rule matters.** Under `built`, a node refuses when it has
  built round `r`. That rule needs no history, but it stalls `nest` at
  round 40: a node that comes late to round 41 needs a join that the
  others have already made, and every signer refuses it. Citing the
  certificates of round 41 that the node holds (`reuse`) does not cover
  its join. Under `clean`, the signers' round-41 blocks contain pairs of
  the request, so they sign.
* **Honest nodes must avoid joins.** A `react` node that takes a block of
  every author joins both carriers of `bulk`, is refused, and stalls the
  system at round 39. Taking blocks that join nothing first, and joining
  blocks only to reach a quorum, removes the stall.
* **The test of `clean` needs the signer's past rounds.** The node keeps
  every block it has stored (garbage collection is out of scope), so a
  signer can always test the round of a request. Under `oldjoin`, a join
  25 rounds back is refused and no Byzantine block enters. Only with a
  simulated horizon of 20 rounds, which the node does not have, is that
  join signed; the blocks below the horizon are then not fetched, and the
  fullest honest disk holds 6 blocks of Byzantine authors.

## 4. The mass

The blocks of Byzantine authors that certificates do not keep out of
honest histories share three properties.

* **They are twins, beyond one chain per author.** Under `nest` every
  one of them is a twin. Under `bulk`, 76 of 153 are; the others are the
  chains of Z and Y that carry the twins, one block of each author a
  round, which no rule on twins can tell from an honest node's chain.
* **They are late.** A block of round `j` is *late* when it is created
  after every honest node has built round `j + 1`. No honest block can
  then reference it, so its honest support is zero. Under `nest` with
  certificates, 197 of 221 such blocks are late at `depth = 13`, and 715
  of 741 at `depth = 39`. The others are the tops, which honest nodes
  adopt at the frontier. Honest blocks have support 6, all the other
  honest nodes, in all but a few cases. The twins of `split` are not
  late, and each has honest support 1.
* **They hang below a top.** A block that references a late block of
  round `j` is of round `j + 1`, and is not honest. The mass is therefore
  a structure of Byzantine blocks whose only link to an honest block is
  its top, adopted at the frontier. The structure joins nothing below the
  frontier, so its history holds at most one block of each Byzantine
  author in each round. Its twins arise only between structures that
  different honest nodes adopt, or that one honest node adopts at
  successive rounds. Honest nodes then join them in public, under
  certificates whose `E` consists of late blocks.

The size of the mass is argued, not proved. Let an honest node adopt
structures one at a time. A structure's top author must not be exposed
in the node's history, so it can have no chain in an earlier structure
it adopted. A Byzantine block at the frontier must reference honest
blocks of the round below, and these carry the evidence of every join
made public more than `Δ` before. So nesting at the frontier stops once
evidence spreads, and under `rtnest` a round holds 7 blocks of Byzantine
authors at most. The best order then has the `i`-th top author carry
chains of the `i` authors before it. An honest node gathers
`f(f + 1)/2` chains, against the `2^f − 1` of the doubling family, and a
round of the union of honest histories holds at most
`n + (n − f)·f(f + 1)/2` blocks. That is 52 at `n = 10, f = 3`, and 103
at `n = 13, f = 4`.

The attack `flat` builds these structures, back-dated `depth = 13`
rounds. In blocks of Byzantine authors in honest histories, all /
largest in a round:

| `n, f` | Rule | `flat` | `flat`, certificates | `nest`, certificates |
|---|---|---|---|---|
| 10, 3 | `react` | 542 / 42 | 497 / 38 | 224 / 17 |
| 10, 3 | `min` | 232 / 18 | 254 / 20 | 26 / 2 |
| 13, 4 | `react` | 1138 / 90 | 744 / 59 | 303 / 23 |
| 13, 4 | `min` | 429 / 34 | 605 / 48 | 39 / 3 |

Certificates leave `flat` nearly whole, and under `min` they let more of
it in. The joins are made by honest nodes, with certificates whose `E`
names up to 1764 pairs. Each structure is as long as the attacker dates
it back, so without garbage collection the mass of one attack grows with
the current round. Each Byzantine author can serve as a top only until it
is convicted, which every honest node does within `Δ` of the first
request naming its twins. The attack therefore works once per author.

## 5. Pruning at the seal

A late block has no honest support, and that can be read from the DAG
once a commit fixes a set of blocks. Under `prune = K`, the first honest
leader at a round `a ≥ r + K + 1` seals round `r` once every honest node
is two rounds past `a`. A block of round `r` is *kept* when it is in the
history of blocks of `f + 1` distinct authors of rounds `r + 1..r + K`
in the history of that leader. A block of a sealed round that is not kept
is *cut*. No node fetches, stores or follows a cut block, and a
reference to one counts as held, both for storing a block and for its
validity. An honest node also references the blocks it holds of its last
`K` rounds that are not yet in its history. The seal is computed once,
for all nodes, so the model assumes the agreement that a commit rule
would give.

Each cell gives the rounds reached, the blocks of Byzantine authors in
the history that validity follows (all / largest in a round), on the
fullest honest disk, and processed by one honest node, and the honest
blocks cut. The rule is `react` with twin checks, and `K = 3`. Under
`fast` there is no attack, and the blocks of Byzantine authors arrive
first, so one honest node is always the last of its round.

| Attack | No pruning | Pruning |
|---|---|---|
| `fast` | 150, 149 / 1, 153, 150, 0 | 150, 149 / 1, 153, 150, 0 |
| `split` | 54, 15 / 14, 20, 17, 0 | 54, 15 / 14, 20, 17, 0 |
| `isolate` | 55, 21 / 21, 27, 24, 0 | 55, 21 / 21, 27, 24, 0 |
| `inject`, `d = 8` | 79, 41 / 3, 300, 14185, 0 | 150, 154 / 3, 162, 159, 0 |
| `nest`, `depth = 13` | 52, 616 / 49, 622, 732, 0 | 55, 39 / 14, 232, 286, 0 |
| `nest`, `depth = 39` | 43, 1890 / 49, 1896, 2153, 0 | 55, 39 / 14, 232, 286, 0 |
| `flat`, `depth = 13` | 52, 539 / 42, 545, 703, 0 | 55, 39 / 14, 221, 275, 0 |
| `bulk`, `depth = 39` | 54, 153 / 4, 156, 153, 0 | 55, 11 / 4, 30, 27, 0 |
| `oldjoin` | 55, 62 / 4, 65, 62, 0 | 55, 4 / 1, 11, 8, 0 |

At `n = 13, f = 4`, `nest` with `depth = 39` falls from 4661 / 123 to
68 / 18, and its disk from 3826 to 314. Under `min` the rows are alike.
The other attacks of §2 are as without pruning.

* **The system stays live.** Every run reaches at least the rounds it
  reaches without pruning. Under `inject`, it reaches 150 rounds instead
  of 79, because no node processes the back-dated tree.
* **The cost of sync no longer grows with the depth.** Under `nest`,
  the disk and the work are the same at `depth = 13` and `depth = 39`.
  A node still fetches what lies in the rounds not yet sealed when an
  attack starts, about `K + 3` rounds below the frontier, and the cut
  blocks of those rounds stay on its disk. What validity follows is the
  tops and the chains of the last `K` rounds below them.
* **Attacks at the frontier are untouched.** The twins of `split`,
  `isolate` and `filler` have honest support, and pruning keeps them.
  They were bounded before.
* **Support must count history, not references.** When only references
  of rounds `r + 1..r + K` count, `fast` cuts 68 blocks of the last
  honest node, which most nodes reach through one other node's block.
  Counting the blocks whose history holds `x` cuts none.
* **The slow node needs references below the previous round.** In the
  model of `LeanDag/Node`, every reference sits one round below its
  referrer. Without the references to older held blocks, `fast` cuts
  95, 66 and 46 honest blocks at `K = 2, 3, 4`, against 17, 0 and 0
  with them. Under `nest` the two agree.
* **`K` trades the slow node against the window.** Under `fast`, `K = 1`
  cuts 144 honest blocks and `K = 2` cuts 17. Under `nest` with
  `depth = 39`, validity follows 0, 19, 39 and 157 blocks of Byzantine
  authors at `K = 1, 2, 3, 6`, and the disk holds 146, 183, 232 and 379.
* **Asynchrony cuts honest blocks.** With delays of up to 10 before
  `GST`, `fast` cuts 42 honest blocks when `GST = 100` and 90 when
  `GST = 200`. A node that falls more than `K` rounds behind loses its
  blocks of those rounds, and its payload must be proposed again. The
  system stays live.

## 6. Bypassed blocks

`LeanDag/Common/Bypass.lean` defines the rule in terms of what a node
holds, not of the seal of §5. A block `x` of round `r` is *bypassed* in a
set `V` of held blocks when the blocks of `V` at round `r + 1` that do
not reference `x` come from at least `q` authors (`Bypassed`). `V` is
*closed up to bypass* when every reference of a block of `V` is in `V`
or bypassed in it (`BypassClosed`). A bypassed block may still be held:
a node stops following its references, but it still counts towards
bypassing the round below. A secret structure of at most `f` authors is
therefore bypassed once a node holds the honest blocks of the rounds
above it, whatever blocks of slow honest nodes are bypassed themselves.

Under `bypass`, `scripts/sync-auth.py` applies the rule at each node. A
node does not fetch or follow a block it finds bypassed, stores every
block it receives whose references it holds or finds bypassed, and so
holds back a block until each reference is one or the other. Each cell
gives, at `n = 10, f = 3` under `react` with twin checks, the rounds
reached, the blocks of Byzantine authors that some honest node follows
(all / largest in a round), on the fullest honest disk, the honest
blocks some other honest node finds bypassed, and the blocks one honest
node follows and another finds bypassed. The pruning column is §5 with
`K = 3` and no references below the previous round.

| Attack | No pruning | Pruning | Bypass |
|---|---|---|---|
| `fast` | 150, 149 / 1, 153, 0, 0 | 150, 149 / 1, 153, 66, 0 | 150, 149 / 1, 153, 87, 0 |
| `split` | 54, 15 / 14, 20, 0, 0 | 54, 15 / 14, 20, 0, 0 | 55, 15 / 14, 20, 1, 14 |
| `isolate` | 55, 21 / 21, 27, 0, 0 | 55, 21 / 21, 27, 0, 0 | 54, 0 / 0, 27, 0, 0 |
| `filler` | 55, 65 / 15, 71, 0, 0 | 55, 44 / 15, 71, 0, 0 | 56, 9 / 7, 32, 3, 7 |
| `inject`, `d = 8` | 79, 41 / 3, 300, 0, 0 | 150, 154 / 3, 162, 60, 0 | 150, 150 / 2, 157, 96, 0 |
| `nest`, `depth = 13` | 52, 616 / 49, 622, 0, 0 | 55, 39 / 14, 232, 0, 0 | 56, 7 / 7, 30, 2, 7 |
| `nest`, `depth = 39` | 43, 1890 / 49, 1896, 0, 0 | 55, 39 / 14, 232, 0, 0 | 56, 7 / 7, 30, 2, 7 |
| `flat`, `depth = 13` | 52, 539 / 42, 545, 0, 0 | 55, 39 / 14, 221, 0, 0 | 56, 7 / 7, 30, 2, 7 |
| `bulk`, `depth = 39` | 54, 153 / 4, 156, 0, 0 | 55, 11 / 4, 30, 0, 0 | 55, 3 / 2, 10, 1, 0 |

* **The system stays live**, under every attack of §2, under `react` and
  `min`, at `n = 13, f = 4`, and with delays of up to 10 before
  `GST = 100, 200, 500`.
* **The cost of an attack no longer depends on its depth.** Under `nest`
  the fullest disk holds 30 blocks of Byzantine authors at both depths,
  against 232 under pruning. At `n = 13, f = 4` and `depth = 39` it holds
  48, against 3826 without pruning, and some honest node follows 9.
  With `GST = 500`, so that the attacks start during asynchrony, `nest`,
  `flat` and `bulk` give the same counts.
* **Blocks wait little.** An honest block waits at most 5 ticks between
  its first arrival at a node and its storage, against 26 under `nest`
  with `depth = 13` and 75 with `depth = 39` without pruning.
* **Nodes seldom disagree.** At most 7 blocks are followed by one honest
  node and bypassed by another under the back-dated attacks; 14 to 18
  under `split`, `rtnest` and `isolate`, whose twins honest nodes see
  differently.
* **Slow honest blocks are bypassed.** Under `fast`, 87 honest blocks are
  bypassed under `react` and 103 under `min`; 112 with `GST = 100`, 130
  with `GST = 200`, and 72 at `n = 13`. Their payload must be proposed
  again. The rule has no window to trade against this.

* **An unreferenced block is bypassed** (`bypassed_of_unreferenced`). If
  `V` holds a round-`(r + 1)` block of every honest validator, no honest
  block of that round references `x`, and `q ≤ |honest|`, then `x` is
  bypassed in `V`.
* **Bypass persists** (`Bypassed.mono`). If `V ⊆ V′`, a block bypassed in
  `V` is bypassed in `V′`. A bypass at one honest node therefore holds at
  every honest node that comes to hold the same blocks.
* **What is not bypassed is bounded** (`card_not_bypassed_le`). Under the
  holding of the first theorem, the round-`r` blocks not bypassed in `V`
  number at most `|honest| · n`, since each is referenced by an honest
  block of round `r + 1`, and a block references at most `n` blocks. The
  bound does not depend on how far back a structure is dated.
* **Supported blocks are never bypassed** (`not_bypassed_of_support`). A
  block referenced at round `r + 1` by `s` honest validators, with
  `n < q + s`, is bypassed in no set. At `q = n − f` that is `s ≥ f + 1`,
  which every leader with a quorum of votes has.

## 7. Safety under bypass

`scripts/sync-bypass-safety.py` asks a solver for a DAG on which two nodes
disagree about a leader `L` of round `r`. Node `w` holds every block and
commits `L` directly. Node `v` holds every honest block and some blocks
of Byzantine authors, each block it holds having its references held or
bypassed; `v` does not commit `L` directly and skips it through an anchor
`A`, since no certificate whose votes `v` holds is reachable from `A`.
The exposure clause and references to the author's own block hold
throughout.

**The rule of §6 is not safe.** At `n = 4, f = 1`, the Byzantine author
`B` shows two twins of round `r + 1`, `B.2` and `B.2′`, both voting.
Honest certificates `h0.3` and `h2.3` reference one twin each, and `B`'s
own certificate the second. Each twin is then referenced by a single
honest block of round `r + 2`, and `v`, holding the honest blocks and a
block of `B` that references neither, bypasses both. `w` sees three
certificates and commits `L`. `v` counts two votes in each honest
certificate, sees none, and skips `L` through `A = h1.4`, which
references `h1.3`, `h2.3` and that block of `B`. No honest block holds
both twins. The same holds at `n = 7, f = 2`.

**What `v` must hold.** Two strengthenings were tested.

| `v` holds | `n = 4, f = 1` | `n = 7, f = 2` |
|---|---|---|
| The rule of §6 | unsafe at `R = 4` | unsafe at `R = 4` |
| The references of each block it follows | unsafe at `R = 4` | |
| Also those of a bypassed block it reaches | safe at `R = 4, 5, 6` | safe at `R = 4, 5, 6` |

Here `R` is the round of `A`, and "safe" means the solver finds no such
DAG with at most two blocks of a Byzantine author a round. In the second
row the honest certificate is itself bypassed, by the blocks of round
`r + 3` that do not reference it, so `v` does not fetch its votes. In
the third row `v` reads the references of a bypassed block it reaches
from a block it follows, and goes no further; a bypassed structure costs
at most `n + n²` more blocks.

## 8. Bypass below the decided horizon

**The rule.** A node applies the test of §6 only below its decided
horizon, and takes the witnesses from the blocks it has ordered, not from
the blocks it holds.

* The *decided horizon* `h` of a node is the highest round such that the
  node has decided every leader of round `h` or below.
* The *ordered set* `C` of a node is the set of blocks its commits have
  ordered.
* A block `x` of round `r < h` is *bypassed* when the blocks of `C` at
  round `r + 1` that do not reference `x` come from at least `q` authors
  (`Bypassed U C q x`). No block of round `h` or above is bypassed.
* A node does not fetch, store, follow or order a bypassed block, and a
  reference to a bypassed block counts as held.
* A commit orders the history of its leader from the top down. A block of
  a round below the horizon before the commit is ordered only if it is
  not bypassed by the ordered blocks one round above it, those that this
  commit orders included.

**Agreement.** A decision reads only the rounds of undecided leaders, all
of them at or above `h`, so the rule changes no decision.
`LeanDag/Common/BypassLedger.lean` defines the ledger under the rule from
the verdicts of the slots and the record, and from no view.

* **The commit** (`layer`, `flush`). A commit of the leader `L` of slot
  `k` orders `L` if it is not yet ordered. It then orders, one round
  further down at each step, each reference of a block it has just
  ordered, unless the reference is already ordered, or its round `r`
  has `r + 1` below the round of slot `k` and the ordered blocks of
  round `r + 1`, those of this commit included, bypass it.
* **The ledger** (`bypassLedger`). The blocks ordered by the commits of
  slots `0, …, n − 1`, in slot order, skipped slots ordering nothing.
* **Agreement** (`bypassLedger_agree_of`). Verdicts that agree below
  `n` give the same ledger after every `m ≤ n` slots. A block therefore
  enters at the same slot at every validator.
* **Agreement of validators** (`AnchoredRule.bypassLedger_agree`). Two
  validators that have decided every slot below `n` agree on the
  verdicts (`decided_agree`), and so on every ordered block.
* **No retraction** (`bypassLedger_mono`, `disjoint_flush`). The ledger
  only grows, and a commit orders no block ordered before it.
* **Within the committed histories**
  (`bypassLedger_subset_ledgerSet`). Every ordered block is in the
  history of a committed leader.
* **Closed up to bypass** (`bypassClosed_bypassLedger`). If every
  committed leader is in the record, every reference of an ordered
  block is ordered or bypassed in the ledger.

The order within one commit is not modelled, as for the ledger without
bypass (`LeanDag/Common/Ledger.lean`).

**What a node holds.** A view in `LeanDag` holds the whole history of
each of its blocks. A node that applies the rule does not.
`LeanDag/Common/BypassView.lean` defines what it holds instead.

* **A bypass view** (`BypassView U q H C`). A set of held blocks that
  contains the ordered set `C`. Every reference of a held block is held,
  or lies at a round `r` with `r + 1 < H` and is bypassed in `C`. A view
  holding `C` is one (`View.toBypassView`).
* **The cut is a view** (`BypassView.chop`). If `H ≤ G + 1`, the held
  blocks of round `G` or above form a view of the record cut at `G`
  (`chop U G` of `LeanDag/GC`). No reference at round `G` or above is
  bypassed, so these blocks are closed under the references the cut
  keeps.
* **A commit reads only what the node holds** (`flushOn_eq`,
  `flush_subset`). `flushOn` computes a commit from a block map, and
  reads the round of a reference off the leader. If the map agrees with
  the record on the held blocks, and the leader is held, `flushOn`
  orders the blocks of `flush`, whatever the map says of other ids. The
  blocks a commit orders are held.

**A node under bypass** (`BypassRun`). A node starts holding nothing, and
its states record what it holds, the slots it has decided, and the
blocks it has ordered. It moves by three steps.

* **Accept.** It takes in a set of new blocks once every reference of
  each is held, among the new blocks, or bypassed: of round `r` with
  `r + 1 < slotRound n` and bypassed in what it has ordered. It follows
  references only up to bypassed blocks, and never fetches those.
* **Skip.** It decides that slot `n` is skipped.
* **Commit.** It decides that slot `n` commits a leader it holds, and
  orders the leader's history with `flushOn`, from a block map that
  agrees with the record on what it holds.

`BypassView.extend` and `BypassView.raise` give the invariant
(`BypassRun.inv`). In every state, what the node has ordered is the
ledger of its verdicts, and what it holds is a bypass view of that
ledger at the horizon `slotRound n`. A bypassed block stays bypassed,
since the ordered set and the horizon only grow, so the node never
needs it later.

`LeanDag/Properties/Arcs/Bypass.lean` adds the decisions, for any rule on
the record. The node decides slot `n` on the blocks it holds at or above
`slotRound n − 1`, read as a view of the record cut there (`DecOnCut`).

* **It can decide on what it holds** (`exists_cutView`). In every state
  those blocks form a view of the cut, by the invariant and
  `BypassView.chop`.
* **Safety** (`bypassRun_agree`). Under `Agree`, two nodes that run the
  rule agree on every verdict and order the same blocks, the ledger of
  those verdicts. Both new decisions and the order of every block are
  agreed.
* **With a full history** (`bypassRun_agree_full`). Under `Banded`, the
  verdicts of a node that runs the rule are those of any node holding a
  view of the whole record, by `decided_agree_chop` of garbage
  collection.

The core rule has both premises (`MysticetiProperties.onRecord`,
`MysticetiProperties.agree`, `MysticetiProperties.banded`).

**What a node follows below the horizon.** If the ordered blocks of round
`r + 1` come from at least `q` authors and none references `x`, then `x`
is bypassed (`bypassed_of_unreferenced_in`). If an ordered block
references `x` and `x` was not ordered with it, then `x` was bypassed
then and is bypassed still (`Bypassed.mono`). At a round below the
horizon whose ordered blocks one round above come from at least `q`
authors, a node therefore follows exactly the ordered blocks. A block
that arrives after the round above it is ordered is never fetched: the
test reads only the references of ordered blocks.

**The bound.** Let `C` hold a block of round `r + 1` of every honest
validator.

* Every block of round `r` that is not bypassed is referenced by an
  honest block of `C` at round `r + 1`
  (`exists_honest_ref_of_not_bypassed`).
* At most `|honest|` blocks of any one author at round `r` are not
  bypassed (`card_not_bypassed_creator_le`). An honest block references
  at most one block of each author.
* If each author outside a set `D` that is not honest has at most one
  block at round `r`, at most `|D| · |honest| + (n − |D|)` blocks of
  round `r` are not bypassed (`card_not_bypassed_le_of_twins`).

The bound holds at every round below the horizon. It does not depend on
how far below the horizon an attack is dated or on when its blocks are
shown. Above the horizon nothing is bypassed. There S7 of
`docs/sync.md` bounds what a node holds by `n + |D|` blocks a round from
the round `m` at which every honest block exposes `D`.

**Simulation.** Under `bypass = 'commit'`, `scripts/sync-auth.py` decides
the leader of round `a`, by author `a mod n`, once every honest node is
two rounds past `a`. The leader is committed if its author is honest and
built at round `a`, and skipped otherwise. Each cell gives the same
measures as §6 at `n = 10, f = 3` under `react` with twin checks: the
rounds reached; the blocks of Byzantine authors that some honest node
follows; the number on the fullest honest disk; the number one honest
node processes; and the honest blocks bypassed.

| Attack | No rule | §6 | Below the horizon |
|---|---|---|---|
| `fast` | 150, 149, 153, 150, 0 | 150, 149, 153, 150, 87 | 150, 149, 153, 150, 74 |
| `split` | 54, 15, 20, 17, 0 | 55, 15, 20, 17, 1 | 54, 15, 20, 17, 0 |
| `isolate` | 55, 21, 27, 24, 0 | 54, 0, 27, 24, 0 | 55, 21, 27, 24, 0 |
| `filler` | 55, 65, 71, 108, 0 | 56, 9, 32, 29, 3 | 55, 23, 58, 74, 1 |
| `inject`, `d = 8` | 79, 41, 300, 14185, 0 | 150, 150, 157, 154, 96 | 150, 153, 160, 157, 76 |
| `nest`, `depth = 13` | 52, 616, 622, 732, 0 | 56, 7, 30, 27, 2 | 55, 22, 146, 163, 1 |
| `nest`, `depth = 39` | 43, 1890, 1896, 2153, 0 | 56, 7, 30, 27, 2 | 55, 22, 146, 163, 1 |
| `flat`, `depth = 13` | 52, 539, 545, 703, 0 | 56, 7, 30, 27, 2 | 55, 22, 143, 158, 1 |
| `bulk`, `depth = 39` | 54, 153, 156, 153, 0 | 55, 3, 10, 7, 1 | 55, 7, 22, 19, 1 |
| `rtnest`, `depth = 13` | 53, 91, 151, 529, 0 | 55, 14, 31, 28, 0 | 54, 8, 64, 163, 0 |

* **The system stays live** under every attack, under `react` and `min`,
  and at `n = 13, f = 4`.
* **The cost of an attack does not depend on its depth.** Under `nest`
  one honest node processes 163 blocks of Byzantine authors at both
  depths, against 732 and 2153 without the rule. At `n = 13, f = 4` it
  processes 203 at both depths, against 1764 and 4106.
* **The rule costs more than §6.** A node
  follows an attack down to the first round whose ordered blocks one
  round above come from `q` authors. The leaders of rounds 37, 38 and 39
  are Byzantine and skipped, so until the leader of round 40 commits, the
  ordered blocks of round 36 come from one author, and `nest` is
  followed down to round 35. The fullest disk holds 25 blocks of
  Byzantine authors in each of rounds 35 to 37, and none below.
* **Slow honest blocks are bypassed** as under §6: under `fast`, 74
  under `react`, 100 under `min`, and 64 at `n = 13`. A block that no
  commit orders before its round falls below the horizon is not ordered
  later.

## 9. Open

* **Validity under the rule of §6.** Whether a reference is bypassed depends on
  what a node holds, and a node holds a block back until each reference
  is held or bypassed. The bound on how long it waits, and the agreement
  of two nodes that come to hold the same blocks, are not proved.
* **Slow honest blocks.** A rule that bypasses fewer honest blocks, for
  example by counting witnesses from more than the next round, without
  losing the bound of §6 or §8.
* **A proof of safety for the third row of §7.** At `R = r + 3` it is
  the standard argument: `A` references an honest certificate, and `v`
  holds it and its votes. For a later anchor, a path of followed blocks
  from `A` to such a certificate must be shown to exist; a followed block
  may have every reference bypassed. A commit must also order the same
  history at every node.
* **Unordered honest blocks.** The bound of §8 assumes that `C` holds a
  block of round `r + 1` of every honest validator. When a slow honest
  block of that round is not ordered, Byzantine ordered blocks alone may
  keep a block of round `r` from being bypassed. The bound then follows
  only from the ordered blocks of round `r + 1`, at most one block of an
  author for each of them, and grows from round to round downward.
* **Between the horizon and the round of exposure.** Above `h`, S7
  bounds what a node holds from the round `m` on. Between `h` and `m`
  twins of `D` are bounded by the blocks one round above, at most one
  for each, which is not proved on the node.
* **Before the honest blocks arrive.** Under §6 and asynchrony, the last honest
  block of round `r + 1` may come late, and until then a node cannot tell
  a secret block from a late honest one.
* **Certificates under pruning.** Below the seal, back-dated joins are
  cut, so certificates may only be needed in the window.
* A bound on what one certificate may name, without the stall a cap
  causes.
* The size of §4, which is argued, not proved.
* Liveness of `clean` in general. The refusal sends a block of round `r`
  whose references join no pair of `E`; the requester then takes them,
  but may join other pairs, and the loop has no proved end.
