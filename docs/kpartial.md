# K-partial DAGs

This document studies the Mysticeti commit rule on a *K-partial DAG*, a DAG
substrate in which a correct node holds only part of the history of the
blocks it references. It states the safety, liveness and order results that
the Lean development `LeanDag/KPartialDag` proves; §8 lists them.

## 1. The substrate

A block carries a round, an author with its signature, a payload, and
references to blocks of the round below, each committed by its hash. The
references come from a quorum of `n − f` distinct authors, and a block
references at most one block of each author. Two things differ from the
DAG of Mysticeti:

1. a block need not reference its author's own block of the round below;
2. a correct author that references a block has downloaded that block's
   history to depth `K` only, not its whole history.

A correct node need not build a block at every round; no result assumes it.

Hashes fix the whole history of every block, so the record of a run is an
ordinary block record (`KRecord`, at the validity `KValid`). What changes is
what a correct node holds of it. A block is *held by a correct node* when it
is a correct author's block, or lies in the history to depth `K` of a block
that a correct author's block references (`CorrectHeld`).

The rule of one reference per author is a validity condition: without it a
correct voter could reference two blocks of a Byzantine leader at one round,
and both could be certified. No result uses a reference to the author's own
block.

## 2. The commit rule

The direct tests read three rounds. A round-`r` block `L` is directly
committed when blocks of a quorum of distinct authors at round `r + 2` each
reference votes for `L` from a quorum (`DirectCommit`). It is directly
skipped when blocks of a quorum of distinct authors at round `r + 1` do not
reference it (`DirectSkip`). A node holding those blocks decides as the
record does.

Mysticeti's indirect rule decides a slot through the nearest committed
anchor above it, by whether the anchor's history holds a certificate for
the slot's block. On a K-partial DAG that history may reach below what a
correct node holds, since the anchor may lie many rounds above the slot. A
certificate that lies only on a branch of Byzantine blocks may be held by
one correct node and not by another, so two nodes reading the anchor's
history on what they hold may disagree. This is so even when every correct
node builds a block at every round. The indirect test is therefore read on
a part of the anchor's history that is fixed by the record and that every
correct node can fetch.

## 3. The available sub-DAG

Below a block `A`, a block is *anchored* when it is `A`, or when blocks of
`f + 1` distinct authors reference it, each in the history to depth `K` of
an anchored block (`AnchoredBelow`). The *available sub-DAG* below `A` is
the union of the histories to depth `K` of the anchored blocks (`Avail`).
The indirect test asks whether the sub-DAG below the anchor holds a
certificate for the slot's block together with the certificate's
references, which carry its votes (`AvailLinked`).

**Theorem 1 (the available sub-DAG; `Avail.Statement`).**

* *Held* (`Avail.Held`). Below a block with a certificate, every block of
  the sub-DAG is held by a correct node. Each block of the sub-DAG lies in
  the history to depth `K` of `A`, which a correct voter of the certificate
  downloaded, or of a block that a correct author's block of the sub-DAG
  references; among `f + 1` distinct authors one is correct.
* *Broad* (`Avail.Broad`). At `K ≥ 2`, every round two or more below `A`
  holds an anchored block of a correct author. Blocks of a quorum of
  distinct authors at one round reference some correct author's block of
  the round below from `f + 1` of those authors, by a double count: each
  references `n − 2f` or more correct blocks, and a correct author has one
  block a round.
* *Linked* (`Avail.Linked`). At `K ≥ 3`, if a round-`r` block is directly
  committed and `A` lies at round `r + 3` or above, the sub-DAG holds a
  certificate for it with its references. A block of round `r + 3` in the
  sub-DAG references a certificate of a correct author, since its references
  and the certificates come from two quorums.
* *Exclusive* (`Avail.Exclusive`). A block for which the sub-DAG holds a
  certificate is not directly skipped.

## 4. Agreement

The commit rule is an anchored rule of `Common/Anchored.lean` (`kRule`): the
direct commit and skip, at wave two, with one rung whose link is
`AvailLinked`.

**Theorem 2 (agreement; `Agreement.Statement`).** At `K ≥ 3` the rule
satisfies the laws of an anchored rule (`Agreement.Laws`), so two views of
one record decide each slot alike (`Agreement.Agrees`).

Two certificates for blocks of one author at one round certify the same
block: their votes come from two quorums, so a correct author's one block of
the round above references both, and it references one block of each
author. With Theorem 1, a commit and a skip exclude each other, and a direct
commit is linked from every eligible anchor.

## 5. What a node reads

A node holds a set `H` of blocks of the record, not closed under histories.
It reads the available sub-DAG below an anchor on `H` (`AnchoredIn`,
`AvailIn`), and links a candidate when it holds there a certificate for it
with its references (`LinkedIn`). It has *fetched the sub-DAG down to round
`ρ`* when it holds the anchor's history to depth `K` and the history to depth
`K` of every block that blocks of `f + 1` distinct authors of the sub-DAG
above round `ρ` reference (`FetchedIn`). It decides by the commit rule read
on what it holds (`NodeDecided`). The direct tests count the certificates and
blamers it holds with their references. The indirect skip of a slot at round
`r` needs the sub-DAG below the anchor fetched down to round `r + 1`, where
the certificate's references lie.

**Theorem 3 (what a node reads; `Node.Statement`).**

* *Local* (`Node.Local`). The indirect test and the fetch test read only
  `H`: they are the same on every record whose blocks agree on `H`.
* *Fetchable* (`Node.Fetchable`). A node holding the sub-DAG below an anchor
  down to round `ρ − K` has fetched it down to `ρ`, for `ρ` at most the
  anchor's round. To decide a slot at round `r` from an anchor `A`, a node
  fetches the sub-DAG between the round of `A` and round `r + 1 − K`, which
  by Theorem 1 it can fetch from correct nodes.
* *Sound* (`Node.Sound`). A decision a node takes on what it holds is a
  decision of the commit rule on every view holding `H`. Fetched down to
  `ρ`, the sub-DAG read on `H` is the record's above `ρ`.
* *Agreement* (`Node.Agrees`). At `K ≥ 3`, two nodes decide each slot alike.

## 6. Liveness

Partial synchrony is read on the record. From a round `R` on, every block
of an author in a quorum `T` of correct validators references every block
of an author in `T` of the round below, and `T` has a block at every round
up to some round `N` (`SyncFrom`). The schedule offers runs: past any slot,
`c` consecutive slots led by `T` (`FairRunOn`), each run spanning
eligibility. A node decides once it holds the blocks of `T` over the run
with their references (`WithRefs`), and the available sub-DAG below every
leader block with a certificate up to the run's end (`AvailBelow`). By
Theorem 1 correct nodes hold all of these, and the sub-DAG below a block
depends only on that block's history, so it does not change as the record
grows.

**Theorem 4 (liveness; `Live.Statement`).** No bound on `K` is needed.

* *A leader in `T` commits* (`Live.Commits`). After `R`, every block of `T`
  two rounds above the slot carries votes from all of `T` for the leader's
  block, so a node holding those blocks with their references commits the
  slot directly.
* *A committed run decides below it* (`Live.Descends`). A committed block
  has a certificate, so the node has fetched the sub-DAG below each anchor
  it uses, and its indirect test returns a commit or a skip. Each slot below
  the run takes its nearest committed eligible anchor, by induction
  downward.
* *Every slot is decided* (`Live.Progress`). Past any slot `k` and round `R`
  the schedule names a run from `b`, fixed before the record. On every
  record synchronous among `T` from `R` to the run's end, a node holding
  what the run needs decides every slot below `b + c`.

With Theorem 3, every correct node eventually decides every slot, and all
decide each slot alike. Under three-round spacing `c = 1`; with one slot a
round, `c = 3`.

## 7. The order

A committed leader `L` outputs the blocks of its available sub-DAG at most
`D` rounds below it (`Out`); a node reads them on what it holds (`OutIn`).
Its ledger after slots `0, …, n − 1` is what the leaders it committed there
output (`LedgerIn`), and a block enters the ledger at the first committed
slot whose leader outputs it (`EntersIn`). Within one slot, blocks are
ordered by round, then author, then id (`KeyLt`); the id separates the
blocks of an equivocating author. A block precedes another in the ledger
when it enters at an earlier slot, or at the same slot and earlier within it
(`PrecedesIn`). By Theorem 1, every block a leader outputs is held by a
correct node.

**Theorem 5 (the order; `Order.Statement`).**

* *Local* (`Order.Local`). What a node reads of a leader's output lies in
  the output, and is all of it once the node has fetched the sub-DAG down to
  `D` rounds below the leader, that is, between the leader's round and
  `D + K` rounds below it.
* *Agreement* (`Order.Agrees`). At `K ≥ 3`, what a node outputs after `n`
  slots, it and every other node output at the same slot and in the same
  order after `n' ≥ n` slots. Ledgers agree, and none is retracted.
* *Total order* (`Order.Total`). The ledger order is irreflexive, transitive
  and total on the ledger, and a reference of a block entering at the same
  slot precedes it.
* *Settled* (`Order.Settled`). A leader outputs only blocks at most `D`
  rounds below it, so a block not in the ledger once every slot up to `D`
  rounds above it is decided never enters.
* *Output* (`Order.Outputs`). After synchrony from `R`, at `K ≥ 1`, a leader
  of `T` outputs every block of `T` from round `R` on at most `D` rounds
  below it. The round just below lies in the leader's history to depth `K`.
  Each block of `T` further down is referenced by the blocks of `T` of the
  round above, `n − f` distinct authors in the sub-DAG, so it is anchored,
  round by round downward.
* *Inclusion* (`Order.Included`). If every `D` consecutive rounds hold a
  slot led by `T`, then after synchrony every block of `T` enters the ledger
  of a node that has decided every slot up to `D` rounds above it.

The ledger carries no causal guarantee across slots: a block may enter
before one of its ancestors, or without it. The order is agreed, so
replicas that execute it reach one state; a consumer that needs causal
order drops the blocks whose references it has not seen in the ledger.

The depth `D` sets what is output, and `K` how far below that a node
fetches. Safety holds for every `D`. Inclusion asks that every `D` rounds
hold a slot led by `T`, so `D` is bounded below by the schedule, not by `K`.
Under round robin with one leader a round, `D = f + 1` suffices, and with `ℓ`
leaders a round, `D = ⌈f/ℓ⌉ + 1`; these counts are not formalised. With a smaller `D`, a block of a correct author may
be dropped during a run of skipped slots; by `Order.Settled` its author
knows so once every slot up to `D` rounds above it is decided, and can
propose its payload again.

## 8. Results

| Theorem | Statement | Assumes |
|---|---|---|
| 1 Held | below a certified block, the sub-DAG is held by correct nodes | — |
| 1 Broad | every round two or more below the anchor has a correct anchored block | `K ≥ 2` |
| 1 Linked | a direct commit is linked through the sub-DAG of an anchor three rounds up | `K ≥ 3` |
| 1 Exclusive | a link excludes a direct skip | — |
| 2 Laws, Agrees | the rule is an anchored rule; views decide each slot alike | `K ≥ 3` |
| 3 Local | the node's tests read only what it holds | — |
| 3 Fetchable | holding the sub-DAG down to `ρ − K` fetches it down to `ρ` | — |
| 3 Sound | a node's decision is the rule's on every view holding it | — |
| 3 Agrees | two nodes decide each slot alike | `K ≥ 3` |
| 4 Commits | a leader in `T` commits directly | synchrony |
| 4 Descends | a committed run decides every slot below it | — |
| 4 Progress | every slot is eventually decided | synchrony, fair runs |
| 5 Local | a node reads a leader's output once fetched `D` rounds down | — |
| 5 Agrees | ledgers agree across nodes and over time | `K ≥ 3` |
| 5 Total | the ledger is a strict total order, causal within a slot | linear orders on authors and ids |
| 5 Settled | a block not output within `D` rounds never is | — |
| 5 Outputs | a leader of `T` outputs the blocks of `T` within `D` rounds | synchrony, `K ≥ 1` |
| 5 Included | every block of `T` enters the ledger | synchrony, a `T` slot every `D` rounds, `K ≥ 3` |

## 9. Why a K-partial DAG

In Mysticeti a validator references a block only once it holds that block's
whole causal history. A validator that falls behind must fetch an unbounded
history before it can vote again; a Byzantine author can publish blocks
whose history is large or partly withheld, which correct validators then
chase; and taking part in consensus is tied to replicating all data. A
K-partial DAG bounds the obligation: a reference states only that the
history to depth `K` is held. What follows from the results above, and what
is argued only:

* *Bounded work to take part* (argued). A validator references, and so votes
  and builds, after fetching `K` rounds of history; a validator returning
  from an outage needs the last `K` rounds, not all it missed.
* *Bounded fetch to decide and to order* (proved). A decision from an anchor
  needs the sub-DAG from the anchor down to `K` rounds below the slot
  (Theorem 3), and a leader's output `D + K` rounds below it (Theorem 5).
* *Availability without a certification round* (proved). The sub-DAG below
  a certified block is held by correct nodes (Theorem 1); the rule of
  `f + 1` distinct authors does the work of an availability certificate, and
  a node never depends on Byzantine nodes for data.
* *Mysticeti's guarantees* (proved). The direct rule, and so the commit
  latency in rounds, is unchanged; agreement holds at `K ≥ 3`, liveness under
  partial synchrony for every `K`, and the ledger is agreed, never retracted
  and totally ordered.
* *Weaker obligations* (argued). No reference to the author's own block is
  required, so a validator that crashed resumes without its own chain, and
  none must build at every round; no result uses either.
* *Bounded state* (argued). A node keeps windows of depth `K` to build and
  `D + K` rounds to order, which suggests a garbage collection rule.

The costs are the loss of causal order across slots, blocks that no leader
outputs within `D` rounds and must be proposed again, a depth `D` set by the
schedule, and `K ≥ 3` with one reference per author for safety.

## 10. Storage and restart (notes, not formalised)

*Building.* A node building at round `r + 1` references a quorum `Q` of
round-`r` blocks and holds `W = ⋃_{x ∈ Q} historyUpto K x`, rounds `r − K` to
`r`. Building needs no decision and nothing below `r − K`.

*Deciding and ordering.* A direct verdict for a slot at round `s` reads rounds
`s` to `s + 2`. An indirect verdict from an anchor at round `a` reads the
sub-DAG from `a` down to `s + 1 − K`; the distance `a − s` is bounded after
synchrony by the run structure and not before. A leader's output reads
`D + K` rounds below it.

*The bound.* With one block per author and round in the band, a node holds
`n (K + 1)` blocks to build, and `n (max(Δ, D) + K + 1)` to decide and order,
for `Δ` the largest distance from a pending slot to its anchor. Equivocation
breaks the bound: with `N_d` the window's blocks at round `r − d`, a block
references one block per author, so `N_0 ≤ n` and `N_d ≤ n + f N_{d−1}`, and
the window may hold of the order of `n f^K` blocks. Three treatments:
(a) a bound `n (K + 1) + E` charged to the `E` extra blocks per author and
round in the window, with no rule change; (b) a cap of two blocks per author
and round, the pair being evidence and the author excluded, giving about
`2 n (K + 1)` but reopening `Avail.Held` and `Avail.Linked`; (c) refusing to
reference blocks whose window holds an equivocation, which likely breaks
liveness, since a Byzantine author can split correct nodes between two
versions. Undecided.

*Restart.* A restarting node needs:

1. on disk, the last round it built at, written before each block is sent,
   so that it never builds twice at one round; it needs no chain of its own;
2. to build again, a quorum of current blocks of distinct authors and their
   windows to depth `K`, which the authors of correct blocks hold;
3. to decide new slots, nothing older than the recent band and the anchor
   distance;
4. to resume the ledger at slot `s` without duplicates, the verdicts and
   outputs of the slots in rounds `slotRound s − D` to `slotRound s`, since a
   block output at round `ρ` could have been output earlier only by leaders
   at rounds `ρ − D` to `ρ`; the executed state up to `s` comes from a
   checkpoint;
5. that some correct node still keeps these blocks, which is the retention
   rule of §11.

*Statements to prove later.* W1, the window holds at most `n (K + 1)` blocks
without equivocation, or the recurrence in general; W2, holding `W` suffices
to build a valid block meeting the obligation; W3, direct verdicts read only
rounds `s` to `s + 2`; W4, entry and order from slot `s` on are fixed by the
verdicts and outputs of the slots of the `D` rounds before `s` and the later
verdicts; and, with a model of nodes over time, that a restarted node builds
no second block at a round.

## 11. Open questions

* Bounds: the cost of fetching the sub-DAG, and how long correct nodes must
  keep the histories they downloaded.
* Chain quality: the share of correct blocks in a leader's output.
* Inclusion counted on every committed leader rather than leaders of `T`:
  the references of any block include `f + 1` blocks of `T`, which suggests
  that any committed leader outputs the blocks of `T` two rounds or more
  below it.
* The treatment of equivocation in the storage bound (§10).
* Quantitative liveness, which a retention bound needs.
* Crash recovery without the author's own chain.
