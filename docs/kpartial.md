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

Liveness is read on the record, from a round `R` on, for a quorum `T` of
correct validators. The premise is *responsiveness* (`RespondsFrom`): for
every slot led by `T`, `T` has a block two rounds above the slot, and each
block of `T` there carries votes from a quorum for one leader block of the
slot (`Responds`). A node produces this by waiting, before it builds two
rounds above a slot, until it holds a certificate for the slot's leader
block. It needs no timer when the leader is correct and the network is
timely: the voters of `T` are a quorum, so no wait depends on a Byzantine
validator. Partial synchrony as it is read elsewhere in the tree implies
responsiveness: from `R` to some round `N`, every block of `T` references
every block of `T` of the round below (`SynchronisedTo`), and `T` has a block
at every round (`SyncFrom`).

The schedule offers runs: past any slot, `c` consecutive slots led by `T`
(`FairRunOn`), each run spanning eligibility. A node decides once it holds
the blocks of `T` over the run with their references (`WithRefs`), and the
available sub-DAG below every leader block with a certificate up to the
run's end (`AvailBelow`). By Theorem 1 correct nodes hold all of these, and
the sub-DAG below a block depends only on that block's history, so it does
not change as the record grows.

**Theorem 4 (liveness; `Live.Statement`).** No bound on `K` is needed.

* *Synchrony implies responsiveness* (`Live.Weaker`). After `R`, every block
  of `T` two rounds above a slot led by `T` carries votes from all of `T`
  for the leader's block.
* *A responsive slot commits* (`Live.Commits`). The blocks of `T` two rounds
  above the slot are a quorum of certificates, so a node holding those
  blocks with their references commits the slot directly.
* *A committed run decides below it* (`Live.Descends`). A committed block
  has a certificate, so the node has fetched the sub-DAG below each anchor
  it uses, and its indirect test returns a commit or a skip. Each slot below
  the run takes its nearest committed eligible anchor, by induction
  downward.
* *Every slot is decided* (`Live.Progress`). Past any slot `k` and round `R`
  the schedule names a run from `b`, fixed before the record. On every
  record responsive among `T` from `R` to the run's end, a node holding
  what the run needs decides every slot below `b + c`.

With Theorem 3, every correct node eventually decides every slot, and all
decide each slot alike. Under three-round spacing `c = 1`; with one slot a
round, `c = 3`.

The order's inclusion results (Theorem 5) still assume synchrony: they need
every block of `T` to be referenced, which a node that builds as soon as it
holds a certificate does not ensure.

Theorem 7 (§11) shows that nodes following a waiting rule produce
responsiveness after synchrony.

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
| 4 Weaker | synchrony implies responsiveness | — |
| 4 Commits | a slot led by `T` commits directly | responsiveness |
| 4 Descends | a committed run decides every slot below it | — |
| 4 Progress | every slot is eventually decided | responsiveness, fair runs |
| 5 Local | a node reads a leader's output once fetched `D` rounds down | — |
| 5 Agrees | ledgers agree across nodes and over time | `K ≥ 3` |
| 5 Total | the ledger is a strict total order, causal within a slot | linear orders on authors and ids |
| 5 Settled | a block not output within `D` rounds never is | — |
| 5 Outputs | a leader of `T` outputs the blocks of `T` within `D` rounds | synchrony, `K ≥ 1` |
| 5 Included | every block of `T` enters the ledger | synchrony, a `T` slot every `D` rounds, `K ≥ 3` |
| 6 Decides | decisions read the band from `K − 1` rounds below the slot | — |
| 6 Progress | a node decides from a band of bounded length | responsiveness, fair runs |
| 6 Builds | building needs the last `K + 1` rounds | — |
| 6 Resumes | the ledger resumes from the band from `D + K` rounds below | `K ≥ 3` |
| 6 Counts, Window, AvailRound | `n` blocks a round without equivocation; with it, `≈ |C| f^(K−1)` per history and `≈ |C| f^(K+1)` per round of the available sub-DAG | — |
| 7 Built | every round is built | reactive rules |
| 7 CatchesUp | blocks of `f + 1` correct validators at a round bring all to it within `δ` | reactive rules |
| 7 Starts | the round after the last one reached before `G + τ` starts a reactive run | reactive rules |
| 7 Slow | each round is built within `δ + τ` | reactive run |
| 7 Fast | a round next to correct leaders takes `δ` | reactive run, `τ ≥ 2δ` |
| 7 Responsive | the run is responsive among the correct validators | reactive run, `τ ≥ 2δ` |
| 7 Commits | a slot among correct leaders commits within `3δ` | reactive run, `τ ≥ 2δ` |

## 9. Why a K-partial DAG

In Mysticeti a validator references a block only once it holds that block's
whole causal history. A validator that falls behind must fetch an unbounded
history before it can vote again; a Byzantine author can publish blocks
whose history is large or partly withheld, which correct validators then
chase; and taking part in consensus is tied to replicating all data. A
K-partial DAG bounds the obligation: a reference states only that the
history to depth `K` is held. What follows from the results above, and what
is argued only:

* *Bounded work to take part* (proved, §10). A validator references, and so
  votes and builds, after fetching `K + 1` rounds of history; a validator
  returning from an outage needs those rounds, not all it missed.
* *Bounded fetch to decide and to order* (proved). A decision from an anchor
  needs the sub-DAG from the anchor down to `K` rounds below the slot
  (Theorem 3), and a leader's output `D + K` rounds below it (Theorem 5).
* *Availability without a certification round* (proved). The sub-DAG below
  a certified block is held by correct nodes (Theorem 1); the rule of
  `f + 1` distinct authors does the work of an availability certificate, and
  a node never depends on Byzantine nodes for data.
* *Mysticeti's guarantees* (proved). The direct rule, and so the commit
  latency in rounds, is unchanged; agreement holds at `K ≥ 3`, liveness on a
  responsive record for every `K`, and the ledger is agreed, never retracted
  and totally ordered.
* *Weaker obligations* (argued). No reference to the author's own block is
  required, so a validator that crashed resumes without its own chain, and
  none must build at every round; no result uses either.
* *Bounded state* (proved in rounds, §10). A node decides from the rounds
  from `K − 1` below its lowest undecided slot, and resumes the ledger from
  `D + K` rounds below; how long others must retain these is open.

The costs are the loss of causal order across slots, blocks that no leader
outputs within `D` rounds and must be proposed again, a depth `D` set by the
schedule, and `K ≥ 3` with one reference per author for safety.

## 10. Bounds for deciding and restarting

No mechanism is added: no pruning and no exclusion of equivocators. The
bounds are stated in rounds, as a band of rounds a node needs, and then in
blocks. The blocks of `H` at round `ρ` or above are its *band from `ρ`*
(`Band`).

**Theorem 6 (bounds; `Bounds.Statement`).**

* *Decisions read a band* (`Bounds.Decides`). A node's decision of a slot at
  round `ρ + K − 1` or above, and not below `ρ`, is the same on its band from
  `ρ`. A block anchored at round `ρ + K` or above is anchored on the band,
  since its derivation reads only blocks above it and their histories to depth
  `K` (`AnchoredIn.band`), so the available sub-DAG, the indirect test and the
  fetch test above round `ρ + K` read only the band (`availIn_band_iff`,
  `linkedIn_band_iff`, `fetchedIn_band_iff`); the direct tests read rounds
  `σ(k)` to `σ(k) + 2` (`heldWithRefs_band`), and every slot a decision
  recurses to lies above (`nodeDecided_band_iff`).
* *Progress from a band* (`Bounds.Progress`). On a responsive run, a node holding
  the blocks of `T` over a run with their references, and the available
  sub-DAG below every certified leader up to the run's end from round `ρ`
  up, decides every slot below the run's end at round `ρ + K − 1` or above.
  So a node keeps only the rounds from `K − 1` below its lowest undecided
  slot, and the length of that band is bounded after synchrony by the
  distance to the next run (`nodeDecided_of_run_band`).
* *Building* (`Bounds.Builds`). A block of round `r + 1` referencing a quorum
  of distinct authors of round `r` is valid, and a node holding the
  histories to depth `K` of that quorum meets its obligation (`Obliged`)
  with its band from `r − K`. A restarting node therefore needs, to build,
  the last round at which it built (so as not to build twice at a round)
  and `K + 1` rounds of blocks.
* *Resuming the ledger* (`Bounds.Resumes`). At `K ≥ 3`, two nodes that
  decided every slot `D` rounds below `s` and above, and fetched those
  slots' leaders down to `D` rounds below `s`, give each block the same entry
  slot from `s` on. Neither needs a verdict of an earlier slot: a leader
  outputs only blocks `D` rounds below it or above, and a block of the
  available sub-DAG lies at or below its leader (`entersIn_resume`). By
  §5's `Fetchable` and the first item, a restarting node resumes the ledger
  at slot `s` from its band from `σ(s) − D − K`, with the executed state at
  `s` from a checkpoint.
* *Counting* (`Bounds.Counts`, `Bounds.Window`, `Bounds.AvailRound`).
  Without equivocation the record holds at most `n` blocks per round
  (`card_between_le`), so a band of `w` rounds holds at most `n w` blocks:
  `n (K + 1)` to build, `n (D + K + lag)` to restart. With equivocation and
  no further mechanism:
  - a history to depth `K` holds at most `N_0 + ⋯ + N_K` blocks, with
    `N_0 = 1` and `N_{d+1} = |C| + f · N_d`: each layer holds at most `|C|`
    blocks of correct authors, and a block references at most `f` Byzantine
    blocks (`card_layers_le`, `card_historyUpto_le`);
  - every Byzantine block of the available sub-DAG hangs at most `K` rounds
    below a *root*, a block of a correct author or an anchored block,
    through Byzantine blocks (`exists_root`), and a round holds at most
    `|C|(f + 1) + 1` roots, since an anchored Byzantine block has a correct
    referencer one round up (`card_anchored_le`, `card_roots_le`); so a round
    of the available sub-DAG holds at most
    `|C| + (|C|(f + 1) + 1)(1 + f + ⋯ + f^K)` blocks
    (`card_avail_round_le`).

  For `n = 100`, `f = 33`, `|C| = 67`:

  | `K` | history to depth `K` | available sub-DAG per round |
  |---|---|---|
  | 3 | 114,646 | 84,459,807 |
  | 4 | 3,783,587 | 2,787,173,766 |

  The per-round bound is of order `|C| f^(K+1)`. An adversary appears able
  to reach that order: in each of `|C|` partitions it makes every Byzantine
  validator equivocate once per round, one correct validator references that
  partition's blocks, and the Byzantine blocks of the partition reference
  each other, so each is anchored by `f + 1` distinct authors, and each
  anchored Byzantine block has up to `f^K` Byzantine blocks in its history to
  depth `K`. This construction is not formalised. A bound near `n` per round
  therefore needs a rule for equivocating authors.

Not proved: that persisting the last round built before sending suffices
to avoid equivocation after a restart, which needs a model of validators
over time; and how long correct nodes must retain a band, which needs a
quantitative liveness bound or a state transfer.

## 11. Reactive nodes in time

Responsiveness is a premise on the record; a model of time shows that the
waiting rule produces it. A *timeline* gives the blocks each validator holds
at each time, with their histories to depth `K`, and the time each block was
built (`Timeline`). A correct node builds above round `r` once it holds what
it waits for (`WaitsFor`): blocks of a quorum of distinct authors at round
`r` (`QuorumIn`), a leader block of every slot at round `r`, and a
certificate for a leader block of every slot at round `r − 1` (`CertIn`). It
also builds once it has held a quorum of round `r` for a timeout `τ`. Its
block references the leader blocks it holds one round below, and carries a
certificate for a leader two rounds below when it holds one. A node *behind*
builds above round `r` at once: it holds blocks of round `r + 1` by `f + 1`
authors other than itself (`BehindIn`), so a correct node has built that
round.

A timeline follows the *reactive rules* from round `R` to round `N`
(`ReactiveRules`) when correct nodes follow these rules there, keep what they
hold with its references, hold a correct block only once it is built, and
another author's correct block only after it is built; every correct
validator has a block at round `R`. From a time `G` on, every correct node
holds a correct block `δ` after it is built. Nodes pass on only correct
blocks: a Byzantine block reaches a node only among the references of a
block it holds, which it fetches from the node that sent it. It is a *reactive run* (`ReactiveRun`)
when, in addition, its correct blocks from round `R` on are built at `G + τ`
or later. The delay `δ` covers the downloads to depth `K`; nodes do not know
it, and only the timeout `τ` is configured.

A quorum spreads. A quorum holds blocks of `f + 1` correct authors, so once
a correct node holds a quorum of round `s` at a time `t ≥ G`, every correct
node holds `f + 1` correct blocks of round `s` by `t + δ`, is behind, and
has built at round `s`. A correct node's timer starts at a quorum, so a
correct leader's block is built within `δ` of the start of every correct
node's timer, and reaches the node within `2δ`: before the timer runs out
when `τ ≥ 2δ`. The same holds for the votes of all correct validators two
rounds above. A node that waited, or was behind, needs no timing argument:
by induction on build times, a correct block built behind rests on an
earlier correct block of its round, and eventually on one built on the wait
or the timer, whose author referenced the leader block and carried the
certificate it held; the node holds these references.

**Theorem 7 (reactive nodes; `Reactive.Statement`).** Under the reactive
rules from round `R` to round `N`:

* *Every round is built* (`Reactive.Built`). Every correct validator has a
  block at every round from `R` to `N`.
* *Nodes behind catch up within `δ`* (`Reactive.CatchesUp`). Once `f + 1`
  correct validators have built at a round by a time `t ≥ G`, every correct
  validator has built at the round by `t + δ`.
* *A reactive run starts* (`Reactive.Starts`). Let `R'` be the round after
  the last round from `R` on that a correct block reached before `G + τ`, or
  `R` if there is none. If `R' ≤ N`, the timeline is a reactive run from `R'`
  to `N`, and every correct validator has built at `R'` within `2δ + 2τ` of
  `G + τ` and of the time all built at `R`.

On a reactive run from round `R` to round `N`:

* *Each round is built within `δ + τ`* (`Reactive.Slow`) of the last correct
  block of the round below.
* *Rounds led by correct validators take `δ`* (`Reactive.Fast`). At
  `τ ≥ 2δ`, when the slots of a round `s ≥ R + 2` and of the round below have
  correct leaders, every correct validator builds above `s` within `δ` of the
  last correct block of round `s`; no correct node waits for its timeout.
* *The run is responsive* (`Reactive.Responsive`). At `τ ≥ 2δ`, the record is
  responsive among the correct validators from round `R + 1` to `N`, so
  Theorem 4 applies with `T` the correct validators.
* *A slot led by correct validators commits within `3δ`*
  (`Reactive.Commits`). At `τ ≥ 2δ`, when every slot from one round below a
  slot at round `r ≥ R + 2` to one round above it has a correct leader, every
  correct node commits the slot directly on what it holds `3δ` after the
  last correct block of round `r`.

The bounds depend on the actual delay `δ`, not on `τ`, except where a slot
next to the round has a Byzantine leader; there a round costs at most
`δ + τ`. No bound depends on `K`.

The rule for nodes behind is what lets nodes pass on only correct blocks. A
single correct block built on the timer does not bring other nodes to its
round within `δ`: its author's quorum may include Byzantine blocks that
reached it alone. Its `f + 1` correct blocks do, through the rule.

A witness (`LeanDagTest/KPartialDag/Reactive.lean`) shows that the premise is
consistent: one correct validator building a chain of blocks, all held at
time `0`, is a reactive run, and `Reactive.Commits` decides its slots. It
exercises none of the timing, since its delay is `0`.

## 12. Open questions

* Bounds: the cost of fetching the sub-DAG, and how long correct nodes must
  keep the histories they downloaded.
* Chain quality: the share of correct blocks in a leader's output.
* Inclusion counted on every committed leader rather than leaders of `T`:
  the references of any block include `f + 1` blocks of `T`, which suggests
  that any committed leader outputs the blocks of `T` two rounds or more
  below it.
* A storage bound linear in `K` under equivocation, which needs a rule for
  equivocating authors (§10).
* Quantitative liveness, which a retention bound needs.
* Crash recovery: that persisting the last round built suffices, with a
  model of validators over time.
