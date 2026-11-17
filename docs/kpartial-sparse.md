# Sparse K-partial DAGs

This document adapts the K-partial DAG of `docs/kpartial.md` to sparse
blocks, after Bluestreak [PVM26]: a block that references a leader of the
round below references nothing else but its author's block, and a block
claims in its payload the leaders it has seen certified. The Lean
development is `LeanDag/KPartialSparse`. The available sub-DAG (Theorem 1),
agreement of the commit rule at the scheme's two-round and three-round rows
(Theorem 2), what a node reads (Theorem 3), liveness (Theorem 4), nodes in
time (Theorem 5) and the order (Theorem 6) are proved; §9 lists what is
open.
`LeanDagTest/KPartialSparse/Witness.lean` is a record on which Theorems 1 to
4 apply, and `LeanDagTest/KPartialSparse/Timed.lean` a timed run of it for
Theorem 5.

## 1. The substrate

The fault model is that of `docs/kpartial.md` §1: at most `f` Byzantine
validators, at most `c` correct validators that crash for good,
`n ≥ 3f + 2c + 1`, and the quorum `q = n − f − c`. A schedule fixes the
leaders of each round before the run (`Leaders`); every round has one or
more. A block carries a round, an author, a payload and references, and
is valid when (`SValid`):

1. its references lie below it, those to other authors one round below,
   at most one per author;
2. a non-genesis block is *dense* or *sparse*. A dense block references
   blocks of `q` distinct authors one round below (`Dense`). A sparse block
   references its author's block one round below and, besides it, only
   leader blocks one round below, at least one (`Sparse`);
3. a leader's block is dense.

A block references its author's latest block, which may lie more than one
round below, so a validator that restarts can jump rounds; its first block
after a gap is then dense (rule 2). The record of a run is a block record
at this validity (`SRecord`). Correct authors keep *chains*: a correct
author's block references a block of its own at or above each of its
earlier blocks (`Chains`).

## 2. Claims

A payload names the blocks it claims certified (`ClaimFormat`). A block `L`
is *certified* at threshold `t` when blocks of `t` distinct authors one
round above reference it (`Certified`). A correct author references a
block only when every claim in that block's history to depth `K` names a
certified block (`Checks`). It need not check claims deeper down: the
commit rule reads claims only in the available sub-DAG, and Theorem 1
shows that a correct author checked each of those.

## 3. The available sub-DAG

Below a block `A`, a block `x` is an *anchor point* when it is `A`, which
brings its history to depth `K`, or when blocks of the sub-DAG from
`f + c + 1` distinct authors each reach `x` through one of their references
`m` and `i ≤ K` further steps; `x` then brings its history to depth `K − i`,
and the history of `m` to depth `i − 1`, through which the path runs, lies
in the history some anchor point brings (`Anchored`). At `i = 0` the authors
reference `x`; at `i = 1` they reach it in two steps, the two cases of
`docs/kpartial.md` §3, where the second needs crashes and here does not. A
correct author holds the history to depth `K` of each block it references,
so one of the `f + c + 1` authors holds what `x` brings and checked its
claims; a node holding the sub-DAG holds the path (§5). The *available
sub-DAG* below `A` is the union of the histories the anchor points bring
(`Avail`).

The sub-DAG needs a depth (`Deep`): `K ≥ 6` under the spreading condition
`(n − f)(f + c) < q(q − f)`, which holds without crashes
and at `n ≥ 5f + 3c + 1`; or `K ≥ 10` at any `n ≥ 3f + 2c + 1`.

**Theorem 1 (the available sub-DAG; `Avail.Statement`).**

* *Linked* (`Avail.Linked`). At the depth the sub-DAG needs, with correct
  chains: if blocks
  of `cm` distinct authors at round `ρ + 2` claim `L` and `n + f < q + cm`,
  then below a leader block at round `ρ + 3` or above the sub-DAG holds a
  claim for `L` at round `ρ + 2`.
* *Backed* (`Avail.Backed`). When correct authors check claims,
  below a block that a correct author references every claim in the
  sub-DAG names a certified block.
* *Held* (`Avail.Held`). Below a block that a correct author
  references, every block of the sub-DAG is held by a correct node
  (`CorrectHeld`).

The proof of *Linked* has four steps.

1. *Two-step reach* (`card_reach2`). Every block at round `ρ + 2` reaches, in
   two steps, round-`ρ` blocks of `q − f` correct authors or more. A sparse
   block reaches them through a leader block it references, which is
   dense. A dense block references blocks of `q − f` correct authors one
   round below. If one of them is dense, the block reaches through it.
   Otherwise each of them is sparse and references its author's block of
   round `ρ` (rule 2), and these are blocks of distinct correct authors.
2. *A new anchor point*, by one of two counts.
   * Under the spreading condition (`exists_correct_named`,
     `exists_reached`): blocks of the sub-DAG from a quorum of distinct
     authors, with their references in the sub-DAG, reach some correct
     author's round-`ρ` block from `f + c + 1` of those authors. This is the
     count of `docs/kpartial.md` §3, *Broad*, taken two steps down.
   * At any `n ≥ 3f + 2c + 1` (`exists_core_reached`): let `M` be the correct
     blocks two rounds below a quorum that some block of the quorum reaches
     in two steps, `m` of them. Each block of the quorum reaches `q − f` of
     `M`, and each block of `M` reaches `q − f` correct blocks two rounds
     further down. Counting, some such block `x` is reached by more than
     `m − (q − f)` blocks of `M`, since `(n − f)(q − f) > m(f + c)` when
     `q − f > f + c` (`core_arith`). So every block of the quorum reaches a
     block of `M` that reaches `x`: all of them reach `x` in four steps. This
     is the two-step core of `docs/kpartial.md` §3, *Core*, with two-step
     layers.
3. *Descent* (`recurs_spread`, `recurs_core`, `denseAt_window`). A dense
   block within one step of an anchor point gives, from its references, an
   anchor point three rounds down (first count) or five (second). That
   anchor point is dense, or it is sparse and references a leader block one
   round lower, which is dense. So dense blocks near anchor points recur at
   most four, or six, rounds apart, and one lies in every such window above
   round `u`.
4. *Overlap* (`linked_count`). The references of that dense block are blocks
   of `q` distinct authors one round below it. Of blocks at round `u` from
   `cm` distinct authors, they share `q + cm − n − f` correct authors or
   more, and each such author's chain leads from its referenced block down
   to its block at round `u`, within the history the anchor point brings at
   the depth the sub-DAG needs. With claims at round `ρ + 2` and
   `n + f < q + cm`, one claim lies in the sub-DAG.

*Backed* and *Held* follow from the definition of anchor points
(`exists_holder`). Among `f + c + 1` distinct authors one is correct. It
references a block whose history to depth `K` contains the history the
anchor point brings, so it holds that history and checked its claims. For `A` itself, the premise supplies the correct author.

Together, if a quorum claims `L` directly, an anchor above finds a claim for
`L` in its sub-DAG; and any claim found there names a certified block. With
`cm = q` at `n = 3f + 1`, `n + f < q + cm` holds.

## 4. The commit rule and agreement

The rule runs the scheme's rows (`Row`). In a *three-round row* a claim
stands for a certificate: two certificate thresholds, a certificate and a
skip threshold, and the quorum and the commit threshold each exceed
`n + f`, and the link is one claim. In a *two-round row* a vote is its own
certificate, and the scheme's two-round inequalities hold at the quorum
`q = n − f − c`; sparse blocks still carry votes, since a vote is a
reference. The certificates of a round-`r` block are its votes at round
`r + 1` or its claimers at round `r + 2` (`certsFor`, `Certifies`). The commit
rule (`sRule`) is an anchored rule of `Common/Anchored.lean`, at the row's
wave:

* *direct commit*: certificates for the candidate from `commitThreshold`
  distinct authors;
* *direct skip*: `skipThreshold` authors whose block one round above
  references no candidate of the slot;
* *link*: certificates for the candidate from `linkSize` distinct authors in
  the available sub-DAG below the anchor (`CertLinked`); twins are broken by
  the least identifier;
* *anchor*: in a three-round row, a certified block.

The rule asks of the schedule and the record (`Disciplined`) that each
slot's leader leads its round on the substrate, that correct authors keep
chains and check claims (§1, §2), and that a correct author claims only
certified blocks (`Truthful`).

**Theorem 2 (agreement; `Agreement.Statement`).**

* *Laws* (`Agreement.Laws`). At a row and the depth the sub-DAG needs, the
  rule meets the laws of an anchored rule on a disciplined schedule and
  record. Hybrid Mysticeti is therefore safe at every crash bound, at
  `K ≥ 10`.
* *Agreement* (`Agreement.Agrees`). So two views of one record decide each
  slot alike.
* *Rows* (`Agreement.Rows`). Without crashes, Mysticeti and Cordial Miners
  are rows and the spreading condition holds, and Blue Bottle is a row at
  `n ≥ 5f + 1`; under any crash bound, Hybrid Mysticeti is a row, and
  Orcaella is a row at `n ≥ 5f + 3c + 1`, where the spreading condition
  holds.

A direct commit certifies its block at the row's *commit strength*: its
votes in a two-round row, and the certificate threshold in a three-round
row, since one of its claimers is correct and claims truthfully
(`certified_of_commit`). A link certifies its block at the *link strength*:
its votes, or the certificate threshold, since a correct voter references
the certified anchor and Theorem 1 *Backed* applies (`certified_of_link`).
The row makes each pair among two commits, a commit and a skip, a commit and
a link, and a link and a skip exceed `n + f` (`row_arith`). Two certified
blocks of one author and round whose strengths exceed `n + f` are one: their
voters share a correct author, whose one block there references one block of
each author (`eq_of_certified`). A certified block and a skip whose strengths
exceed `n + f` exclude each other the same way (`not_certified_skip`).
Visibility generalises Theorem 1 *Linked* to a count (`linked_count`): below
a leader block above round `u`, of blocks at round `u` from `cm` distinct
authors, the sub-DAG holds those of `q + cm − n − f` authors or more, which
the row makes `linkSize` or more (`certLinked_of_commit`).

## 5. What a node reads

A node holds a set `H` of blocks of the record. It reads anchor points on `H`
when it holds the history each brings and the path through which it is
reached, which lies in the history an anchor point brings
(`AnchoredIn`, `AvailIn`), and links a candidate when it
holds there a claim for it two rounds above the slot (`LinkedIn`). It has
*fetched the sub-DAG down to round `ρ`* when it holds the anchor's history to
depth `K`, and the history every anchor point brings when the blocks of the
sub-DAG on `H` that reach it lie above `ρ` (`FetchedIn`). It decides by the
commit rule read on `H` (`NodeDecided`): the direct tests count the claimers
and blamers it holds, and the indirect tests need the sub-DAG fetched down
to the round of the slot's claims. A claim is read from the claiming block's
payload alone, so a node need not hold the claimers' references.

**Theorem 3 (what a node reads; `Node.Statement`).**

* *Local* (`Node.Local`). The link and the fetch test read only `H`: they
  are the same on every record whose blocks agree on `H`.
* *Fetchable* (`Node.Fetchable`). A node holding what every anchor point
  brings has fetched the sub-DAG down to every round. Unlike
  `docs/kpartial.md` §5, the bound is not a number of rounds: a block's
  reference to its author's latest block may skip rounds, so a history to
  depth `K` may span more than `K` rounds.
* *Sound* (`Node.Sound`). A decision a node takes on what it holds is a
  decision of the commit rule on every view holding `H`. Fetched down to
  `ρ`, the sub-DAG read on `H` is the record's at and above `ρ`, since an
  anchor point lies below the blocks that reach it.
* *Agreement* (`Node.Agrees`). At a row and the depth the sub-DAG needs, on
  a disciplined schedule and record, two nodes decide each slot alike.
* *Checked* (`Node.Checked`). A node *backs* a claim for `L` when it holds `L`
  and votes for it from `t` distinct authors one round above (`Backs`); this
  reads only what it holds. If each correct block was built by a node holding
  blocks of the record that back its claims and every claim in the history
  to depth `K` of each of its references (`BuildsChecked`), then correct
  authors check and claim truthfully (`Checks`, `Truthful`).

The votes behind a claim lie outside every history, so `BuildsChecked` asks a
correct node to fetch them; a correct claimer holds them.

## 6. Liveness

Liveness is read on the record, from a round `R` on, for a quorum `T` of
correct validators. *Synchrony* in sparse terms (`SyncFrom`): `T` has a block
at every round; one round above a slot led by `T`, every block of `T`
references every leader block of the slot; and two rounds above a block that
every block of `T` one round up references, every block of `T` claims it.
*Responsiveness* (`Responds`, `RespondsFrom`): for every slot led by `T`, `T`
has blocks at the round of the slot's certificates (`certRound`), and each
certifies one leader block of the slot. A node decides a run once it holds the
blocks of `T` over the run (`HeldBy`) and the available sub-DAG below every
leader block up to the run's end (`AvailBelow`). A row is *live* when its
commit and certificate thresholds are at most the quorum (`LiveRow`).

**Theorem 4 (liveness; `Live.Statement`).**

* *Synchrony implies responsiveness* (`Live.Weaker`), at every row: the
  leader block of a slot led by `T` is referenced by every block of `T` one
  round up, so it is certified by every block of `T` there or two rounds up.
* *The votes behind a claim are there* (`Live.Backable`). Under synchrony, a
  node holding a leader block of a slot led by `T` and the blocks of `T` one
  round above it backs a claim for it (§5) at any threshold within the
  quorum. So a correct node can meet `BuildsChecked` for the claims of `T`.
* *A responsive slot commits* (`Live.Commits`). At a live row, a node holding
  the blocks of `T` at the round of a slot's certificates commits the slot
  directly: they are certificates from `|T| ≥ q` authors.
* *A committed run decides below it* (`Live.Descends`). A node holding the
  available sub-DAG below every leader block up to slot `n`, which has
  committed every slot from `b` to `n`, decides every slot below `b` that `n`
  may anchor: holding the sub-DAG fetches it (Theorem 3), so the indirect test
  returns the least linked candidate or a skip.
* *Every slot is decided* (`Live.Progress`). Past any slot and round `R`, a
  schedule offering runs of slots led by `T` names a run, fixed before the
  record; on every record responsive among `T` from `R` to the run's end, a
  node holding what the run needs decides every slot below its end, at a live
  row.

With Theorem 3, every correct node that holds what a run needs decides every
slot below it, and all decide each slot alike.

## 7. Nodes in time

Nodes follow timed rules from round `R` to round `N` (`TimedRules`), with the
nodes of a quorum `T` correct and up from time `G`, message delay `δ` from
`G`, a timeout `τ` and a grace period `γ`; the timeline of held blocks and
build times is that of `docs/kpartial.md` §11 (`Timeline`). Before building
above round `r`, a node waits for what the sparse policy needs (`WaitsFor`):
a quorum at round `r`, a leader block of every slot at round `r`, and votes
from a quorum for a leader block of every slot at round `r − 1`. It builds
once it has held these for `γ`, once it has held a quorum of round `r` for
`τ`, or once it is behind round `r + 1`, holding blocks of `f + c + 1` other
authors there (`BehindIn`). A correct block references a leader block of each
slot one round below, led by a correct validator, whose leader block its
author holds (`votes`), so it is
sparse when it holds the leaders and dense otherwise, and claims each leader
block two rounds below for which its author holds votes from a quorum
(`claims`). Two delivery rules carry what a dense DAG carries in references:
a node holding a correct block above round `R` holds a quorum of the round
below, as its author did (`grounded`), and the votes behind its claims
(`backed`). Bluestreak's round-advance messages and its acceptance of a block
only once its claims can be backed realise them. A *timed run* (`TimedRun`)
adds that `T` has reached round `R` (`TimedStarted`) and built there from
`G + τ` on.

Crashes and restarts are those of `docs/kpartial.md` §11: before `G`, correct
nodes may crash and restart, holding after a restart only what they keep on
disk. A correct node keeps on disk every block it has built (`stores`) and
holds what it keeps there (`disk_held`); it may also keep the histories to
depth `K` of its blocks' references (`KeepsHistory`). From `G` on, the nodes
of `T` are up and keep what they hold. Persisting the last round built
(`Persists`) and building above the disk (`BuildsAboveDisk`) read only the
block map, so `docs/kpartial.md` Theorem 7, *Persisted* and *OnDisk*, apply to
the sparse record as they stand: a correct node builds at most one block a
round across restarts.

**Theorem 5 (nodes in time; `Reactive.Statement`).**

* *Built* (`Reactive.Built`). On a timed run, every validator of `T` reaches
  every round from `R` to `N`.
* *Catching up* (`Reactive.CatchesUp`). Once a node of `T` holds a quorum at
  round `s` at a time `t ≥ G`, every validator of `T` has reached round `s`
  by `t + δ`.
* *Slow* (`Reactive.Slow`). At `δ < γ ≤ τ`, each round is built by every
  validator of `T` within `δ + τ` of the round below.
* *Fast* (`Reactive.Fast`). At `τ ≥ 2δ` and `δ < γ ≤ τ`, a round whose slots
  and the slots one round below are led by `T` is built within `δ + γ`.
* *Synchronised* (`Reactive.Synchronised`). At `τ ≥ 2δ` and `δ < γ ≤ τ`, a
  timed run is synchronous among `T` from round `R + 1` (§6), so responsive at
  every row.
* *Commits* (`Reactive.Commits`). At a live row, `τ ≥ 2δ` and `δ < γ ≤ τ`,
  when the slots around a slot are led by `T`, every node of `T` commits the
  slot directly within `3δ + 2γ` of `T` building its round.
* *Starts* (`Reactive.Starts`). Under the rules started at round `R`, the
  round after the last round a node of `T` reached before `G + τ`, or `R`,
  starts a timed run, which every validator of `T` reaches within `2δ + 2τ` of
  `G + τ` and of the time all reached `R`.
* *Resumes* (`Reactive.Resumes`). With any crashes and restarts before `G`,
  once a validator of `T` has built above round `R` by `G`, a timed run starts
  above `R`, and every validator of `T` reaches it by `G + 3δ + 3τ`: its block
  is on its disk, reaches every node of `T` within `δ`, and grounds a quorum
  below it.
* *Checked* (`Reactive.Checked`). Timed nodes that reference a block only once
  it is referenceable on what they hold (§2, `Referenceable`) and claim only
  what they back (`TimedChecks`) meet the record's claim disciplines,
  `Checks` and `Truthful`.
* *Unblocked* (`Reactive.Unblocked`). The wait never blocks a correct block:
  when delivery carries what a block's author held, the history to depth `K`
  of each reference with the votes behind every claim there, and the votes
  behind the block's own claims, a correct node holding a correct block holds
  it referenceable. So the votes for a leader of `T`, and the quorum a dense
  block references, are never held up by the check.
* *Claimable* (`Reactive.Claimable`). Every claimer of `T` backs its claim for
  a leader of `T`, at a threshold within the quorum: when it builds, it holds
  the leader block and votes for it from a quorum.
* *Chained* (`Reactive.Chained`). A correct block references a block of its own
  at or above each block its author built before it (`self_ref`); with
  building above the disk (`docs/kpartial.md` Theorem 7, *OnDisk*), correct
  authors keep chains (§1).
* *Buildable* (`Reactive.Buildable`). A valid block can always be built: a
  dense block from the correct blocks one round below of a quorum of distinct
  authors, and a sparse block from a correct node's own block one round below
  and a correct leader's block there, when it does not lead the round above.
  On a timed run, at `2δ ≤ γ ≤ τ` and `δ < γ`, a node of `T` holds the blocks
  of `T` one round below when it builds (`mem_held_below`), so it can build a
  valid dense block. Validity is a property of the record, so every block of a
  run is valid; this says the rules never leave a correct node without one.
* *Covered* (`Reactive.Covered`). A correct leader's block references every
  correct block one round below its author holds (`covers`). On a timed run,
  at `2δ ≤ γ ≤ τ` and `δ < γ`, with each slot's leader leading its round on the
  substrate, leaders of `T` cover `T` (§8, `CoversFrom`), so *Included* holds
  of timed runs.
* *Durable* (`Reactive.Durable`). When correct nodes keep histories on disk,
  every block of the available sub-DAG below a block with votes from
  `f + c + 1` distinct authors is on the disk of a node of any quorum `T` of
  correct nodes from some time on, through any crash: among the voters of the
  anchor, or the `f + c + 1` authors reaching an anchor point, is a node of
  `T`, which keeps on disk the history to depth `K` of the block it
  references.

The proofs follow `docs/kpartial.md` §11. A node of `T` skips no round of a
run (`builtBy_below`): a quorum held at round `s` brings every node of `T`
there within `δ`, through the `f + c + 1` correct authors it contains. A
leader of `T` reaches every voter of `T` before its timeout, since a timeout
fires `τ ≥ 2δ` after a quorum, by which time the leader has built and its
block has arrived (`leader_mem_held`); in the same way the votes of `T` reach
every claimer of `T` (`certIn_held`). A block built behind inherits both from
the block of `T` it holds: through `closed` for the leader block, and through
`backed` for the votes. `LeanDagTest/KPartialSparse/Timed.lean` is a timed run
of the witness record at `G = 0`, `δ = 1`, `γ = 2`, `τ = 4`, on which every
correct validator commits slot `2` by time `17`; read with `G = 10`, it meets
the rules for nodes, and a run resumes above round `0` by time `25`; its
nodes check claims at `K = 6`, so the record meets the claim disciplines.

## 8. The order

The order is that of `docs/kpartial.md` §7. A committed leader `L` outputs the
blocks of its available sub-DAG at most `D` rounds below it (`Out`); a node
reads them on what it holds (`OutIn`). Its ledger after slots `0, …, n − 1` is
what the leaders it committed there output (`LedgerIn`), a block enters at the
first committed slot whose leader outputs it (`EntersIn`), and within a slot
blocks are ordered by round, then author, then id (`KeyLt`, `PrecedesIn`).

Inclusion needs more than synchrony on a sparse DAG: a block of `T` is
referenced by its author's next block and by the leaders that hold it, not by
every block of `T`. Leaders of `T` *cover* `T` (`CoversFrom`) when a leader
block of a slot led by `T` references every block of `T` one round below it,
as a leader referencing the latest block of every node, when it is one round
below, does under synchrony.

**Theorem 6 (the order; `Order.Statement`).**

* *Local* (`Order.Local`). A node reads a leader's output on what it holds,
  and all of it once it has fetched the sub-DAG down to `D` rounds below the
  leader.
* *Agreement and no retraction* (`Order.Agrees`). At a row and the depth the
  sub-DAG needs, on a disciplined schedule and record, what a node outputs
  after `n` slots, every node outputs at the same slot and in the same order
  after `n' ≥ n` slots, once each has fetched below the leaders it committed.
* *Total* (`Order.Total`). The ledger order is a strict total order on the
  ledger, and within a slot a reference precedes the block referencing it.
* *Settled* (`Order.Settled`, `Order.Excluded`). A block not in a node's ledger
  once every slot at most `D` rounds above it is decided never enters it, nor
  any node's ledger.
* *Outputs* (`Order.Outputs`). With correct chains and `D ≤ K`, a leader of `T`
  covering `T` outputs every block of `T` at most `D` rounds below it: it
  references the author's block one round below, and the author's chain leads
  down to the block, within depth `D`.
* *Included* (`Order.Included`). After synchrony, with leaders of `T` covering
  `T` and a slot led by `T` in every `D` rounds, every block of `T` enters the
  ledger of a node that has decided every slot at most `D` rounds above it and
  holds the blocks of `T` that certify such a slot: it commits the slot
  directly, and the slot's leader outputs the block.

Unlike `docs/kpartial.md` §7, *Outputs* needs no run of slots led by `T`
between the block and the leader, only the author's chain. A block of `T`
whose author leaves no leader of `T` within `D` rounds is left out, and its
payload is proposed again; *Excluded* says when that is safe.
`LeanDagTest/KPartialSparse/Order.lean` puts a block of the witness record in
a node's ledger by *Included*.

## 9. Open

Safety (Theorems 1 to 3) holds at every row of the scheme, at every crash
bound, on a disciplined schedule and record, whose disciplines (chains,
checked and truthful claims, leaders leading on the substrate) are what a
correct node does. Liveness holds on responsive records (Theorem 4), and timed
nodes produce them after `G`, through crashes and restarts before it
(Theorem 5). The ledger is agreed, totally ordered and never retracted, and
includes every block of `T` once leaders of `T` cover `T` (Theorem 6). Open:

* Crashes of nodes of `T` after `G` (a stable set per window, as
  `docs/kpartial.md` §12 leaves open), and a witness with a restart before
  `G`.
* A bound in rounds on what a node fetches.
* The bounds of `docs/kpartial.md` Theorem 6, and adaptive schedules.
