# Sparse K-partial DAGs

This document adapts the K-partial DAG of `docs/kpartial.md` to sparse
blocks, after Bluestreak [PVM26]: a block that references a leader of the
round below references nothing else but its author's block, and a block
claims in its payload the leaders it has seen certified. The Lean
development is `LeanDag/KPartialSparse`. The available sub-DAG (Theorem 1)
and agreement of the commit rule (Theorem 2) are proved; §5 lists what is
open. `LeanDagTest/KPartialSparse/Witness.lean` is a record on which both
apply.

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
and `i ≤ K` further steps; `x` then brings its history to depth `K − i`
(`Anchored`). A correct author holds the history to depth `K` of each block
it references, so one of the `f + c + 1` authors holds what `x` brings and
checked its claims. At `i = 0` the authors reference `x`, and at `i = 1` they
reach it in two steps, the two cases of `docs/kpartial.md` §3; there the
second needs crashes, here neither does, and the intermediate blocks need
not lie in the sub-DAG. The *available sub-DAG* below `A` is the union of
the histories the anchor points bring (`Avail`).

**Theorem 1 (the available sub-DAG; `Avail.Statement`).**

* *Linked* (`Avail.Linked`). Under the spreading condition
  `(n − f)(f + c) < q(q − f)`, at `K ≥ 6`, with correct chains: if blocks
  of `cm` distinct authors at round `ρ + 2` claim `L` and `n + f < q + cm`,
  then below a leader block at round `ρ + 3` or above the sub-DAG holds a
  claim for `L` at round `ρ + 2`.
* *Backed* (`Avail.Backed`). At `K ≥ 1`, when correct authors check claims,
  below a block that a correct author references every claim in the
  sub-DAG names a certified block.

The proof of *Linked* has four steps.

1. *Two-step reach* (`card_reach2`). Every block at round `ρ + 2` reaches, in
   two steps, round-`ρ` blocks of `q − f` correct authors or more. A sparse
   block reaches them through a leader block it references, which is
   dense. A dense block references blocks of `q − f` correct authors one
   round below. If one of them is dense, the block reaches through it.
   Otherwise each of them is sparse and references its author's block of
   round `ρ` (rule 2), and these are blocks of distinct correct authors.
2. *Double count* (`exists_correct_named`, `exists_reached`). Blocks of the
   sub-DAG from a quorum of distinct authors, with their references in the
   sub-DAG, reach some correct author's round-`ρ` block from `f + c + 1` of
   those authors, under the spreading condition. That block is an anchor
   point. This is the count of `docs/kpartial.md` §3, *Broad*, taken two
   steps down.
3. *Descent* (`denseAt_step`, `denseAt_window`). A dense block within one
   step of an anchor point gives, from its references, an anchor point
   three rounds down. That anchor point is dense, or it is sparse and
   references a leader block one round lower, which is dense. So, from `A`
   down, dense blocks within one step of an anchor point recur at most
   four rounds apart, and one lies at a round `t` with
   `ρ + 3 ≤ t ≤ ρ + 6`.
4. *Overlap* (`linked`). The references of that dense block are blocks of
   `q` distinct authors at round `t − 1`. They share a correct author with
   the `cm` claimers, since `n + f < q + cm`. That author's chain leads
   from its block at round `t − 1` down to its claim at round `ρ + 2`, at
   most `t − ρ − 3` steps. The claim therefore lies within depth
   `t − ρ − 1 ≤ K − 1` of the anchor point.

*Backed* follows from the definition of anchor points. Among `f + c + 1`
distinct authors one is correct. It references a block whose history to
depth `K` contains the history the anchor point brings, and so checked its
claims. For `A` itself, the premise supplies the correct author.

Together, if a quorum claims `L` directly, an anchor above finds a claim for
`L` in its sub-DAG; and any claim found there names a certified block. With
`cm = q` at `n = 3f + 1`, `n + f < q + cm` holds.

## 4. The commit rule and agreement

The rule runs the scheme's three-round rows with a claim in place of a
certificate. A row (`Row`) has a link of one claim and asks that two
certificate thresholds, a certificate and a skip threshold, and the quorum
and the commit threshold each exceed `n + f`. The commit rule (`sRule`) is
an anchored rule of `Common/Anchored.lean`, at wave `2`:

* *direct commit*: claims for the candidate from `commitThreshold` distinct
  authors two rounds above it;
* *direct skip*: `skipThreshold` authors whose block one round above
  references no candidate of the slot;
* *link*: a claim for the candidate two rounds above it, in the available
  sub-DAG below the anchor (`ClaimLinked`); twins are broken by the least
  identifier;
* *anchor*: a certified block.

The rule asks of the schedule and the record (`Disciplined`) that each
slot's leader leads its round on the substrate, that correct authors keep
chains and check claims (§1, §2), and that a correct author claims only
certified blocks (`Truthful`).

**Theorem 2 (agreement; `Agreement.Statement`).**

* *Laws* (`Agreement.Laws`). At a row, under the spreading condition, at
  `K ≥ 6`, the rule meets the laws of an anchored rule on a disciplined
  schedule and record.
* *Agreement* (`Agreement.Agrees`). So two views of one record decide each
  slot alike.
* *Rows* (`Agreement.Rows`). Without crashes, Mysticeti and Cordial Miners
  are rows and the spreading condition holds; under any crash bound, Hybrid
  Mysticeti is a row.

Every law reduces to four facts. A direct commit names a certified block,
since one of its claimers is correct and claims truthfully
(`certified_of_commit`). A link from a certified anchor names a certified
block, since a correct voter references the anchor and Theorem 1 *Backed*
applies (`certified_of_link`). Two certified blocks of one author and round
are one: their voters share a correct author, whose one block there
references one block of each author (`eq_of_certified`). A certified block
is not directly skipped: its voters and the blamers share a correct author
(`not_certified_skip`). Visibility, a direct commit linked from every
eligible anchor, is Theorem 1 *Linked*, since an eligible anchor is a leader
block three rounds or more above the slot.

## 5. Open

* Two-round rows: votes are references, so no claims are needed, but
  *Linked* must be restated for votes one round above the slot.
* *Held*: every block of the sub-DAG is held by a correct node.
* What a node reads (`docs/kpartial.md` §5), with the votes behind the claims
  it checks as a new fetch obligation.
* The crash case beyond `c ≤ 1` at `n = 3f + 2c + 1`, where the spreading
  condition fails; anchor points reached in more steps may give the core
  argument there.
* Liveness, order, the bounds of `docs/kpartial.md` Theorem 6, the timed
  model, and adaptive schedules.
