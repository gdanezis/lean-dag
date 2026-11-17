# Sparse K-partial DAGs

This document adapts the K-partial DAG of `docs/kpartial.md` to sparse
blocks, after Bluestreak [PVM26]: a block that references a leader of the
round below references nothing else but its author's block, and a block
claims in its payload the leaders it has seen certified. The Lean
development is `LeanDag/KPartialSparse`. Only the available sub-DAG
(Theorem 1) is proved so far; §4 lists what is open.

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

Below a block `A`, a block is an *anchor point* when it is `A`, or when
blocks of the sub-DAG from `f + c + 1` distinct authors reference it, and
each brings its history to depth `K`; or when blocks of the sub-DAG from
`f + c + 1` distinct authors reach it in two steps through blocks of the
sub-DAG, and it brings its history to depth `K − 1` (`Anchored`). Unlike
`docs/kpartial.md` §3, the two-step anchor points do not need crashes. The
*available sub-DAG* below `A` is the union of the histories the anchor
points bring (`Avail`).

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
distinct authors one is correct. It referenced the anchor point, or a block
that references it, and so checked the claims of the history the anchor
point brings. For `A` itself, the premise supplies the correct author.

Together, if a quorum claims `L` directly, an anchor above finds a claim for
`L` in its sub-DAG; and any claim found there names a certified block. With
`cm = q` at `n = 3f + 1`, `n + f < q + cm` holds.

## 4. Open

* The commit rule on claims (a direct commit by `commitThreshold` claims, the
  indirect link by one claim in the sub-DAG) and agreement, from Theorem 1
  and the uniqueness of a certified block.
* *Held*: every block of the sub-DAG is held by a correct node.
* The crash case beyond `c ≤ 1` at `n = 3f + 2c + 1`, where the spreading
  condition fails; `docs/kpartial.md` used a two-step core there, which
  here would need a third step.
* Liveness, order, the bounds of `docs/kpartial.md` Theorem 6, and a witness
  record.
* Adaptive schedules.
