# K-partial DAGs

This document studies the safety of the Mysticeti commit rule on a
*K-partial DAG*, a DAG substrate in which an honest node holds only part of
the history of the blocks it references. The Lean development is
`LeanDag/KPartialDag`.

## 1. The substrate

A block carries a round, an author with its signature, a payload, and
references to blocks of the round below, each committed by its hash. The
references come from a quorum of `n − f` distinct authors. They differ from
those of the core DAG in two ways:

1. a block need not reference its author's own block of the round below;
2. an honest author that references a block has downloaded that block's
   history to depth `K` only, not its whole history.

Hashes fix the whole history of every block, so the record of a run is an
ordinary block record (`KRecord`, at the validity `KValid`: references one
round below, from a quorum of distinct authors). What changes is what an
honest node holds of it: the history to depth `K` of each block it
references or accepts, not the record's histories in full.

Point 1 does not affect safety: the core's self-reference (`self_parent` of
`ValidWrt`) is used by no safety or liveness result.

## 2. The commit rule on a K-partial DAG

The direct tests read three rounds. A round-`r` block `L` is directly
committed when certificates for it, round-`(r+2)` blocks each referencing
votes for `L` from a quorum, come from a quorum of distinct authors
(`DirectCommit`); it is directly skipped when a quorum of distinct authors
has a round-`(r+1)` block that does not reference it (`DirectSkip`). A node
holding those blocks decides as the record does.

The indirect rule of Mysticeti decides a slot through the nearest committed
anchor above it, by whether the anchor's causal history holds a certificate
for the slot's block. That history may reach below what an honest node
holds, since the anchor may lie many rounds above the slot. A node that
evaluates the test on what it holds may then skip a block that another node
committed. This holds even when every honest node builds a block at every
round: such a node holds, in each round of the anchor's history, a block it
references, but a certificate that lies only on a branch of Byzantine blocks
may be held by one honest node and not another.

The test is therefore read on a part of the anchor's history that every
honest node can fetch and that is fixed by the record.

## 3. The available sub-DAG

Below a block `A` honest nodes referenced, a block is *anchored* when it is
`A`, or when blocks of `f + 1` distinct authors reference it, each in the
history to depth `K` of an anchored block (`AnchoredBelow`). The *available
sub-DAG* below `A` is the union of the histories to depth `K` of the anchored
blocks (`Avail`). It is a function of the record, so every node computes the
same one. The indirect test reads it: the sub-DAG below the anchor holds a
certificate for the slot's block (`AvailLinked`).

The development proves, on any K-partial DAG (`Avail.Statement`):

* **held** (`Avail.Held`): each block of the sub-DAG lies in the history to
  depth `K` of `A`, or of an anchored block that a correct author's block of
  the sub-DAG references. That author downloaded that history, so a node
  can fetch every block of the sub-DAG from a correct node;
* **broad** (`Avail.Broad`): at `K ≥ 2`, every round two or more below `A`
  holds an anchored block of a correct author. Blocks of a quorum of
  distinct authors at one round reference some correct author's block of
  the round below from `f + 1` of those authors (`exists_correct_referenced`),
  by a double count: each references `n − 2f` or more correct blocks, and a
  correct author has one block a round;
* **linked** (`Avail.Linked`): at `K ≥ 2`, if a round-`r` block is directly
  committed and `A` lies at round `r + 3` or above, the sub-DAG holds a
  certificate for it. A block of round `r + 3` whose references lie in the
  sub-DAG references a certificate of a correct author, since its
  references and the certificates come from two quorums;
* **exclusive** (`Avail.Exclusive`): a block for which the sub-DAG holds a
  certificate is not directly skipped.

So the indirect test through any anchor agrees with every direct decision,
and, being a function of the record, with every other node's indirect test
through the same anchor.

## 4. Next

* The commit rule as an anchored rule (`AnchoredRule` of
  `Common/AnchoredBelow.lean`), with `AvailLinked` as its link, and agreement
  across views from the rule's laws.
* Views a node holds on a K-partial DAG: closed under histories to depth
  `K`, not under whole histories; a decision taken on such a view, with the
  available sub-DAG below the anchor fetched, is the record's.
* Liveness: the cost of fetching the sub-DAG, how far below an anchor
  decisions reach, and how long honest nodes must keep the histories they
  downloaded.
