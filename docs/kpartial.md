# K-partial DAGs

This document studies the safety, liveness and order of the Mysticeti
commit rule on a *K-partial DAG*, a DAG substrate in which an honest node
holds only part of the history of the blocks it references. The Lean development is
`LeanDag/KPartialDag`.

## 1. The substrate

A block carries a round, an author with its signature, a payload, and
references to blocks of the round below, each committed by its hash. The
references come from a quorum of `n − f` distinct authors, and a block
references at most one block of each author. They differ from those of the
core DAG in two ways:

1. a block need not reference its author's own block of the round below;
2. an honest author that references a block has downloaded that block's
   history to depth `K` only, not its whole history.

A correct node need not build a block at every round: nothing below assumes
it.

Hashes fix the whole history of every block, so the record of a run is an
ordinary block record (`KRecord`, at the validity `KValid`: references one
round below, from a quorum of distinct authors, at most one of each). What changes is what an
honest node holds of it: the history to depth `K` of each block it
references or accepts, not the record's histories in full.

Point 1 does not affect safety: the core's self-reference (`self_parent` of
`ValidWrt`) is used by no safety or liveness result. The rule of one
reference per author is a validity condition (`Clause.distinct`), as in the
core: without it a correct voter could reference both twins of a Byzantine
leader, and both could be certified.

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
certificate for the slot's block, with the certificate's references, which
carry its votes (`AvailLinked`).

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
* **linked** (`Avail.Linked`): at `K ≥ 3`, if a round-`r` block is directly
  committed and `A` lies at round `r + 3` or above, the sub-DAG holds a
  certificate for it, with its references. A block of round `r + 3` whose
  references and theirs lie in the sub-DAG references a certificate of a
  correct author, since its references and the certificates come from two
  quorums;
* **exclusive** (`Avail.Exclusive`): a block for which the sub-DAG holds a
  certificate is not directly skipped.

So the indirect test through any anchor agrees with every direct decision,
and, being a function of the record, with every other node's indirect test
through the same anchor.

## 4. Agreement

The commit rule is Mysticeti's, read on the K-partial DAG, as an anchored rule
of `Common/Anchored.lean` (`kRule`): the direct commit and the slot skip read
on a view, at wave two, with one rung, whose link is `AvailLinked`. At
`K ≥ 3` it satisfies the laws of an anchored rule (`Agreement.Laws`), so any
two views of one record decide each slot alike (`Agreement.Agrees`), and the
committed sequences and ledgers agree by the relation's own theorems.

* Two certificates for blocks of one author at one round certify the same
  block (`eq_of_certificates`): their votes come from two quorums, so a
  correct author's one block of the round above references both, and it
  references one block of each author.
* A direct commit has a certificate, and a slot skip directly skips each
  candidate (`directSkip_of_blameSkip`), so a commit and a skip exclude each
  other, and so do a skip and a link (`not_directSkip`).
* A direct commit is linked from every eligible anchor (`linked`): eligible
  anchors lie at round `r + 3` or above.

The views of this framework are closed under whole histories, and the link
is read on the record. §5 reads the rule on what a node holds.

## 5. What a node reads

A node holds a set `H` of blocks of the record, not closed under histories.
It reads the available sub-DAG below an anchor on `H` (`AnchoredIn`,
`AvailIn`): a block is anchored in `H` when its history to depth `K` is held
and it is the anchor, or blocks of `f + 1` distinct authors of the sub-DAG
read so far reference it. It links a candidate when it holds, in that
sub-DAG, a certificate for it with its references (`LinkedIn`). It has
fetched the sub-DAG down to round `ρ` when the anchor's history is held, and
so is the history of every block that blocks of `f + 1` distinct authors of
the sub-DAG above round `ρ` reference (`FetchedIn`). It decides by the
commit rule read on what it holds (`NodeDecided`): the direct tests count
the certificates and blamers it holds with their references, the indirect
commit reads `LinkedIn`, and the indirect skip of a slot at round `r` needs
the sub-DAG below the anchor fetched down to round `r + 1`, where the
certificate's references lie.

The development proves (`Node.Statement`):

* **local** (`Node.Local`): the indirect test and the fetch test are the
  same on every record whose blocks agree on `H`, so a node computes them
  from what it holds. A history to depth `K` that it holds reads alike under
  every block map agreeing on `H` (`historyUptoFrom_eq_of_subset`);
* **fetchable** (`Node.Fetchable`): a node that holds the record's available
  sub-DAG below an anchor down to round `ρ − K` has fetched it down to `ρ`,
  for `ρ` at most the anchor's round. A block of a history to depth `n` lies
  at most `n` rounds below it (`round_of_mem_historyUpto`). By §3's `Held`
  the node can fetch that part of the sub-DAG from correct nodes. To decide a
  slot at round `r` from an anchor `A`, a node fetches the sub-DAG between
  the rounds of `A` and `r + 1 − K`;
* **sound** (`Node.Sound`): a decision a node takes on what it holds is a
  decision of the commit rule on every view holding `H`. A link read on `H`
  is the record's (`linkedIn_avail`). Once the sub-DAG is fetched down to
  `ρ`, it is the record's sub-DAG above `ρ` (`avail_subset_availIn`), so the
  record's link is read on `H` too (`avail_linkedIn`), and an indirect skip
  on `H` is one on the record;
* **agreement** (`Node.Agrees`): at `K ≥ 3`, two nodes decide each slot
  alike, by soundness on the full view and §4's agreement
  (`NodeDecided.agree`).

## 6. Liveness

Partial synchrony is read on the record as in the rest of the tree. From a
round `R` on, every block of an author in a quorum `T` of correct validators
references every block of an author in `T` of the round below
(`SynchronisedOn`), and the rounds are populated by `T` (`PopulatedOn`). The
schedule offers runs: past any slot, `c` consecutive slots led by `T`
(`FairRunOn`), and each run spans eligibility, that is, every slot below a
run may be anchored by the run's last slot. No bound on `K` is needed for
liveness.

A node decides the slots up to `n` once it holds two sets of blocks:

* the blocks of `T` over the rounds of the run, with their references
  (`WithRefs`);
* the available sub-DAG below every leader block of a slot up to `n` that
  has a certificate (`AvailBelow`). It depends only on the history of that
  block, so it does not change as the record grows.

The development proves (`Live.Statement`):

* **a leader in `T` commits** (`Live.Commits`): after `R`, every block of
  `T` two rounds above the slot carries votes from all of `T` for the
  leader's block (`carriesVotes_of_synchronisedOn`), so a node holding those
  blocks with their references commits the slot directly;
* **a committed run decides below it** (`Live.Descends`): a committed block
  has a certificate (`NodeDecided.certified`), so the node has fetched the
  sub-DAG below each anchor it uses down to the round above the slot
  (§5's `Fetchable`). Its indirect test
  then returns a commit or a skip. Each slot below the run takes its nearest
  committed eligible anchor, and the slots between are skipped, by
  induction downward (`nodeDecided_below`);
* **what a node needs, a correct node holds** (`Live.Delivered`): the blocks
  of `T` are their correct authors', their references lie in those authors'
  windows, and the sub-DAG below a certified block lies in the window of a
  block that a correct voter of the certificate, or a correct author's block
  of the sub-DAG, references (§3's `Held`). So after synchrony a node can
  fetch each of them from a correct node;
* **every slot is decided** (`Live.Progress`): past any slot `k` and round
  `R` the schedule names a run from `b`, fixed before the record. On every
  record synchronised on `T` from `R` and populated over the run, a node
  holding what the run needs decides every slot below `b + c`.

With §5's agreement, every correct node eventually decides every slot, and
all decide each slot alike. Under three-round spacing `c = 1`; with one slot
a round, `c = 3`.

## 7. The order

A committed leader `L` outputs the blocks of its available sub-DAG at most
`D` rounds below it (`Out`). A node reads them on what it holds (`OutIn`).
Its ledger after slots `0, …, n − 1` is what the leaders it committed there
output (`LedgerIn`). A block enters the ledger at the first committed slot
whose leader outputs it (`EntersIn`). As in the rest of the tree, the order
within one slot's output is left open.

The development proves (`Order.Statement`):

* **available** (`Order.Available`): what a certified block outputs is held
  by correct nodes (`avail_correctHeld`), so a node orders only blocks it can
  fetch;
* **local** (`Order.Local`): what a node reads of a leader's output lies in
  the output, and is all of it once the node has fetched the sub-DAG down to
  `D` rounds below the leader (`outIn_eq`). By §5's `Fetchable`, the node
  fetches the sub-DAG between the leader's round and `D + K` rounds below
  it;
* **agreement** (`Order.Agrees`): at `K ≥ 3`, two nodes that have fetched
  below the leaders they committed have one ledger, and one entry slot per
  block. Their verdicts agree (`NodeDecided.agree`), and so do their reads
  of each leader's output (`ledgerIn_agree`);
* **inclusion** (`Order.Includes`): after synchrony from round `R`, a leader
  of `T` outputs every block of `T` from round `R` on at most `D` rounds
  below it, at `K ≥ 1`. The leader references the blocks of `T` of the round
  below, which lie in its history to depth `K`. Each block of `T` two rounds
  below or more is referenced by the blocks of `T` of the round above, `n − f`
  distinct authors whose blocks lie in the sub-DAG, so it is anchored, round
  by round downward (`anchoredBelow_of_synchronisedOn`,
  `mem_out_of_synchronisedOn`);
* **entry** (`Order.Enters`): after synchrony, a node deciding a slot led by
  `T` has in its ledger every block of `T` at most `D` rounds below the
  slot (`mem_ledgerIn_of_leader_mem`).

The depth `D` sets what is output, and `K` sets how far below that a node
fetches. A block not output by a committed leader within `D` rounds above it
is never output. So once every slot up to `D` rounds above a block is
decided, its author knows whether the block is in the ledger, and can
propose its payload again if it is not. After synchrony a block of `T` is
output when a slot led by `T` lies at most `D` rounds above it. So `D` is
bounded below by the gap between such slots that the schedule allows, not
by `K`: under round robin with one slot a round, `D ≥ f + 1` suffices.

## 8. Next

* Bounds: the cost of fetching the sub-DAG, and how long correct nodes must
  keep the histories they downloaded.
* The order within one slot's output.
