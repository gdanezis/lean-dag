# Plan: the sync model on the node, with DoS protections

This document plans two changes to the node of `docs/validator.md`
(`LeanDag/Node`). The first replaces the node's receipt and fetching of
blocks (§3.1, §3.4 of `docs/validator.md`) by the syncs of the Sync model
(`docs/sync.md`, `LeanDag/Node/Sync`), which bounds the blocks a node
holds waiting. The second adds the checks and the evidence of the Sync
model's exposure bound (S5), which bounds the blocks a node takes in a
round once every equivocator is exposed. It records the decisions to take,
the stages, and what each stage keeps proved.

## 1. Where the node stands

Stages 0 to 4 are done (§4), but for the premise in time of Stage 4. The
node receives blocks by announcements and syncs, one sync for each peer
(`docs/validator.md` §3.4); it holds at most `n − 1` syncs (V1,
`SyncsBound`), and the honest nodes converge (V3′). Its blocks carry
evidence of equivocation and the authors they expose; a block is valid
only if it references no author it exposes (`Clause.exposes`). The node
convicts the authors its evidence names, takes no announcement from
them, answers none of their requests, and leaves them out of its
references.

A stream piece is taken in only if it brings the whole history of the
sync's block, every block of which passes the checks (`takeIn`), so a
convicted author's twins under blocks that break the exposure rule are
not taken in. The node holds at most `n + |D|` blocks of each round once
every honest block of a round exposes the convicted authors `D` (V13 of
`docs/validator.md`), the bound of S5 (`docs/sync.md`) on the node. What
remains is the round from which that premise holds.

## 2. The design

### 2.1 Syncs

* **Announcements.** A peer's broadcast of its own block is an
  announcement. If the block is ready on arrival (its references accepted,
  one round below it, valid), it is accepted at once, as now. Otherwise it
  becomes the target of the sync with that peer, if the peer is not
  detected, the block is not held, and it lies above the current target.
* **Requests and streams.** For each target the node sends the target's
  author a request: the target, its frontier (for each author the least
  round at which it holds no block of the author, and `0` for a detected
  author), and the identifiers it asks for by name. The author streams the
  blocks of its disk in the target's history at or above the frontier, the
  target and those asked for, in order of round.
* **Taking a stream in.** A streamed block in the history of the target
  of its sender's sync that is ready on arrival is accepted; the others
  are dropped. A pass that leaves the target unready asks next for the
  missing references by name (S1: within `2e + 1` passes, for `e`
  equivocators).
* **Pending is the targets**, at most one for each other node not
  detected (S2). On the retry timer and on a restart the node sends its
  requests again (`resync`). The jump waits for no target above the round
  it jumps to (`syncTop`).

The withholding attack of `docs/validator.md` §3.4 (a Byzantine node shows
one node a block referencing a block it reveals only to the others) stays
harmless: the honest peers that built on the revealed block have it in
the history of their targets.

### 2.2 DoS protections

* **Evidence.** A block's payload carries evidence items: an author and
  two block identifiers (`Exposure.ev`). The node carries only items of
  twins it holds; that another node's items are authentic is a premise
  of the claims (`EvidenceAuthentic`), which signed headers give.
* **Exposure.** A block's payload also names the authors it exposes
  (`Exposure.ex`): those its evidence names and those its references
  expose. The validity clause checks this against the references, so
  exposure is read off each block and no check walks a history.
* **Validity.** The row's validity gains one clause: the exposure is as
  above, and the block references no author it exposes
  (`Clause.exposes`, `rowValid q E`). The clause reads a block and its
  references only, so every node judges a block alike.
* **The builder** leaves out of its references the authors its evidence
  names and those its round's blocks expose (`excluded`, `refsFor`), and
  its block carries the evidence against the authors it does not
  reference (`payloadFor`). With fewer than `q` authors left, it builds on
  the references of a held valid block of the next round (`lent`), and
  on its retry timer asks every peer for its block of its top round
  (`Input.ask`, `Output.send`).
* **Conviction.** Two blocks of one author at one round on the disk, or
  evidence in an accepted block, convict the author. The node syncs no
  target of a convicted author, ignores its announcements and answers
  none of its requests. Evidence travels in blocks, so no report message
  is needed: after GST an honest block carrying it reaches every
  reliable node within `Δ + Δₛ`.
* **Checks on arrival.** Each streamed block is taken in only if it is
  ready and passes the checks, the validity clause among them (§3, D1).

With header-first admission in place of the check on arrival (Stage 3),
S5 says a node holds at most `n + |D|` blocks of each round from the round
at which every honest admitted block exposes the convicted authors `D`;
after GST that round is one above the highest round an honest node built
at before every reliable node held the evidence.

### 2.3 Ordering, bypass and certification (Stage 5)

Stage 5 adds the mechanisms of `docs/dos-bounds.md` to the node. The
decisions it raises are D10 to D16 (§3).

**Ordering.** The node keeps the set `ordered` of the blocks its commits
have ordered. When it decides that slot `k` commits the leader `L`, it
adds the blocks of `flushOn` for `L` (`Common/BypassView.lean`), read
from its disk, with the horizon `slotRound k`. Its *horizon* is
`H = slotRound lo`, for `lo` its next undecided slot, and its *cut* is
`G = H − 1`.

**Bypass.** A block `x` of round `r` is *bypassed* at the node when
`r + 1 < H` and the ordered blocks of round `r + 1` that do not
reference `x` come from at least `q` authors (`Bypassed U ordered q x`).

* **Ready.** A block is ready when each reference is on disk or
  bypassed, one round below it, and the block passes the checks. A block
  of round `G` or below is checked as a base block (D10).
* **Requests.** A request carries the requester's horizon. The responder
  streams the history of the target at or above both the requester's
  frontier and `G`. The requester asks by name for a reference below `G`
  that it lacks and does not find bypassed.
* **Keeping.** The node keeps every block it takes in, bypassed or not
  (D13). Its disk stays a bypass view of `ordered` at `H`
  (`BypassRun.inv`).
* **Catch-up.** A node whose syncs wait on a reference that no correct
  peer serves asks each peer for its blocks of the rounds of its next
  undecided slots, decides from them, and so raises its cut (D16).
* **Decisions** read the disk at or above `G`, a view of the record cut
  at `G` (`BypassView.chop`), as the memory already does from its floor.

**Certification.** A block *joins* a twin pair when both blocks are in
its history and in the history of no single reference of it.

* **The join test** is a rule of admission, not of validity (D11). The
  node takes a block in only if, on its disk at or above its cut and the
  blocks taken in with it, the block joins no pair, or carries a
  certificate for the pairs it joins.
* **The certificate.** A block that joins pairs carries a certificate:
  its round, a set `E` holding every pair it joins, and the signatures of
  at least `q` nodes. The certificate is evidence against
  the authors of `E`, and authentic by premise (`CertAuthentic`, as
  `EvidenceAuthentic`).
* **The builder** prefers references that join nothing. When it cannot
  reach `q` authors without a join, it sends `(r, E)` to every peer and
  builds once `q` nodes have signed.
* **The signer.** A node that receives `(r, E)` convicts the authors of
  `E`. It refuses, and sends back the block, when it holds a block of
  round `r` whose history holds no pair of `E` (`clean`); it also
  refuses when `r` is at or below its cut (D14). Otherwise it signs.
* **Inputs and outputs.** `Input.signRequest` and `Input.signAnswer`;
  `Output.signRequest` and `Output.signAnswer`.

## 3. Decisions

* **D1. Header-first admission or a check on arrival.** *Decided: a
  check on arrival in Stages 1 and 2, header first from Stage 3.* A check
  on arrival takes each streamed block in if it is ready and valid when
  it arrives. It does not give S5: a Byzantine target can carry any
  number of a convicted author's valid twins under blocks that break the
  exposure rule, and they arrive, and are taken in, before the blocks
  that break it. Header-first admission takes a piece's part in the
  target's history in only if the target is then held, and none of it
  otherwise (`takeIn`). The piece is the buffer: a part not taken in is
  dropped, and the next answer streams it again with the names asked
  for, so the node keeps no buffer across pieces. A piece has no size
  limit: the history of an honest target above the frontier grows with
  the time the node is behind, and with a limit a node behind by more
  than it does not catch up. A target refused does not mark its announcer: the node keeps no record
  of faults that it cannot pass on as evidence.
* **D2. Authenticated links.** An announcement and a stream must name
  their sender: `Input.deliver` gains the peer. The proofs already assume
  timely authentication (`TimelyAuthentic`); this asks it of links too.
* **D3. Evidence in the payload.** *Decided.* The block type is shared by
  every rule, so evidence goes in the payload: the configuration gains a
  reader of evidence and exposure from a payload (`Config.xp`) and a
  payload source that takes the evidence and exposure to carry
  (`Config.payload`), with the law that the reader returns what was put
  in (`Config.Faithful`), a premise of the liveness claims only.
* **D4. Exposure carried by each block.** *Decided:* the payload names
  the authors the block exposes, and the validity clause checks it
  against the references. This keeps the clause local, so the memory's
  checks agree with the disk's, and needs no store invariant.
* **D7. Authentic evidence.** *Decided: a premise.* The node checks that
  an item names two distinct identifiers, not that they are signed
  blocks of the author; the claims assume that no known block carries
  evidence against an honest author (`EvidenceAuthentic`).
* **D8. Too few authors left.** *Decided: both.* The node builds on the
  references of a held valid next-round block, which the liveness proofs
  use, and asks each peer for its block of the round.
* **D9. Requests of convicted peers.** *Decided: ignored.* An
  equivocator's copy that rejects every block built on its twin keeps a
  low frontier, and each of its requests would stream the history above
  it (411,549 blocks in 200 ticks at Orcaella with `n = 9`, against 181
  in all in 1,000 ticks once ignored).
* **D10. Checks at and below the cut.** *Decided: base blocks.* A block
  of round `G` may reference a bypassed block, whose header the node
  lacks, and the history below it cannot be checked at all. The node
  checks a block of round `G` or below on its own header only, as the
  base layer of the cut of `LeanDag/GC`, and every block above `G` in
  full. Safety needs no check below the cut: decisions read the record
  cut at `G`, which is valid by construction, and the ledger reads only
  identifiers and rounds. The record of a run is then valid above every
  cut, not everywhere; `chop` and `bypassLedger` are to be stated on
  such a record. The alternatives were to hold the headers of bypassed
  references, which leaves the question one round lower, and to follow a
  block only with `f + 1` ordered referrers, under which a bypass does
  not persist.
* **D11. The join test is a rule of admission.** *Decided, on review.*
  A digest in the payload over the `K = L + 2` rounds below a block keeps
  the test in the validity clause, but `L = w + per · (c + 1)` grows with
  `f`, and the digest holds up to `n · K` identifiers: about 3,800 at
  `n = 100`. The node instead tests a block it takes in against its disk
  at or above its cut. A join of pairs below the cut needs no
  certificate: such pairs are bypassed or ordered. Two nodes with
  different cuts may then disagree on a block for a time, which affects
  liveness only (D16); validity, and so safety, are unchanged.
* **D12. The builder does not wait.** *Decided.* A builder that waits,
  up to a timeout, for a block of every author of its round would
  reference every correct block, which gives exposure in rounds without
  certification and orders every correct block. A Byzantine author that
  withholds its block would then make every round last the timeout.
  Exposure in rounds rests on the signers of a join instead (R3 of
  `docs/dos-bounds.md`).
* **D13. Blocks are kept.** *Decided, on review.* Dropping a bypassed
  block would keep only ordered blocks below the cut, but a correct node
  behind needs, to decide, blocks that a node ahead has bypassed (D16);
  the store bound B3 holds without dropping, since it bounds what a node
  takes in at each round.
* **D14. A signer refuses a join at or below its cut.** *Decided.* It no
  longer holds the histories that `clean` reads there. A correct signer
  past round `r` holds a clean block of round `r`, its own, so `clean`
  already refuses most such joins.
* **D15. A request carries the requester's horizon.** *Decided.* A
  responder then streams nothing below the requester's cut.
* **D16. Catch-up by decision.** *Decided, on review.* Correct nodes have
  different cuts. A block `x` of round `r` with `G_B ≤ r < G_A` is
  bypassed at the node `A` and needed at the node `B`. If `x` is late,
  no correct node holds it, and a Byzantine author that shows `B` a
  block above `x` and withholds `x` stops `B`'s syncs on every block
  above it: bypass removes the defence of `docs/validator.md` §3.4, that
  the correct peers that built on a block hold its history. `A` decided
  the slots that make `x` bypassed before it took in the block above
  `x`, from blocks without `x` in their history, and keeps them (D13).
  So `B` asks each peer for its blocks of the rounds of its next
  undecided slots, decides from them, and raises its cut until `x` is
  bypassed at `B` too. Liveness in synchrony (B1) must cover this, and
  the simulator must decide at each node, not by an oracle.
* **D5. The fast path.** A broadcast block ready on arrival is accepted
  without a sync, as now. *Recommended*: it is the common case.
* **D6. What stays with the environment.** Rate limits on streams from a
  peer (S4's premise) and on requests from a peer: the cost of answering
  requests is not bounded by the program.

## 4. Stages

Each stage ends with `lake build` green, the standard axioms, the six
audits, the documents updated, and a commit.

* **Stage 0 — isolate receipt in the proofs.** *Done.* What the proofs
  use of receipt is a few lemmas: a delivery or a stream piece changes
  nothing or is a receipt (`Received`, `step_receipt`), which grows the
  disk with blocks of the syncs or the input and keeps the rest of what
  the claims read; after every step no sync's block is ready
  (`noReady_step`).
* **Stage 1 — syncs on the node** (§2.1, D2, D5). *Done.* The program:
  state `syncs` (the peer, its block and the names asked for) and
  `detected`; inputs for announcements, which name their sender, stream
  pieces and requests; outputs for requests and streams; the pending
  list, walk, pruned answer and refetch removed. Proofs: V1–V3, V11, V11′
  and V12 through the Stage 0 lemmas. V3′ (convergence) is re-proved by
  the sync's last request (`last_ask`, `step_stream_stuck`), with no
  fault bound, for the history of each honest node's top block.
  Synchronisation (`SyncedWithin`) says that a reliable block given to a
  reliable node, at its author's round at GST or above, is on its disk
  within `Δₛ` past GST. New clause of
  V1: at most `n − 1` syncs (`SyncsBound`). The simulator sends requests
  and streams; the outage sweep, the attacks and the withholding
  scenario ran again (`docs/validator.md` §6).
* **Stage 2 — evidence and validity** (§2.2, D3, D4, D7–D9). *Done.*
  Evidence and exposure in the payload, the validity clause, the builder
  rule, asks and conviction. The node checks blocks at `rowValid q E`;
  V12's record stays at `ValidAt q Clause.none`, which the scheme's
  results read. Liveness needs that honest blocks pass the clause, which
  holds since the builder leaves out the authors its block exposes and
  the payload is faithful, and that no reliable author is left out,
  which holds by authentic evidence (`not_excluded`); V3′, V11, V11′ and
  V12 gain the premise `EvidenceAuthentic`, and V11, V11′ and V12
  `Faithful`. Where fewer than `q` authors are left, the proofs build on
  a lent reference set (`lent_buildable`).
* **Stage 3 — admission** (D1). *Done.* `takeIn`; V3′ re-proved: a
  valid part in order of
  round whose references are held or in it is taken in whole
  (`foldl_all`), so the last request's piece lacks a reference, which was
  asked for. The simulator reports the most blocks of one round on an
  honest disk; the outage sweep, the attacks and the equivocator runs
  give the same results as in Stage 2. The attacks of
  `scripts/sync-reports.py` (trees of twins, twins per node, chains
  carried each round) are not ported to the node's simulator.
* **Stage 4 — the exposure bound on the node.** *Done, but for the
  premise in time.* V13 (`Node.Bound.Bounded`): a node takes a block of
  an author in the author's own name only while it has not convicted the
  author, and the other blocks of a piece it takes in are referenced by
  blocks taken in with them, so each author has at most two blocks a
  round that no block of the disk references, one if not convicted
  (`steady_before`); once every honest block of round `m + 1` exposes the
  convicted authors, D17 (`not_mem_creators_refs_of_correct_exposed`,
  generalised to `CorrectBelow`) leaves their blocks from round `m + 1` on
  unreferenced, and the disk holds at most `n + |D|` blocks a round. The
  walk through a piece goes only through blocks under their hash
  (`hashed`); were it to go through blocks under another identifier too,
  a peer could have any valid block taken in. Open: the premise in time,
  which the Sync model does not prove either. It does not hold with the
  builder as it is: a reliable node that convicted `X` and lends the
  references of another author's next-round block, because its own fail
  the tests, can reference a block of `X`, and its block then does not
  expose `X` (`docs/validator.md` §9). Lending only sets that avoid the
  authors the builder leaves out, while its own set can be built, would
  give it, if the wave facts can do without a lent set that references
  such an author.
* **Stage 5 — ordering, bypass and certification** (§2.3, D10–D16).
  *Planned* (`docs/dos-bounds.md`, Phase 3). In three increments, each
  with safety under any timing, liveness in synchrony (V11) and V13
  proved again: ordering (`ordered`, the horizon); bypass (a disk that
  need not be closed below the cut, requests with the horizon, catch-up
  by decision); certification (the join test on admission, the
  certificate, the builder's request and the signer).

Stage 3 needs Stages 1 and 2, and Stage 4 needs Stage 3. Stage 5 needs Stage 4.

## 5. What stays open

* Stage 5, ordering, bypass and certification on the node, is planned
  in `docs/dos-bounds.md`.
* The disk keeps every block it accepts, by design of the core, so it
  grows with the chain; the bound of Stage 4 is per round.
* Before an equivocation is exposed, only a rate bounds what a node takes
  in (S4), and only with rate limits from the environment.
* The cost of answering requests (D6), before conviction.
* V12's record at the exposure clause.
* V13's premise, that every honest block of a round exposes the convicted
  authors, holds from round `n_E + 1` under spread evidence
  (`Live.Spread`, `docs/validator.md` §5.1); the spread is assumed.
* Catch-up after a long outage takes in one piece holding the history of
  the target above the frontier, which grows with the time the node was
  behind. The frontier is an author's least round not held, so after a
  restart's jump every stream carries the restarted author's blocks from
  the jump up.
