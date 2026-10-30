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
  Synchronisation (`SyncedWithin`) now says that a reliable block given
  to a reliable node is on its disk within `Δₛ` past GST. New clause of
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

Stage 3 needs Stages 1 and 2, and Stage 4 needs Stage 3.

## 5. What stays open

* The disk keeps every block it accepts, by design of the core, so it
  grows with the chain; the bound of Stage 4 is per round.
* Before an equivocation is exposed, only a rate bounds what a node takes
  in (S4), and only with rate limits from the environment.
* The cost of answering requests (D6), before conviction.
* V12's record at the exposure clause.
* V13's premise, that every honest block of a round exposes the convicted
  authors, is not yet proved from the spread of the evidence
  (`docs/validator.md` §9).
* Catch-up after a long outage takes in one piece holding the history of
  the target above the frontier, which grows with the time the node was
  behind. The frontier is an author's least round not held, so after a
  restart's jump every stream carries the restarted author's blocks from
  the jump up.
