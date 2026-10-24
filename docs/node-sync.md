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

Stages 0 and 1 are done (§4). The node receives blocks by announcements
and syncs, one sync for each peer (`docs/validator.md` §3.4); it holds at
most `n − 1` syncs (V1, `SyncsBound`), and the honest nodes converge
(V3′). It detects an author whose twins it accepts, and takes no
announcement from it after.

Two consequences of the node before Stage 1 remain.

* **A convicted author still makes valid blocks.** An author whose twins
  are known can build blocks that reference only honest blocks; they are
  valid, and the node accepts those it is sent in streams, since honest
  blocks may reference them.
* **Nothing bounds what a node takes in a round.** A Byzantine target
  can carry any number of valid twins of an author not yet detected.

Stage 2 makes honest blocks stop referencing convicted authors; Stages 3
and 4 bound what a node takes in a round once every equivocator is
exposed (S5 of `docs/sync.md`).

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

* **Evidence.** Every block carries the twin pairs its author knows: two
  signed headers by one author at one round, at most `f` pairs. A node
  checks a pair by the headers alone.
* **Exposure.** The authors a block exposes are those its references
  expose and those its own evidence names: at most `f`, computed when the
  block is accepted and kept with it, so no check walks a history.
* **Validity.** The row's validity gains one clause: a block references no
  author it exposes (`DoSValidOn` with exposure from evidence,
  `LeanDag/Common/Exclusion.lean`). Validity stays a function of the block
  and its history, so every node judges a block alike.
* **The builder** drops from its references the authors its block would
  expose, and its block carries the evidence of every author it has
  convicted.
* **Conviction.** Two blocks of one author at one round on the disk, or
  evidence in an accepted block, convict the author. The node syncs no
  target of a convicted author and ignores its announcements. Evidence
  travels in blocks, so no report message is needed: after GST an honest
  block carrying it reaches every reliable node within `Δ + Δₛ`.
* **Checks on arrival.** Each streamed block is taken in only if it is
  ready and passes the checks, the validity clause among them (§3, D1).

With header-first admission in place of the check on arrival (Stage 3),
S5 says a node holds at most `n + |D|` blocks of each round from the round
at which every honest admitted block exposes the convicted authors `D`;
after GST that round is one above the highest round an honest node built
at before every reliable node held the evidence.

## 3. Decisions

* **D1. Header-first admission or a check on arrival.** *Decided: a
  check on arrival, first.* Each streamed block is checked when it
  arrives, and taken in if it is ready and valid. This needs no buffer.
  It does not give S5: a Byzantine target can carry any number of a
  convicted author's valid twins under blocks that break the exposure
  rule, and they arrive, and are taken in, before the blocks that break
  it. Header-first admission reads the headers of the target's history
  above the frontier first, top down, and takes blocks in only if all
  pass; a target refused proves its announcer faulty to the node, which
  then syncs nothing more from it. It costs a buffer of headers per
  target, with a cap that must exceed the history of any honest target
  above the frontier (from the exposure round on, `n + f` blocks a round
  over the rounds a node is behind). It is left for after Stage 2.
* **D2. Authenticated links.** An announcement and a stream must name
  their sender: `Input.deliver` gains the peer. The proofs already assume
  timely authentication (`TimelyAuthentic`); this asks it of links too.
* **D3. Evidence in the payload.** The block type is shared by every rule,
  so evidence goes in the payload: the configuration gains a reader of
  evidence from a payload and a payload source that takes the evidence to
  carry, with the law that the reader returns what was put in. *Recommended*
  over a field of `Block`.
* **D4. Exposure kept with each block.** The store keeps, for each block,
  the authors it exposes, with the invariant that it is the union over its
  references and its evidence. *Recommended* over recomputing from the
  history at each check.
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
* **Stage 2 — evidence and validity** (§2.2, D3, D4). Evidence in the
  payload, exposure kept in the store, the validity clause, the builder
  rule and conviction. The scheme's record is then at the stronger
  validity; the scheme's results read only quorum, distinct authors and
  references one round below, so they apply unchanged, and V12 states the
  record at the row's validity with the clause. Liveness needs that honest
  blocks pass the clause, which holds since an honest author never
  equivocates and its builder drops the authors its block exposes, and
  that the quorum survives the drop: exposed authors are Byzantine, and
  the honest authors alone make a quorum.
* **Stage 3 — admission, later** (D1). The header pass and its cap;
  the simulator's attacks of `scripts/sync-reports.py` (trees of twins,
  twins per node, chains carried each round) on the node, with the blocks
  processed per round reported.
* **Stage 4 — the exposure bound on the node, later.** S5's proof read
  on the node's disk: D27 (`creator_ne_of_correct_exposed`) on an admitted
  history, a convicted author's blocks taken in only as its own target
  before conviction, and an author not convicted holding one block a
  round. Then the premise in time, which the Sync model does not prove:
  past GST, every honest block built `Δ + Δₛ` after an honest node
  convicted `X` carries or inherits the evidence, from `Arrival`; so from
  the round above the highest round built by then, the node holds at most
  `n + f` blocks a round.

Stages 1 and 2 are independent of each other; 3 needs both, and 4 needs 3.
Stage 1 alone bounds what a node holds waiting, and Stage 2 alone stops
honest nodes referencing convicted authors.

## 5. What stays open

* The disk keeps every block it accepts, by design of the core, so it
  grows with the chain; the bound of Stage 4 is per round.
* Before an equivocation is exposed, only a rate bounds what a node takes
  in (S4), and only with rate limits from the environment.
* The cost of answering requests (D6).
* Catch-up after a long outage reads the headers of every round missed;
  the cap of D1 must allow it, or a node behind by more than the cap needs
  a bootstrap, which the core does not have.
