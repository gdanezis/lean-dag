# Plan: bounds on what a correct node syncs and holds

This document plans the bounds on the blocks a correct node syncs, and on
its histories, store and memory, under attack. It lists the mechanisms
the bounds use, the theorems to prove, the decisions taken, and the
phases of the work. The bounds are to hold for a node of `LeanDag/Node`
that implements every mechanism they use.

## 1. Scope

* **Synchronous runs.** The bounds assume that every message between
  correct nodes arrives within `Δ`, and every sync answer within `Δₛ`,
  from the start of the run. Safety is proved without any assumption on
  time.
* **The quantities.** For a correct node: the blocks it syncs and takes
  in, the history of each block it holds, its store (the disk), and its
  memory.
* **The form of a bound.** A constant in `n`, `f` and the lag `L` of the
  decided horizon behind the frontier, in rounds. No bound depends on how
  far back an attack is dated, or on the round of the run.
* **Out of scope.** Streams that a peer sends unasked and that the node
  drops; requests from peers and the cost of answering them; the size of
  payloads; the order of the blocks within one commit.

## 2. The mechanisms

* **M1. The validity shape.** A block references at most one block of
  each author, one round below, and at least `q` authors
  (`Common/BlockRecord.lean`). So a block references at most `n` blocks.
  Proved.
* **M2. Header-first admission** (`takeIn`, Stage 3 of
  `docs/node-sync.md`). Every block taken in lies in the history of an
  accepted target. Proved.
* **M3. One sync for each peer** (S2, V1). At most `n − 1` syncs. Proved.
* **M4. Detection and conviction** (Stage 2, S6). The announcements and
  syncs of a convicted author are refused. Proved, with
  `EvidenceAuthentic` a premise.
* **M5. The exposure clause** (S5 to S8, V13). At most `n + |D|` blocks
  a round from the round `m + 1` at which every correct block exposes the
  convicted authors `D`. Proved from round `n_E + 1` under the premise
  `Live.Spread`.
* **M6. Certified joins** (`docs/sync-auth.md` §1 to §4). A join of twins
  is public, and signed only at the frontier. Simulated; on the record,
  exposure one round above a join is proved (R1 to R3).
* **M7. Bypass below the decided horizon** (`docs/sync-auth.md` §8). Below
  the horizon a node follows only ordered blocks, and is safe. Proved on
  the record and on a run model.
* **M8. Decisions within a bound** (V11, `DecidesBy`). The decided
  horizon trails the frontier by a bounded time. Proved; in rounds, open.

## 3. The theorems

Each is to be stated on the node of Phase 3, with its premises listed.
The constants are fixed in Phase 0 and checked in Phase 1.

* **B0. Safety.** Under any timing, two correct nodes agree on every
  verdict and order the same blocks (`bypassRun_agree` on the node, and
  V12 proved again for a store that need not be closed).
* **B1. Liveness.** In a synchronous run no correct node stalls, and
  every correct node decides every slot (V11 proved again with ordering,
  bypass and certification). A node behind rests on catch-up by proof
  (D16 of `docs/node-sync.md`): once its top has not moved for a time
  `T_c`, it asks its peers for the proof of the verdict of its next
  undecided slot and the blocks that slot's commit orders. Every correct
  node that has decided the slot keeps both (D13), so the node decides
  the slot within `T_c + 2Δ` of stalling. A node that no correct node
  is ahead of needs no catch-up: no correct node drops a block at or
  above its cut, and the argument is that of V11.
* **B2. The lag.** In a synchronous run, a correct node's horizon is at
  most `L` rounds below its top, with `L = w + per · (c + 1)`. Here `w`
  is the number of rounds from a slot's round to the round at which a
  node that has built it decides it, `per` the number of rounds between
  slot rounds, and `c` the longest run of slot rounds without a correct
  leader, at most `f` under a fair schedule with one leader a slot round.
  For the rule of Phase 1, `w = 3` and `per = 1`.
* **B3. The store.** In a synchronous run, a correct node takes in at
  most `n + |D|` blocks of each round, except at the rounds of bands. The
  band of a Byzantine author is the set of rounds at which the node takes
  in twins of it. Each author has at most one band, of at most `L + 2`
  rounds. At each round the node takes in at most
  `K = n + (n − f) · f` blocks, and over the run at most
  `f · (n − f) · (L + 2)` blocks beyond one of each author a round.
  Below its cut it takes in only ordered blocks and the blocks of rounds
  whose ordered blocks above come from fewer than `q` authors, and keeps
  only ordered blocks, the blocks of a proof of a verdict, and blocks not
  bypassed.
* **B4. Histories.** The bound of B3 holds for the history of every block
  the node holds or takes in.
* **B5. Memory.** The memory holds the rounds from the floor to the top,
  at most `L + 1` of them, so at most `(L + 1) · K` blocks.
* **B6. Sync.** The blocks a node takes in at a round number at most the
  bound of B3 for that round. A piece from a correct responder holds
  only blocks at or above the requester's cut, so at most
  `(t − G + 1) · K` blocks for a target of round `t`. A catch-up reply
  holds a proof and the blocks of one commit, each within the bound of
  B3 at the rounds it spans.

**The constant `K`.** No attack in the simulator exceeds `K`: 31 at
`n = 10` and 49 at `n = 13`, against 28 and 45 seen. The 28 and 45 are
`n + f · (n − f − 1)`, reached for one round when every Byzantine author
shows each correct node its own block (`alltwins`), so `K` is within `f`
of what an attack achieves. The argument of `docs/sync-auth.md` §4 for
the union of the honest histories gives only
`M = n + (n − f) · f (f + 1) / 2`, which grows as `n · f²`: 37,687 at
`n = 100, f = 33`, against `K = 2,311`. R5 is to prove `K`, with `M` as
the fallback. The bound `n + f (f + 1) / 2` that §4 argues for one
history fails in the simulator (§6): a correct block joins, at the
frontier, the structures that its references adopted.

**The length of a band.** A band can last as long as the lag. In the
simulator the band of one author spans up to 8 rounds at `n = 10, f = 3`
and 7 at `n = 13, f = 4`, within `L + 2` (9 and 10). The long bands lie
at rounds below the cut where bypass does not apply, after a run of
skipped Byzantine leaders. Bands can therefore fill the memory, and B5
is `(L + 1) · K`, not `(L + 1) · (n + |D|)` with the mass of a band
added. Both `L` and the length of a band shrink only with `c`, the run
of slots without a correct leader. A leader schedule that bounds `c` by
a constant, by reputation for instance, would bound both, but changes
the commit rule and its proof of safety; it is not in this plan.

## 4. Decisions

* **E1. Certification is kept.** Without it, Byzantine blocks may join
  twins silently in the window above the horizon. A Byzantine block
  references at most one block of each Byzantine author, so the history
  of one adopted block may hold up to `f ^ L` Byzantine blocks of a
  round. Under certification a correct signer refuses a join below the
  frontier, so joins are public and made at the frontier, and the
  histories of the correct nodes hold about `(n − f) · f (f + 1) / 2`
  Byzantine chains a round (`docs/sync-auth.md` §4).
* **E2. Bypass is the rule of `docs/sync-auth.md` §8.** The test applies
  only below the decided horizon, and its witnesses are the ordered
  blocks. Neither the cut of `LeanDag/GC` nor the rule of its §6, which
  is not safe (its §7), is used.
* **E3. Time only in the bounds.** Every mechanism must be safe without
  timing; only B1 to B6 assume synchrony.
* **E4. Out of scope**, as in §1.

The node's design and the decisions it raises are Stage 5 of
`docs/node-sync.md` (§2.3, D10 to D16). D10, the checks at and below the
cut, decides what record the safety and the bounds of the run are
stated on.

## 5. Phases

**Phase 0. The specification.** Stage 5 of `docs/node-sync.md`: the
node's new state (ordered set, horizon, certificates), the new messages
(sign requests and answers), the rule for taking a block in (each
reference held or bypassed), the builder, the signer, and the join test.
Done: `docs/node-sync.md` §2.3 and D10 to D16.
The theorems of §3 are stated in full, with their constants.

**Phase 1. The simulator.** `scripts/dos-sim.py` runs the node of
Phase 0: bypass below commit with certification, synchrony from the
start, and the builder of Phase 0. Each node decides from the blocks it
holds, not by an oracle, so that nodes have different cuts (D16). It
reports each quantity of §1 under every attack, against the constants of
§3, and checks that every run is live. Each node reads histories as it
saw them. Done: §6.

**Phase 2. Lemmas on the record.** R1 to R3 are proved in
`Common/Join.lean`, over a causal structure, as `Common/Exclusion.lean`
is. A block *joins* two blocks when both lie in its history and in the
history of no single reference of it (`JoinsFrom`).

* **R1. Twins in one history are joined in it.** Two blocks in a
  history are joined by a block of that history (`exists_joinsFrom`),
  above their round when they are distinct blocks of one round
  (`JoinsFrom.round_lt`). Proved.
* **R2. A certificate has `q − f` correct signers.** In a certified
  record a block that joins two twins has at least `q` signers and names
  their author (`CertifiedOn`); at most `f` nodes are not correct, so at
  least `q − f` signers are (`card_signers_inter_le`). Proved. That the
  block of a correct signer at the round of the join exposes the named
  authors (`SignersExposeOn`) is a premise, the signer's obligation, to
  be proved on the node in Phase 3.3: the signer refuses when it holds a
  block of that round whose history holds no pair of the twins, so its
  block of that round either holds a pair or is built after it convicted
  their authors.
* **R3. Exposure one round above a join.** With `n + f < 2q`, the `q`
  authors a block references include a correct signer
  (`correctBelow_of_card`), so every block from one round above the join
  of two twins exposes their author (`exposed_of_twins`). Under the DoS
  condition no such block references a block of that author
  (`not_mem_creators_refs_of_twins`), and D27 and D28 of
  `Common/Exclusion.lean` apply from that round. Proved.

R4 to R6 are statements on runs, not on the record. R4 reads the stores
of correct nodes, R5 depends on when Byzantine structures are made and
adopted, and R6 on what correct nodes hold when a node behind asks.
They are proved in Phase 4, on the node of Phase 3.

* **R4.** The ordered blocks of a round number at most `n + |D|`, since
  each was in a correct node's store when it was ordered (V13). This
  removes the premise of `card_not_bypassed_le_of_twins` that every
  correct block is ordered. Within a band the bound is that of R5.
* **R5.** The bands. A join convicts its authors, so a run has at most
  `f` bands. By R3 every block from one round above a join exposes the
  twins' author, so a band ends one round above its last join. That the
  joins are made at the frontier, so that a band lasts at most `L + 2`
  rounds, needs time. A band holds a bounded number of twins a round:
  `K − n = (n − f) · f`, or failing that `M − n`.
* **R6, optional.** What a node behind needs. In a synchronous run, the
  history down to a correct node's cut of the blocks from which another
  correct node decided its next slot is held by a correct node: on its
  disk above its cut, in its ledger, or in a proof (D13). It would
  explain why no node catches up by proof in the synchronous runs of
  the simulator. B1 does not rest on it.

**Phase 3. The node, in three increments.** After each, B0 (safety under
any timing), B1 (liveness in synchrony) and V13 are proved again.

1. **Ordering.** The node computes its ledger and its decided horizon
   from its verdicts (`bypassLedger`). Done: what a node ordered after
   `n` slots is the ledger of its verdicts read from its disk
   (`State.ordered`, `ledgerOn`, `Node/Model/Order.lean`). Two honest
   nodes order the same blocks after any number of slots both decided
   (`Order.Agrees`), and an honest node holds what it ordered
   (`Order.Held`), in `Node/Order`. The ordered set is read off the
   state, so no step changes, and V11, V12 and V13 stand as they are.
2. **Bypass.** First, `BypassRun` gains the step that takes the blocks
   of a commit in with the commit (D16), with its invariant and B0;
   catch-up, on which B1 rests, and the exemption of those blocks from
   the join test need it. Done: `BypassRun.absorb`, with `flushOn_eq_of`
   and `BypassView.absorb`; a skip, too, may be decided on a proof.
   Then the store need not be closed: a block is kept once each
   reference is held or bypassed (`BypassRun`), and a
   bypassed block outside the ledger and every proof is dropped (D13).
   The store's invariant (`keep` requires every reference on disk),
   `ready`, the checks and V12 change with it. A node behind catches up
   by deciding on proofs from its peers.
3. **Certification.** Sign requests and answers, the signer's
   conviction, the builder's wait for a certificate, and the join test
   on admission.

**What Phase 3.2 changes on the record (D10).** Phase 3.1 keeps the
store closed, and needs none of this.

* **The ledger on known blocks.** `layer`, `flush` and `bypassLedger`
  read only the block map and the ordered set, but the bypass test reads
  the round of the bypassed block from its own header. Under bypass a
  correct node may order a block whose bypassed reference no correct
  node ever held. Done: the ledger read from a block map (`ledgerOn`)
  reads the round of a block of a layer off the leader, so it never
  reads a bypassed block. It depends only on the blocks it reads
  (`ledgerOn_congr`), agrees for agreeing verdicts
  (`ledgerOn_agree_of`) and only grows (`ledgerOn_mono`), with no record;
  on a record it is `bypassLedger` (`ledgerOn_eq`).
* **One record for each cut.** `globalRecord` (`Node/Helpers/Global.lean`)
  holds the blocks that are real all the way down: known, valid, with
  real references. A block a correct node holds at or below its cut may
  not be. Every decision of slot `k` reads the record cut at
  `slotRound k − 1` (`Proves`, `Store.window`), so the record is to be
  the blocks real down to that round, those at it read as base blocks.
  V12 (`Holds`, `Loops`) and the facts of V11 that read the record are
  restated for each slot on that record. The cut rebases rounds and
  slots, as `BlockRecord.chop` and `Slots.chop` do, since a base block
  must sit at round `0`. In steps:
  1. *The record cut at `G`.* Done: the known blocks at or above `G`
     that are real down to `G`, cut there (`globalCut`, `RealDown`,
     `Node/Helpers/GlobalCut.lean`). Real down to `G` is real down to
     every higher round, and the cut of `globalRecord` lies in it.
  2. *Nesting.* For `G ≤ G'`, the blocks of the record cut at `G`, cut
     again at `G' − G`, are blocks of the record cut at `G'`, read alike.
  3. *Decisions on a cut.* The scheme's loop on the record cut at `G`,
     with slots rebased by `Slots.chop`, decides as the loop on the
     record from slots above `G`. The scheme has no such lemma yet;
     `ViewsAbove` compares records at the same rounds.
  4. *Agreement across cuts.* Two decisions of one slot on cuts `G ≤ G'`
     agree: the lower one, cut again, lies on the higher record (step 2),
     where it is unchanged (`decided_agree_chop` under `Banded`, which
     the scheme shows at a local vote), and `Agree` holds there.
  5. *V12 and V11.* `Holds`: a disk at or above its cut is a cut of the
     record cut there. `Loops`: each decision step is the loop on a view
     of the record cut at its slot. `Leads` and `Waves` on the record cut
     at the lowest round they read.
* **Checks at the cut.** A block of round `G` or below is checked on its
  own header only (D10), so `ready` and the checks change below the cut.

**Phase 4. The bounds.** R4 and R5, and B2 to B6 on the node of Phase
3, from R1 to R5, V13 and the invariant of `BypassRun`. R6 is optional.

Phases 3.1 and 3.2 do not depend on certification. With them, B3 holds
below the horizon before Phase 3.3.

## 6. The simulator

`scripts/dos-sim.py` runs the node of Stage 5 at `n = 10, f = 3` and
`n = 13, f = 4`, for 300 ticks with `Δ = 3`, under the attacks it lists.
Every message to one correct node takes `Δ`. Every run is live except
`nest cert`, and in every run all correct nodes order the same blocks
for every slot they have decided. The largest values over the
synchronous runs of the node of Stage 5, that is all but `cut`, `cert`
and `late deaf`:

| Quantity | `n = 10` | `n = 13` | Bound of §3 | Bound |
|---|---|---|---|---|
| Lag `top − H` | 6 | 8 | `L = 3 + (c + 1)` | 7, 8 |
| Memory | 77 | 125 | `(L + 1) · K` | 248, 441 |
| Taken in at a round | 28 | 45 | `K` | 31, 49 |
| Rounds above `n + ∣D∣` | 8 | 10 | `f · (L + 2)` | 27, 40 |
| History at a round | 28 | 45 | `K` | 31, 49 |
| Piece per round of target | 11.8 | 19.8 | `K` | 31, 49 |

* **The join test.** A node reads the history of a block as it saw it,
  through the references it held when it took the block in. This gives
  the counts of a test on full histories, and no node refuses a correct
  block on it. With the test of D11 as first decided, on pairs at or
  above the cut, `nest` puts 56 blocks of one round into a correct node
  at `n = 10`, above `K = 31` and `M = 52`. The families of `nest` join their twins
  below the frontier, at rounds that are below the cut but not bypassed:
  the round above holds ordered blocks of fewer than `q` authors after
  Byzantine leaders are skipped. Taken over the blocks the node follows
  at every round (D11, revised), the test brings this to 16. Counting a
  pair as joined when a certificate the node took in names it (`cert`)
  stalls `nest` at round 41: a builder leaves out a pair whose
  certificate a receiver has not taken in, and the receivers refuse 36
  correct blocks at `n = 10`, and 64 at `n = 13`, for good.
* **The bands.** One round under `twins` exceeds `n + |D|`, before X is
  convicted. Under `alltwins` every Byzantine author shows each correct
  node its own block; at the next round each correct block references
  the blocks of other correct nodes, which carry other twins, so a
  correct node takes in `n + f · (n − f − 1)` blocks of one round: 28 at
  `n = 10` and 45 at `n = 13`. The joins are made at once, every author
  is convicted, and no other round exceeds `n + |D|`. The other such
  rounds are those of `nest` and `flat`, and lie within `L + 2` rounds
  of the run of skipped Byzantine leaders before the attack's frontier.
  There the ordered set is thin and bypass does not apply, and each
  correct node adopts at the frontier its own structure of Byzantine
  chains, which joins nothing below the frontier. A correct block then
  joins its references' structures under a certificate. At `n = 13`
  under `nest`, a round holds 10 blocks of each of three Byzantine
  authors, one for each of 9 correct nodes and one more. The structures
  of `docs/sync-auth.md` §4 (`flat`) give 22 blocks taken in at a round
  at `n = 10`, and a history with 27 at `n = 13`. All are within `K`;
  the `f (f + 1) / 2` chains for each correct node that `M` allows do
  not appear.
* **The band of one author.** Under `nest` and `flat` the band of one
  author at one node spans up to 8 rounds at `n = 10` and 7 at `n = 13`,
  within `L + 2`, and the author adds up to 40 and 67 blocks beyond one
  a round, within `(n − f) · (L + 2)`, 63 and 90. At one round it may
  have more blocks than `n − f`, 10 at `n = 10` and 11 at `n = 13`, so
  the bound of B3 is on the round, not on the author.
* **What is kept.** Below the cut a node keeps 7 to 13 blocks a round,
  nearly all ordered; proofs add at most 0.7 a round. In all, the nodes
  drop 250 and 784 blocks under `nest`, 357 and 857 under `flat` at
  `depth = 13`, 21 and 144 under `late`, 4 under `race w2` at `n = 13`,
  and none under the other attacks.
* **Catch-up.** In synchronous runs no node catches up by proof: a node
  behind receives by broadcast, within `Δ`, the blocks from which the
  nodes ahead decided, and syncs their histories from them. Under
  `race`, X shows the fast nodes only a block `z` of round `R − 1` under
  a block `y` of `R`, so that a commit orders `y` and bypasses `z`
  (`race w2`: shown to two fast nodes only). The fast nodes keep `z` in
  their proof of slot `R`, which holds the history of the certificates
  of round `R + 2` down to round `R − 1`, nearly every block of those
  rounds. Of 24 such blocks at `n = 13` under `race w2`, one is left out
  of that proof, and dropped, by 4 of the 8 fast nodes; the slow node
  takes it from the other 4. B1 does not rest on this, but on catch-up
  by proof. Under `late deaf`, a node cut off for 100 ticks catches up
  once by proof and then by sync, and its proofs check.

## 7. What exists

* **Bypass.** `Common/Bypass.lean` (the test and its bounds),
  `Common/BypassLedger.lean` (the ledger and its agreement),
  `Common/BypassView.lean` (what a node holds, the run `BypassRun`, which
  may drop bypassed blocks, and its invariant), `Properties/Arcs/Bypass.lean`
  (proofs of verdicts, and safety of the run deciding on proofs under
  `Agree`, and with a full history under `Banded`).
* **Ordering on the node.** `Node/Order`: the ledger read from the disk
  is the record's (`ledgerOn_eq`), and two honest nodes order the same
  blocks (Phase 3.1).
* **Exposure and conviction on the node.** V13 (`Node.Bound`), S5 to S8
  (`Node.Sync`), Stages 1 to 4 of `docs/node-sync.md`.
* **Certification.** Simulated in `scripts/sync-auth.py`, with the
  findings of `docs/sync-auth.md` §2 to §4. On the record,
  `Common/Join.lean`: joins of twins (R1), certified records (R2), and
  exposure one round above a join (R3).
* **The node of Stage 5 in simulation.** `scripts/dos-sim.py`, §6.
* **Bypass in simulation.** `scripts/sync-auth.py` with
  `bypass = 'commit'`, `docs/sync-auth.md` §8: live under every attack,
  and the cost of `nest` does not depend on its depth.
