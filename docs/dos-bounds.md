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
  is public, and signed only at the frontier. Simulated.
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
  bypass and certification).
* **B2. The lag.** In a synchronous run, a correct node's horizon is at
  most `L` rounds below its top, with `L = w + per · (c + 1)`. Here `w`
  is the number of rounds from a slot's round to its direct decision,
  `per` the number of rounds between slot rounds, and `c` the longest run
  of slot rounds without a correct leader, at most `f` under a fair
  schedule with one leader a slot round.
* **B3. The store.** In a synchronous run, a correct node holds at most
  `n + |D|` blocks of each round, except at the rounds of at most `f`
  bands. A band is at most `L + 2` rounds long, and the node holds at
  most `n + f (f + 1) / 2` blocks of each of its rounds. Below its cut it
  takes in only ordered blocks and the blocks of rounds whose ordered
  blocks above come from fewer than `q` authors, and keeps only ordered
  blocks, the blocks of a proof of a verdict, and blocks not bypassed.
* **B4. Histories.** The bound of B3 holds for the history of every block
  the node holds or takes in.
* **B5. Memory.** The memory holds the rounds from the floor to the top,
  at most `L + 1` of them, so at most `(L + 1) · (n + f (f + 1) / 2)`
  blocks.
* **B6. Sync.** The blocks a node takes in at a round number at most the
  bound of B3 for that round. A piece from a correct responder holds
  only blocks at or above the requester's cut, so at most
  `(t − G + 1) · (n + f (f + 1) / 2)` blocks for a target of round `t`.

The constant `f (f + 1) / 2` of a band is the argument of
`docs/sync-auth.md` §4, to be proved in R5 or replaced by the bound R5
proves; the simulator of Phase 1 measures it.

## 4. Decisions

* **E1. Certification is kept.** Without it, Byzantine blocks may join
  twins silently in the window above the horizon. A Byzantine block
  references at most one block of each Byzantine author, so the history
  of one adopted block may hold up to `f ^ L` Byzantine blocks of a
  round. Under certification a correct signer refuses a join below the
  frontier, so joins are public and made at the frontier, and a history
  holds about `f (f + 1) / 2` Byzantine chains (`docs/sync-auth.md` §4).
* **E2. Bypass is the rule of `docs/sync-auth.md` §8.** The test applies
  only below the decided horizon, and its witnesses are the ordered
  blocks. Neither the cut of `LeanDag/GC` nor the rule of §6, which is
  not safe (§7), is used.
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

**Phase 1. The simulator.** `scripts/sync-auth.py` runs the node of
Phase 0: bypass below commit with certification, synchrony from the
start, and the builder of Phase 0. Each node decides from the blocks it
holds, not by an oracle, so that nodes have different cuts (D16). It
reports each quantity of §1 under every attack, against the constants of
§3, and checks that every run is live.

**Phase 2. Lemmas on the record.**

* **R1.** Twins in one history imply a block of that history that joins
  them.
* **R2.** Under certification, a join is signed by `q` nodes, at least
  `q − f` of them correct, and no correct node signs a join below its
  frontier.
* **R3.** Exposure in rounds. With `q = n − f` and `n ≥ 3f + 1`, the
  `q` authors referenced by any block meet the correct signers of a join,
  so every block a constant number of rounds above the join exposes its
  authors.
* **R4.** The ordered blocks of a round number at most `n + |D|`, since
  each was in a correct node's store when it was ordered. This removes
  the premise of `card_not_bypassed_le_of_twins` that every correct block
  is ordered.
* **R5.** The bands. A join convicts its authors, so a run has at most
  `f` bands; each lasts the constant of R3, and holds a bounded number of
  twins a round.

**Phase 3. The node, in three increments.** After each, B0 (safety under
any timing), B1 (liveness in synchrony) and V13 are proved again.

1. **Ordering.** The node computes its ledger and its decided horizon
   from its verdicts (`bypassLedger`).
2. **Bypass.** The store need not be closed: a block is kept once each
   reference is held or bypassed (`BypassRun`), and a bypassed block
   outside the ledger and every proof is dropped (D13). The store's
   invariant (`keep` requires every reference on disk), `ready`, the
   checks and V12 change with it. A node behind catches up by deciding on
   proofs from its peers and taking in the blocks of each commit with the
   commit (D16), a step `BypassRun` is to gain.
3. **Certification.** Sign requests and answers, the signer's
   conviction, the builder's wait for a certificate, and the join test
   on admission.

**Phase 4. The bounds.** B2 to B6 on the node of Phase 3, from R1 to R5,
V13 and the invariant of `BypassRun`.

Phases 3.1 and 3.2 do not depend on certification. With them, B3 holds
below the horizon before Phase 3.3.

## 6. What exists

* **Bypass.** `Common/Bypass.lean` (the test and its bounds),
  `Common/BypassLedger.lean` (the ledger and its agreement),
  `Common/BypassView.lean` (what a node holds, the run `BypassRun`, which
  may drop bypassed blocks, and its invariant), `Properties/Arcs/Bypass.lean`
  (proofs of verdicts, and safety of the run deciding on proofs under
  `Agree`, and with a full history under `Banded`).
* **Exposure and conviction on the node.** V13 (`Node.Bound`), S5 to S8
  (`Node.Sync`), Stages 1 to 4 of `docs/node-sync.md`.
* **Certification.** Simulated in `scripts/sync-auth.py`, with the
  findings of `docs/sync-auth.md` §2 to §4.
* **Bypass in simulation.** `scripts/sync-auth.py` with
  `bypass = 'commit'`, `docs/sync-auth.md` §8: live under every attack,
  and the cost of `nest` does not depend on its depth.
