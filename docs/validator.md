# An honest validator for the scheme

This document plans a Lean program that acts as an honest validator of
the partially synchronous rows of the scheme (`docs/scheme.md`), and the
proofs that it conforms to the scheme. Nothing in it is built yet. Names
in backticks are existing declarations; names in italics are planned.

## 1. Scope

The program is parametrised by a row `p : Params` and the quorum `q`. It
covers the six partially synchronous rows: Cordial Miners PS, Mysticeti,
Blue Bottle PS, Orcaella, Nemo-Nemo and Hybrid Mysticeti. The
asynchronous rows, the coin and `AsyncPace` are out of scope.

It integrates three mechanisms:

* **garbage collection**, with crash persistence and restart;
* **Safe Skip**, the one-message return after downtime;
* **rate limiting**, the novelty budget on acceptance;
* **bootstrap**, the return of a validator down past the horizon, from
  the attested base.

Two of these rest on results stated on the core's universe only, which
are lifted to block records at quorum `q` first (§8).

Out of scope: stake weights, a mempool (the payload comes from a
configured source), and an implementation of hashing (identifiers are
the environment's hash, assumed injective on the blocks of a run).

## 2. Interface

The program is a pure, total transition function

> *step* : *Config* → *State* → *Input* → *State* × List *Output*

wrapped by two executables: one reading inputs and writing outputs as
JSON lines, and a simulator running `n` instances over a seeded network.

**Configuration.** The row `p`, the quorum `q`, the validator's own
identity, the schedule `Slots`, the timeout per round, the vote rule
(`leastSel` first, `votedBlock` with the stored reference order
second), the hash *idOf*, the horizon lag `Λ`, the novelty budget `τ`,
and the payload source.

**Inputs.**

* a delivered block: identifier, round, author, ordered references,
  payload;
* a delivered jump message (`JumpMsg`);
* a timer for round `r` that fired;
* a restart, carrying the persisted state (§5.1);
* a base offer from a peer: its round-`G` blocks and its window above
  them (§3.6);
* a base request from a peer.

**Outputs.**

* persist a block, emitted before the block is broadcast;
* broadcast a block;
* broadcast a jump message;
* set a timer for round `r`;
* commit slot `k` with a decision `Option BlockId`;
* prune below the horizon `G`;
* request the base from the peers;
* serve the base and window to a peer.

Time is discrete (`ℕ`), as in `PaceCore`.

## 3. The program

### 3.1 The store

A received block passes through three stages.

1. **Pending**: some parent is missing. The block waits.
2. **Held**: its parents are held and it satisfies the row's validity
   `ValidAt q C`, which is decidable.
3. **Accepted**: its novelty, the blocks of its history not yet
   accepted, is at most `τ` (`UniformBudget`). Otherwise it is deferred
   until the accepted set has grown.

The accepted set is closed under references, so it is a
`BlockRecord.View`; this is the view the decider reads. Byzantine
twins are accepted, since their votes count. Blocks below the horizon
`G` are dropped, and round-`G` blocks are read without references.

### 3.2 The builder

The program builds round `r + 1` when it holds `q` distinct authors of
round `r` and, for the slots whose wave is in progress, either

* the block it would build reaches the slot's leader block, at each round
  from the one above the proposal to the vote round, and certifies it at
  the decision round of a three-round row; or
* the timer for round `r` has fired.

These are the clauses `advancesAt`, `reach_or_wait` and `cert_or_wait`
of `SchemeReactive`, written as a rule the program runs, so the liveness
hypotheses hold by construction.

The new block references one accepted block per round-`r` author,
including the validator's own previous block, choosing the least
identifier between twins. The program builds rounds in sequence and
never skips one. It persists the block, then broadcasts it, then sets
the timer for round `r + 1`.

### 3.3 The decider

After each step the program runs `tryDecide p σ U V lo N` on its view,
where `lo` is the slot after the last decision output and `N` the last
slot whose decision round it holds, and outputs the new decisions. Over
successive views this is `consumed`.

### 3.4 Garbage collection

The horizon is `G = min(F − Λ, t − Λ)` with `Λ ≥ 2`, where `F` is the
decided frontier (the largest round below which every slot is decided)
and `t` the validator's round (the depth rule of `garbage.md` §6). Below
`Λ = 2` the attested base can miss blocks a joiner needs; safety holds
at every `G`. The decider runs at the schedule re-indexed from the first
slot above the horizon (`Slots.chop`).

### 3.5 Safe Skip

After a restart whose downtime the network has moved past, the program
sends one jump message `(v1, B1, v2, B2)` instead of building every
missed round. A receiver derives the fill blocks locally, with
identifiers from the hash, so every receiver derives the same fill
(`JumpMsg`, SS10 of `SafeSkip/Jump.lean`).

### 3.6 Bootstrap

A validator whose last own block lies below its peers' horizons cannot
rejoin from its window, because the blocks its window references are
pruned. It requests the base from its peers and keeps a round-`G` block
once `f + 1` distinct presenters offer it, a presenter's attestation
being its own offer (G10, `garbage.md` §7). Every block kept then has a
non-Byzantine presenter, and no block of an honest author is filtered
out. It adds the offered window above the kept base, through the store's
usual stages, and resumes at the horizon of the assembled view, by a jump
message if its own line has a gap. Peers serve their round-`G` blocks
and their window on request; the obligation is bounded by the window's
size (G7).

## 4. Conformance

| | Claim | Route |
|---|---|---|
| V1 | Every block the program broadcasts satisfies `ValidAt q C`; it builds at most one block per round, in consecutive rounds, across restarts; it references only what it accepted; its accepted set is a view. | induction over *step* |
| V2 | The commit outputs are `consumed` over the successive views. | unfolding; `Restart` |
| V3 | In a run of honest programs and arbitrary Byzantine blocks, the blocks accepted by honest validators form a `BlockRecord` whose honest set is the program-run validators. Under `Params.Tolerates`, any two honest validators' commit sequences are prefix-comparable. | V1, V2, `Scheme.safety` |
| V4 | The pruned store is `View.chop` of the full-history view, and decisions across the horizon equal the full-history ones, at any two horizons. | `decided_chop_iff`, `chop_chop` |
| V5 | A restart from the persisted state is a prune at an admissible horizon. | V4 |
| V6 | A run with jump messages is a `skipFill` extension of the run without them; decisions persist across the fill, and new slots in the gap are skipped at once. | `decided_fill_of_persist`, `decided_none_of_novel` |
| V7 | Rate limiting does not make a validator decide wrongly. | `decided_mono_of_banded` |
| V8 | The efficient store and decider compute the reference program's values. | one equality per function |
| V9 | A bootstrapped validator's view is a view of the record cut at its horizon, so its decisions agree with every other validator's at the slots both hold; the fetch is bounded. | lifted G10–G12 (§8), V4 |
| V10 | Under the novelty budget, every honest block is eventually accepted, and an honest validator's store, with garbage collection, has a size independent of the runtime. | lifted C3 and B4 (§8), `card_retained_le` |
| V11 | A timed run past GST, with timeouts of at least `2Δ + proc`, gives a `SchemeReactive` and the delivery obligation `DeliversOn`; the mechanisms compose (`Stack.safe_and_live`), and every slot commits. | field by field from the run, V10 |

Two hypotheses belong to the environment, not the program: the hash is
injective on the blocks of a run, and the network meets the delivery
assumptions.

## 5. Crashes

### 5.1 What survives

The last own block is not enough. Suppose a Byzantine author sends `X`
to `v` alone, `v` accepts it, builds `B` referencing it, broadcasts `B`
and crashes before any peer has fetched `X`. No correct validator holds
`X`, so none can complete `B`'s history: an honest block is lost, which
breaks `converges` and `holds_mono` of `PaceCore`.

The program therefore persists every block not yet in the common core,
that is, every accepted block above the horizon `G`, which includes its
own blocks. After GST, whatever a correct validator holds by round `m`
every correct store holds by `m + 1` (`viewUpto_subset_viewUpto_succ`),
so a peer can serve whatever lies below the horizon
(`pruned_subset_peer_store`). It also persists `G`, so as not to accept
blocks below it again, and `lo`, so as not to repeat commits; repeats
would be identical, since the loop's restart is idempotent (`Restart`).

A block is persisted before it is broadcast. Otherwise a crash between
the two lets the restarted validator build a different block at the same
round, which is an equivocation.

Pending and deferred blocks are not persisted: no own block references
them, and their authors or other peers can serve them again.

With garbage collection the persisted window has a size independent of
the runtime (`card_retained_le`, G6).

### 5.2 What this gives

A crash loses exactly what pruning at the horizon would have dropped, so
a restart needs no theorem beyond V4 (V5), and holdings above the
horizon never shrink. Before GST possession is not universal in one
round, and the horizon's frontier term keeps more blocks; safety holds
at every horizon. Safe Skip covers the downtime itself: on restart the
validator is at its last own block `B1` with its window intact. A
validator down past its peers' horizons rejoins by bootstrap (§3.6).

## 6. Testing

1. **Agreement with the model.** `#guard` checks in
   `LeanDagTest/Validator/` that the program's commits on the scheme's
   hand-built records match those the scheme's tests record.
2. **Differential tests.** The efficient program against the reference
   program on random records of a few rounds.
3. **The simulator.** `n` programs over a seeded network that reorders
   and delays messages, with crashes, restarts and scripted Byzantine
   equivocators, over all six rows. It checks validity, prefix-comparable
   ledgers and commits after GST at run time; small scenarios also run as
   `#guard` checks in the build.
4. **Optionally**, replaying records through the Rust decider of the
   Mysticeti codebase, where the scheme's table comes from.

## 7. Steps

| Step | Content |
|---|---|
| 0 | This document; the interface types, all mechanisms' inputs and outputs included |
| 1 | Reference program without mechanisms: *step* over a `Finset` store calling the model's functions; `#guard` tests |
| 2 | V1 and V2 |
| 3 | Simulator and JSON executable |
| 4 | V3 |
| 5 | Garbage collection, persistence and restart: V4, V5 |
| 6 | Safe Skip: V6 |
| 7 | Lift the bootstrap results to block records (§8, L1); bootstrap in the program: V9 |
| 8 | Lift the rate-limiting results to block records (§8, L2) |
| 9 | Rate limiting in the program: V7, V10 |
| 10 | Efficient store and decider refining the full reference program: V8; differential tests |
| 11 | Liveness: V11 |

The order proves safety and local conformance of every mechanism before
the two large steps, so that step 10 refines the complete program once
and step 11 proves liveness once, against it. The model's own functions
are too slow to run beyond a few rounds (`historyUptoFrom` recurses
without sharing), which is why step 10 exists. Steps 7 and 8 change the
shared layer and are recorded among the shared-layer steps of
`docs/target-properties.md`.

## 8. Lifting to block records

Two groups of results the program needs are stated on the core's
universe, at `n = 3f + 1` and quorum `quorumCard`, and so hold at the
Mysticeti and Cordial Miners PS rows only. Each is lifted to block
records at a quorum `q` with `2q ≥ n + f + 1`, as `exists_commonCore`
was, with the core's statement kept as the corollary at `q = n − f`.

* **L1, bootstrap**: the attested base and its soundness and
  completeness (G10), window completeness (G11), the bounded fetch
  (G6b), the joiner's view (G12) and the relay obligation (G7), from
  `GC/AttestedBase.lean` and `GC/Bootstrap.lean`, with the depth rule
  (`viewUpto_subset_viewUpto_succ`, `pruned_subset_peer_store`) they rest
  on.
* **L2, rate limiting**: the delivery model of `Network/Delivery.lean`
  (`Delivery`, `EventuallyDelivers`), the novelty budget (`UniformBudget`,
  `ByzBudget`), the liveness half (C3) and linear storage (B4) of
  `DoS/Novelty.lean`, and the coverage witness of `DoS/Delivers.lean`.

The hybrid rows have `c` crash-prone validators besides the `f`
Byzantine ones. Crash-prone validators are honest (they do not
equivocate), so the attestation threshold stays `f + 1`; what changes is
that a crashed validator neither presents nor serves, which the lifted
statements take as the reliable set `T` rather than the honest set.
