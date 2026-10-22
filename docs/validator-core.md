# The core validator: refactor plan

This document plans the reduction of the validator (`LeanDag/Node`,
`docs/validator.md`) to the consensus core of the scheme
(`docs/scheme.md`), on branch `validator-core`. It lists what the core
is, what it must prove, what is removed, and the order of removal.
Until stage 6 rewrites it, `docs/validator.md` describes the program
with every mechanism, as on branch `scheme-validator`.

| Stage | State |
|---|---|
| 1. Rate limiting | removed |
| 2. Restart, resume, bootstrap, stall | next |
| 3. Checkpoints and certificates | |
| 4. Exclusion | |
| 5. Garbage collection | |
| 6. Consolidation | |

## 1. Goal

**Phase 1.** A validator that runs one partially synchronous row of the
scheme and does nothing else: it builds, receives, fetches missing
blocks and decides. It keeps every block it accepts, never restarts,
and has no checkpoints, no bootstrap, no rate limiting and no exclusion
of equivocators. Phase 1 ends when the core is built and the claims of
§3 are proved, with the build green, the standard axioms only and the
six audits passing; that state is the milestone commit.

**Phase 2.** Crash recovery on the core (§7), planned after the
milestone.

## 2. The core

**Configuration.** The row `p`, `f`, `c`, the quorum `q`, the node `me`,
the schedule (`per`, `m`, `elect`), the timeouts, the vote rule `σ`, the
hash `idOf`, and the payload source. Removed: `lag`, `ahead`, `limit`,
`extend`, `root`. `Admissible` loses the clauses that only checkpoints
and bootstrap read (`f < q`, `0 < skipThreshold`) unless a core claim
reads them.

**State.** `store`, `pending`, `top`, `own`, `fired`, `lo`, `requested`.
Removed: `recovering`, `offers`, `asked`, `decided`, `lastProposed`,
`chain`, `props`, `cert`, `owner`, `exposed`, `stalled`. (`decided` goes
unless a core claim reads it; the commits are outputs.)

**Store.** The ordered map of accepted blocks, closed under references
above round `0`. Removed: the horizon `base`, `prune`, `window`, and the
reading of blocks at the horizon without references (`atBase`), except
that a round-`0` block is read without references.

**Inputs.** `start`, `deliver`, `timer`, `fetchRequest peer ids`.
Removed: `restart`, `baseOffer`, `baseRequest`, `proposal`, `certOffer`,
`decisionRequest`, `announced`, and the horizon argument of a fetch
request.

**Outputs.** `broadcast`, `setTimer`, `commit`, `fetch peer ids`,
`send`. Removed: `persist` (phase 2 restores it), `prune`,
`requestBase`, `serveBase`, `propose`, `serveCert`, `requestDecisions`,
`announce`, `relay`, and the horizon argument of a fetch.

**Functions kept** (`Model/Step.lean`): `accept`, `ready`, `flush`,
`refsFor`, `reachReady`, `certReady`, `buildable`, `refsAt`, `lent`
(without exclusion), `tryBuild`, `progress`, `built`, `expand`,
`walkLevel`, `missing`, `answerIds`, `answer`, `decidable`,
`decideStep` (deciding only), `advance` (build, decide, flush),
`quiesce`, `pendingTop`, `passes`, `settle`, `step`. A single pass may
suffice once nothing but building and deciding changes the state;
stage 6 decides whether `quiesce` stays.

**Functions removed**: `usable`, `usableAuthors` (the quorum counts all
authors), `twinOf`, `twinned`, `evidence`; `slotOf`, `slotted`,
`State.charge`, `wanted`, `chargeTo`, `kept`, `charged`;
`State.certHeight`, `above`, `ownHead`, `certify`, `certifyAt`,
`record`, `nextHeight`, `proposeNext`, `proposeFrom`, `proposeAt`,
`serveFrom`, `adoptable`, `adopt`, `confirms`, `confirm`, `Cert`,
`Config.headOf`; `horizonAt`, `collect`, `Store.window`; `aheadOf`,
`caughtUp`, `quorumRound`, `jumpRound`, `resumeAt`, `tryResume`,
`State.persisted`, `State.recover`, `resume`, `Persisted`; `stalledAt`,
`stallsTwice`, `timerAsks`, `timerState`, `timerOut` (the timer only
records the firing and settles).

## 3. What the core proves

| | Claim | Premises dropped |
|---|---|---|
| V1 | The node's own blocks are valid at the row (`ValidAt q Clause.distinct`), at strictly increasing rounds, each referencing its predecessor; it references only what it holds; it broadcasts exactly the blocks it builds; its commits are slots `0, 1, …` in order; its store is a view. | restarts, resumes, bootstraps, certificates, proposal bounds |
| V2 | **Decision equivalence with the scheme**: the commits are `Scheme.tryDecide` on the store's view, and over successive views they are `consumed`, the scheme's loop. | the horizon (V4 is retired: nothing is pruned) |
| V3 | **Safety**: over a trace with timely authentication, an injective hash and `Params.Tolerates`, the blocks the honest nodes knew form a `BlockRecord` at quorum `q` of which every honest store is a view, and any two honest nodes' commits are prefix-comparable. | `NoRejoin`; the record's construction for unchecked blocks at a horizon (`Real`, `Lives`) |
| V3′ | **Convergence**: with delivery, every block an honest node broadcast, with its history, ends in every honest store. | `limit = none`, horizon `0`, `NoRestart`, `NoRejoin` |
| V8 | The claims are about the code that runs: the map-backed store, the bounded vote, `@[csimp]` only; replay of the scheme's hand-built records and differential tests against the scheme's loop. | none |
| V11 | **Liveness**: past GST, the reliable nodes produce a round per timeout and decide every run of reliably led slots within the scheme's bound; the run gives the scheme's `WaveFacts`, and the wave argument is the scheme's. | `limit = none`, `NoRestart`, `NoStallBy`, `ExposedFrom`, `TimelyCerts`, `ChainInjective`, `n < q + |T|`, `voteOffset ≤ Λ`, the horizon clause of `SyncedWithin` |

**Equivalence with the scheme** is V1, V2 and V11 together: the blocks
are the scheme's (V1), the decisions are the scheme's decider on the
node's view (V2), and a timed run of the core meets the scheme's
reactive conditions, so the scheme's liveness argument applies (V11).
A stretch goal for V11: derive `SyncedWithin` from `DeliveredWithin`,
since without a horizon a reliable author answers a fetch with the
whole history it holds.

Retired: V4 (pruned stores), V5 (restart; phase 2 restates it), V6,
V7 and V10 (rate limiting), V9 and V12 (bootstrap and certificates).

## 4. What is removed, by mechanism

| Mechanism | Model | Proof helpers | Claims and premises | Simulator and tests |
|---|---|---|---|---|
| Rate limiting | `limit`, `owner`, charges, `wanted` | `Storage` | V7 (`Defer`), V10 (`Storage`); `limit = none` premises | `--limit`, `flood` |
| Restart, resume, bootstrap, stall | `restart`, base messages, `Persisted`, `recover`, `resume`, `recovering`, `offers`, `asked`, `stalled`, jump, resume, stall rule | `Resume`, `Stall`, `Reach`, `Prefix`; the recovering cases of `Horizon` (`Held.top`), `Wait` (`Calm`), `Shape`, `Local` | V5 (`Restart`), V9 (`Boot.Agrees`); `NoRestart`, `NoRejoin`, `NoStallBy`, `Steady`, `n < q + |T|` | `--recover`, `fakeBase`, `splitBase`, `hide`, stall counts |
| Checkpoints and certificates | `Cert`, proposals, certificates, announcements, adoption, `extend`, `root`, `ahead`, `decided` | `Certify`, `Retain`, `Catch`; the certificate parts of `Decided`, `Quiet`, `Boot`, `Agree`, `Arrive` | V12 (`Boot.Certified`), `Local.Certifies`, `Local.Bounded`; `TimelyCerts`, `ChainInjective` | `fakeCert`, `conflictProposals`, `--ahead` |
| Exclusion | `exposed`, `twinned`, `evidence`, `relay`, `usable` | the exclusion parts of `Wait`, `Drift`, `Commits` | `ExposedFrom` | `twinSplit` (kept as an equivocation attack, without exclusion) |
| Garbage collection | `lag`, `base`, `prune`, `window`, `atBase`, `horizonAt`, `collect`, the fetch horizon | `Horizon` (shrinks to the top's block), `Grow`, `Hold`, `Global` (`Real`, `Lives`), `PassShape.rise`, `advance_rise`, the base bounds of `Arrive` and `Drift` | V4; `voteOffset ≤ Λ`, the horizon clause of `SyncedWithin` | `--lag`, `junkAtCut` |

Kept as written, then shrunk: `ReadsView`, `Local`, `Steps`, `Flush`,
`Walk`, `Trace`, `Converge`, `Commits`, `Decided`, `Wait`, `Live`,
`Reliable`, `Shape`, `Arrive`, `Drift`, `Wave`, `Agree`, `Boot`
(its cut invariant, `IsCut.step`, without adoption).

Not touched: the shared-layer arcs (`LeanDag/GC`, `LeanDag/DoS`,
`LeanDag/Checkpoint`, `LeanDag/SafeSkip`, `Common/Record/Fill`), which
are theory the validator no longer uses, and the scheme
(`LeanDag/Scheme`).

## 5. Order of removal

Each stage removes one mechanism from the model, deletes the helpers,
claims, premises, simulator options and tests that serve only it, and
repairs what remains; it ends with the build green, the standard axioms
and the six audits, and is committed on `validator-core`. The order
removes what others depend on last.

1. **Rate limiting.** It depends on exclusion (`wanted`) and nothing
   depends on it.
2. **Restart, resume, bootstrap and the stall rule.** The jump reads
   certificates, and the stall rule reads the horizon; both go before
   them. With no restart input, every reachable state is one the node
   reached from `start`.
3. **Checkpoints and certificates.** The horizon then follows the
   decided frontier alone, until stage 5.
4. **Exclusion.** The quorum counts every author of a round.
5. **Garbage collection.** The store keeps every block; `IsCut` becomes
   "every honest store is a view of the record", and the record is the
   union of what the honest nodes knew.
6. **Consolidation.** Delete dead lemmas, merge helper files that have
   become small, restate the claims of §3 in their final form, shrink
   the simulator, the JSON executable and the tests, rewrite
   `docs/validator.md` to describe the core, and fold this plan's
   remaining content into it.

Milestone commit: the core validator.

## 6. Risks

* **Intermediate stages repair proofs that later stages delete.** The
  order keeps that small: stages 1 to 4 mostly delete branches of
  `step`, and the horizon stays general until stage 5 removes it.
* **The liveness proof's horizon bookkeeping** (`rise`, `horAt`, the
  base bounds) runs through `Shape`, `Arrive`, `Drift` and `Wait`.
  Stage 5 simplifies these rather than deleting them, and is the
  largest stage.
* **Settling.** `quiesce` passes until nothing changes, for
  announcements and adoption. Stage 6 checks whether one pass suffices
  in the core before simplifying `Quiet`.

## 7. Phase 2: crash recovery

After the milestone. Without garbage collection a node can persist
everything a step leaves (its store, top, own block and next slot), so
a restart resumes the state it left with its timers lost. The claims to
restate: V5 (resuming gives the state the crash left), V1 and V3 across
restarts, and liveness for reliable nodes that crash and recover before
GST. Whether a restarted node may skip rounds (resume at a quorum) is
the phase's first design question.
