# lean-dag

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

A Lean 4 + Mathlib formalization of uncertified DAG consensus in the
style of Mysticeti: the DAG itself, the commit rule, and machine-checked
safety and liveness — together with further developments built on the
same foundation, each in its own module consuming the core read-only.
The core is stated for `n ≥ 3f+1` validators with quorums of size
`n − f`, over pipelined, multi-leader slot schedules; the variant arcs
move the committee — `n ≥ 5f+1` for two-round commitment,
`n = 3f + 2p − 1` for a fast path that tolerates `p` missing votes,
`n ≥ 5·fb + 3·fc + 1` for hybrid faults, and a bare majority at
`n ≥ 2f+1` for crash faults alone.

## What is proved

- **Safety** of the Mysticeti-style commit rule — agreement across
  views and routes, uniqueness of the committed sequence, a monotone and
  agreed ledger — with no network assumption of any kind.
- **Chain quality** (`LeanDag/Quality/`): every commit's flush carries,
  at every round below it, blocks from **at least half of the correct
  validators** — with no synchrony assumption — and once the DAG is
  synchronous, every correct block enters the agreed ledger within a
  schedule-window of its creation; a six-validator counterexample shows
  the aggregate guarantee provably does not imply the individual one.
- **Liveness** above *eventual DAG synchrony*, a structural condition on
  the DAG under which no liveness theorem mentions time. The whole of
  what the network must supply reduces to a single clause of **view
  convergence** — after stabilisation, whatever one correct validator
  holds reaches every correct validator within `Δ` — from which the
  structural condition is derived, and block production with it, rather
  than assumed. The threshold a deployment must meet is the constant
  `2Δ + proc`: no quantity set by deployment appears, because the
  pacemaker's catch-up rule collapses any clock spread to `Δ + proc` in
  one post-stabilisation round. And liveness is **local** — not merely
  that some view commits, but that every reliable validator decides on
  *its own* view, at an explicit time (`commits_recur_local`).
- **Denial-of-service resistance** (`LeanDag/DoS/`): safety is shown
  independent of any anti-equivocation condition; storage is bounded
  under an exposure condition (with a matching construction showing its
  exponential constant is forced) and made linear-forever under an
  enforceable, author-blind **novelty budget** (`dos_resistance`).
- **Garbage collection** (`LeanDag/GC/`): a per-validator horizon below
  which nothing is retained, with commit verdicts invariant across the
  cut, storage **constant** at a lag, bootstrap by an `f+1`-sampled
  attested base — and **no consensus on the cut** anywhere.
- **Odontoceti** (`LeanDag/Odontoceti/`): safety and liveness of the
  two-round commit rule (arXiv:2510.01216), generalized from `n = 5f+1`
  to `n ≥ 5f+1`, on the unmodified DAG layer — including four findings
  about the published safety argument, one of which (agreement among
  indirect commits resting on candidate-iteration order) is refutable
  on data without the canonicity repair the formalization supplies.
- **Reactive schedules** (`LeanDag/Reactive/`): both commit rules remain
  live when validators wait only until they hold the leader's block —
  or, under Mysticeti, until they can certify — with the timeout as a
  fallback. The fast path is quantified: round latency is bounded by
  drift, delivery and processing with the timeout appearing nowhere,
  and when delivery undercuts the timeout no timeout ever fires.
- **Catch-up**, now a clause of the pacing core: drift between
  validators is *preserved*, not contracted, by the waiting rule alone —
  refuted on data — and the pacemaker's second rule (seeing evidence of a
  round is entering it) collapses any spread to `Δ + proc` in a single
  post-stabilisation round, whatever it was before; a witness starts with
  a spread of ten and collapses to exactly three. A valid block cannot
  outrun the honest schedule, so the author-blind rule a deployment runs
  is safe (`exists_honest_floor`).
- **The view a validator holds** (`LeanDag/PaceDelivery.lean`): the
  commit rules are view-relative and the pacing line reasons about
  time-indexed holdings; the two are now joined. A validator's holdings
  *are* a view (`viewAt_ids`), which is what makes liveness local; and a
  pacing structure **induces** a delivery layer, so the storage model of
  the DoS arc is derived rather than postulated — including its
  acceptance rule, at most one block per author, which follows from the
  reference discipline (`heldOf_inj`). One structure plus the acceptance
  budget then yields liveness and linear storage together
  (`dos_resistance_of_pace`).
- **Safe Skip** (`LeanDag/SafeSkip/`): a crashed validator rejoins with
  **one constant-size message** denoting a block for every missed round —
  a donor's references plus the self reference the validity rules force.
  The fill is proved a block universe extending the old one unchanged;
  production is restored at every missed round, a filled leader
  candidate is directly skipped rather than committed, and every verdict
  reached before the fill re-derives and agrees after it
  (`decided_fill_agree`).
- **Adaptive leaders** (`LeanDag/Adaptive/`): a Hammerhead-style
  schedule — the leaders ahead recomputed from the agreed prefix, to
  favour validators observed live — proved safe and live for **both**
  commit rules. Safety is unconditional: the schedule-and-verdict
  fixpoint is unique under **no synchrony or fairness hypothesis**, for
  arbitrary adapted policies (`adaptiveRun_agree`); liveness is its
  existence under one clause — the policy keeps placing runs of
  reliable leaders (`adaptiveRun_exists`); and the layer is
  rule-agnostic, the two-round mirror consuming the same policy
  objects.
- **Hybrid fault tolerance** (`LeanDag/Hybrid/`): the two-round rule
  proved safe and live under **separate Byzantine and crash caps** —
  `fb` equivocators, `fc` honest validators that may halt — at
  Orcaella's bound `n ≥ 5·fb + 3·fc + 1` (arXiv:2607.04789), for every
  indirect threshold in an admissible interval whose nonemptiness *is*
  the committee bound. Four validators suffice for two-round finality
  under a single crash, where Byzantine tolerance costs six; at
  `fc = 0` the development collapses onto Odontoceti. The bound is
  also proved **necessary**: one validator short, one view derives
  conflicting verdicts at every threshold
  (`hybrid_bound_necessary`).
- **Resilient checkpoints** (`LeanDag/Hybrid/Checkpoint/`): explicit
  epoch-, height-, and history-bearing proposal messages are
  emitted from append-only per-validator protocol state. The
  `FlexibleFaults` model keeps the hybrid Byzantine and crash classes
  and adds alive-but-corrupt signers; the standalone safety layer
  accepts forked histories as execution inputs. `CommitSpec.lean` adds
  the secure-base bridge at `abc = ∅`: a deterministic VM maps each
  Hybrid commit to one checkpoint, and a `SigningRule` states the
  protocol as two rules, sign what you commit on your own view and
  witness what you proposed. `CommitProofs.lean` derives the quorum
  from the inherited fault bound, ties every online correct validator's
  proposal to a given commit through `Hybrid.safety`, and composes with
  `Hybrid.decided_of_leader_mem` so that DAG production and coverage
  alone yield a finalized checkpoint for a correctly led slot.
  The `*Spec.lean` files are the human-review trust boundary.
  `CommitSpec.lean` also states its theorems as `Prop`-valued claims, so
  `CommitProofs.lean` needs no reading; the safety and recovery pairs
  still keep theorem statements in their `*Proofs.lean` files, where
  the statements, not the bodies, require review.
  Conditional on those inputs, at
  `fabc < n - 3·fb - 2·fc`, quorum intersection derives same-height
  uniqueness and within-epoch prefix consistency; checkpoint safety is
  intentionally scoped to one epoch. Concrete witness messages prove
  that finality leaves a recovery-correct recorder. Recovery broadcasts
  concrete checkpoint-certificate payloads carrying signer sets and
  checkpoint content. An explicit local verifier checks the epoch,
  quorum, and every authenticated proposal, with a soundness theorem
  constructing a `CheckpointQC`; malformed broadcast inputs are not
  channel-excluded. Finite highest-checkpoint selection handles the
  empty case with the closing epoch's canonical execution genesis.
  Submission and preservation are explicitly scoped to the closing
  epoch, so retained older records do not make later recovery rounds
  inconsistent. This recovers checkpoint history under explicit
  submission, broadcast, validation, and adoption assumptions; it does
  not recover the discarded DAG or restart consensus. The broadcast
  algorithm and the paper's post-checkpoint VoteQC extension are not
  formalized.
- **Integration** (`LeanDag/Integration/`): the arcs are proved to
  **compose** — not by settling a quadratic matrix, but by naming the
  invariants each consumes and proving the two universe transformers
  preserve them, after which a validator running four mechanisms at
  once still cannot disagree about a verdict (`hybrid_agree_stack`).
  The deployment constraints only the composition reveals: garbage
  collection at lag `Λ` supports one-message recovery from outages of
  up to `Λ` rounds and no more; a horizon must fall on an epoch
  boundary of an adaptive schedule; and a validator pruned past its own
  history can read but not produce until it **re-genesises** — a
  provision that needs no exemption from the self-parent rule and no
  agreement on where anyone's cut falls.
- **Crash-fault consensus** (`LeanDag/Nemo/`): Nemo-Nemo, the same
  commit rule at a **bare majority quorum** — `n ≥ 2f + 1`, at most `f`
  validators halting, none equivocating — proved safe with **no fault
  bound and no side conditions** (`Nemo.decided_unique`): universal
  non-equivocation retires the twin machinery, and the quorum is
  consumed exactly once in the agreement proof. Liveness holds at the
  classical bound (`Nemo.all_decided_below_of_fairRun`) under a
  fairness clause the mechanisation sharpens: with no failure detector
  a lone committed leader settles only the slot two rounds below it,
  and progress requires committed leaders at **adjacent** rounds —
  which round-robin provides by counting.
- **Mahi-Mahi** (`LeanDag/MahiMahi/`): the asynchronous protocol
  (arXiv:2410.08670) — the same rule at a **wave of `w` rounds**, votes
  counted through the causal cone with a canonical support choice —
  proved safe for every `w ≥ 3` (collapsing onto the core at `w = 3`)
  and live with **no synchrony hypothesis**: every wave directly
  commits some correct validator's block at `w ≥ 4`, at least
  `n − f − |byzantine|` of them at `w ≥ 5` (the core's own common-core
  lemma), and liveness follows from one clause on the schedule and the
  DAG — the late-revealed leader keeps landing among the committed
  candidates — which a coin makes true and which synchrony derives from
  fairness. Two findings about the published argument: the five-round
  count holds only for non-equivocating authors (`1/3` per wave, not
  `2/3`; `2f + 1` leader slots for a deterministic commit, not `f + 1`),
  and the core's per-candidate skip rule is weaker than the
  implementation's slot blame. The arc is built under a
  statement/proof partition: definitions and statements are the audited
  surface, proofs are generated, and a checker enforces the split.
- **Black Marlin** (`LeanDag/BlackMarlin/`): the three-round commit rule
  of a partially synchronous protocol (DISC 2025) that uses neither
  reliable broadcast nor a common coin and elects an anchor in **every
  round**. Its own safety results hold at the core's committee
  `n ≥ 3f+1`, and liveness above the same structural condition as the
  rest of the development, from a run of **two** consecutive reliable
  anchors. **Definition 1's Agreement and Total order do not.** At
  `n = 4`, `f = 1` two reliable validators output different twins of an
  equivocating anchor and neither ever outputs the other's; on the same
  execution they order two *reliable* authors' twinless blocks
  oppositely, which no rule for choosing among twins can repair. The
  repair that restores both descends to a supported anchor, and no
  validator can run it: deciding from its own view loses safety, waiting
  for the evidence loses liveness. The arc is the second under the
  statement/proof partition.


- **Minnow** (`LeanDag/Minnow/`): `crs*`, the commit rule proposed as
  *minimal* for eventual synchrony (arXiv:2608.18029), which decides a
  leader slot from the round immediately above it — `2f+1` processes
  pointing commits, `2f+1` not pointing skips. Two of its clauses are
  written in a way their own sentences do not support, and both are
  settled on data at four processes with `f = 1`. **Two defects survive
  either reading.** A slot counts as *resolved* when some vertex of it
  lies in a candidate's causal past, which is not that vertex being
  decided: under equivocation one twin carries a later leader past the
  slot while the other acquires its quorum, costing **Safe-Commit** —
  and Lemma 10's own case split is where the paper's proof permits it.
  The commit and skip thresholds then leave a gap no view ever decides,
  costing **Live-Commit** for the rule paired with a multi-leader round
  robin, though not for the rule alone.

- **FinWhale** (`LeanDag/FinWhale/`): a fast path at a tunable committee
  (arXiv:2606.26292), which commits a leader block **one round above
  it** — `n − p` distinct validators referencing it — at
  `n = 3f + 2p − 1`, `1 ≤ p ≤ f`, where `p` is not a second class of
  fault but how many of the round's votes the path can do without. Its
  safety rests on one statement: under such a commit **every** block two
  rounds up is evidence for it, so no view can commit a conflicting
  block, skip the slot, or reach a different verdict through an anchor. The committee is exactly the
  least at which that closes — at one validator fewer the count falls
  one short, for every `f` and `p` in range — which is a tightness
  result the paper has and does not use, asserting optimality by
  citation instead. Liveness is derived from the protocol's own
  block-creation conditions C1, C2 and C3 rather than from reference
  coverage, which a reactive builder does not have; the
  two-message-delay latency of Definition 1, stated and not proved
  there, is proved here. **Three further findings**: Lemma 22's proof
  covers `p = 1` only, the C3 case of Lemmas 18 and 19 counts one
  validator too many into a set and has no margin left at `p = 1` once
  that is fixed, and Lemmas 6 and 7 are routed through a clause that a
  validator which has not seen the committed block satisfies for
  nothing. A `Run` bundles one execution and states what a validator
  guarantees — agreement, total order, integrity, validity — with no
  verdict assignment, view or well-formedness condition in the
  statements. And a Mysticeti DAG under this development's
  denial-of-service condition satisfies FinWhale's validity rule with
  the self-parent edge included, so the whole arc applies to it
  unchanged — on the reactive schedule such a universe is a run at every
  horizon, and the condition provably never leaves a builder short of
  authors it may cite.
- **Barnacle** (`LeanDag/Barnacle/`): the adaptive **leader
  count** — every few seconds, measure on the agreed DAG the fraction
  of leader slots the base protocol decided directly and drive the
  number of leaders per round with an additive-increase,
  multiplicative-decrease rule — proved safe and live over an explicit
  interface rendering the paper's assumptions A1–A4, and instantiated
  on Mysticeti, Odontoceti, Nemo-Nemo and Orcaella. Safety is agreement of the
  configuration sequence and of the ledger for **any** update rule,
  under no synchrony or fairness hypothesis (`Agreement.holds`,
  `Ledger.holds`): the algorithm decides under the count in force and
  only then switches, so each configuration's verdicts are derivations
  against one fixed schedule and no fixpoint is needed. There is no
  total run — a finite universe closes finitely many configurations —
  and the paper's sequence of configurations is what every prefix of it
  agrees on. Liveness is Configuration Progress and runs of every
  height under a horizon (`Progress.holds`), from a clause on a
  schedule the paper assumes of its base protocols and that its own
  rotation does not meet by this development's run-fairness route at
  two leaders and four validators; it holds by a descent through the
  *heads* of rounds and a pigeonhole on residues (`Heads.holds`), so
  each rule is live under round-robin at **every** leader count — the
  paper's A4 for its schedule, proved. Seven findings for the paper,
  among them that its liveness clause needs a margin above the slot and
  that Nemo-Nemo's slack is what a majority may miss, not the crash
  bound. The Orcaella instantiation holds at **every admissible
  indirect threshold**, over the subtype of universes whose honest —
  crash-prone included — class does not equivocate, at slack
  `fb + fc` and gap `n + 1`; its witnesses include one DAG the
  interval's two ends decide differently, the twin-canonicity case at
  the genuinely mixed committee, and the slack proved exact. The arc
  is the third under the statement/proof partition.

- **Hydrozoan** (`LeanDag/Hydrozoan/`): the dual-path commit rule of
  the Hydrozoan paper under the hybrid fault model of DagHydrangea —
  `n ≥ 3f + 2c + k + 1`, at most `f` Byzantine, at most `c` crashed,
  `k` a tunable slack — which commits a leader in two message delays on
  `n − p` votes, `p = ⌊(c + k)/2⌋`, or in three on `2f + c + 1`
  certificates, skips it on `n − p` blames, and decides a slot none of
  those settles from the nearest committed anchor by a graded rule
  (certificate, weak quorum, skip). Safety is agreement of any two
  verdicts across views and routes, from six threshold inequalities
  that hold for every fault configuration the class admits — no cap on
  the slack is needed, though the Hydrangea paper states one — and
  prefix consistency of the committed sequences. Liveness above a
  structural rendering of synchrony routes through the slow path, the
  only one a quorum of correct replicas is sure to reach; the fast
  path and the direct skip are stated as performance facts outside the
  liveness claim, firing exactly when the actual faults fit `p`. The
  hypotheses are grounded by exhibition: the wave-aligned rotation is
  fair with no premise, where per-slot rotation is starved inside the
  hybrid bound, and the synchrony package is realizable at every
  horizon. Two findings for the paper: the anchor-sees-the-fast-footprint
  row is consumed in a strengthened, non-Byzantine form, and a slot can
  fast-commit while no certificate for it exists anywhere, so the
  indirect rule's weak rung is necessary. The arc is the fourth under
  the statement/proof partition, and the one that partition was
  designed for; it is developed in
  [`asonnino/mysticeti`](https://github.com/asonnino/mysticeti) beside
  the reference implementation.

- **Optimal-Hydrozoan** (`LeanDag/OptimalHydrozoan/`): the theory-only
  variant of Hydrozoan whose fast path tolerates one more fault —
  `pOpt = ⌊(c + k)/2⌋ + 1`, Hydrangea's lower bound on two-round
  commits, at the same committee — by FinWhale's device: a decision-round
  block that has seen the leader equivocate must not reference the
  leader's block, and quorums of decision-round blocks that are
  *fast evidence* for a candidate replace Hydrozoan's weak quorum of
  votes, in the indirect rule's second rung and in the direct skip. The
  seam consumes the validity rule exactly once, so the evidence rung is
  unique with no tie-break and the statements need no order on ids.
  Safety and liveness mirror Hydrozoan's; what the arc adds is that a
  slot whose leader produced no candidate is skipped by the guaranteed
  quorum alone — a liveness claim where Hydrozoan's skip is
  opportunistic — and not otherwise, since with a candidate present
  `f` Byzantine votes defeat the skip, FinWhale's attack on data. At
  `k = 2f + c − 2` every fault fits the fast path at `n ≥ 5f + 3c − 1`.
  A peer arc importing the Hydrozoan arc read-only, and the second
  developed in `asonnino/mysticeti`.

Every definition is exercised on concrete models by `decide` before
anything is proved from it, and every principal result depends on
exactly Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`, no bespoke axioms, no `native_decide`.

## Building

```
lake build
```

Requires [elan](https://github.com/leanprover/elan). The toolchain version
is pinned in `lean-toolchain`; `lake build` will fetch it automatically.

A `Makefile` splits the work by what it costs. `make fast` builds the
library alone and runs the checks that cost nothing, which is the loop to
work in; `make check` adds the concrete-model layer and is what a commit
needs; `make deps` regenerates the dependency graph and is only needed when
the set of declarations changes. `make help` lists them.

## Layout

- `LeanDag/` — theorem/definition source: the core DAG and Mysticeti
  development at the top level, with the pacing structures in
  `ViewPace.lean` and the delivery layer they induce in
  `PaceDelivery.lean`; `Causality.lean` and `Participation.lean` hold the
  fault-agnostic vocabulary — reachability, the finite cone, production
  and coverage — stated over the raw block data, so the Byzantine and
  crash universes instantiate one set of definitions rather than
  restating them. The arcs are in subdirectories (`Quality/` —
  chain quality; `DoS/` — equivocation and the novelty budget; `GC/` —
  garbage collection; `Odontoceti/` — the two-round protocol;
  `Reactive/` — the reactive schedule; `SafeSkip/` — crash recovery in
  one message; `Adaptive/` — adaptive leader schedules; `Hybrid/` —
  Byzantine and crash faults apart; `Nemo/` — crash-fault consensus at
  a majority quorum; `FinWhale/` — the fast path at
  `n = 3f + 2p − 1`, whose `Model/` holds every definition of the
  protocol and no proof; `MahiMahi/` — the asynchronous rule at wave `w`,
  `BlackMarlin/` — the three-round rule with an anchor every round, and
  `Barnacle/` — the adaptive leader count over an interface for the
  four base rules, `Hydrozoan/` — the dual-path rule under hybrid
  faults, with its own fault model and universe, and
  `OptimalHydrozoan/` — its fast path at Hydrangea's bound, a peer arc
  importing the first, all under a statement/proof partition (`Model/`, `<Result>/Statement.lean`,
  `<Result>/Proof.lean`); `Network/` — the composed
  denial-of-service capstones; `Integration/` — how the arcs compose).
- `LeanDag.lean` — root import file.
- `LeanDagTest/` — `decide` witnesses and concrete models, mirroring the
  same layout.
- `docs/` — the design records and the report. `docs/build-pdf.sh`
  compiles them to `docs/pdf/` — requires `pandoc` and `typst`
  (`brew install pandoc typst`).
- `scripts/` — the extraction and verification pipeline. `DepGraph.lean`
  and `depgraph.py` extract and draw the support diagrams
  (`docs/depgraph/README.md`); `svg2pdf.sh` renders them to PDF;
  `extract-decls.py` reads every declaration with its docstring and
  statement, and `gen-reference.py` regenerates the report's reference
  appendices from it; `audit-report.py` checks the report's
  cross-references, its Lean identifiers, and every displayed statement
  verbatim against the compiled source. Regeneration is deterministic,
  so regenerate-and-diff is the pre-merge check. `check-arc-holes.py` enforces the statement/proof partition of the arcs that adopt it, and `black-marlin-figure.py` draws the execution that refutes Agreement (`docs/figures/`).

## Documents

| Document | Contents |
|---|---|
| [`docs/report.md`](docs/report.md) | **the entry point**: the full report — model, commit rule, trust boundary (including what the adversary may do), safety, liveness on view convergence, the extension arcs, satisfiability, mechanisation — plus generated reference appendices giving **every definition and public theorem verbatim** and an index of the internal lemmas |
| [`docs/spec.md`](docs/spec.md) | the safety design record |
| [`docs/liveness.md`](docs/liveness.md) | the liveness design record, and eventual DAG synchrony |
| [`docs/liveness-routes.md`](docs/liveness-routes.md) | why one liveness route was kept and the others deleted, and what the later clause changes cost |
| [`docs/pipelining-and-multi-leader.md`](docs/pipelining-and-multi-leader.md) | the schedule generalization: eligibility, runs, pipelined commits |
| [`docs/chain-quality.md`](docs/chain-quality.md) | chain quality: coverage without synchrony, inclusion with it |
| [`docs/dos-equivocation-and-growth.md`](docs/dos-equivocation-and-growth.md) | equivocation, exposure, view growth, and the novelty budget |
| [`docs/garbage.md`](docs/garbage.md) | the horizon: truncation, bounded storage, bootstrap without consensus |
| [`docs/odontoceti.md`](docs/odontoceti.md) | the two-round protocol: the generalized thresholds, and the findings |
| [`docs/adaptive-leaders.md`](docs/adaptive-leaders.md) | adaptive leader schedules: the design record and theorem plan |
| [`docs/hybrid-plan.md`](docs/hybrid-plan.md) | hybrid fault tolerance: the design record and theorem plan |
| [`docs/mahi-mahi.md`](docs/mahi-mahi.md) | the asynchronous rule at wave `w`: the clause, and the statement/proof partition |
| [`docs/black-marlin.md`](docs/black-marlin.md) | the three-round commit rule: the link clause, the run of two, what the reactive exit costs, agreement, the delivered order the descent computes, the sequence it outputs, where Agreement fails, and a repair |
| [`docs/minnow.md`](docs/minnow.md) | the minimal commit rule: the two readings its own sentences force, and the two defects that survive both |
| [`docs/finwhale.md`](docs/finwhale.md) | the fast path at `n = 3f + 2p − 1`: the committee and its tightness, the validity clause the fast path needs, liveness from the block-creation conditions, what a validator guarantees, and what the paper should change |
| [`docs/barnacle.md`](docs/barnacle.md) | the adaptive leader count: the interface A1–A4, the configuration-sequence model and why it needs no fixpoint, the liveness clause and its margin, the heads descent, the four instantiations, and the findings |
| [`docs/hydrozoan.md`](docs/hydrozoan.md) | the dual-path rule under hybrid faults: the thresholds and their table, the two-case consistency argument as one statement, the slow path as the guaranteed one, the liveness package and its grounding, and the findings |
| [`docs/optimal-hydrozoan.md`](docs/optimal-hydrozoan.md) | the fast path at Hydrangea's bound: the validity rule and per-block fast evidence, the seam that consumes the rule once, the skip as a liveness claim and FinWhale's attack on it, and the always-fast parametrisation |
| [`docs/integration.md`](docs/integration.md) | composing the arcs: the invariant interface, and what composition revealed |
| [`docs/hydrozoan-integration.md`](docs/hydrozoan-integration.md) | connecting the Hydrozoan arcs to the rest: the three layers, the committee bound the round-robin schedule needs, the missing self-parent clause, Hydrozoan as a Barnacle base rule, the transport of safety and liveness through a recovery and a horizon, and what the absent delivery layer costs |
| [`docs/transformer-interface.md`](docs/transformer-interface.md) | what a protocol-generic transformer interface would take: the survey of the nine decision relations, the schema they share, and the semantic conditions a cut and a fill turn on |
| [`docs/related.md`](docs/related.md) | a survey of consensus on uncertified DAGs |
| [`docs/style.md`](docs/style.md) | writing conventions for the documents and the source |

## Contributors

- [Alberto Sonnino](https://github.com/asonnino) — the crash-fault arc
  (`LeanDag/Nemo/`,
  [#1](https://github.com/gdanezis/lean-dag/pull/1)): the majority-quorum
  foundation and its intersection lemma, the wave-two commit rule,
  agreement without side conditions, liveness at `n ≥ 2f+1`, and the
  three-validator witness model. He also contributed the wave-robin
  schedule ([#3](https://github.com/gdanezis/lean-dag/pull/3)), the
  Mahi-Mahi arc ([#5](https://github.com/gdanezis/lean-dag/pull/5)), the
  Barnacle arc ([#7](https://github.com/gdanezis/lean-dag/pull/7)), and
  the Hydrozoan arc (`LeanDag/Hydrozoan/`,
  [#8](https://github.com/gdanezis/lean-dag/pull/8)): the dual-path commit rule
  under hybrid faults, its safety from the threshold table alone and its
  liveness through the slow path — and its Optimal variant
  (`LeanDag/OptimalHydrozoan/`,
  [#9](https://github.com/gdanezis/lean-dag/pull/9)), the fast path at
  Hydrangea's bound.

- [Lefteris Kokoris-Kogias](https://github.com/LefKok) — the resilient
  checkpoint arc (`LeanDag/Hybrid/Checkpoint/`,
  [#4](https://github.com/gdanezis/lean-dag/pull/4)): the
  assume-guarantee model of epoch-bearing proposals over append-only
  validator state, same-height uniqueness and within-epoch prefix
  consistency from quorum intersection at
  `fabc < n − 3·fb − 2·fc`, resilient finality, and highest-checkpoint
  recovery with its local verifier and soundness theorem.

## License

MIT — see [`LICENSE`](LICENSE).
