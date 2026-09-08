# lean-dag — Hydrozoan and Optimal-Hydrozoan: the carriers, Barnacle, and the mechanisms

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Hydrozoan (`docs/hydrozoan.md`) and Optimal-Hydrozoan
(`docs/optimal-hydrozoan.md`) are stated against Mathlib alone: their
model, rules and theorems import nothing from the rest of the
development. This document records how they nonetheless get every
mechanism the development has — garbage collection, crash recovery,
re-genesis, the adaptive leader count — and what design decisions that
took. The route is the one every rule takes (`docs/target-properties.md`,
opening part): a carrier, the properties and a support at it, and the
generic theorems applied. The arcs themselves are untouched.

## 1. The carriers

`LeanDag.Hydrozoan.rule` (`Hydrozoan/Helpers/Carrier.lean`) is
Hydrozoan's `BlockUniverse` read as a `Properties.DagRule`. That
universe is the block record at Hydrozoan's validity with
non-equivocation asked of the non-Byzantine replicas, its block the
shared `Block` with a `Unit` payload and its schedule the shared
`Slots`, so `block`, `ids`, the views and the decision relation are the
arc's own with nothing renamed. The carrier's three laws come from the
record: views hold universe blocks, views are closed under references,
and the universe is a block DAG by its `complete` field and the
`predecessor` clause of its validity.

`OptimalHydrozoanProperties.optimalRule` (`OptimalHydrozoan/Carrier.lean`)
is `OptUniverse`'s own anchored relation read through its projection to
Hydrozoan's record, `toDagRuleVia OptUniverse.toBlockRecord`; the
exclusion the laws hold under is `Clause.leaderExcluded`, one clause of
`OptUniverse`'s own validity `ValidOpt` (§3), and `DecidedOpt` is the
decision relation that projection builds. Both carriers are the ones
Barnacle's `hydrozoan` and `optimalHydrozoan` rules name for their
`DagRule` parent, so there is one carrier per rule.

The fault model is `hzReliability`: the correct set with slack `f + c`,
Byzantine and crashed together, a minority by Hydrozoan's committee
bound. The fast paths have their own, `hzFastReliability` and
`optFastReliability`, at the fast thresholds.

## 2. The properties and the supports

Hydrozoan shows the four properties: `banded` (`Helpers/Banded.lean`,
the one induction with work in it, over the six constructors of
`Decided`), `agree` (HZ3 in the carrier's vocabulary),
`commitsCandidate` and `indirect` (`Helpers/Commit.lean`). Its support
is `hzSupport`, whose `Commits` law is the slow path: certifiers three
rounds up, certifying by the slow certificate. A second support,
`voteSupport` at `hzFastReliability`, is the fast path, and
`voteSupport_fast_commits` is its `Commits` law at the stronger fault
model. Optimal-Hydrozoan shows the same four with `optSupport` and its
own fast-path support.

Of the optional properties Hydrozoan shows `CommitsDirect`,
`SkipsUnsupported` and `Quorate`; Optimal shows `CommitsDirect` and
`Quorate`. The grade of Hydrozoan's `SkipsUnsupported` is a finding: its
skip needs `qFast = n − p` blames at the slot, while a quorum of correct
replicas has `q = n − f − c` members, so a correct quorum skips an
unsupported slot exactly when `f + c ≤ p` (`Helpers/Skippability.lean`).
Optimal's skip is at `qCert ≤ q` and needs no such condition. Neither
model carries a self-parent clause, so neither shows `SelfParent`, and
their liveness headline is progress without inclusion (§4).

`Hydrozoan/Properties/Statement.lean` lists what Hydrozoan shows, as a
conformance statement in the arc's own partition, and `Proof.lean`
discharges it from the helpers.

## 3. Barnacle over the two rules

Barnacle (`docs/barnacle.md`) abstracts a commit rule as `BaseRule`,
which extends `DagRule`, and proves the adaptive leader count against
it. The instantiations are `Barnacle/Hydrozoan/`, `HydrozoanLive/`,
`OptimalHydrozoan/` and `OptimalHydrozoanLive/`, each a statement file
and a proof file. The decisions they embody:

- **The base rule is the carrier.** `hydrozoan.toDagRule` is
  `LeanDag.Hydrozoan.rule`; the wave length is three; the interface's
  direct-commit field is the disjunction of the two commit paths, each
  judged from the view (`FastCommitInView ∨ SlowCommitInView`), and it
  is decidable. `hydrozoan` is `ofAnchored (Hydrozoan.hydrozoanAnchored ..)`
  (`Model/Anchored.lean`), the generic adapter every rule of this arc
  now uses; nothing under `Helpers/` is bespoke to Hydrozoan any more.
- **The laws are read off the decision relation.** `agree` is HZ3;
  `candidates` is `commitsCandidate`. The history view is defined with
  `historyFrom`, so the interface's `historyView_ids` law is by
  construction.
- **Neither a self-parent clause nor a committee condition is consumed
  by the base rule.** The history layer reads a Hydrozoan universe
  through `CausalStructure`, which its own fields supply; nothing else of
  the universe is read.
- **The live rule's good DAG is Hydrozoan's own liveness package**: a
  quorum-sized set of correct replicas, synchronised from a round and
  populating every round to a horizon. Its slack is `f + c`, the
  fully-correct class being what liveness counts. The descent laws come
  from the support through `descent_of_support` — `hzSupport`'s
  `Commits` law and `indirect` — since at wave length three the
  interface's spacing condition is Hydrozoan's anchor eligibility.
- **Round-robin liveness is the one place a committee condition
  appears**, and it is `3(f + c) + 1 ≤ n`, the bound
  `liveOn_roundRobin` needs, reached by a route that mentions neither
  Hydrozoan's quorum nor its intersection argument. Hydrozoan's own
  bound `3f + 2c + k + 1 ≤ n` gives it when `c ≤ k`, but that is
  sufficient rather than necessary, so the bound is the hypothesis and
  the slack condition is not. It is a hypothesis of `RoundRobinLive` and
  of nothing above it.
- **Optimal's leader exclusion carries no schedule at all.**
  `Clause.leaderExcluded` (`Common/BlockRecord.lean`) is a clause of
  `OptUniverse`'s own validity `ValidOpt`, stated over a block's parents
  and their votes with no `Slots` instance anywhere in its type — it
  binds before any schedule is chosen, not merely independently of the
  leader count. `OptUniverse.leader_excluded`
  (`OptimalHydrozoan/Helpers/Universe.lean`) is the theorem reading it
  back at a schedule, giving `LeaderExcluded` — the round/leader form
  `sections/optimal-protocol.tex` states and the decision relation's
  laws consume (`SlotAgreement/Proof.lean`) — at every `Slots` instance
  the interface hands over, so no leader-count monotonicity argument is
  needed: the clause was never schedule-indexed to begin with. Optimal's
  evidence rung needs no tie-break, so `DecidableEq` suffices where
  Hydrozoan's instantiation takes a `LinearOrder`.

## 4. The mechanisms

`Integration/HydrozoanMechanisms.lean` takes Hydrozoan's cut and fill
from the block record, Hydrozoan's universe being that record.
`Model/BlockUniverse.lean` shows its validity `Mechanised` and
`CopyStable` as the validity family `ValidAt` at `q` with the
distinct-creators clause, and `Hydrozoan/Helpers/Record.lean` gives the carrier's
`onRecord`, every map the identity with
every equation `rfl`. The cut, the copy fill and re-genesis are then
`BlockRecord.chop`, `BlockRecord.copyFill` and `BlockRecord.addGenesis`
themselves, under no name of Hydrozoan's own, and their witnesses and
verdict cells are the generic ones at `onRecord`. The
verdict cells are then `LocalTruncate.of_banded` and `Persist.of_banded`
at `banded`, with agreement from `agree`: `decided_chop_iff_hz`,
`decided_agree_chop_hz`, `decided_copyFillHZ`, `decided_agree_copyFillHZ`.
The fill needs no quorum hypothesis where the core's does, because
Hydrozoan's skip counts blames at the slot and the count does not move
when no old block references a fresh identifier; the prompt skip at the
fill is `decided_none_fresh_hz`, at grade `qFast ≤ |T|`, with
`decided_none_fresh_agree_hz` saying no view decides that slot
otherwise. The same witness gives what the fill does to coverage:
`not_synchronisedOn_copyFill_hz` is the generic refutation of
`Timed/Extension.lean` at the record's `extends_copyFill`.

`OptimalHydrozoan/Record.lean` needs no invariant at all:
leader exclusion is now a clause of `OptUniverse`'s own validity
`ValidOpt` (§3), and the record's cut, copy fill and re-genesis
preserve validity clause by clause, so `OptimalHydrozoanProperties.onRecord` reads the carrier
as records under the trivial invariant `BlockRecord.Any`, with nothing
proved per mechanism. The record's constructions at it are
`OptimalHydrozoanProperties.onRecord.chop`, `OptimalHydrozoanProperties.onRecord.copyFill` and `OptimalHydrozoanProperties.onRecord.addGenesis`.
Every verdict cell of both rules is `Properties/Arcs/Record.lean` at
`Hydrozoan.onRecord` or `OptimalHydrozoanProperties.onRecord`, with nothing written per cell.

Liveness across every mechanism is the generic `Support.live_of_truncates`
and `Support.live_of_sustains` at `hzSupport` and `optSupport`, and the
adaptive leader schedule runs over Hydrozoan in
`Integration/AdaptiveHydrozoan.lean`. The headlines are
`Hydrozoan.Properties.safety` and `progress`, and
`OptimalHydrozoanProperties.safety` and `progress`: safety across any
stack of the mechanisms, every slot below a fair run decided and
commits recurring on any execution meeting the support's `live`. The
inclusion half of liveness is absent for both, because their models
carry no self-parent clause; a replica's own blocks are guaranteed into
the ledger by the coverage half of chain quality (`Quorate`) and not
individually.

## 5. Witnesses and discipline

`LeanDagTest/Barnacle/Hydrozoan.lean` exercises the base rule by `decide`
on the arc's own seven-replica universe `U3`, with the schedule fixed
explicitly as `S7` in every statement so that nothing depends on which
`Slots` instance resolution would pick. `LeanDagTest/Barnacle/HydrozoanLive.lean`
exhibits configurations on both sides of the round-robin bound
`3(f + c) + 1 ≤ n`, and shows where `c ≤ k` is consumed.
`LeanDagTest/Barnacle/OptimalHydrozoan.lean` shows that
`Clause.leaderExcluded` separates exactly the universes the arc's own
rule does, on the sixteen-block universe where the Byzantine leader
equivocates: `UX`, exhibited as an `OptUniverse`, satisfies it, and
`UbadX`, exhibited as a `BlockUniverse` no `OptUniverse` extends, fails
it at one block. The
`holds` statements are audited for axioms in `LeanDagTest/Barnacle/Axioms.lean`.
The cut and fill are checked by the build and by the audits of
`docs/target-properties.md`, which show every mechanism cell for both
rules.

The layout follows the statement/proof partition of the arcs: statement
files are proof-free, model files theorem-free, and
`scripts/check-arc-holes.py` enforces it for `Barnacle/`, `Hydrozoan/`
and `OptimalHydrozoan/`.
