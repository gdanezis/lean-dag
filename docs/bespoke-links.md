# The bespoke links, and how they were removed

`docs/target-properties.md` part 2 claims that a rule showing the
properties composes with each mechanism **with no further proof**. That
claim was true of the mechanisms the arc converted and not of the
library. `scripts/audit-bespoke.py` said by how much, and this file is
the record of closing the gap.

**Result: none remain.** Every mechanism theorem in the development, for
every rule that shows the six properties, now reaches that rule only
through the properties.

## What the audit measures

Not whether a mechanism *mentions* a protocol — a theorem about garbage
collection over Hydrozoan must say `Hydrozoan.Decided`, and no
abstraction removes that. What it measures is whether a mechanism
theorem's **proof** reaches a protocol theorem *about verdicts* by a
path that avoids the properties. The dependency closure is taken with
`LeanDag.Properties.*` and each protocol's conformance file as barriers;
what is still reachable is borrowed reasoning.

Two exclusions, both deliberate:

* **Shared structure is not borrowing.** `mem_blocksAt`, `historyFrom_*`,
  `quorumCard_*`, `Faults.card_validators` live in protocol files and are
  facts about DAGs and committees. Counting them gives 382 links and
  measures nothing; restricting the targets to the 115 protocol theorems
  that name a decision relation gives 49 and measures the claim.
* **A rule with no `Banded` has nothing to route through.** Fifteen
  links for Optimal-Hydrozoan, Nemo and Hybrid/Orcaella were the
  instances gap of §11.4 seen from a third side, not a defect of the
  arc. The script reported them separately and they did not fail a run.

That left **35 links, for the four rules that show the six**. The script
still runs, and now fails on any new one.

**The second exclusion is now empty.** Nemo, Hybrid/Orcaella, FinWhale
and Optimal-Hydrozoan have since been given bands, and their links —
eight, all Optimal's — were closed the same way as the original 35:
`Barnacle.OptimalHydrozoan.holds` reads the three properties instead of
`SlotAgreement.holds` and the constructors,
`Barnacle.OptimalHydrozoanLive` is `descent_of_properties` over
`LeaderCommits` and `Indirect`, and
Optimal-Hydrozoan's own cut/fill verdict cells are the generic
`Properties/Arcs/Record.lean` cells applied at `optOnRecord`, with no
bespoke name left to route — two more inductions over a decision relation
deleted. Every rule with a carrier now shows the six, so the audit's
separate column has nothing left to report.

## A. Agreement — `Properties.Agree` (10)

`Hydrozoan.agree` replaces `SlotAgreement.holds` at the stack capstones
and in `ViaProperties`, and `Deployment.{agrees,safe}` follow through
them. `OdontocetiProperties.agree` replaces `Odontoceti.decided_unique`
in the adaptive arc, taking `partialRun_agree`, `adaptiveRun_agree` and
`adaptiveRun_exists` with it.

`SkipMsg.decided_fill_agree` was **deleted** rather than rerouted. Like
garbage collection and Hydrozoan's two transformers, the bespoke
transport it composed already had a properties replacement, so the pair
went and `Arcs.decided_fill_agree_of_properties` took over. That took
`SkipMsg.decided_fill` from group B with it.

## B. A commit names a candidate — `Properties.CommitsCandidate` (5)

`Hydrozoan.commitsCandidate` replaces `isLeaderBlock_of_decided` in the
transformer study, and the deleted `SkipMsg.decided_fill` was the fifth.

## C. Barnacle's `Laws` — three properties (5)

`Laws.agree` **is** `Agree` and `Laws.candidates` **is**
`CommitsCandidate` (§11.2). `Laws.decided_of_directCommitIn` was the
blocker: `CommitsDirect` was *derived from* `Laws` for these rules, so
citing it would have been circular.

The circularity dissolved once `CommitsDirect` was proved natively. The
core already had one; Odontoceti's moved with its carrier; Hydrozoan's
was written for this, at a *disjunction* — the fast path or the slow one
— which is what Barnacle's `DirectCommitIn` is for that rule. All three
`Laws` proofs now read the three properties, and `Barnacle.Live.holds`
follows.

## D. A reliable leader's slot commits — `Properties.LeaderCommits` (11)

This group needed a bridge rather than a substitution: the consumers
carry their synchrony hypotheses loose, and `LeaderCommits` takes them
packaged as the protocol's `Live`.

`MysticetiProperties.decided_of_leader_of_populated_of_properties` is
that bridge — the shape every capstone uses, reached from
`LeaderCommits` and `CommitsCandidate` instead of from L4 — and
`commits_recur_on_of_properties` carries it through the schedule half so
that a pacing mechanism consuming L6 does not thereby reach into the
protocol. Chain quality, inclusion, the quantitative bound and the
pacing spine take those two.

Hydrozoan's pair was restated rather than reproved. `commitLiveness_stackHZ`
asserted `CommitLiveness`, whose middle conjunct is the *slow threshold* —
direct evidence in the DAG, with no property, which a mechanism has no
business asserting. `decided_of_leader_stackHZ` claims the verdict and
not the evidence, which is what a recovered replica's liveness is about.

## E. The indirect descent — `Properties.Indirect` (2)

Routable only once §11.2b existed. `decided_of_anchor_stackHZ` is
`Indirect` at the stack where `anchoredTotality_stackHZ` was HZ6, and
`Deployment.decidesBelow` follows.

## F. View monotonicity — free from `Banded` (1)

`decided_mono_of_band` replaces `decided_full` in `ViewPace`.

## G. An unsupported slot is skipped — `Properties.SkipsUnsupported` (1)

`decided_none_of_leader_absent_of_properties` reads the reliable set off
the view — it is the creators of the blocks the view holds one round up,
so the quorum bound the caller already has *is* `Ok`, and `PresentAt` is
what membership of that set means. `Unsupported` is vacuous, since a
halted leader leaves nothing to support, and that is the whole content
of L5.

## What it cost

**Universes, and this was the price of the separation rather than a side
effect of it.** `Properties/` is `Type`; `ViewPace`, `Quantitative`,
`Quality/Inclusion` and `Integration/Lifecycle` were `Type*` and so
could not *name* a property at all. Dropping them brought 27 files with
them — the pacing layer, and through it FinWhale, Black Marlin and
Mahi-Mahi, none of which this work otherwise touches. The generality
lost is unused: every instance in the development is at `Type`.

**One structural change, and it is the more interesting finding.**
`OdontocetiProperties.lean` imports the adaptive arc for the bounded
relation, so Odontoceti's carrier sat *downstream of a mechanism* and no
mechanism could reach it. The carrier, `Causal`, `Agree`,
`CommitsCandidate` and `CommitsDirect` moved to
`LeanDag/Odontoceti/Carrier.lean`, upstream of everything — the shape
Hydrozoan has had since its carrier was written. A conformance layer has
to be upstream of every mechanism or it cannot serve one, and nothing
before this audit had forced the point.

## What the audit does not claim

It says nothing about the two rules with no carrier. Mahi-Mahi's band is
conditional on `2 ≤ w` and Black Marlin commits by round with no
slot-indexed relation, so neither has a `DagRule` to state a property
at; a mechanism over either would be bespoke by construction, and none
is in the development. What the count now covers is the eight rules that
do have carriers, and for those it is zero.
