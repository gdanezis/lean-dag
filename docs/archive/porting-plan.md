# Porting the four remaining rules to the properties

> **Archived.** The plan is complete: Nemo, Hybrid/Orcaella,
> Optimal-Hydrozoan and FinWhale all now show the six properties this
> document ports them onto (`scripts/audit-conformance.py`,
> `scripts/audit-bespoke.py`). The closing section below, written before
> Optimal-Hydrozoan's `Banded` was finished, is corrected in place.
> Kept for historical record only.

`docs/bespoke-links.md` closed the protocol-to-mechanism gap for the four
rules that show the six properties. Fifteen links stand, and they stand
because their rule has no `Banded` to route through:

| rule | bespoke links | where |
|---|---|---|
| Optimal-Hydrozoan | 8 | carrier done; band open |
| Hybrid / Orcaella | ~~4~~ **0** | routed (`Hybrid/Carrier.lean`, `HybridProperties.lean`) |
| Nemo | ~~3~~ **0** | routed (`Nemo/Carrier.lean`, `NemoProperties.lean`) |
| FinWhale | 0 | — |

FinWhale has none, and that is itself the finding: nothing consumes
FinWhale's verdicts, because it has no slot-indexed decision relation for
a mechanism to consume. Porting it removes no bespoke code. What it supplies is the one
thing §11.4 says is still missing — evidence that the six obligations are
the right six, tested against the rule least like Mysticeti.

## What each rule already has

| | `Slots` | `Decided` | agreement | candidate | direct | eligibility |
|---|---|---|---|---|---|---|
| Nemo | yes | 5 ctors | `decided_unique` | `isLeaderBlock_of_decided` | `DirectCommitIn` | wave 2 |
| Hybrid | yes | 6 ctors, indexed by threshold `k` | `decided_unique`, **under `HonestNoEquiv`** | `isLeaderBlock_of_decided` | `DirectCommitIn` | wave 2 |
| Optimal-Hydrozoan | yes | 6 ctors, over `OptUniverse` | `decided_unique` | `isLeaderBlock_of_decidedOpt` | fast/slow | wave 3 |
| FinWhale | **no** | **none** — per-round predicates | Lemma 12 | — | `DirectCommit D l` | — |

So for three of the four the work is one `Banded` induction apiece plus a
carrier; for the fourth it is a modelling job first.

## Order, and why

**1. Nemo — done.** The cheapest and the pattern-setter: it has every ingredient,
five constructors, and a wave of two — its decision relation mirrors
Odontoceti's, whose `Banded` is the template (122 lines). If the port is
not routine here it will not be routine anywhere, so this is the one that
tests the estimate.

**2. Hybrid / Orcaella — done.** One real obstacle, and it has a known answer.
`Hybrid.decided_unique` is **conditional on `HonestNoEquiv U`**, so
`Properties.Agree` — which is unconditional — cannot hold at the bare
universe. Barnacle already solved this: its Orcaella carrier takes
`Universe := {U // HonestNoEquiv U}`, and the hypothesis becomes a field
of the object rather than a premise of the theorem. A native carrier does
the same, one per admissible threshold. Nothing else here is unusual.

**3. Optimal-Hydrozoan — carrier done, band open.** The biggest payoff, because four of its eight
links are `Integration/Hydrozoan/OptimalChopDecided.lean` — three
inductions carrying verdicts across the cut, which is precisely what
`LocalTruncate.of_banded` replaces. Expect the deletion cascade that
`GC/ChopDecided.lean` and `Integration/Hydrozoan/ChopDecided.lean` already
went through (§11.4e). The carrier is over `OptUniverse` with
`block := fun U => U.toBlockUniverse.block`; `DagRule.Universe` is an
arbitrary type, so nothing in the carrier resists this.

**4. FinWhale — carrier and three properties done; the band needs a rewrite.** Two blockers, and the first is not conformance work.

* **No slot layer.** Commits and skips are per-round predicates over a
  `Dag`, and verdicts are a `Verdict` inductive with `WellFormed`. There
  is no `Decided S V k v`. A carrier needs one, and the honest way to get
  it is an identity schedule — slot `k` at round `k` — with `Decided`
  assembled from `DirectCommit`, `DirectSkip` and the anchor rule.
* **An absolute round read.** `ExposesEquivocation` uses truncated
  subtraction on a round (`scripts/audit-rounds.py`, §3.4c), so the band
  is unprovable until that is restated as a comparison. This is
  independent of the slot layer and has to go first.

If either reshapes FinWhale's model rather than wraps it, the
right answer is to stop and record why — a rule that cannot carry the
obligations without being rewritten is *evidence about the obligations*,
which is what porting FinWhale is for.

## The shape of each port

Fixed by the three ports already done, so this is a checklist rather than
a design:

1. **`<Rule>/Carrier.lean`**, upstream of every mechanism — the carrier,
   `Causal`, `Agree`, `CommitsCandidate`, `CommitsDirect`. Upstream is not
   optional: Odontoceti's carrier sat downstream of the adaptive arc and
   no mechanism could reach it (`docs/bespoke-links.md`).
2. **`<Rule>Properties.lean`** — `Banded`, the one induction the rule
   owes, and then `Indirect`, `LeaderCommits`, `descends` on top of it.
   `Persist` and `LocalTruncate` follow from the band and are not stated.
3. **Convert the links.** `Laws` fields become the three properties;
   `Descent` becomes `descent_of_properties` plus a `GoodGives` bridge;
   any bespoke transport with a properties replacement is **deleted**
   rather than kept as a corollary.
4. **Re-run `scripts/audit-bespoke.py`.** It fails on an unrecorded link,
   so the conversion is checked rather than asserted.

## What would falsify the plan

Three things, each of which is worth more than the port succeeding:

* **A rule whose `Banded` is false.** The band forbids reading an absolute
  round. Odontoceti's attempt found a defect in its skip rule; a second
  such find would say more about the obligation than another success.
* **A property that has to be graded to fit.** `Agree` for Hybrid is the
  test case. If the subtype carrier does not work, the alternative is a
  conditional `Agree`, and that would mean the obligation as stated is
  wrong rather than the rule.
* **A mechanism law with no property at all.** Already seen once, in
  Hydrozoan's `CommitLiveness` and its slow threshold. A second instance
  would be a candidate for a new obligation rather than a gap.

## Nemo, done

The estimate held. What it took:

* **`Nemo/Carrier.lean`** — the carrier, `Causal`, `Agree`,
  `CommitsCandidate`, `CommitsDirect`. Nemo's agreement is
  hypothesis-free, because non-equivocation is a *field* of its
  `Universe` rather than a premise: the model is crash-only. That is why
  `Agree` holds at the bare universe here and will not for Hybrid.
* **`NemoProperties.lean`** — `Banded` (one induction, three cases),
  then `Indirect`, `LeaderCommits` and `descends` on top.
* **Five generic band helpers**, lifted into `Properties/Band.lean`. They
  existed only at the core's carrier, where they were written, and every
  rule's band proof needs them. Nemo needed local wrappers anyway,
  phrased in `U.block` rather than `R.block U` — the two are equal by
  definition and distinct atoms to `omega`, so saying it once per rule
  keeps the proofs in one vocabulary.
* **The three links**, converted: `Laws` reads the three properties, and
  `Descent` is `descent_of_properties` with a ten-line `GoodGives`.

**`SkipsUnsupported` is not owed and the table's dash is right.** Nemo
has three constructors and no direct skip: a slot with no candidate waits
for an anchor. That is exactly the case the property was made optional
for (§11.4c), and it is the first time a rule has exercised the
distinction rather than simply having the property.

**Nothing was falsified.** No graded property was needed, the band went
through as stated, and every mechanism law had a counterpart.

## Hybrid / Orcaella, done — and the plan's first falsification fired

Both predictions held, and one of them was the interesting kind.

**The subtype carrier works.** `Hybrid.decided_unique` is conditional on
`HonestNoEquiv`, and `Properties.Agree` is unconditional with no graded
form. Taking `Universe := {U // HonestNoEquiv U}` makes the hypothesis
part of the object, and `Agree` then holds outright — which is what
Barnacle's carrier already did and what the plan said to copy. No
property had to be weakened.

**The band was false, and the rule was wrong.** `Decided.directSkip`
quantified over the candidates a slot happens to have; a slot with none
satisfied it for nothing, and a mechanism adding one defeats it. This is
the *third* rule with that defect — the core (§3.2), Odontoceti (§3.12),
now Hybrid — and each time the band is what found it. The repair is the
same each time: `DirectSkipSlotIn`, a quorum of voting-round blocks
referencing no candidate at all, with the per-candidate form recovered
as a corollary so nothing stated over it changes.

Hybrid's quorum is its own, `q = n − fb − fc`, so unlike Odontoceti it
could not reuse the core's predicate verbatim — the shape transferred,
the threshold did not.

**One witness was vacuous and is now a refutation.** `uhyb4_slot3`
claimed the crashed validator's slot was skipped. Under the repaired
rule it is not: `Uhyb4` stops at round `3`, so no evidence exists and
the slot is undecided there. Saying that is worth more than the claim it
replaced. The Orcaella witness at `UL` survived, its DAG carrying the
round-`4` blocks, so the repair cost one vacuous theorem and no real
one.

**`SkipsUnsupported` came with it**, as it did for Odontoceti: the
liveness half, and the reason to believe the repair was a repair rather
than a tightening. A skip rule no quorum can trigger would be sound and
useless.

## Optimal-Hydrozoan, half done

**The carrier is built, and the obstacle it raised was the sharpest of
the four.** `OptUniverse` is *indexed by the schedule* — `leader_excluded`
reads `S.leader k` and `decisionRound k` — so `OptUniverse` at `S` and at
`S'` are different types. `DagRule.Universe` is one type and `Banded`
compares verdicts across schedules, so a carrier over `OptUniverse` could
not state the band at all. The cut says the same from the other side:
`optChopHZ` lands in a *different universe type* from the one it starts
in, which `Truncates` cannot relate.

The escape was already in the development. `LeaderExcludedAll`
quantifies the same exclusion over rounds and validators instead of over
slots, so it is schedule-free, and `optUniverseOf` rebuilds the indexed
universe at any schedule. The carrier's universe is the subtype it cuts
out — the shape Hybrid needed for `HonestNoEquiv` — and the schedule
re-enters in `Decided`, where `DagRule` puts it.

So neither the interface nor the rule had to change. What had to change
is reading the invariant in the vocabulary that does not mention the
schedule, and the rule already had it. That is worth more than the port:
it says a schedule-indexed universe is not a counterexample to the
carrier, provided the invariant can be stated schedule-free — and if one
ever cannot be, *that* is the counterexample.

**What is left.** `Banded`, and it is the largest of the four: six
constructors, and rules the other three do not have — fast evidence with
a threshold that depends on whether the block witnesses an equivocation,
`IsNoFastEvidence` quantified negatively over the slot's candidates, and
the anchor-linked evidence quorum. Most of it should come from
Hydrozoan's band helpers, which Optimal's universe shares; the
Optimal-specific part is roughly eight lemmas.

Two things checked ahead of writing it, because either would have
stopped it:

* **The skip needs no repair.** Unlike the core, Odontoceti and Hybrid,
  Optimal's `SkippedLeaderOptInView` already counts blames at the *slot*
  rather than per candidate. Its `IsNoFastEvidence` clause is the
  negative universal, and a candidate the band did not carry is fast
  evidence for nothing, since no old block votes for it — provided the
  thresholds are positive, which `tPlain_pos` gives.
* **Equivocation witnesses do not appear from nowhere.** A fresh
  candidate cannot be one of the two a decision block witnesses, because
  witnessing needs an old block to vote for it.

**Then the eight links**, four of which are
`Integration/Hydrozoan/OptimalChopDecided.lean` — three inductions
carrying verdicts across the cut, which is what `LocalTruncate.of_banded`
replaces. That deletion cascade is the payoff and is why this rule was
ordered third rather than last.

## FinWhale: what it has, and what the band actually costs

`FinWhale/Carrier.lean` has the carrier, `Causal`, `Agree`,
`CommitsCandidate`, and — the one that matters most here — a proof that
the relation is **inhabited**.

**Its `Decided` is existential, which is why inhabitation matters.**
FinWhale has no inductive decision relation. Every other rule derives
verdicts inductively; FinWhale assigns them by a *function*
`dec : ℕ → Verdict BlockId` constrained by `WellFormed`, the paper's
reverse pass read as a condition rather than a construction. So
`Decided S U V r v` says *some* well-formed assignment on this view gives
`v` at `r`, with two further conjuncts that are facts about a real
validator's assignment rather than inventions: it commits only blocks of
the slot, and it is finite.

An existential relation can be empty, and then `Agree` holds for nothing.
This arc has been caught by vacuity twice (§3.4, §3.6), so
`decided_of_directCommit` is proved: FinWhale's own reverse pass, run on
the view with the universe's tie-break, *is* an assignment — well formed,
committing only slot blocks, finite because a view is a finite set — and
`WellFormed.direct_commit` reads the commit off it.

**Two properties are blocked, and by one cause.** FinWhale reads its
leader schedule off the **`Dag`**, as a field, where every other rule
takes it from a `Slots` instance; and it indexes verdicts by **round**,
where the properties index by slot. So the carrier's `Decided` has to
*pin* the two together — slots are rounds, and the schedule's leaders are
the DAG's — and the pinning is a conjunct that has to be proved wherever
`Decided` is concluded.

* `CommitsCandidate` **can** have it, because `IsCandidate` is stated at
  the schedule, so the pinning is available as a hypothesis.
* `CommitsDirect` **cannot**: its direct predicate is passed a view, a
  block and a round, and never the schedule, so nothing can supply the
  pinning. The theorem it would have followed from is proved instead.
* `Banded` cannot either, and for the sharper reason: `AgreeBand`
  constrains ids, blocks and references, and says nothing about a DAG's
  `leader` field — so two DAGs in a band may name different leaders and
  decide differently. The band is *false* as the rule stands.

**What the fix is, and what it costs.** Not a property and not the
carrier: FinWhale's decision layer has to read the schedule from a
`Slots` instance rather than from the `Dag`, and index by slot rather
than by round. Concretely, `slotBlocks D r` becomes
`blocksAt D (S.slotRound k)` filtered by `S.leader k`, every `r + 2`
becomes `S.slotRound k + 2`, and `Anchor`'s `r + 2 < a` becomes a
condition on slot rounds. That reaches `Verdict`, `WellFormed`, `Anchor`,
the reverse pass, Lemma 12's downward induction and the ledger order —
about 5000 lines whose arithmetic is round arithmetic.

Worth noting what this does *not* say. The obligations are not wrong for
FinWhale, and no property needed weakening or grading. What the port
found is that a rule which puts its schedule inside its universe cannot
be related to another DAG by a band, because a band is a statement about
blocks. That is a fact about the rule's formalisation, and it is the
same fact §3.4c recorded from the other end when it said FinWhale has no
`Slots` layer.

**The absolute-round read is a second, smaller blocker** and is
unchanged: `ExposesEquivocation` uses truncated subtraction on a round,
so even after the slot-indexing it would need restating as a comparison.

## FinWhale: the schedule is out of the DAG

The blocker was never a property. FinWhale carried its leader function
as a **field of the `Dag`**, which put a schedule inside a universe: a
band is a statement about blocks, so two DAGs in one band could name
different leaders and decide differently, and `Banded` was false for
that reason alone.

The field is gone. `slotBlocks`, `DirectSkip`, `IndirectCommit`,
`viewCommit`, `viewSkip`, `decOf` and the rest take the leader function
they are given; `Run` carries it, which is where a schedule belongs —
an execution runs a schedule, a DAG is blocks. `FinWhaleProperties.Decided`
reads `S.leader`, exactly as every other carrier does.

**Two validity clauses had to be restated, and both came out better.**

* `ExposesEquivocation` read `D.leader ((D.block b).round - 2)`, naming
  the schedule *and* subtracting from a round. It is now
  `ExposesEquivocationBy D b v`, at a validator, with `FPEvidence` reading
  it at the candidate's own author — the same validator wherever the rule
  is used. `lemma4` no longer needs to know that its candidate is a
  leader block at all.
* `ValidHere.leader_clause` privileged the leader two rounds down. It now
  holds at **every** validator: a block whose parents expose `v`'s
  equivocation does not cite `v`. That is a genuine strengthening of the
  paper's rule, and a harmless one — a validator can check it locally,
  and it drops at most the `f` visibly equivocating validators' blocks,
  leaving the `n − f` its quorum needs. Every witness DAG in the arc
  still satisfies it by `decide`, the equivocation witness included,
  which is the empirical check that nothing real was lost.

The same shape as Optimal-Hydrozoan's `LeaderExcludedAll`, and adopted
for the same reason: an invariant that mentions the schedule cannot live
in a universe that a band relates.

**What is left for the band** is the indexing. `Decided` still asks for
`S.slotRound s = s`, which is a statement of what FinWhale's slots are
rather than a restriction, and the band tolerates it — `Banded` only
requires the round shift to match the slot shift. The remaining work is
`Banded` itself over the existential verdict relation: the transported
assignment has to be well formed at *every* round, including below the
band's floor, which is the one place this rule's shape differs from the
other five.

## What completing FinWhale now costs, and why it is not the next thing

The schedule extraction removed the *structural* blocker. What is left is
three properties, and their cost is now measurable rather than unknown.

**`Banded` is a different theorem here from the other five.** Everywhere
else the band is an induction over a *derivation*. FinWhale has none: its
verdicts are a function constrained by `WellFormed`, so the band has to
say that the **reverse pass is band-invariant**. The route is clear and
was worked out before writing any of it:

1. Transport the block-level rules across the band — `slotBlocks`,
   `voters`/`FastCommit`, `parentsVoting`/`SPCertificate`/`SPCommit`,
   `SPSkip`, `NonFPEvidence`, `DirectSkip`, `IndirectCommit`, and
   `FPEvidence` with the novel-candidate clause the other rules also
   needed.
2. Show `decOf` — the pass itself — takes the same verdicts on both
   sides, by downward induction from the finiteness bound. The band's
   `top` is `S.slotRound N` for the assignment's own `N`, so every slot
   the pass reads at or above `k` is inside it.
3. Bridge an arbitrary assignment to the pass with `lemma12`: both are
   well formed on the same view with the same tie-break, so they agree
   wherever both decide.

**`CommitsDirect` is still blocked, and by the last piece of pinning.**
`Decided` asks for `S.slotRound s = s`, and `CommitsDirect`'s direct
predicate never sees the schedule, so that conjunct cannot be discharged.
Removing it means indexing `Verdict`, `WellFormed` and `Anchor` by slot
rather than round — and `Anchor`'s `r + 2 < a` becomes a condition on
slot rounds, which `lemma12`'s downward induction is stated in the
arithmetic of. That is the deep change, and it is what `LeaderCommits`
and `Indirect` would need too.

**So FinWhale is three substantial theorems and one model change away
from the six, and it removes no bespoke link when it gets there** — it
has none. Its value is coverage: evidence that the obligations are right,
tested against the rule least like Mysticeti. That is worth having and it
is not the most urgent thing.

**The most urgent thing is Optimal-Hydrozoan**, which is the only rule
still standing between the development and *every mechanism running on
the properties alone*: eight links, four of them the chop transport that
`LocalTruncate.of_banded` replaces outright.

## FinWhale, slot-indexed: what landed and what is genuinely left

The pinning is gone from `Decided`. FinWhale's rules read the schedule
they are given — `slotBlocks S D k` is the blocks at `S.round k` by
`S.leader k`, `DirectSkip` and `IndirectCommit` read `S.round k + 2`,
`Anchor` is stated at an eligibility rather than at `r + 2 < a`, and
`Run` carries the schedule as `Sched`. `Agree`, `Causal` and
`CommitsCandidate` hold with nothing pinned, and `CommitsDirect` became
**statable**, which it was not before.

### Gaps 1 to 3, closed

**1. The pass enumerated an interval.** `anchorCands` was
`Finset.Ioc (r + 2) N`, so the reverse pass was well formed at one
eligibility and no other. It is now
`(Finset.Iic N).filter (fun a => Elig r a ∧ above a ≠ skip)`, with
`Elig` and `[DecidableRel Elig]` threaded through `anchorVerdict`,
`slotVerdict`, `passFrom` and `decOf`, and `passElig` deleted. The pass
is well formed at whatever eligibility it is handed, given that
eligibility's own `r < a`.

FinWhale's own eligibility is now one definition, `Sched.Elig S r a`,
`S.round r + 3 ≤ S.round a`, sitting in `Model/Rule.lean` beside
`Sched`. The protocol and the carrier run the same pass at the same
relation; under `Run.roundId` it unfolds to the old `r + 2 < a`, which
is `Run.elig_iff`.

**A horizon had to be found, and that was the real content.** A view
bounds *rounds*; the pass recurses down over *slots*; nothing in
`Slots` related the two. `Slots.slot_lt_of_slotRound_le` does:
`keyed` makes `k ↦ (slotRound k, leader k)` injective, `mono` makes the
slots below a round an initial segment, so with `Fintype Validator`
those slots inject into `range (N + 1) ×ˢ univ` and stop below
`(N + 1) * card Validator`. `wellFormed_decOf` accordingly takes two
bounds now — `N` for rounds, `M` for slots, related by
`hrle : ∀ r, S.round r ≤ N → r ≤ M` — and the carrier discharges `hrle`
from that lemma at `viewHorizon`.

**2. Inhabitation, and so non-vacuity of `Agree`, at every schedule.**
`decided_of_directCommit` now takes an arbitrary `Slots` and no side
condition: it exhibits the pass on the view, at `(schedOf S).Elig`, with
horizon `viewHorizon`. `Decided` is inhabited wherever a view directly
commits a block of a slot, so `Agree` is saying something at a general
schedule and not only at the identity one. That was the trap §3.4 and
§3.6 record, and FinWhale is out of it.

**3. `CommitsDirect` holds.** `FinWhaleProperties.DirectCommitIn V L r`
is `L ∈ V ∧ DirectCommit (restrict D V) L`, and `commitsDirect` is
`IsCandidate` placing the block at the slot and
`decided_of_directCommit` reading the commit off the pass. Barnacle's
leader count can therefore be run on FinWhale.

### Gaps 4 and 5, closed

**5. `LeaderCommits` and `Indirect`.** Both fell out of one fact: every
rule FinWhale applies at a slot reads the schedule at *that slot* and
nowhere else. `slotBlocks_congr`, `directSkip_congr`,
`indirectCommit_congr`, `chooseLeast_congr` and the two view versions
say so, and they are what makes a verdict survive a reassignment of
leaders away from the slot — which is the bound both properties carry.

`finWhaleLive` is the liveness precondition, over a slot window:
`CommitsCorrectLeaders` from a coverage round to a horizon, the window
above the round and two rounds under the horizon, and the view holding
the reliable blocks between. Both that interface and `SeesCommits` are
now stated in **rounds** rather than slot indices — `R ≤ S.round s` and
`S.round s + 2 ≤ N` — which is what lets them mean anything at a
schedule that is not the identity, and which took the last `hid` out of
`sees_of_commits_of_held`.

**4. `Banded`.** The theorem no other rule needs, and it needed a lever
first. `eq_of_wellFormed` says two assignments over one validator's
rules agree wherever *either* has decided, and `decided_iff` turns that
into a normal form: a verdict of this rule is the reverse pass's
verdict. `Banded` is then a downward induction on slots with
`LeanDag/FinWhale/Band.lean`'s transport at each step — `Band` restating
`AgreeBand` in the model's vocabulary, then `parentsVoting_eq`,
`fpEvidence_iff`, `exposes_iff`, the forward transports of the commit
rules, `directSkip`, `reaches_of`/`reaches_old`, `indirectCommit_iff`
and `chooseLeast_band`.

Two things came out of it worth keeping. The skip rule quantifies over
the slot's candidates and a band may add one — the defect §3.2 and
§3.12 record — and FinWhale escapes it without repair, because its
blames count against what a block's *parents* reference and an old
block's parents reference only old blocks. And the one case the band
cannot settle, the larger DAG deciding directly what the smaller decided
from an anchor, is FinWhale's own exclusion read inside the larger DAG
alone.

### What the identity assumption is now

It used to be a conjunct of `Decided`, where nothing could discharge it.
Then it was a hypothesis of every theorem that constructs a pass. It is
now a hypothesis of the *protocol* alone — `Run.roundId`, and the
liveness capstones that count rounds — and of nothing in the carrier or
the properties. That is where it belongs: a FinWhale execution runs one
slot per round, and saying so at the execution rather than in the
decision relation is what let the carrier take an arbitrary schedule.

### Where the plan stands

Every rule this plan named is ported. FinWhale shows all six required
properties and `CommitsDirect`; Nemo, Hybrid/Orcaella and Odontoceti
did earlier. **Optimal-Hydrozoan finished last**: it now has `Banded`
too (`OptimalHydrozoan/Carrier.lean`), the eight recorded bespoke links
and the `OptimalChopDecided` inductions a band deletes are gone, and
`scripts/audit-conformance.py` shows all eight rules with carriers
at the six properties. The plan is complete.
