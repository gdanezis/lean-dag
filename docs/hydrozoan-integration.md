# lean-dag — Hydrozoan integration: connecting the arc to the rest

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for connecting the **Hydrozoan** and
**Optimal-Hydrozoan** arcs (`hydrozoan.md`, `optimal-hydrozoan.md`) to
the rest of the development. Both arcs consume nothing from the core:
`grep '^import'` over `LeanDag/Hydrozoan/` and
`LeanDag/OptimalHydrozoan/` returns `Mathlib.*` and nothing else. That
is a deliberate property — `hydrozoan.md` §10 states it, so that the
arc's trusted core is the Hydrozoan paper's model and nothing further —
and its consequence is that the integration arc
(`LeanDag/Integration/`, `integration.md`) does not reach either. The
integration arc names four mechanisms — truncation at a horizon
(`chop`), crash recovery by one message (`skipFill`), the adaptive
leader schedule (`slotsOf`) and the hybrid fault model — and proves
they compose; Hydrozoan appears in none of its statements, and the
novelty budget of `LeanDag/DoS/` does not apply to a Hydrozoan
universe.

The document settles what a connection would require, in what order,
and what the development lacks while the connection does not exist.
Results will carry **HI**-labels. Nothing here is proved yet; §7 is the
work plan.

## 0. Overview

The two developments meet at the three layers `integration.md` §2
names, and the position at each is different.

- **Layer S, the schedule.** Already identical. `LeanDag.Slots`
  (`Mysticeti.lean:310`) and `LeanDag.Hydrozoan.Slots`
  (`Hydrozoan/Model/Slots.lean`) are the same class, field for field:
  `slotRound`, `leader`, `mono`, `unbounded`, `keyed`. `FairRunOn` and
  `SpansEligible` are defined in both. A coercion between the two
  classes is the whole of the work (§1).
- **Layer U, the block universe.** Three mismatches, of which one is
  nominal, one is a missing validity clause, and one is a committee
  condition that is a result in its own right (§2, §3).
- **Layer D, the delivery structure.** Absent from Hydrozoan
  altogether. This is what `hydrozoan.md` §12 defers, and §6 states
  precisely which theorems of the rest of the development are
  unavailable because of it.

Two routes follow from this. The **Barnacle route** (§4) needs none of
layers U or D: `Barnacle.BaseRule` abstracts over the universe type and
requires no `Faults` instance, so Hydrozoan instantiates it with the
frozen `Model/` untouched, and the hardest of its laws is discharged by
HZ3, already proved. The **transformer route** (§5) is where the
committee condition and the missing validity clause are consumed.

One question crosses both routes and is settled in §5.1: Hydrozoan's
direct skip is a count at the slot where the core's is a condition on
candidates, so a slot whose leader published nothing is skipped with no
counting in the core, by a theorem in Optimal-Hydrozoan, and not at all
in Hydrozoan. It decides which of the two variants admits
`integration.md` I9's lifecycle composite.

## 1. Layer S: the schedule coincides

Both classes carry the same five fields, and Hydrozoan's slot
arithmetic — `votingRound k = slotRound k + 1`,
`decisionRound k = slotRound k + 2` — is the core's three-round wave.
`FairRunOn` is `Liveness.lean:731` in the core and
`Hydrozoan/EventualDecision/Statement.lean:49` in the arc, with the
same statement; `SpansEligible` is `Liveness.lean:752` and
`Hydrozoan/IndirectLiveness/Statement.lean:45`.

So **HI1** is a coercion `LeanDag.Slots V → Hydrozoan.Slots V` together
with the two agreements, and every layer-S result of the integration
arc — I3 (`fairRunOn_chop`, `spansEligible_chop`) and I5
(horizon-stability, epoch alignment) — transports across it.
`integration.md` §3.2 predicts this: `Slots.chop` and `slotsOf` are
functions of a `Slots` instance and nothing else, so the layer-S
results hold for a validator running any stack of universe
transformers.

The one substantive question at this layer is not a preservation fact.
Hydrozoan's HZ8 proves the wave-aligned rotation satisfies
`FairRunOn Correct 3` with no premise, and exhibits a per-slot rotation
at `n = 5`, `f = 0`, `c = 2` that starves every correct three-run
inside the hybrid bound (`hydrozoan.md` §11). Barnacle reports a
related failure for its own base protocols: the paper's rotation does
not meet A4 by this development's run-fairness route at two leaders and
four validators (`barnacle.md` §7). The two arcs found the same class
of defect in leader rotation independently, and a connected development
should state the relation between the two counterexamples.

## 2. Layer U: the fault models agree, and the committee bound does not

`HybridFaults.toFaults` (`Hybrid/Faults.lean:74`) sets
`f := fb + fc` and `byzantine := byzantine ∪ crash`, so the base quorum
is `n − fb − fc` and the base `Correct` is the fully-correct class.
Under `fb := f`, `fc := c` this is Hydrozoan's model exactly:

| | Hydrozoan | `HybridFaults.toFaults` |
|:---|:---|:---|
| quorum | `q = n − f − c` | `quorumCard = n − fb − fc` |
| `Correct` | `(byzantine ∪ crashed)ᶜ` | `(byzantine ∪ crash)ᶜ` |
| never-equivocating class | `NonByzantine = byzantineᶜ` | the honest class |

The agreement extends to the universe. `HonestNoEquiv` — the hybrid
arc's one genuinely new invariant, U5 of `integration.md` §2.1, and the
predicate Barnacle's Orcaella instantiation carries a subtype for — is
Hydrozoan's `no_equivocation` field, stated at `NonByzantine` inside
the structure (`Hydrozoan/Model/BlockUniverse.lean:54`). A Hydrozoan
universe needs no subtype, which is one condition fewer than Orcaella
carries.

**The committee bounds are incomparable.** `HybridFaults` requires
`3 · (fb + fc) + 1 ≤ n` (`Hybrid/Faults.lean:64`), that is
`3f + 3c + 1 ≤ n`; Hydrozoan requires `3f + 2c + k + 1 ≤ n`
(`Hydrozoan/Model/Faults.lean:57`). The projection is therefore
available exactly under

    c ≤ k

and not otherwise: at `n = 8`, `f = 1`, `c = 2`, `k = 0` Hydrozoan's
bound reads `3 + 4 + 0 + 1 ≤ 8` and holds, while the hybrid bound reads
`3 · 3 + 1 ≤ 8` and fails.

The gap is not slack in either class; it is the difference between the
two intersection arguments. Two sets of `q = n − f − c` authors
intersect in at least `n − 2f − 2c`.

- Hydrozoan's uniqueness arguments need one member of that intersection
  outside `byzantine`, of which there are at most `f`, so they need
  `n − 2f − 2c ≥ f + 1`, that is `n ≥ 3f + 2c + 1`. The committee bound
  supplies this with `k` to spare.
- The core's T0 (`exists_correct_mem_inter`, `Validators.lean:179`)
  concludes a member of `Correct`, which for the derived instance
  excludes `byzantine ∪ crashed`, of which there are at most `f + c`.
  It therefore needs `n − 2f − 2c ≥ f + c + 1`, that is
  `n ≥ 3f + 3c + 1`.

So Hydrozoan admits committees below the core's because it never asks
for the stronger intersection: a crashed replica does not equivocate,
and every Hydrozoan uniqueness argument counts `NonByzantine` rather
than `Correct`. **HI2** states the projection under `c ≤ k` and
refutes it without, and the refutation is the informative half —
a deployment at `k < c` can run Hydrozoan and cannot run the core's
transformers over it.

### 2.1 The committee specialises to five of the arcs

The `(f, c, k)` space names most of the committees in this repository,
and the Optimal variant is the one that reaches them all:

| arc | as `(f, c, k)` | committee | quorum, or fast threshold |
|:---|:---|:---|:---|
| Mysticeti | `c = 0`, `k = 0` | `n ≥ 3f + 1` | `q = n − f` |
| Odontoceti | `c = 0`, `k = 2f` | `n ≥ 5f + 1` | `qFast = n − f` |
| Orcaella | `f = fb`, `c = fc`, `k = 2fb + fc` | `n ≥ 5fb + 3fc + 1` | `qFast = n − fb − fc` |
| Nemo-Nemo | `f = 0`, `c` the crash bound, `k = 0` | `n ≥ 2c + 1` | `q = c + 1`, the majority |
| FinWhale | **Optimal**, `c = 0`, `k = 2p − 2` | `n ≥ 3f + 2p − 1` | `qFastOpt = n − p` |

The last row separates the two variants. At `c = 0` Hydrozoan has
`p = ⌊k/2⌋`, so an allowance of `p` requires `k = 2p` and a committee
of `3f + 2p + 1` — two replicas above FinWhale's. Optimal's
`pOpt = ⌊k/2⌋ + 1` reaches the allowance at `k = 2p − 2` and lands on
`n ≥ 3f + 2p − 1` exactly, which follows from
`optimal-hydrozoan.md`'s own account: the device is FinWhale's.
FinWhale's `1 ≤ p ≤ f` supplies `OptimalFaults`'s standing assumption
`1 ≤ f + c` on that row.

Two arcs lie outside the space. Mahi-Mahi's parameter is the wave
length `w ≥ 3`, and Hydrozoan fixes the wave at three
(`votingRound k = slotRound k + 1`, `decisionRound k = slotRound k + 2`);
Black Marlin and Minnow are different rules rather than different
thresholds.

**The specialisation is of the thresholds and never of the rule**, and
§9 records why the converse route — deriving those arcs from
Optimal-Hydrozoan — is not taken.

## 3. Layer U: the self-parent clause is absent

The core's `ValidWrt` (`Block.lean:67`) has four fields; Hydrozoan's
(`Hydrozoan/Model/Block.lean:79`) has three. The missing one is
`self_parent`, P3′: a non-genesis block references a block by its own
author.

P3′ is what `DoS/SelfParent.lean`, `DoS/Pedigree.lean` and
`DoS/Novelty.lean` rest on, what `fillBlock` is obliged to insert, and
what `no_blocks_of_no_genesis` descends (`integration.md` §3.2, I8).
Without it, four integration results have no Hydrozoan analogue, and
the reason is structural rather than technical:

- **I8, I10, I11, I12** concern a validator whose self-parent chain has
  been severed by a horizon. In a universe without P3′ a validator with
  no block in the genesis layer can still produce, so severance is not
  a condition that arises and re-genesis repairs nothing.
- **I13, I14, I15** rest on a causal cone being a complete record of
  its author's acceptances, which is what P3′ supplies. The novelty
  budget of `LeanDag/DoS/` therefore does not apply to a Hydrozoan
  universe at all, independently of the delivery layer (§6).

The first of those two is not only a loss. Because nothing chains a
block to its author's previous one, a replica pruned past its whole
history can resume by building a block referencing `q` current blocks.
There is no severed chain, so **Hydrozoan needs no re-genesis for an
outage longer than the garbage-collection lag**: I8 and I10 to I12
have no analogue because the condition they repair does not arise, not
because the machinery for it is missing. The absent clause therefore
removes a recovery mechanism from the plan at the same time as it
removes the storage arc from reach.

The property holds of the deployed protocol — a Mysticeti block carries
its author's previous block — so the situation is that the Hydrozoan
model omits a clause the implementation has, because the paper's
argument never consumes it. Recording that is the first part of
**HI8**.

The second part is a choice, and it should be made deliberately. Adding
a fourth field to `Hydrozoan/Model/Block.lean` modifies a frozen
audited file, and every witness universe in `LeanDagTest/Hydrozoan/`
would need self-parent edges added, which changes the author counts
those `decide` witnesses pin. Defining `SelfParenting U : Prop`
alongside and conditioning the transformer results on it modifies
nothing and leaves the arc's statements as they are. `integration.md`
§4.2 sets the rule that decides this: modify existing code only when a
result cannot otherwise be stated. A side predicate states every
result, so the side predicate is the route, and the frozen file stays
frozen.

## 4. Route A: Hydrozoan as a Barnacle base rule

`Barnacle.BaseRule` (`Barnacle/Model/Rule.lean:58`) abstracts over the
universe type itself — `Universe : Type`, `View : Universe → Type`,
`block`, `ids`, `viewIds`, `full`, `historyView`, `waveLength`,
`DirectCommitIn`, `decDirect`, `Decided` — and takes **no `Faults`
instance**. Orcaella's instantiation states the principle: the fault
class lives on the instantiation, never on the interface. Neither the
committee condition of §2 nor the validity clause of §3 arises on this
route.

What **HI4** requires:

| obligation | source |
|:---|:---|
| `block`, `ids`, `viewIds`, `full` | Hydrozoan's `BlockUniverse`, `View`, `View.full` |
| `view_subset`, `view_complete`, `full_ids` | `View.subset_ids`, `View.complete`, `View.full`, verbatim |
| `agree` | **HZ3 `SlotAgreement.holds`**, already proved |
| `decided_of_directCommitIn`, `candidates` | the `Decided` constructors, which carry `IsLeaderBlock` |
| `decDirect` | `FastCommit` and `SlowCommit` are `Finset.card` comparisons |
| `historyView_ids` | **HI3**, below |

**HI3** is the block adapter and one lemma. The interface's `block`
field returns `LeanDag.Block Validator BlockId Payload`, so the
instantiation needs
`Hydrozoan.Block Replica BlockId → LeanDag.Block Replica BlockId Unit`,
mapping `author` to `creator` and `parents` to `refs`. It is used only
at the interface boundary; no file under `LeanDag/Hydrozoan/` changes.
The lemma is that `Hydrozoan.Reaches`
(`Relation.ReflTransGen (RefStep U)`,
`Hydrozoan/Model/CausalHistory.lean:37`) agrees with
`Causality.historyFrom` (`Causality.lean:190`) across the adapter.

One design decision is genuine rather than mechanical. `waveLength` is
the number of rounds the direct rule reads from a slot's proposal, and
Hydrozoan has two direct commit routes at different depths: the fast
path reads rounds `r` and `r + 1`, the slow path reads `r`, `r + 1` and
`r + 2`. Setting `waveLength := 3` with
`DirectCommitIn V L r := FastCommitInView … ∨ SlowCommitInView …` is
sound, and it makes the leader-count mechanism treat a fast commit as
occupying a three-round window when it occupies two. Whether the AIMD
signal should distinguish the two routes is a question for the
instantiation, not for the interface, and it should be settled before
the statement is frozen.

**HI5** is the liveness half, and it has three parts rather than two.
`Barnacle.LiveRule` (`Barnacle/Model/Live.lean`) extends `BaseRule`
with `Good : Universe → ℕ → ℕ → Prop`, the rule's own notion of a good
DAG, and `LiveOn S c` concludes on a view satisfying
`BaseRule.CoversUpto`. Hydrozoan's liveness package instantiates `Good`
directly — a quorum-sized `T ⊆ Correct` with `SynchronisedOn U T Rnd`
and `PopulatedOn U T r` through the horizon — and HZ5 and HZ7 conclude
on `View.CoversUpto`, which is the same interface. The commit gap `c`
is what HZ7 supplies through `FairRunOn` and `RunsRecur`.

The third part is `LiveRule.Descent slack` (`Barnacle/Model/Heads.lean:42`),
which Orcaella carries at `slack = fb + fc`. Hydrozoan is shaped for it
at `slack = f + c`:

- `goodLeaders` asks for a set `T` with
  `Fintype.card Validator ≤ T.card + slack`, which at `slack = f + c`
  is `T.card ≥ n − f − c = q` — HZ5's own premise.
- `indirect` at `waveLength = 3` reads `S.slotRound i + 3 ≤ S.slotRound j`,
  which is `EligibleAsAnchor Replica i j` — slot `j`'s propose round
  strictly past slot `i`'s decision round — and its conclusion is HZ6's
  `AnchoredTotality`.

`goodLeaders` quantifies over every schedule *inside* the existential
for `T`, so `Good U Rnd N` must supply `PopulatedOn U T r` at every
round of the window rather than at slot rounds alone. That is the
reading "good from `Rnd` to `N`" should have in any case, and it is how
the statement should be written.

`Descent.goodLeaders` produces one `T` per good DAG, and Hydrozoan's
`SynchronisedOn U T Rnd` fixes one `T` from `Rnd` on, so a replica
absent for part of the window is outside `T` for all of it. This is the
core's own shape — `Liveness.lean:229` fixes `T` and `R` the same way —
and §5.2 states how the fill and the two arcs' results divide the
window rather than widen `T`.

**The health signal reads Hydrozoan's crash class as unhealthy.**
`SlotDirect` (`Barnacle/Model/Window.lean:55`) counts slots with a
direct *commit*, and `expected = (interval − waveLength + 1) * m`
counts a window in which every scoring slot commits. Barnacle records
the limitation already: `Healthy/Statement.lean` states that a good DAG
does not make a window healthy, since slots led by validators outside
the good set do not commit in any case. Under Hydrozoan the statement
is sharper rather than new — with `c ≥ 1` crashed replicas holding
slots, `WindowHealthy` is unreachable and BN12 says nothing about such
a deployment. So the Barnacle route yields Agreement and Ledger in
full, and the health results only as far as Barnacle's own hold: the
useful Hydrozoan form is the partial count that
`Barnacle/Healthy/Statement.lean` names as the next result and does not
prove.

**HI6** repeats HI4 and HI5 for Optimal-Hydrozoan over `DecidedOpt`,
with OH3 discharging `agree`. Its evidence rung needs no tie-break
(`optimal-hydrozoan.md` §7), so the instantiation requires no
`LinearOrder` on ids where Hydrozoan's does.

For scale: Orcaella's instantiation is 120 lines of statement and 38 of
proof. Hydrozoan's should be comparable, plus HI3.

The outcome of this route is that Hydrozoan and Optimal-Hydrozoan
become the fifth and sixth base rules under the adaptive leader count,
beside Mysticeti, Odontoceti, Nemo-Nemo and Orcaella, with no frozen
file modified.

## 5. Route B: the universe transformers

`chop` (`GC/Chop.lean:92`) is generic over
`BlockUniverse Validator BlockId Payload` and would apply to a
Hydrozoan universe under the adapter of §4, with a validity obligation
one field smaller than the core's. Its verdict-invariance companion is
the real work.

**HI7** is `decided_chop` for Hydrozoan's `Decided`. The core's version
(`GC/ChopDecided.lean:214`) is a biconditional proved by structural
induction under a single premise, `hd : G ≤ S.slotRound d`, with
anchors and intermediate slots re-indexed by the base slot `d` and the
schedule replaced by `Slots.chop S G d hd`. Hydrozoan's relation has
six constructors (`Hydrozoan/Model/Decided.lean:45`) and
Optimal-Hydrozoan's another six.

Three of the six are direct and should be routine: `directFast`,
`directSlow` and `directSkip` count authors at rounds `r + 1` and
`r + 2`, all above the cut under the base-slot premise, so the view
filter is invisible to them, which is the argument the core's
`DirectCommitIn` and `DirectSkipIn` cases already make.

The three indirect constructors carry negative premises — `indirectWeak`
fires only when no candidate has an anchor-linked certificate, and
`indirectSkip` only when both rungs are empty for every candidate — and
removing blocks does not preserve a negative premise in general.
Under the base-slot premise it should nonetheless transport:
`chop` empties `refs` only at the base layer, so `Reaches` is preserved
for targets at rounds at or above `G`, and with
`G ≤ S.slotRound d ≤ S.slotRound k` every certificate and every vote
the rungs inspect sits above the cut. The obligation to predict is a
different one — `EligibleAsAnchor` re-indexes as
`S.slotRound j − G > S.slotRound k + 2 − G`, and `integration.md` §3.4
records that truncated subtraction is faithful only above the cut, paid
three times so far and discharged each time by a hypothesis already in
scope. Monotonicity of `slotRound` from the base slot supplies it here,
and this would be the fourth.

### 5.1 The fill, and where the two protocols separate

**HI9** is `skipFill` over both rules, and the two do not behave alike.

SS3 concludes that a filled leader candidate is **directly skipped**
(`SafeSkip/Basic.lean:39`), because no old block references a fresh
identifier. Hydrozoan's direct skip needs `qFast = n − p` blames, and
the supply a quorum of correct replicas guarantees is `q = n − f − c`.
The conclusion therefore requires `n − p ≤ n − f − c`, that is
`f + c ≤ p`, which is the condition under which Hydrozoan's direct skip
fires at all and which `hydrozoan.md` §7 keeps outside the liveness
claim for that reason. **SS3 does not transfer to Hydrozoan.**

What transfers is SS5, `decided_fill_agree`. A filled candidate carries
no votes, so it reaches neither `qFast` nor `qSlow` nor either rung, and
no commit verdict appears; and a blame is a voting-round block
referencing *no* candidate of the slot, so every blame that existed
before the fill still counts. The verdict a replica reached before the
fill re-derives after it, which is the statement Hydrozoan supports.

**Optimal-Hydrozoan does obtain SS3.** Its skip is `qCert` blames
together with a `NoEvidenceQuorum`, both at `qCert ≤ q`, and the
no-evidence half holds of a filled candidate: `votesFor U C L` is empty,
while `EvidencePlain` gives `1 ≤ tPlain` and `tEquiv = f + pOpt` is at
least one, so no decision-round block is fast evidence for it. This is
the same separation `optimal-hydrozoan.md` D5 records between an
opportunistic and a guaranteed skip, arriving through a mechanism
neither arc considered.

It also forces a hypothesis weakening, of the shape `integration.md` I9
describes. `SkipLiveness` is stated with `∀ L, ¬ IsLeaderBlock U k L` —
the slot has no candidate at all — and a filled slot has one. What the
proof consumes is only that no candidate reaches `tPlain` votes, which
the filled candidate satisfies. So the composite is unstatable until
`SkipLiveness`'s hypothesis is weakened to the fact it stands for,
which is the act `integration.md` §4.2 permits and a refactor is not.

**The same split decides the lifecycle composite, and there it matters
more.** `integration.md` I9's `lifecycle` (`Integration/Lifecycle.lean:117`)
concludes three things at once: the halted leader's slot is skipped,
the fill restores production with the recovered validator in the set,
and honest non-equivocation survives. The second and third transport —
`skipFill_populatedOn` counts blocks, and Hydrozoan's
`no_equivocation` field is what `honestNoEquiv_skipFill` re-establishes.
The first divides the same way §5.1 does, and for a reason recorded
elsewhere in this development.

The core's L5 needs no counting at all. `Decided.directSkip` takes
`∀ L, IsLeaderBlock U k L → …`, a premise over candidates, so a leader
that published nothing satisfies it vacuously
(`Liveness.lean:623`). Hydrozoan's `Decided.directSkip` takes
`SkippedLeaderInView`, which is `qFast ≤ (blamesInView …).card` — a
count at the slot, not a condition on candidates — and `qFast` blames
are not available. Optimal-Hydrozoan's is a count too, but OH5 proves
it from population alone.

| conjunct | core | Hydrozoan | Optimal-Hydrozoan |
|:---|:---|:---|:---|
| the halted leader's slot is skipped | no counting | needs `qFast` blames | OH5, from population |
| the fill restores production | SS2 | transports | transports |
| non-equivocation survives | I1 | transports | transports |

`mahi-mahi.md` reports the same distinction as a finding against the
core — the per-candidate skip rule is weaker than the implementation's
slot blame — and it is what decides here which of the two variants
admits the composite.

### 5.2 The recovered replica, and which window readmits it

`hydrozoan.md` §12 records that `T` is fixed across a synchrony suffix,
so a replica that rejoins **by jumping to the frontier round** — that
is, authoring nothing for the rounds it missed — sits outside `T`
permanently, and names a wave-scoped `SynchronisedAt` as the repair.
Safe Skip is the mechanism that makes jumping unnecessary: the replica
fills the rounds instead of skipping them. So HI9 addresses that item
rather than inheriting it, and the repair `hydrozoan.md` §12 names is
not a prerequisite for anything in §7.

The fill readmits the replica to the two invariants at different
points, and the division is `integration.md` I4's, unchanged:

- **Production, across the gap.** `skipFill_populatedOn` puts a block
  at every filled round, so `PopulatedOn` holds for a set containing
  the recovered replica at rounds during which it was absent. This is
  the restoration `lifecycle` claims, and it transports to Hydrozoan
  by counting.
- **Coverage, strictly above the fill.** `SynchronisedOn` is refuted
  for any set containing the recovered replica at its gap rounds, since
  no block built during the outage references an identifier that did
  not then exist, and it returns above the fill
  (`synchronisedOn_skipFill_above`). A window whose `Rnd` lies above
  the fill therefore has the replica inside `T`.

Neither point is Hydrozoan-specific. The core fixes `T` and `R` the
same way (`Liveness.lean:229`), and `lifecycle` claims restoration to
the populated set and does not mention coverage at all. What Hydrozoan
lacks relative to the core is the first conjunct of that theorem, for
the reason §5.1 gives, and nothing else.

### 5.3 The novelty budget is two layers away

The budget is behind **HI8** and, for its own statement, behind
the delivery layer: `DoSValid` is a layer-U predicate and needs the
self-parent clause, while `UniformBudget` and `RefsAccepted` range over
`Delivery U`. Both together are not sufficient either —
`integration.md` I16 found `RefsAccepted` refuted under the fill in the
core, and the refutation describes Safe Skip rather than the
transformer, so the same result and the same unsettled modelling choice
about what a `Delivery` records should be expected here.

## 6. Route C: the delivery layer, and what its absence costs

Hydrozoan has no `Delivery`, no `ViewPace`, no time index. This is
declared out of scope by `hydrozoan.md` §12, and the declaration is
defensible: HZ8 proves the liveness hypotheses satisfiable at every
horizon, so nothing above them is vacuous. The following is what the
development lacks while the layer does not exist, and it is stated here
so that the deferral is a known position rather than an unexamined one.

**The two-message-delay claim cannot be stated.** Hydrozoan's principal
claim is that the fast path commits in two message delays where the
slow path takes three. `FastLatency` states this in rounds, and rounds
are not message delays. The theorem that relates the two exists in this
development, for the arc closest to Hydrozoan in structure —
`FinWhale.fastCommit_latency` (`FinWhale/Reactive.lean:132`) concludes

    FastCommit D L ∧
      ∀ v ∈ T, rc.built v (S.slotRound k + 1)
        ≤ rc.built v (S.slotRound k) + rc.delay + δ + 2 * rc.proc

under `δ`-propagation past GST and at most `p` actual faults, with the
timeout appearing nowhere, and `no_timeout_of_fast` beside it states
that the fallback branch of the vote rule is dead where delivery beats
the timeout. Its fault hypothesis has the same shape as Hydrozoan's
`FastLatency` premise, and the bound is proved for any protocol on the
reactive schedule. Hydrozoan has no structure to state it over.

**`PopulatedOn` and `SynchronisedOn` remain hypotheses where the core
has theorems.** In the core both are derived: `ViewPace.populatedOn`
(`ViewPace.lean:538`) and `ViewPace.synchronisedOn_of_converges`
(`ViewPace.lean:594`), from one network clause `converges` — whatever a
correct validator holds reaches every correct validator within `delay`
past `gst` — together with two protocol clauses, `references` (P7) and
`waits` (P9, the waiting rule). The step Hydrozoan defers is
`covers_of_converges` (`ViewPace.lean:482`), which the core proves from
`converges` and `references` alone.

Hydrozoan's `Model/Liveness.lean` names the same derivation as future
work in the same terms: what makes coverage true of the deployed system
is the protocol's waiting rule, a replica building a full timeout after
entering a round rather than on the first quorum it holds, together
with timely post-stabilization delivery. So the audit surface
`hydrozoan.md` §7 identifies stays at two assumed structural
predicates, where the core's is one clause about views.

**There is no threshold a deployment can evaluate.**
`commits_recur_local` (`ViewPace.lean:689`) consumes
`2 * vp.delay + vp.proc ≤ vp.timeout n`, in which no quantity set by
the deployment appears, because the pacemaker's catch-up rule collapses
any clock spread to `delay + proc` in one post-stabilisation round.
Hydrozoan has no `delay`, no `proc`, no `timeout` and no clock, so
nothing in the arc tells an operator how to configure the timeout. The
reference implementation is in `asonnino/mysticeti`, which is where
this absence has the most direct consequence.

**Liveness is local in the view but not in time.** HZ5 and HZ7 conclude
on any view satisfying `View.CoversUpto (slotRound k + 2)`, which is a
genuine localisation and stronger than a whole-universe reading. What
is missing is a statement of when a replica's view satisfies it. The
core names the instant:
`vp.viewAt v (vp.latest (S.slotRound k' + 2) + vp.delay)`.

**The storage line is unavailable for a second, independent reason.**
`UniformBudget` and `RefsAccepted` range over `Delivery U`, and
`dos_resistance_of_pace` (`PaceDelivery.lean:205`) concludes liveness
and linear storage from one structure. One part of that line would
transport: `heldOf_inj` (`PaceDelivery.lean:92`) derives the acceptance
rule — at most one block per author, held — from P7 and P2 rather than
postulating it, and Hydrozoan's `ValidWrt.distinct_authors` is P2. What
would not transport is everything indexed by a `Delivery` the arc does
not have.

**Round-jumping recovery stays unmodelled.** `hydrozoan.md` §12 records
that `T` is fixed across a synchrony suffix, so a replica rejoining by
jumping to the frontier round sits outside `T` permanently. The core's
answers are `LeanDag/SafeSkip/` and a wave-scoped refinement of
`SynchronisedOn`; neither is available.

**What the layer would not change.** `synchronisedOn_of_converges`
concludes `SynchronisedOn U T R`, a statement about the DAG that never
mentions `Decided`. The delivery layer's output is therefore
rule-independent, and **HI10** is a port of `ViewPace` to
`Hydrozoan.BlockUniverse` rather than a re-proof of anything above it:
HZ5, HZ6 and HZ7 would stand unchanged with their hypotheses discharged
instead of assumed. The rule-specific remainder is small — re-deriving
`decided_local` for the dual-path rule, which amounts to naming the
instant at which a replica's view holds `qFast` votes or `qSlow`
certificates — and `View.CoversUpto` is already the interface for that
step.

## 7. The results, and the order

| | Result | Depends on |
|:---|:---|:---|
| HI1 | the schedule coercion; `FairRunOn` and `SpansEligible` agree | — |
| HI2 | the fault projection under `c ≤ k`, refuted without it | — |
| HI3 | the block adapter; `Reaches` agrees with `historyFrom` | — |
| HI4 | Hydrozoan as a `Barnacle.BaseRule` with its `Laws` | HI1, HI3, HZ3 |
| HI5 | as a `Barnacle.LiveRule`: `Good`, `LiveOn`, `Descent` at `f + c` | HI4, HZ5–HZ7 |
| HI6 | HI4 and HI5 for Optimal-Hydrozoan | HI4, HI5, OH3, OH5 |
| HI7 | `decided_chop` for `Decided` and `DecidedOpt` | HI1, HI2, HI3 |
| HI8 | the self-parent predicate, stated beside the frozen `ValidWrt` | — |
| HI9 | the fill: verdict agreement for both rules; SS3 for Optimal alone | HI7, HI8 |
| HI10 | the delivery layer | HI3 |

The order is HI1–HI3, then HI4–HI6, then HI7, then HI8 and HI9, then
HI10.

HI1 to HI6 modify no existing file and are the substantive part: they
place Hydrozoan and Optimal-Hydrozoan under the adaptive leader count
and state the exact committee condition under which the rest of the
core applies to them. HI2 is publishable on its own — it says what
Hydrozoan's committee admits that the core's does not, and the witness
at `n = 8`, `f = 1`, `c = 2`, `k = 0` is a `decide` obligation.

HI7 is the largest single proof obligation, six constructors in each of
two decision relations. HI9 is where the two protocols separate (§5.1),
where the weakening of `SkipLiveness` falls due, and where the
lifecycle composite is available for Optimal-Hydrozoan and not for
Hydrozoan. HI10 is larger than everything above it.

**No result here modifies a frozen file.** The one weakening the plan
predicts is to Optimal-Hydrozoan's `SkipLiveness` (§5.1), which is a
statement rather than a `Model/` definition, and is conservative in the
sense `integration.md` §4.2 requires. `hydrozoan.md` §12's wave-scoped
`SynchronisedAt` is **not** a prerequisite for anything above: §5.2
gives the reason.

## 8. Findings anticipated

Recorded before the work, so that the record distinguishes what was
predicted from what was discovered.

- **Hydrozoan's committee is genuinely weaker than the core's for
  `k < c`.** §2 derives both bounds from the same intersection and
  locates the difference in the pool each argument counts. The
  expectation is that `c ≤ k` is exactly the condition, and that
  nothing in the transformer arcs weakens it, since T0 is consumed
  everywhere.
- **The self-parent clause is a fidelity gap of the Hydrozoan model,
  not of the protocol.** §3. The expectation is that adding it to
  `ValidWrt` would be sound and that no Hydrozoan theorem consumes it,
  which is why it was omitted; the side-predicate route tests this
  without modifying the frozen file.
- **Two arcs found the same defect in leader rotation.** §1. The
  expectation is that Hydrozoan's `n = 5`, `f = 0`, `c = 2`
  counterexample and Barnacle's two-leader four-validator one are
  instances of one pigeonhole statement about run-fairness under
  rotation, and that stating it once would serve both.
- **The graded indirect rule may constrain where a horizon may fall.**
  §5. The rungs' negative premises are not preserved by removing
  blocks in general, and the base-slot premise may not be sufficient.
  If a further condition is needed it is a placement condition, in the
  category `integration.md` §4.1 names as the integration arc's most
  usable output.
- **The fill separates the two protocols, and the separation is the
  one `optimal-hydrozoan.md` already reports.** §5.1. Hydrozoan's
  direct skip of a filled candidate requires `f + c ≤ p`, so SS3 holds
  for Optimal-Hydrozoan and not for Hydrozoan, and the composite for
  Hydrozoan is verdict agreement rather than a direct skip. The
  expectation is that this is D5's opportunistic-versus-guaranteed skip
  reached by a route neither arc considered, and that it is the first
  place where the Optimal variant composes better than the protocol it
  varies.
- **The composite will require weakening `SkipLiveness`.** §5.1. Its
  candidate-less hypothesis is stronger than its proof consumes, which
  needs only that no candidate reaches `tPlain` votes. The expectation
  is a one-field weakening of the shape `integration.md` I9 performed
  on `SkipMsg`, strictly conservative, with the Hydrozoan-side route
  recovering the old form.
- **Safe Skip answers `hydrozoan.md` §12's round-jumping item rather
  than inheriting it.** §5.2. The item is about a replica that rejoins
  by authoring nothing for the rounds it missed; the fill authors them.
  The expectation is that production is readmitted across the gap and
  coverage above the fill, by `integration.md` I4's division unchanged,
  and that the wave-scoped `SynchronisedAt` is needed for neither.
- **The absent self-parent clause removes a recovery mechanism as well
  as the storage arc.** §3. Without a chain to sever, a replica pruned
  past its own history can resume unaided. The expectation is that I8
  and I10 to I12 have no Hydrozoan analogue because their premise is
  unsatisfiable there, which is a stronger statement than their being
  unavailable.
- **Barnacle's health results say nothing about a Hydrozoan deployment
  with crashed replicas holding slots.** §4. `WindowHealthy` asks every
  scoring slot to commit directly, which `c ≥ 1` prevents under a
  schedule that gives crashed replicas slots. The expectation is that
  this is an instance of the limitation `Barnacle/Healthy/Statement.lean`
  already records rather than a defect of the instantiation, and that
  the partial count Barnacle names as its next result is what a
  Hydrozoan deployment would need.

## 9. Out of scope

- **Executions**, as for every other arc: composition here is
  composition of structural conditions, and nothing about the order in
  which mechanisms fire is modelled.
- **The decision-relation interface** of `integration.md` §3.6, which
  that arc moved out as a refactor of working code. Two reasons hold
  here independently of that one. Barnacle's `BaseRule` already
  supplies an interface at the level HI4 needs, and instantiating it is
  additive; and no interface of that shape can carry HI7, because
  `BaseRule.Decided` is a record field with no constructors and `Laws`
  exposes only consumers of it — `agree`,
  `decided_of_directCommitIn`, `candidates` — while `decided_chop` is a
  structural induction over derivations
  (`GC/ChopDecided.lean:32`). An interface abstracts the uses of a
  decision relation and not inductions over it, so the per-rule
  obligation survives any amount of abstraction.
- **Deriving the other arcs as special cases of Optimal-Hydrozoan.**
  §2.1's table is of committees and thresholds; the rules themselves
  differ in kind. The core's `Decided` carries four constructors to
  Hydrozoan's six, its direct skip is a condition on candidates where
  Hydrozoan's is a count at the slot, and at `c = k = 0` neither
  relation contains the other — `qFast = n` and `qWeak = f + 1` leave
  `directFast` and `indirectWeak` derivable rather than removing them.
  A specialisation would therefore be a bisimulation per arc, over
  relations already proved, witnessed and pinned to their axiom lists,
  and would yield no statement §7 does not already have.
- **Everything Hydrozoan leaves out** (`hydrozoan.md` §12): delivery,
  GST, weak links, the depth-first reading of a vote, round-jumping
  recovery. HI10 addresses the first two and nothing else on that
  list; §5.2 records round-jumping recovery as answered by HI9, since
  the fill authors the rounds a jump would leave empty.
- **The certified variant, and cryptography.**
