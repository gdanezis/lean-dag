# Black Marlin: the commit rule

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

The design record for `LeanDag/BlackMarlin/`: the commit rule of *DAG it
off: Latency Prefers No Common Coins* (Amores-Sesar, Grøndal, Holmgård
and Ottendal, arXiv:2508.14716v3): its safety, its liveness, the round
rule it advances on, Definition 1's Agreement, and the order its
deliveries come out in.

## 1. The protocol, and what this arc covers

Black Marlin is a partially synchronous DAG protocol at `n ≥ 3f + 1`
with neither reliable broadcast nor a common coin. It elects one
**anchor** per round by round robin, and it commits three rounds after
proposal. A round advances when a validator holds blocks from `n − f`
parties, has the anchor of the round, and sees the two anchors below it
supported; a timeout supplies the second disjunct when an anchor is
Byzantine, which is what keeps the protocol responsive.

This arc covers the commit rule of `delivery(r)` (Algorithm 1, L14–L17)
with §5.1's safety results (§4), liveness above the structural condition
in place of §5.2's timing argument (§8), the round rule of L38–L41 and
the responsiveness it yields (§9), Definition 1's Agreement (§10), and
the order the descent of `commit` delivers in (§11, §12), a
refutation of Definition 1's Agreement (§13), and a repair tested as a
side-condition (§14). §15 says what remains.

## 2. The rule

Write `supp(B)` for the number of distinct validators whose block at
round `round(B) + 1` references `B`. The anchor `B` of round `r` is
committed when

1. `supp(B) ≥ n − f`, and
2. some anchor `B′` of round `r + 1` references `B` and has
   `supp(B′) ≥ n − f`.

In the source these are `Supported U L r` and `Linked U L r`, and their
conjunction with `IsAnchor U r L` is `Committed U L r`
(`LeanDag/BlackMarlin/Model/Rules.lean`). No threshold above `n − f`
appears, and no certificate round: the second clause is what the other
protocols of this repository obtain from a certificate.

`supp` is the core's `supporters`, which counts authors rather than
blocks. The paper's side condition on `supp` excludes a supporter whose
**cone** holds a second block of `B`'s author and round, not merely one
whose references do. The two coincide, and the reason is a fact about
the model rather than a modelling choice: a reference sits exactly one
round below its referrer, so the round-`r` members of a round-`(r+1)`
block's cone are exactly its references, and the condition reduces to
the core's `ValidWrt.distinct_creators`.

`Linked` is a `Finset` of witnesses rather than a bare existential, so
that the rule is decidable on a concrete DAG. The rotation is a class
`Rotation` with one field, `anchor : ℕ → Validator`, rather than the
core's `Slots`: the protocol is indexed by rounds, and every clause
above names round `r + 1` explicitly, which under `Slots` would be a
hypothesis `slotRound (k + 1) = slotRound k + 1` carried through every
statement. §4 reconciles the two.

## 3. The rule as a validator applies it

`delivery(r)` runs against one validator's `DAG`, so each count is taken
over the blocks that validator holds: `SupportedIn`, `LinkedIn` and
`CommittedIn` are the definitions of §2 with each block set intersected
against a `View` (`LeanDag/BlackMarlin/Model/Decision.lean`).

There is no decision relation. Mysticeti and Odontoceti carry one
because a slot may be **skipped**, and a skip has to be derived through
an anchor. Black Marlin has no skip verdict and no indirect rule: an
anchor the rule does not admit is delivered, in its turn, inside the
causal history of a later anchor that the rule does admit. So the whole
of what a validator decides is `CommittedIn`, and agreement is the
statement that two validators' committed anchors lie on one chain.

`IsAnchor` is not relativised. Which validator anchors a round is a
schedule fact rather than an observation, and that the block exists at
all follows from the view holding a block that references it — which is
the second conjunct of BM4.

## 4. The results

Seven claims, stated in `LeanDag/BlackMarlin/Safety/Statement.lean` and
proved in the neighbouring `Proof.lean`. None assumes synchrony, a
global stabilisation time, or any bound beyond `n ≥ 3f + 1`; as in the
paper, they hold during the asynchronous period as well.

| | Claim | Paper |
|:---|:---|:---|
| BM1 | `AnchorUniqueness` — two supported anchors of one round are one block | Lemma 3 |
| BM2 | `Propagation` — a supported block is in the causal history of every block two rounds above | Lemma 5 |
| BM3 | `Density` — below the highest round, every round carries a quorum of authors | Lemma 4 |
| BM4 | `ViewSound` — a view's verdict is the universe's, and the view holds the block | — |
| BM5 | `Chained` — two committed anchors are one block, or one is in the causal history of the other | Lemma 6 |
| BM6 | `HistoryPrefix` — the lower committed anchor's history is contained in the higher's | Lemma 6, corollary |
| BM7 | `AnchorsAreLeaderBlocks` — the anchors are the core's leader blocks | — |

**BM1** is quorum intersection: two support quorums share `n − 2f ≥ f+1`
authors, each supporting both blocks, and a validator that supports two
blocks of one author and round is an equivocator — one more than the
fault bound admits. Only `n ≥ 3f + 1` is used, which is the whole
committee of this arc.

**BM2** is the core's `reaches_of_honest_support_of_card` followed by
`reaches_pred_of_round_le`, so it consumes no Black Marlin definition
beyond `Supported`. The support quorum holds `f + 1` correct authors,
each with one block at the round above; a block two rounds above names
`n − f` of the at most `n` authors of that round and cannot miss all of
them.

**BM5** is where the rule's second clause is used, and the only place.
The three cases of the paper's Lemma 6 are the three ranges of the round
gap between the two committed anchors: at gap `0` BM1 identifies them;
at gap `≥ 2` BM2 applies to the higher block itself; at gap `1` the
lower anchor's linking block and the higher anchor are both supported
anchors of the same round, so BM1 identifies *them*, and the link is a
direct reference. Without the link clause, two supported anchors one
round apart need not be comparable, and nothing else in the rule would
make them so.

**BM6** is what the paper means by the committed anchors defining one
partial order across honest parties. `commit(B)` delivers the
undelivered blocks of `past(B)` and then `B`, so containment of causal
histories is containment of delivered prefixes: two validators'
deliveries agree wherever both have delivered, and neither can retract.
The order *within* each increment is the deterministic sort `τ`, which
the rule does not constrain and this arc does not model.

**BM7** connects a round-indexed arc to the slot-indexed vocabulary of
the rest of the development: under `Slots.uniformSingle 1` — one slot
per round, slot `r` led by the validator the rotation elects for round
`r` — an anchor block of round `r` is a leader block of slot `r`, and
conversely. It asserts nothing about any verdict.

`commit(B)`'s recursion over `strong(B) \ D` selects `maxAnchor`, the
highest-round undelivered anchor in the strong past. That choice fixes
the order in which anchors are visited; it does not enlarge the set of
blocks delivered, since `past(B′) ∪ {B′} ⊆ past(B)` for every
`B′ ∈ strong(B)`, which is why BM5 and BM6 are stated about `history`.
The order it fixes is §11.

## 5. Modelling choices

**(i) The DAG layer is the core's, unchanged.** The paper's validity
predicate `V` — a quorum of distinct authors from the round below, no
two blocks of one author, all signed — is the core's `ValidWrt`
(`spec.md` §3.2). The one addition the core makes is
`ValidWrt.self_parent`, a reference by the block's own author, which
Black Marlin does not require. It restricts the universes the results
range over and is consumed by none of them, so what is proved here is
weaker than the paper by exactly that clause. Removing it would be a
change to the core rather than an addition to an arc, and is recorded
rather than performed.

**(ii) Strong references only.** A Black Marlin block carries a second,
time-bounded set of weak references to earlier rounds; `past` follows
both and `strong` follows the first alone. The commit rule reads
`strong`, so the arc is stated over the core's `refs`, and BM2 and BM5
conclude something stronger than the paper's `past`. Weak references
bear on delivery completeness — that every block is eventually
delivered — rather than on the rule.

**(iii) `Reaches` is reflexive** where the paper's `past` and `strong`
exclude their own argument, which is why BM5 states equality as a
separate disjunct rather than folding it into the reachability case.

**(iv) The rotation is abstract.** `Rotation.anchor` is an arbitrary
function `ℕ → Validator`; round robin is one instance, used in the
witness. No result below depends on which validator is elected, only on
one being elected per round.

**(v) Anchors are a predicate, not a function.** The paper's `RR`
"returns both blocks" when the elected validator equivocates, so an
anchor round has one elected *author* but may hold several anchor
*blocks*. `IsAnchor U r L` admits all of them, and the uniqueness the
rule needs is BM1 rather than a property of the rotation.

## 6. Witnesses

`LeanDagTest/BlackMarlin/Model.lean` is the paper's Figure 1: four
validators with validator `0` Byzantine, `f = 1`, six rounds, one anchor
per round, and every block referencing three of the four below it
including its author's own. Every definition of `Model/` is settled on
it by `decide` before anything is proved from it.

The figure's point is the last two rounds. Anchors `B0`, `B1`, `B2` and
`B3` all carry a quorum of support, but validator `0` omits `B3` from
`B4`, so `B3` fails the link clause while `B0`, `B1` and `B2` satisfy
the whole rule — `decide` settles both halves, and `linkers Ubm 15 3 = ∅`
identifies the clause that fails. `B4` fails the other way: supported,
with its linking anchor present, but that anchor unsupported because the
DAG stops at round `5`.

The same universe carries the configuration the link clause exists for:
`B3` and `B4` are both supported anchors, one round apart, and neither
lies in the causal history of the other — so a rule with the support
clause alone would admit two incomparable anchors and BM6 would fail of
them.

The seven claims are then instantiated at this universe through
`Safety.holds` itself, so what the witness exercises is the proved
theorem rather than a restatement of it.

## 7. Layout and discipline

The arc adopts the statement/proof partition of `LeanDag/MahiMahi/`
(`mahi-mahi.md` §9).

The figure of §13 is generated by `scripts/black-marlin-figure.py` from
the same block table as the witness, so it drifts from the Lean only if
the script does.

```
LeanDag/BlackMarlin/
  Model/         definitions only, theorem-free: Rules, Decision, Round,
                 Ledger, Descent, Order, Repair
                 (decidable instances by `inferInstanceAs` included: definitions, not proofs)
  Helpers/       generated lemma infrastructure; unaudited
  <Result>/Statement.lean imports Model/ only; definitions, prose, `def Statement : Prop`
  <Result>/Proof.lean     `theorem holds : Statement`; unaudited
                          Results: Safety (BM1-BM7), Liveness (BML1-BML5),
                          Reactive (BMR1-BMR6), Agreement (BMA1-BMA4),
                          Ledger (BMD1-BMD6), Descent (BME1-BME5),
                          Order (BMO1-BMO9), Repair (BMP1-BMP13),
                          ViewLiveness (BMV1-BMV3), ViewOrder (BMT1-BMT3)
LeanDagTest/BlackMarlin/  witness models; the instantiations are audited
scripts/check-arc-holes.py   sorry/admit/axiom/native_decide/unsafe/partial absent;
                             Statement.lean files proof-free; Model/ files theorem-free
```

The audit surface is `Model/`, the seven `Statement.lean` files, the
witness instantiations and the checker. `scripts/check-arc-holes.py` covers both
partitioned arcs; it was named for Mahi-Mahi and is renamed here, its
checks unchanged.

**Relation to the core.** The core is consumed read-only: `Block`,
`BlockDag`, `Causality`, `CausalHistory`, `History`, `Support`,
`Validators`, `Schedule` for BM7 alone, `Liveness` for the participation
vocabulary and the counting step BML1 reuses, and `ViewPace` for the
pacing trunk `Pace` extends. The self-parent clause of
§5(i) is the one place a change to the core would strengthen a result,
and it is reported rather than made.

## 8. Liveness

The paper reaches liveness through §5.2's timing argument: Lemma 7's
`3∆` bound on a round, Lemma 10 on the timeout not firing when anchors
are honest, Lemma 11 on the expected number of rounds to a correct
anchor. This development states liveness above the structural condition
instead (`liveness.md`), so those are replaced rather than transcribed,
and no timeout, message delay, stabilisation time or probability appears
below. Five claims, in `LeanDag/BlackMarlin/Liveness/Statement.lean`:

| | Claim | Paper |
|:---|:---|:---|
| BML1 | `CommitStep` — a run of two reliable anchors over three populated rounds is committed | — |
| BML2 | `FullViewSound` — the full view reaches the verdict the rule reaches | — |
| BML3 | `Inclusion` — a reliable validator's block is in the causal history of every block two rounds above | Lemma 8 |
| BML4 | `Recurrence` — the rotation names a committing round arbitrarily far out | Lemma 11, role |
| BML5 | `RotationFair` — round robin supplies the run of two | — |

**BML1** is the core's counting step read twice. `Supported U L r` is
the core's `DirectCommit` under another name, so
`directCommit_of_votesAt` applies verbatim: coverage makes every
reliable block one round above `L` reference it, and those authors carry
a quorum. The link clause then costs no hypothesis of its own. The
round-`(r+1)` anchor is one of those reliable blocks, so the same
coverage fact already makes it reference the round-`r` anchor; and it is
supported by the same argument one round higher. Hence three populated
rounds and a run of two reliable anchors — where the core's three-round
rule needs a run that spans eligibility.

**BML3** consumes no clause of the commit rule. Coverage gives the block
a support quorum and BM2 carries it upward, so inclusion does not depend
on which anchors the rule admits, only on one being admitted above.
Together with BML4 this is the Validity property of Definition 1 for
reliable authors.

**BML4** plays the role of the paper's Lemma 11 — that commits keep
happening — without its probability. It quantifies the universe *inside*
the conclusion, as the core's
`CommitsAt` does and for the same reason: the rotation names the round,
and any DAG grown two rounds past it and covered from `R` commits it.
Fixing a universe first would cap how far the rotation may reach.

**BML5 is a theorem here where the core's counterpart is an assumption.**
The core's `FairRunOn` needs runs of three, and its docstring records the
pigeonhole for per-slot rotation as prose rather than proving it;
`WaveRobin.lean` supplies runs of three by rotating in waves instead.
Black Marlin needs runs of two, and that case is a short counting
argument: if no two cyclically adjacent anchors were reliable, the
successor map would inject the reliable set into the Byzantine one,
giving `n − f ≤ f` against `3f + 1 ≤ n`. So the rotation Black Marlin
actually deploys — `RR(r) = r mod n` — discharges the clause outright,
at every committee and whichever validators are Byzantine. This is a
consequence of the two-round rule rather than of the mechanisation:
three consecutive reliable leaders is a strictly harder fact than two,
and the second commit clause is what lets the rule ask only for two.

The witness is a second universe (`LeanDagTest/BlackMarlin/Liveness.lean`)
— four rounds, every block referencing the whole round beneath it.
Figure 1 cannot serve, and `decide` says why: its point is that
validator `0` omits the round-3 anchor from its round-4 block, which is
exactly a failure of coverage among the reliable validators.

## 9. The round rule, and the reactive schedule

`delivery(r)` is one half of the protocol; the other is L38–L41, which
says when a round is concluded. A validator waits for blocks from `n − f`
parties and then for **either** the round's anchor together with the two
anchors below it supported, **or** the round's timeout. The dual
condition is what makes the protocol responsive: it runs at the actual
delivery time rather than at `∆`, and it does not deadlock when an anchor
is Byzantine.

`LeanDag/BlackMarlin/Model/Round.lean` states the three clauses as
`QuorumIn`, `AnchorIn` and `SuppAnchorIn` over a `View`, and their
conjunction as `ConcludesAt`. `SuppAnchorIn` reads the same `SupportedIn`
the commit rule reads, so the round rule and the commit rule share their
arithmetic. The two lower clauses are written `∀ ρ, ρ + 1 = r → …` and
`∀ ρ, ρ + 2 = r → …` rather than with truncated subtraction, so the first
two rounds — where the paper's initialisation has no such anchors to
check — are vacuous rather than a separate branch.

`Pace` extends the core's `PaceCore` (report §6.9): the views,
convergence, the progress rule and production are inherited. Two clauses
are new. `anchor_or_wait` is the round rule read on the block a validator
produces — at the round above a reliable anchor, a block either
references that anchor or its builder waited the full timeout —  and it
is the same clause as the core's `ReactivePace.vote_or_wait`, since
concluding a round requires holding that round's anchor.
`prompt_conclude` bounds the exit from above, and it is **not** the same
as the core's `prompt_vote`: there the exit fires once the leader's block
is held, here once the whole round rule is satisfied.

Six claims, in `LeanDag/BlackMarlin/Reactive/Statement.lean`:

| | Claim | Paper |
|:---|:---|:---|
| BMR1 | `Votes` — every reliable block above a reliable anchor references it | — |
| BMR2 | `ReactiveCommit` — a run of two is committed, with no coverage hypothesis | — |
| BMR3 | `Exit` — the exit fires, given a run of **three** reliable anchors | — |
| BMR4 | `ExitSustained` — but only to enter: one further anchor per round after that | — |
| BMR5 | `Latency` — `D + δ + proc`, and `Δ + δ + 2 · proc` past GST | Lemma 7, role |
| BMR6 | `NoTimeout` — the timeout never fires when those undercut it | Lemma 10, role |

**BMR2 replaces BML1's coverage hypothesis.** `SynchronisedOn` asks that
every reliable block reference every reliable block below it, which a
reactive builder deliberately does not do. What survives is exactly what
the commit rule counts, and `anchor_or_wait` guarantees it — so reactive
liveness needs no coverage assumption at all.

**BMR3 is the cost of the extra clauses, and it is a run of three.** For
the exit to be guaranteed at round `r + 2`, the anchors of rounds `r`,
`r + 1` and `r + 2` must all be reliable: `quorum` and `anchor` come from
the round-`(r+2)` blocks, `suppAnchor(r+1)` from those blocks referencing
the round-`(r+1)` anchor, and `suppAnchor(r)` from the round-`(r+1)`
blocks referencing the round-`r` anchor. The commit rule asks for two
(§8); the fast path asks for three.

**BMR4 says the third is paid once.** `suppAnchor(r)` was already checked
to conclude round `r + 1`, and holdings only grow, so a validator already
on the fast path needs one further reliable anchor per round. Entering
costs a run of three; remaining costs a run of two. This is where the
run-of-three pigeonhole the core sidesteps re-enters the Black Marlin
arc — not for the commit rule, where BML5 discharges a run of two
outright, but for the guarantee that no timeout ever fires.

The witnesses are two (`LeanDagTest/BlackMarlin/Reactive.lean`).
`ConcludesAt` and its clauses are settled by `decide` on the covered
four-round model: round `3` may be concluded and round `4` may not. The
pacing structure is witnessed on `Ugrow`, the growing model the core's
reactive arc uses, at the same holdings and the same build spacing of
`6`; processing is `7` rather than the core's `5`, because the exit is
bounded by the round rule rather than by holding one block, and the
timeout is `25`, which is what lets both routes fire on one model.

## 10. Agreement

Definition 1's **Agreement** — if an honest party delivers a block, every
honest party eventually delivers it. Four claims, in
`LeanDag/BlackMarlin/Agreement/Statement.lean`:

| | Claim | Paper |
|:---|:---|:---|
| BMA1 | `Monotone` — a block delivered with a committed anchor is delivered with every committed anchor from that round on | Lemma 6, corollary |
| BMA2 | `LocalCommit` — a run of two is committed by each reliable validator on its **own view**, at an explicit time | Lemma 12, half |
| BMA3 | `Delivered` — the two composed | Definition 1, Agreement |
| BMA4 | `RunRecurs` — such a round exists above every round | — |

**BMA2 is the new work.** BML1 and BMR2 say a verdict is *available* over
the universe; Definition 1 speaks about what a party outputs. BMA2 runs
the same run-of-two argument inside `viewAt v t` rather than inside the
universe, with `PaceCore.holds_roundBlocks` putting the two rounds the
rule reads into every reliable validator's hands by
`max (latest (r+1)) (latest (r+2)) + Δ`. It needs no hypothesis beyond
BMR2's: that every build past round `R` lies past GST is derived from
`built_lt`, since the round number itself bounds the build time from
below.

**What is stated, and what is not.** A validator delivers `B` when it
calls `commit(A)` for an anchor it committed with `B ∈ past(A)`, so the
claims are about `B ∈ history U L` for the anchor `L` each validator
commits. Two things stand between that and the `ab-deliver` events of
Definition 1. The recursion of `commit` visits the undelivered anchors of
`strong(A)` before flushing, which fixes the **order** in which blocks
are delivered; that is §11. And the per-`(creator, round)` filter of L27
decides which of an equivocator's twins is delivered, which the
segmentation and the deterministic sort `τ` together arbitrate; `τ` is
not modelled. So the claims here are agreement on the delivered **set**,
with the order treated separately.

The witness is the covered four-round model for BMA1 — rounds `0` and `1`
are committed there and round `2` is not, the DAG stopping before its
link can be supported — and the pace of §9 for BMA2.

## 11. The delivered order

`commit(B)` does not deliver `past(B)` in one piece. It descends through
the undelivered anchors of `strong(B)`, flushing one `τ`-sorted segment
per anchor round from the lowest up (L18–L32). That segmentation *is* the
delivered order, and it is also what makes two validators' orders agree:
a validator that committed at rounds `3` and `5` and one that committed
only at `7` flush the same segments, because the second one's descent
visits `5`, `4` and `3` on the way down. `Model/Ledger.lean` models the
record the descent leaves rather than the recursion that builds it, as
the core models `Decided` rather than the implementation.

| | Claim | Paper |
|:---|:---|:---|
| BMD1 | `StepUnique` — the descent has one candidate where it steps by one round | — |
| BMD1′ | `CorrectAnchorUnique` — and at a round whose anchor is reliable, however deep the cone | — |
| BMD2 | `AgreeStep` — records agreeing at a round agree at the round below | — |
| BMD3 | `AgreeBelow` — and throughout any stretch they both descend | — |
| BMD4 | `CommittedPins` — records flushing committed anchors at one round agree there | Lemma 3 |
| BMD5 | `LinkPopulates` — the link clause keeps the descent from skipping | — |
| BMD6 | `Ledger` — no retraction, agreement, and one position per block | Definition 1, Total Order |

**BMD1 and BMD1′ say a tie needs two things at once.** The candidates at
round `ρ` below a round-`(ρ+1)` block are that block's references, and
`ValidWrt.distinct_creators` allows one block per author — so a
consecutive step has at most one candidate, whoever anchors. And at a
round whose elected validator is reliable the candidates are a singleton
however deep the cone, since non-equivocation gives it one block there.
So a choice requires a **skipped anchor round** — the elected validator
produced nothing, or its block is not referenced — **and** an
equivocating anchor at the round the descent then lands on. Either alone
leaves the descent determinate.

A skip stops the propagation of BMD2 and BMD3 there, and affects nothing
else: BML3's inclusion, BMA3's agreement and the whole of §4 are
statements about causal history rather than about segment boundaries, and
none of them reads the record.

**BMD5 is the point of the phase.** The commit rule's second clause was
used in exactly one case of one theorem for safety (§4). Here it does a
second job: above a committed anchor sits a *supported* anchor, which BM2
puts in the cone of every block from three rounds up — so the round above
a committed anchor is never the one skipped. The clause that makes
adjacent committed anchors comparable is also what keeps the delivery
order determinate around them.

**The skipped-round case, closed.** BMD3's stretch hypothesis is an
artifact of taking the record as given. `Model/Descent.lean` computes it
instead: `maxAnchor`, the metric of L24 and the descent are definitions,
and the record of `commit(B)` is what the descent returns. Five further
claims follow.

| | Claim | Paper |
|:---|:---|:---|
| BME1 | `DescendSound` — the choice is an anchor strictly below, at the highest anchor round | L21–L24 |
| BME2 | `DescendTotal` — and is made whenever an anchor lies below | L20–L21 |
| BME3 | `RecordIsFlush` — the record satisfies `Flush`, so BMD6 applies to it | — |
| BME4 | `Suffix` — the record below a visited block is that block's own record | — |
| BME5 | `AgreeBelow` — two records reaching the same block agree at every round below | — |

**BME5 closes BMD3.** L24's metric,
`|round(A) − round(maxAnchor(strong(A)))|`, reads the candidate and its
own cone alone, so every validator evaluates it identically and the
descent from a block is a function of that block. BME4 turns that into
the suffix property — below a visited block, a record *is* that block's
record — and BME5 reads off agreement with no hypothesis about the rounds
in between. `step` and `dense`, which `Flush` assumes, are derived
(BME3), so the ledger results of BMD6 apply to the computed record
unchanged.

Two modelling choices are recorded rather than derived. `𝒟` is dropped:
the delivered set only removes what an earlier descent visited, so a
validator's flushes over all its commits are one chain read from its
highest commit down. And "break ties deterministically" is read as the
`≤`-least survivor under a `LinearOrder` on identifiers, as the
Odontoceti and Mahi-Mahi arcs read their canonical choices; nothing
depends on which rule it is, only that it is shared and reads the
candidate alone.

The one defect in the pseudocode stands. L20 guards `𝒜 ≠ ∅` where
L21–L24 need `maxAnchor(𝒜) ≠ ∅`: when the undelivered remainder of
`strong(B)` holds no anchor at all, `B′` is undefined. BME2 states the
condition that is actually required.

Ordering *within* a segment is `τ`, which the rule does not constrain and
this arc does not model, so the ledger is a set and a record's rounds are
the positions in it. BMD6's last two clauses — a block enters at exactly
one round, and records that agree concur on which — are total-order
safety at that granularity.

The witness is the covered four-round model with its four anchors: the
candidate sets are singletons on data, and validator `3`'s genesis block
is placed at round `1`, with the anti-vacuity that it is not in the
round-0 anchor's cone.

## 12. The delivered sequence

Definition 1 speaks about `ab-deliver` events — a **list**, not a set.
§10 and §11 gave the set and the segment boundaries; this section gives
the list, by modelling the sort `τ` of L26 and the filter of L27.

`TopoSort` asks of `τ` exactly what the paper uses: that it is a
function of the set, hence shared, and that it respects causality.
`filterFirstFrom` threads the delivered set through L27, which is
stateful within a segment as well as between them. Nine claims:

| | Claim | Paper |
|:---|:---|:---|
| BMO1 | `AnchorLast` — the anchor is last in its own segment | L26, L30 |
| BMO2 | `SeqAgree` — records that agree output the same list | — |
| BMO3 | `SeqPrefix` — and the list only extends | — |
| BMO4 | `Integrity` — no author-and-round twice | Definition 1, Integrity |
| BMO5 | `KeyDelivered` — every author-and-round flushed is output | — |
| BMO6 | `CorrectDelivered` — and for a correct author, by the block itself | — |
| BMO7 | `TotalOrder` — records that agree cannot invert a pair | Definition 1, Total order |
| BMO8 | `DescentOrder` — two descents that meet output the same list | Lemma 12, half |
| BMO9 | `Validity` — a reliable author's block is output | Definition 1, Validity |

**BMO1 is a fidelity check.** L26 flushes `τ(past(B) \ 𝒟)` and L30 then
emits `B`; since every block of `history U B` is reachable from `B`, a
topological sort of `history U B \ 𝒟` places `B` last of its own accord,
so the two are one list and the model's single `segment` is faithful.

**BMO4 and BMO7 are Definition 1's Integrity and Total order.** The first
is a property of the filter alone; the second follows from BMO2, since
records that agree produce one list and a single list cannot order a pair
two ways.

**BMO6 is what closes Validity and Agreement at the level of events.**
BMO5 says *some* block of a flushed author-and-round is output; for a
correct author there is no twin for the filter to prefer, so it is that
block. With BMO9 — a reliable author's block reaches an anchor two rounds
up, by BML3, and is therefore flushed — Definition 1's Validity holds for
reliable authors as an `ab-deliver` statement rather than a membership
one.

**What is *not* closed, and a correction.** §10 said the remaining
distance to Definition 1's Agreement was the filter, and implied that
Lemma 12 and Validity were compositions of results already in hand. That
was too optimistic. The filter is closed for correct authors (BMO6), but
for an **equivocator** the twin that is output depends on the
segmentation, and two validators' records can differ at a round where
neither committed directly: the descent from a higher anchor picks the
round-`ρ` anchor its own chain reaches, and nothing forces that to be the
anchor another validator committed directly at `ρ`. BMO8 rules the
divergence out wherever the two descents meet at a common block; they
need not, and §13 exhibits an execution where they do not.

The witness is the covered four-round model: identifiers run downward
along references there, so sorting by identifier is a topological sort
and `TopoSort` is not vacuous. The list it delivers is
`[0, 1, 2, 3, 5, 4, 6, 7, 10, 8, 9, 11, 15]` — one sorted segment per
anchor round, each anchor last in its own — settled by `decide`, with the
round-3 blocks no committed anchor reaches absent from it.

## 13. Agreement, refuted

§12 left one thing open: whether two validators' records must agree at a
round where neither committed directly. They need not, and
`LeanDagTest/BlackMarlin/Divergence.lean` exhibits an execution where two
honest validators output **different blocks** of the same author and
round, neither ever outputting the other's. That is Definition 1's
Agreement refuted for the protocol as specified, at `n = 4`, `f = 1`.

The universe has four validators with `0` Byzantine, seven rounds, and
the rotation anchoring rounds `0` to `6` by `3, 3, 0, 1, 2, 3, 1`.
Validator `0` equivocates at round `2`, producing blocks `8` and `12`.
Every step is settled by `decide`:

![**Agreement refuted, on data.** The execution of `LeanDagTest/BlackMarlin/Divergence.lean`. Validator `0` is Byzantine and equivocates at round `2`; three round-3 blocks support `8` and the round-3 anchor `14` links it, so the rule commits `8`, while `12` has one supporter and the rule never admits it. The round-4 anchor `19` omits `14` — legal, since a block needs three references of four — so its cone holds no round-3 anchor at all. A validator that missed the round-2 commit and commits `19` instead therefore descends past round `3` and meets both twins at round `2`, where L24's metric prefers `12`: one round from the nearest anchor of its own cone, against two for `8`. Each validator then bars the other's block at the filter of L27. Rounds `5` and `6` carry the support that makes `19` committed and are drawn without highlighting.](figures/black-marlin-divergence.svg)


* **The rule commits `8`, and only `8`.** Three round-3 blocks reference
  it, and the round-3 anchor `14` both references it and carries three
  supporters, so `Committed Udiv 8 2`. Its twin `12` has one supporter,
  so BM1 is untouched — the rule admits exactly one of them.
* **The round-4 anchor omits `14`.** A block needs `n − f = 3` references
  of `4`, so a correct validator that has not yet received `14` builds
  without it, legally. Then `coneAnchors Udiv 19 3 = ∅`: a descent
  arriving at `19` finds no round-3 anchor and skips the round.
* **At round `2` it therefore faces both twins**, and the tie-break of
  L24 prefers `12`: block `8` omits the round-1 anchor from its own
  references where `12` includes it, so the metric reads `2` for `8` and
  `1` for `12`.
* **The records part.** `flushRecord Udiv 8 2 = some 8`, and
  `flushRecord Udiv 19 2 = some 12`.
* **And so do the outputs.** The first validator outputs `8` and never
  `12`; the second outputs `12` and never `8`. The second does *flush*
  `8` — it lies in the round-4 anchor's cone — and drops it at the filter
  of L27, that author and round having already gone out.

The execution behind the two records: one validator runs `delivery(4)`
with `17`, `18` and `20` in view, sees `14` supported, and commits `8`.
The other lacks those three, so `delivery(4)` finds `14` unsupported and
the attempt fails; the protocol never retries a round, so it commits
nothing until round `6`, where `delivery(6)` admits the round-4 anchor
and the descent takes `12`.

**No timing hypothesis is needed.** Agreement is a safety property, and
§5 of the paper states that the safety properties "are satisfied during
both synchrony and asynchrony". Asynchrony is exactly the freedom to
delay `17`, `18` and `20` to the second validator, which is all the
execution asks for. The DAG itself is buildable: every block references
only blocks of the round beneath it that its author could have held, each
honest one carries every block of that round it holds as L46–L48
require, and each carries a quorum of three distinct authors.

**And the protocol cannot escape by not filtering.** Both twins are
flushed by the second validator — `8` lies in the round-4 anchor's cone —
and they carry one author-and-round between them. L27 must drop one:
emitting both would output two blocks for a single `(party, round)`,
which Definition 1's Integrity forbids "at most once **regardless of
`B`**". So the execution admits no reading that satisfies both
properties. Filter, and Agreement fails; do not filter, and Integrity
does. Neither depends on tracing what the first validator does at its
later commit.

**What this does and does not touch.** It does not contradict the commit
rule: `12` is never committed by the rule, and BM1 through BM7 are
untouched. It does not touch liveness. What it refutes is Definition 1's
Agreement, and with it Theorem 13, for the algorithm as written — and it
locates the defect precisely at the two steps the paper asserts without
argument, Lemma 12's "by construction of the delivery function, party
`j` must have also committed `B`" and Theorem 13's Agreement clause
"therefore party `j` eventually ab-delivers(B, j, r)".

**Is it a slip in the pseudocode?** No. The recursion is described three
times and no description is support-aware. §4.4's prose has "party `i`
searches for a non-delivered block `B′` from a higher round reachable
through strong references from `B`" — not even restricted to anchors.
Figure 2's caption has "it will recursively commit earlier uncommitted
anchor blocks first". §4.5 has "`maxAnchor(𝒜)` … returns the anchor from
the highest round". And L21–L24's tie-break is the round-distance metric.
The commit *rule* is support-aware and considers every twin — L15's "if
multiple consider them all", and `RR` "returns both blocks" when the
anchor equivocates — so the design has the Byzantine-anchor case in view
throughout. The recursion simply does not inherit it.

§4.4 states the property this refutes, in the same paragraph: "These
conditions prevent honest parties from committing different blocks when
the anchor party is Byzantine." That is true of L16, and BM1 proves it.
It is not true of the code path that runs when L16 *fails*.

**Nor is equivocation assumed away.** The one place the paper excludes it
is its complexity section, and explicitly only to size
`DAG \ history[j]` for the communication bound; the safety and liveness
sections assume nothing of the kind, and Lemma 3's proof reasons about
multiple blocks per party directly.

**And the adversary chooses.** Which twin loses the tie-break is fixed by
the twins' own references, which their Byzantine author writes. It can
give the twin it feeds the honest majority the *larger* metric, as `8`
has here, so this is an attack rather than an unlucky configuration.

**What would repair it** is §14: making the descent prefer a *supported*
anchor among tied candidates, which BM1 makes unique. That is tested
there as a side-condition on the record rather than as a change to the
model.

## 14. The repair, tested

§13 named a repair — let the descent prefer a supported anchor among
tied candidates — and left it unmade. This section makes it as a
**side-condition** rather than a change to the model: `descend`,
`flushRecord` and everything proved of them stand, and
`LeanDag/BlackMarlin/Model/Repair.lean` sits beside them.

A record is **support-preferring** when, at any round where some anchor
carries a quorum of support, what it flushes there is supported. And
`descendSupp` filters the candidates of L21–L24 to those the rule could
commit, falling back to L24 only where none is. Six claims:

| | Claim | |
|:---|:---|:---|
| BMP1 | `AtMostOneSupported` — at most one candidate of a step is supported | BM1 |
| BMP2 | `RepairPrefers` — `descendSupp` takes it where there is one | — |
| BMP3 | `RepairRefines` — and is L21–L24 verbatim where there is not | — |
| BMP4 | `NoStall` — a step never stalls and never moves to another round | — |
| BMP5 | `Agrees` — support-preferring records cannot part at a supported round | BM1 |
| BMP6 | `LivenessUntouched` — `Committed` mentions no part of the descent | definitional |

**BMP5 is the answer to the question.** Two records that both flush at a
round where a supported anchor exists flush the same block, because BM1
makes the supported anchor of a round unique. That is exactly what §13's
execution lacked, and on that execution the repair closes it: only `8` is
supported among the two candidates, so `descendSupp` takes it, and the
two records agree at round `2` where before they did not.

**Liveness does not fail.** What the liveness results conclude is
`Committed`, which is the conjunction of `IsAnchor`, `Supported` and
`Linked` and mentions no part of the descent — BMP6 is that observation,
and it is an identity, which is the point. BML1 through BML5 and BMR1
through BMR6 hold of the repaired protocol word for word. BMP4 adds that
the descent still terminates and still visits a block at every step the
unrepaired one did, so nothing is left undelivered.

**What it does cost.** The delivered *order* changes. A chain through a
different block descends through a different cone, so a record may flush
at different rounds: on §13's execution the repaired chain reaches `8`,
whose cone holds no round-1 anchor, and so flushes nothing at round `1`
where the unrepaired chain flushed `7`. No block is lost — `7` is in the
round-4 anchor's cone and comes out in that segment instead — but the
segmentation differs, which is why BMP4 speaks of a step and not of a
record.

**But the weak form does not close the general case**, and the reason is
worth stating. `descendSupp` chooses among the candidates L21–L24 already
offers. Where the cone reaches the supported anchor of a round but the
*step* does not — because the block it steps through cites a twin
instead — the filter is empty and the fallback takes the twin. So the
repair helps exactly where the supported anchor is already a candidate.

### The strengthened form

`descendS` drops the tie-break rather than filtering it: descend to the
highest-round **supported** anchor of the cone, and nowhere else. Four
more claims, and one about liveness.

| | Claim | |
|:---|:---|:---|
| BMP7 | `StrongSupported` — every boundary is supported | — |
| BMP8 | `StrongReaches` — no committed anchor is passed by | BM1, BM2 |
| BMP9 | `StrongAgrees` — agreement runs down from any meeting point | — |
| BMP10 | `StrongNoStall` — a choice is made where one exists, and sits lower | — |
| BMP11 | `StrongAgreesCommitted` — two records with committed tops agree outright | BM5 |
| BMP12 | `NotStuck` — committed rounds still recur | BML4, BML5 |

**BMP7 answers the equivocation-without-quorum case.** A round whose
anchors carry no quorum is not a boundary at all, so the strengthened
descent makes no choice there and two records cannot part over one. The
case that the weak form leaves open does not arise.

**BMP8 is the argument.** Above a committed anchor at `ρ` there is a
supported anchor at every round the chain could land on: the committed
anchor itself is in every cone from `ρ + 2` up (BM2), and its linking
anchor at `ρ + 1` is supported because the commit rule says so — and BM1
fixes which block each of those is. So the chain cannot step over `ρ`;
it lands on the committed anchor.

**BMP9 and BMP11 complete it.** Two records whose tops are committed
anchors both reach the lower of the two — BM5 puts it in the higher's
cone — and therefore agree at every round below it, with no hypothesis
about what lies between the two tops. On §13's execution the only
supported anchor in the round-4 anchor's cone is `8`, so the descent goes
straight to it and the two records agree at every round.

**Liveness survives.** BMP12 is the recurrence of committed rounds
restated for the repaired protocol: it is a statement about `Committed`
and the rotation, neither of which the repair touches, so no execution is
stuck after synchrony. BMP10 adds that the descent still terminates.
Segments only coarsen — on §13's execution the round-1 and round-0
anchors carry two supporters apiece, one short, so neither is a boundary
and their blocks come out inside the segment above — so nothing is
delivered later than the next committed anchor.

### Is the support in view when the descent needs it?

Both repairs read `Supported`, a fact about the **universe**, where a
validator reads its own view. That gap is the last thing between a repair
proved and a repair deployable, and it does not close.

**It closes in one case, and not the one that matters.** BMP13: an anchor
by a *reliable* author, past the round coverage takes hold, is referenced
by every reliable block of the round above, so any view holding those
sees the whole quorum. Coverage says nothing about a **Byzantine**
author's anchor — and a Byzantine anchor is exactly what the repair
exists for.

**And there it fails, by counting.** A view carrying a quorum at the
round above shares only `n − 2f` authors with an anchor's supporters,
which at `n = 3f + 1` is `f + 1` — short of the `2f + 1` the test wants.
§13's execution carries such a view: the cone of the round-4 anchor holds
a quorum of authors at round `3`, so its holder could conclude that round
and run the rule, and yet it sees two of `8`'s three supporters. The
third is `14`, which the round-4 anchor does not reference — the same
omission the whole construction turns on. So the repaired descent, run
against that view, would not make `8` a boundary.

A caveat on that witness, in the other direction. The second validator of
§13 *does* see the support: it holds a quorum at round `6`, hence those
blocks' cones, hence `14`. The cone of the round-4 anchor is a view that
misses it, and it is a legal one — ref-closed, carrying a quorum at the
round it would run the rule on — so **nothing in the model forces the
support into view**. What is refuted is that it is always there, not that
it is missing in §13's run.

So the repair is **proved of the universe** and **not established as a
view-local rule**: a validator applying it is applying a test it cannot
always evaluate, and no hypothesis in this development supplies the
missing one.

### Two repairs that do not work, and why the third must read support

**Delivering both twins does not work.** L27's per-`(creator, round)`
filter is what makes a boundary observable, and it is there because
Definition 1's Integrity forbids two outputs for one party and round
whatever the blocks are. Dropping it — one output per *block* — leaves
the segmentation untouched, and the segmentation is what differs. The
first validator's segment at round `2` is the cone of `8` and the
second's is the cone of `12`, and each picks the other twin up only in
the round-4 segment. So one delivers `8` before `12` and the other `12`
before `8`, by `decide`; and the same for ordinary blocks, `5` lying
below one twin and `7` below the other. An Agreement failure becomes a
Total-order failure, which is no better.

**A canonical order on the twins does not work either.** One is already
in the model: `descend` takes the `≤`-least of the gap-minimisers, and it
still takes the wrong twin, because L24's metric decides before the order
is consulted. Nor does the order alone suffice, and the reason is
general rather than particular to §13's execution.

Give the twins the **same references**. They then agree in round, in
creator and in cone, so every function of the candidate blocks and their
own histories returns one answer on both: L24's metric ties exactly, and
a canonical order decides by identifier. What is left to tell them apart
is which of them the round-3 blocks reference — that is, support.

Two universes witness it, alike in all of those respects and differing
only there. `strongOf` agrees on the twins within each and across both;
`8` is the committed twin in one and `12` in the other; and `descend`,
which reads neither, answers `8` in both — right once and wrong once.
No rule blind to support does better, because its input is the same in
the two. The support-preferring descent separates them: `descendS`
answers `8` and `12` respectively.

**So the tie-break must read support, and support is what a view need
not carry.**

### Counting support in the cone does not settle it either

The obvious weakening is to read support **relatively**: prefer the twin
that more of the descent's own cone references. That is view-independent
by construction — every validator descending from one block reads one
cone — and on §13's execution it answers correctly, `{2, 3}` against
`{0}`, where the quorum test needed three and found two.

It has no margin. A committed twin holds `2f + 1` supporters of
`3f + 1`, of which at least `f + 1` are reliable; a reliable supporter
authors one block at the round above and that block references the twin,
so it is counted exactly when the cone holds it — and a cone need only
carry `n − f` authors, omitting up to `f`. **One** cone-supporter is all
the committed twin is promised. Its twin is bounded the other way: a
supporter of both authors two blocks at one round, so the two supporter
sets meet only inside the `f` Byzantine validators, and outside the
quorum there are `f` more. That gives `2f`, and every one of them can
sit in the cone, the Byzantine ones contributing the block that
references the twin rather than the one that references the anchor.

Both ends are realised at `f = 1`, where they are `1` and `2`, so the
rule fails at the smallest committee the protocol admits. Four
validators, `0` Byzantine, seven rounds; `0` equivocates at round `2`
with `8` and `12` and gives them the same references, so nothing
block-intrinsic separates them. Round `3` gives `12` the quorum
`{0, 1, 2}` and `8` only `{0, 3}`, one short, with `0` equivocating
again to support both. The round-4 anchor `21` omits the round-3 anchor,
so a descent arriving there skips the round and faces both twins — and
of the three round-3 blocks in its cone, two reference `8` and one
references `12`. Counting prefers the twin that was not committed, and
the identifier order prefers it too. Only the quorum reading separates
them, and that is the reading a view need not be able to evaluate.

### Which leaves a dichotomy, not a gap

The tie-break must read support, and a view need not carry it. Read
operationally that is a choice between two unsound implementations.

**Decide from what is held**, evaluating the rule against `SupportedIn`.
That under-reports: §13's execution carries a view seeing two of three
supporters, and the `f = 1` model above carries one seeing *no* twin
supported at all. A validator that descends regardless selects by some
fallback, and every fallback available to it is one of the rules refuted
above. **Safety fails.**

**Or wait until the quorum is held.** A committed twin's `2f + 1`
supporters include at least `f + 1` reliable ones and up to `f`
Byzantine ones. The reliable blocks arrive; the Byzantine ones need
never be sent, and under partial synchrony nothing obliges them to be.
The `f = 1` model exhibits it: the deciding supporter of the committed
twin is authored by the equivocator and referenced by no reliable block,
so a view holding every reliable block and everything those reference
sees `{1, 2}` for one twin and `{0, 3}` for the other — neither a
quorum, and no further reliable block will settle it. **Liveness
fails.**

**A correction.** This section previously recorded liveness as untouched
by the repair, because BMP10 and BMP12 are untouched. They are, and they
conclude `Committed U L r` — a statement about the universe, which is a
modelling device rather than anything a validator holds. Liveness is
conventionally about what a party outputs from its own view, and on that
reading the repaired rule is not live. BML1–BML5, BMR1–BMR6 and BMP12
are all stated at the universe; BMA2 alone is stated at a view, because
Agreement forced it to be. For the unrepaired rule the distinction is
harmless, coverage putting a reliable anchor's supporters into every
reliable view, which is BMP13 — and it is exactly where the repaired
rule needs a *Byzantine* anchor's supporters that coverage is silent.

## 15. Liveness at a validator's view

§8 and §9 conclude `Committed U L r`: the **universe** admits a commit
at that round. That is not what liveness asserts. A validator delivers
from its own view, and the universe is a device of this model rather
than an object anyone holds, so a liveness result read there is about
the wrong thing. This section restates the arc where liveness lives, and
draws the line the rest of the record has been circling.

**BMV1, no reliable validator is stuck.** Above every round the rotation
names a later one that *every* reliable validator commits **on its own
view**, by a time the pace supplies, in any sufficiently grown DAG.
BML4 said such a round exists; this says everyone reaches it.

**BMV2, nothing is held back.** And what any view committed below that
round is in what every reliable validator delivers at it. BMA3 asked for
a reliably anchored round above `ρ`; the rotation supplies one, so the
hypothesis becomes a conclusion.

Neither is new work at the level of the DAG. BMA2 and BMA3 already
concluded at a view, and BMA4 already discharged the round they ask for;
what was missing was the composition and the statement that the earlier
results were being read at the wrong level.

### Where it holds, and where it stops

**BMV3 is the line.** At a reliably anchored round past coverage, an
anchor is referenced by every reliable block of the round above, so a
view holding those sees the quorum. The commit rule's input at such a
round is reliable blocks, and coverage delivers reliable blocks. So the
rule can be applied without waiting for anything a Byzantine validator
might withhold, which is why BMV1 has a time in it and not merely an
"eventually".

**Past that line there is nothing.** The descent reads `Supported` at
whichever anchor its chain lands on, and no clause constrains that
anchor's author. Where the author is the equivocator, coverage is silent
— it constrains `T`-authored blocks only — and a committed anchor's
quorum of `2f + 1` supporters need contain just `f + 1` reliable ones.
§14 exhibits a view holding every reliable block, and everything those
reference, in which neither twin is supported.

So the protocol as the paper states it is live at the view for the
delivered **set**, and the repair of §14 has no live implementation: its
validator either decides from too little and loses safety, or waits on a
block the equivocator need never send and loses liveness. BMV3 is the
boundary between the two, and it is a narrow one — the commit rule sits
on the near side and the descent does not.

## 16. The delivered order at a validator's view

§15 concludes `B ∈ history U L` — membership in what a validator
delivers, not position in the sequence it delivers. The position is
fixed by the descent. This settles it, in both directions.

**BMT1.** Two records that flush at a round whose anchor is *reliable*
flush the same block, whatever views they came from. Not an agreement
argument and needing no coverage: the block flushed there is that
round's anchor, its author is correct, and `no_equivocation` leaves one
such block in the universe. A reliable anchor gives the descent no
choice, so every view makes the same one.

**BMT2.** BMD3 needs a round two records agree at, and BMT1 supplies
one, so agreement descends from any reliably anchored round through the
stretch a record flushes at.

**BMT3.** Where every anchor below a round is reliable, two records
flushing at the same rounds deliver the **same list** — Definition 1's
Total order, unconditionally, on that stretch.

### And the hypothesis is tight

One Byzantine anchor below is enough, and the break is not confined to
the equivocator's blocks. In §13's execution the two records deliver `5`
before `7` and `7` before `5`. Both are authored by **reliable**
validators, neither has a twin, and L27's filter never touches either.
What orders them is which segment they fall in: `5` lies below one twin
and `7` below the other, so each record takes one in its round-2 segment
and the other only in the round-4 segment.

So Definition 1's **Total order** fails, and on honest blocks. That is a
sharper failure than §13's and a more robust one — it does not depend on
which twin the filter prefers, so no rule for choosing among twins
repairs it. Only a rule making the two descents agree does, which is
`descendS`, and §15 is why that has no live implementation.

![**Total order refuted, on data.** Above, the DAG of `LeanDagTest/BlackMarlin/Divergence.lean`: the equivocator's twins differ in one reference, `8` taking `5` and `12` taking `7`, drawn in colour. Below, the two `ab-deliver` sequences `commitSeq` — Algorithm 1's own recursion — computes from it, grouped by the invocation of `commit` that emitted each block. The first validator commits `8` at `delivery(4)` and `19` at `delivery(6)`; the second fails `delivery(4)` for want of `17`, `18` and `20`, and commits `19` alone, its descent reaching `12` and so `7`. Blocks `5` and `7` are authored by reliable validators and have no twins, so L27's filter never examines either, yet they come out in opposite orders. Block `7` is the anchor of round `1`, so an honest leader's block is a segment boundary for one validator and mid-segment for the other.](figures/black-marlin-order.svg)

### Checked against Algorithm 1, and one more defect

`Flush` records a validator's boundaries as a function of round and
`ledgerSeq` reads them off in round order. `commit(B)` is invoked afresh
at each successful `delivery(r)` and threads `D` across invocations, so a
later commit can descend below a boundary an earlier one passed and emit
those blocks *after* blocks of a higher round — which a round-indexed
record cannot express. `Model/Recursion.lean` writes L18–L32 out
directly so the abstraction can be checked rather than assumed.

Run through it, the second validator's `Flush` reproduces its sequence
exactly, and the first's differs in one position and no more: the
round-0 anchor `3` is flushed as its own segment at `delivery(4)`, where
a record with no round-0 boundary emits it inside the round-2 segment.
The pair the order turns on is unaffected. So the inversion is a
property of the algorithm as written.

**L30 sits outside the loop L27 guards.** Read literally, the anchor `B`
is `ab-deliver`ed whatever `D` holds, so the first validator — having
delivered `8`, then descending to `12` — would deliver both, breaking
Integrity outright. §4.4's prose says otherwise: "In case of conflicting
blocks from the same party and round, only the first block ... is
ab-delivered". `commitSeq` takes the prose and filters `B` as well,
which is the reading under which everything above stands; under the
literal one Integrity fails with no argument needed.

The order therefore agrees exactly as far as the rotation is reliable
and no further. The boundary is not a limitation of this record: BMT3 is
proved, its converse is refuted on data, and between them nothing is
left open.

## 17. What is not covered

**Lemma 11.** No counterpart, and none needed: BML5 makes the recurring
run deterministic where the paper bounds an expectation. The expectation
sits oddly with the paper's own "substitution of the common coin with a
deterministic round-robin mechanism", and its time-complexity section
derives the headline latency — `4.25` rounds under Byzantine faults —
from it.

**Lemmas 7 and 10 in their own terms.** BMR5 and BMR6 play their roles —
a bound on the time to conclude a round, and the timeout not firing when
anchors are reliable — but state them in `∆`, the actual delivery `δ` and
the processing bound, above the pacing structure rather than over a
message schedule.

**Delivery completeness.** BML3 covers reliable authors. That *every*
block reaches the ledger needs the weak-reference window of §4.3.

**Agreement for an equivocator's twins** — refuted rather than left
open (§13). Definition 1's other three properties are Validity (BMO9),
Integrity (BMO4) and Total order (BMO7); Agreement holds for correct
authors' blocks and, for an equivocator's, wherever two descents meet
(BMO8), which §13 shows they need not.

**The deterministic tie-break as a rule.** L24's metric is transcribed
(§11); "break ties deterministically" is read as `≤`-least under a
`LinearOrder` on identifiers, which is a choice the paper leaves open.
