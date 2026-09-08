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

Black Marlin [Amo+25] is a partially synchronous DAG protocol that uses
neither reliable broadcast nor a common coin, and elects an anchor in
every round. It commits three rounds after proposal at `n ≥ 3f + 1`, and
without a certificate round.

**This arc is a refutation.** Definition 1's Agreement does not hold of
the protocol as presented: §9 exhibits an execution, machine-checked at
`n = 4`, `f = 1`, in which two reliable validators output different
blocks of one author and round and neither ever outputs the other's. Its
Total order fails on the same execution, and on blocks of *reliable*
authors, for a reason that does not turn on the twins at all.

**So the arc carries the rule and the refutation, and nothing else.**
What it carried before, and no longer does: the commit rule's own safety
results, liveness above the structural condition, the round rule and the
reactive schedule, Agreement as a statement, the view-relative order
results, and a repair. A scheme this development has refuted is not one
to integrate with the target properties, so the arc has no carrier and
shows none of them.

**On the repair.** Making the descent prefer a *supported* anchor closes
§9's execution, and its internal claims were proved. What was never
proved is that a validator can run it: support is a quorum over the
universe, a validator reads a view, and a view carrying a quorum at the
round above shares only `n − 2f` authors with an anchor's supporters —
`f + 1` at `n = 3f + 1`, short of the `2f + 1` the test wants. Deciding
from what is held selects the wrong block; waiting until the quorum is
held need never complete. The first loses safety, the second liveness,
so no member of that family is deployable and its development is not
carried.

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
statement. §2 states the rule the two describe.

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
the second conjunct of the commit test.

## 4. Modelling choices

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

## 5. Witnesses

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
clause alone would admit two incomparable anchors, and chaining would fail of
them.

The seven claims are then instantiated at this universe through
`Safety.holds` itself, so what the witness exercises is the proved
theorem rather than a restatement of it.

## 6. Layout and discipline

The arc adopts the statement/proof partition of `LeanDag/MahiMahi/`
(`mahi-mahi.md` §9).

The figure of §9 is generated by `scripts/black-marlin-figure.py` from
the same block table as the witness, so it drifts from the Lean only if
the script does.

```
LeanDag/BlackMarlin/
  Model/         definitions only, theorem-free: Rules, Decision,
                 Ledger, Descent, Order, Recursion
                 (decidable instances by `inferInstanceAs` included: definitions, not proofs)
  Helpers/       the lemmas the descent and the delivered order need:
                 Rules, Ledger, Descent, Order
LeanDagTest/BlackMarlin/Divergence.lean   the refuting execution
scripts/check-arc-holes.py   sorry/admit/axiom/native_decide/unsafe/partial absent;
                             Model/ files theorem-free
```

No `<Result>/Statement.lean` and `Proof.lean` pairs remain: the results
they stated — safety, liveness, the reactive schedule, agreement, the
view-relative order, and the repair — are not carried, so the audit
surface is `Model/`, the witness, and the checker.

**Relation to the core.** The core is consumed read-only: `Block`,
`BlockDag`, `Causality`, `CausalHistory`, `History`, `Support`,
`Validators` and `Schedule`. The self-parent clause of
§4(i) is the one place a change to the core would strengthen a result,
and it is reported rather than made.

## 7. The delivered order

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
else: the liveness and agreement results this arc no longer carries are
statements about causal history rather than about segment boundaries, and
none of them reads the record.

**BMD5 is the point of the phase.** The commit rule's second clause was
used in exactly one case of one theorem for safety. Here it does a
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

## 8. The delivered sequence

Definition 1 speaks about `ab-deliver` events — a **list**, not a set.
§7 gave the set and the segment boundaries; this section gives
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
| BMO9 | `Validity` — a reliable author's block is output | Definition 1, Validity |

**BMO1 is a fidelity check.** L26 flushes `τ(past(B) \ 𝒟)` and L30 then
emits `B`; since every block of `history U B` is reachable from `B`, a
topological sort of `history U B \ 𝒟` places `B` last of its own accord,
so the two are one list and the model's single `segment` is faithful.

**Integrity and Total order are Definition 1's.** The first
is a property of the filter alone; the second follows from BMO2, since
records that agree produce one list and a single list cannot order a pair
two ways.

**BMO6 is what closes Validity and Agreement at the level of events.**
BMO5 says *some* block of a flushed author-and-round is output; for a
correct author there is no twin for the filter to prefer, so it is that
block. With BMO9 — a reliable author's block reaches an anchor two rounds
up, by the liveness argument the arc no longer carries, and is therefore
flushed — Definition 1's Validity holds for
reliable authors as an `ab-deliver` statement rather than a membership
one.

**What is *not* closed, and a correction.** The agreement account said the remaining
distance to Definition 1's Agreement was the filter, and implied that
Lemma 12 and Validity were compositions of results already in hand. That
was too optimistic. The filter is closed for correct authors (BMO6), but
for an **equivocator** the twin that is output depends on the
segmentation, and two validators' records can differ at a round where
neither committed directly: the descent from a higher anchor picks the
round-`ρ` anchor its own chain reaches, and nothing forces that to be the
anchor another validator committed directly at `ρ`. The descent-agreement
result ruled the
divergence out wherever the two descents meet at a common block; they
need not, and §9 exhibits an execution where they do not.

The witness is the covered four-round model: identifiers run downward
along references there, so sorting by identifier is a topological sort
and `TopoSort` is not vacuous. The list it delivers is
`[0, 1, 2, 3, 5, 4, 6, 7, 10, 8, 9, 11, 15]` — one sorted segment per
anchor round, each anchor last in its own — settled by `decide`, with the
round-3 blocks no committed anchor reaches absent from it.

## 9. Agreement, refuted

§8 left one thing open: whether two validators' records must agree at a
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
§4 of the paper states that the safety properties "are satisfied during
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
rule: `12` is never committed by the rule, and the commit rule's own
safety statements are
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

**What would repair it** is making the descent prefer a *supported*
anchor among tied candidates, which BM1 makes unique. That is tested
there as a side-condition on the record rather than as a change to the
model.

## 10. What is not covered

**Lemma 11.** No counterpart: the liveness development that made the
recurring run deterministic, where the paper bounds an expectation, is
not carried. The expectation
sits oddly with the paper's own "substitution of the common coin with a
deterministic round-robin mechanism", and its time-complexity section
derives the headline latency — `4.25` rounds under Byzantine faults —
from it.

**Lemmas 7 and 10 in their own terms.** The reactive results played their roles —
a bound on the time to conclude a round, and the timeout not firing when
anchors are reliable — but state them in `∆`, the actual delivery `δ` and
the processing bound, above the pacing structure rather than over a
message schedule.

**Delivery completeness.** The liveness argument covered reliable authors. That *every*
block reaches the ledger needs the weak-reference window of §4.3.

**Agreement for an equivocator's twins** — refuted rather than left
open (§9). Definition 1's other three properties are Validity (BMO9),
Integrity and Total order; Agreement holds for correct
authors' blocks and, for an equivocator's, wherever two descents meet
which §9 shows they need not.

**The deterministic tie-break as a rule.** L24's metric is transcribed
(§7); "break ties deterministically" is read as `≤`-least under a
`LinearOrder` on identifiers, which is a choice the paper leaves open.
