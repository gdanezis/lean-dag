# lean-dag — Odontoceti: two-round commitment, formalized

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document records the formalization of **Odontoceti** — the first
DAG protocol to commit in **two** communication rounds:

> P. Vander Vos (supervised by P. Jovanovic and A. Sonnino). *Odontoceti:
> Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis,
> arXiv:2510.01216, 2025.

Machine-checked **safety** and **liveness** of the two-round decision
rule, proved in `LeanDag/Odontoceti/` with `decide` witnesses in
`LeanDagTest/Odontoceti/`, at thresholds *generalized* from the thesis's
fixed committee. Results carry **O**-labels, continuing the house
scheme. The existing DAG development is consumed read-only — not one
definition or theorem outside the new directory changed — and the
formalization surfaced four findings about the thesis (§6): a
consensus-critical gap in the agreement argument, a missing lemma its
case analysis needs, a consequential ambiguity in the indirect test's
counting unit, and a loose counting step — alongside confirmation that
everything else is sound, at a generality the thesis does not claim.

## 0. Overview

**Notation.** `n` validators with at most `f` Byzantine; Odontoceti
requires `n ≥ 5f+1` (the thesis fixes `n = 5f+1`; we prove the
generalization). `Correct` is the complement of the Byzantine set. `U`
is the block universe; a block at round `r` references `n − f`
distinct-author blocks of round `r−1`, self-parent included. Slots are
leader assignments through the existing `Slots` schedule; the slot at
round `r` **decides at round `r+1`** — waves are two rounds, pipelined,
with no certificate round.

**The headline results.**

- **Safety** (`Odontoceti.agree`, `Odontoceti.safety`): no two
  validators reach conflicting decisions for any slot, whatever views
  they hold and whichever routes — direct or indirect — they took.
- **Liveness** (`OdontocetiProperties.all_decided_below_of_fairRun`): under
  `Live`, `DeliversQuorum`, post-`R` synchrony, and a recurring run of
  **two** consecutive correct-led slots, every slot below the run is
  decided on any view caught up to the horizon (`View.CoversUpto`) —
  with commit latency one round shorter than Mysticeti's at every step
  of the composition.
- **The generalization held**: everything is proved at `n ≥ 5f+1` with
  direct thresholds `n − f` and indirect threshold `n − 3f`,
  specializing to the thesis's `4f+1` / `2f+1` at the boundary. The
  planned fallback (pinning `n = 5f+1`) was never needed.
- **The findings** (§6): four issues in the thesis's safety argument.
  Chief among them: agreement between two *indirect* commits at a
  shared anchor is not a consequence of the quorum arithmetic — two
  equivocating candidates can both pass the indirect test at one
  anchor, realised on data by `utwin6_both_pass` — so the formalized
  rule commits the **canonical least** passing candidate, the
  implementation's deterministic iteration order stated as mathematics,
  and exactly what makes agreement a theorem. Also: a lemma the
  agreement proof needs but the thesis lacks (O4′), the
  blocks-versus-authors ambiguity in the indirect test, and a counting
  step that needs the exact complement identity to go through.

## 1. The protocol, in our vocabulary

Odontoceti runs on an **uncertified** structured DAG. Per round, each
block carries `n − f` references to distinct-author blocks of the
previous round, one of them the author's own previous block (the
mandatory self-parent). Every round proposes leaders (ranked,
round-robin in the thesis), and the wave proposing at round `r` decides
at round `r+1`:

- A round-`(r+1)` block **supports** a leader block `L` at `r` if it
  references `L` as a parent, and **blames** it otherwise. Support and
  blame are *direct-parent* facts — there is no certificate round.
- **Direct commit**: `n − f` distinct authors support `L` at `r+1`.
- **Direct skip**: `n − f` distinct authors blame `L` at `r+1`.
- **Indirect rule**: an undecided leader looks for an **anchor** — the
  nearest committed-or-undecided leader at rounds `≥ r+2`; if the
  anchor is undecided, the leader stays undecided; if committed, the
  leader commits iff the anchor's causal history carries `n − 3f`
  distinct authors of support blocks for it (`ThickLink`), else skips —
  committing the **canonical** candidate when several pass (§6).
- Leader equivocation is handled per candidate block: every block
  authored by the slot's leader is evaluated against the same rule.

Out of scope, as always: the `2Δ` proposal timeout and the
early-production optimisation (network layer — `Delivery` and
`EventuallyDelivers` are where their effects enter the model), and
performance claims.

## 2. The reuse boundary

**Odontoceti's quorums are `n − f`.** At `n = 5f+1`, the DAG quorum
`4f+1` and both direct thresholds *are* `n − f` — precisely the shape
the whole development is parameterised at. Its validity rules match
`ValidWrt` clause for clause (`predecessor`, `distinct_creators`,
`quorum` at `n − f`, `self_parent` — the thesis mandates the
self-parent this development added as S10), and its support/blame
primitives *are* the existing `supporters`/`blames`. Consequently the
entire DAG layer is **reused verbatim**: `Block`, `BlockUniverse`,
`View`, `history`/cones, the counting layer, `Slots` (multi-leader
support is free — the rule layer is slot-indexed through the same
schedule class), `IsLeaderBlock`, `Delivery`/`viewUpto`,
`Populated`/`Synchronised`/`EventuallyDelivers`/`DeliversQuorum`/
`Live`, and `FairRunOn`. The witness file proves the reuse claim as a
computation: `Uodo`, a quorum-5 universe over six validators, satisfies
the untouched `BlockUniverse` by `decide`.

**The fault bound is an extension, not a replacement.**
`Faults5 extends Faults` with `card_validators5 : 5f+1 ≤ n`, so a
`Faults5` instance *is* a `Faults` instance and every existing theorem
applies to the same types; the stronger bound is consumed only where
the two-round arithmetic needs it (O2 and O4′, and nowhere else).

**Mirrored, not reused — the eligibility-indexed liveness
combinatorics.** `SpansEligible` and the committed-run/fair-run lemmas
induct over the decision relation, so their Odontoceti versions are
re-proved in the new directory with the same proof shapes. The
alternative — refactoring Mysticeti's `Decided` to be
rule-parameterised so they could be literally shared — was rejected
because it would rewrite `Mysticeti.lean`; the DAG layer stayed
read-only, and the diff against the pre-Odontoceti tree confirms it:
every change is inside `LeanDag/Odontoceti/`, `LeanDagTest/Odontoceti/`,
and two prose files.

**Naming.** Everything lives in `namespace LeanDag.Odontoceti` under
plain names (`Odontoceti.DirectCommit`, `Odontoceti.Decided`, …);
qualification disambiguates from the Mysticeti layer.

## 3. The rule layer (`Rules.lean`)

```lean
class Faults5 (Validator) extends Faults Validator where
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator

def DirectCommit (U) (L) (r) : Prop :=
  (Fintype.card Validator - F.f) ≤ (supporters U L (r + 1)).card

def DirectSkip (U) (L) (r) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blames U L (r + 1)).card

/-- Authors of decision-round support blocks for `L` in `A`'s cone. -/
def coneSupports (U) (A L) (r) : Finset Validator :=
  creatorsOf U.block ((blocksAt U (r + 1)).filter
    (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A))

def ThickLink (U) (A L) (r) : Prop :=
  (Fintype.card Validator - 3 * F.f) ≤ (coneSupports U A L r).card
```

`ThickLink` counts **distinct authors** of in-cone support blocks, not
raw blocks. The thesis says "2f+1 supports in the history of the
anchor" without disambiguating; an equivocating supporter can plant any
number of support-twins in one cone, so the block count is
adversary-inflatable, and the author count is the one the arithmetic on
both sides actually bounds (O2 gives `≤ 2f` authors, O3 gives
`≥ n − 3f` authors). All rule predicates are decidable, which is what
lets every witness run by `decide`.

**The arithmetic core — where each `f` is needed.** Four counting
theorems carry the entire safety story; each is sharp at the boundary:

- **O1** (`not_directSkip_of_directCommit`): no block is both directly
  committed and directly skipped. Two `n−f` quorums over `n` authors
  share `n−2f ≥ f+1`; an author both supporting and blaming has two
  decision-round blocks, so all of them are equivocators
  (`not_correct_of_supports_and_blames`, via `no_equivocation`) — one
  too many. **Needs only `n ≥ 3f+1`**: commit-versus-skip is not where
  the larger committee is needed.
- **O1′** (`eq_of_directCommit`): two directly committed same-author
  blocks are equal. Same intersection; an author supporting two
  distinct twins is an equivocator, because one block cannot reference
  both (`distinct_creators`) and two supporting blocks are an
  equivocation (`not_correct_of_supports_two`). Also at `n ≥ 3f+1`.
- **O2** (`card_supporters_le_of_directSkip`,
  `not_thickLink_of_directSkip`): a directly skipped leader's
  supporters — anywhere in the universe, hence in any cone — number at
    most `2f`, and `2f < n−3f` exactly when `n ≥ 5f+1`. **This is where
  the fifth `f` is needed.** The proof needs the **exact complement
  identity** `|Correct| = n − |byzantine|`
  (`card_correct_add_byzantine`): correct supporters and correct
  blamers are disjoint, correct blamers number
  `≥ (n−f) − |byzantine|`, and the `|byzantine|` cancels, leaving
  correct supporters `≤ f`. Bounding `|Correct| ≤ n` instead degrades
  the estimate to `3f`, which is *not* below the threshold at the
  boundary — the naive bounding fails, the exact one works — a trap the
  design review identified before the proof was attempted.
- **O3** (`thickLink_of_directCommit` — the heart): if `L` is directly
  committed, **every** block from two rounds above it on — Byzantine
  authors included, validity is structural — carries `≥ n−3f` distinct
  authors of support blocks in its cone. One hop: a round-`(r+2)`
  block's `n−f` distinct-author parents meet the `n−f` supporters in
  `n−2f` authors, of whom up to `f` are Byzantine equivocators whose
  *referenced* parent may be a non-supporting twin — the honest
  `≥ n−3f` remainder's unique decision-round block is both supporting
  and in the cone. Depth: cones are monotone through any single parent
  (`coneSupports_subset_of_reaches`), so the bound never decays. Every
  anchor's cone *is* the certificate — the two-round replacement for
  Mysticeti's M2/M4.
- **O4′** (`eq_of_directCommit_of_thickLink`): a directly committed
  block is the **only** same-author block that can pass the indirect
  test, at any anchor: `n−f` supporters of `L₁` and `n−3f` in-cone
  supporters of a twin `L₂` would overlap in `≥ n−5f ≥ 1` correct
  authors, each supporting two twins — impossible. The other place
  `n ≥ 5f+1` bites, and the replacement for Mysticeti's M5′ in every
  direct-versus-indirect crossing. It has no analogue in the thesis,
  and §6 is why it had to exist.

## 4. The decision relation (`Decision.lean`)

Eligibility at wavelength two: `decisionRound k = slotRound k + 1`,
`Eligible k j ↔ slotRound k + 2 ≤ slotRound j` (`eligible_iff`) — a
predicate on the slot pair alone, which is what lets the agreement
induction match two validators' premises against each other. The
view-relative direct rules (`DirectCommitIn`/`DirectSkipIn` over
`supportersIn`/`blamesIn`) are monotone into the universe level — a
view can only under-report — and the safety lemmas lift accordingly
(`not_directSkipIn_of_directCommitIn`, `eq_of_directCommitIn`,
`thickLink_of_directCommitIn`, `not_thickLink_of_directSkipIn`,
`eq_of_directCommitIn_of_thickLink`).

`Decided U V k v` mirrors Mysticeti's relation constructor for
constructor — direct commit; direct skip quantified over all candidate
blocks (vacuously true for an absent leader); indirect commit and
indirect skip through the **nearest eligible** anchor, with the
intermediate premise stated positively over eligible slots — plus one
new element:

```lean
| indirectCommit :
    k < j → Eligible Validator k j → Decided U V j (some A) →
    (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
    IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
    (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) → ¬ L' < L) →
    Decided U V k (some L)
```

The last premise — the committed candidate is the `≤`-least one passing
the test at the anchor, under `[LinearOrder BlockId]` — is the
canonicity discussed in §6.

## 5. Safety (O5, O6)

**`agree` (O5; thesis Lemma 5), in `Carrier.lean`.** No two validators reach
conflicting decisions for a slot. Structural induction on the first
derivation, in exactly the M6 shape:

- the **direct/direct** diagonal closes by O1 (commit vs skip) and O1′
  (commit vs commit);
- every **direct/indirect crossing** closes by counting: a direct skip
  refutes any `ThickLink` (O2); a direct commit passes `ThickLink` at
  every eligible anchor (O3 + `anchor_round_le` — the engine case) and
  is the *unique* candidate that can (O4′), so an indirect commit at
  any anchor must name the same block;
- the one real case, **indirect against indirect**, closes by the
  anchor trichotomy: an earlier anchor is covered by the *other*
  validator's intermediate-skip premise (which is why the premise must
  be positive and eligibility view-independent), and a shared anchor —
  forced equal by the induction hypothesis — yields a shared verdict:
  skip-vs-commit by the skip's `∀`-premise, commit-vs-commit by
  **canonicity**, the step the thesis takes silently.

**`safety` (O6).** Two committed blocks for one slot are equal, across
any views and any routes.

## 6. Findings: what the formalization surfaced in the thesis

Four items, ranked by severity — one consensus-critical gap, one
missing lemma, one consequential ambiguity, one proof-precision issue —
followed by what was confirmed sound. The first is the one place the
formalization diverges from the thesis by *necessity* rather than
generalization, and the design review had flagged the risk in advance.

### F1 — agreement needs a canonical candidate (consensus-critical)

The thesis's Lemma 5 proof handles the indirect/indirect case by
arguing both validators use the same anchor and "the indirect decision
rule solely depends on the causal history of the anchor". That is true
of the *test* — but the rule must also **choose a candidate**, and
nothing in the quorum arithmetic prevents two equivocating candidates
from both passing the test at one anchor. The counting that would be
needed — two `n−3f` in-cone supporter sets overlapping in more than the
`f` equivocators — requires `2(n−3f) − f > n`, i.e. `n > 7f`, which
**fails** at `n = 5f+1`. And the configuration is realisable:
`utwin6_both_pass` exhibits, on a valid six-validator universe, a
Byzantine leader's two round-0 twins each gathering exactly three
supporters (disjoint correct pairs plus the equivocator's own split),
and a round-3 block against which **both twins pass `ThickLink`** — by
`decide`. An `∃`-style indirect commit rule would admit derivations
committing either twin: agreement would be *false*.

What actually arbitrates in the protocol is the iteration order of
`GetLeaderBlocks` — the implementation commits the first passing
candidate it examines, and every honest implementation examines
candidates in the same (unspecified, but deterministic) order. The
formalized rule states that determinism as mathematics: `indirectCommit`
commits the **least** passing candidate in a `[LinearOrder BlockId]`
(hash order, in an implementation), and with that premise agreement is
a theorem. The premise is needed *exactly* where the thesis is silent:
O4′ shows a **directly** committed block is the unique candidate
passing the test anywhere, so all other pairings close by counting, and
canonicity is consumed only in the indirect-vs-indirect, shared-anchor,
equivocating-leader corner.

For implementers the finding reads: **the candidate-iteration order of
the indirect rule is consensus-critical.** Two honest nodes iterating
`GetLeaderBlocks` in different orders (e.g. arrival order) can commit
different blocks for the same slot at `n = 5f+1`. Any fixed order
shared by all nodes (block hash is the natural one) restores agreement;
"first seen" does not.

### F2 — a missing lemma in the safety argument

The thesis's lemma set covers commit-vs-skip (Lemma 1),
skip-vs-indirect-commit (Lemma 2), propagation (Lemma 3), and
commit-vs-indirect-**skip** (Corollary 4) — but not *direct commit
versus indirect commit of a different candidate*, and Lemma 5's case
analysis silently assumes that crossing closes. It does, but it needs
its own counting lemma: **O4′** (`eq_of_directCommit_of_thickLink`) —
a directly committed block is the unique same-author block that can
pass the indirect test at any anchor, by
`(n−f) + (n−3f) − f > n ⟺ n ≥ 5f+1`. The inequality is one of the two
places the five-`f` committee is genuinely required, which is a sign the
lemma is essential rather than routine.

### F3 — "2f+1 supports" is ambiguous, and only one reading is provable

The thesis counts "supports in the history of the anchor" without
saying whether it counts support *blocks* or their *distinct authors*.
The difference is adversarial: an equivocating supporter can plant any
number of support-twins in one cone, so the block count is inflatable
and the skip-side bound (Lemma 2 / O2) fails for it. The author count
is the reading for which both sides of the arithmetic go through — O2
bounds it above by `2f`, O3 bounds it below by `n−3f` — and it is what
`ThickLink` counts (§3).

### F4 — Lemma 2's counting is loose as written

The thesis's "honest supporters ≤ f" step reasons as if exactly `f`
validators are Byzantine. The bound is correct for **any** actual
Byzantine count `b ≤ f`, but only via the exact complement identity
`|Correct| = n − |byzantine|`, in which `b` cancels
(`card_supporters_le_of_directSkip`, §3); the natural loose bounding
`|Correct| ≤ n` yields `3f`, which does **not** clear the `n−3f`
threshold at the boundary. The result stands; the written argument does
not quite prove it as stated.

### What was confirmed sound

Everything else. The two-round direct rules, the propagation lemma
(Lemma 3 / O3), the skip-side arithmetic, the two-consecutive-leaders
liveness structure (Lemmas 8–11 / O7–O9), and the
self-parent/distinct-author validity rules all check out — and more:
they hold at the generalization `n ≥ 5f+1` with thresholds `n−f` /
`n−3f`, which the thesis does not claim. The core design is right; the
gaps sit in the safety argument's equivocation corners, which is
exactly where hand proofs about uncertified DAGs tend to be thinnest.

## 7. Liveness (O7–O10)

- **O7** (`directCommit_of_leader_mem`, `decided_of_leader_mem`,
  `decided_of_correct_leader`; thesis Lemma 8 + Corollary 9). Post-`R`,
  a correct-led slot commits **directly**: `SynchronisedOn` makes every
  correct decision-round block reference the leader's block in one
  step, and `Correct` carries a quorum. **Two populated rounds**
  (propose and decide) against the Mysticeti analogue's three — the
  protocol's latency advantage, visible as a shorter hypothesis list.
  The decision-valued forms conclude on any view caught up to the
  decision round (`View.CoversUpto`, `directCommitIn_of_coversUpto`) —
  the supporters sit one round above the leader, so a caught-up view
  holds them; the full view is the special case
  (`View.coversUpto_full`).
- **O8** (the generic `AnchoredRule.SpansEligible`; thesis Lemma 10's
  content). Under a pipelined identity-round schedule, a run of **two**
  consecutive committed slots spans eligibility for everything below:
  a slot cannot anchor on the round immediately above it
  (`Eligible k j ↔ slotRound k + 2 ≤ slotRound j`), but the second
  slot of the run clears the bound. This is exactly why the thesis
  needs two consecutive honest top-ranked leaders.
- **O9** (the generic `Common/Anchored/Bounded.lean` theorem
  `decided_below_of_committed_run`; thesis Lemma 11). A
  committed run of eligible span clears every slot below it: the
  nearest-eligible-committed-anchor induction, with the indirect
  commit taking the `Finset.min'` of the passing candidates — the
  constructive face of the canonicity premise.
- **O10** (`OdontocetiProperties.all_decided_below_of_fairRun`,
  `all_decided_below_of_fairRun_correct`, in `Odontoceti/Properties.lean`;
  thesis Theorem 12). The
  composition, under enforceable hypotheses only: `Live`,
  `DeliversQuorum`, `SynchronisedOn`, and a `FairRunOn` run of `c`
  correct-led slots placed past both the target and `R` by fairness —
  concluding on any view caught up to the horizon. The horizon asks
  for rounds up to the run's `slotRound + 1` — one round fewer than
  Mysticeti's `+ 2`, the latency advantage again.

**The schedule fact is hypothesized, not derived** — liveness takes
"runs of two consecutive correct-led slots recur" as `FairRunOn`, in
house style. The thesis derives it from round-robin over a `2f+2`
window; that derivation is about one concrete schedule, separable from
the consensus argument, and remains available as a self-contained
extension touching nothing else.

## 8. Witnesses (`LeanDagTest/Odontoceti/Model.lean`)

Everything runs at the boundary `n = 6, f = 1`: `Validator = Fin 6`,
Byzantine `{0}`, quorum `5`, indirect threshold `3` — the thesis's
`4f+1` and `2f+1` exactly. Schedule: `uniformSingle 1` with round-robin
leaders (slot `k` at round `k`, leader `k % 6`).

- **`Uodo`** (`Fin 24`, four full rounds): validity by `decide` — the
  untouched `BlockUniverse` accepts the Odontoceti parameters, the §2
  reuse claim as a computation. Slot 1 commits directly with all six
  supporters; O7 applied commits slot 2 from `uodo_populated` and
  `uodo_synchronised`; O8 applied (`SpansEligible`).
- **`Uskip`** (`Fin 36`, six rounds — the decision zoo, all four
  `Decided` constructors on one universe): slot 0's Byzantine leader is
  **directly skipped** — five blames, exactly the quorum, with author 0
  pinned to support by its own mandatory self-parent
  (`uskip_slot0`); slot 1 splits 3–3 (neither direct rule fires) and is
  committed **indirectly** through the slot-3 anchor with
  `coneSupports` exactly `{1,2,3}` — `ThickLink` tight at the threshold
  (`uskip_slot1`); slot 2 splits 2–4 and is **indirectly skipped**
  through the slot-4 anchor — two supporters cannot reach three in any
  cone (`uskip_slot2`); slots 3 and 4 commit directly and form the
  committed run to which O9 applies, deciding every slot below.
- **`Utwin6`** (`Fin 25` — the §6 finding on data): the Byzantine
  leader's round-0 twins with supporters `{0,1,2}` and `{3,4,5}`;
  `utwin6_both_pass` — both twins pass `ThickLink` against the
  round-3 block that sees all of round 1; at the slot's *actual*
  anchor (slot 2, whose cone misses one support of the second twin)
  only the canonical twin passes, and `utwin6_slot0` commits it.

All witnesses are by `decide`; all proofs use the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) only.

## 9. Decisions, deviations, and what remains

**Decisions, as they played out:**

- **The generalization** — `n ≥ 5f+1`, thresholds `n−f` / `n−3f` —
  **held everywhere**; the pinning fallback was never used. What the
    general form says that the thesis's fixed `5f+1` does not: the
  five-`f` committee is required in exactly two places (O2's
  skip-vs-indirect bound and O4′'s commit-vs-rival bound), the direct
  rules are sound already at `3f+1`, and at the boundary the indirect
  threshold's window is the single value `2f+1`.
- **`ThickLink` counts distinct authors** — confirmed as the provable
  reading: O2 and O3 bound the author count from both sides; the raw
  block count is adversary-inflatable.
- **The schedule fact is hypothesized** (`FairRunOn`), with the
  round-robin derivation separable and undone.
- **The DAG layer stayed read-only** — the constraint held to the
  letter; the only files touched outside the new directory are this
  document and `related.md` (whose earlier claim that Odontoceti's
  quorums are not `n−f` was wrong, and is corrected).

**The deviations that are contributions** (§6): the canonicity premise
on `indirectCommit` and the O4′ lemma have no counterparts in the
thesis; without the former, agreement is refutable on data, and without
the latter, its proof does not close. Worth communicating upstream,
together with F3/F4.

**What remains, optionally:** deriving the run-recurrence from a
round-robin schedule definition (thesis Lemma 10's `2f+2`-window
argument); multi-leader witness instances (the theorems are already
schedule-generic); and the reconfiguration/DoS/GC layers of this
development, which apply to any universe — including these — but whose
Odontoceti-specific instantiation was not this arc's concern.

## 10. Where everything lives

| module | contents |
|---|---|
| `LeanDag/Odontoceti/Rules.lean` | `Faults5`; `DirectCommit`/`DirectSkip`/`coneSupports`/`ThickLink`; the arithmetic core O1, O1′, O2, O3, O4′ |
| `LeanDag/Odontoceti/Decision.lean` | `decisionRound`/`Eligible`; the view layer; `Decided` with the canonicity premise; `safety` (O6) |
| `LeanDag/Odontoceti/Liveness.lean` | O7 (`decided_of_leader_mem`), O8 (`AnchoredRule.SpansEligible`) |
| `LeanDag/Odontoceti/Carrier.lean` | O5 (`agree`) |
| `LeanDag/Odontoceti/Properties.lean` | O9 (the generic `decided_below_of_committed_run`), O10 (`all_decided_below_of_fairRun`) |
| `LeanDagTest/Odontoceti/Model.lean` | the boundary instance; `Uodo`, `Uskip`, `Utwin6`; every rule and all four `Decided` constructors witnessed by `decide`, including `utwin6_both_pass` |
