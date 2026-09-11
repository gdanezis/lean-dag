# The common layer: what is shared, what is restated, and what is left to share

A study of the tree after the unification of §11.29 and the move of
§11.30 (`docs/target-properties.md`). Every rule is now an instance of
one decision relation, and the substrate sits in `LeanDag/Common/`. This
document asks four questions of the result and answers each with file
references, so the answers can be checked and the work ordered.

1. Which properties are still proved per rule that the common layer could
   derive once — the causal, counting and leader facts in particular.
2. Which of the arcs that instantiate every rule — Adaptive and Barnacle —
   could be proved once over the relation.
3. What is the minimal content that distinguishes each rule, and can it
   be written in a few lines a reader can review.
4. Which proofs repeat in shape across rules, and what one theorem plus
   what obligation would replace each family.

Line counts are from the tree at `243db27` (the merge of PR 18). Where a
number is an estimate of lines removed it is marked as such.

| directory | lines | | directory | lines |
|:--|--:|:--|:--|--:|
| `FinWhale/` | 6483 | | `Integration/` | 2751 |
| `BlackMarlin/` | 4979 | | `MahiMahi/` | 2610 |
| `Barnacle/` | 4901 | | `Hybrid/` | 2407 |
| `Common/` | 4756 | | `Adaptive/` | 1480 |
| `Hydrozoan/` | 4585 | | `Odontoceti/` | 1189 |
| `Properties/` | 4275 | | `Nemo/` | 1160 |
| `Mysticeti/` | 4054 | | `OptimalHydrozoan/` | 3685 |

## 1. The rule cards

Each instance of `AnchoredRule` (`Common/Anchored.lean:141`) is six
fields: `waveAt`, `Commit`, `Skip`, `rungs`, `Link`, `tie`, plus the record
it reads and the invariant `I` its laws need. The table gives the eight
instances in those terms. Thresholds: `n − f` is `quorumCard`; Hybrid's
`q = n − (fb + fc)`; Hydrozoan's `p, q, qFast, qCert, qSlow, qWeak` are
in `Hydrozoan/Model/Faults.lean:69–94`; Optimal's `qFastOpt`,
`tPlain`, `tEquiv` in `OptimalHydrozoan/Model/Faults.lean:55–80`;
FinWhale's `spQuorum = 2f + p`, `fastCard = n − p` in
`FinWhale/Model/Params.lean:75–80`.

| rule | record, validity, honest | wave | Commit (on the view) | Skip | rungs, Link | tie | `I` |
|:--|:--|:--|:--|:--|:--|:--|:--|
| core `Mysticeti/Rule.lean:438` | core record, `ValidWrt`, `Correct` | 2 | `n−f` certifiers at `r+2`, each with `n−f` votes | `n−f` blamers of the slot at `r+1` | 1: `CertifiedIn` | none | — |
| Nemo `Nemo/Decision.lean:67` | `Nemo.Universe`, `Nemo.ValidWrt`, everyone | 1 | `majority` supporters at `r+1` | none (`False`) | 1: `CertifiedIn` over `history` | none | — |
| Odontoceti `Odontoceti/Decision.lean:119` | core record | 1 | `n−f` supporters at `r+1` | core's `n−f` slot blamers | 1: `ThickLink` at `n−3f` cone supporters | `<` | — |
| Hybrid `Hybrid/Decision.lean:168` | core record via `HybridFaults.toFaults` | 1 | `q` supporters at `r+1` | `q` slot blamers | 1: `ThickLink k` | `<` | `HonestNoEquiv` |
| Mahi-Mahi `MahiMahi/Model/Decision.lean:87` | core record | `w−1` | `n−f` certifiers at `r+w−1`, votes are least-in-cone | `n−f` blamers of `(leader, round)` | 1: `CertifiedIn` at wave `w` | none | — |
| Hydrozoan `Hydrozoan/Model/Decided.lean:51` | Hydrozoan record, `NonByzantine` | 2 | `qFast` supporters ∨ `qSlow` certifiers with `qCert` votes | `qFast` slot blamers | 2: `CertifiedIn`; `WeakLinked` at `qWeak` | none; `<` | — |
| Optimal `OptimalHydrozoan/Model/Decided.lean:48` | Hydrozoan record at `OptUniverse` | 2 | `qFastOpt` supporters ∨ Hydrozoan's slow half | `qCert` blamers ∧ `qCert` no-evidence blocks | 2: `CertifiedIn`; `EvidenceLinked` | none; none | `LeaderExcluded` |
| FinWhale `FinWhale/Model/Decided.lean:31` | `Dag`, `ValidHere` with the leader clause, `Correct` | 2 | `fastCard` voters ∨ `spQuorum` SP-certificates, on `V.toRecord` | SP-skip of every slot block ∧ `spQuorum` non-FP-evidence | 1: SP-certificate in cone ∨ `spQuorum` FP-evidence in cone | `<` | — |

Black Marlin and Minnow are not instances. Black Marlin has no skip
verdict and no rung: an unadmitted anchor is recovered by causal
inclusion in a later admitted one (`BlackMarlin/Model/Decision.lean:10`).
Minnow's rule recurses over every earlier slot with a concurrency test on
a bespoke `Dag` (`Minnow/Model/Rule.lean:62,161`) and is left as it is.

### 1.1 The shared shapes

Reading the table by column:

- **Commit** is one of two shapes. *Supporters at `r+1` ≥ t*: Nemo,
  Odontoceti, Hybrid, and the fast halves of Hydrozoan, Optimal and
  FinWhale. *Certifiers at `r + wave` ≥ t, each with ≥ t′ votes*: the
  core, Mahi-Mahi, the slow halves of Hydrozoan and Optimal, and
  FinWhale's SP half. Six thresholds, two shapes.
- **Skip** is *slot blamers at `r+1` ≥ t* for five of eight (the core,
  Odontoceti, Hybrid, Mahi-Mahi, Hydrozoan). Nemo has none. Optimal and
  FinWhale conjoin a blame count with a second no-evidence count.
- **Link** is `∃ C ∈ certificates, Reaches U A C` for five rungs (the
  core, Nemo, Mahi-Mahi, Hydrozoan rung 0, Optimal rung 0), and
  *distinct authors of anchor-reachable round-`r+1` votes ≥ t* for three
  (Odontoceti, Hybrid, Hydrozoan rung 1).
- **tie** is empty or `<`. **`I`** is trivial for six rules.

Six combinators, each taking a threshold and where needed a round offset,
would write six of the eight instances in three or four lines each:

```
supportCommit (t)          -- t ≤ |supportersIn U V L (r+1)|
certCommit    (t t' off)   -- t ≤ |creatorsOf (certificatesAt t' off U L r ∩ V.ids)|
blameSkip     (t)          -- t ≤ |creatorsOf (slotBlamers U k ∩ V.ids)|
certifiedLink (t' off)     -- ∃ C ∈ certificatesAt t' off U L r, Reaches U A C
coneLink      (t)          -- t ≤ |coneSupports U A L r|
noSkip
```

Odontoceti and Hybrid then differ only in two thresholds and the
invariant; the core and Mahi-Mahi in the offset and the vote relation.

### 1.2 The residue: what genuinely distinguishes each rule

This is the list a reviewer should read. Everything not on it is a
threshold, an offset, or a choice among the six shapes.

1. **Mahi-Mahi's vote** (`MahiMahi/Model/Rules.lean:79`): a vote for `L`
   is not `L ∈ refs` but "`L` is the least block of its author and round
   in the voter's cone". `certCommit` and `certifiedLink` need a vote
   relation as a parameter; that parameter is Mahi-Mahi.
2. **Optimal's fast evidence** (`OptimalHydrozoan/Model/DirectRules.lean:87`):
   a case split on `WitnessesEquivocation` with a negative clause on every
   rival. Not a count. It is why Optimal's second rung has no tie.
3. **Optimal's skip and FinWhale's skip** are conjunctions of a blame
   count and a no-evidence count at another round.
4. **FinWhale's FP evidence** (`FinWhale/Model/Rule.lean:204`): an `if` on
   `ExposesEquivocationBy` with two thresholds; and its single rung packs a
   certificate link and an evidence link as a disjunction.
5. **FinWhale evaluates on `V.toRecord`** (`FinWhale/Model/Decided.lean:34`),
   not on `U ∩ V.ids`; every other rule intersects. A combinator built on
   `supportersIn` misses this by construction unless
   `supportersIn_eq_toRecord` (`Common/Support.lean:192`) is applied.
6. **Nemo's record**: `honest = univ`, `majority` for `quorumCard`, no
   direct skip. The crash model changes the record, not a threshold.
7. **Hybrid's `k`** is a rule parameter over an admissible interval, and
   its laws need `HonestNoEquiv`.
8. **Optimal's `LeaderExcluded`** is the only schedule-dependent invariant
   on the record; FinWhale expresses the same shape as a validity clause
   (`FinWhale/Model/Rule.lean:81`), which is the better home.

Proposal for review: each rule directory gets a `Rule.lean` of only the
instance written with the combinators, with the residue items above as
its only non-parameter definitions. The card table is then generated
from those files rather than written by hand.

## 2. Common derivations: what the substrate could prove once

### 2.1 Counting on a view: one combinator

Every direct rule is `t ≤ (creatorsOf U.block (s ∩ V.ids)).card` for some
counted set `s`. The consequences are proved per rule:

| family | sites | shape of every proof |
|:--|--:|:--|
| `_mono` in the view | 20 | `le_trans h (card_le_card (image_subset_image (inter_subset_inter …)))` |
| `_congr` across schedules | 17 | rewrite `slotRound k` and `leader k`, close with `isLeaderBlock_congr` (`Common/Anchored.lean:71`) |
| `_of_coversUpto` / `_full` | 14 | `s ∩ V.ids = s` when `V` covers the rounds of `s` |
| `Decidable` instances | 53 | `inferInstanceAs` |

Sites include `Hydrozoan/Helpers/DirectRules.lean:90–129`,
`OptimalHydrozoan/Helpers/DirectRules.lean:117–203`,
`FinWhale/View.lean:442–567`, `Hybrid/Decision.lean:150,157`,
`Mysticeti/Rule.lean:404,556`, `Nemo/Decision.lean:46,54`, and the five
verbatim `directCommitIn_of_coversUpto` at `Nemo/Liveness.lean:149`,
`Odontoceti/Liveness.lean:95`, `Hybrid/Liveness.lean:82`,
`Mysticeti/Liveness.lean:474`, `MahiMahi/Properties.lean:327`.

**Once (landed as step 2, `docs/target-properties.md` §11.32):**
`heldAuthors U V s` and the predicate `HoldsAtLeast U V t s` in
`Common/Support.lean`, with `HoldsAtLeast.mono` (grows only with the
view), `HoldsAtLeast.le` (bounded by what the record holds),
`HoldsAtLeast.full` (the full view holds everything) and
`HoldsAtLeast.of_coversUpto` (given the set's round bound), plus
`heldAuthors_band`/`holdsAtLeast_band` for the set's transport
(§4.3, `Common/Anchored/Band.lean`) and one `Decidable` instance.
Obligation per counted set: its members' rounds, its congruence, its
transport, and `0 < t`. Estimated removal: about 250 lines across seven
directories.

### 2.2 Quorum intersection: one lemma family

`Finset.card_union_add_card_inter` appears in 18 files. The intersection
lemma itself is written seven times: `Common/Validators.lean:166,179`,
`Common/Block.lean:158`, `Hydrozoan/Helpers/Counting.lean:118`,
`Hybrid/Faults.lean:125`, `Hybrid/Checkpoint/SafetyProofs.lean:58`,
`Nemo/Basic.lean:37`, `FinWhale/Counting.lean:49`. Every one is
`by_contra`, `A ∩ B ⊆ Bad`, `card_union_add_card_inter`, `card_le_univ`,
`omega`. The block-level consequence "two same-round sets whose author
counts sum past `n + m` share a block" exists once, at Hydrozoan's record
only (`Hydrozoan/Helpers/Counting.lean:146`).

The three lemmas of the same argument at any record with the distinct
creators clause are also copied: supports-two ⇒ faulty
(`Odontoceti/Rules.lean:168`, `Hybrid/Rules.lean:203`,
`BlackMarlin/Helpers/Rules.lean:39`, `Hydrozoan/Helpers/Counting.lean:67`),
equal under quorum support (`Odontoceti/Rules.lean:184`,
`Hybrid/Rules.lean:218`, `BlackMarlin/Helpers/Rules.lean:55`,
`Mysticeti/Rule.lean:226`), and no blame quorum against a support quorum
(`Odontoceti/Rules.lean:147`, `Hybrid/Rules.lean:182`,
`Mysticeti/Rule.lean:127`). `Common/Support.lean:403,426` already hold
two of the five in subset form.

**Once:** in `Common/` (a `Counting.lean`, or `Validators.lean`):
`exists_mem_inter_notMem (hbad : Bad.card ≤ m) (h : n + m < |A| + |B|)`,
its cardinality form, and `exists_common_block_of_thresholds` at any
record. Obligation per rule: one arithmetic row `n + m < t₁ + t₂` per
conflict pair, which `Hydrozoan/ThresholdArithmetic/Statement.lean`
already states as data. Estimated removal: about 250 lines, and
`OptimalHydrozoan/DirectSafety/Proof.lean` (160 lines) reduces to its
rows, since it differs from Hydrozoan's (181 lines) only in which row it
cites.

### 2.3 Hydrozoan shadows the substrate it sits on

Hydrozoan's record is a `BlockRecord` and its validity is `Mechanised`
(`Hydrozoan/Model/BlockUniverse.lean:42,53`), yet
`Hydrozoan/Model/DirectRules.lean:38,73,122` redefine `blocksAt`,
`supporters`, `supportersInView` character for character
(`Common/Support.lean:52,114,156`), `Hydrozoan/Helpers/Counting.lean:24,29`
re-prove `mem_blocksAt` and `mem_supporters`, and
`Hydrozoan/Helpers/CausalHistory.lean` (26 lines) is
`Common/BlockDag.lean:94`. The band helper then has to write
`LeanDag.Hydrozoan.blocksAt` to disambiguate, and `blocksAt_bnd`
(`Hydrozoan/Helpers/Banded.lean:59`) re-proves `blocksAt_band`
(`Common/Anchored/Band.lean:217`). Optimal inherits all of it.

**Once:** delete the shadows; Hydrozoan and Optimal read `Common`. About
250 lines, and this unblocks §2.1 and §4.3 for both.

### 2.4 Blames of a slot, and the certificate stack

`Common/Support.lean:137` blames a *block* (`L ∉ refs`). Three arcs blame
a *slot* (no candidate of the slot among the refs): `Mysticeti/Rule.lean:369`
`slotBlamers`, `MahiMahi/Model/Rules.lean:129` `blamers`,
`Hydrozoan/Model/DirectRules.lean:107` `blames`. One predicate-filtered
`blamesP` covers all three and the block form.

The certificate stack is copied five times: votes of a certificate
(`Mysticeti/Rule.lean:38`, `Hydrozoan/Model/DirectRules.lean:62`,
`FinWhale/Model/Rule.lean:169`, `OptimalHydrozoan/Model/DirectRules.lean:64`,
`MahiMahi/Model/Rules.lean:105`), `Certifies` at four thresholds,
`certificates` at three offsets, `certificatesIn` three times, and
`CertifiedIn` four times, of which the core's and Hydrozoan's are byte
identical (`Mysticeti/Rule.lean:242`, `Hydrozoan/Model/IndirectRules.lean:35`).

**Once:** a `Certified` section in `Common/Support.lean` over
`(vote relation, t′, offset)`. Estimated removal: about 200 lines.

### 2.5 Leaders: the blocks of a slot, and the schedule as identity

`IsLeaderBlock` is generic (`Common/Leader.lean`), with a generic
`Finset` form, `leaderBlocksAt`, alongside it. Its `Finset` form is
still written separately in places: `FinWhale/Model/Decision.lean:33`
`slotBlocks`, `MahiMahi/Model/Rules.lean:68` `candidatesAt`,
`BlackMarlin/Model/Rules.lean:70` `IsAnchor`,
`Minnow/Model/Rule.lean:110`, and inside `slotBlamers`.
Optimal-Hydrozoan's own copy is gone with the validity refactor
(`docs/optimal-hydrozoan.md`); it reads `leaderBlocksAt` at its
projection to Hydrozoan's record. Black Marlin's
`class Rotation` (`BlackMarlin/Model/Rules.lean:53`) is `Slots.identity`
(`Common/Slots.lean:116`). Hydrozoan's `votingRound`/`decisionRound`
(`Hydrozoan/Model/Slots.lean:30,34`) and Mahi-Mahi's
(`MahiMahi/Model/Rules.lean:53,59`) are `slotRound k + wave − 1` and
`AnchoredRule.decisionRound` (`Common/Anchored.lean:169`).

Nemo's `isLeaderBlock_unique` (`Nemo/Decision.lean:28`) has the generic
shape "the leader of `k` is honest ⇒ at most one leader block", which
every rule with a non-trivial tie uses implicitly.

**Once:** `leaderBlocksAt U k` with `mem_leaderBlocksAt ↔ IsLeaderBlock`,
`AnchoredRule.votingRound`, and `isLeaderBlock_unique_of_honest`, all in
`Common/Anchored.lean`; Black Marlin re-based on `Slots.identity`.
`LeaderExcludedAll` moves onto the `Clause` mechanism as FinWhale's
`leaderClause` already does, which retires the three preservation proofs
at `OptimalHydrozoan/Record.lean:42,93,139`.

### 2.6 Nemo's mirrors, FinWhale's restriction family, Minnow

- `Nemo/Support.lean:137` `reaches_pred_of_round_le` is a verbatim copy of
  `Common/Support.lean:315` and has no quorum content. `Nemo/Support.lean:52,90,104,119`
  are `Common/Support.lean:259,298,339,357` at `majority` and
  `honest = univ`; parameterising the Common four on the threshold and
  the honest set covers both. `Nemo/Basic.lean:124,128` are
  `Common/BlockDag.lean:90,94`. About 155 lines.
- FinWhale's `*_restrict` family (`FinWhale/View.lean:59–208`, about 160
  lines) states `X V.toRecord ⊆ X U`; `Common/Support.lean:192,205` state
  the same through `supportersIn`. Three Common lemmas
  (`blocksAt_toRecord_subset`, `supporters_toRecord_subset`,
  `blames_toRecord_subset`) erase three of them and shorten the other
  nine. `FinWhale/Model/Skip.lean:26` `nonVoters` is `blames`;
  `FinWhale/Evidence.lean:41` `causalStructure` is `D.causal`.
- Minnow's `Dag` is `BlockRecord` at `ValidHere`; `verticesAt`, `cone`,
  `Reaches`, `pointers`, `Quorum` would all vanish into Common. Recorded
  only; Minnow stays untouched.

### 2.7 Odontoceti is Hybrid at `fc = 0`

The two arcs are the same inventory at two thresholds:
`coneSupports` and its three lemmas (`Odontoceti/Rules.lean:90–111`,
`Hybrid/Rules.lean:125–146`) are identical; `ThickLink` is Hybrid's at
`k = kRel`; `card_supporters_le_of_directSkip` is the same forty lines
twice (`Odontoceti/Rules.lean:212`, `Hybrid/Rules.lean:245`); the
`Decision`, `Properties`, `Liveness` and `Carrier` files pair line for
line. `Hybrid/Conservativity.lean:29–86` already proves the collapse and
its docstring says the bodies are syntactically the same, but nothing is
deleted on the strength of it. Odontoceti's own content is `Faults5`
(`Odontoceti/Rules.lean:45`) and the `n ≥ 5f + 1` arithmetic.

**Once:** Odontoceti becomes the Hybrid instance at `fc = 0, k = kRel`,
with `HonestNoEquiv` discharged by `Hybrid/Conservativity.lean:51`.
Estimated removal: about 1100 lines. This is a design decision as much as
a deletion: the report presents Odontoceti as the published two-round
rule and Hybrid as its generalisation, and the presentation can stay that
way with the Lean pointing the other direction.

## 3. Adaptive and Barnacle: prove once

### 3.1 Adaptive

The mechanism is already generic over `Properties.DagRule` and named
properties (`Adaptive/Run.lean:98` `partialRun_agree`,
`Adaptive/Liveness.lean:174` `run_exists`, `Adaptive/Joiner.lean:140`),
with `Live` a bare parameter. The per-rule files:

- `Adaptive/Odontoceti.lean` (291 lines, since deleted) **did not use
  it**. It re-declared the run types, re-proved the
  strong induction (`:86`), the epoch closure (`:132`), the run
  construction with its `dif` splicing (`:185`) and the diagonal gluing
  (`:256`), against `AnchoredRule.DecidedWithin` where the generic
  mechanism speaks `Properties.DecidedBelow`. One bridge,
  `DecidedBelow R.toDagRule S B V k v ↔ R.DecidedWithin U V B k v`,
  turns it into the 60 lines of corollaries that `Adaptive/Mysticeti.lean`
  already is. About 230 lines.
- `Adaptive/Mysticeti.lean:151,162` and `Integration/AdaptiveHydrozoan.lean:43,70`
  duplicate `spansEligible_slotsOf` (proof `h`) and `descends_slotsOf`;
  both belong in `Adaptive/Basic.lean`. `Adaptive/Mysticeti.lean:68` and
  `Adaptive/Odontoceti.lean:38` are the same wrapper around
  `decidedWithin_congr_of_slotRound` (`Common/Anchored/Bounded.lean:167`).
- The five theorems at `Adaptive/Mysticeti.lean:170–265` all build the
  rule's `Live` record at `slotsOf` from global hypotheses and finish with
  `S.mono` and `omega`; one "global ⇒ staged" combinator per rule
  replaces them (about 100 lines to 20).

An `Adaptive.ofAnchored (R) (hl : R.Laws) (hleast) (hspans) …` needs no
new field on the relation: `Agree`, `Banded`, `Indirect` and `Descends`
come from `Common/Anchored/Band.lean:87,505,120` and
`Properties/Derived/Descent.lean:94`. Each rule then supplies `hleast`,
its `Live` and the staged-live lemma, and `Persist` for growth.

**What landed (step 8) took a different shape than this bundled call.**
There is no `Adaptive.ofAnchored`; instead `Adaptive/Policy.lean` states
`Adaptive.Policy` over any `Properties.DagRule`, and `Adaptive/Basic.lean`
holds the shared lemmas this section asks for (`descends_slotsOf` among
them). The per-rule files are gone entirely: each
statement of the arc was a corollary of the generic theorem at that
rule's carrier, so the mechanism is read at the generic theorems and no
rule restates it.

### 3.2 Barnacle

Every generic theorem consumes `Properties.*` only (`Barnacle/Model/Rule.lean:121`
records that two `Laws` fields have no consumers). The eight per-rule
instantiations (1466 lines over 22 files) repeat five parts:

| part | copies | what varies |
|:--|--:|:--|
| `BaseRule.Laws` (`full_ids`, `historyView_ids` by `rfl`; `agree`, `commitsDirect`, `commitsCandidate` by the rule's properties) | 8 | the invariant argument (`hk`, `hw`) |
| `goodOf` bridge, a re-tupling of `∃ T, … ∧ SynchronisedOn ∧ PopulatedOn` | 8, four byte identical | one `omega` on the threshold |
| `LiveRule.Descent` as one application of `descent_of_support` (`Barnacle/Helpers/Descent.lean:65`) | 8 | the `Support` and the wave inequality |
| history view is reference-closed | 4 | nothing |
| `RoundRobinLive` | 8 | one inequality `waveLength · slack + 1 ≤ n` from the fault class |

`Common/Anchored/Band.lean:87,105,109` already prove the three
non-trivial `Laws` fields over any `AnchoredRule` with `Laws`, and
`Band.lean:120` gives `Indirect`. So `Barnacle.ofAnchored (R) (hl) (hleast) (sp : Support) …`
produces `BaseRule` (with `full := View.full`, `historyView` from the
record's `CausalStructure`, `waveLength := R.waveAt 0 + 1`, which matches
`LiveRule.elig` at `Barnacle/Helpers/Descent.lean:46`), `BaseRule.Laws`
and `LiveRule.Descent` for every rule at once. Each `Statement.lean`
shrinks to the carrier, the `Support` and one inequality; each
`Proof.lean` to one application. Adding `rel : Reliability` to `LiveRule`
and defining `Good := GoodOf toDagRule rel` makes the eight `goodOf`
bridges the identity. `historyView_of_causalStructure` once removes the
four closure proofs. The two dead `Laws` fields go. Estimated removal:
about 700 of the 1466 lines.

**What landed (step 9, `docs/target-properties.md` §11.36) is not one
bundled call.** `Barnacle.ofAnchored R` (`Barnacle/Model/Anchored.lean`)
builds the `BaseRule` alone; `ofAnchored_laws` proves the laws
separately, from `Common/Anchored/Band.lean`'s agreement, candidate and
direct-commit properties; `descent_of_support` (renamed from
`descent_of_properties`, §11.36) is its own call at the rule's support.
Three departures from this plan: `Good` stays a field of `LiveRule`
rather than gaining a `rel` field, so `LeanDagTest/Barnacle/Progress.lean`
can still pin one universe; the two view laws (`full_ids`,
`historyView_ids`) stay in `Laws` rather than going, since nothing else
constrains those fields; and `GoodOf` is renamed `Timed.Good`
(`Timed/Coverage.lean`), not merely redefined. Otherwise the shape
matches: `historyView` comes from `BlockRecord.historyView`, not a
closure proof rebuilt per rule.

## 4. Proof shapes that repeat

### 4.1 The liveness chain

Every chain is four links: (a) a reliable set of size `t` at round
`r + wave` whose blocks all certify `L` meets the commit threshold; (b)
coverage after `SynchronisedOn` gives (a)'s premise; (c) a view covering
`r + wave` sees the commit; (d) a run of `c` commits with `SpansEligible c`
decides everything below. Links (b) and (d) are generic today
(`Timed/Coverage.lean:94,116,135`, `Common/Anchored/Bounded.lean:319`).
Link (c) is §2.1's `HoldsAtLeast.of_coversUpto`. Link (a) is the one per-rule
fact.

Yet the chain is assembled by hand in two families. Nemo, Odontoceti and
the core go through `Timed.decidedBelow_of_fairRun` with a three-line
wrapper (`Nemo/Properties.lean:213`, `Odontoceti/Properties.lean:328`,
`Mysticeti/Properties.lean:940`). Hybrid (`Hybrid/Liveness.lean:136`, 31
lines), Hydrozoan (`Hydrozoan/Helpers/EventualDecision.lean:37`), Optimal
(`OptimalHydrozoan/EventualDecision/Proof.lean:30`, line for line
Hydrozoan's), Mahi-Mahi (`MahiMahi/Helpers/Liveness.lean:62`) and Black
Marlin (`BlackMarlin/Helpers/Liveness.lean:129`) each open-code the
`S.unbounded`, `max`, `Nat.add_sub_cancel'` block and finish with
`decided_below_of_committed_run`. `directCommit_of_leader_mem` and
`decided_of_leader_mem` are written four times each
(`Nemo/Liveness.lean:129,162`, `Hybrid/Liveness.lean:63,95`,
`Odontoceti/Liveness.lean:81,108`, `Mysticeti/Liveness.lean:433,508`)
and duplicate `Timed.exists_decided_of_coverage`.

**Once:** `AnchoredRule.decided_below_of_run (hleast) (hc) (hspan) (hrun) (commit)`
in `Common/Anchored/Bounded.lean`, with `commit` the link-(a) fact; and
the four rules not yet on `Support` + `Timed` migrated. The
`AnchoredRule.Total`/`DecidedBelowRun` statements of Hydrozoan and Optimal
(`Hydrozoan/IndirectLiveness/Statement.lean:45`, its Optimal twin, with
byte-identical eight-line proofs) become one statement over `R`, read at
dot notation (`(hydrozoanAnchored ..).Total`) rather than a standalone
`AnchoredTotality` name. Estimated removal: about 300 lines.

Where the chains genuinely differ is in the hypotheses, not the proof:
Nemo needs `FairRunOn T 2` because it has no direct skip; Mahi-Mahi takes
`good` as given; FinWhale's liveness lives in block creation
(`FinWhale/Creation.lean`); Black Marlin is round-indexed.

### 4.2 `exists_least` and the tie

Seven `exists_least` theorems (`Mysticeti/Rule.lean:616`,
`MahiMahi/Helpers/Decision.lean:151`, `OptimalHydrozoan/Helpers/Decided.lean:42`,
`Odontoceti/Decision.lean:194`, `Hybrid/Decision.lean:244`,
`FinWhale/Consistency.lean:93`, `Hydrozoan/Helpers/IndirectLiveness.lean:25`)
plus Nemo's inline one are each two lines of body under six lines of
signature, and each is `least_of_no_tie` or `exists_least_of_lt`
(`Common/Anchored/Bounded.lean:213,219`). The `link_unique` law at a `<`
tie is the same `le_antisymm` at four sites.

**Once:** a `tie_wf` field on `Laws` (irreflexive and transitive per
rung), `exists_least` derived by `Finset.exists_minimal` over
`U.ids.filter`, and `link_unique` derived for total ties. This also
removes `[LinearOrder BlockId]` from four rules' public statements, where
it is carried only for the tie. About 70 lines, and a smaller interface.

### 4.3 `Laws` and `BandLaws` as theorems of the combinators

The eight `Laws` total 294 lines; `commit_mono`, `skip_mono`,
`link_congr`, `skip_congr` and the `commit_link` preamble are the same
one to three lines in every one. The eight `BandLaws` delegate to `_band`
lemmas that are themselves copied: `supportersIn_band` verbatim at
`Nemo/Properties.lean:46`, `Odontoceti/Properties.lean:87`,
`Hybrid/Properties.lean:48`; `coneSupports_band` at
`Odontoceti/Properties.lean:119` and `Hybrid/Properties.lean:82`;
`certifiedIn_band` and `not_certifiedIn_band_novel` four times each;
`directSkipSlotIn_band` **already generic** at
`Common/Anchored/Band.lean:273` and re-proved at
`Mysticeti/Properties.lean:398` and `Hybrid/Properties.lean:154` because
the Common one is stated at `quorumCard` only. The incantation
`simp only [<rule>Anchored_waveAt] at hhi; omega` appears nineteen times.

With §1.1's combinators, `commit_mono`, `skip_mono`, `skip_congr`,
`link_congr`, `commit_band`, `skip_band`, `link_band` and `link_novel`
are theorems of the combinator given, per counted set, its transport,
its congruence, `novel_empty` and `0 < t`. What remains a per-rule law is
the quorum-intersection content: `commit_unique`, `commit_skip`,
`commit_link`, `commit_link_unique`, `skip_link`, `link_unique`, and §2.2
supplies those from arithmetic rows. `Validity.Mechanised`
(`Common/BlockRecord.lean:186–333`) is the template: per-clause
instances, an `and` combinator, two lines per rule.

Estimated removal: about 250 lines of `_band` lemmas and 60 of law
fields; and every future rule owes a threshold and a set instead of
twelve proofs.

## 5. Order of work

Each step keeps the build, the axioms, the six audits and the report
current, and is a commit. Dependencies run downward.

| # | step | needs | est. removed |
|--:|:--|:--|--:|
| 1 | Hydrozoan and Optimal read `Common/Support` (§2.3); `blamesP` for slot blames (§2.4); `leaderBlocksAt`, `votingRound`, `isLeaderBlock_unique_of_honest` (§2.5); Nemo's copies deleted (§2.6) | — | 500 |
| 2 | `heldAuthors`/`HoldsAtLeast` with its lemmas and instance (§2.1); the `_mono`/`_congr`/`_of_coversUpto` families and decidability rewritten through it | 1 | 250 |
| 3 | the quorum-intersection family in `Common/` (§2.2); the M3/M5 lemma trio at any record; Hydrozoan and Optimal direct safety on rows | 1 | 350 |
| 4 | `Certified` section over a vote relation (§2.4); `directSkipSlotIn_band` at a threshold; `supportersIn_band`, `coneSupports_band`, `certifiedIn_band` in `Common/Anchored/Band.lean` (§4.3) | 1, 2 | 400 |
| 5 | `tie_wf` on `Laws`; `exists_least` and `link_unique` derived (§4.2) | — | 70 |
| 6 | `AnchoredRule.decided_below_of_run`; generic `AnchoredRule.Total`; Hybrid, Hydrozoan, Optimal, Mahi-Mahi on `Support` + `Timed` (§4.1) | 2, 5 | 300 |
| 7 | the combinators (§1.1) and each rule's `Rule.lean` as parameters; `Laws`/`BandLaws` fields that are combinator theorems removed (§4.3) | 2, 3, 4 | 300 |
| 8 | `DecidedBelow ↔ DecidedWithin`; `Adaptive/Odontoceti.lean` as corollaries; `slotsOf` lemmas in `Adaptive/Basic.lean`; the staged-live combinator (§3.1) | 5 | 350 |
| 9 | `Barnacle.ofAnchored`, `ofAnchored_laws`, `descent_of_support`; `historyView_of_causalStructure` (§3.2 — `rel` on `LiveRule` and the two view `Laws` fields were not adopted, see the note there) | 7 | 700 |
| 10 | Odontoceti as Hybrid at `fc = 0` (§2.7) | 7 | 1100 |
| 11 | FinWhale's restriction family and aliases on Common (§2.6); `LeaderExcludedAll` as a clause (§2.5) | 2 | 250 |

**Progress.** Steps 1 to 4 and 6 to 9 landed as §11.31 to §11.36, §11.38 and §11.39 of `docs/target-properties.md`, and step 11 as §11.40 to §11.42; step 9 kept `Good` as a field and the two view laws, for the reasons §11.36 records.

The estimates sum to about 4,500 lines, or a little under a sixth of the
library after the last round. Steps 1 to 4 are mechanical and carry no
design choice. Step 5 changes the `Laws` interface. Step 7 is where the
rule cards become the source and is the point at which the human-review
goal of §1 is met. Steps 10 and 11 are the two that change how a
protocol is presented and should be confirmed before they start.

## 6. What stays per rule

- The residue of §1.2, one item per rule, and the record and fault class
  each rule reads.
- The arithmetic rows relating each rule's thresholds to `n` and its
  fault parameters.
- Odontoceti's cone descent (`Odontoceti/Rules.lean:290–330`), Optimal's
  fast-evidence lemma (`OptimalHydrozoan/Helpers/SlotAgreement.lean:149`),
  FinWhale's equivocation discount (`FinWhale/Counting.lean:70–130`),
  Mahi-Mahi's wave-three correspondence with the core, Black Marlin's
  order and repair machinery, and each rule's `Live` predicate.
- The liveness hypotheses that differ by rule (§4.1).

## 7. Small findings on the way

- `scripts/gen-reference.py` lists `Nemo.CausalHistory` and
  `Nemo.History` in its layer table; both modules were deleted in
  `959f610` and the entries match nothing.
- `Barnacle/Model/Rule.lean:121–128` records two `Laws` fields with no
  consumers; `full_ids` has one (`Barnacle/Helpers/Cover.lean:20`).
- `Hydrozoan/Helpers/DirectLiveness.lean:55,105` state the same
  certificate-from-synchrony fact twice in one file, once against
  `CoversToward` and once against `SynchronisedOn`.
- `Barnacle/Helpers/Delivery.lean:60,73` are identical bodies, and the
  docstring says so.
