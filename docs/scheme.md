# lean-dag — the unified decider: design record

The object is a unified decider for the single-tier rules of the
Mysticeti codebase (`fast_path = None`): one commit loop and one set of
decision rules, parameterised by a flat record, given as pseudocode with
a table of rows (Cordial Miners PS and Async, Mysticeti, Mahi-Mahi, Blue
Bottle PS and Async, Orcaella, Nemo-Nemo, and four derived rows). The arc
lives in `LeanDag/Scheme/` and changes no rule of the development; the
report's account is §27.

## 0. Key findings

Each finding is machine-checked unless marked otherwise; the Lean names
are the evidence.

**What holds.**

* **The table's arithmetic.** Every published row meets its family's
  inequalities and the liveness bound (Cordial Miners except its skip
  threshold `n`); the derived rows meet what their published counterparts
  meet; Orcaella meets its inequalities at every `n ≥ 5f + 3c + 1`. The
  inequalities with the liveness bound force `n ≥ 5f + 3c + 1` (two
  rounds) and `n ≥ 3f + 2c + 1` (three rounds), and at those committees
  force Orcaella's and Hybrid Mysticeti's thresholds, and Mysticeti's at
  `c = 0` (`Scheme.Table.holds`).
* **Five rows are rules of the development**, at every vote-selection
  rule (`Scheme.Equiv.holds`): Mysticeti is `mysticetiRule`, Blue Bottle
  PS is `odontocetiRule`, Orcaella at `n = 5f + 3c + 1` is
  `hybridRule (n − 3f − 2c)`; Cordial Miners PS and Nemo-Nemo are the
  variants of §4, each with laws and agreement. Every theorem of those
  carriers holds of the decider at those parameters.
* **Three rows with buffer rounds are rules of the development at the
  least vote** (`Scheme.Equiv.holds`): Mahi-Mahi at `w ≥ 3` is
  `mahiMahiRule w`, Blue Bottle Async is `asyncBlueBottleRule`, and
  Cordial Miners Async is `cordialAsyncAnchored 5`, Mahi-Mahi at wave five
  with no direct skip, with Mahi-Mahi's laws. Their thresholds, fault
  bounds and wave lengths are the rules'.
* **The table's inequalities suffice for agreement**
  (`Scheme.Sufficiency.holds`, §7). On any record whose blocks reference
  `q` distinct authors one round down and where at most `f` validators
  may equivocate, every two-round row meeting `TwoRound n f q` and every
  three-round row with a link of one certificate meeting
  `ThreeRound n f q` decides alike from two views, at every vote. The
  derived rows follow: Hybrid Mysticeti and Hybrid Mahi-Mahi at
  `n = 3f + 2c + 1`, and Orcaella and Async Orcaella at every
  `n ≥ 5f + 3c + 1`. Where nobody equivocates, the inequality against an
  equivocating twin (two rounds) and the one making certificates unique
  (three rounds) are not needed; Nemo-Nemo and Async Nemo-Nemo meet the
  rest at `n = 2c + 1` and agree.
* **The commit loop computes the relation** (`Scheme.Loop.holds`, §8).
  `tryDecide`, the scheme's `TryDecide` as a function of a view, outputs
  only verdicts `Decided` derives from that view, at every row and vote
  with positive link and certificate thresholds. At the rows the
  inequalities cover it outputs every derived verdict once its scan
  reaches far enough, and two validators' outputs are prefix-comparable.
  Restarting is idempotent: calls on growing views, each restarting
  after the last decision output, output what one call on the last view
  outputs. The scheme's loop in its own order, over rounds and leader
  indices, is `tryDecide` under `Slots.uniform`, and its output from
  slot `0` is the ledger, nested between validators.
* **The family shows every property the mechanisms read** (§9): banded at
  a local vote, which the least vote and `VotedBlock` are; candidate,
  direct, indirect, quorate, non-equivocating, self-parent; safe at every
  row meeting its inequalities; and a support with its three laws, so it
  lives on the core's universes at every vote.
* **Hybrid Mysticeti is Hydrozoan without its fast path** (§10). On
  Hydrozoan's universe the row decides as Hydrozoan's slow commit with a
  skip on `⌊(n + f + 1)/2⌋` blames and the certificate rung alone. Under
  Hydrozoan's fault model, which admits `n = 3f + 2c + 1`, its carrier is
  safe and progresses, and on records that also ask self-reference it
  lives.
* **The asynchronous rows are live under the coin** (§11), the coin
  abstracted as in the Mahi-Mahi and Async BlueBottle arcs. At
  `2q ≥ n + f + 1`, which every asynchronous row meets, a common core
  exists; one buffer round gives a safe leader (an honest one whose block
  every vote-round block reaches) and the paper's double count, two give
  `q − f`, and further buffer rounds add nothing: at every `f < q ≤ n` an
  execution under eventual delivery has exactly `q − f`. A uniform coin names a
  safe leader with probability at least the count over `n`, and misses
  `m` times with probability that vanishes. Under eventual delivery alone,
  with no time bound (§11.1), a safe leader's slot commits on every
  reliable validator's own view from some time on, every window commits
  and every slot below a run is decided.
* **Every row is safe and live** (§12): Cordial Miners on the core's
  universes; the rows with crash faults under the hybrid fault model with
  self-reference; the asynchronous rows ready for the count.
* **The family runs reactively** (§13): building on votes and
  certificates as they arrive, with the timeout only as a fallback, every
  reliably-led slot commits past GST, at every reliability whose quorum
  meets the thresholds, the hybrid committees included, and with
  self-reference no reliable block is censored; Reactive Mysticeti is an
  instance.

**What the table claims and does not hold, or holds otherwise.**

1. **Nemo-Nemo is no solution of the two-round inequalities.** At
   `f = 0`, `n = 2c + 1` and `c ≥ 1`, its commit plus link is `c + 2`,
   below `n + 1 = 2c + 2` (`Table.NemoNotTwoRound`). The table's "Nemo-Nemo
   at `f = 0`" does not follow from the inequalities; their solution at
   `f = 0` is Orcaella's `n = 3c + 1`. The inequality that fails guards
   against equivocating twins. Where nobody equivocates it is not needed
   (§7.1): the remaining inequalities give agreement, Nemo-Nemo and Async
   Nemo-Nemo meet them at `n = 2c + 1`, and its "no direct skip" is what
   brings the committee from `3c + 1` down to `2c + 1`.
2. **The scheme's Nemo-Nemo is not this development's Nemo-Nemo.** Nemo's
   validity has no self-parent clause, so a skip threshold of `n` is met
   when every vote-round block, the leader's included, omits the leader's
   block; the scheme then skips directly, where Nemo waits for an anchor.
   The extra skip is safe (`Scheme.nemoBlameLaws`). That the threshold can
   be met follows from the validity definition; no witness DAG exhibits it.
3. **Cordial Miners' "no direct skip" holds unconditionally.** The table's
   footnote says a skip threshold of `n` never triggers under faults. On
   the core's universe every block references its author's previous block,
   so the leader never blames its own slot and `n` blames never occur
   (`Scheme.not_holdsAtLeast_card_slotBlamers`). Cordial Miners PS is the
   core with no direct skip, with the core's laws (`Scheme.cordialLaws`).
4. **Orcaella above its bound is a different rule.** Its fixed skip
   threshold `4f + 2c + 1` equals Hybrid's `n − f − c` only at
   `n = 5f + 3c + 1`. Above it the row reads differently from Hybrid;
   it meets the two-round inequalities, so it is safe
   (`Scheme.Sufficiency.holds`).
5. **The vote changes the rules with buffer rounds, not their safety.**
   The scheme's vote, `VotedBlock`, is the first block of the slot met in
   a depth-first search of the parents in their stored order; this
   development's is the least block in the voter's history. One round
   above the candidate both are the reference (`Scheme.votes_iff`), which
   is why five rows match at every vote. With buffer rounds a voter's
   history can hold both twins of an equivocating leader, and the two
   votes then differ: on Mahi-Mahi's `twin4`, the least vote names one
   twin and `VotedBlock` with the parents in descending order the other
   (`LeanDagTest/Scheme/VotedBlock.lean`). So Mahi-Mahi, Blue Bottle Async
   and Cordial Miners Async equal this development's rules at the least
   vote only. Their safety does not depend on the vote: `VotedBlock` is a
   vote-selection rule for every parent order, and at every vote-selection
   rule the three rows have the anchored laws, so two views decide alike
   (`Scheme.Safety.holds`). The proofs read the vote through two facts: a
   block selects at most one block of a slot, and a block that selects a
   block of a slot does not blame it.
6. **The hybrid fault model of `LeanDag/Hybrid` does not contain Hybrid
   Mysticeti's committee.** `HybridFaults` asks `n ≥ 3(fb + fc) + 1`,
   above `3f + 2c + 1` when `c ≥ 1`. The sufficiency theorems are stated
   over the record's quorum `q` and a non-equivocating set instead, so
   crash faults enter only through `q`. Hydrozoan's fault model admits
   the committee, and the row lives there (§10).

**Open.** The asynchronous liveness, and the gaps to the concrete
algorithms; §9.2–§9.4 list them with a plan.

## 1. The parameters

`Scheme.Params` has the six parameters of the table: `waveLength`,
`voteIsCert`, `commitThreshold`, `skipThreshold`, `certThreshold` and
`linkSize`. Leader count and pipelining are the schedule's (`Slots`), not
the rule's, and stake is read as one unit per validator. Each row is a
function of the committee size `n`, the Byzantine bound `f` and the crash
bound `c` (`Params.mysticeti`, `Params.orcaella`, …), at the table's
values. The table's conditions are `Params.TwoRound` (with `q`
references per block: skip plus link and commit plus link at least
`n + f + 1`, link at most `commit + q − n − f`), `Params.ThreeRound`
(twice the certificate threshold, skip plus certificate, and commit plus
`q`, each at least `n + f + 1`) and `Params.Live` (each threshold at most
`n − f − c`).

## 2. The table's claims

`Scheme/Table/Statement.lean` states the reading paragraph's claims and
`Proof.lean` proves them by linear arithmetic:

* every published row meets its family's inequalities and the liveness
  bound, Cordial Miners but its skip threshold `n`;
* the derived rows meet what their published counterpart meets;
* Orcaella meets its inequalities at every `n ≥ 5f + 3c + 1`;
* the inequalities with the liveness bound force `n ≥ 5f + 3c + 1` (two
  rounds) and `n ≥ 3f + 2c + 1` (three rounds), and at those committees
  force Orcaella's and Hybrid Mysticeti's thresholds, and Mysticeti's at
  `c = 0`.

**Finding.** Nemo-Nemo's row is no two-round solution: at `f = 0`,
`n = 2c + 1` and `c ≥ 1`, commit plus link is `c + 2 < n + 1`. The
table's "Nemo-Nemo at `f = 0`" does not follow from the inequalities;
their solution at `f = 0` is Orcaella's `3c + 1`. The failing inequality
guards against an equivocating twin, which the crash model excludes; the
inequalities without it (§7.1) hold of Nemo-Nemo.

## 3. The rule

`Scheme.schemeAnchored` is Algorithm 2 as an `AnchoredRule` with one
rung: the supported-leader test is the direct commit, the skipped-leader
test the direct skip, the certified-link test the rung, the least identifier the tie-break, and
the wave `waveLength − 1`. The vote round is `voteOffset` above the
candidate: the decision round when `voteIsCert`, otherwise the round
below it, and at least one.

**The vote.** The scheme's `VotedBlock` returns the first block of the
slot met walking the voter's references in stored order. The block
record keeps references as a `Finset`, so the vote is a parameter,
`Scheme.VoteSel`: a selection returning a block of the slot from the
voter's history below it when there is one, and none otherwise. Every
claim of the rows one round up is stated at every `VoteSel`.
`Scheme.leastSel`, the least block in the history and Mahi-Mahi's vote,
is one, and the rows with buffer rounds equal this development's rules
at it (§5). `Scheme.votedBlock` is the scheme's own search, with the
parent order a parameter `ord`; when `ord` lists every parent it is a
`VoteSel` (`votedBlockSel`), and the rows with buffer rounds are safe at
every `VoteSel` (§6). A `VoteSel` returns nothing at a block of the
record only when its history holds no block of the slot; off the record
the search's pruning by round is not exact, and no claim reads it there.

## 4. Three rules the rows name

The table writes "no direct skip" as a skip threshold of `n`.

* **Cordial Miners PS.** On the core's universe every non-genesis block
  references a block of its own author, so the leader's vote-round block
  never blames its own slot and `n` blames never occur. The row is
  `cordialAnchored`, the core with no direct skip; it has the core's laws
  (`cordialLaws`).
* **Cordial Miners Async.** The leader's vote-round block reaches a
  block of the leader at the candidate's round through its self-parent
  chain (`exists_self_ancestor`), so `n` blames never occur at any wave.
  The row is `cordialAsyncAnchored 5`, Mahi-Mahi's rule at wave five with
  no direct skip; it has Mahi-Mahi's laws (`cordialAsyncLaws`).
* **Nemo-Nemo.** Nemo's validity has no self-parent clause, so `n`
  blames occur when every vote-round block omits the leader's block. The
  row is `nemoBlameAnchored`, Nemo's rule with that direct skip; it has
  Nemo's laws (`nemoBlameLaws`), the skip cases by the observation that a
  blame from every validator leaves no vote for the candidate in a model
  where nobody equivocates. Its rung reads a vote in the anchor's
  history, so its anchors are blocks of the record (`Anchor := A ∈ U.ids`).

**Finding.** The scheme's Nemo-Nemo is not this development's Nemo-Nemo:
it skips directly where Nemo waits for an anchor. Both are safe.

## 5. The rows as carriers

`AnchoredRule.ReadAlike` (`Common/Anchored/ReadAlike.lean`) is what
`Decided` reads; `ReadAlike.decided_iff` proves that two rules agreeing
on it decide alike, and `AnchoredRule.toDagRule_eq` that their carriers
are equal. One round above the candidate, a vote is a
reference and a blame a reference to no candidate (`votes_iff`,
`blamersAt_eq`). `Scheme/Equiv/Statement.lean` then states, at every
`VoteSel`:

| Row | Carrier | Condition |
|:---|:---|:---|
| Mysticeti | `mysticetiRule` | none |
| Blue Bottle PS | `odontocetiRule` | none |
| Orcaella | `hybridRule (n − 3f − 2c)` | `n = 5f + 3c + 1` |
| Cordial Miners PS | `cordialAnchored`, with `Agree` | none |
| Nemo-Nemo | `nemoBlameAnchored`, with `Agree` | `n = 2c + 1` |

Mysticeti has no tie-break; the scheme's least choice there is the one
linked candidate, by `coreLaws.link_unique`. Orcaella's skip threshold
`4f + 2c + 1` equals Hybrid's `n − f − c` only at the bound.

At the least vote, the rows with buffer rounds (`Helpers/Buffered.lean`):

| Row | Carrier | Condition |
|:---|:---|:---|
| Mahi-Mahi | `mahiMahiRule w` | `w ≥ 3` |
| Blue Bottle Async | `asyncBlueBottleRule` | none |
| Cordial Miners Async | `cordialAsyncAnchored 5`, with `Agree` | none |

Below the voter, any `VoteSel` returns nothing exactly when Mahi-Mahi's
`Blames` holds (`sel_eq_none_iff_blames`), and `leastSel` votes exactly
as Mahi-Mahi's `Votes` (`leastSel_votes_iff`). Mahi-Mahi has no
tie-break; two linked candidates are one block by
`MahiMahi.eq_of_hasCertificate`.

On a record in which no validator equivocates, every vote-selection rule
selects the slot's one block (`sel_eq_of_noEquiv`), so any two give one
carrier (`VoteFree`, `readAlike_noEquiv`), and the three rows with buffer
rounds are their rules at every vote there (`BufferedRowsNoEquiv`). The
choice of vote matters only where a voter holds two blocks of an
equivocating leader: it decides which twin, if any, reaches the
certificate threshold.

Async Nemo-Nemo agrees by the inequalities where nobody equivocates
(§7.1).

## 6. The scheme's own vote

`Scheme/Safety/Statement.lean` states, and `Proof.lean` proves, that
**`VotedBlock` is a vote-selection rule** for every parent order that
lists every parent (`VotedBlockIsVote`). The search walks references as
`historyUpto` does; at a block of the record a reference lies one round
down, so pruning at the slot's round loses no block of the slot.

Every row agrees at every vote-selection rule, this one included (§7):
Mahi-Mahi at `w ≥ 3` and Cordial Miners Async meet the three-round
inequalities, and Blue Bottle Async at `n ≥ 5f + 1` the two-round ones,
at `q = n − f` (`Table.RowsCovered`). The properties of Mahi-Mahi and
Async BlueBottle beyond agreement are proved of those rules, and transfer
to the rows only at the least vote (§5); the family's own (§9) hold at
every vote.

## 7. The table's inequalities suffice

`Scheme/Sufficiency/Statement.lean` states, and `Proof.lean` proves, at
every vote-selection rule, on records whose blocks reference `q` distinct
authors one round down (`Validity.Quorate q`) and with at most `f`
validators outside the record's honest set, **every row the inequalities
cover agrees** (`CoveredAgree`, from `coveredLaws`). The honest set is
the set of validators that never equivocate, so a crash-prone validator
belongs to it. `Params.Tolerates honest f q` collects the three
hypotheses: `honestᶜ.card ≤ f`, `q ≤ n`, and the row is covered. A
record keyed to a smaller set, as the hybrid arc's records are keyed to
the fully correct validators, is read at its non-equivocating set by
`withHonest`, with the same blocks. The rows covered, `Params.Covered n f q`, are:

* **two rounds** (`twoRoundLaws`): a row whose vote is its certificate,
  with a wave of at least two, meeting `TwoRound n f q`;
* **three rounds** (`threeRoundLaws`): a row that certifies votes one
  round later, with a wave of at least three and a link of one
  certificate, meeting `ThreeRound n f q`;
* the same rows meeting the weaker inequalities where nobody equivocates
  (§7.1).

Every row of the table is covered, at `q = n − f − c` and every committee
from its bound up (`Table.RowsCovered`): Mysticeti, Mahi-Mahi at every
wave of three or more and Cordial Miners from `3f + 1`, Blue Bottle from
`5f + 1`, Orcaella and Async Orcaella from `5f + 3c + 1`, Hybrid
Mysticeti and Hybrid Mahi-Mahi from `3f + 2c + 1`, and Nemo-Nemo and
Async Nemo-Nemo, where nobody equivocates, from `2c + 1`. So every row
agrees.

Every step is one of two counts. Two sets of same-round blocks whose
authors number more than `n + f` together share a block
(`exists_common_block`), and that block selects at most one block of a
slot and does not blame a slot it selects in: this gives each inequality
of the form `n + f + 1 ≤ a + b`. A block above `c` authors'
decision-round blocks holds at least `c + q − n − f` of them in its
history (`card_inHistory_ge`, `Common/History.lean`): this gives visibility, the inequality
with `q`. In the two-round family the third inequality and `q ≤ n` give
`commit ≥ link + f`, which the cases of two direct commits, and of a
direct commit and a direct skip, need.

### 7.1 Where nobody equivocates

When every validator is honest (`f = 0`), a slot has one block
(`eq_of_noEquiv_all`), and the laws that compare two blocks of one slot
need no count: two direct commits, a direct commit and a link, and two
links name one block. The inequality written for them is not needed:
`n + f + 1 ≤ commit + link` in the two-round family, which keeps a
direct commit consistent with a link to an equivocating twin, and
`n + f + 1 ≤ 2·cert` in the three-round family, which makes certificates
unique. What remains is `Params.TwoRoundCrash n q`
(`n + 1 ≤ skip + link`, `link + n ≤ commit + q`) and
`Params.ThreeRoundCrash n q` (`n + 1 ≤ skip + cert`,
`n + 1 ≤ commit + q`).

* **Agreement** (`CoveredAgree`, from `twoRoundCrashLaws`,
  `threeRoundCrashLaws`): a row meeting them agrees on records where
  nobody equivocates, at every vote.
* **The table** (`Table.CrashWeaker`, `Table.CrashRows`,
  `Table.CrashBound`): at `f = 0` the inequalities imply these;
  Nemo-Nemo and Async Nemo-Nemo meet the two-round ones at `n = 2c + 1`,
  `q = c + 1`. With `q = n − c`, a two-round row needs `n ≥ 2c + 1`, and
  `n ≥ 3c + 1` when its skip is within the liveness bound, where
  Orcaella's thresholds at `f = 0` are forced; a three-round row needs
  `n ≥ 2c + 1`, where Hybrid Mysticeti's at `f = 0` are forced. A direct
  skip within the bound costs a two-round row `c` validators, and
  Nemo-Nemo's "no direct skip" saves them.
* **The Nemo rows**: Nemo-Nemo and Async Nemo-Nemo are covered at
  `n ≥ 2c + 1`, `q = n − c`, where nobody equivocates
  (`Table.RowsCovered`), and agree. A test instantiates Async Nemo-Nemo
  on Nemo's universe, whose majority quorum is `c + 1`.

The rows the inequalities cover, `Params.Covered n f q`, include these at
`f = 0`, so the commit loop (§8) and the family's properties (§9) hold
at them.

## 8. The commit loop

`Scheme/Model/TryDecide.lean` writes the scheme's loop as functions of a
validator's view `V`. A decision is an `Option (Option BlockId)`:
undecided (`⊥`), a skip, or a commit.

* `tryDirect k`: skip if the slot's blames reach the skip threshold,
  else commit the least candidate whose certificates reach the commit
  threshold. The scheme tries the candidates in an unstated order and
  notes that at most one qualifies; the laws make the order immaterial.
* `tryIndirect k later`: walk the later slots' decisions in slot order,
  past the ineligible ones; stop undecided at an undecided eligible slot,
  pass over skipped ones, and at the first committed one commit the
  least linked candidate the view holds, or skip.
* `scan N m`: the decisions of slots `N + 1 − m, …, N`, each from the
  decisions above it, the scheme's list `S`.
* `tryDecide lo N`: the longest decided prefix from slot `lo`.

The scheme's schedule is `Slots.uniform p m`: `m` leaders every `p`
rounds, `p = 1` with pipelining and `p = waveLength` without. Slot
`j·m + l` is round `p·j` with leader index `l`, so the scheme's scan,
rounds downward and leader indices downward, is slot order reversed
(`Order`, `OrderUniform` below).

`Scheme/Loop/Statement.lean` states, and `Proof.lean` proves:

* **Soundness** (`Sound`, from `tryDecide_sound`): at positive link and
  certificate thresholds, every output is a derivation of `Decided` from
  the same view, at consecutive slots from `lo`. A candidate linked from
  an anchor the view holds lies in the view, so the least linked
  candidate the view holds is the tie-break's choice.
* **Prefix comparability** (`PrefixComparable`, from `tryDecide_prefix`):
  at every row of §7, two validators' outputs are prefix-comparable.
* **Completeness** (`Complete`, `OutputComplete`, from
  `decisionAt_complete` and `tryDecide_eventually`): at every row of §7,
  a verdict `Decided` derives is the loop's decision for its slot once
  the scan passes the derivation's largest slot, and `tryDecide` outputs
  it once every slot from `lo` up to it is decided. By induction on a
  bounded derivation (`DecidedWithin`): a direct decision the loop makes
  is the derived one by soundness and uniqueness; otherwise the walk
  passes the skipped slots, meets the derivation's anchor, and the
  tie-break makes the derivation's candidate the least linked one.

`LeanDagTest/Scheme/TryDecide.lean` runs the loop: on `full4` at the
Mahi-Mahi row of wave four it commits slots `0`–`2` directly at the
least vote and at `VotedBlock`, and on Mysticeti's `U7` it commits slot
`0` indirectly through slot `1`.

**The restart** (`Restart`, `Resume`, `Repeated`; `Helpers/Restart.lean`).
The scheme's *TryDecide* takes `r_last`, the round of the last consumed
decision, and calls itself idempotent. Stated at slot granularity:

* **Restarting inside the output repeats its tail** (`Restart`, from
  `tryDecide_restart`), at every row and vote: for `lo ≤ lo'` within the
  output from `lo`, `tryDecide lo' N` is that output without its first
  `lo' − lo` entries. The scan lists each slot with the loop's decision
  for it (`scan_eq_map`), and a slot's decision reads only the slots
  above it, so where the scan stops at the bottom changes nothing above.
* **Resuming on a larger view** (`Resume`, from `tryDecide_resume`), at
  the rows of §7: the output on `V₁` to slot `N₁`, followed by the output
  on `V₂ ⊇ V₁` to `N₂ ≥ N₁` from the slot after it, is the output on `V₂`
  from `lo`. A decision the scan makes is a derivation bounded by
  `N₁ + 1` (`SoundAt` carries the bound); a bounded derivation holds on
  every larger view (`DecidedWithin.view_mono`); and completeness at the
  bound decides it at `N₂` (`decisionAt_mono`).
* **Successive calls output what one call outputs** (`Repeated`, from
  `consumed_eq`): `consumed lo W N t` lists the decisions of `t` calls on
  views `W 0 ⊆ W 1 ⊆ …` scanned to `N 0 ≤ N 1 ≤ …`, each restarting after
  the last decision output, and after `t + 1` calls it is
  `tryDecide (W t) lo (N t)`.

The scheme restarts at the *round* of `r_last`, not the slot after it.
With several leaders per round, or with pipelining, the slots of that
round already consumed are output again; `Restart` says they are output
alike, so the caller drops them by slot. The tests restart `full4` at
slot `1`, run three calls on it, and on `U7` show a first call that
outputs nothing because slot `0` waits on slot `1`.

**The scheme's order** (`Order`, `OrderUniform`; `Helpers/Order.lean`).
`schemeOrder per m rLast rHigh` lists the pairs of round and leader index
the scheme visits: the rounds from `rHigh` down to `rLast` with a wave
offset, every `per`-th one, and in each the leader indices from `m − 1`
down to `0`. `schemeTryDecide` is the scheme's loop over that list,
transcribed: decide the pair's slot `slotOf per m r l = (r / per)·m + l`
from the decisions already made, put it in front, and return the longest
decided prefix.

* **The pairs are their slots' rounds and leader indices**
  (`OrderUniform`, from `schemeOrder_uniform`): under
  `Slots.uniform per m`, slot `slotOf per m r l` is proposed at round `r`
  and has leader index `l`.
* **The scheme's loop is `tryDecide`** (`Order`, from
  `schemeTryDecide_eq`), at every row and vote: over rounds
  `rLast, …, rHigh` it outputs `tryDecide` from slot `⌈rLast/per⌉·m` to
  slot `⌈(rHigh+1)/per⌉·m − 1`. The slots it visits are those, downward
  (`schemeOrder_slots`, by induction on the rounds: a round with a wave
  offset adds its `m` slots on top), and deciding them in turn from the
  top is the scan (`foldr_range'`).

**The restart at a round** (`RestartRound`, from
`schemeTryDecide_restartRound`), at the rows of §7. A call over rounds
`rLast, …, rHigh₁` on `V₁` whose last decision is slot `k` is followed by
a call on `V₂ ⊇ V₁` over rounds from `k`'s round, `r_last = per·(k/m)`,
to `rHigh₂ ≥ rHigh₁`, with the slots up to `k` dropped. Together they
output the call on `V₂` over rounds `rLast, …, rHigh₂`. The second call
is `tryDecide` from `r_last`'s first slot (`Order`), which lies inside
the first output; by `Resume` and `Restart` its output is the tail of
the first output from that slot, followed by the resumed output, and
dropping the slots up to `k` leaves the resumed output.

**The ledger** (`Ledger`, `LedgerAgree`; `Helpers/Ledger.lean`). The
loop's assignment `loopAssign N k` is slot `k`'s committed block, if any;
the output lists its slots with it (`tryDecide_eq_map`).

* **The output from slot `0` is the ledger** (`Ledger`, from
  `ledger_read`), at positive link and certificate thresholds: its
  committed blocks are `commitSeq (loopAssign N)` over its length, the
  blocks they reach are `ledgerSet` over its length, and every slot
  below its length is decided by the relation with the assignment's
  verdict, so the agreement theorems of `Common/Anchored.lean`
  (`commitSeq_agree`, `ledgerSet_agree`, `outputAt_agree`) read it.
* **Two validators' ledgers are nested** (`LedgerAgree`, from
  `ledger_agree`), at the rows of §7: their commit sequences are
  prefix-comparable and one ledger contains the other.

With `Repeated`, the ledger after `t + 1` calls on growing views is the
ledger of one call on the last view. The tests run the scheme's loop in
its own order on `full4` and `U7`, restart it at round `3` on `U7`, read
the committed blocks `0` and `12` off `U7`'s output, list the slots
`5, 4, 3, 2` for two leaders per round over rounds `2` down to `1`, and
on `full4` restart at slot `1`'s round, where slot `1` is output again
and dropped.

## 9. The family as a carrier, and what remains

### 9.1 The properties the mechanisms read

`Scheme/Properties.lean` states them at the family's carrier
`schemeRule p σ` (`Model/Local.lean`), the decider on block records:

| Property | Holds at |
|:---|:---|
| `Banded` | every row with a wave of at least two and positive link and certificate thresholds, at a local vote (`banded`) |
| `CommitsCandidate`, `CommitsDirect`, `Indirect` | every row and vote |
| `SkipsUnsupported` | every row whose vote round is one above the slot |
| `Quorate`, `NoEquiv` | from validity's quorum and the record's honest set; `SelfParent` on the core's universes |
| `Agree`, `Safe` | every row meeting its inequalities, at a local vote for `Safe` (`agree`, `safety`) |
| support `familySupport` | `Local` at a local vote; `Commits` at `commit ≤ n − slack`; `OfCoverage` at `cert ≤ n − slack` (`Helpers/Support.lean`) |
| `Lives` | the core's universes, at `commit ≤ n − f` (`lives`) |

`OnRecord` is `Scheme/Record.lean`, with the prompt skip after an
extension; chain quality at the carrier is
`LeanDagTest/Quality/Generic.lean`. In `audit-conformance.py` and
`audit-mechanisms.py` the family shows every obligation and has every
mechanism; adaptive leaders (Barnacle and HammerHead) are §14.

**The local vote.** `Banded` asks that a slot's verdict survive a
truncation or a round shift of the record, so the vote must survive it.
`VoteSel.Local` asks this of a vote: a voter in a band, reading a slot at
or above the band's floor, votes alike in both records. `leastSel` is
local because the voter's history from the slot's round up is the same
set across the band; `votedBlockSel` because the search reads the same
parents at every block strictly above the slot's round and the same
author and round at the blocks it tests, at any fuel that reaches the
slot's round (`Helpers/Local.lean`). With it, the band laws hold
(`schemeBandLaws`): certificates and blames carry into the band's other
side, an old anchor's linked certificates are the same set, and a
candidate the band adds is linked from no old anchor, since its votes
would put it in the anchor's history in the old record. The rule needs
nothing of its anchors, so `Banded` holds at every row, inequalities or
not.

**The support.** A block certifies a candidate a wave below it when
`IsCert` holds. `Commits`: a reliable quorum populating the wave and
certifying the candidate at the decision round holds a direct commit in
any view caught up to that round, at a commit threshold the quorum
meets. `OfCoverage`: under coverage toward the candidate, every reliable
block from one round above it reaches it, layer by layer; an honest
candidate in a voter's history is the voter's vote, every vote rule
selecting it since it is the only block of its slot there; so a reliable
decision-round block votes for it (vote rows) or references every
reliable vote-round block (certificate rows, at a wave of at least
three). Neither law reads the vote beyond that, so the family lives at
every vote.

**Checkpoints.** The checkpoint bridge reads `Agree` and the support's
`Commits`, so it holds at the family's carrier
(`Integration/SchemeCheckpoint.lean`). At every tolerated row a commit
settled on every rule-following validator's view has a finality
certificate (`commitFinalized_scheme`), one slot has one checkpoint
content (`checkpointUnique_scheme`), and at `commit ≤ n − slack` a slot
led by a rule-following validator reaches finality from production and
certification (`liveCommitFinalized_scheme`). The `*_classes` forms tie
the row to the checkpoint layer's fault model
(`Integration/FaultClasses.lean`): Byzantine, crash-prone and
alive-but-corrupt sets at `3f + 2c + f_a < n`, the row covered at the
classes' `f`, the honest set leaving out Byzantine validators only, the
checkpoint quorum `n − f − c`, and the reliability quorum discharged
with alive-but-corrupt validators in it. The liveness hypothesis is the
commit conjunct of `Params.Live` alone; the full `Live` is not available
at the rows with no direct skip, whose skip threshold is `n`. The slack
is arithmetic:
a two-round committee `n ≥ 5f + 3c + 1` admits any `f_a ≤ 2f + c`
(`resilient_of_twoRound`), a three-round committee at `3f + 2c + 1`
admits none (`resilient_threeRound_iff`). The wave is constant, so the
rule is a Barnacle base rule and the bridge runs over leader-scheduling
runs (`commitFinalized_barnacle_scheme`), for an update rule with
`Anchored`. `LeanDagTest/Scheme/Checkpoint.lean` witnesses the three
forms on Mysticeti's `U7` and Mahi-Mahi's `full4`, with distinct views
per validator and proposals carried in blocks.
`LeanDagTest/Scheme/CheckpointAbC.lean` runs liveness with `f_a > 0`:
the Hybrid Mahi-Mahi row on four validators at `f = 0`, `c = 1`,
`f_a = 1`, one above the row's committee, where the alive-but-corrupt
validator leads the slot, is counted in both quorums and proposes a
fork that has no certificate. The same file runs the commit path
through `commitFinalized_classes` and inhabits the classes at Hybrid
Mysticeti's, Nemo-Nemo's and Blue Bottle's committees, the last with a
Byzantine and two alive-but-corrupt validators.
`LeanDagTest/Scheme/CheckpointBarnacle.lean` applies
`commitFinalized_barnacle_scheme` to a run of the Mysticeti row on `U7`
under the constant update rule.

### 9.2 The gaps to the concrete algorithms

* **The buffer-round rows.** Mahi-Mahi, Blue Bottle Async and Cordial
  Miners Async equal the development's rules at the least vote only; at
  `VotedBlock` they are different rules (`twin4`), which have every
  property of §9.1. The development's Mahi-Mahi takes the least vote
  (`mahi-mahi.md` §2). Which vote the implementation takes is not
  checked; if it is the first block in reference order, the
  development's Mahi-Mahi differs from the implementation.
* **Nemo-Nemo.** The scheme's row is `nemoBlameAnchored`, with its own
  laws on Nemo's universes (`nemoBlameLaws`), and meets the inequalities
  where nobody equivocates (§7.1), as Async Nemo-Nemo does. There is no
  asynchronous Nemo in the development to compare Async Nemo-Nemo with.
* **Orcaella above its bound** is a rule other than Hybrid's, with every
  property of §9.1, and has no reference algorithm.
* **Cordial Miners and the derived rows** other than Hybrid Mysticeti
  have no earlier formalisation to compare with. Hybrid Mysticeti is
  Hydrozoan without its fast path (§10). Every one of them is shown safe
  and live (§12); what cannot be checked is fidelity to an
  implementation.
* **Stake.** The scheme counts stake; the arc counts one unit per
  validator.
* **The asynchronous leader.** The coin is abstracted (§11): by the
  clause on the schedule and the record, and by a uniform distribution
  for the probabilities. Its cryptographic construction is not
  formalised, as in the Mahi-Mahi and Async BlueBottle arcs.
* **The buffer rounds.** The paper's count is formalised (§11), with its
  claim that buffer rounds past two add nothing (`BufferTight`); its
  formula for `K` leaders,
  `1 − C(n − |core|, K)/C(n, K)`, is stated only in its deterministic
  form (`K > n − |core|` gives a safe leader).
* **The hybrid fault model.** The family's `Lives` is stated on the
  core's universes, where a `Faults` instance asks `n ≥ 3f + 1` of the
  slack `f`; that excludes Hybrid Mysticeti's committee `3f + 2c + 1` at
  `c ≥ 1`. Every covered row lives at Hydrozoan's fault model, which
  admits it (§10), with self-reference: Hybrid Mysticeti, Hybrid
  Mahi-Mahi, Orcaella, Async Orcaella, Nemo-Nemo and Async Nemo-Nemo
  (§12), and every covered row whose thresholds are within `q` commits
  run reactively (§13), the pacemaker advancing on `q` round authors.

### 9.3 Liveness

The partially synchronous liveness is the family's: `Lives` (progress
and inclusion) on the core's universes at every row with
`commit ≤ n − f`, at every vote, and the three support laws, `OfCoverage`
at `cert ≤ n − slack`. The table's liveness bounds (`Params.Live`) are
the hypotheses these read. Hybrid Mysticeti progresses on Hydrozoan's
universe under Hydrozoan's fault model (slack `f + c`), and with
self-reference lives (§10). The asynchronous rows are live under the
coin for the whole family (§11): a safe leader exists by the count with
no network hypothesis, a uniform coin names one with probability bounded
below at every round, and under eventual delivery its slot commits on
every reliable validator's own view (§11.1).

### 9.4 Plan

1. Stake weights.

## 10. Hybrid Mysticeti against Hydrozoan

Hydrozoan (`hydrozoan.md`) is the development's rule under the hybrid
fault model: `n ≥ 3f + 2c + k + 1` replicas, at most `f` Byzantine, at
most `c` crashed. Both it and the scheme are anchored rules, and they
read alike part by part:

| Part | Hybrid Mysticeti row | Hydrozoan |
|:---|:---|:---|
| Anchor eligibility | `waveLength − 1 = 2` | `2` |
| Vote | `σ.Votes`, one round up: a reference | a reference (`IsVote`) |
| Certificate | `⌈(n + f + 1)/2⌉` votes | `q_cert = (n + f)/2 + 1`, the same |
| Direct commit | `2f + c + 1` certificates | the fast path or the slow path, `q_slow = 2f + c + 1` certificates |
| Direct skip | `⌊(n + f + 1)/2⌋` blames | `q_fast = n − ⌊(c + k)/2⌋` blames |
| Rungs | a certificate in the anchor's history | that, then `q_weak` linked votes |
| Tie-break | least id | none at the certificate rung |

Hydrozoan's weak rung finds a fast commit, which may leave no
certificate, through an anchor, and its skip threshold `q_fast` excludes
a fast commit. Without the fast path neither is needed.

`Scheme/Model/Hydrozoan.lean` defines `hydrozoanSlowAnchored`, Hydrozoan
without its fast path on Hydrozoan's universe: the slow commit in view,
a skip on `⌊(n + f + 1)/2⌋` blames, and the certificate rung alone.
`Scheme/HybridRow/Statement.lean` states, and `Proof.lean` proves, at
every vote-selection rule:

* **The row is Hydrozoan without its fast path** (`SlowRow`, from
  `readAlike_hydrozoanSlow`): one round up a vote is a reference
  (`certsAt_eq_certificatesAt`, `blamersAt_eq`), the thresholds are
  Hydrozoan's, and the scheme's tie-break never fires, since two
  candidates of a slot with certificates are one block
  (`eq_of_certs_three`, at `2·q_cert > n + f`).
* **On Hydrozoan's universe the carrier is safe and progresses**
  (`OnHydrozoan`), at a local vote. The row meets its inequalities at
  every `n ≥ 3f + 2c + 1` with `q = n − f − c`
  (`Table.HybridAnyCommittee`), so it is covered, and safe. Under
  Hydrozoan's fault model `hzReliability`, whose slack is `f + c`, the
  commit and certificate thresholds are reachable by the correct
  replicas, so the support commits (`familySupport_commits`), which is
  progress, and its coverage law holds (`familySupport_ofCoverage`).
* **With self-reference the carrier lives** (`WithSelfParent`): on
  records at `HybridValid`, Hydrozoan's validity with every block
  referencing its author's previous block, `SelfParent` holds
  (`Scheme.selfParent`, now stated for any validity that asks it), and
  with it inclusion: progress and inclusion together.

Hydrozoan's validity has no self-parent clause, which is why Hydrozoan's
own liveness is progress only, and the same holds of the row on
Hydrozoan's universe. A side finding: the row's skip threshold
`⌊(n + f + 1)/2⌋` is at most `n − f − c` exactly when
`n ≥ 3f + 2c + 1`, so the correct replicas alone skip a slot, where
Hydrozoan's `q_fast` exceeds `q`.

`LeanDagTest/Scheme/HybridRow.lean` takes six replicas, one Byzantine and
one crashed: `n = 3f + 2c + 1` at `f = c = 1`, which Hydrozoan's fault
model admits and the core's excludes. Every threshold of the row is
`4 = q`, Hydrozoan's `q_fast` is `6`, and the statements hold at the
least vote.

Nothing in `LeanDag/Hydrozoan/` changes; the arc is read, not edited.

## 11. The asynchronous rows: the coin and the buffer rounds

The asynchronous rows add `b` buffer rounds between the proposal and the
vote (`b = voteOffset − 1`) and elect a wave's leader by a coin opened at
the decision round. The coin is abstracted as the Mahi-Mahi and Async
BlueBottle arcs abstract it (`mahi-mahi.md` §5, `async-bluebottle.md`
§6): a deterministic count of the leaders that would commit, a clause on
the schedule that the coin makes true, and a uniform distribution for
the probabilities. `Scheme/Model/Async.lean` defines `safeAt p U r`, the
honest validators whose round-`r` block every vote-round block reaches
(the paper's core), and the clauses `SafeWithin` and `SafeRunWithin`
over safe leaders. Every decision-round block certifies a safe block
(`isCert_of_safe`), so a safe leader commits wherever the reliable
decision-round blocks are held; a leader committed only by certificates
that include Byzantine ones need not commit at a reliable validator,
which is why the arc counts the safe set.
`Scheme/Async/Statement.lean` states, and `Proof.lean` proves, on any
record whose blocks reference `q` distinct authors one round down and
whose validators outside `honest`, at most `f`, may equivocate, at every
row and vote:

**The count, with no network hypothesis.**

* **The common core** (`CommonCore`, from `exists_commonCore`,
  `Common/CommonCore.lean`): at `2q ≥ n + f + 1`, a block at round
  `r + 2` gives an honest round-`r` block in the history of every block
  from round `r + 2` up. Some honest author collects so many honest
  supporters that every round-`(r+2)` block names one
  (`commonCore_arith`). The core's T3a and T3c are the case
  `q = n − f`. Every
  asynchronous row meets the condition at `q = n − f − c`: Mahi-Mahi,
  Cordial Miners Async, Async Nemo-Nemo and Hybrid Mahi-Mahi at
  equality, Blue Bottle Async and Async Orcaella above it.
* **One buffer round** (`SafeNonempty`): the core of the proposal round
  is safe. **The double count** (`SafeCount`): with an honest population
  `T` of the buffer round, `|T|·(q − f) + G·(n − q) ≤ G·|T| + |honest|·(n − q)`,
  `G` the size of the safe set, since a block named by more than `n − q`
  of `T` is reached from two rounds up. At `|T| = |honest| = n − f` this
  is the paper's `|core| ≥ h − ⌊mh/(h − m)⌋`: `4` at Blue Bottle Async
  `f = 1`, `2` at Mahi-Mahi `f = 1, 2`.
* **Two buffer rounds** (`SafeCard`): the core of the buffer round's first
  round is reached by every block two rounds above it, and so is each of
  its honest references: `q ≤ G + f`, the paper's `h − m`.
* **Several leaders** (`MultiLeader`): leaders of a round more than `n`
  less the safe set include a safe one.
* **Buffer rounds past two add nothing** (`BufferTight`, from
  `Scheme/Helpers/Starve.lean`): at every `f < q ≤ n` and every vote
  offset, some execution has exactly `q − f` safe validators, so the
  two-buffer bound is attained at every number of buffer rounds from two
  on. In the execution the first `f` validators are Byzantine and
  `m = n − q` honest validators are starved: a starved validator's block
  references the whole round below, and every other block references the
  round below less the starved validators' blocks, `q` authors. A block
  outside the starved set then never reaches a starved block
  (`Starve.not_starved_of_reaches`), at any depth, while every block above
  round `0` reaches every other round-`0` block, so the safe set is the
  `n − f − m = q − f` honest validators outside the starved set
  (`Starve.card_safeAt_starve`). Every block also references its author's
  previous block, so the execution is valid where self-reference is
  required. It is what validators produce under eventual delivery when
  each references every block of the round below it holds and the starved
  validators' blocks arrive one round late (`Starve.starvePace`,
  `Starve.refs_starve_eq_held`).
* **One buffer round against a population of `q`** (`SafeOneBuffer`,
  `card_safeAt_oneBuffer`): with an honest population of the buffer round
  at least `q` strong and `n ≤ 2q`, the double count reads
  `q·(q − f) ≤ G·(2q − n) + |honest|·(n − q)`.
* **A third at the five-`f` committees** (`SafeThird`,
  `card_safeAt_third`): at `n ≥ 5f + 3c + 1` and `q = n − f − c`, one
  buffer round gives `n ≤ 3G`. This covers Blue Bottle Async (`c = 0`) and
  Async Orcaella.
* **Two at the three-`f` committees** (`TwoSafe`,
  `Scheme/Helpers/TwoSafe.lean`): at every `b ≤ k` with `k ≥ 2`, on
  `n = b + 2k + 1` validators with `q = b + k + 1` and `b` Byzantine, some
  execution under eventual delivery has exactly two safe validators at one
  buffer round. These are the committees `2q = n + f + 1` of Mahi-Mahi at
  wave four (`b = k = f`), Hybrid Mahi-Mahi at wave four (`b = f`,
  `k = f + c`) and Async Nemo-Nemo (`b = 0`, `k = c`). Validators `b` and
  `b + 1` are `x₁` and `x₂`; the other `2k − 1` honest validators carry
  labels on a cycle. A round-`1` block references the Byzantine round-`0`
  blocks, `x₁`, `x₂`, and the `k − 1` labels from a centre: its own label,
  `0` for `x₁`, `k − 1` for `x₂`. A Byzantine validator has one round-`1`
  block per label `x`, centred one past `x`. At round `2` the validator
  labelled `x + 1` references the Byzantine blocks for `x`, the honest
  blocks of the `k` labels from `x + 1`, and the block of `x₁` or `x₂`
  whose window misses `x`; no round-`2` block reaches label `x`, while
  every round-`2` block reaches `x₁` and `x₂`. The safe set is `{x₁, x₂}`
  (`TwoSafe.card_safeAt_twoSafe`), and the coin finds a safe leader with
  probability `2/n`. A constant fraction of safe validators therefore
  needs two buffer rounds, or one buffer round at the five-`f`
  committees.
**The coin** (`CoinCommit`, `CoinTail`, through Steelhead's counts,
`Steelhead/Helpers/Coin.lean`, whose fault model a fault-free instance
supplies inside the proofs): a uniform coin names a safe leader with
probability at least `1/n` at one buffer round and `(q − f)/n` at two,
and at least `1/3` where a third of the validators is safe (`CoinThird`);
`m` independent coins over rounds whose safe sets hold `c` validators all
miss with probability at most `((n − c)/n)^m`, which vanishes.

`LeanDagTest/Scheme/Async.lean` shows the count on data at the Mahi-Mahi
row: on `full4` every honest round-`0` block is safe; on `starve4`,
where one honest block is referenced only along its author's own chain,
the safe set is `{2, 3}`, of size `q − f = 2`, at one, two and three
buffer rounds alike.

### 11.1 On a validator's own view, under eventual delivery

Asynchronous liveness should rest on eventual delivery alone. The
timed pacing trunk (`PaceCore`) bounds the delay after GST, and the local
commit of the Mahi-Mahi and Async BlueBottle arcs reads that bound.
`Scheme/Model/AsyncPace.lean` defines `AsyncPace qp U T N`, pacing with no
clock: a reliable validator's holdings grow, are causally closed, and
include its own blocks from some time on; whatever one reliable
validator holds, every reliable validator holds at some later time
(`ConvergesEventually`, the untimed half of the trunk's `converges`); and
a reliable validator holding `qp` distinct round-`n` authors gets past
round `n`. The quorum `qp` is a parameter, so the hybrid committees are
covered. `AsyncPace.viewAt` is a reliable validator's view at a time: its
holdings. `AsyncPace.Eventually Φ` says that from some time on every
reliable validator's view satisfies `Φ`; every conclusion below has this
form. Each statement asks that a certificate fit the wave and the quorum
(`Params.CertFits q`: a wave of two or more, and where votes are certified
a round later a wave of three or more and a certificate threshold of at
most `q`).

`Scheme/AsyncLocal/Statement.lean` states, and `Proof.lean` proves, with
the reliable set `T` at least `qp` strong, at every row and vote:

* **The coin's leader eventually commits** (`CoinLive`), the arc's
  asynchronous headline: at a row ready for the count
  (`Params.AsyncReady`), under asynchronous pacing at `q`, a uniform coin
  names a leader whose slot commits on every reliable validator's own
  view from some time on (`AsyncPace.EventuallyCommits`), with
  probability at least `1/n` at one buffer round and `(q − f)/n` at two or
  more. The coin's outcome `v` is a schedule in which `v` leads the slot.
* **Delivery** (`Delivered`): from some time on, every reliable
  validator's view holds every reliable block of the record. The record is finite,
  each of its reliable blocks is eventually held, and holdings only grow
  (`AsyncPace.exists_time`).
* **Production** (`Populated`): every round below the horizon has a block
  by every reliable validator. At each round the reliable blocks are
  eventually held, which is `qp` authors.
* **A safe leader's slot commits** (`SafeCommits`) on every reliable
  validator's own view from some time on, when `T` meets the commit
  threshold: the view holds every reliable decision-round block, and each
  certifies the safe block. This and the counts give `CoinLive`.
* **Every window commits, and every slot below a run is decided**
  (`CommitsWithin`, `AllDecidedBelow`), on every reliable validator's own
  view from some time on, under `SafeWithin` and `SafeRunWithin`. On one
  view these are `WindowsCommit` (every window of `c` slots below the
  horizon has a committed slot) and `PrefixDecided` (for each slot `k`
  below the horizon, every slot below some `b ≥ k` is decided).
* **Every timed run is an asynchronous one** (`OfPaceCore`): the trunk,
  with a progress rule at `qp`, forgets its clock.

`LeanDagTest/Scheme/AsyncLocal.lean` reads the hybrid three-replica run
of §13, with its clock forgotten, as an asynchronous run at `qp = 2`:
every leader block is safe there, and every slot, and every window of one
slot, commits on each live replica's own view from some time on. On the
starving execution of four validators at the Mahi-Mahi row of wave five,
`CoinLive` gives probability at least `1/2`.

### 11.2 Across waves

The record and its pacing are fixed before the coins are drawn: the
adversary does not see the coin. `Scheme/Model/AsyncLive.lean` defines
`coinSlots S₀ h coin`, the schedule on the rounds and kinds of `S₀`,
whose rounds strictly increase, in which slot `s` is led by `coin s`. The
coins of `M` blocks of `d` consecutive slots from slot `s₀` are uniform and
independent (`Steelhead.coinOfBlocksFrom`), and `AsyncPace.UndecidedBelow`
is the set of draws under which some slot below `s₀` is not decided on
every reliable validator's own view from some time on.
`Scheme/AsyncLive/Statement.lean` states, and `Proof.lean` proves, when
every `d` consecutive slots of `S₀` span eligibility, at every row and
vote:

* **the tail** (`Tail`): when the safe set of every block slot holds at
  least `c` validators, `UndecidedBelow` has probability at most
  `((n^d − c^d)/n^d)^M` (`Steelhead.Coin.badBlockBoundAt c d ^ M`). A block
  of `d` safe coins is a run of `d` slots that commit
  (`decided_of_safe_of_holds`), and a run that spans eligibility decides
  every slot below it (`AnchoredRule.decided_below_of_run`); a draw outside
  every such block is counted by `Steelhead.no_good_block_prob_le`;
* **the tail vanishes** (`Vanishes`) at `c ≥ 1`;
* **the rows ready for the count** (`Live`): the floor `c` is `1` at one
  buffer round, `q − f` at two, and `⌈n/3⌉` at one buffer round where
  `n ≥ 5f + 3c + 1` and `q = n − f − c` (`floors`).

At a schedule with one slot per wave, `slotRound s = s · waveLength`,
`d = 1` spans eligibility and the bound is `((n − c)/n)^M`; at one slot per
round, `d = waveLength` (`spansEligible_of_identity`).

**Not formalised.** The coin's construction, an adversary that sees the
coin, and the probability for `K` leaders per round. With `K` leaders
drawn without replacement the chance that none is safe is
`C(n − G, K)/C(n, K)`, which `MultiLeader` bounds only at
`K > n − G`, and `coinSlots` asks for one slot per round.

## 12. Every row, safe and live

The family's theorems are stated over any row meeting their hypotheses;
`Scheme/Rows/Statement.lean` states, and `Proof.lean` proves, that every
row meets them. At every local vote:

* **On the core's universes** (`CoreRows`): Cordial Miners PS and Async
  are safe and live, progress and inclusion, at every `n ≥ 3f + 1`.
* **Under the hybrid fault model** (`HybridRows`), on records that also
  ask self-reference (`HybridValid`): Orcaella and Async Orcaella from
  `n ≥ 5f + 3c + 1`, Hybrid Mysticeti, Hybrid Mahi-Mahi at every wave of
  three or more, and, with no Byzantine replica, Nemo-Nemo and Async
  Nemo-Nemo, are safe and live. This reads `HybridRow.WithSelfParent`,
  now stated for every row covered at `q = n − f − c` whose commit
  threshold is within `q` (and `HybridRow.OnHydrozoan`, progress on
  Hydrozoan's own universe, likewise).
* **The asynchronous rows are ready for the count of §11** (`AsyncRows`,
  `Params.AsyncReady`: `2q ≥ n + f + 1`, the buffer rounds, and the
  certificate and commit thresholds within `q`): one buffer round for
  Mahi-Mahi and Hybrid Mahi-Mahi at wave four, Blue Bottle Async, Async
  Orcaella and Async Nemo-Nemo; two for Mahi-Mahi and Hybrid Mahi-Mahi at
  wave five and Cordial Miners Async.

The rows with no reference algorithm get every result of the family; what
they lack is a comparison with an implementation.

## 13. The family, run reactively

A responsive validator builds as soon as what the rule counts has
arrived, with the timeout only as a fallback. The reactive timing is the
development's (`ReactiveCore`, `Reactive/Basic.lean`);
`Scheme/Model/Reactive.lean` defines `SchemeReactive`, at a quorum `q`,
which adds the pacemaker's progress rule at `q` and the family's wait
clauses, one per round of the wave:

* **advance at `q`** (`advancesAt`): a reliable validator holding `q`
  distinct round-`n` authors gets past round `n`;

* **reach or wait**, at each round from the one above the proposal to the
  vote round: a reliable block already reaches the slot's leader block, or
  its builder waited the timeout and references the leader's block of the
  round below if it holds it;
* **certify or wait**, at the decision round where votes are certified a
  round later: a reliable block already certifies the leader block, or its
  builder waited the timeout and references every reliable vote for it
  that it holds.

At the Mysticeti row these are Reactive Mysticeti's `vote_or_wait` and
`cert_or_wait`.

The development's pacing trunk (`PaceCore`) advances on the core's quorum
`n − f`, read off a `Faults` instance, which asks `n ≥ 3f + 1`. Reading
the hybrid fault bound `f + c` into it fails exactly at the hybrid
committees (`3(f + c) + 1 > 3f + 2c + 1` at `c ≥ 1`, and
`3c + 1 > 2c + 1`). `SchemeReactive` therefore reads the trunk at a fault
model with no faults (`noFaults`), where every committee is admitted and
the trunk's own progress clause is implied by `advancesAt`, and carries
the quorum `q` in `advancesAt`. With the reliable set `q` strong every
reliable validator reaches every round below the horizon, and every
round is populated: the run with its clock forgotten is asynchronous
pacing at `q` (`SchemeReactive.toAsyncPace`, §11.1), whose production
needs no clock. Drift collapses past GST
(`SchemeReactive.driftOn`, from the trunk's `drift_collapse`). The
precondition `reactiveLive` is stated at a reliability `rel`, pacing at
`q = n − rel.slack`: the core's `n − f`, Hydrozoan's `n − f − c`, Nemo's
majority.

`Scheme/Reactive/Statement.lean` states, and `Proof.lean` proves, at every
row and vote, past GST with the timeout clearing `2Δ + proc`:

* **every reliable decision-round block certifies** a reliably-led slot's
  leader block (`Certifies`), when the reliable set is `q` strong and the
  certificate threshold within `q`. A reliable block that waited holds every
  reliable block of the round below (`SchemeReactive.arrives`: built at
  most `Δ + proc` later, arriving `Δ` after); round by round from the
  proposal every reliable block reaches the leader block, on the exit by
  the clause and on the fallback through the leader's own block
  (`SchemeReactive.reaches`); a reliable vote-round block then votes, and
  a reliable decision-round block certifies, its vote being the
  certificate or its fallback referencing every reliable vote;
* **the reactive precondition is the family support's**
  (`Live`, `live_of_reactiveLive`), so **a reliably-led slot commits**
  (`Commits`, the generic `LeaderCommits`) at every reliability whose
  quorum meets the commit and certificate thresholds;
* **no reliable block is censored** (`Includes`, `includes_reactive`), on
  records whose blocks reference their author's previous block, under a
  schedule fair to each reliable validator: a reliable validator's block
  enters the ledger through the next slot its author leads, its leader
  block reaching it down the author's own chain. A reactive builder omits
  what has not arrived, so coverage, from which the timed runs draw
  inclusion, fails; the argument is the generic
  `committed_of_correct_block` over the reactive `LeaderCommits`, as
  Reactive Mysticeti's RS5 is;
* **Reactive Mysticeti is an instance** (`OfMysticeti`, `ofReactiveM`):
  every Reactive Mysticeti execution with a correct reliable set is the
  family run reactively at the Mysticeti row, at every vote, pacing at
  `n − f`.

`LeanDagTest/Scheme/Reactive.lean` converts the Reactive Mysticeti witness
`ugrowReactive`, in which no validator ever waits a timeout, shows it meets
the family's reactive precondition, and commits a reliably-led slot.
`LeanDagTest/Scheme/ReactiveHybrid.lean` runs the Hybrid Mysticeti row
reactively at three replicas, none Byzantine and one crashed
(`f = 0, c = 1`, `q = 2`), a committee the core's fault model excludes:
the two live replicas build at spacing `6` inside a timeout of `9`, the
execution meets the reactive precondition at Hydrozoan's reliability, and
a reliably-led slot commits. On both witnesses a reliable validator's
round-`1` block enters the ledger through a slot its author leads
(`ugrowScheme_includes`, `hyReactive_includes`); on the second, replica
`0` never builds.

## 14. The family under Barnacle and HammerHead schedules

Barnacle (`LeanDag/Barnacle/`) and HammerHead (`LeanDag/Adaptive/`) are
stated over any Barnacle live rule. `Scheme/Model/Schedules.lean` reads
the decider as one, `schemeLive p σ rel`, through
`Barnacle.liveOfAnchored`; the decider's wave does not depend on the slot,
so the adapter's wave condition is `rfl`, and `schemeLive`'s wave length
is `p.waveLength`. `Scheme/Schedules/Statement.lean` states, and
`Proof.lean` proves, at every vote:

* **safety under every update rule** (`Safe`): at every row with
  `p.Tolerates honest f q`, two runs agree on the configurations, the
  anchors and the verdicts, and under an update rule that does not read
  the view the ledger is agreed, grows by appending, and holds no block
  twice. The only laws read are `Scheme.agree` and
  `Scheme.commitsCandidate`;
* **the descent laws at slack `rel.slack`** (`Descends`), when
  `rel.correct ⊆ honest`, the wave is at least two (three where votes are
  certified a round later), and `n − rel.slack` meets the certificate and
  commit thresholds. This is `Timed.descent_of_support` at
  `familySupport`, with the gap of `Scheme.indirect`;
* **every height under a schedule whose heads come in runs**
  (`RunsExist`, Barnacle's BN11): if every set missing at most `rel.slack`
  validators leads `p.waveLength` consecutive heads within every `c₀ + 1`
  rounds, an update rule that keeps the heads and the bounds reaches every
  height whose horizon fits;
* **Barnacle's AIMD rule** (`Aimd`) and **every HammerHead score**
  (`HammerHead`) over the decider: at a row meeting `Params.Scheduled n
  rel.slack` (`cert ≤ n − slack`, `commit ≤ n − slack`,
  `waveLength · slack + 1 ≤ n`), the AIMD rule on a leader function whose
  first leader is round-robin, and a score that keeps the shape and whose
  output's heads are a permutation of round-robin (`PermRR`), reach every
  height with gap `n + waveLength − 1`. A HammerHead score is safe at every
  tolerated row with no clause on the score;
* **the partially synchronous rows meet `Params.Scheduled`**
  (`RowsScheduled`): Mysticeti and Cordial Miners PS at slack `f` from
  `3f + 1`, Blue Bottle PS from `5f + 1`, Orcaella at slack `f + c` from
  `5f + 3c + 1`, Nemo-Nemo at slack `c` from `2c + 1`, and Hybrid
  Mysticeti at slack `f + c` from `3f + 3c + 1`.

Three limits. Barnacle's configurations have a slot in every round, so
the schedules it emits are pipelined; a row run with one slot per wave is
not one of them. Barnacle's liveness reads `Timed.Good`, partial
synchrony; the asynchronous rows are safe under Barnacle and HammerHead
by `Safe`, but their liveness rests on a coin the adversary cannot
predict (§11), and a reputation schedule is computed from the committed
history. The heads argument needs `waveLength` consecutive reliable heads, which
`n ≥ waveLength · (f + c) + 1` guarantees under round-robin.

**Silent crashes.** After every crash has happened a crashed validator
authors no block. `Timed.SilentGood rel fb` adds to `Timed.Good` a set `Z`
of validators with no block from the good round on, with at most `fb`
validators outside the synchronised quorum and `Z`. A slot led by a member
of `Z` has no candidate, so at a vote round one above the proposal and a
skip threshold within `n − rel.slack` it is skipped directly
(`Scheme.skipsUnsupported`). `schemeLiveSilent p σ rel fb` is the decider
with this goodness, and it is `LiveRule.Decisive`: the quorum commits the
slots it leads and the quorum with `Z` decides the slots it leads
(`SilentDescends`). A slot is then decided below `w − 1` rounds of decided
slots and a committed head (`Barnacle.liveOn_of_skipRun`, the stretch
descent over the whole run), and on one slot per round a permutation of
round-robin has such runs once `(w − 1)·fb + slack + 1 ≤ n`
(`Barnacle.skipRun_perm_roundRobin`: positions whose head is outside the
quorum number at most `slack`, and positions with a head outside `D` among
the `w − 1` before them inject into `Fin (w − 1) × Dᶜ`). Every update rule
that keeps one slot per round and the heads a permutation of round-robin,
HammerHead's scores among them, reaches every height (`SilentLive`,
`HammerHeadSilent`) at `Params.SkipScheduled`, which Mysticeti, Blue Bottle
PS, Orcaella and Hybrid Mysticeti meet at their committees with `fb = f`
(`RowsSkipScheduled`; Hybrid Mysticeti needs `3f + c + 1 ≤ n`). Cordial
Miners PS and Nemo-Nemo have no direct skip and meet `Params.Scheduled` at
their committees. With several leaders per round the run would need every
slot of its rounds decided, so Barnacle's AIMD rule keeps
`n ≥ waveLength · (f + c) + 1`, which Hybrid Mysticeti meets from
`3f + 3c + 1`.


## 15. Byzantine atomic broadcast

Issue #57. The family is checked against two definitions, stated so that
each Lean statement reads against one clause of a paper:

| Paper clause | Lean |
|---|---|
| Sailfish, Def. 1, Integrity: per round `r` and author `P_k`, at most one `a_deliver` | `AtomicBroadcast.Integrity` |
| Sui–Duan, Def. 2.1, Integrity: each message at most once, and only a broadcast one | `AtomicBroadcast.IntegritySD` |
| Sailfish, Total order: `x` before `y` at `P_i` ⇒ not `y` before `x` at `P_j` | `AtomicBroadcast.TotalOrder` |
| Sui–Duan, Total order: `x` before `y` at one ⇒ `y` at another only after `x` | `AtomicBroadcast.TotalOrderSD` |
| Sailfish and Sui–Duan, Agreement | `AtomicBroadcast.Agreement` |
| Sailfish, Validity: an honest sender's message delivered by every honest party | `AtomicBroadcast.ValidityPS`, `AtomicBroadcast.ValidityRoundRobin`, `AtomicBroadcast.ValidityAsync` |
| Sui–Duan, Liveness: an honest sender eventually delivers its own message | `AtomicBroadcast.LivenessPS`, `AtomicBroadcast.LivenessAsync` |

A delivered message is a block; `deliverSeq` delivers committed leaders'
histories in order of round and block id, keeping the first block of each
round and author, so a Byzantine author's equivocating blocks are
delivered once. An honest party is a validator holding a view; the order
of a delivered sequence is the order of output, since sequences only grow
(`Grows`, `RunGrows`). Agreement and, when stated, validity are for the
reliable validators of a run. The adversary's adaptivity and payload-level
deduplication are out of scope.

**Validity.** Partially synchronously, the author leads a slot past GST at
or above its block's round, followed within the horizon by a run of
reliably-led slots spanning eligibility: the slot commits on the author's
own view, the run decides every slot below it, and the leader block
reaches the block by self-reference. Under round-robin on one slot per
round, at `waveLength · (n − |T|) < n`, every rotation holds such a run, so
the premise reduces to a horizon of `n · (max R r + 2) + 2 · waveLength`
(`ValidityRoundRobin`). Asynchronously, against a coin-blind
adversary, the author's block of some round `r` is referenced by every
reliable block of round `r + 1`; the failure probability over `M` blocks
of coins from round `r + 2` is at most `badBlockBoundAt c d ^ M`. That
condition cannot be dropped: references reach one round down
(`Validity.Mechanised.pred`), so a reliable validator the adversary keeps
late at every round builds blocks that no later block references, and
Sailfish's weak edges to older rounds have no counterpart in the model.

## 16. Responsive liveness at every partially synchronous row

`docs/mechanisms.md` M1; statement `Scheme/Responsive/Statement.lean`.

| Claim | Lean |
|---|---|
| The partially synchronous rows at their committees, parent quorum `n − f − c` | `Params.PSRow` |
| A responsive run exists at every such row, every vote and every schedule | `Responsive.Inhabited` (`Full.record`, `Full.run`) |
| Validity (Sailfish) and the author's own delivery (Sui and Duan) at every such row | `Responsive.RowsValidity` |

The witness is the full record run in lockstep: every block references the
whole round below, so every block reaches every block of a lower round and
every decision-round block certifies every leader block, and no validator
waits a timeout. Validity at a row is `AtomicBroadcast.ValidityPS` with the
row's coverage (`Table.RowsCovered`) and threshold fits discharged; the
reactive run itself remains its premise, as GST is.

## 17. Crash recovery, partially synchronous

`docs/mechanisms.md` M2; statement `Scheme/Crash/Statement.lean`.

| Claim | Lean |
|---|---|
| A crash run read past `max gst tr` is a responsive run | `Crash.ToReactive` (`CrashRun.toReactive`) |
| The crash precondition is the reactive one | `Crash.Live` (`crashLive`) |
| A reliably led slot commits past `max gst tr` | `Crash.Commits` |
| Validity at every partially synchronous row | `Crash.RowsValidity` |
| Every validator may crash at once | `Crash.Inhabited` (`Full.crashRun`) |

The model separates what a crash leaves intact (the disk, the rounds
rebuilt on restart, the wait rule with timers set again) from what needs
the validator running (delivery, catch-up, the timeout ceiling). The
reactive timing's ceiling and wait clauses are asked only past GST, which
is where the proofs read them; that change is what lets a run with crashes
before `tr` be a responsive run past `max gst tr`.

## 18. Crash recovery, asynchronous

`docs/mechanisms.md` M3; statement `Scheme/Crash/Statement.lean`.

| Claim | Lean |
|---|---|
| An asynchronous crash run is an asynchronous run | `Crash.AsyncToPace` (`AsyncCrashRun.toAsyncPace`) |
| Agreement | `Crash.AsyncAgreement` |
| Validity with probability 1, coin-blind adversary | `Crash.AsyncValidity` |
| Every validator may crash at once, at every quorum | `Crash.AsyncInhabited` (`CrashRun.toAsync`) |

## 19. Checkpoints over responsive and crash runs

`docs/mechanisms.md` M5b; statement `Scheme/Compose/Statement.lean`.

| Claim | Lean |
|---|---|
| A reliably led slot reaches second-tier finality over a responsive run | `Compose.CheckpointsResponsive` |
| The same with crashes and restarts, past `max gst tr` | `Compose.CheckpointsCrash` |

## 20. The decider under schedules, run responsively

`docs/mechanisms.md` M5a; statement `Scheme/Schedules/Statement.lean`.

A responsive validator waits only for the leaders its schedule names, so
Barnacle's goodness takes the schedule (`LiveRule.Good S U Rnd N`), and a
responsive run says up to which round it waits for them
(`SchemeReactive.waits`, the horizon under a fixed schedule).
`schemeLiveReactive p σ rel` is the decider as a Barnacle live rule whose
DAG is good under `S` when a quorum of `rel` runs it responsively under
`S` past GST and waits for `S`'s leaders up to the horizon
(`reactiveGood`). It has the descent laws at every reliability whose
quorum meets the commit and certificate thresholds (`ReactiveDescends`):
the run's certificates feed the family's commit law
(`familySupport_commits`), and the indirect rule is the family's.

The boundary. A new configuration's first rounds come before its
validators learn the pivot that fixes it — about a wave under Barnacle,
which starts it after the pivot's round, up to the gap and a wave under
HammerHead, which starts it at the threshold — so no validator waits for
its leaders there. Its schedule is therefore good only `δ` rounds after its
start, and the slots of the rounds before are decided by a later commit
(`LiveRule.SettlesBelow`, from a run of heads by the stretch descent,
`settlesBelow_of_headsRun`). Validators keep waiting for the old
configuration's leaders until its range closes. The progress step looks
for the anchor from the later of the threshold and the good start
(`progress_exists`), and runs of every height exist under the hypothesis
that each configuration's schedule is good from `δ` past its start up to
the round its step needs, unless the run has already moved past it
(`Barnacle.Live.RunsExistFrom`, horizon `horizonFrom`).

| Claim | Lean |
|---|---|
| Every height, run responsively, under a schedule whose heads run | `Schedules.RunsExistReactive` |
| The same under Barnacle's AIMD rule | `Schedules.AimdReactive` |
| The same under every HammerHead score permuting round-robin | `Schedules.HammerHeadReactive` |
| Responsive goodness under every schedule is inhabited at every row | `Schedules.ReactiveGoodInhabited` |
