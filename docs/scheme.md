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

`Scheme.ReadAlike` is what `Decided` reads; `ReadAlike.decided_iff`
proves that two rules agreeing on it decide alike, and `toDagRule_eq`
that their carriers are equal. One round above the candidate, a vote is a
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

Async Nemo-Nemo agrees by the inequalities where nobody equivocates
(§7.1).

## 6. The rows with buffer rounds at every vote

`Scheme/Safety/Statement.lean` states, and `Proof.lean` proves:

* **`VotedBlock` is a vote-selection rule** for every parent order that
  lists every parent (`VotedBlockIsVote`). The search walks references as
  `historyUpto` does; at a block of the record a reference lies one round
  down, so pruning at the slot's round loses no block of the slot.
* **The three rows have the laws at every vote.** Mahi-Mahi at `w ≥ 3`
  and Cordial Miners Async meet the three-round inequalities, and Blue
  Bottle Async at `n ≥ 5f + 1` the two-round ones, at `q = n − f`; on the
  core's universe the correct validators never equivocate, so §7 gives
  the laws.

Each row's carrier then has `Agree` (`MahiMahiAgree`,
`CordialMinersAsyncAgree`, `BlueBottleAsyncAgree`). The properties of
Mahi-Mahi and Async BlueBottle beyond agreement, liveness among them,
are proved of those rules, and transfer to the rows only at the least
vote (§5).

## 7. The table's inequalities suffice

`Scheme/Sufficiency/Statement.lean` states, and `Proof.lean` proves, at
every vote-selection rule, on records whose blocks reference `q` distinct
authors one round down (`Validity.Quorate q`) and whose validators
outside a set `Hon` of all but `f` never equivocate:

* **Two rounds** (`TwoRoundAgree`, from `twoRoundLaws`): a row whose vote
  is its certificate, with a wave of at least two, meeting
  `TwoRound n f q`, agrees.
* **Three rounds** (`ThreeRoundAgree`, from `threeRoundLaws`): a row that
  certifies votes one round later, with a wave of at least three and a
  link of one certificate, meeting `ThreeRound n f q`, agrees.
* **The derived rows** (`HybridRowsAgree`, `OrcaellaRowsAgree`): Hybrid
  Mysticeti and Hybrid Mahi-Mahi at `n = 3f + 2c + 1`, `q = 2f + c + 1`,
  and Orcaella and Async Orcaella at every `n ≥ 5f + 3c + 1`,
  `q = n − f − c`, by `Table.holds`.

Every step is one of two counts. Two sets of same-round blocks whose
authors number more than `n + f` together share a block
(`exists_common_block`), and that block selects at most one block of a
slot and does not blame a slot it selects in: this gives each inequality
of the form `n + f + 1 ≤ a + b`. A block above `c` authors'
decision-round blocks holds at least `c + q − n − f` of them in its
history (`card_inHistory_ge`): this gives visibility, the inequality
with `q`. In the two-round family the third inequality and `q ≤ n` give
`commit ≥ link + f`, which the cases of two direct commits, and of a
direct commit and a direct skip, need.

### 7.1 Where nobody equivocates

When `Hon` is every validator (`f = 0`), a slot has one block
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

* **Agreement** (`TwoRoundCrashAgree`, `ThreeRoundCrashAgree`, from
  `twoRoundCrashLaws`, `threeRoundCrashLaws`): a row meeting them agrees
  on records where nobody equivocates, at every vote.
* **The table** (`Table.CrashWeaker`, `Table.CrashRows`,
  `Table.CrashBound`): at `f = 0` the inequalities imply these;
  Nemo-Nemo and Async Nemo-Nemo meet the two-round ones at `n = 2c + 1`,
  `q = c + 1`. With `q = n − c`, a two-round row needs `n ≥ 2c + 1`, and
  `n ≥ 3c + 1` when its skip is within the liveness bound, where
  Orcaella's thresholds at `f = 0` are forced; a three-round row needs
  `n ≥ 2c + 1`, where Hybrid Mysticeti's at `f = 0` are forced. A direct
  skip within the bound costs a two-round row `c` validators, and
  Nemo-Nemo's "no direct skip" saves them.
* **The Nemo rows** (`NemoRowsAgree`): Nemo-Nemo and Async Nemo-Nemo
  agree at `n = 2c + 1`, `q = c + 1`, where nobody equivocates. A test
  instantiates Async Nemo-Nemo on Nemo's universe, whose majority quorum
  is `c + 1`.

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
`schemeRule p σ Hon` (`Model/Local.lean`), the decider on the records
where `Hon` does not equivocate:

| Property | Holds at |
|:---|:---|
| `Banded` | every row with a wave of at least two and positive link and certificate thresholds, at a local vote (`banded`) |
| `CommitsCandidate`, `CommitsDirect`, `Indirect` | every row and vote |
| `SkipsUnsupported` | every row whose vote round is one above the slot |
| `Quorate`, `NoEquiv` | from validity's quorum and the invariant; `SelfParent` on the core's universes |
| `Agree`, `Safe` | every row meeting its inequalities, at a local vote for `Safe` (`agree`, `safety`) |
| support `familySupport` | `Local` at a local vote; `Commits` at `commit ≤ n − slack`; `OfCoverage` at `cert ≤ n − slack` (`Helpers/Support.lean`) |
| `Lives` | the core's universes, at `commit ≤ n − f` (`lives`) |

`OnRecord` is `Scheme/Record.lean`, with the prompt skip after an
extension; chain quality at the carrier is
`LeanDagTest/Quality/Generic.lean`. In `audit-conformance.py` and
`audit-mechanisms.py` the family shows every obligation, and every
mechanism but adaptive leaders, which no rule of the development has.

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
the probabilities. `Scheme/Model/Async.lean` defines `goodAt p σ U r`,
the validators whose round-`r` block the record's certificates commit
(`commit` authors of decision-round blocks certify it); `safeAt p U r`,
the honest validators whose round-`r` block every vote-round block
reaches; and the clauses `UnpredictableWithin` and
`UnpredictableRunWithin` over good leaders, `SafeWithin` and
`SafeRunWithin` over safe ones. The counts bound the safe set; the good
set contains it once the decision round is populated, and may also
contain validators whose blocks only Byzantine certificates commit.
`Scheme/Async/Statement.lean` states, and `Proof.lean` proves, on any
record whose blocks reference `q` distinct authors one round down and
whose validators outside `honest`, at most `f`, may equivocate, at every
row and vote:

**The count, with no network hypothesis.**

* **The common core** (`CommonCore`, from `exists_commonCore`): at
  `2q ≥ n + f + 1`, a block at round `r + 2` gives an honest round-`r`
  block in the history of every block from round `r + 2` up. This is the
  core's double count (`Common/CommonCore.lean`, at `q = n − f`) at a
  general quorum: some honest author collects so many honest supporters
  that every round-`(r+2)` block names one (`core_arith`). Every
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
* **A safe validator is good** (`SafeGood`): every vote-round block
  reaches its block, so votes for it; every decision-round block
  certifies it (`isCert_of_safe`, where `cert ≤ q` if votes are certified
  a round later); and a population of the decision round meeting the
  commit threshold commits it.

**Liveness under the clause, on a covering view.** A good leader's slot
commits on every view holding its decision round (`GoodCommits`); under
the single-hit clause every window commits (`CommitsWithin`); under the
run clause, when a run spans eligibility, every slot below it is decided
(`AllDecidedBelow`, the common descent with the least-id tie-break). All
three conclude on views holding every block of the record up to the
clause's horizon. §11.1 replaces that hypothesis by eventual delivery.

**The coin** (`CoinCommit`, `CoinTail`, through Steelhead's counts,
`Steelhead/Helpers/Coin.lean`, whose fault model a fault-free instance
supplies inside the proofs): a uniform coin names a safe leader with
probability at least `1/n` at one buffer round and `(q − f)/n` at two;
`m` independent coins over rounds whose safe sets hold `c` validators all
miss with probability at most `((n − c)/n)^m`, which vanishes.

`LeanDagTest/Scheme/Async.lean` shows the count on data at the Mahi-Mahi
row: on `full4` every round-`0` block is good; on `starve4`, where one
honest block is referenced only along its author's own chain, the good
set is `{0, 2, 3}` at one, two and three buffer rounds alike, and the
safe set `{2, 3}`, of size `q − f = 2`. The count of two buffer rounds is
tight there, and a third buffer round adds nothing.

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
holdings.

`Scheme/AsyncLocal/Statement.lean` states, and `Proof.lean` proves, with
the reliable set `T` at least `qp` strong, at every row and vote:

* **Delivery** (`Delivered`): every reliable block of the record is held
  by every reliable validator from some time on. The record is finite,
  each of its reliable blocks is eventually held, and holdings only grow
  (`AsyncPace.exists_time`).
* **Production** (`Populated`): every round below the horizon has a block
  by every reliable validator. At each round the reliable blocks are
  eventually held, which is `qp` authors.
* **A safe leader's slot commits** (`SafeCommits`) on every reliable
  validator's own view from some time on, when `T` meets the commit
  threshold: the view holds every reliable decision-round block, and each
  certifies the safe block.
* **Every window commits, and every slot below a run is decided**
  (`CommitsWithin`, `AllDecidedBelow`), on every reliable validator's own
  view from some time on, under `SafeWithin` and `SafeRunWithin`.
* **Every timed run is an asynchronous one** (`OfPaceCore`): the trunk,
  with a progress rule at `qp`, forgets its clock.

The coin enters as before: it names a safe leader with the probabilities
of `CoinCommit` and `CoinTail`. A leader that is only good may owe its
commit to Byzantine certificates that a reliable validator never
receives, which is why the local results read the safe set.

`LeanDagTest/Scheme/AsyncLocal.lean` reads the hybrid three-replica run
of §13, with its clock forgotten, as an asynchronous run at `qp = 2`:
every leader block is safe there, and every slot, and every window of one
slot, commits on each live replica's own view from some time on.

**Not formalised.** Measurability of the safe set (it reads only rounds up
to the vote round, which is what makes the clause the coin's
consequence), and the hypergeometric probability for `K` leaders.

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
reliable validator reaches every round below the horizon
(`SchemeReactive.reached`, the trunk's induction at `q`), so every round
is populated (`SchemeReactive.populated`) and drift collapses past GST
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
