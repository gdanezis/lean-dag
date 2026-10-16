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
  `n ≥ 5f + 3c + 1`.
* **The commit loop computes the relation** (`Scheme.Loop.holds`, §8).
  `tryDecide`, the scheme's `TryDecide` as a function of a view, outputs
  only verdicts `Decided` derives from that view, at every row and vote
  with positive link and certificate thresholds. At the rows the
  inequalities cover it outputs every derived verdict once its scan
  reaches far enough, and two validators' outputs are prefix-comparable.

**What the table claims and does not hold, or holds otherwise.**

1. **Nemo-Nemo is no solution of the two-round inequalities.** At
   `f = 0`, `n = 2c + 1` and `c ≥ 1`, its commit plus link is `c + 2`,
   below `n + 1 = 2c + 2` (`Table.NemoNotTwoRound`). The table's "Nemo-Nemo
   at `f = 0`" does not follow from the inequalities; their solution at
   `f = 0` is Orcaella's `n = 3c + 1`. The inequality that fails guards
   against equivocating twins, which a crash-only model excludes, so
   Nemo-Nemo is safe for a reason the table does not state.
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
   crash faults enter only through `q`.

**Open.** Liveness of every row not equal to a rule of this development,
and of the buffer-round rows at votes other than the least; Async
Nemo-Nemo's safety, which the inequalities do not give; and the commit
loop's restart at the last consumed decision.

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
guards against an equivocating twin, which the crash model excludes.

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

**Open.** The asynchronous derived rows; the laws of the derived rows
(both settled by §7 but for Async Nemo-Nemo).

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
rounds downward and leader indices downward, is slot order reversed.

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

**Open.** The restart at the round of the last consumed decision.
