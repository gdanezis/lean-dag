# lean-dag — Barbouni: a schedule in segments

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** Proposed, not built. Nothing below is in
> the development. Results would carry **BB**-labels. Two other answers
> to the same question are recorded: `adaptive-rounds.md`, the
> composition of `Adaptive.Policy` with Barnacle, and
> `adaptive-schedule.md`, one policy emitting the whole schedule at a
> two-epoch lag. §9 compares the three.

**Barbouni** is a third answer to how an adaptive schedule may be
reassigned safely. It replaces the two-epoch lag with a structural
condition: the schedule changes only over verdicts that are already
decided, and decided verdicts are never revised.

The consequence is that the assumption the other two arcs carry —
`Adaptive.SettlesInTwoEpochs`, that a verdict settles within the window
its schedule reads — is not discharged here. It is absent.

## 1. What the lag is for

`Adaptive.Policy.adapted` has the schedule for slot `k` read the
verdicts of epochs at or below `epochOf k − 2`. The lag exists for one
reason: to make it likely that those verdicts have *settled*, so that two
validators reading them read the same thing.

`SettlesInTwoEpochs` is that likelihood made a hypothesis. It is a
theorem at the slots a rule decides directly, since a direct decision
reads the slot's own wave and nothing above it; it is not one at the
slots decided indirectly, where the derivation rests on an anchor whose
distance above the slot is the number of consecutive eligible slots that
skipped, and no bound on that holds under asynchrony.

Report §13.7 records the same question from the other side as **AL9**:
whether the anchor bound is necessary. The two are the same question, and
a model with two runs disagreeing about an undecided slot under diverging
schedules answers both.

Barbouni removes the question rather than answering it.

## 2. The mechanism

A **segment** is a schedule together with a marker saying how much of it
is to be committed.

Segment `i` assigns leaders to every slot from `n i` upward. Its slots
divide in two: those below `n (i + 1)`, which are **committed**, and
those above, which are **scaffolding**. The scaffolding is run and
decided like any other slot; its verdicts are used, and its commits are
not output.

The mechanism runs one segment at a time.

1. Read the DAG under segment `i`'s schedule.
2. A committed slot may be decided directly, or indirectly from an anchor
   — and that anchor may be a scaffolding slot, which is why the
   scaffolding is there.
3. When every committed slot of segment `i` is decided, its verdicts are
   **frozen** and appended to the ledger.
4. Segment `i + 1` — its assignment and its own marker `n (i + 2)` — is a
   deterministic function of the verdicts frozen so far. It takes effect
   from slot `n (i + 1)`, replacing segment `i`'s scaffolding.

The function reads the verdicts, commits and skips alike: a skip is the
informative case for a reputation scheme, being evidence that a leader
failed.

## 3. Why the scaffolding may be replaced

Replacing segment `i`'s scaffolding means assigning new leaders to slots
at rounds the system has already passed. That is sound because a schedule
in this development is a *reading* of the DAG and not a rule for
producing it:

```lean
IsLeaderBlock U k L := L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧
  (U.block L).creator = S.leader k
```

Nothing about which blocks exist depends on the schedule; `Populated` and
`Synchronised` are facts about the universe. Every validator produces a
block every round, and the schedule chooses which of them is a slot's
candidate. So a segment change re-reads rounds already past, and the
candidate it names is a block that is already there.

This is what makes the mechanism insensitive to *when* each validator
finishes deciding a segment. One may freeze segment `i` several rounds
before another; both then re-read the same DAG under the same segment
`i + 1`, and reach the same verdicts. There is no moment at which two
validators are running different schedules over the same rounds, because
no one is running a schedule — they are reading one.

## 4. The design

A run carries a sequence of schedules, a sequence of frontiers, and one
verdict function.

```lean
structure SegmentRun (f : (ℕ → Option BlockId) → ℕ → Slots Validator × ℕ)
    (base : Slots Validator × ℕ) (U : R.Universe) (V : R.View U) (K : ℕ) where
  sched : ℕ → Slots Validator
  frontier : ℕ → ℕ
  vdct : ℕ → Option BlockId
  init : (sched 0, frontier 1) = base ∧ frontier 0 = 0
  frontier_lt : ∀ i, i < K → frontier i < frontier (i + 1)
  closed : ∀ i, i < K → ∀ k, frontier i ≤ k → k < frontier (i + 1) →
    R.Decided (sched i) V k (vdct k)
  next : ∀ i, i < K →
    (sched (i + 1), frontier (i + 2)) = f vdct (frontier (i + 1))
```

`closed` is the whole of what a segment owes: every committed slot of
segment `i` is decided **at segment `i`'s schedule**. Its derivation may
read scaffolding slots at rounds above the frontier, and does so at
`sched i`, which is total.

`next` is the reassignment: the schedule and marker for segment `i + 1`
are a function of the verdicts and of where segment `i` ended. Nothing
restricts what `f` may read below the frontier — no lag, no epochs.

`frontier_lt` is what makes the ledger grow.

## 5. Safety

Two runs over one universe, at any two heights, agree on every segment
both have closed. The induction is over segments and it is three lines.

* Segment `0`'s schedule is `base`, so the two agree on it.
* Given `sched i` agreed, every committed slot of segment `i` is decided
  at that one schedule in both runs, so `Properties.Agree` gives
  `vdct k = vdct' k` for `frontier i ≤ k < frontier (i + 1)`.
* `f` is a function, so `sched (i + 1)` and `frontier (i + 2)` agree.

There is no band, no `DecidedFrameBelow`, and no window.
`Adaptive.frameRun_agree`'s machinery exists to establish agreement
*across* a schedule change, from verdicts that were decided at a
different schedule. Here there is nothing to establish: the change
happens only over data the previous segment already fixed.

## 6. What is absent

Three clauses the other two arcs carry have no counterpart.

**The lag.** `Policy.adapted` reads epochs two below. `f` reads the
verdicts below the frontier, which are frozen, so the schedule for a slot
depends only on strictly earlier slots and that is automatic.

**`SettlesInTwoEpochs`.** The window exists to bound where a verdict's
derivation reaches. Here a derivation may reach as far as it likes: it is
read at `sched i`, which both runs share, and no later segment re-reads
it.

**`Params.gap`.** The composition's `2 * W` rounds exist to put a count
two epochs behind every round it governs. A frontier is behind by
construction.

What replaces all three is one clause — that a segment's committed slots
are decided at that segment's schedule — and one discipline, that they
are then frozen.

## 7. Liveness

A segment closes when every committed slot of it is decided. Under
synchrony that is the shape `Adaptive.epoch_closes` already has: the
fairness clause places a stretch of reliable slots, one of them commits,
and the descent clears everything below it. Read at a segment rather than
at an epoch, it says a segment's committed prefix is decided within `c`
slots of its end, so the ledger advances a segment at a time and the
schedule is reassigned once per segment.

Under asynchrony the segment does not close and the schedule does not
change. The ledger stops growing and resumes when decisions do, which is
the behaviour wanted: a schedule reassigned on undecided data is the
failure §1 is about.

Two conditions are then worth stating rather than assuming. `f` must
place its committed prefix so that the fairness clause can hold inside a
segment — the analogue of `adaptive-schedule.md` §6's floor, and derivable
from the fairness clause the same way. And `f` must give a non-empty
committed prefix, since `frontier_lt` is what makes the ledger grow.

## 8. Immutability, and one idealisation that is not one

`closed` asserts a decision at `sched i`, a schedule defined at every
round, so a committed slot's anchor may sit at a round a later segment
re-reads under a different assignment. Barnacle's `PartialRun.closed`
makes the same assertion at `Sched getLeader hk (count k)` and there it
is an unstated assumption, since the system does run the next count at
those rounds and a validator re-reading them would derive something else.

Here it is not an assumption. Both runs use `sched i` for segment `i`'s
slots and **neither re-derives them**, so the clause defines `vdct` on the
segment rather than predicting what a validator reading a later schedule
would compute. Immutability is what turns the idealisation into a
definition, and it is the one discipline the mechanism asks that the
other two arcs do not have.

Operationally: hold segment `i`'s schedule until its committed prefix
is decided, freeze it, and move on.

## 9. Against the other two answers

| | `adaptive-rounds.md` | `adaptive-schedule.md` | Barbouni |
|:---|:---|:---|:---|
| what varies | leaders, and the count | leaders, widths, epoch length | leaders, and whatever `f` emits |
| lag | two epochs | two epochs | none |
| `SettlesInTwoEpochs` | assumed | assumed | absent |
| gap parameter | `2 * W` rounds | none | none |
| reassignment cadence | at a commit past a threshold | every epoch | when a segment closes |
| under asynchrony | the count stops moving | the schedule keeps changing | the schedule stops changing |
| ledger | one schedule's decisions | one schedule's decisions | a concatenation of segments |
| safety argument | `frameRun_agree` plus five determinisms | `frameRun_agree` plus three clauses | `Agree`, per segment |

The last row is the substance. The ledger is no longer the decision
sequence of any one schedule, so safety cannot be stated as two runs of
one schedule agreeing. It is stated segment-wise, and that is what lets
the window go.

## 10. Module plan

* `LeanDag/Barbouni/Model/Run.lean` — `SegmentRun` and its clauses.
* `LeanDag/Barbouni/Agreement/Statement.lean`, `Proof.lean` — the segment
  induction of §5.
* `LeanDag/Barbouni/Ledger/Statement.lean`, `Proof.lean` — the ledger as
  the committed prefixes concatenated, agreed, growing by prefixes, and
  holding each block once. `Barnacle.ledgerOf` is the same function of a
  verdict function and an interval.
* `LeanDag/Barbouni/Live/Statement.lean`, `Proof.lean` — a segment closes
  under the fairness clause, from `Adaptive.epoch_closes`' argument read
  at a segment.
* `LeanDagTest/Barbouni/Model.lean` — a run over `Ugrow` whose second
  segment differs from the first because a slot of the first skipped.

The statement/proof partition is the arc discipline of report §17.5,
which Barnacle follows and which this should.

## 11. Order of work

1. `SegmentRun`, and a witness at `K = 0` — every clause is about a
   segment the run has not closed.
2. §5's agreement. It is short, and it is the whole safety argument; it
   should land before anything is built on it.
3. The ledger, which is Barnacle's `Ledger` with the interval read off
   the frontiers rather than off `count k * r`.
4. Liveness at a segment.
5. A witness over `Ugrow` at `K = 2`, exhibiting a reassignment that a
   skip caused.
6. The record: a report section, **BB**-labels in Appendix A, and this
   document in the companion list.

## 12. What could go wrong

**The ledger is not one schedule's.** Every result of the development
that reads a run's decisions — `Barnacle.Validity`, the chain-quality
arc, the garbage-collection arc — is stated at one schedule. Reading them
at a segmented ledger is not automatic, and the first of them to be tried
will say how much of that is a restatement and how much is real.

**State sync replays every segment.** A validator joining late must
reconstruct `sched 0`, decide segment `0`, compute `sched 1`, and so on,
since each schedule is a function of the previous segment's verdicts.
That is sound — the chain is determined by the DAG — but it is linear in
the number of segments and it has no counterpart in a fixed schedule.

**`f` is unconstrained.** As in every arc here, no scoring rule is
modelled: what would be proved is that *any* deterministic `f` is safe
and any `f` whose segments admit the fairness clause is live. Whether a
particular `f` resists an adversary gaming it is not this arc's question.

**The scaffolding has no bound.** Segment `i`'s schedule must be defined
above its frontier, and how far the mechanism reads before the segment
closes is however far the anchors lie. Under asynchrony that is
unbounded, which is the correct behaviour and is worth stating rather
than discovering.
