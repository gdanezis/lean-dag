# Mechanisms over the scheme: plan

This document plans the proofs the paper's §4 needs: responsive liveness,
crash recovery, and leader scheduling, each over the scheme's protocol
model (not the executable validator of PR #53), and their composition
with each other and with checkpoints. Branch `mechanisms`, cut from
`atomic-broadcast` (PR #58, stacked on #55).

## 0. Decisions taken (user, 2026-11-13)

* **Asynchronous scheduling** is Barnacle's adaptive leader count: the
  number of coin-elected leaders per round adapts to the committed
  history; the coin still picks who leads. No reputation-filtered coin.
* **Crash recovery**: a restarted validator rebuilds every round it
  missed, so its self-parent chain stays whole. Validators may restart
  until a time `t_r`; the reliable ones stay up from then on. Every
  validator may crash, and the case with every honest validator reliable
  covers "all crashed and restarted".
* **Responsive liveness** is complete when a responsive run exists at
  every partially synchronous row and atomic broadcast's Validity and
  Liveness follow from it at every such row.
* **Composition**: all four mechanisms (responsive liveness, crash
  recovery, scheduling, checkpoints) compose under partial synchrony;
  crash recovery, scheduling and checkpoints compose under asynchrony.

## 1. What exists

| Piece | Where | Reads |
|---|---|---|
| Responsive run at quorum `q` | `SchemeReactive` (`Scheme/Model/Reactive.lean`), extends `ReactiveCore` → `PaceCore` | premise bundle over a fixed record `U` and a fixed `Slots` |
| Its claims | `Scheme.ReactiveRun.{Certifies, Live, Commits, Includes, OfMysticeti}` | `reactiveLive` |
| Asynchronous run | `AsyncPace` (`Scheme/Model/AsyncPace.lean`); `SchemeReactive.toAsyncPace` | eventual delivery |
| Coin liveness | `Scheme.AsyncLive.holds` (tail bound), `Scheme.Async.holds` (safe-leader counts) | one leader per wave, or a slot every round |
| Atomic broadcast | `Scheme.AtomicBroadcast.{ValidityPS, LivenessPS, ValidityRoundRobin, ValidityAsync, LivenessAsync}` | `SchemeReactive`, `AsyncPace` |
| Scheduling | `Scheme.Schedules` over `schemeLive p σ rel = liveOfAnchored … rel`, whose `Good` is `Timed.Good` | timed run, partially synchronous rows |
| Checkpoints | `Integration/SchemeCheckpoint.lean` (`commitFinalized_scheme`, `liveCommitFinalized_classes`, `commitFinalized_barnacle_scheme`) | agreement; commit of a reliably led slot as a premise |

## 2. Gaps closed by this plan

1. `SchemeReactive` is shown inhabited only at the Mysticeti row.
2. `ValidityPS` excludes Nemo-Nemo (no self-parent clause in its
   validity) and lacks round-robin at Hybrid Mysticeti's `3f + 2c + 1`.
3. No crash or restart in any scheme run model.
4. Scheduling's liveness is over the timed run, not the responsive one,
   and the asynchronous rows have no scheduling liveness.
5. No theorem joins checkpoints with the responsive run, the asynchronous
   run, or crashes.

## 3. Steps

Each step: full build, standard axioms, six audits, a section in
`docs/scheme.md` (§16 on), report §27.x, commit and push.

### M1. Responsive runs at every partially synchronous row

* **M1a. Witness.** A lockstep execution in which every validator is
  reliable, every block references every block of the round below, and
  round `n` is built at `n · (delay + proc)`; show it is a
  `SchemeReactive` at every partially synchronous row and vote rule
  (`ReactiveRun.Exists`). Every leader block is reached and certified at
  once, so the wait clauses hold by their first disjunct.
* **M1b. Nemo-Nemo.** The paper's row adds a self-parent to Nemo-Nemo;
  state Validity at the row with the self-parent clause, so that
  `ValidityPS` covers all six rows.
* **M1c. Round-robin at Hybrid Mysticeti's bound** (pending on PR #58).

### M2. Crash recovery, partially synchronous

* **Model** `Scheme/Model/Crash.lean`: `CrashRun` over a record `U`, a
  reliable set `T`, and per-validator down intervals ending by `t_r`.
  Clauses: a validator writes a block to disk before sending it and
  holds after a restart what it held before the crash (persistence); it
  never builds a round twice; on restart it resends its latest block,
  asks again for what it lacks, and builds every round it missed; the
  network delivers between validators that are both up, within `Δ`
  after GST; timers set before a crash are lost.
* **Theorem `Crash.ToReactive`**: from `G = max t_r gst + W`, `W` twice
  the largest timeout of the round below the one a reliable validator
  is at by `max t_r gst`, the run restricted to rounds built after `G`
  is a `SchemeReactive` with `gst := G`. All of M1 and `AtomicBroadcast`
  then apply.
* **Safety** needs only "never builds a round twice", which keeps
  honest blocks unique per round, so the record is a `BlockRecord` and
  every safety theorem applies unchanged.

### M3. Crash recovery, asynchronous

* The same `CrashRun` without clocks: delivery is eventual between
  validators that are both up from some time on.
* **Theorem `Crash.ToAsyncPace`**: from `t_r`, an `AsyncPace` on the
  rounds above the one every reliable validator is at by `t_r`;
  `AsyncLive` and `ValidityAsync` then apply to the slots above it.

### M4. Scheduling under asynchrony

* Barnacle's AIMD count of leaders per round, leaders drawn by the coin.
  Safety is `Schedules.Safe`, which covers every row already.
* **Liveness with probability 1**: in each round only the first slot is
  needed (as in the partially synchronous argument). Its coin leader is
  safe with probability at least `s / n` (`Scheme.Async` counts), so the
  `AsyncLive` tail bound gives that every configuration height is
  reached with probability 1. New statement:
  `Schedules.AsyncLive` over a coin-elected `Slots` family.
* Risk: Barnacle's `Run` is deterministic per view; the probabilistic
  claim must be stated over the coin's outcomes, as `AsyncLive` does.

### M5. Composition, partially synchronous

* **M5a.** `schemeLiveReactive`: the scheme as a Barnacle live rule with
  `Good := reactiveLive`; prove the descent laws from
  `ReactiveRun.Commits`, so `Schedules` liveness holds over the
  responsive run.
* **M5b.** `liveCommitFinalized` with its commit premise supplied by
  `ReactiveRun.Commits`: checkpoints over the responsive run.
* **M5c.** One theorem: a `CrashRun` past `G`, under an anchored update
  rule, gives atomic broadcast over the scheduled ledger, every height
  reached, and every committed slot finalized by the checkpoint tier.
* Risk: `SchemeReactive` fixes one `Slots`; under scheduling the
  schedule changes per configuration, so the wait clauses must be
  stated per configuration (a `Slots` per configuration range). This is
  the step most likely to need a model change.

### M6. Composition, asynchronous

* A `CrashRun` past `t_r`, under the AIMD count with coin leaders: every
  height reached with probability 1, atomic broadcast over the scheduled
  ledger, and every committed slot finalized.

### M7. Paper

Replace the `\george` notes of §4 by the results, as `\edits{…}`.

## 4. Status

* **M1a, M1b done.** `Scheme.Responsive.{Inhabited, RowsValidity}`
  (`Scheme/Responsive/`, `Helpers/FullRun.lean`, `scheme.md` §16, report
  §27.17). M1b needed no new argument: Nemo-Nemo was never excluded by
  the Lean statement, which asks self-reference of the record, not of the
  published protocol; its coverage is the crash-only one.

* **M2 done.** `Scheme.Crash.{ToReactive, Live, Commits, RowsValidity,
  Inhabited}` (`Model/Crash.lean`, `Scheme/Crash/`, `Full.crashRun`,
  `scheme.md` §17, report §27.18). `ReactiveCore.deadline` and
  `SchemeReactive`'s wait clauses are now asked only past GST; no proof
  read them before it. The executable's `W` (timers re-armed after a
  restart) has no counterpart: the model's timers are set again at the
  restart, so the wait clause holds of every block.

* **M3 done.** `Scheme.Crash.{AsyncToPace, AsyncAgreement, AsyncValidity,
  AsyncInhabited}` (`AsyncCrashRun`, `CrashRun.toAsync`; `scheme.md` §18,
  report §27.19).
* **M5b done.** `Scheme.Compose.{CheckpointsResponsive, CheckpointsCrash}`
  (`scheme.md` §19, report §27.20).
* **M5a decision (user, 2026-11-13).** A responsive validator waits for the
  leaders of the configuration in force, and past its interval keeps
  waiting for the old configuration's leaders until the pivot commits.
  Barnacle's goodness must therefore be indexed by schedule; the run
  hypothesis: the DAG is good under each configuration's schedule as long
  as no slot past its interval has committed.

* **M5a, steps 1–2 done.** Barnacle's goodness takes the schedule
  (`LiveRule.Good`, `LiveRule.Descent` its own structure,
  `LiveRule.Descent.ofProperties`); a responsive run's wait clauses stop
  at `SchemeReactive.waits`; `schemeLiveReactive` and
  `Schedules.ReactiveDescends` (`scheme.md` §20).
* **M5a, step 3 (next).** A new configuration's first rounds precede the
  validators' learning of the pivot that fixes it (about a wave under
  Barnacle, up to the gap and a wave under HammerHead), so its leaders are
  not waited for there. Plan: generalise `LiveOn` so that slots below the
  round goodness starts are decided by a later commit (stretch descent),
  and state every height under the hypothesis that each configuration's
  schedule is good from its start plus a learning delay up to the round
  its range closes, unless the run has already extended.

## 5. Order

M1a → M1b → M2 → M5a → M5b → M5c → M3 → M4 → M6 → M1c → M7.
Partially synchronous first, since M5 depends on M2 and M1; M1c is
independent and may move.
