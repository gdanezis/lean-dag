# lean-dag — Barnacle at a full schedule: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** Proposed, not built. Nothing below is in
> the development. Results would extend the **BN** series. The name is
> descriptive and provisional; report §21's mechanism is the one being
> extended.

Barnacle's update rule emits one number. At each pivot it reads the
window and returns the next leader count, and the schedule of a
configuration is `Sched getLeader hk (count k)` — the fixed rotation,
`count k` slots to every round, for as long as the configuration lasts.

This plan has it emit the whole schedule: which validator leads each
slot, how many slots each round holds — **round by round, not one number
for the configuration** — and how long the configuration runs before the
next reconfiguration is due.

## 1. Why this is now a small change

Two things landed on `main` that were not there when the mechanism was
first written.

**A schedule with varying widths is already a `Slots`.** The class asks
`slotRound` to be monotone and unbounded, `leader` to be a function, and
the pair to be injective. Nothing asks a round to hold a fixed number of
slots. So a configuration's schedule need not be built from a width
function and a rotation: the update rule may return a `Slots` and the
model need not know how it was made.

**`Properties.exists_roundLocal` is stated over `Slots`.** Every decided
slot has a round below which any schedule agreeing on the rounds and the
leaders decides it the same way. `Barnacle.sched_local` is that at
`Sched getLeader hk m`; at an emitted schedule it is the same theorem
with nothing to adapt, because the theorem never mentioned a width.

Together these mean the generalisation asks for no new machinery for
rounds. `Frame`, and everything that reasons about widths as a separate
object, is not needed: a `Slots` carries the widths in its `slotRound`.

## 2. What a configuration becomes

```lean
structure Config (Validator : Type) where
  /-- The schedule the configuration's rounds run on: which validator
  leads each slot, and how many slots each round holds. -/
  sched : Slots Validator
  /-- Rounds from this configuration's start before the next
  reconfiguration is due. -/
  interval : ℕ
  interval_pos : 0 < interval
  /-- No round holds more than `width` slots. What the descent reads,
  and the only thing the model asks of how the schedule is shaped. -/
  width : ℕ
  width_bound : ∀ k, sched.slotRound k < sched.slotRound (k + width)
```

`width_bound` says any `width + 1` consecutive slots span more than one
round, which is "at most `width` slots to a round" without naming a width
function. It is what `SpansEligibleAt` consumes, and it replaces
`Params.maxLeaders` as the bound liveness reads.

`UpdateRule` becomes

```lean
abbrev UpdateRule (R : BaseRule Validator BlockId Payload) : Type :=
  Config Validator → ℕ → (U : R.Universe) → R.View U → BlockId →
    Config Validator × ℕ
```

— from the configuration in force, the back-off, and the anchor's block,
the next configuration and the next back-off. `Params.interval` and
`Params.maxLeaders` move into `Config`, so what remains in `Params` is
the threshold the AIMD rule reads.

## 3. What the run becomes

`PartialRun`'s `count : ℕ → ℕ` becomes `cfg : ℕ → Config Validator`, and
the clauses read better rather than worse, since `κ / count k` was
standing in for a round:

| clause | now | becomes |
|:---|:---|:---|
| the range | `start k < κ / count k` | `start k < (cfg k).sched.slotRound κ` |
| decided at | `Sched getLeader hk (count k)` | `(cfg k).sched` |
| the threshold | `start k + P.interval < anchor k / count k` | `start k + (cfg k).interval < (cfg k).sched.slotRound (anchor k)` |
| the next start | `anchor k / count k + P.gap` | `(cfg k).sched.slotRound (anchor k)` |
| the update | `(count (k+1), backoff (k+1)) = upd …` | `(cfg (k+1), backoff (k+1)) = upd (cfg k) …` |

The last row is where the mechanism grows: one function now decides the
leaders, the widths and the interval together, from the same anchor it
already reads.

`start_succ` takes the paper's form — the new configuration begins at the
round after the pivot's — and not the round-plus-gap form. §7 says why.

## 4. Safety is the same induction

BN3's proof does not change shape. Two runs agreeing on configuration `k`
read its range at *one* schedule, `Properties.Agree` settles the verdicts
there, the anchor is the least committed slot past the threshold and so
agrees, and the update is a function of the anchor's block. What was
"same count" becomes "same `Config`", and `Config` is data.

`Slots.ext'` is what makes the last step usable: two schedules with the
same rounds and the same leaders are the same schedule, so agreeing on
what a configuration *does* is agreeing on the configuration.

What the induction needs of the emitted schedule is nothing. It never
inspects `slotRound`; it only needs both runs to hold the same one.

## 5. Liveness

`Descends` needs the spanning clause, which `width_bound` supplies at
`c ≥ width * (wave + 1)` — the same arithmetic `Frame.spansEligible`
did, read off the schedule instead of a width function.

The fairness clause is Barnacle's `HeadsRun` at a schedule the mechanism
now chooses. That is a real change: `HeadsRun` is a property of a *fixed*
rotation, and a mechanism emitting the leaders must be asked to keep
emitting fair ones. The honest form is a clause on the update rule —
every configuration it can emit places a run of `c` reliable slots within
`c₀` rounds — which is the multi-leader `PickKeyed` obligation's sibling
and is assumed, not derived, exactly as §13's `PlacesRuns` is.

## 6. What the emitted leaders owe

`Slots.keyed` is a field, so a `Config` cannot name one validator twice
in a round: the obligation `Adaptive.PickKeyed` states for a reassignment
rule is discharged by construction here, because the schedule is a
`Slots` and not a bare function. That is the advantage of emitting the
schedule rather than a width and a rotation separately.

What is *not* discharged is that the emitted leaders are drawn from a
committee the rule can justify. Nothing in `Slots` says a leader is a
validator the protocol trusts; a rule could emit a schedule led entirely
by one validator, safe and never live. §5's fairness clause is where that
is priced.

## 7. The pivot, and why there is no gap

Report §21's mechanism starts the next configuration at the round after
the pivot's. `barnacle.md` records why that matters: `TryCommit` walks
the decision sequence in order up to the first undecided slot, so the
pivot sits above a fully decided prefix, and every slot below it was
derived while the configuration list still named that configuration's
schedule at every round. A mechanism that started the next configuration
*later* would put slots above the pivot inside a range it does not
govern,
where an implementation reads the next configuration's schedule and
the clause asks for this one's.

So `start_succ` should keep the paper's form. The generalisation changes
what a configuration *is*, not when it starts.

## 8. Module plan

* `LeanDag/Barnacle/Model/Config.lean` — `Config`, `width_bound`, and
  the arithmetic that a bound on slots per round gives.
* `LeanDag/Barnacle/Model/Rule.lean` — `UpdateRule` at a `Config`.
* `LeanDag/Barnacle/Model/Run.lean` — `PartialRun` at `cfg`.
* `LeanDag/Barnacle/Agreement/` — BN3, the same induction.
* `LeanDag/Barnacle/Ledger/`, `Validity/`, `Conservativity/` — the
  interval read off `Config`, otherwise mechanical.
* `LeanDag/Barnacle/Live/` — the descent from `width_bound`, and the
  fairness clause on the update rule.
* `LeanDagTest/Barnacle/` — a run whose second configuration differs from
  its first in all three: a leader, a round's width, and the interval.

## 9. Order of work

1. `Config` and `width_bound`, with a witness: a schedule whose rounds
   differ in width, exhibited as a lawful `Slots`. *This is the check
   that the class admits what §1 claims it does.*
2. `UpdateRule` and `PartialRun` at `Config`, and the constant instance —
   `Config` at a fixed rotation and a fixed count reproduces the present
   arc. *Nothing new is proved; the check is that the arc still builds.*
3. BN3. The induction is §4's and should be short.
4. Ledger, validity, conservativity.
5. Liveness, and the fairness clause on the update rule.
6. The witness of §8, and the report.

## 10. What could go wrong

**The AIMD rule reads a count.** `Model/Window.lean` computes the direct
decision rate as observed over expected, and expected is
`(Interval − waveLength + 1) × leadersPerRound`. At a variable schedule
the expected count is the number of slots the window holds, which the
schedule knows and the arithmetic does not. That rule needs restating
before it instantiates the new interface.

**`Slots` is a class.** Making a `Config` carry one means carrying a term
of a class, and the arc reads schedules through instance resolution in
places. Where a configuration's schedule is a field rather than an
instance, those reads become explicit arguments, and the change is wide
even where it is shallow.

**Emitting a schedule is a large surface.** The present rule returns two
naturals and a validator can check the whole of it by inspection. A rule
returning a `Slots` returns a function, and what it is allowed to return
is bounded only by `Slots`' own clauses plus §5's fairness. Whether that
is the right interface — as against emitting a width function and a
rotation, and constructing the `Slots` — is the first design question the
build will answer.
