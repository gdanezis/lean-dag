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

The width function is the primitive, and the schedule derives from it.

```lean
structure Config (Validator : Type) where
  /-- How many slots round `r` holds. A function of the round, so a
  configuration's rounds need not agree. -/
  slotsAt : ℕ → ℕ
  slotsAt_pos : ∀ r, 0 < slotsAt r
  /-- Who leads position `i` of round `r`. -/
  lead : ℕ → ℕ → Validator
  /-- Distinct positions of a round have distinct leaders. -/
  keyed : ∀ r i j, i < slotsAt r → j < slotsAt r → lead r i = lead r j → i = j
  /-- Rounds from this configuration's start before the next
  reconfiguration is due. -/
  interval : ℕ
```

with `cum r` the first slot of round `r`, `roundOf g` the round of slot
`g`, and `sched : Slots Validator` built from the two — `slotRound` is
`roundOf`, and the leader of slot `g` is `lead` at its round and
position. `Config.keyed` is what `Slots.keyed` needs.

**Why not emit a `Slots` and stop.** §1 says a varying-width schedule is
already a `Slots`, and it is; but two places need the *first slot of a
round*, which a `Slots` does not give without inverting `slotRound`. The
ledger's range is `count k * (start k + 1)` — the first slot of the round
after the start — and the window's measurement enumerates the slots of
each round in the window as `m * (round − d) + l`. Both are `cum`. So the
width function has to be in the interface, and the schedule is what comes
out rather than what goes in.

This is a frame and an assignment in one structure. What it is *not* is
the reasoning layer that name once carried: no clause bounding a verdict
by a round with the widths free, no congruence of one frame with another,
no transport across a change of frame. A configuration has one schedule
over its whole range, and `Properties.exists_roundLocal` is what carries
a verdict across the boundary, so none of that is wanted here.

**What a configuration must satisfy** goes where the present arc puts it,
as a clause of the run beside `count_pos` and `count_le`:

```lean
interval_pos : ∀ k, 0 < (cfg k).interval
slotsAt_le : ∀ k r, (cfg k).slotsAt r ≤ P.maxLeaders
```

`slotsAt_le` is `count_le` with a round argument, and it is what the
descent's spanning clause reads.

`Config.uniform getLeader hk m` is the present arc: `slotsAt` constantly
`m`, `lead r i = getLeader (r + i)`. `uniform_sched` says its schedule is
`Sched getLeader hk m`, and that identity is what makes step 2's check a
rewrite rather than a re-proof.

`LeanDagTest.VaryingSchedule.vary` remains the check of §1's claim about
the class, and is not the shape a `Config` takes.

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

`Descends` needs the spanning clause, which `slotsAt_le` supplies at
`c ≥ maxLeaders * (wave + 1)` —
the same arithmetic the spanning clause
always did, read off the configuration.

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

* `LeanDag/Barnacle/Model/Config.lean` — `Config`, its `cum`, `roundOf`
  and `sched`, and the arithmetic those need.
* `LeanDag/Barnacle/Model/Rule.lean` — `UpdateRule` at a `Config`.
* `LeanDag/Barnacle/Model/Run.lean` — `PartialRun` at `cfg`.
* `LeanDag/Barnacle/Agreement/` — BN3, the same induction.
* `LeanDag/Barnacle/Ledger/`, `Validity/`, `Conservativity/` — the
  interval read off `Config`, otherwise mechanical.
* `LeanDag/Barnacle/Live/` — the descent from `slotsAt_le`, and the
  fairness clause on the update rule.
* `LeanDagTest/Barnacle/` — a run whose second configuration differs from
  its first in all three: a leader, a round's width, and the interval.

## 9. Order of work, and what the work was

1. ~~`Config` and the width bound, with a witness: a schedule whose
   rounds differ in width, exhibited as a lawful `Slots`.~~ The witness
   is `LeanDagTest.VaryingSchedule.vary` — rounds alternating one slot
   and two — and `vary_width_le` is the bound at two. The class admits
   what §1 claims it does.
2. ~~`Config` and the run, in five parts, nothing new proved.~~ Done, but
   not in five separable parts, and not with nothing new proved. **The
   plan's step 2 was not separable from steps 3 to 5.** The moment
   `PartialRun` stops carrying a count, `Model/Window.lean` has no count
   to read, so `observed`, `expected` and the AIMD rule move with it;
   and every arc stated over `PartialRun` breaks at once. What was
   actually done in one pass:

   * `Barnacle/Config.lean`: the structure, `cum`, `roundOf`, `index`,
     `head`, `sched`, `LeadKeyed`, `Config.uniform` and the arithmetic
     those need. The file is not under `Model/`, which carries no
     theorems.
   * `Model/Rule.lean`, `Model/Run.lean`: `UpdateRule` emits a `Config`;
     `PartialRun` carries `cfg` and a genesis `C₀`, with `slotsAt_le`,
     `interval_pos` and `interval_le` replacing `count_pos` and
     `count_le`.
   * `Model/Window.lean` and `Aimd/Rule.lean`: the measurement and the
     step at a configuration. `Params` keeps `maxLeaders`,
     `maxInterval`, `num`, `den`.
   * `Helpers/Schedule.lean`: `Config.uniform_sched`, the bridge, and
     `leadKeyed_of_keyed`.
   * `Helpers/Agreement.lean`, `Helpers/Ledger.lean`,
     `Helpers/Progress.lean`, `Helpers/Heads.lean`: every `κ / count k`
     a `roundOf`, every `count k * r` a `cum`, every `m * ρ` a `cum ρ`.
   * BN3, BN5, BN6, BN7, BN8, BN9, BN11, BN12 and BN14 restated and
     reproved, and the witnesses rewritten at `Config.uniform`.

   Three things needed an argument rather than a rewrite, and §2's shape
   was wrong about each:

   * `expected` is now the slots the window's scoring rounds offer,
     `cum (r − wave + 1) − cum (r − interval)`. At one width `m` this is
     the paper's `(interval − wave + 1) · m`; below one wave it is `0`,
     where the old truncation gave `m` for a window with no decidable
     round. The witnesses at interval one change verdict as a result: a
     window nothing scores is read as healthy because nothing was
     expected.
   * BN3 asks both runs to start from one genesis configuration. `init`
     no longer pins a count of one — there is no canonical `Config` —
     so there is nothing else to agree on at height zero.
   * Liveness asks the update rule to preserve a clause `Q` of the
     configurations it emits (`UpdKeeps`) and asks `LiveOn` only of
     those. Without it BN8b would need liveness at *every* configuration
     inside the bounds, including ones of varying width that the AIMD
     rule never emits — a strictly stronger hypothesis than the
     mechanism needs, and one the finite witnesses cannot discharge by
     case analysis on a width.
3. ~~The witness of §8 — a run whose second configuration differs from
   its first in a leader, a round's width and the interval.~~
   `LeanDagTest/Barnacle/Varying.lean`. `varC` is two slots wide at round
   `4` and one elsewhere, its leaders are the rotation shifted by a
   round, and its interval is two; `varRun` is a height-`2` run on `Usun`
   that installs it after round `2`, decides its range — slots `3` to
   `6`, four slots over three rounds — against `varC.sched`, and finds
   its anchor at slot `6`, which is round `5` where under one leader a
   round it would be round `6`. The rule is not the AIMD rule, which is
   the point: BN3 and BN5 hold for every update rule, and BN3 applied to
   two views identifies the configuration itself rather than a count.

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
returning a `Config` returns two functions, bounded by `Config`'s own
clauses, `slotsAt_le`, and §5's fairness — and the last of those is
assumed. What a rule may emit is therefore much wider than what it may
emit today, and the arc says less about it.

**The window's measurement is a rewrite, not an adaptation.** `expected`
is `(interval − waveLength + 1) * m` — rounds times slots-per-round,
which at a varying width is not a product but a sum, and `cum` is what
computes it. `observed` enumerates `range (interval + 1) ×ˢ range m` and
indexes a slot as `m * (round − d) + l`, an indexing that assumes uniform
width throughout. Both become enumerations over `cum`, and
`Model/Window.lean` is the file this plan rewrites rather than adapts.

**`Heads` is about a rotation.** `LiveOnOfHeads` concludes
`∀ m, R.LiveOn (Sched getLeader hk m) c₀` — a family over counts at one
fixed leader function. Where the leaders are emitted there is no family
and no fixed function, and what the arc should conclude instead is a
property of whatever a rule emits. That changes what BN12 and BN13 claim
and is not settled here.
