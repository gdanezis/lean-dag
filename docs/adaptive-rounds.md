# lean-dag — Composing adaptive leaders with adaptive counts: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** §2 is built and on this branch. §3 is the
> open question and §4 the experiment that settles it; nothing after §2
> is built. The composition on branches `compose-barnacle-hammerhead` and
> `compose-cadence` is superseded, and retained only for the proofs §6
> names.

This document plans the composition of Barnacle (`docs/barnacle.md`),
which sets how many leaders a round has, with the adaptive leader
schedule (`docs/adaptive-leaders.md`), which sets who they are. An
earlier revision proposed re-coordinatising the adaptive arc in rounds.
§2 removed the obstacle that proposal was drawn against, and §3 states
what is left of it.

## 1. Two numberings

Barnacle sets how many leaders a round has. Under `Sched getLeader hk m`
slot `κ` is proposed at round `κ / m`, so a change of `m` at round `r`
renumbers every slot at and above `r`. Barnacle never changes the rounds:
round `r` is round `r` at every count.

The adaptive arc indexes both its epochs and its verdicts by slot
number. `epochOf W k = k / W` (`Adaptive/Basic.lean`), and a run's
verdicts are `vdct : ℕ → Option BlockId` (`Adaptive/Run.lean`).
`Policy.adapted` states the lag in that numbering: the leader of slot `k`
is a function of `v j` for those `j` with `epochOf W j + 2 ≤ epochOf W k`.

A composition must therefore relate a configuration's numbering to the
one the policy reads. On `compose-barnacle-hammerhead` that relation is
`base`, `width`, `flat`, `flat_eq`, `base_eq`, `base_det`, `flat_det` and
`dvd_base`, with the restriction `OneEpoch` — every configuration is
exactly `W` slots — and its consequences `count_dvd`, `span_eq` and
`count_interval`. `OneEpoch` forces Barnacle's configuration length to
equal the policy's epoch length, so the two mechanisms cannot be tuned
independently.

Two remedies are available. Give the composition **one** numbering, so
that no relation is needed; or state the policy in coordinates a
renumbering does not disturb. §2 supplies the first. §3 asks whether the
second is still wanted.

## 2. What is built

### 2.1 The band bounds the rounds it reads

`Banded` (`Properties/Band.lean`) transports a decided verdict to
another schedule. Its leader clause was already local to the band; its
round clause was not, so nothing related two schedules differing in
`slotRound` anywhere. The round clause now carries the same restriction:

    (∀ m m', m + d' = m' + d → S.slotRound m ≤ top →
      S.slotRound m + g = S'.slotRound m' + g') →

No protocol owes anything new. `BandLaws` states each clause pointwise at
a slot, with the round correspondence as a hypothesis there; none reads a
global one. Four of the five protocols discharge `Banded` by delegation
in one line and are unchanged, and consumers are unchanged because a
weaker hypothesis on `S'` makes the property stronger. The work was
confined to `banded_aux`, the single generic transport, where each site
needed what the leader clause already needed — that the slot is in the
band.

`Properties.exists_roundLocal` is the consequence: every decided slot has
a round bound below which the schedule settles it, and any schedule
agreeing there, on the rounds as well as the leaders, decides it the same
way.

### 2.2 A schedule is a frame and an assignment

    structure Frame where
      width : ℕ → ℕ
      width_pos : ∀ r, 0 < width r

`Frame.cum r` is the slots below round `r`, `Frame.roundOf g` the round
index `g` falls in, `Frame.index r i` the index of position `i` of round
`r`, and `Frame.toSlots` the `Slots` a frame and an assignment make,
enumerating slots in round order. `Slots.keyed` follows from distinctness
within a round.

This is the decomposition the two mechanisms make: Barnacle varies the
widths, the adaptive arc varies the leaders. `constFrame m` is the
constant frame, and `Barnacle.Sched_eq_frame` says Barnacle's schedule at
count `m` is exactly that, so the arc needs no change to acquire the
reading.

### 2.3 Verdicts survive a change of width above them

`Properties.decided_of_frame_agree`: a slot decided under one frame is
decided under any frame agreeing with it below a round bound the verdict
determines, whatever the widths above.

`Barnacle.sched_frame_local` is that at the constant frame, and states
what the arc has been assuming. `PartialRun.closed` records a
configuration's verdicts as decided against
`Sched getLeader hk (count k)` — the uniform schedule at that count,
extended to every round — which is not the schedule that runs once the
count changes. The arc is sound because a configuration's verdicts are
settled within its own rounds; that is now a theorem rather than a
reading.

### 2.4 What §2 removed from the earlier plan

`DecidedBelowRound` was proposed as a definition protocols would owe. It
is unnecessary: `exists_roundLocal` is stronger and follows from
`Banded`.

The earlier §2.7 held that two runs' verdicts could be compared only
against a schedule they agree on everywhere, and concluded that a
composition must compare inside a configuration, against a schedule
uniform there. That is no longer so, and the retention of `configSched`
had no other reason.

## 3. The open question

**Does the composition still need the adaptive arc in round
coordinates?**

The case that it does not. A composed run may carry one global frame,
whose widths are the counts in force. Slots are then enumerated once, by
`Frame.index`, and there is no second numbering to relate: `flat`,
`base`, `flat_eq` and `base_eq` are replaced by `Frame.cum` and
`Frame.index`, which are general and proved. `epochOf` continues to read
the global index. Two runs' numberings agree wherever their widths do,
and §2.3 is what makes that enough, since the frames need agree only
below the bound.

The case that it does. Under a global frame an epoch is `W` slots and so
spans a variable number of rounds, since the widths vary. Round
coordinates would make an epoch a fixed span of rounds. This is a
statement about what an epoch means, not about whether the proof closes,
and it should be decided on its merits rather than under pressure from
the numbering.

**What is not in question.** Neither remedy needs `OneEpoch`, the
divisibility `count k ∣ W`, or any alignment between configuration
boundaries and epoch boundaries. Those were consequences of relating two
numberings and have no source once there is one.

**What remains in either case** is the lag. `Policy.adapted` fixes the
assignment two epochs behind the verdicts. The count is also derived from
verdicts — from a configuration's anchor — and the composition's
induction needs it settled where it is read. Whether Barnacle owes a lag
on the count, and of what size, is the substance of §4 and is independent
of coordinates.

## 4. The experiment that settles §3

Rebuild the composition on a global frame with the adaptive arc
otherwise unchanged, and find where the induction stalls.

    structure ComposedRun … where
      cnt   : ℕ → ℕ                      -- the count in force at round r
      asg   : ℕ → Validator              -- by global slot index
      vdct  : ℕ → Option BlockId         -- by global slot index
      …

with `F := ⟨cnt, _⟩` the frame and `F.toSlots` the schedule. Barnacle's
configuration data — `start`, `count`, `backoff`, `anchor` — is retained
in its own numbering, and `Frame.index` relates the two where Barnacle's
theorems are used.

The safety induction runs on the epoch, and at each step needs the
widths, then the assignment, then the verdicts. The first of those is
where a lag on the count would be needed, and the experiment's purpose is
to see exactly which rounds' widths the step reads. That is a question
about `Frame.cum` and the bound of §2.3, and it can be answered without
touching either arc.

This is much smaller than either rewrite, and it is to be done before
either is begun.

## 5. What survives §3 either way

`Policy.inj : Function.Injective S.slotRound` states one leader per
round, which the composition contradicts. It becomes

    keyed : ∀ U V v κ₁ κ₂, S.slotRound κ₁ = S.slotRound κ₂ →
      pick U V v κ₁ = pick U V v κ₂ → κ₁ = κ₂

with `slotsOf` becoming `slotsOfKeyed`, and the derived clause
`PickKeyed` — the same law at every count up to a bound — for the
composition's use. All three are proved on
`compose-barnacle-hammerhead` and are to be carried over rather than
rewritten. This is the one change the adaptive arc needs whatever §3
decides.

## 6. Carried over from the superseded branches

Proved, and to be reused rather than reproved:

* `PickKeyed`, `Policy.keyed`, `slotsOfKeyed` — §5.
* `config_det`, `anchor_det` — the configuration data and the anchor are
  functions of the verdicts below them.
* `extend`, `genesis`, `every_height` — the liveness shape, less the
  divisibility conditions, which came from `OneEpoch`.
* `Closes` — what a configuration owes on the schedule the composition
  computes for it, asked at the reassignment rather than the rotation.
* The two-sided `mixLeader` (`compose-cadence`), if a per-configuration
  assignment is retained. Under §4's global assignment it is not needed.

Superseded, and not to be carried: `base`, `width`, `flat`, `flat_eq`,
`base_eq`, `base_det`, `width_det`, `flat_det`, `dvd_base`, `OneEpoch`,
`count_dvd`, `span_eq`, `count_interval`, `EpochAligned`,
`epochAligned_sum`, `rangeSlots`, `roundUp`, `dvd_roundUp`,
`le_roundUp`, `roundUp_lt`, `delay_lt`, `UpdDivides`.

## 7. Labels

The AL labels of `docs/adaptive-leaders.md` are preserved where the
statement is preserved. Composition results are `I`-labelled, as in
`docs/integration.md`.

## 8. Order of work

1. **Done.** §2: the band's round clause, `exists_roundLocal`, `Frame`,
   `decided_of_frame_agree`, `Sched_eq_frame`, `sched_frame_local`.
2. §5: `keyed`, `slotsOfKeyed`, `PickKeyed`, carried over.
3. §4: the composition on a global frame, to the point where the safety
   induction either closes or names the lag it needs.
4. Whatever §4 reports: either the lag on the count, or the round
   coordinates, or both. Not planned further here, because §4 decides
   what is worth planning.

## 9. What could go wrong

**The cost of restating an arc.** `Adaptive/` is 889 lines and
`Barnacle/` is 2986. Restating Barnacle over the frame is therefore some
three times the work of restating the adaptive arc, and neither is
warranted before §4. §4 avoids both: it keeps each arc's own numbering
and relates them with `Frame.index`, which §2.2 supplies.

**The lag on the count.** If §4 reports that the count must be settled
two epochs before it is read, Barnacle installs a new count one
configuration after the anchor that computed it and would have to install
it two. That is a change to the control loop rather than to the
composition — the rule reacts a configuration later — and it is a design
decision, not a proof obligation.

**`Frame.roundOf` is a search.** It is `Nat.findGreatest`, and every
statement about a slot index is a statement about `Frame.cum`. The design
keeps such statements to the `closed` clause. If they multiply, the frame
presentation removes less than it introduces and a per-configuration
numbering should be kept instead.

**The joiner.** `epochOf_add_of_dvd` states that a numbering starting at
an aligned offset agrees with the original about epochs, and
`Adaptive/Joiner.lean` uses it for a validator that joins mid-execution.
Under a global frame the offset is a slot offset into a varying frame,
and whether the lemma survives is not assessed.
