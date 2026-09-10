# lean-dag — Adaptive widths: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** Proposed, not built. Nothing below is in
> the development. `adaptive-rounds.md` records the built alternative —
> the same capability obtained by composing `Adaptive.Policy` with
> Barnacle — and §8 compares the two.

This document is the design record for **adaptive widths**: a second
question put to the arc of `adaptive-leaders.md`, which is whether a
reassignment policy can determine how many leaders a round holds as well
as which validators lead. Results would carry **AW**-labels, siblings of
that arc's **AL**.

The design is `Adaptive.Policy` with one more field. There is no new
mechanism to compose, and no second numbering to reconcile.

## 1. The question

A schedule has two halves. `Frame` gives each round a width and
`Slots.leader` gives each slot a validator, and the two are independent:
`Frame.toSlots` reads a frame and an assignment as a `Slots`. The
adaptive arc varies the second half and holds the first fixed. Barnacle
varies the first and holds the second fixed. `adaptive-rounds.md` is the
record of running both at once.

The question here is whether one mechanism can vary both. The
information is the same in either case — a validator scores its peers on
what it can agree they did, and the score should be able to say *four
leaders this round, and these four* rather than only *these four*.

## 2. The clause the development already asks for

`Integration.FrameRun` is a frame, an assignment, verdicts, that the
assignment is the policy's, and that every slot of a closed epoch is
decided. It names no count mechanism. Its safety theorem,
`Integration.frameRun_agree`, takes one hypothesis about widths:

```lean
(hwd : ∀ r, r < Rn.F.roundOf (W * (H + 1)) →
    (∀ j, epochOf W j + 2 ≤ epochOf W (Rn.F.cum r) → Rn.vdct j = Rn'.vdct j) →
    Rn'.F.width r = Rn.F.width r)
```

Read as a clause on a mechanism rather than as a hypothesis of a
theorem, `hwd` says: *the width of round `r` is a function of the
verdicts of epochs at or below `epochOf (F.cum r) − 2`.* That is
`Policy.adapted` with `width` in place of `pick`.

So the safety argument for adaptive widths already exists.
`Integration/CompRun.lean` discharges `hwd` for the composed run through
`CompRun.width_det`, which needs `config_det`, `anchor_det`,
`cnt_det`, `start_succ_det` and Barnacle's threshold restated as a slot.
A policy that emits the widths discharges it from its own adaptedness
clause.

## 3. The design

`Adaptive.Policy` gains a width function and four clauses beside the four
it has:

```lean
widthOf : (U : R.Universe) → (ℕ → Option BlockId) → ℕ → ℕ
widthOf_pos : ∀ U v r, 0 < widthOf U v r
widthOf_le : ∀ U v r, widthOf U v r ≤ maxWidth
widthOf_adapted : ∀ U (v w : ℕ → Option BlockId) r,
  (∀ j, epochOf W j + 2 ≤ epochOf W (frameOf U v).cum r → v j = w j) →
  widthOf U v r = widthOf U w r
widthOf_base : ∀ U v r, (frameOf U v).cum r < W * 2 → widthOf U v r = 1
```

`maxWidth` replaces `Params.maxLeaders`, and `widthOf_base` replaces
`Policy.base_prefix` for the first half of the schedule: epochs `0` and
`1` run at one leader a round, as they run at the base leaders.

`frameOf U v` is the frame the widths generate. It is defined by strong
recursion on the round: `width r` reads `cum r`, which reads the widths
of rounds below `r` and nothing else, so the recursion is well founded.
The epoch of round `r` is then `epochOf W ((frameOf U v).cum r)`, and
`widthOf_adapted` is stated at that epoch.

`FrameRun` gains one field, mirroring `coherent`:

```lean
widths : ∀ r, epochOf W (F.cum r) < H + 1 → F.width r = P.widthOf U vdct r
```

and `hwd` becomes a lemma of two steps: the two runs agree on the
verdicts `widthOf_adapted` reads, by hypothesis; therefore they agree on
the width.

## 4. What the widths owe elsewhere

Three clauses of the existing arc are stated at a width someone else
chose. Each becomes an obligation on the policy.

**`Slots.keyed`.** Distinct slots differ in round or in leader.
`Policy.keyed` states it once, at the ambient schedule. A policy that
also chooses the width owes it at **every width it can choose**, since a
reassignment could collide two slots of one round onto one validator at
a width it selects and not at another. `Composed.reframe` already names
this obligation for a count-varying mechanism, at each count it can
reach; here it is the same obligation, and the mechanism reaching those
counts is the policy itself.

**The descent.** `Composed.descends` asks
`P.maxLeaders * (wave + 1) ≤ c`, so `widthOf_le` is what the spanning
clause consumes and `maxWidth` is what it is stated at.

**`PlacesRuns`.** Unchanged in form. It asks for `c` consecutive slots
of an epoch led by reliable validators, and a policy emitting the widths
must place them at whatever widths it emitted.

## 5. The floor on the epoch length

`PlacesRuns P T c` asks for `b` with `W * (e + 1) ≤ b` and
`b + c ≤ W * (e + 2)`, so `c ≤ W`. The descent asks
`maxWidth * (wave + 1) ≤ c`. Together

```
W ≥ maxWidth * (wave + 1)
```

and, if the degenerate case of §6 is to discharge `PlacesRuns` through
`placesRuns_const_of_headsRun`, also `W ≥ c₀`, the reach of the
rotation. So

```
W ≥ max c₀ (maxWidth * (wave + 1))
```

At Mysticeti's `wave = 2` and four validators this is
`max 6 (3 * maxWidth)` slots. The bound is in slots, so in rounds the
epoch is `W / m` long at width `m`: at the widest schedule the floor is
`wave + 1` rounds, and at one leader a round it is `W` rounds. Epochs are
short in rounds exactly when the schedule is wide.

## 6. The degenerate case, and what is not available

Where the score has nothing to read — an epoch in which nothing
committed — the policy returns the base schedule: one leader a round, on
the rotation. That case is not merely safe, it is the case with a proof.
`Adaptive.Policy.const` is the constant policy and

```lean
theorem placesRuns_const_of_headsRun (hW : 0 < W) (hinj : Function.Injective S.slotRound)
    (hleader : ∀ κ, S.leader κ = getLeader κ) (hc₀ : c₀ ≤ W)
    (hhr : Barnacle.HeadsRun getLeader T c c₀) :
    PlacesRuns (Policy.const (R := R) W hW hinj) T c
```

discharges the liveness clause from the rotation's own fairness.

A sparser default is **not** available. `Frame.width_pos` requires every
round to hold a slot, so a schedule of one slot every `wave` rounds
cannot be a frame. The exclusion is structural rather than incidental:
with empty rounds `Frame.cum` is only monotone, and the agreement
argument needs it strictly monotone at the window's end, since a run of
empty rounds below that boundary leaves the widths there to be settled by
verdicts the induction is in the middle of deciding. `Slots` remains the
general notion and `Slots.uniform p m` admits a period `p > 1`; a
schedule that skips rounds is outside the varying-frame argument, not
merely outside this design.

## 7. What `adapted` permits and an implementation must not

`Policy.adapted` constrains the dependence of `pick` on the verdicts and
forbids dependence on the view. It permits arbitrary dependence on the
universe `U`. That is sound for agreement — two runs of `frameRun_agree`
share one universe, so any function of it agrees — and it is not
implementable, since a validator holds `V` and not `U`. Nothing in the
present clause stops a policy from reading blocks no validator could
have.

The discipline an implementation needs is Barnacle's, stated for its
window rule: read the causal history of settled commits and nothing else.
`Barnacle.Anchored` is the clause, and BN2 is why it is enough — every
view holding the anchor holds its history whole and restricts it
identically, so two validators compute one answer. Restricting
`widthOf` and `pick` to the cones of commits from epochs at or below
`e − 2` is stronger than either arc currently asks, and should be stated
rather than assumed.

## 8. Against the composition

Both designs deliver variable widths with a two-epoch lag. They differ in
four ways that can be checked rather than argued.

**Rate.** A composed configuration's range is at least
`interval + 1 + gap` rounds, and `gap = 2 * W`, so a width change is at
least `2 * W + 2` rounds apart, which at width `m` is `m * (2 * W + 2)`
slots. A policy emitting the widths may change them every round. Neither
is more current — the lag is two epochs in both — but the composition
changes more slowly.

**Granularity.** `CompRun.cnt_eq` makes every round of a configuration's
range the same width. A policy emitting the widths is under no such
clause, so each round may differ from the next.

**Alignment.** Under the composition an epoch meets at most two
configurations, since a configuration's range is at least `2 * W + 2`
rounds and an epoch spans at most `W` of them. So the composition admits
at most one width change inside an epoch, and `mRun` sits on that bound.
This is a consequence of `thr_lt_start_succ` and `Frame.cum_gap` rather
than a theorem of the development.

**What the composition keeps.** Barnacle's control loop as a proved
object: `Barnacle.Aimd` and `Barnacle.Healthy` are stated over the update
rule and the parameters, not over a run, and they hold of a composed run
unchanged. A policy emitting the widths carries the control rule inside
itself and owes its soundness again. The composition also blocks by
construction where nothing commits, a configuration not closing until a
commit lands past its threshold; a policy must decide that case in
`widthOf`, which §6 is.

## 9. Module plan

* `LeanDag/Adaptive/Width.lean` — `widthOf` and its four clauses on
  `Policy`, `frameOf` by strong recursion on the round, and `frameOf`'s
  arithmetic: `cum`, `roundOf`, and that the recursion reads only rounds
  below.
* `LeanDag/Adaptive/WidthRun.lean` — `FrameRun`'s `widths` field, `hwd`
  as a lemma, and safety as a corollary of `frameRun_agree`.
* `LeanDag/Adaptive/WidthLive.lean` — the descent at `maxWidth`, and
  `commits_in_epoch` at a width-emitting policy.
* `LeanDagTest/Adaptive/WidthModel.lean` — a policy on `Ugrow` whose
  width moves, its epochs at the floor of §5, and the degenerate case of
  §6 exhibited.

Nothing under `Integration/` is needed: the arc composes with no second
mechanism.

## 10. Out of scope

**Variable epoch length.** `epochOf W k = k / W` fixes `W`, and it is
read by `adapted`, `base_prefix`, `PlacesRuns`, `SettlesInTwoEpochs` and
the induction of `frameRun_agree`. Making the boundaries a function of
the score turns `epochOf` into a lookup and the two-epoch lag into two
boundaries back, which touches every one of those. It is a separate
question and a larger one; the widths do not depend on it.

**Retiring the composition.** `adaptive-rounds.md`'s arc answers a
different question — whether Barnacle's mechanism specifically can run
beside adaptive leaders — and the answer does not become less true if
this one is built. The two records stand side by side, as `minnow.md`
and `black-marlin.md` do.

## 11. What could go wrong

**`keyed` at every width.** §4's first obligation is the one with no
precedent in the arc as it stands. A scoring rule that ranks validators
and takes the top `m` satisfies it — the top `m` are distinct — but a
rule that maps scores to validators by a hash does not, and the clause
would be discovered late.

**The recursion's cost.** `frameOf` by strong recursion on the round is
well founded, and it is not obviously reducible: `cum r` is a sum over
`r` terms each of which is a recursive call. Every proof that computes a
width at a concrete round pays for the whole prefix. The witnesses of §9
may need a closed form, as `mF_cum_high` is for the composed witness.

**The floor may bind.** §5 asks `W ≥ maxWidth * (wave + 1)`. A design
wanting both wide rounds and short epochs cannot have them: at
`maxWidth = 8` and `wave = 2` the epoch is at least `24` slots, which at
one leader a round is `24` rounds. The bound comes from `PlacesRuns`
asking for its run of reliable slots to fit inside one epoch, and
relaxing it means letting a run straddle an epoch boundary, which the
clause is not stated to allow.
