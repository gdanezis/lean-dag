# lean-dag — The adaptive schedule: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** Proposed, not built. Nothing below is in
> the development. `adaptive-rounds.md` records the built alternative —
> variable widths obtained by composing `Adaptive.Policy` with Barnacle —
> and §9 compares the two.

This document is the design record for the **adaptive schedule**: a
second question put to the arc of `adaptive-leaders.md`, which varies who
leads and holds the rest of the schedule fixed. The question here is
whether one policy can emit the whole of it — how long an epoch is, how
many leaders a round holds, and which validator holds each of those
places — with every part read from the same settled information at the
same lag. Results would carry **AS**-labels, siblings of that arc's
**AL**.

The design is `Adaptive.Policy` with two more fields and a second
`Frame`. There is no mechanism to compose and no second numbering to
reconcile.

## 1. The three outputs

A schedule is three functions and the arc as it stands varies one of
them.

| | emitted by | today |
|:---|:---|:---|
| `len e` | slots in epoch `e` | fixed, `W` |
| `width r` | slots in round `r` | fixed, or Barnacle's |
| `pick g` | the leader of slot `g` | `Policy.pick` |

All three would read the verdicts of epochs at or below `e − 2`, where
`e` is the epoch of the thing being scheduled, and nothing else. A
validator scoring its peers on what it can agree they did should be able
to say *this epoch runs sixteen slots, this round holds four of them, and
these four validators lead* rather than only the last clause.

## 2. The clause the development already asks for

`Adaptive.FrameRun` is a frame, an assignment, verdicts, that the
assignment is the policy's, and that every slot of a closed epoch is
decided. It names no count mechanism. Its safety theorem,
`Adaptive.frameRun_agree`, takes one hypothesis about widths:

```lean
(hwd : ∀ r, r < Rn.F.roundOf (Rn.E.cum (H + 1)) →
    (∀ j, Rn.E.roundOf j + 2 ≤ Rn.E.roundOf (Rn.F.cum r) → Rn.vdct j = Rn'.vdct j) →
    Rn'.F.width r = Rn.F.width r)
```

Read as a clause on a mechanism rather than a hypothesis of a theorem,
`hwd` says: *the width of round `r` is a function of the verdicts of
epochs at or below `E.roundOf (F.cum r) − 2`.* That is `Policy.adapted`
with `width` in place of `pick`.

So the safety argument for adaptive widths already exists.
`Integration/CompRun.lean` discharges `hwd` for the composed run through
`CompRun.width_det`, which needs `config_det`, `anchor_det`, `cnt_det`,
`start_succ_det` and Barnacle's threshold restated as a slot. A policy
that emits the widths discharges it from its own adaptedness clause.

## 3. Epochs over slots are a second frame

`Frame` is a width function with `width_pos`, and `cum`, `roundOf` and
`index` derived from it. Epochs stand to slots exactly as slots stand to
rounds:

| | slots over rounds | epochs over slots |
|:---|:---|:---|
| width | `F.width r` | `len e` |
| cumulative | `F.cum r` | `bd e`, the first slot of epoch `e` |
| lookup | `F.roundOf g` | `epochOf g` |
| non-degeneracy | `F.width_pos` | every epoch holds a slot |

The identity that makes this exact is `constFrame_roundOf`: a frame of
constant width `m` has `roundOf g = g / m`, so the present
`epochOf W k = k / W` **is** `(constFrame W hW).roundOf k`. Generalising
the epoch structure is therefore the substitution of an arbitrary frame
`E` for `constFrame W`, under which `epochOf` becomes `E.roundOf` and
`W * (e + 2)` becomes `E.cum (e + 2)`.

Most of the arithmetic transfers with no new proof. `epochOf_lt_iff`,
which is `epochOf W k < e ↔ k < W * e`, is `Frame.cum_le_iff_le_roundOf`
negated. `Frame.cum_congr` and `Frame.roundOf_congr` are what the
agreement argument reads of the round frame and would read of the epoch
frame in the same places.

`width_pos` is not a restriction here. §6's floor already asks
`maxWidth * (wave + 1) ≤ len e`, which is at least one.

## 4. The design

`Adaptive.Policy` gains two functions and their clauses.

```lean
len : (U : R.Universe) → (ℕ → Option BlockId) → ℕ → ℕ
widthOf : (U : R.Universe) → (ℕ → Option BlockId) → ℕ → ℕ
```

`epochFrame U v : Frame` is built from `len` by strong recursion on the
epoch: `len e` reads the verdicts of slots below `bd (e − 1)`, and
`bd (e − 1)` is fixed by `len` at epochs strictly below `e − 1`.
`frameOf U v : Frame` is built from `widthOf` by strong recursion on the
round: `width r` reads `cum r`, which reads the widths of rounds below
`r`. Both recursions are well founded, and each reads only values it has
already produced.

Writing `E = epochFrame U v` and `F = frameOf U v`, the clauses are

```lean
len_pos : ∀ U v e, 0 < len U v e
len_floor : ∀ U v e, maxWidth * (wave + 1) ≤ len U v e
len_adapted : ∀ U v w e,
  (∀ j, (epochFrame U v).roundOf j + 2 ≤ e → v j = w j) →
  len U v e = len U w e
len_base : ∀ U v e, e < 2 → len U v e = baseLen

widthOf_pos : ∀ U v r, 0 < widthOf U v r
widthOf_le : ∀ U v r, widthOf U v r ≤ maxWidth
widthOf_adapted : ∀ U v w r,
  (∀ j, (epochFrame U v).roundOf j + 2 ≤ (epochFrame U v).roundOf (F.cum r) → v j = w j) →
  widthOf U v r = widthOf U w r
widthOf_base : ∀ U v r, (epochFrame U v).roundOf (F.cum r) < 2 → widthOf U v r = 1
```

`Policy.adapted` and `Policy.base_prefix` are restated at `E.roundOf` in
place of `epochOf W`. `maxWidth` replaces `Params.maxLeaders` and is the
policy's own bound rather than a parameter of another mechanism.

`FrameRun` gains two fields beside `coherent`:

```lean
epochs : ∀ e, e < H + 1 → E.width e = P.len U vdct e
widths : ∀ r, E.roundOf (F.cum r) < H + 1 → F.width r = P.widthOf U vdct r
```

## 5. The third determinism

This is the part that is new proof rather than substitution.

Today `epochOf` is one function that both runs of `frameRun_agree` share,
so the induction may index on it directly. With `len` emitted by the
policy, two runs may place the boundary of epoch `e` differently, and the
induction has to rule that out before it can state that the verdicts of
epochs at or below `e − 2` agree. So there is a clause beside `hwd`:

```lean
(hbd : ∀ e, e < H + 1 →
    (∀ j, Rn.E.roundOf j + 2 ≤ e → Rn.vdct j = Rn'.vdct j) →
    Rn'.E.width e = Rn.E.width e)
```

`E` is a field of `FrameRun` rather than a parameter, which is what lets
two runs place a boundary differently and makes `hbd` say something. A
run whose epochs are fixed sets it to `constFrame W` and discharges `hbd`
by `rfl`.

and the induction at epoch `e` runs in three steps instead of two: the
boundaries, then the round widths, then the verdicts.

It closes. `hbd` at `e' ≤ e` reads verdicts of epochs at or below
`e' − 2`, which is at or below `e − 2`, all strictly below `e`; from
those widths `Frame.cum_congr` gives `E'.cum e' = E.cum e'` up to
`e + 1`, which is where epoch `e` ends; and from there the argument is
the present one.

One restatement is called for. `frameRun_agree` concludes
`∀ g, epochOf W g < H → Rn.vdct g = Rn'.vdct g` and inducts through
`epochOf W g = e`. With the boundaries in question, *which epoch a slot
belongs to* is a fact about a run, so the induction hypothesis should be
carried on the slot bound — `∀ j, j < E.cum e → Rn.vdct j = Rn'.vdct j` —
which is frame-independent and says the same thing once the boundaries
are known to agree.

## 6. The floor on an epoch

`PlacesRuns P T c` asks for `b` with `bd (e + 1) ≤ b` and
`b + c ≤ bd (e + 2)`, so `c ≤ len (e + 1)`. The descent asks
`maxWidth * (wave + 1) ≤ c`. Together, per epoch,

```
len e ≥ max c₀ (maxWidth * (wave + 1))
```

where `c₀` is the reach of the rotation, needed if §7's degenerate case
is to discharge `PlacesRuns` through `placesRuns_const_of_headsRun`. At
Mysticeti's `wave = 2` and four validators the floor is
`max 6 (3 * maxWidth)` slots.

**Variable widths already vary an epoch's duration.** An epoch of `len`
slots at width `m` spans `len / m` rounds. With `len` at the floor and
`maxWidth = 4`, that is `3` rounds at the widest schedule and `12` at one
leader a round — a factor of `maxWidth` in duration with no control over
`len` at all. What `len` adds is control over the *slot* count, which is
what `PlacesRuns` is stated in, and so over how long a fairness window
the policy commits to.

**The floor is stated at the wrong quantity, and that is the sharper
prize.** `Composed.descends` consumes `cnt_le`, the bound on *every*
width the frame may hold, rather than the widths actually held inside the
span it is about. A descent stated at the widths of the span would give
`len e ≥ (widths in epoch e) * (wave + 1)`, so a narrow epoch could be
short without the policy giving up the right to be wide elsewhere. That
is a change to `Properties/`'s descent and is independent of everything
above; §11 keeps it separate.

## 7. The degenerate case, and what is not available

Where the score has nothing to read — an epoch in which nothing committed
— the policy returns the base schedule: the base epoch length, one leader
a round, on the rotation. That case is not merely safe, it is the case
with a proof. `Adaptive.Policy.const` is the constant policy and

```lean
theorem placesRuns_const_of_headsRun (hW : 0 < W) (hinj : Function.Injective S.slotRound)
    (hleader : ∀ κ, S.leader κ = getLeader κ) (hc₀ : c₀ ≤ W)
    (hhr : Barnacle.HeadsRun getLeader T c c₀) :
    PlacesRuns (Policy.const (R := R) W hW hinj) T c
```

discharges the liveness clause from the rotation's own fairness. At a
variable epoch length its `hc₀` becomes `c₀ ≤ len e` for the epochs the
default governs, which §6's floor gives.

A sparser default is **not** available. `Frame.width_pos` requires every
round to hold a slot, so a schedule of one slot every `wave` rounds
cannot be a frame. The exclusion is structural rather than incidental:
with empty rounds `Frame.cum` is only monotone, and the agreement
argument needs it strictly monotone at the window's end, since a run of
empty rounds below that boundary leaves the widths there to be settled by
verdicts the induction is in the middle of deciding. `Slots` remains the
general notion and `Slots.uniform p m` admits a period `p > 1`; a
schedule that skips rounds is outside the varying-frame argument, not
merely outside this design. The same reading applies to the epoch frame:
an empty epoch is excluded for the same reason, and §6's floor excludes
it anyway.

## 8. What the schedule owes elsewhere

Three clauses of the existing arc are stated at a schedule someone else
chose. Each becomes an obligation on the policy.

**`Slots.keyed`.** Distinct slots differ in round or in leader.
`Policy.keyed` states it once, at the ambient schedule. A policy that
also chooses the width owes it at **every width it can choose**, since a
reassignment could collide two slots of one round onto one validator at a
width it selects and not at another. `Composed.reframe` already names
this obligation for a count-varying mechanism, at each count it can
reach; here the mechanism reaching those counts is the policy itself.

**The descent.** `Composed.descends` asks
`P.maxLeaders * (wave + 1) ≤ c`, so `widthOf_le` is what the spanning
clause consumes and `maxWidth` is what it is stated at.

**`PlacesRuns`.** Unchanged in form, and now stated over an epoch whose
extent the policy also chose: the run of `c` reliable slots must fit
inside the epoch the same policy sized.

## 9. Against the composition

Both designs deliver variable widths with a two-epoch lag. They differ in
five ways that can be checked rather than argued.

**Rate.** A composed configuration's range is at least
`interval + 1 + gap` rounds, and `gap = 2 * W`, so a width change is at
least `2 * W + 2` rounds apart, which at width `m` is `m * (2 * W + 2)`
slots. A policy emitting the widths may change them every round. Neither
is more current — the lag is two epochs in both — but the composition
changes more slowly.

**Granularity.** `CompRun.cnt_eq` makes every round of a configuration's
range the same width. A policy emitting the widths is under no such
clause, so each round may differ from the next. Nothing in the common
layer stands in the way: `Frame.width` is an arbitrary function of the
round, and `LeanDagTest.VaryingFrame.vF` cycles through widths `1`, `2`,
`3` and still satisfies the spanning clause, `Frame.spansEligible_toSlots`
asking the widths to be bounded rather than equal.

**Alignment.** Under the composition an epoch meets at most two
configurations, since a configuration's range is at least `2 * W + 2`
rounds and an epoch spans at most `W` of them. So the composition admits
at most one width change inside an epoch, and `mRun` sits on that bound.
This is a consequence of `thr_lt_start_succ` and `Frame.cum_gap` rather
than a theorem of the development.

**The epoch.** The composition cannot vary it at all. `Policy.W` is a
field of the policy and a constant of the induction, and Barnacle has no
say in it.

**What the composition keeps.** Barnacle's control loop as a proved
object: `Barnacle.Aimd` and `Barnacle.Healthy` are stated over the update
rule and the parameters, not over a run, and they hold of a composed run
unchanged. A policy emitting the schedule carries the control rule inside
itself and owes its soundness again. The composition also blocks by
construction where nothing commits, a configuration not closing until a
commit lands past its threshold; a policy must decide that case in `len`
and `widthOf`, which §7 is.

## 10. What `adapted` permits and an implementation must not

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
identically, so two validators compute one answer. Restricting `len`,
`widthOf` and `pick` to the cones of commits from epochs at or below
`e − 2` is stronger than either arc currently asks, and should be stated
rather than assumed.

## 11. Where the files go

The arc belongs under `Adaptive/`, and one move is needed first.
`Integration/AdaptiveFrame.lean` holds two things: `FrameRun`,
`frameRun_agree`, `SettlesInTwoEpochs` and the spanning clause, which
name no second mechanism; and `placesRuns_const_of_headsRun`, which reads
`Barnacle.HeadsRun` and is the only reason that file imports Barnacle at
all. The first is adaptive-arc material sitting in the integration
directory.

| file | holds |
|:---|:---|
| `LeanDag/Adaptive/Frame.lean` | `FrameRun` and `frameRun_agree`, moved from `Integration/AdaptiveFrame.lean`, with `SettlesInTwoEpochs`, `closed_of_settles`, `Frame.spansEligible_toSlots` and `descends_frame` |
| `LeanDag/Adaptive/EpochFrame.lean` | `epochOf` as a frame's `roundOf`, and the arithmetic the arc reads of it |
| `LeanDag/Adaptive/Schedule.lean` | `Schedule`, `len` and `widthOf` with their clauses, `epochFrame` and `frameOf` by strong recursion |
| `LeanDag/Adaptive/ScheduleRun.lean` | the run, its `toFrameRun`, `hbd` and `hwd` as lemmas, safety |
| `LeanDag/Adaptive/ScheduleLive.lean` | the descent at `maxWidth`, `PlacesRuns` at a variable epoch, and the commits result |
| `LeanDag/Integration/AdaptiveFrame.lean` | what is left: `placesRuns_const_of_headsRun` alone |
| `LeanDagTest/Adaptive/ScheduleModel.lean` | the witness over `Ugrow` |

`Schedule` is **not** an extension of `Policy`. The reason is the
adaptedness clause: `Policy.adapted` reads the epoch of a slot at a fixed
`W`, and a schedule that emits the lengths must read it at its own epoch
frame. A `Schedule` therefore carries its own `pick` and its own
adaptedness, and `Policy` stays what the fixed-epoch arc is stated at —
`Policy.const` and `Adaptive/Liveness.lean` are untouched.

## 12. Order of work

Each step names what it changes and what must still hold when it is done.

**0. Move the frame arc.** `Adaptive/Frame.lean` takes everything of
`Integration/AdaptiveFrame.lean` above its `Fairness` section; that
section stays and imports the new file. `Common/Frame.lean`'s docstring
names the old path and is corrected. *No content changes; the build and
the six audits are unchanged, and no proof is edited.*

**1. Epochs as a frame, instantiated constant.** `EpochFrame.lean`
records `epochOf W k = (constFrame W hW).roundOf k` and the frame forms
of `epochOf_lt_iff` and `epochOf_add_two`. `FrameRun` and
`frameRun_agree` take a frame `E` where they took `W`, and every present
caller passes `constFrame W`. *Still no content changes: `Composed` and
the witnesses build with the new argument and no new proof.*

**2. The third determinism, still constant.** `frameRun_agree` gains
`hbd` and its induction hypothesis moves to the slot bound of §5.
Callers discharge `hbd` by `rfl`, `E` being constant. *This is the only
genuinely new argument in the plan, and it is proved before anything
depends on it.*

**3 and 4. The policy emits the widths and the epoch lengths.**
`Schedule.lean` is the structure — `len`, `widthOf`, `pick`, `maxWidth`
and the three adaptedness clauses — with `epochFrame` and `frameOf` the
two frames it gives at a verdict function. Neither is a recursion: `len`
and `widthOf` take the index directly, and it is the clauses that name
the frames the indices are read against. `ScheduleRun.lean` is the run,
its `toFrameRun`, and `agree`, where each of `frameRun_agree`'s three
determinisms is one of the schedule's clauses read at the two runs.
`coherent` is `rfl`, the assignment being the policy's by construction.

One hypothesis changed shape. `frameRun_agree`'s `hadapted` quantified
over every pair of verdict functions with the epoch frame fixed; a
schedule reads the epoch of a slot at *its own* frame, so the two cannot
be reconciled in general. The hypothesis is now stated at the runs it is
applied to, which is all the induction ever used.

*The check is that the three clauses are satisfiable together at a
schedule whose two frames both move. `Schedule.ofFixed` and
`LeanDagTest.ScheduleModel.sched` are it: epochs of `3, 4, 5` slots over
rounds of `1, 2, 3`, neither aligned with the other and neither
constant.*

**5. Liveness.** `ScheduleLive.lean`: `commits`, that a slot led by a
reliable validator commits; `PlacesRunsIn`, the fairness clause at an
epoch the policy sized; `commits_in_epoch`, that every epoch a run has
closed carries `c` consecutive commits; and `descends`, the descent from
`widthOf_le`, which asks the widths to be bounded and not equal. The
degenerate case is `placesRunsIn_ofFixed_of_headsRun`, in `Integration/`
because it reads Barnacle's rotation: at one leader a round the head of
round `r` is slot `r`, so `HeadsRun`'s stretch is a stretch of slots and
falls inside an epoch as soon as that epoch is `c₀` slots long, which is
§6's floor stated per epoch.

`Composed.commits` and `Composed.commits_in_epoch` are stated at a
composed run and could be restated at a `FrameRun`, which would give both
arcs one proof; that is a refactor and not a dependency.

**6. The witness.** `ScheduleModel.lean` over `Ugrow`: a schedule whose
epoch length and width both move, epochs at the floor of §6, and the
degenerate case exhibited. Closed forms for `epochFrame`'s and
`frameOf`'s cumulative functions will be wanted, as `mF_cum_high` is for
the composed witness.

**7. The record.** `LeanDag.lean` and `LeanDagTest.lean` gain the
imports; the report gains a subsection of §13 and Appendix A gains the
**AS** rows; `scripts/audit-mechanisms.py` gains the arc; and
`deps.tsv`, `decls.json` and the four dependency-graph SVGs are
regenerated.

**Separable, and not required.** The sharpened descent of §6 — stated at
the widths of the span rather than at `maxWidth` — is a change to
`Properties/` that would lower the floor on `len`. It is worth having and
nothing above waits for it.

**Not in scope.** `adaptive-rounds.md`'s arc answers a different question
— whether Barnacle's mechanism specifically can run beside adaptive
leaders — and the answer does not become less true if this one is built.
The two records stand side by side, as `minnow.md` and `black-marlin.md`
do.

## 13. What could go wrong

**`keyed` at every width.** §8's first obligation is the one with no
precedent in the arc as it stands. A scoring rule that ranks validators
and takes the top `m` satisfies it — the top `m` are distinct — but a
rule that maps scores to validators by a hash does not, and the clause
would be discovered late.

**Two recursions and no closed form.** `epochFrame` and `frameOf` are
both defined by strong recursion, and `E.cum e` is a sum over `e` terms
each of which is a recursive call. Every proof computing a boundary or a
width at a concrete index reads the whole prefix. The witness of §11 will
need closed forms, as `mF_cum_high` is for the composed witness, and it
needs two of them.

**The floor may bind.** §6 asks `len e ≥ maxWidth * (wave + 1)`. A design
wanting both wide rounds and short epochs cannot have them until the
descent is sharpened: at `maxWidth = 8` and `wave = 2` every epoch is at
least `24` slots, which at one leader a round is `24` rounds. The bound
comes from `PlacesRuns` asking its run of reliable slots to fit inside
one epoch, and relaxing it means letting a run straddle a boundary, which
the clause is not stated to allow.

**The lag is two boundaries, not two of anything fixed.** With `len`
varying, "two epochs back" is a distance in boundaries and not in slots
or rounds. A policy that shortens epochs sharply shortens its own memory:
at the floor, two epochs is `2 * max c₀ (maxWidth * (wave + 1))` slots,
and a scoring rule reading that window sees less than it did. Nothing
breaks, but the mechanism's statistics and its cadence stop being
independent, and a policy that shortens epochs to react faster reacts on
less evidence.
