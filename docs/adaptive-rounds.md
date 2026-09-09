# lean-dag — Adaptive leaders in round coordinates: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** A plan, not a record: nothing below is
> built. It supersedes the composition on branches
> `compose-barnacle-hammerhead` and `compose-cadence`, which are retained
> for their proofs but whose numbering scaffolding this plan removes.

This document is the design record for re-coordinatising the
adaptive-leaders arc. `docs/adaptive-leaders.md` is the arc's own plan
and remains accurate about what the mechanism does; this document changes
the coordinates in which it says it, and the reason is the composition
with Barnacle (`docs/barnacle.md`).

## 1. Two numberings, and which one survives a reconfiguration

Barnacle sets how many leaders a round has. Under `Sched getLeader hk m`
slot `κ` is proposed at round `κ / m`, so a change of `m` at round `r`
renumbers every slot at and above `r`. Barnacle never changes the rounds
themselves: round `r` is round `r` at every count.

Hammerhead indexes both its epochs and its verdicts by slot number.
`epochOf W k = k / W` (`Adaptive/Basic.lean`), and a run's verdicts are
`vdct : ℕ → Option BlockId` (`Adaptive/Run.lean`). `Policy.adapted`
states the lag in that numbering: the leader of slot `k` is a function of
`v j` for those `j` with `epochOf W j + 2 ≤ epochOf W k`.

The two are therefore stated in different coordinates, and the
composition must translate. The translation was attempted on
`compose-barnacle-hammerhead` and consists of `base`, `width`, `flat`,
`flat_eq`, `base_eq`, `base_det`, `flat_det` and `dvd_base`, together with
the restriction `OneEpoch` — every configuration is exactly `W` slots —
and its consequences `count_dvd`, `span_eq` and `count_interval`. Those
declarations exist only to translate, and `OneEpoch` forces Barnacle's
configuration length to equal Hammerhead's epoch length, so the two
mechanisms cannot be tuned independently.

The proposal is to remove the translation by changing the coordinates.
Sections 2.1 to 2.3 fix the coordinates, 2.4 to 2.6 restate the
mechanism in them, and 2.7 states the one rule that governs how far the
generalisation extends.

## 2. The proposed shape

Signatures below are proposals. Binders are elided with `…`.

### 2.1 The frame: round widths, and the schedule they induce

A schedule is a sequence of round widths together with a leader for each
position in each round. This is the decomposition the two mechanisms
already make: Barnacle varies the widths and leaves the leaders alone,
Hammerhead varies the leaders and leaves the widths alone.

    structure Frame where
      width : ℕ → ℕ
      width_pos : ∀ r, 0 < width r

    def Frame.toSlots (F : Frame) (asg : ℕ → ℕ → Validator)
        (hkey : ∀ r i j, i < F.width r → j < F.width r → asg r i = asg r j → i = j) :
        Slots Validator

The induced instance enumerates slots in round order: slot
`(∑ r' < r, F.width r') + i` is at round `r` with leader `asg r i`.
`Slots.keyed` follows from `hkey`, since slots of one round have
distinct positions and slots of different rounds have distinct rounds.
`Slots.uniform p m …` (`Common/Slots.lean`) is the constant frame, and
Barnacle's `Sched getLeader hk m` is that frame with the rotation as
`asg`.

Protocols continue to see `Slots` and nothing else; `Frame` is a
mechanism-side presentation of one.

### 2.2 Epochs are spans of rounds

    structure Epochs where
      startRound : ℕ → ℕ
      zero : startRound 0 = 0
      mono : StrictMono startRound
      unbounded : ∀ r, ∃ e, r < startRound e

    def Epochs.at (E : Epochs) (r : ℕ) : ℕ   -- the `e` with `startRound e ≤ r < startRound (e+1)`

Epoch `e` is the rounds `[startRound e, startRound (e+1))`. The present
development is the constant grid `startRound e = W * e`, for which
`E.at r = r / W`; `epochOf` and its arithmetic lemmas
(`epochOf_lt_iff`, `epochOf_mono`, `epochOf_add_of_dvd`) remain and serve
that case. §2.7 states when the grid may be derived from the verdicts
rather than fixed in advance.

Under one leader per round a round and a slot are interchangeable and
this agrees with the present `epochOf`; under `m` leaders they differ by
the factor `m`, and it is the round form that is stable under a change of
`m`.

### 2.3 Two coordinates

Both are meaningful at every width, and neither is renumbered by a change
of width.

**The assignment is indexed by round and position.**

    asg : ℕ → ℕ → Validator

`asg r i` is the leader of the `i`-th slot of round `r`, for
`i < F.width r`; larger `i` receive values no clause reads. The
assignment is therefore one global function rather than one per
configuration, which is what removes `mixLeader` (§3): a
per-configuration assignment says nothing outside its range, and a
globally indexed one says something everywhere.

**The history is indexed by round and validator.**

    vdct : ℕ → Validator → Option BlockId

`Slots.keyed` states that `fun k => (S.slotRound k, S.leader k)` is
injective, so this is faithful: distinct slots receive distinct
coordinates. The policy scores validators, so this is the coordinate it
needs. Under `(round, position)` the policy would have to recover the
historical assignment before it could attribute a verdict, and that
assignment is `asg`, which is what the policy computes — a recursion
where there is otherwise a function.

### 2.4 The policy

    structure Policy (R : DagRule Validator BlockId Payload) (F : Frame) (E : Epochs) where
      pick : (U : R.Universe) → R.View U →
        (ℕ → Validator → Option BlockId) → ℕ → ℕ → Validator
      keyed : ∀ U V v r i j, i < F.width r → j < F.width r →
        pick U V v r i = pick U V v r j → i = j
      adapted : ∀ U V₁ V₂ v w r i,
        (∀ r' a, E.at r' + 2 ≤ E.at r → v r' a = w r' a) →
        pick U V₁ v r i = pick U V₂ w r i
      base : ℕ → ℕ → Validator
      base_prefix : ∀ U V v r i, E.at r < 2 → pick U V v r i = base r i

Three changes beyond the coordinates. `inj : Function.Injective S.slotRound`
becomes `keyed`, since the composition places several leaders in a round;
the substitution and the derived clause `PickKeyed` — the same law at
every count up to a bound — are proved on
`compose-barnacle-hammerhead` and are to be carried over. `adapted`'s
hypothesis quantifies over a round `r'` and a validator `a`, and names no
slot index; that is the whole of the change this document is for. And
`base_prefix` names a base assignment at the same coordinates rather than
`S.leader`.

**The coordinate and the lag.** `vdct` is indexed by the assignment,
which `pick` computes, so the coordinate is well defined only where the
assignment is settled. It is settled where it is read: `adapted` reads
epochs `≤ e − 2`, and the agreement induction fixes the assignment at
those epochs before it reaches epoch `e`. The lag that makes the adaptive
fixpoint well-founded is the same lag that makes the coordinate well
defined, and no separate argument is owed.

### 2.5 The run

    structure PartialRun (P : Policy R F E) (U : R.Universe) (V : R.View U) (H : ℕ) where
      asg : ℕ → ℕ → Validator
      keyed : ∀ r i j, i < F.width r → j < F.width r → asg r i = asg r j → i = j
      vdct : ℕ → Validator → Option BlockId
      closed : ∀ r i, i < F.width r → E.at r < H →
        DecidedBelowRound R (F.toSlots asg keyed)
          (E.startRound (E.at r + 2)) V (F.index r i) (vdct r (asg r i))
      coherent : ∀ r i, E.at r < H + 1 → asg r i = P.pick U V vdct r i

`F.index r i` is the slot index §2.1 assigns to position `i` of round
`r`. It appears here only because `Decided` is indexed by slot; no clause
of this document reasons about its value.

The agreement induction (`partialRun_agree`, `run_agree`, AL5 and AL6)
runs on the epoch as before, and the induction hypothesis must supply the
assignment as well as the verdicts, for the reason in §2.4.

### 2.6 A round-indexed bound

`DecidedBelow R S B V κ v` (`Properties/Bounded.lean`) holds the round
structure fixed and requires the verdict to be unchanged when the leaders
of slots with **index** `≥ B` are reassigned. Under §2.2 the bound wanted
is a round.

    def DecidedBelowRound (R : DagRule …) (S : Slots Validator) (B : ℕ)
        (V : R.View U) (κ : ℕ) (v : Option BlockId) : Prop :=
      S.slotRound κ < B ∧ R.Decided S V κ v ∧
        ∀ S' : Slots Validator, S'.slotRound = S.slotRound →
          (∀ m, S.slotRound m < B → S'.leader m = S.leader m) → R.Decided S' V κ v

**No protocol owes anything new.** Slots are enumerated in round order
(`Slots.mono`), so `m < B` implies `S.slotRound m ≤ S.slotRound B`, and
therefore

    DecidedBelow R S B V κ v → DecidedBelowRound R S (S.slotRound B + 1) V κ v

converts what the protocols already supply. `LeaderCommits` produces a
verdict at bound `κ + 1` and `Descends` at bound `b + c`
(`Properties/Derived/`), and both convert. This conversion is the
cheapest falsifier of the plan and is to be written first (§5, step 1).

### 2.7 How far the generalisation extends

**The rule: a schedule parameter derived from the verdicts owes the lag
of two.** `adapted` is that rule for the assignment. It applies equally
to anything else the mechanism computes from history.

*The epoch grid.* If `Epochs` is fixed in advance, nothing more is owed
and §2.2 stands as written. If the grid is derived from the verdicts —
epoch boundaries chosen by the mechanism rather than by a constant — then
`startRound (e + 2)` must be a function of the verdicts at epochs
`≤ e − 1`, and the grid owes a clause of `adapted`'s shape. Given that
clause the bound in §2.5 is available at the point the induction reaches
it, and the grid may be any increasing sequence.

*The widths.* `Frame` above is fixed. Barnacle's widths are not: they are
the counts, and they are derived from the anchors. §3 states what this
costs.

**What does not generalise.** `Decided` is an opaque field of `DagRule`
and no round-locality is available for it, so `DecidedBelow` and
`DecidedBelowRound` both require `S'.slotRound = S.slotRound` as total
functions. Two runs' verdicts can therefore be compared only against a
schedule they agree on everywhere. For a partial run the widths above the
horizon are unconstrained, so the comparison must take place where the
widths are fixed by data both runs have settled. §3 is where that
constraint is discharged, and it is the one part of the design that
flexibility elsewhere does not reach.

## 3. The composition after the change

The composed run keeps Barnacle's per-configuration data — `start`,
`count`, `backoff`, `anchor` — together with one global assignment
`asg : ℕ → ℕ → Validator` and one global verdict function
`vdct : ℕ → Validator → Option BlockId`. It carries no translation.

**Deleted from `Integration/AdaptiveBarnacle.lean`:** `width`, `base`,
`base_zero`, `base_succ`, `dvd_base`, `base_det`, `width_det`, `flat`,
`flat_eq`, `flat_det`, `base_eq`, `OneEpoch`, `count_dvd`, `span_eq`,
`count_interval`, `EpochAligned`, `epochAligned_sum`, `rangeSlots`,
`roundUp`, `dvd_roundUp`, `le_roundUp`, `roundUp_lt`, `delay_lt`,
`UpdDivides`, `mixLeader`, `mix_threshold`, `mix_top`,
`mixLeader_keyed`, and the `coherent` and `flat_eq` fields of
`ComposedRun`. The first group translates between numberings; the second
exists because a per-configuration assignment says nothing outside its
range, which §2.3 removes.

**Retained:** `configSched` and `configSched_congr`, for the reason in
§2.7. Barnacle's frame is constant on a configuration, so within one
configuration `slotRound κ = κ / count k` and the two runs' round
structures agree as soon as the single number `count k` does. Across a
configuration boundary they have no such property while the horizon is
finite. The comparison therefore happens inside a configuration, against
a schedule uniform there, and that is a condition for the comparison
existing rather than a convenience.

**Safety.** Induction on the epoch. At epoch `e`: the configuration in
force is a function of verdicts at earlier epochs (Barnacle's
`config_det` argument, unchanged); the assignment is then a function of
those verdicts by `adapted`; the schedules of the two runs agree; the
verdicts agree by `Properties.Agree`. No step consults a numbering.

**Liveness.** `Closes` — what a configuration owes on the schedule the
composition computes for it — is stated in the same terms as now, with
`DecidedBelowRound` in place of `DecidedBelow`. `extend`, `genesis` and
`every_height` follow the shape proved on
`compose-barnacle-hammerhead`, less the divisibility conditions, which
had no source other than `OneEpoch`.

### 3.1 Three arrangements, and what each costs

The parameters are now independent, and the choice among them is a
deployment question rather than a constraint of the proof. In increasing
order of flexibility and of cost:

**(a) A constant grid, configurations spanning whole epochs.** `Epochs`
is `startRound e = W * e`; a configuration is any number of epochs. `W`
and the configuration length are independent, which is what `OneEpoch`
prevented. Nothing is owed beyond §2. Whether the alignment between
configuration boundaries and epoch boundaries is needed at all is open;
see §3.2.

**(b) A constant grid, configurations unaligned.** Nothing in §2 refers
to a configuration, so an epoch straddling a boundary contains rounds at
two counts without ambiguity. This is admissible if §3.2 resolves in its
favour.

**(c) Epochs are configurations.** The grid is derived: an epoch ends
where a configuration ends. Maximal flexibility — no constant `W`, no
divisibility, no alignment. By §2.7 the grid then owes the lag of two,
and a configuration's boundary is set by its anchor, so the boundary of
configuration `k + 1` is a function of the verdicts of configuration
`k` — a lag of one. **Making (c) fit requires Barnacle to install a
count two configurations after the anchor that computed it, rather than
at the next one.** That is a change to Barnacle's control loop, not to
the composition: the AIMD rule reacts one configuration later. It is a
design decision and is not taken here.

### 3.2 Open: whether alignment is still needed

`OneEpoch` and the epoch-boundary restriction on count changes both
existed to keep a slot numbering stable. Under §2.2 and §2.3 no numbering
changes at a configuration boundary. It is therefore possible that the
composition needs no alignment between configuration boundaries and epoch
boundaries at all, which would make arrangement (b) available.

This is not established. Barnacle's `closed` is stated per configuration
against one uniform schedule, and by §2.7 the comparison must happen
where the widths are settled; whether the window of §2.5 may cross a
configuration boundary has to be checked. The answer decides whether
`boundary` survives as a field of the composed run, and it is the second
thing to determine (§5, step 8).

## 4. Labels

The AL labels of `docs/adaptive-leaders.md` are preserved where the
statement is preserved. AL5 (`run_agree`), AL6 (`run_commitSeq_agree`)
and the liveness results change coordinates, not content, and keep their
labels. Composition results are `I`-labelled, as in `docs/integration.md`.

## 5. Order of work

Each step is to build clean, with the six audits passing, before the
next begins.

1. `Properties/Bounded.lean` and `Properties/Derived/Bounded.lean`:
   `DecidedBelowRound`, its `mono`, `reschedule` and `agree` laws, and
   the conversion of §2.6. Nothing else changes. **This step is the
   cheapest test of the plan's premise; if the conversion needs more than
   `Slots.mono`, stop and reconsider.**
2. `Common/Slots.lean`: `Frame`, `Frame.toSlots`, `Frame.index`, and
   `Slots.uniform` recovered as the constant frame.
3. `Adaptive/Basic.lean`: `Epochs`, `Epochs.at`, and the constant grid.
4. `Adaptive/Policy.lean`: the structure of §2.4, `PickKeyed`, and
   `Policy.const` at the new signature.
5. `Adaptive/Run.lean`: the structures of §2.5, then `partialRun_agree`,
   `partialRun_assign_agree`, `run_agree`, `run_commitSeq_agree` and
   `Policy.const_run_decided`.
6. `Adaptive/Liveness.lean`: `PlacesRuns` over rounds, then
   `epoch_closes`, `exists_partialRun`, `run_exists`, `Run.commits` and
   the `OfSupport` section.
7. `Adaptive/Growth.lean`, `Adaptive/Joiner.lean`, and
   `LeanDagTest/Adaptive/Model.lean`.
8. `Integration/AdaptiveBarnacle.lean`: rebuilt as §3, beginning with
   §3.2 and settling on arrangement (a) or (b).

Arrangement (c) of §3.1 is deliberately not in this list. It requires a
change to Barnacle and should be decided separately, after (a) or (b) is
built and the cost of the rest is known.

## 6. What could go wrong

**The liveness arithmetic.** `Adaptive/Liveness.lean` holds 21 of the 85
uses of `epochOf` and 20 of the 24 uses of `W * …`. Those bounds are
presently linear in the slot index, so `omega` closes them; after §2.2
they are mediated by the frame and the grid, which `omega` cannot see
into. The step-6 proofs will need explicit monotonicity where they now
need none. This is the largest identified risk and the reason step 6 is
not attempted before step 5 is complete.

**The cumulative sum.** `Frame.toSlots` enumerates slots by a running
total of widths, and `Frame.index` is that total. Every use of a slot
index in the mechanism becomes a statement about it. The design keeps
those uses to one — the `closed` clause of §2.5 — and if they multiply,
the frame presentation removes less than it introduces, and the
constant-width case should be kept instead.

**The joiner.** `epochOf_add_of_dvd` states that a numbering starting at
an aligned offset agrees with the original about epochs, and
`Adaptive/Joiner.lean` uses it for a validator that joins mid-execution.
Under round coordinates the offset is a round offset and the lemma must
be restated. Its difficulty is not assessed.

**Conservativity.** `Policy.const_run_decided` anchors the definitions:
under the constant policy a run's verdicts are ordinary `Decided`
verdicts of the base schedule. It must still hold, and it is the check
that §2.3's re-indexing has not changed what a verdict means.

**The blast radius.** `Properties/` gains a definition and loses none, so
no protocol's obligations change, and `Decided S V κ v` remains indexed
by slot. If step 1 shows otherwise — if a protocol must supply a
round-bounded verdict directly rather than by conversion — the cost of
the plan is much larger than estimated here and it should be reconsidered
against leaving the composition at `OneEpoch` and documenting the
restriction.
