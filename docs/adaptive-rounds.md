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
only the coordinates in which it says it, and the reason is the
composition with Barnacle (`docs/barnacle.md`).

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

**The coordinate to use is `(round, validator)`.** `Slots.keyed`
(`Common/Slots.lean`) states that `fun k => (S.slotRound k, S.leader k)`
is injective, so a slot is determined by its round and its leader. Rounds
are common to every configuration, and so are validators. Slot indices
are not.

The coordinate depends on the assignment, which is what the policy
computes. This is not circular. The assignment at epoch `e` is a function
of the verdicts at epochs `≤ e − 2`, whose assignment is determined
before epoch `e` is; the lag that makes the adaptive fixpoint
well-founded is the same lag that makes the coordinate well-defined at
the point where it is read. §2.4 states the obligation this places on the
induction.

## 2. The proposed shape

Signatures below are proposals. Binders are elided with `…`.

### 2.1 Epochs are spans of rounds

    def epochAt [S : Slots Validator] (W κ : ℕ) : ℕ := S.slotRound κ / W

`W` becomes a number of rounds. Under one leader per round `epochAt W κ`
and `epochOf W κ` agree; under `m` leaders per round they differ by the
factor `m`, and it is `epochAt` that is stable under a change of `m`.

`epochOf` remains for the arithmetic lemmas that are about division
(`epochOf_lt_iff`, `epochOf_mono`, `epochOf_add_of_dvd`); `epochAt W κ`
is `epochOf W (S.slotRound κ)`.

### 2.2 Verdicts are indexed by round and validator

    vdct : ℕ → Validator → Option BlockId

read at `(S.slotRound κ, S.leader κ)` wherever the present development
reads `vdct κ`. `Slots.keyed` is what makes this faithful: distinct slots
receive distinct coordinates.

Pairs that are not slots of `S` receive values that no clause reads,
exactly as out-of-range slot indices do now.

### 2.3 The policy

    structure Policy (R : DagRule Validator BlockId Payload) [S : Slots Validator] where
      W : ℕ
      W_pos : 0 < W
      pick : (U : R.Universe) → R.View U →
        (ℕ → Validator → Option BlockId) → ℕ → Validator
      keyed : ∀ U V v κ₁ κ₂, S.slotRound κ₁ = S.slotRound κ₂ →
        pick U V v κ₁ = pick U V v κ₂ → κ₁ = κ₂
      adapted : ∀ U V₁ V₂ v w κ,
        (∀ r a, r / W + 2 ≤ S.slotRound κ / W → v r a = w r a) →
        pick U V₁ v κ = pick U V₂ w κ
      base_prefix : ∀ U V v κ, S.slotRound κ / W < 2 → pick U V v κ = S.leader κ

Two changes beyond the coordinates. `inj : Function.Injective S.slotRound`
becomes `keyed`, since the composition places several leaders in a round;
the substitution and the derived clause `PickKeyed` — the same law at
every count up to a bound — are already proved on
`compose-barnacle-hammerhead` and are to be carried over. And `adapted`'s
hypothesis now quantifies over a round `r` and a validator `a`, and names
no slot index; that is the whole of the change this document is for.

### 2.4 The run

    structure PartialRun (P : Policy R) (U : R.Universe) (V : R.View U) (E : ℕ) where
      assign : ℕ → Validator
      keyed : ∀ κ₁ κ₂, S.slotRound κ₁ = S.slotRound κ₂ → assign κ₁ = assign κ₂ → κ₁ = κ₂
      vdct : ℕ → Validator → Option BlockId
      closed : ∀ κ, S.slotRound κ / P.W < E →
        DecidedBelowRound R (slotsOfKeyed assign keyed)
          (P.W * (S.slotRound κ / P.W + 2)) V κ (vdct (S.slotRound κ) (assign κ))
      coherent : ∀ κ, S.slotRound κ / P.W < E + 1 → assign κ = P.pick U V vdct κ

`DecidedBelowRound` is §2.5. The agreement induction (`partialRun_agree`,
`run_agree`, AL5 and AL6) runs on the epoch as before; what changes is
that the induction hypothesis must now supply the assignment as well as
the verdicts before the coordinate `(S.slotRound κ, assign κ)` is
meaningful. It does: at epoch `e` the hypothesis covers epochs `< e`,
`adapted` reads epochs `≤ e − 2`, and the coordinates at those epochs are
fixed by assignments the hypothesis has already settled.

### 2.5 A round-indexed bound

`DecidedBelow R S B V κ v` (`Properties/Bounded.lean`) holds the round
structure fixed and requires the verdict to be unchanged when the leaders
of slots with **index** `≥ B` are reassigned. Under §2.1 the bound wanted
is a round: the leaders of slots at **rounds** `≥ B`.

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

## 3. The composition after the change

The composed run keeps Barnacle's per-configuration data — `start`,
`count`, `backoff`, `anchor` — and one global verdict function
`vdct : ℕ → Validator → Option BlockId`. It carries no translation.

**Deleted from `Integration/AdaptiveBarnacle.lean`:** `width`, `base`,
`base_zero`, `base_succ`, `dvd_base`, `base_det`, `width_det`, `flat`,
`flat_eq`, `flat_det`, `base_eq`, `OneEpoch`, `count_dvd`, `span_eq`,
`count_interval`, `EpochAligned`, `epochAligned_sum`, `rangeSlots`,
`roundUp`, `dvd_roundUp`, `le_roundUp`, `roundUp_lt`, `delay_lt`,
`UpdDivides`, and the `coherent`/`flat_eq` fields of `ComposedRun`. Their
subject is the translation.

**Retained:** the per-configuration schedule `configSched`, and with it
`mixLeader`, `mix_threshold`, `mix_top`, `mixLeader_keyed` and
`configSched_congr`. Two runs' verdicts can be compared only over one
`Slots`, and `DecidedBelow`'s third clause fixes the round structure by
design — `Decided` is an opaque field of `DagRule`, so no round-locality
is available generically. A schedule uniform at count `m` has
`slotRound κ = κ / m`, whose agreement follows from agreement of the
single number `count k`; a schedule spanning several counts has no such
property. Retaining the uniform per-configuration schedule is therefore
not a convenience but the condition under which the comparison is
available at all.

`mixLeader` is two-sided — Barnacle's rotation at the rounds outside a
configuration's range, the reassignment inside — which is proved on
`compose-cadence` and is to be carried over. It is what lets the window
in §2.4 reach past a configuration, since the reassignment says nothing
there.

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

**Open: whether any alignment restriction remains.** `OneEpoch` and the
epoch-boundary restriction on count changes both existed to keep a slot
numbering stable. Under §2.1 and §2.2 no numbering changes at a
configuration boundary, and an epoch that straddles one contains rounds
at two counts without ambiguity. It is therefore possible that the
composition needs no alignment between configuration boundaries and
epoch boundaries at all. This is not established: Barnacle's `closed` is
stated per configuration against one uniform schedule, and whether the
window of §2.4 crossing a configuration boundary is admissible has to be
checked. It is the second thing to determine (§5, step 8), and the answer
decides whether `boundary` survives as a field of the composed run.

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
   the conversion of §2.5. Nothing else changes. **This step is the
   cheapest test of the plan's premise; if the conversion needs more than
   `Slots.mono`, stop and reconsider.**
2. `Adaptive/Basic.lean`: `epochAt`, and `slotsOfKeyed` in place of
   `slotsOf` (carried from `compose-barnacle-hammerhead`).
3. `Adaptive/Policy.lean`: the structure of §2.3, `PickKeyed`, and
   `Policy.const` at the new signature.
4. `Adaptive/Run.lean`: the structures of §2.4, then `partialRun_agree`,
   `partialRun_assign_agree`, `run_agree`, `run_commitSeq_agree` and
   `Policy.const_run_decided`.
5. `Adaptive/Liveness.lean`: `PlacesRuns` over rounds, then
   `epoch_closes`, `exists_partialRun`, `run_exists`, `Run.commits` and
   the `OfSupport` section.
6. `Adaptive/Growth.lean` and `Adaptive/Joiner.lean`.
7. `LeanDagTest/Adaptive/Model.lean`: the witnesses.
8. `Integration/AdaptiveBarnacle.lean`: rebuilt as §3, beginning with the
   question left open there.

## 6. What could go wrong

**The liveness arithmetic.** `Adaptive/Liveness.lean` holds 21 of the 85
uses of `epochOf` and 20 of the 24 uses of `W * …`. Those bounds are
presently linear in the slot index, so `omega` closes them; after §2.1
they are mediated by `S.slotRound`, which `omega` cannot see into. The
step-5 proofs will need explicit monotonicity where they now need none.
This is the largest identified risk and the reason step 5 is not
attempted before step 4 is complete.

**The joiner.** `epochOf_add_of_dvd` states that a numbering starting at
a slot-aligned offset agrees with the original about epochs, and
`Adaptive/Joiner.lean` uses it for a validator that joins mid-execution.
Under round coordinates the offset is a round offset and the lemma must
be restated. Its difficulty is not assessed.

**Conservativity.** `Policy.const_run_decided` anchors the definitions:
under the constant policy a run's verdicts are ordinary `Decided`
verdicts of the base schedule. It must still hold, and it is the check
that §2.2's re-indexing has not changed what a verdict means.

**The blast radius.** `Properties/` gains a definition and loses none, so
no protocol's obligations change, and `Decided S V κ v` remains indexed
by slot. If step 1 shows otherwise — if a protocol must supply a
round-bounded verdict directly rather than by conversion — the cost of
the plan is much larger than estimated here and it should be reconsidered
against leaving the composition at `OneEpoch` and documenting the
restriction.
