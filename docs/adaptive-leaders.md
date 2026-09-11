# lean-dag — Adaptive leaders: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

> **Status (September 2026).** Built, and since generalised. The
> mechanism planned below is now `Adaptive.Policy` over any
> `Properties.DagRule` (`Adaptive/Policy.lean`, `Adaptive/Basic.lean`,
> `Adaptive/Liveness.lean`); the core's bounded relation `DecidedWithin`
> is `AnchoredRule.DecidedWithin` (`Common/Anchored/Bounded.lean`), and
> every statement planned here stands verbatim in
> `Integration/AdaptiveMysticeti.lean` and
> `Integration/AdaptiveOdontoceti.lean` as corollaries of the generic
> theorems, the mechanism itself naming no protocol. §5's module plan is
> the plan as written.
>
> **§7 and §8 were added after reading the Hammerhead paper itself.**
> They record what the paper does that this arc does not — the
> reputation score reads parent edges rather than verdicts, and a
> schedule governs a bounded range of rounds — and plan the change. §1
> to §6 describe what is built; §7 says what it assumes of the network
> without saying so. §8 was rewritten once the Barnacle arc merged,
> because most of what §7 asks for is that arc's run.

This document is the design record for the **adaptive-leaders** arc,
written before the development rather than after it: the definitions and
theorems below are a plan, and the Lean signatures are proposals. The
question is whether a Hammerhead-style adaptive leader schedule — after
a commit, validators consult the agreed information and reassign the
leaders ahead, to favour validators observed live and fast — is safe and
live for both commit rules of this development, Mysticeti (report §3)
and Odontoceti (report §10). Results will carry **AL**-labels,
continuing the house scheme; everything will live in `LeanDag/Adaptive/`
with `decide` witnesses in `LeanDagTest/Adaptive/Model.lean`, consuming the
core read-only like every other arc.

## 1. The problem

In the base development the schedule is a `Slots` instance: `slotRound`
and `leader` are arbitrary *fixed* functions, and every result — the
decision relation, agreement, the liveness chain — is parameterised by
the instance. Fairness (P10, `FairScheduleOn`; its rated and run forms)
is an assumption precisely because a fixed `leader` could name Byzantine
validators for ever.

An adaptive schedule replaces the fixed `leader` with a function of the
*committed prefix*: after deciding the slots of one scheduling window,
validators recompute the leaders of a later window — demoting validators
whose slots were skipped, promoting those whose blocks certify quickly.
The intuition for safety is the development's own agreement theorem:
the verdict sequence is agreed (M6, M7), so any function of it is
agreed, and all correct validators derive the *same* revised schedule.
The intuition for liveness is Hammerhead's: a schedule that reacts to
observed skips satisfies fairness in practice far more readily than a
blind rotation.

Turning the safety intuition into a proof meets a genuine circularity.
In the decision relation, verdicts flow **downward**: a slot `k` is
decided indirectly by anchoring on a committed slot `j > k`, arbitrarily
far above. An adaptive schedule makes leader identity flow **upward**:
the leader of a high slot depends on verdicts below. Composing the two,
the verdict of `k` may depend on the leader of its anchor `j`, whose
identity depends on the verdict of `k`. Unrestricted, nothing rules out
a *self-justifying* schedule — an assignment whose induced verdicts are
exactly the ones that select it, alongside a second assignment doing the
same — and then two correct validators could hold different schedules
with all clauses satisfied, which is an agreement failure manufactured
by the mechanism itself. The whole design problem is to stratify the
dependency so the fixpoint is forced unique, without giving up the
anchors liveness needs.

## 2. The design

**Epochs, and a lag of two.** Slots are grouped into epochs of `W`
consecutive slots (`epochOf k := k / W`; `W` a parameter, constrained
below by liveness only). The schedule of epoch `e` is computed from the
verdicts of epochs `≤ e − 2`; epochs `0` and `1` use the base
assignment. Verdicts of epoch `e` must be derivable with every slot of
the derivation — anchor and intermediates alike — lying strictly below
the start of epoch `e + 2`.

The dependency is then well-founded:

    assignment of epoch e+1   ← verdicts of epochs ≤ e−1
    verdicts of epoch e−1     ← leaders of epochs ≤ e   (anchors below start of e+1)
    leaders of epoch e        ← verdicts of epochs ≤ e−2

Each line consults strictly earlier data than the line above it
produces. The lag of two is the least that closes the loop: with lag
one, the verdicts of epoch `e` would need leaders of epoch `e + 1`,
which would need verdicts of epoch `e − 1` — sound — but the anchor
window for epoch `e` would end at the epoch boundary itself, and the
slots at the top of an epoch would have no eligible anchors at all.
This mirrors what deployments do: reputation computed from committed
sub-DAGs is applied to leader selection after a pipeline delay.

**The bounded decision relation.** The stratification cannot be
expressed with the existing `Decided`, whose derivations record no bound
on their anchors. A four-constructor relation `DecidedWithin B` —
`Decided` with every slot mentioned strictly below `B` — carries the
bound in the relation, and two structural lemmas connect it to the
development:

- `DecidedWithin.toDecided` — forgetting the bound yields an ordinary
  derivation, so every safety theorem of the base development applies to
  bounded verdicts without change. Agreement for the new relation is
  M6, not a new proof.
- `decidedWithin_congr` — the relation reads the schedule only at slots
  below `B` (only `IsLeaderBlock` reads `leader`; `slotRound` is fixed),
  so two `Slots` instances agreeing on leaders below `B` derive exactly
  the same bounded verdicts. This is what lets each epoch's verdicts be
  computed against a schedule that is only partially determined.

An alternative was considered and rejected: keeping plain `Decided` and
proving that some derivation uses only bounded anchors. The relation is
a `Prop`; derivations cannot be inspected, so the bound must live in the
statement.

**The policy.** A `Policy` packages the reassignment rule with the
clauses it owes:

```lean
structure Policy (Validator : Type*) [Slots Validator] where
  W : ℕ                       -- epoch length
  pick : (U : BlockUniverse Validator BlockId Payload) →
    View Validator BlockId Payload U → (ℕ → Option BlockId) → ℕ → Validator
  adapted : ∀ U (V₁ V₂ : View Validator BlockId Payload U) v w k,
    (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
    pick U V₁ v k = pick U V₂ w k
  keyed : …                   -- per-round leader distinctness, every output
  base_prefix : ∀ U V v k, epochOf W k < 2 → pick U V v k = Slots.leader k
```

`adapted` is the measurability clause and the heart of the safety
argument: the leader of slot `k` is a function of the verdicts of
epochs `≤ epochOf k − 2` and of nothing else — the view included.
`pick` receives the universe and the validator's own view of it, so
reputation may consult the committed blocks themselves — certification
patterns, timestamps in payloads — not merely the verdict vector. The
view is what a validator actually has; a rule reading it freely could
hand two correct validators different leaders, and `adapted` is what
rules that out. It is no restriction in practice: the committed prefix
is what every view holding those verdicts holds whole, by causal
completeness, and a rule computing from its own copy of it satisfies
the clause. (What a *deployed* validator may consult is its committed
prefix only; as with the
enforceability discussion of report §4, the model states the
mathematical condition and the implementation owes the discipline.)

`keyed` deserves a note. `Slots` requires `(slotRound, leader)` to be
injective. Under one leader per round this is free whatever the policy
does; under multi-leader rounds a reassignment could collide two slots
of one round onto one validator, so the clause is genuinely owed. The
initial development will take the single-leader-per-round case
(`slotRound` injective), where `keyed` is a lemma, and record the
multi-leader obligation.

`slotsOf` turns an assignment `ℕ → Validator` into a `Slots` instance —
`slotRound`, `mono`, `unbounded` from the base instance, `leader` the
assignment (AL1).

**The run.** The central object is a schedule-and-verdict pair coherent
with the policy:

```lean
structure AdaptiveRun (P : Policy Validator)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  assign : ℕ → Validator
  vdct : ℕ → Option BlockId
  closed : ∀ k, DecidedWithin (S := slotsOf P assign)
    (P.W * (epochOf P.W k + 2)) U V k (vdct k)
  coherent : ∀ k, assign k = P.pick U V vdct k
```

Existence and uniqueness are deliberately separated, mirroring the base
development's split between the `Decided` relation and `decided_unique`:
**uniqueness is the safety theorem, existence is the liveness theorem.**
A partial variant (`closed`/`coherent` for epochs `< E` only) states
prefix agreement for validators that have not decided equally far.

## 3. The theorems

**AL1 (instance).** `slotsOf` yields a lawful `Slots` instance;
`keyed` from injective `slotRound` in the single-leader case.

**AL2 (structure).** `DecidedWithin.toDecided` and
`decidedWithin_congr`, as above. Mechanical, and consumed everywhere.

**AL3 (safety: the fixpoint is unique).** `adaptiveRun_unique`: any two
runs over the same universe — *whatever views they were derived from,
and with no fairness or synchrony hypothesis at all* — have equal
assignments and equal verdicts. Built as `Adaptive.run_agree`, whose two
halves are the verdict and assignment statements directly, so the planned
corollary is a projection.
Proof plan, by strong induction on the epoch: the verdict prefixes
below epoch `e − 1` agree by hypothesis, so `adapted` forces the
assignments to agree through epoch `e + 1`, so `decidedWithin_congr`
puts both runs' epoch-`e` verdicts in the *same* `Slots` instance, where
`toDecided` and M6 close the case. Per epoch the argument instantiates
the base agreement theorem; nothing about counting is re-proved. The
headline: **adaptivity is safe unconditionally** — only liveness will
price the policy's choices.

**AL4 (conservativity).** For the constant policy
(`pick _ _ := Slots.leader`), a run's verdicts are fixed-schedule
verdicts: `vdct k` is `Decided`-derivable with the base instance and
agrees with every base verdict by M6. The anchor for the definitions,
per the house rule that a new relation must instantiate to the old one.

**AL5 (liveness: the fixpoint exists).** Under the standard interface —
`SynchronisedOn` and `PopulatedOn`, supplied by view convergence
unchanged — and the policy's fairness clause, an `Adaptive.Run` exists on
any view caught up to the horizon (`View.CoversUpto`: the view holds
every block at a round up to `N`). The full view is caught up to every
horizon, so the whole-universe reading is the special case; under
eventual DAG synchrony (`liveness.md` §4.2) every correct validator's
view is caught up once delivery has reached the horizon, which is what
makes the statement one about validators rather than about what exists.
The fairness clause is the adaptive counterpart of
`FairRunOn`: every assignment the policy emits contains, in each epoch,
`c` consecutive `T`-led slots positioned so that their span anchors the
whole epoch below (`SpansEligible c` at the run's top). Construction by
strong recursion on epochs: the run that fairness places in epoch
`e + 1` commits directly (L4, bounded trivially), and a
`DecidedWithin`-sharpened `decided_below_of_committed_run` decides every
slot below it with anchors at or below the run's top — strictly inside
the epoch-`e` window. The existing proof already anchors at
`Nat.find … ≤ n`; sharpening its statement to the bounded relation is
expected to be a restatement, not a new argument.

Hammerhead's purpose lands here: an adaptive policy satisfies the
fairness clause by *reacting* — a validator skipped throughout an epoch
is demoted before the window two epochs up — where a fixed schedule
satisfies it only by assumption. But which validators are reliable is
not the designer's to know, so fairness remains a joint condition
exactly as P10 is: the theorem consumes it as a clause, and proving
that a concrete scoring rule discharges it under a crash model is
future work, not this arc.

**AL6 (the adaptive ledger).** The commit sequence read from `vdct` is
agreed across validators — a corollary of AL3 in the shape of M7.

**AL7 (Odontoceti).** The identical skeleton over the two-round
relation: `Odontoceti.DecidedWithin`, its congruence and embedding, then
per-epoch instantiation of O5/O6 for uniqueness and of O7–O10 for
existence, with the two-round span (`spansEligible_two`, O8) replacing
the three-round one. The arc will show the adaptive layer is
rule-agnostic: it consumes each protocol's agreement and committed-run
theorems as interfaces and never counts anything itself.

**AL8 (witness).** A four-validator model at `f = 1` with a genuinely
adaptive policy — demote-on-skip: a validator skipped in the last closed
epoch moves to the back of the rotation. To exhibit on data, by
`decide`: the epoch-2 assignment *differs* from the base rotation (the
policy actually adapts); every epoch closes within its window; and the
run's verdicts agree with the hand-computed ones. The `Ucrash` family
of the Safe Skip arc is the natural substrate — its crashed validator
is skipped at every slot it leads, so the policy rotates it out, and
the two arcs compose into one story: demoted while down, safe-skipped
back in, re-promoted after recovery.

**AL9 (the necessity question — stretch).** Is the anchor bound
necessary for AL3? A model with two self-justifying runs under
unbounded anchors would justify the stratification the way the
`bound_is_necessary` witness justified the convergence bound; a proof
that small models admit none would also be informative. Open, and not
promised: the interaction between an anchor's leader and the verdict it
anchors is delicate, and the answer may need more than four validators.

## 4. What liveness constrains

Safety is indifferent to `W`; liveness is not. Anchors for epoch `e`
live below the start of epoch `e + 2`, so the eligibility gap (three
rounds under Mysticeti's rule, two under Odontoceti's) plus the run
length `c` plus the fairness placement slack must fit inside a window of
`2W` slots — and the top-of-epoch slots need their anchors from the
*next* epoch's run, which is why the lag is two and not one. The
witness will pin a workable `W` for the pipelined round-robin base
(expected single digits); the theorems will carry `W`'s lower bound as
an explicit hypothesis rather than a chosen constant.

## 5. Module plan

| Module | Contents |
|:---|:---|
| `Adaptive/Basic.lean` | epochs; `DecidedWithin`; congruence and embedding (AL2) |
| `Adaptive/Policy.lean` | `Policy`, `slotsOf` (AL1) |
| `Adaptive/Run.lean` | `Adaptive.Run`; uniqueness/safety (AL3); conservativity (AL4); the ledger (AL6) |
| `Adaptive/Liveness.lean` | the bounded committed-run lemma; existence (AL5) |
| `Adaptive/Odontoceti.lean` | the two-round mirror (AL7) |
| `LeanDagTest/Adaptive/Model.lean` | demote-on-skip on the round-robin base (AL8) |

## 6. Out of scope

- **Composition with garbage collection** — whether `chop` commutes with
  the adaptive fixpoint. Expected from G2-style invariance plus AL3, but
  a separate arc's question.
- **Reputation mechanisms.** The fairness clause is assumed of the
  policy, not derived: no scoring rule is modelled, and nothing is said
  about an adversary gaming reputation. What is proved is that *any*
  adapted policy is safe and *any* adapted-and-fair policy is live.
- ~~**Multi-leader reassignment.**~~ Built. `Policy.keyed` replaces the
  one-leader clause `inj`, `slotsOfKeyed` replaces `slotsOf` through the
  arc, and `Adaptive.PickKeyed` states the obligation at every count a
  count-varying mechanism may reach. Report §13.1 and AL1.
- **Changing `slotRound`.** Adaptivity here reassigns leader identity
  only; the round structure of the schedule stays fixed, as it does in
  Hammerhead.

## 7. What the Hammerhead paper does that this arc does not

*(Added September 2026, after reading `papers/hammerhead.pdf`
— Tsimos, Kichidis, Sonnino and Kokoris-Kogias, *HammerHead:
Score-based Dynamic Leader Selection*.)*

§2's design pays for its stratification with a condition on executions.
`Adaptive.PartialRun.closed` asks

```lean
closed : ∀ k, epochOf P.W k < E →
  DecidedBelow R (slotsOfKeyed assign keyed) (P.W * (epochOf P.W k + 2)) V k (vdct k)
```

and `DecidedBelow R S B V k v` asks that the verdict of slot `k` be
unchanged by any reassignment of the leaders at or above `B`. So every
slot must settle without reading the schedule two epochs up. §4 sizes
`W` against the eligibility gap, the run length `c` and the placement
slack, and `Adaptive.exists_partialRun` carries liveness on the window
`[W, W · (E + 2))` as a hypothesis at every height. Before GST the run
length is unbounded, so no `W` satisfies it, and on such an execution no
`Adaptive.Run` exists: AL3 is true and has no instances. The arc says
nothing about what a validator should do when a slot has not settled in
time, and the obvious thing — continue under the schedule in force —
is what loses agreement.

The paper has no such condition, and says why it does not need one.

**The boundary is a round, not an event.** A schedule expires at
`activeSchedule.initialRound + T`, fixed when the schedule is installed,
whether or not anything commits in between.

**Ordering stops at the boundary.** `ORDERHISTORY` (Algorithm 2, lines
27–37) pops committed anchors in order and, at the first one whose round
has reached the boundary, updates the schedule and **returns** — without
ordering that anchor or anything above it:

```
30:   t ← activeSchedule.initialRound + T
31:   if t ≤ anchor.round then
32:     activeSchedule ← UPDATESCHEDULE(anchor)
33:     return
```

A verdict derived under a schedule therefore reaches the ledger only for
rounds strictly below that schedule's expiry. The safety claim is stated
with the same bound: Claim 4 concludes that two honest parties order the
same vertices in the same order between `max{r¹ᵢ, r¹ⱼ}` and
`min{S, r²ᵢ, r²ⱼ}`, where `S` is the round of the next schedule change.

**The switch is retroactive.** §III addresses exactly the case a slot
fails to settle: validators "may not commit a leader immediately, but
through recursion over the DAG and after an unbounded number of rounds
before GST", and a validator that has been running a stale schedule
"need[s] to retroactively apply the new schedule for the time-period in
which they where operating under the previous schedule, while the new
schedule was already active". The schedule may be stale for unboundedly
long; the output never is.

The invariant that makes this consistent is a separation the arc does
not have. *Naming* an anchor may run past a schedule's boundary — that
is how the switch is detected, and both parties do it under the same
stale schedule, so they detect it at the same anchor. *Ordering* never
runs past the boundary under an expiring schedule. Proposition 1 turns
the first into agreement on the switch point, and Claim 4 turns the
second into agreement on the output.

### 7.1 The deeper difference: the score reads the DAG, not the verdicts

`Policy.pick` takes `ℕ → Option BlockId` — the verdicts. That is the
source of the circularity §1 describes, and the two-epoch lag is the
repair.

`UPDATESCHEDULE` (Algorithm 2, lines 38–42) reads no verdict. It walks
the rounds of the trigger anchor's causal history and adds a point to
each validator that *voted* for the previous round's leader under the
schedule in force — a parent edge, not a decision. The reputation score
is a function of two agreed objects: the causal history of an agreed
anchor, and the schedule already installed. §VII draws the contrast
with Shoal, which scores committed and skipped leaders and so does read
verdicts.

Because the score reads no verdict, the leader of a slot cannot depend
on the verdict of a slot the leader affects, and the circularity of §1
does not arise. Hammerhead needs no epoch lag: it excludes the trigger
anchor's own sub-DAG from the score — "we calculate the reputation score
up to but excluding the committed leader" — and that one exclusion is
the whole of its delay.

### 7.2 What is missing, in three items

1. **The policy reads verdicts, and that is the root.** The two-epoch
   lag repairs a circularity that a score over parent edges does not
   create, and the lag is what puts the `2W` window into `closed`. The
   lag is a sound device for a strictly larger class of policies, and it
   is not Hammerhead's device.
2. **The run has no ranges.** One global `assign` and one `vdct` over all
   slots leaves nowhere to say which rounds a schedule governs, which is
   why the window has to be a condition on the execution rather than a
   bound the mechanism enforces. Hammerhead's boundary and Barnacle's
   range are the same device, and this arc has neither. §8.4 corrects an
   earlier reading of this section that took the boundary to be the
   root; it is a consequence of the first item.
3. **The fixpoint is not the process.** One `assign : ℕ → Validator`
   admits no validator that is behind, and so no retroactive
   re-application. Proposition 1 and Lemma 1 are about validators
   catching up through every intermediate schedule, "without skips";
   the paper calls the schedule switch "the second and most critical
   challenge", and it is the part this model cannot see.

None of this makes AL3 false. It makes AL3 a theorem about executions
in which the network behaves, stated in a form that does not say so.

## 8. Plan: Hammerhead as a Barnacle configuration rule

*(Rewritten after the Barnacle arc merged. This section planned a
segmented run of its own; the Barnacle arc builds that run, so most of
what it planned is an instantiation.)*

The Barnacle arc on `main` reconfigures by installing a `Config` —
the slots of each round, the leader of each slot, and the interval to
the next reconfiguration — chosen by a rule that reads the universe and
an anchor. Hammerhead reconfigures by installing a leader assignment
chosen by a rule that reads the universe and an anchor. They are the
same mechanism with two statistics: Barnacle's counts direct commits to
set the widths, Hammerhead's counts parent edges to set the leaders.

### 8.1 What is already common, and what is not

`Barnacle.Config` mentions no protocol, and neither do the run, the
update interface or the three safety results:

| declaration | what it consumes |
|:---|:---|
| `Config`, `cum`, `roundOf`, `head`, `sched` | nothing but `Slots` |
| `UpdateRule`, `Anchored` | `R.Universe`, `R.View` |
| `PartialRun` | `R.Decided`, `R.Universe`, `R.View`, two numeric bounds |
| BN3, BN5, BN6 | `R.toDagRule`, `Properties.Agree`, `CommitsCandidate` |

Every one of those is at `Properties.DagRule` level. The `BaseRule`
extras — `full`, `historyView`, `waveLength`, `DirectCommitIn` — are
consumed by the window, the AIMD rule and the liveness arc, not by the
run or by agreement. So the run and its safety could be lifted to the
common layer over a `DagRule` with `maxLeaders` and `maxInterval` as
plain naturals, leaving Barnacle with `BaseRule`, `Params`, the window,
AIMD and the heads descent.

**That lift is not proposed yet.** It is a move of about a thousand
lines across five directories for the benefit of a second caller, and
the second caller can be written without it. It becomes the right thing
when a third mechanism arrives, or when either of the two frictions
below starts to bite.

### 8.2 The minimal path, and what it accepts

Write the Hammerhead score as a `Barnacle.UpdateRule`:

```lean
def hammerhead (score : (U : R.Universe) → BlockId → (ℕ → ℕ → Validator) → ℕ → ℕ → Validator)
    (hk : …) : UpdateRule R :=
  fun C b U _V A => (⟨C.slotsAt, C.slotsAt_pos, score U A C.lead, hk …, C.interval⟩, b)
```

— a rule that leaves the widths and the interval alone and moves the
leaders. Then BN3 gives agreement of the schedule sequence and of the
verdicts, BN5 the ledger, BN6 conservativity and BN14 validity, with no
new induction. `Anchored` is the clause the score owes, and it is the
same clause `Aimd.rule` discharges by not reading the view.

Three frictions come with the minimal path, and none of them is a
proof obligation:

1. **The interface asks for more than the score needs.** `BaseRule`
   carries `DirectCommitIn` and `waveLength`, which a Hammerhead score
   does not read. Every rule of this development supplies them through
   `ofAnchored`, so the cost is in the signature and not in the work.
2. **`Params` carries `num` and `den`**, the AIMD threshold, which a
   Hammerhead run leaves unused.
3. **Pipelined bases only.** `Config.slotsAt_pos` puts at least one slot
   in every round, and `roundOf` is `Nat.findGreatest` bounded by the
   slot index, which is sound because `r ≤ cum r`. Allowing empty rounds
   breaks that bound and leaves `roundOf` with no search range, so this
   is not a clause to relax — it is what `Config` means. The
   consequence: a `Config` cannot express `Slots.uniform 3 1`, the
   three-round spacing that `LeanDagTest/Adaptive/Model.lean` uses on
   `U7`. That witness stays with the fixpoint arc, where the base is an
   arbitrary `Slots`.

### 8.3 Steps

1. **AL11 — the score.** A function
   `(U : R.Universe) → BlockId → (ℕ → ℕ → Validator) → ℕ → ℕ → Validator`
   from the universe, the trigger anchor and the leaders in force, with
   two clauses: `Anchored`, which BN3 consumes, and the sharper reading
   that `score U A prev` reads `U` only through
   `historyFrom (R.block U) A` — the clause `BaseRule.Laws.historyView_ids`
   states for the window and BN2 turns into agreement across views.
   `Config.keyed` for the emitted leaders is the obligation
   `Policy.keyed` and `Adaptive.PickKeyed` already record.
2. ~~**AL12 — the segmented run.**~~ `Barnacle.PartialRun`.
3. ~~**AL13 — safety.**~~ BN3 at the rule of AL11.
4. ~~**AL14 — the ledger.**~~ BN5. ~~**AL15 — conservativity.**~~ BN6 at
   `constRule`, and BN14 gives validity as well.
5. **AL16 — liveness, and this is the work.** BN11 discharges the
   liveness clause from runs of heads, but it asks
   `UpdKeeps upd (fun C => C.head = head)` for **one fixed** head
   function: the AIMD rule satisfies it by never moving the heads, and a
   Hammerhead rule does nothing else. `Progress.Statement` is already
   general in the clause `Q`, so the shape is

   ```
   Q C := C.head ∈ 𝓗
   ```

   for the set `𝓗` of head functions the score can emit, with the
   liveness hypothesis becoming "every member of `𝓗` has runs of heads
   for every good set". BN8b accepts that as a hypothesis today.
   Discharging it for a concrete score is the paper's Lemmas 2 to 4 and
   Leader-Utilization, and it is the one part of this plan that is not a
   restatement. **Hammerhead is the missing instance of Barnacle's
   `UpdKeeps`**, which the review of the Barnacle arc recorded as
   supported and unwitnessed.
6. **AL17 — the witnesses.** A run whose second configuration differs
   from its first in the leaders alone, alongside `Varying.lean`'s run
   that differs in the widths and the interval; and a refutation for the
   fixpoint arc — an execution in which a slot needs an anchor more than
   two epochs above it, so that no `Adaptive.Run` exists over it. The
   second makes §7's vacuity concrete and is the honest companion to
   AL9.

### 8.4 The truncation is Barnacle's already

§7 separated *naming* an anchor from *ordering* it, and read the Barnacle
arc as lacking the second. That reading was wrong, and the correction is
worth stating because it makes this plan smaller.

`Barnacle.PartialRun` truncates. Configuration `k` governs the rounds
`(start k, start (k + 1)]` with `start (k + 1)` the anchor's own round,
consecutive ranges abut, `rangeLedger k` reads exactly the range, and
`round_of_mem_ledgerUpto` says the ledger to any height stops at that
height's start round. The schedule is extended above the range to name
anchors, which is what a validator does while it is still on `cfg k` and
has not yet found the anchor that closes the range. Nothing above the
range is output under `cfg k`.

So there is no Strand A. What §7 diagnosed is Strand B alone, and it is
this arc's alone: `Policy.pick` reads verdicts, which creates the
circularity of §1, which forces the two-epoch lag, which forces
`DecidedBelow` at `W · (epochOf k + 2)`. That last clause is what
asynchrony falsifies, and it is not a truncation question. Deciding
slots beyond an epoch in order to settle slots within it is exactly what
the bound forbids and exactly what both Barnacle and Hammerhead do.

A rule that reads the anchor's causal history rather than the verdicts
has no circularity, needs no bound, and inherits the truncation from the
run it is installed in.

### 8.5 What remains of the fixpoint arc

`Adaptive.Run` and AL3 are not superseded. They prove safety for
policies that read **verdicts**, which is a strictly larger class than
the scores Hammerhead admits, and the two-epoch lag is what makes that
class tractable. The window condition of §7 is the price of the
generality, and the arc should say so rather than carry it silently. Its
`U7` witness at `slotRound k = 3k` also exercises a base that no `Config`
can express, so the two arcs cover different schedules as well as
different policies.

### 8.6 Decisions

- **D18 — the boundary's unit.** Settled by the instantiation:
  `Config.interval` counts rounds, as Hammerhead's `T` does.
  `epochOf W k = k / W` counts slots and belongs to the fixpoint arc.
- **D19 — where a boundary sits.** `Barnacle.PartialRun` places it at
  `start k + (cfg k).interval`, and `start (k + 1)` at the anchor's own
  round; Hammerhead places the next boundary at
  `activeSchedule.initialRound + T`. The two agree once `start k` is
  read as "the round after which configuration `k` is in force", and the
  paper's footnote 3 leaves open whether `T` counts rounds or committed
  leaders. Take Barnacle's, and record the paper's ambiguity.
- **D20 — what becomes of the fixpoint arc.** Keep it, and label it as
  §8.5 describes.
- **D21 — when to lift the run to the common layer.** Not with this
  arc. When a third mechanism wants it, or when §8.2's first two
  frictions stop being cosmetic.
