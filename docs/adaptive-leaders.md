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
> every statement planned here stands verbatim in `Adaptive/Mysticeti.lean`
> and `Adaptive/Odontoceti.lean` as corollaries of the generic theorems.

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
assignments and equal verdicts; corollary `adaptive_decided_agree`.
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
unchanged — and the policy's fairness clause, an `AdaptiveRun` exists on
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
| `Adaptive/Run.lean` | `AdaptiveRun`; uniqueness/safety (AL3); conservativity (AL4); the ledger (AL6) |
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
- **Multi-leader reassignment.** The `keyed` obligation under
  multi-leader rounds is recorded but the initial development takes one
  leader per round.
- **Changing `slotRound`.** Adaptivity here reassigns leader identity
  only; the round structure of the schedule stays fixed, as it does in
  Hammerhead.
