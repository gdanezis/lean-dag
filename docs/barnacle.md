# lean-dag — Barnacle: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Barnacle** arc,
written before the development and brought to its final position after
it (§10, §14): the definitions and theorems below are what was built,
the Lean signatures are the sources', and §12 records the decisions
taken along the way. The question
is whether the adaptive *leader-count* mechanism of the Barnacle
paper (`\sysname` in the manuscript) — every few seconds,
measure on the agreed DAG the fraction of leader slots the base protocol
decided directly, and drive the number of leaders per round with an
additive-increase, multiplicative-decrease rule — is safe and live over
each of the four base protocols this development already formalises:
Mysticeti (report §3), Odontoceti, which the paper calls Blue Bottle
(report §10), Nemo-Nemo (report §15), and Orcaella, the hybrid
two-round rule at `n ≥ 5·fb + 3·fc + 1` (report §14; instantiated
after the arc closed — §15). Results carry **BN**-labels;
everything lives in `LeanDag/Barnacle/` under the statement/proof
partition (§10), with `decide` witnesses in `LeanDagTest/Barnacle/`,
consuming the core read-only.

## 0. Overview

The paper abstracts its base protocol as four assumptions, A1–A4: rounds
and slots, causal completeness, a direct decision predicate local to a
wave, and safety and liveness for every fixed configuration. Its
mechanism is a control loop on one integer. Upon committing the first
leader whose round exceeds `lastRound + Interval` — the *anchor* — a
validator takes the anchor's causal history over the last `Interval`
rounds as the *window*, counts the slots the direct rule decides within
the window, compares the count with the number expected under the
current leader count, and moves the count up by one or down by
`2^backoff`; the new count applies to rounds after the anchor.

The arc's one structural observation is that **the paper's algorithm
decides under the count in force and only then switches**. Algorithm 2's
`TryDecide` evaluates every round above the last commit at the current
count; `TryCommit` walks the verdicts in slot order, commits the anchor,
updates, and returns; only rounds above the anchor are re-decided under
the new count. So the verdicts of configuration `k`'s range — the rounds
strictly above the `k`-th anchor and up to the `(k+1)`-st — are
derivations of the base relation against a **fixed** uniform schedule,
`m_k` leaders in every round, including whatever decision-anchors above
the `(k+1)`-st anchor an indirect decision reads. Nothing in the range
depends on configuration `k+1`. The dependency is therefore well-founded
by induction on `k`, and the arc needs neither the bounded relation nor
the two-epoch lag of the identity-adapting arc (`adaptive-leaders.md`
§2), whose circularity arose because there the leader of a slot's anchor
was itself a function of verdicts.

Three consequences shape the plan.

- **Safety holds for any update rule a validator can run.** An update
  rule takes the validator's own view, and nothing then makes two of them
  agree — a rule reading its view freely could hand two correct
  validators different counts. `Anchored` is the condition that rules
  that out: the step must not depend on which view computes it. It needs
  no further hypothesis, because the window a rule measures on is the
  anchor's causal
  history, which BN2 shows every view holding the anchor holds whole and
  restricts identically; the AIMD rule satisfies it by not reading the
  view at all (BN7e). Given that, the `(k+1)`-st count is a function of
  the anchor block and the previous state; the anchor is the least
  committed slot past the threshold in a schedule both validators share;
  and the verdicts of the range are agreed by the base rule's own
  agreement theorem. So two validators agree on every configuration and
  every verdict, with no synchrony or fairness hypothesis (BN3).
- **Liveness is the existence of the configuration sequence.** Each
  range closes because the base rule decides every slot of a fixed
  schedule on any view caught up to the horizon; the next anchor exists
  because committed slots recur; the sequence is built by recursion on
  `k` (BN8). What the arc consumes from the base is exactly the paper's
  A4, stated as a clause on a schedule (§7).
- **A4 is not automatic under multiple leaders.** With the paper's
  own rotation, `GetLeader(r + l)`, and `m ≥ 2` leaders, the run
  fairness the development's liveness route consumes (`FairRunOn`,
  report §5) fails at `n = 4`, `f = 1`: no three consecutive rounds are
  ever fully correct-led. Liveness holds anyway, by a different descent
  in which only the *first* slot of each round matters (§8). Discharging
  A4 for the paper's schedule is Phase 4, and is the arc's one piece of
  new base-protocol theory.

The arc is generic over the base protocol through an explicit interface
(§2), instantiated four times (Phase 5, and §15's later Orcaella
addition); the paper's Lean appendix can then say, accurately, that
everything is proved from A1–A4 and not from Mysticeti.

### 0.1 Correspondence with the paper

| paper | this arc |
| :-- | :-- |
| A1 rounds and slots; `GetLeader(r + l)` | `Sched m`, `elect` (§3) |
| A2 causal completeness | `View.complete`, P4; the window as a view (§4) |
| A3 direct decision predicate | `BaseRule.DirectCommitIn` (§2) |
| A4 base safety | `BaseRule.agree` (§2) |
| A4 base liveness | `BaseRule.LiveOn S` (§7), discharged in Phases 4–5 |
| Algorithm 2 (`TryCommit`, `TryDecide`) | `PartialRun` (§5) |
| Algorithm 3 (`UpdateLeaders`, `GetSubDag`, `CountDirectCommits`, `ExpectedCommits`) | `window`, `observed`, `expected`, `Aimd.update` (§4) |
| Window Agreement | BN2 |
| Leader-Count Agreement | BN3 |
| Safety (Agreement, Integrity, Total Order) | BN3, BN5 |
| Configuration Progress; Liveness | BN8 |
| Lean appendix: assumed vs. proved, witnesses | §9, §11 |

## 1. The mechanism, in this development's vocabulary

A *configuration* is a pair `(start, m)`: the round after which it is in
force and its leader count. Configurations are indexed `k = 0, 1, …`;
`C_0 = (0, 1)` (Algorithm 2 initialises `lastRound ← 0` and, per the
paper's Algorithm 1, one leader). The `(k+1)`-st anchor `A_{k+1}` is the
least slot of `Sched m_k`, in slot order, that is committed and whose
round exceeds `start_k + Interval`; then `start_{k+1}` is `A_{k+1}`'s
round and `m_{k+1} = update(m_k, backoff_k, U, A_{k+1})`.

The *range* of configuration `k` is the set of slots of `Sched m_k` at
rounds in `(start_k, start_{k+1}]`. Every slot of the range is decided by
the base relation against `Sched m_k`. The slots of round `start_{k+1}`
*after* the anchor belong to range `k`: the paper's text says the new
count applies to rounds after the anchor, and this arc follows the text
(§12, D4; the pseudocode is ambiguous there and a comment in the
manuscript records it).

The *ledger* is the concatenation over `k` of the committed blocks of
range `k`, in slot order of `Sched m_k`.

## 2. The base-protocol interface

The arc never counts anything. What it needs of a base protocol is a
decision relation parametric in the schedule, agreement across views for
a fixed schedule, and — for the measurement — the direct-commit
predicate. The four protocols differ in their universe and view types
(Nemo has `Nemo.Universe` and `Nemo.View`; the Byzantine rules share
`BlockUniverse` and `View`; Orcaella's universe is the subtype bundling
`HonestNoEquiv`) and in their fault classes — Mysticeti needs
`Faults`, Odontoceti `Faults5` and a linear order on ids, Orcaella
`HybridFaults` with an admissible indirect threshold, Nemo's safety
none at all — so the interface bundles the types and puts each rule's
fault class on its instantiation, never on the interface
(`Model/Rule.lean`):

```lean
structure BaseRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type) where
  Universe : Type
  View : Universe → Type
  block : Universe → BlockId → Block Validator BlockId Payload
  ids : Universe → Finset BlockId
  viewIds : ∀ {U : Universe}, View U → Finset BlockId
  full : ∀ U : Universe, View U
  historyView : ∀ (U : Universe) (A : BlockId), A ∈ ids U → View U
  waveLength : ℕ
  DirectCommitIn : ∀ {U : Universe}, View U → BlockId → ℕ → Prop
  decDirect : ∀ {U : Universe} (V : View U) (L : BlockId) (r : ℕ),
    Decidable (DirectCommitIn V L r)
  Decided : Slots Validator → ∀ {U : Universe}, View U → ℕ → Option BlockId → Prop

structure BaseRule.Laws (R : BaseRule Validator BlockId Payload) : Prop where
  view_subset : ∀ {U : R.Universe} (V : R.View U), R.viewIds V ⊆ R.ids U
  view_complete : ∀ {U : R.Universe} (V : R.View U),
    ∀ i ∈ R.viewIds V, ∀ j ∈ (R.block U i).refs, j ∈ R.viewIds V
  full_ids : ∀ U, R.viewIds (R.full U) = R.ids U
  historyView_ids : ∀ U A (hA : A ∈ R.ids U),
    R.viewIds (R.historyView U A hA) = historyFrom (R.block U) A
  agree : ∀ (S : Slots Validator) {U : R.Universe} (V₁ V₂ : R.View U) (k : ℕ)
    (v₁ v₂ : Option BlockId), R.Decided S V₁ k v₁ → R.Decided S V₂ k v₂ → v₁ = v₂
  decided_of_directCommitIn : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U)
    (k : ℕ) (L : BlockId), R.IsLeaderBlock S U k L →
    R.DirectCommitIn V L (S.slotRound k) → R.Decided S V k (some L)
```

The interface is split into **data** and **laws**, so that the data —
what the rule *is* — is proof-free and audited, and the laws — what it
must satisfy — are a proposition each instantiation is proved to meet
as a result of the house shape: `Mysticeti/Statement.lean` defines the
data and states `Laws mysticeti`, `Mysticeti/Proof.lean` proves it, and
Phase 5 adds the same pair for Odontoceti and Nemo. Every generic
theorem takes `(hR : R.Laws)`. The laws render the paper's
assumptions: `view_subset` and `view_complete` are A2 (a validator
holds a block only with its whole causal history), `DirectCommitIn` and
`waveLength` are A3, `agree` is the safety half of A4; the liveness
half is §7. `BaseRule.IsLeaderBlock
R S U k L` is the generic candidate predicate — the right round, the
right author — over the interface's `block` and `ids`; it is the
conjunction every rule of the development states, so each
instantiation's `Decided.directCommit` accepts it by unfolding.

Three shapes are fixed by the instantiations rather than by taste. The
schedule is an *explicit* argument of `Decided`, `R.Decided S V k v`: an
instance binder in a structure field is never referenced by the field's
type and trips the unused-variable linter, and an anonymous one cannot
be passed by name. Types live in `Type`, not `Type*`: every concrete
universe of the development is in `Type`, and a universe-polymorphic
field would complicate every statement for no instance (§12, D1). And
there is no view-monotonicity law: Odontoceti has no `decided_mono`,
safety does not need one, and the local form of liveness that would is
deferred with the liveness fields to Phase 3's extension of this
structure, so that the frozen file is not reopened.

One construction the data needs cannot be proof-free: the anchor's
history as a `View`, whose closure the core's `View` type requires as a
field. It lives in `Helpers/Mysticeti.lean` (`historyViewOf`), the one
helper a `Statement.lean` of this arc imports, and it is not trusted:
the law `historyView_ids` pins its ids to the history whatever the
helper builds.

`decided_of_directCommitIn` is what makes the window count well defined:
two directly committed candidates of one slot on one view are one block
by `agree`, so the paper's count over leader *blocks* — several upon
equivocation — equals a count over *slots* (§4).

## 3. Schedules

The paper's slot `(r, l)`, for `l` below the count, is led by
`GetLeader(r + l)`; the leader function does not depend on the count, and
only *which slots exist* changes across configurations. In this
development a schedule with `m` leaders in every pipelined round is
`Slots.uniform 1 m elect`, slot `κ` at round `κ / m` with offset `κ % m`
(`pipelining-and-multi-leader.md` §3.2):

```lean
/-- `m` leaders in every round, slot `(r, l)` led by `getLeader (r + l)`. -/
@[reducible] def Sched (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) : Slots Validator :=
  Slots.uniform 1 m Nat.one_pos hm (fun κ => getLeader (κ / m + κ % m)) (hk m hm hmax)
```

`Slots.keyed` asks that the `m` leaders of a round be distinct
validators. `Keyed getLeader w` states that obligation of the leader
function at every count up to `w`, in the form `Slots.uniform`
consumes — so `Sched` passes it through and `Model/Schedule.lean` holds
no proof. The readable form, injectivity of `getLeader` on every window
of `w` consecutive rounds (`WindowInjective`), implies it
(`Helpers/Schedule.lean`, `keyed_of_windowInjective`), and round-robin
`getLeader r = r % n` has it for `w ≤ n` (`roundRobin_keyed`); it is the
arc's witness schedule (BN1). `getLeader` is abstract (D8).

`Sched` is a `def`, not an instance, and every use passes
`(S := Sched … m …)`: the arc's whole point is several `Slots` instances
on one validator type.

## 4. The window and the update

**The window.** `GetSubDag` is the anchor's causal history restricted to
rounds `[r − Interval, r]`. In this development the window view is the
anchor's whole history, `historyFrom (block U) A`, supplied by the
instantiation as `historyView` — for `BlockUniverse` it is `history U A`
with closure through `Reaches`, as `viewAt` builds views — and the round
bound is applied by the count, not by the view (D9). Both readings give
the same count, since the direct predicate at round `r'` reads rounds
`[r', r' + w)` only (A3).

**The measurement.** For each round `r'` of `[r − Interval, r]` and each
offset `l < m`, the slot `(r', l)` of `Sched m` — slot `m · r' + l` —
counts if some candidate of it is directly committed on the window view
(`Model/Window.lean`):

```lean
def BaseRule.SlotDirect (R : BaseRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (V : R.View U) (κ : ℕ) : Prop :=
  ∃ L ∈ R.ids U, R.IsLeaderBlock S U κ L ∧ R.DirectCommitIn V L (S.slotRound κ)

def observed (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (U : R.Universe) (A : BlockId) (m : ℕ) (hm : 0 < m) (hmax : m ≤ P.maxLeaders) : ℕ :=
  if hA : A ∈ R.ids U then
    ((Finset.range (P.interval + 1) ×ˢ Finset.range m).filter (fun dl : ℕ × ℕ =>
      dl.1 ≤ (R.block U A).round ∧
      R.SlotDirect (Sched getLeader hk m hm hmax) U (R.historyView U A hA)
        (m * ((R.block U A).round - dl.1) + dl.2))).card
  else 0

def expected (R : BaseRule Validator BlockId Payload) (P : Params) (m : ℕ) : ℕ :=
  (P.interval - R.waveLength + 1) * m
```

The paper counts leader blocks; by §2 the two counts agree, and the arc
counts slots because that is what `expected` counts. The clause
`dl.1 ≤ round` keeps truncated subtraction from counting round `0` once
per excess `d`; inside a run the anchor's round exceeds the interval and
the clause is vacuous. The wave length is the rule's (`R.waveLength`),
not a parameter of the mechanism.

**The rule.** `threshold` is a rational in the paper and an integer
comparison in the implementation; the arc takes an integer pair
`(num, den)` and the test `den * observed ≥ num * expected` (D3). The
paper's `0.96` is `(96, 100)`.

```lean
structure Params where
  interval waveLength maxLeaders num den : ℕ
  interval_pos : 0 < interval
  max_pos : 0 < maxLeaders

/-- Additive increase, multiplicative decrease. -/
def Aimd.update (P : Params) (m backoff : ℕ) (healthy : Bool) : ℕ × ℕ :=
  if healthy then (min (m + 1) P.maxLeaders, 0)
  else (max (m - 2 ^ backoff) 1, backoff + 1)

/-- The paper's `UpdateLeaders`, as a function of the universe and the anchor. -/
def Aimd.rule (R) (P) : UpdateRule R :=
  fun m backoff U A =>
    Aimd.update P m backoff (decide (P.den * observed R P U A m ≥ P.num * expected P m))

/-- Any deterministic function of the state, the universe and the anchor. -/
abbrev UpdateRule (R : BaseRule …) := ℕ → ℕ → R.Universe → BlockId → ℕ × ℕ
```

Safety (§6) is stated for `UpdateRule`; the AIMD facts (BN7) are stated
for `Aimd.rule`.

**A note on `expected`.** The window has `Interval + 1` rounds. A slot
at round `r'` is decidable within it when `r' + w − 1 ≤ r`, which is
`Interval − w + 2` rounds, one more than the paper's formula. On the
other hand the anchor's own round contributes one block to the window,
so at round `r − w + 1` a direct commit needs a quorum of certifiers
among a single block, and the count there is zero whenever the quorum
exceeds one; the decidable rounds are then `Interval − w + 1`, the
paper's number, for a reason the paper does not give. **Settled on
data** (Phase 1, `LeanDagTest/Barnacle/Model.lean`): on `U7` with
the anchor at round `5`, the slot `(3, 1)` two rounds below it — block
`12` — has three certifiers on the full view and is directly committed
there, and has exactly one on the window, the anchor itself, and is
not; rounds `r − 3` and `r − 4` score. The paper's number, for the
second reason (§11, F2). The bound `observed ≤ expected` is protocol-specific
— it needs A3's locality and a quorum above one — and is proved for
Mysticeti in Phase 5 rather than assumed of the interface.

## 5. The run

What a validator holds mid-execution is a *partial run* closed up to a
configuration height; the object safety and liveness are stated on.

```lean
structure PartialRun (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R) (U : R.Universe) (V : R.View U) (K : ℕ) where
  start : ℕ → ℕ
  count : ℕ → ℕ
  backoff : ℕ → ℕ
  anchor : ℕ → ℕ
  vdct : ℕ → ℕ → Option BlockId
  init : start 0 = 0 ∧ count 0 = 1 ∧ backoff 0 = 0
  count_pos : ∀ k, 0 < count k
  count_le : ∀ k, count k ≤ P.maxLeaders
  closed : ∀ k, k < K → ∀ κ, start k < κ / count k → κ / count k ≤ start (k + 1) →
    R.Decided (Sched getLeader hk (count k) (count_pos k) (count_le k)) V κ (vdct k κ)
  anchor_commits : ∀ k, k < K →
    (∃ A, vdct k (anchor k) = some A) ∧ start k + P.interval < anchor k / count k
  anchor_least : ∀ k, k < K → ∀ κ, κ < anchor k →
    start k + P.interval < κ / count k → vdct k κ = none
  start_succ : ∀ k, k < K → start (k + 1) = anchor k / count k
  update : ∀ k, k < K → ∀ A, vdct k (anchor k) = some A →
    (count (k + 1), backoff (k + 1)) = upd (count k) (backoff k) U A
```

`start k` is the round after which configuration `k` is in force,
`anchor k` the slot index in `Sched (count k)` of the anchor that closes
it, and `vdct k κ` the verdict of slot `κ` of `Sched (count k)`. The
round clauses are written as `κ / count k`, which is `Sched`'s
`slotRound`, so that only `closed` names the instance. `start 0 = 0`
is Algorithm 2's `lastRound ← 0`: round `0` lies in no range, as in the
algorithm, whose first decision walk starts at round `1`.

**There is no total run.** Every configuration commits an anchor, the
`candidates` law places it at its own round, `start` grows strictly, and
a universe holds finitely many blocks: a run with a configuration for
every `k` would inject `ℕ` into `ids U`. The Phase 2 review proved this
(`configRun_empty`, on the Phase 2 draft's total structure), and the
draft's `ConfigRun`, with the results stated over it, was withdrawn as
vacuous. The paper's *sequence of configurations* is therefore what
every prefix of it agrees on: `PartialRun` at height `K` closes `K`
ranges in full — through the end of each anchor's round, so that each
range's ledger is defined — and determines configuration `K`; safety
is agreement of prefixes of any two heights (BN3), and liveness will be
that prefixes of every height exist (BN8).

`count_pos` and `count_le` are clauses of the run rather than
consequences of the rule because the run is stated for an arbitrary
`UpdateRule`; for `Aimd.rule` they are theorems (BN7) and the clauses
are discharged.

Slots are numbered per configuration (D2): `vdct k` is a verdict
function on `Sched (count k)`, which is the object every base theorem
speaks about, and the ledger of the range is `ledgerOf (vdct k)` over
the range's slot interval, `(List.range' lo (hi − lo)).filterMap`; the
core's `commitSeq` has no offset and is reached by a shift. A global
`(round, offset)` indexing was considered and rejected: it would need a
fourth schedule structure the base development does not have, and every
derivation would be translated into it and back.

## 6. Safety

**BN1 (schedules).** `Sched m` is a lawful `Slots` instance for every
`0 < m ≤ maxLeaders`; round-robin is window-injective at
`maxLeaders ≤ n`. From `Slots.uniform`; nothing new.

**BN2 (the window is agreed).** Any two views holding the anchor hold
its whole history (`View.mem_of_reaches`, T6a), so the window view, the
count and the update read the same data on every view. In this model
the universe is the shared ground truth and the statement is that the
measurement is a function of `(U, A)` alone — which is the paper's
Window Agreement lemma, with the paper's Claims 1–2 being P4 and view
convergence (report §5).

**BN3 (partial runs agree).** Two partial runs over one universe —
whatever views, whatever heights — agree on `start`, `count`,
`backoff`, `anchor` and on every verdict of their common ranges:

```lean
theorem partialRun_agree {V₁ V₂ : R.View U} {K₁ K₂ : ℕ}
    (R₁ : PartialRun R P upd U V₁ K₁) (R₂ : PartialRun R P upd U V₂ K₂) :
    ∀ k, k ≤ min K₁ K₂ →
      R₁.start k = R₂.start k ∧ R₁.count k = R₂.count k ∧ R₁.backoff k = R₂.backoff k ∧
      (k < min K₁ K₂ → R₁.anchor k = R₂.anchor k ∧
        ∀ κ, R₁.start k < (Sched (R₁.count k)).slotRound κ → κ ≤ R₁.anchor k →
          R₁.vdct k κ = R₂.vdct k κ)
```

By induction on `k`. The configurations agree below `k` by hypothesis,
so both runs' range-`k` verdicts are derivations against one schedule
and agree by `R.agree`; the anchor is the least committed slot past one
threshold in one verdict function, so the anchors agree; the update is
one function of one universe, one anchor and one state. No synchrony, no
fairness, no clause on `upd`.

**BN4** — withdrawn: there is no total run (§5), and BN3 at equal
heights is the form there is.

**BN5 (the ledger).** The concatenated committed sequences of two runs
are equal on every range both have closed, hence as one list to every
height both reach; the ledger to a lower height is a prefix of the
ledger to a higher one; and a block appears at most once — `Slots.keyed`
within a range through the `candidates` law, distinct rounds across
ranges. This is the paper's Agreement, Total Order and Integrity in the
form the development states them (M7, `outputAt_unique`).

**BN6 (conservativity).** Under the constant rule
`fun m b _ _ => (m, b)` every configuration a run determines — `k ≤ K`,
the height; above it a run holds no data — has the initial count and
back-off, and a run's verdicts are `Decided` verdicts of `Sched 1`: the
arc collapses onto the base development.

**BN7 (the AIMD rule).** `Aimd.update` keeps the count in
`[1, maxLeaders]`; an unhealthy window strictly decreases a count above
one; a healthy one increases a count below the maximum by one; `backoff`
resets on a healthy window. For Mysticeti (Phase 5): `observed ≤
expected`, from A3's locality and `quorumCard ≥ 2`, in whichever of the
two forms §4 turns out to hold on data.

## 7. Liveness, interface half

The paper's A4 liveness is "after GST, honest validators commit new
leaders infinitely often". In this development liveness is structural —
a condition on the DAG, no clock — and every statement carries a
horizon, because a universe is finite (§5). The interface adds one
field (D10): `LiveRule extends BaseRule` with `Good : Universe → ℕ → ℕ →
Prop`, the rule's own notion of a DAG good from a round to a horizon —
for the rules of this development, synchronised over a reliable quorum
and populated (`∃ T ⊆ Correct, quorumCard ≤ T.card ∧ SynchronisedOn U T
Rnd ∧ ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn U T r`), defined at each
instantiation where its predicates are checked. The mechanism never
inspects it. A4 is then a clause on a schedule, with a commit gap `c`
(D11) so that each configuration's anchor is found before the horizon
(`Model/Live.lean`):

```lean
def LiveRule.LiveOn (R : LiveRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) :
    Prop :=
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N →
      R.toBaseRule.CoversUpto U V N →
    (∀ κ, Rnd ≤ S.slotRound κ → S.slotRound κ + c + R.waveLength ≤ N →
      ∃ v, R.Decided S V κ v) ∧
    (∀ r, Rnd ≤ r → r + c + R.waveLength ≤ N →
      ∃ κ, r ≤ S.slotRound κ ∧ S.slotRound κ ≤ r + c ∧
        ∃ L, R.Decided S V κ (some L))
```

`CoversUpto U V N` (`Model/Rule.lean`) is the condition on the view: it
holds every block of `U` at a round up to `N`, which is what a validator
that has received everything up to the horizon holds. Still no
view-monotonicity field — the covering condition does that work, and
Odontoceti has none. `coversUpto_full` (`Helpers/Cover.lean`) gives the
condition for `R.full U` at every `N`, so the whole-universe reading is
the special case. Extending a run by a configuration needs the update
rule to keep the count in range, `UpdBounded P upd` (D13), which BN7a
supplies for the AIMD rule.

**BN8a (progress).** The paper's Configuration Progress, at the run's
own count (D12): a run whose current configuration's range lies at or
after the synchrony round, whose schedule is live with gap `c`, on a DAG
good to a horizon leaving room for the threshold, the gap and one wave,
extends by one configuration:

```lean
  ∀ (U : R.Universe) (V : R.View U) (Rnd N K : ℕ),
    R.toBaseRule.CoversUpto U V N →
    ∀ (Rn : PartialRun R.toBaseRule P getLeader hk upd U V K),
    R.LiveOn (Sched getLeader hk (Rn.count K) (Rn.count_pos K) (Rn.count_le K)) c →
    R.Good U Rnd N → Rnd ≤ Rn.start K + 1 →
    Rn.start K + P.interval + 1 + 2 * c + R.waveLength ≤ N →
    Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V (K + 1))
```

The new range's slots lie at rounds above `start K`, hence at or after
`Rnd`, and at most `start K + interval + 1 + c`, hence one wave under
`N`: the first clause decides them. The second clause at `r := start K
+ interval + 1` yields a committed slot past the threshold within `c`;
the anchor is the least such slot, `anchor_least` its minimality; the
safety law `agree` identifies the verdict chosen for the anchor's slot
with the commit the clause provides — safety is consumed inside
liveness. The rule gives the next state, in range by `UpdBounded`.

**BN8b (every height).** From a synchrony round at genesis and the
clause at every count, a run of every height exists under the horizon
its height needs, `horizon P R c K := K · (interval + 1 + c) + c +
waveLength`: BN8a iterated, the induction carrying `start K ≤ K ·
(interval + 1 + c)`. The paper's Liveness, in the prefix form.

Both statements are on any view caught up to the horizon, so a run is
what a validator holding everything up to `N` reaches, not merely what
exists in the universe (D6). Under eventual DAG synchrony
(`liveness.md` §4.2: whatever one correct validator holds, all
eventually hold, whoever authored it) every correct validator's view
satisfies the covering condition, so the statements cover every correct
validator. What remains structural is the time: the time-indexed form,
where a validator decides on its own view at an explicit time and the
horizon is a function of when it looks, needs the pacing structures of
report §5 and is not attempted.

## 8. Liveness, the descent under multiple leaders

**The problem.** The base liveness route decides everything below a run
of `c` consecutive committed slots spanning the eligibility gap
(`decided_below_of_committed_run`, L10), and the run comes from
`FairRunOn T c`: `c` consecutive `T`-led slots, arbitrarily far out.
With `m` leaders per round the run must cover three full rounds,
`c = 3m`, all of whose `3m` leaders are in `T`. Under
`getLeader (r + l) = (r + l) % n` the leaders of three consecutive rounds
are `m + 2` consecutive residues, and at `n = 4`, `f = 1`, `m = 2` these
are all four validators: no run ever exists. The witness schedule of the
identity-adapting arc, `waveRobin`, sidesteps this by holding a leader
for a wave; the paper's schedule does not, and the paper's evaluation
runs `m` up to five.

**The descent.** Only the *head* of a round — its slot at offset `0` —
matters. For a slot `σ` at round `ρ'`, the eligible anchors begin at
round `ρ' + w` (`w` the wave length, which is the eligibility gap of
every rule of this development), and the head of that round precedes
every other eligible slot. If the head is committed then it is the
least eligible committed slot, the set of eligible intermediates is
empty, and `σ` is decided by the indirect rule outright, whatever its
own direct evidence. Two facts of the base protocol carry this, stated
as a second law structure so that `Laws` stays as frozen
(`Model/Heads.lean`, D14):

```lean
structure LiveRule.Descent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  goodLeaders : ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ (S : Slots Validator) (V : R.View U) (κ : ℕ), R.toBaseRule.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
        S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L)
  indirect : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    S.slotRound i + R.waveLength ≤ S.slotRound j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → S.slotRound i + R.waveLength ≤ S.slotRound i' →
      R.Decided S V i' none) →
    ∃ v, R.Decided S V i v
```

`goodLeaders` is the paper's A4 — after GST an honest leader's slot is
decided directly — with the good set `T` missing at most `slack`
validators; `indirect` is A3's indirect rule. For Mysticeti the first
is L4 at `slack = f`, through `directCommit_of_leader_mem` rather than
`decided_of_leader_mem`: the latter concludes on the full view, so the
verdict is rebuilt inside `V` instead, which works because the
certificates sit a wave below the horizon and a covering view therefore
holds them (`certificates ∩ V.ids = certificates`; the supporter sets
of the two-round rules are the same shape). The second is the two
indirect constructors of `Decided`, which were view-parametric already.

```lean
def HeadsRun (getLeader : ℕ → Validator) (T : Finset Validator) (g c₀ : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ρ + g ≤ r + c₀ ∧ ∀ i, i < g → getLeader (ρ + i) ∈ T
```

Under `Sched m` the head of round `ρ` is slot `m · ρ`, led by
`getLeader ρ` whatever the count: one clause serves every configuration
(D16).

**BN9a (the stretch descent).** The base descent, weakened: a stretch of
consecutive slots all *decided*, whose top slot is committed, and whose
top lies a full wave above everything below the stretch, decides
everything below it. From `indirect` alone; the intermediates the
minimality argument meets are decided and not committed, hence skipped.

**BN9b (heads decide).** If the heads of rounds `ρ, …, ρ + w − 1` are
`T`-led, `Rnd ≤ ρ` and `ρ + 2w ≤ N + 1`, then every slot at a round `r`
with `r < ρ ≤ r + w` is decided on any view caught up to `N` and the
head of `ρ` is committed: each such slot's wave-up head is one of the
`T`-led heads, committed directly, with no eligible slot between (D18).

**BN9c (`LiveOn` from `HeadsRun`).** A run of heads with gap `c₀` for
every set missing at most `slack` validators gives
`R.LiveOn (Sched getLeader hk m hm hmax) c₀` at every count: clause 1
by `HeadsRun` at `r + 1`, BN9b, then BN9a on the stretch from the first
slot of `ρ' − w` to the head of `ρ'`; clause 2 by `HeadsRun` at `r`.

**BN9d (round-robin has runs of heads).** For every `T` on `Fin n` with
`n ≤ T.card + slack` and `g · slack + 1 ≤ n`,
`HeadsRun (roundRobin n hn) T g (n + g − 1)`: if no window of `g`
consecutive residues starting in a cycle lay inside `T`, choosing for
each start a residue outside `T` within its window would inject `Fin n`
into `Fin g × Tᶜ`, so `n ≤ g · slack < n` (D17). This is the
arc-counting argument the `FairRunOn` docstring records and the
wave-aligned schedule was introduced to avoid; it is needed here because
the paper's schedule is per-round rotation, and it is sharp: Mysticeti's
committee bound `3f + 1 ≤ n` is exactly `g · slack + 1 ≤ n` at `g = 3`,
`slack = f`.

**BN9e (round-robin is live).** A live rule with descent laws at `slack`
on `n ≥ w · slack + 1` validators is live under round-robin at every
count, with gap `n + w − 1`.

**Mysticeti (`MysticetiLive/`).** `mysticetiLive` is Mysticeti with the
base development's own liveness interface as `Good` — a correct quorum
synchronised from `Rnd` and populating the rounds to `N` — and the
result is its descent laws at slack `f` together with
`LiveOn (Sched (roundRobin n hn) hk m hm hmax) (n + 2)` at every count:
the paper's A4 for Mysticeti under its own schedule, assumed there,
proved here (§11, F3).

**The two-round rules (`Odontoceti/`, `Nemo/`, Phase 5).** Each is a
`BaseRule` with its laws, a `LiveRule` with its descent laws, and live
under round-robin at every count with gap `n + 1`. Odontoceti's
`indirect` commits the *least* candidate with a thick link
(`Finset.min'` over the candidates), which is the canonicity clause of
its indirect rule; its slack is `f`, as Mysticeti's, its `Good`
demanding a quorum of `n − f`. Nemo's `Good` demands a synchronised
*majority* of the live validators, as its own L4 does, and a majority
misses `n − majority` validators — so its slack is `n − majority`, not
`f` — `n − majority = (n − 1) / 2`, the largest crash bound admissible
at `n`, equal to `f` exactly at `n = 2f + 1` and `n = 2f + 2`. As a
descent law this is *weaker* than slack `f` would be, and the strength
is in the weaker `Good`: the mechanism is live over any synchronised
majority. The pigeonhole's bound `2 · (n − majority) + 1 ≤ n` holds at
every `n`, so the crash bound is consumed nowhere in the proofs; it is
what makes `Good` satisfiable, the live set being a majority. The
witness `Majority.lean` attacks the choice: a bare majority strictly
inside the live set, an adversarial live validator outside it, and the
theorem applied with both clauses non-vacuous and its verdicts pinned;
the slack is exact at `n = 3`. Nemo's laws consume no fault class at
all.

## 9. Witnesses (`LeanDagTest/Barnacle/`)

Every definition is exercised by `decide` before anything is proved
from it, and a run whose count moves is exhibited before agreement is
stated.

- **The window and the count.** A four-validator universe at `f = 1`,
  `Interval` small (three or four rounds), with an anchor whose history
  the count reads: `observed` and `expected` computed by `decide`, which
  settles §4's question about the top rounds of the window on data;
  `Aimd.update` at both branches; the count reaching `maxLeaders` and
  the floor.
- **A run whose count moves.** The same universe extended: configuration
  `0` at count `1`, the first anchor healthy, configuration `1` at count
  `2`; a slot `(r, 1)` that exists in `Sched 2` and not in `Sched 1`,
  with a verdict; two views' partial runs constructed and shown
  identical by BN3. Then the unhealthy branch: a window with a stalled
  slot and the count returning to `1`.
- **The heads descent.** A DAG with a Byzantine head undecided directly
  and decided by the head three rounds above; `HeadsRun` for round-robin
  at `n = 4` by `decide` over one cycle.
- **The four instantiations.** `BaseRule` for Mysticeti, Odontoceti
  and Nemo, each on its existing test model (`U7`, the Odontoceti model,
  the three-validator Nemo model), with the window count computed under
  each rule; Orcaella's witnesses (§15) live in their own three files.

## 10. Layout and discipline

The arc adopts the statement/proof partition of the Mahi-Mahi and Black
Marlin arcs (`mahi-mahi.md` §9), and is the third to do so;
`Barnacle` is added to `ARCS` in `scripts/check-arc-holes.py` in
Phase 1.

```
LeanDag/Barnacle/
  Model/         definitions only — no theorem and no proof term:
                 Rule (§2, §7), Schedule (§3), Window (§4), Run (§5), Heads (§8)
  Helpers/       lemma and construction infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ only; `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
  <Rule>/Statement.lean     the rule's `BaseRule` data and `Statement := Laws …`;
                            imports Model/ and the one helper the data needs
  <Rule>/Proof.lean         the laws, proved; unaudited
LeanDagTest/Barnacle/  witness models; audited
```

The bar for `Model/` is the Hydrozoan formalisation's: definitions
that carry no proof at all, so that a reviewer reads meaning and never
argument. An obligation a definition would otherwise discharge inline
is stated as a definition in the form its consumer needs (`Keyed`) and
discharged in `Helpers/`.

Results: `Window` (BN2), `Agreement` (BN3), `Ledger` (BN5),
`Conservativity` (BN6), `Aimd` (BN7), `Liveness` (BN8), `Heads`
(BN9a–d); and per rule, `Mysticeti`, `Odontoceti`, `Nemo` — the
rule's data and the proof that it satisfies `Laws` (BN10). BN1 is
`Sched` with `Keyed`.

**The freeze protocol**, as in the two arcs before: for each phase,
statements are written, reviewed, agreed, and then frozen — no edit to
`Model/` or a `Statement.lean` without notice to the author, however
small; a proof that needs a statement changed stops and raises the
need. Proofs are then written until they verify, the hole checker and
`#print axioms` are clean, and the phase is committed.

**Relation to the core.** Read-only: `Block`, `BlockDag`, `Causality`,
`History`, `Validators`, `Schedule`, `Mysticeti`, `Liveness`,
`Odontoceti/`, `Nemo/`. BN9a is a weakening of
`decided_below_of_committed_run`; it is proved in the arc's `Helpers/`,
not by editing the core, and reported as a candidate for the core if
the base development wants it. If a phase finds it needs a change to
the core, that is a finding, not a refactor.

**Relation to the identity-adapting arc.** `LeanDag/Adaptive/` is not
consumed. The paper says the two mechanisms are orthogonal and
composable; their composition — a policy that chooses both who leads and
how many — is a later question, and §13 records it.

## 11. Findings for the paper

Each is recorded here with its status and reaches the manuscript as an
author comment when confirmed.

- **F1 — the anchor's round.** Algorithm 2 returns at the anchor and
  restarts from `r_committed + 1`; whether the slots of the anchor's
  round after the anchor are committed at all, and under which count,
  is not determined by the pseudocode. The arc follows the text
  (previous count through the anchor's round). *In the manuscript*
  (`sections/protocol.tex`).
- **F2 — `expected`.** The window's decidable rounds are
  `Interval − w + 2` by the stated reason and `Interval − w + 1` by
  another (§4). *Settled in Phase 1: the paper's number, for the other
  reason — round `r − 2`'s only certifier inside the window is the
  anchor itself.*
- **F3 — A4 under multiple leaders.** Run fairness fails for the paper's
  schedule at `m ≥ 2` and small `n`; liveness holds by the heads
  descent, and the paper's A4 is a theorem for its own schedule:
  Mysticeti under round-robin is live at every count with gap `n + 2`
  (`MysticetiLive.holds`). *Proved in Phase 4; for the Lean appendix.*
- **F9 — the liveness clause needs a margin.** A slot the direct rule
  does not settle is decided by a committed anchor a wave above it,
  whose own wave must fit under the horizon; so no rule decides every
  slot up to `N − w`, and the clause's first half carries the gap `c`
  as a margin above the slot. The Phase 3 statement lacked it and was
  unsatisfiable under Mysticeti's natural `Good` for every `c`; found
  and repaired in Phase 4. *Phase 4.*
- **F4 — A5 is unnecessary.** The proof outline's "any leader committed
  after `r_i` has the anchor in its causal history" is not consumed:
  agreement is the base agreement theorem under one fixed schedule plus
  determinism of the update, and the lagging validator is view
  convergence. *Phase 2.*
- **F5 — safety for any update rule.** The paper's Leader-Count
  Agreement is stated for the AIMD rule; it holds for any deterministic
  rule whose step does not depend on which view computes it
  (`Anchored`) — which is every rule reading only the anchor's window,
  AIMD among them — a stronger and simpler statement for the Lean
  appendix. *Phase 2.*
- **F8 — safety inside liveness.** Configuration Progress consumes
  the agreement law: the verdict the liveness clause chooses for the
  anchor's slot and the commit it provides for it are identified by
  `agree`. The paper's Progress lemma does not say so. *Phase 3.*
- **F7 — no total run.** A finite DAG closes finitely many
  configurations; the paper's sequence of configurations exists only as
  the family of its prefixes, and its safety theorem is agreement of
  prefixes. *Phase 2; for the Lean appendix.*
- **F6 — blocks versus slots.** `CountDirectCommits` iterates over
  leader blocks and could in principle count a slot twice; it cannot,
  by the base agreement theorem (§2). *Phase 2.*

## 12. Decisions for the author

Settled 2026-08-26, each on its recommendation (the first option
below); the Phase 1 sources implement them as written.

- **D1 — the interface's types.** Bundle `Universe`/`View` in `Type`
  inside `BaseRule` (recommended: three instantiations, one statement
  each), or make the arc a functor over a typeclass on universe types.
- **D2 — indexing.** Per-configuration slot numbering, verdicts as
  functions on `Sched (count k)` (recommended), or a global
  `(round, offset)` index.
- **D3 — the threshold.** An integer pair with the test
  `den * observed ≥ num * expected` (recommended; the implementation's
  form), or a `ℚ`.
- **D4 — the anchor's round.** The previous count through the whole of
  the anchor's round (recommended; the text's reading), or the new count
  from the slot after the anchor.
- **D5 — the count.** Over slots, with the block count shown equal
  (recommended), or over blocks as the pseudocode iterates.
- **D6 — local liveness.** BN8 on the full view, local form deferred, or
  the time-indexed local statement in scope from the start. **Revisited**:
  the liveness clause, the descent law and BN8 are now stated over any
  view *caught up to the horizon* (`CoversUpto U V N`), so a run is what a
  validator holding everything up to `N` reaches. The full view satisfies
  the condition at every `N` (`coversUpto_full`), so the earlier reading
  is the special case and nothing downstream weakened. Still not
  attempted is the time-indexed form, where the horizon is a function of
  when the validator looks.
- **D7 — the initial configuration.** `(0, 1)` as Algorithm 1
  initialises (recommended), or an initial count as a parameter.
- **D8 — the leader function.** Abstract `getLeader` with the
  window-injectivity clause, round-robin as witness (recommended), or
  round-robin fixed in the model.
- **D9 — the window view.** The anchor's whole history as the view with
  the round bound in the count (recommended; it is a `View` with no
  closure proof — the history is closed), or the round-restricted
  set with the closure argument of §4.

Settled 2026-08-27 for Phase 3, on the recommendations:

- **D10 — the liveness interface.** One field, `Good : Universe → ℕ → ℕ
  → Prop`, the rule's own notion of a good DAG (recommended), or the
  four predicates `SynchronisedOn`, `PopulatedOn`, `Reliable`, `quorum`
  as fields.
- **D11 — the commit gap.** `LiveOn` bounds the recurrence of committed
  slots by a gap `c` (recommended), or leaves it unbounded and states
  liveness without a horizon — which a finite universe cannot inhabit.
- **D12 — progress at the run's own count.** Configuration Progress
  needs `LiveOn` at the current count only, and every height follows by
  induction (recommended), or a single statement under the clause at
  every count.
- **D13 — bounded rules.** Extending a run consumes `UpdBounded`
  (recommended), or the run structure drops its `count_pos`/`count_le`
  clauses and every consumer re-derives them.

Settled 2026-08-27 for Phase 4, on the recommendations:

- **D14 — the descent laws** are a second law structure, `Descent`
  (recommended), or fields of the frozen `Laws`.
- **D15 — the eligibility gap is the wave length**; no separate field.
- **D16 — heads, not runs**: `HeadsRun`, one clause for every count
  (recommended), or a per-count fairness clause.
- **D17 — the pigeonhole at general `n`**, by an injection into
  `Fin g × Tᶜ` (recommended), or witnessed only on small committees.
- **D18 — the gap is `c₀`**: BN9b on the heads themselves and `HeadsRun`
  called one round up (recommended), or `c₀ + w` with the offset form.

## 14. Phases

| phase | deliverable | commit |
| :-- | :-- | :-- |
| 0 | this record | `31ee0da` |
| 1 | `Model/{Rule,Schedule,Window,Run}.lean`; `Mysticeti/`; the witnesses on `U7`, `Uodo`, `U6`; the checker | `80e59bc` |
| 2 | `Window/`, `Agreement/`, `Ledger/`, `Conservativity/`, `Aimd/` (BN2–BN7); `Usun`; F7 | `e99b364` |
| 3 | `Model/Live.lean`, `Progress/` (BN8); the test rule; `Usk`; F8 | `e209281` |
| 4 | `Model/Heads.lean`, `Heads/`, `MysticetiLive/` (BN9, BN10 for Mysticeti); `U44`; F3 proved, F9 | `ebddc72` |
| 5 | `Odontoceti/`, `Nemo/` (BN10); the twin universe; `Majority.lean` | `0856ea1` |
| 6 | this record brought to the final position; report §21; README; the reference pipeline; the paper's Lean appendix | — |

Each phase ran as statements → review → freeze → proofs → witnesses →
a reviewing agent over the witness file → commit; phases 1, 3 and 4
were planned before their statements were written. Two frozen
statements were amended after their phase, each on notice: `LiveOn`'s
first clause gained its margin (F9, Phase 4), and Nemo's slack became
the majority's (Phase 5); a third, the total run, was withdrawn as
uninhabited (F7, Phase 2).

## 13. Out of scope

- **Composition with the identity-adapting arc** — one policy choosing
  who leads and how many. The count-adapting mechanism decides under
  the count in force and the identity-adapting one needs the bounded
  relation; whether one stratification serves both is a separate arc's
  question.
- **Garbage collection.** A joiner reading the window from a truncated
  universe; the analogue of `HorizonStable` (report §16, I5).
- **Non-pipelined base protocols**, where `expected` is divided by the
  wave length; all four instantiated protocols are pipelined.
- **Certified DAGs.** The paper says the measurement applies; the model
  has no certified-DAG base.
- **Validity, for the two Byzantine rules.** BN14: a good author's block
  lies in the causal history of the block a closed configuration's anchor
  commits, so the run delivers it. The route is coverage rather than the
  self-parent edge report §20 uses — no self-parent clause, which this
  interface does not carry; no rotation hypothesis; and the author's own
  slot need never commit. Nemo-Nemo is outstanding: its persistence
  lemmas conclude from a block *exactly* two rounds above where the
  core's conclude from every block at two rounds or more, and closing
  that needs a descent the crash arc does not have. BN14 consumes only
  the law, so the crash rule joins by proving that descent and nothing
  else.

- **The real rule on data.** BN11 discharges the liveness clause, so the
  synthetic test rule is no longer the only way to run BN8 on data:
  `LeanDagTest/Barnacle/Real.lean` gives runs of every height on the
  grown family under the real Mysticeti rule with its real `Good`, at the
  horizon each height costs.

- **Performance (R2).** The paper's evaluation claims are outside the
  formal model, as the paper says. What *is* now inside it is that the
  loop is not inert: BN12 shows `expected` is exactly the count of a
  window whose scoring slots all commit, so a healthy window is read as
  healthy and the rule raises the count. What remains outside is the step
  from a *good DAG* to a healthy window, which needs the anchor's history
  to carry the good validators' blocks below it and is bounded by the
  good set rather than by `expected`.
- **Byzantine bias of the measurement.** The paper notes a Byzantine
  leader can lower the direct rate within a window; that the damage is
  bounded to one interval is a quantitative claim not attempted here.

## 15. Addendum: the fourth instantiation (2026-09-01)

Orcaella — the hybrid two-round rule of `LeanDag/Hybrid/` at
`n ≥ 5·fb + 3·fc + 1` (report §14) — joins the interface as
`Barnacle/Orcaella/`, closing the gap with the paper's Lean section,
which lists four base protocols. The instantiation is the Odontoceti
trio one parameter and one subtype away, with two decisions that carry
the hybrid model's shape rather than mirroring Odontoceti's:

- **The universe bundles `HonestNoEquiv`.** The hybrid model's one
  genuinely new assumption — a crash-prone validator authors at most
  one block per round too — is a hypothesis of every hybrid safety
  theorem, and `BaseRule.Laws.agree` has no slot for it; per §2's
  design, the fault class lives on the instantiation, so the universe
  is `{U : BlockUniverse … // HonestNoEquiv U}`. At `fc = 0` the
  subtype is provably full (`honestNoEquiv_of_fc_zero`,
  `Hybrid/Conservativity.lean`), so the crash-free collapse onto
  Odontoceti loses no universes; `Ubad`
  (`LeanDagTest/Barnacle/Orcaella.lean`) shows the clause bites as
  soon as a crash class exists.
- **The indirect threshold is a parameter.** The hybrid indirect rule
  works at any `k` in the admissible interval
  `2·fb + fc + 1 ≤ k ≤ n − 3·fb − 2·fc`, whose nonemptiness *is* the
  committee bound, so `orcaella (k)` and every statement quantify over
  an admissible `k`; the paper's link size is the top end `kRel`.

The statements mirror BN10's shape: the laws at every admissible
threshold, the descent laws at slack `fb + fc` — the only place the
mixed bound enters, through the reliable set being the fully-correct
class at quorum `q = n − fb − fc` — and round-robin liveness at every
leader count with gap `n + 1` (`Orcaella/Statement.lean`, proofs in
`Orcaella/Proof.lean` and `Helpers/Orcaella.lean`).

The witnesses span three files, none of which may import
`LeanDagTest.Model`'s competing `Faults (Fin 4)` instance (each file's
header says so, and instance pins guard the resolution):

- `LeanDagTest/Barnacle/Orcaella.lean` — the subtype formed on
  `Uhyb4`; the window count under a crash (healthy at count one,
  backing off from four); `Good` and the descent law by pigeonhole
  (the reliable set may contain the crashed validator, so the sunny
  Odontoceti script does not transfer); the slack `fb + fc` proved
  exact (`not_descent_zero`); and `Ubad`.
- `LeanDagTest/Barnacle/OrcaellaIndirect.lean` — the indirect rule at
  admissible thresholds, previously witnessed nowhere: `U5`
  (`n = 5, fb = 0, fc = 1`, the first non-singleton interval
  `[2, 3]`), one DAG that commits its split slot at threshold `2` and
  skips it at `3`; and `UhybX` (`n = 9`, `fb = fc = 1`, five rounds),
  the first `Good` at `fb, fc > 0` and the twin-canonicity witness —
  both Byzantine twins pass at the anchor, the least commits.
- `LeanDagTest/Barnacle/OrcaellaLive.lean` — a nine-round crash model
  tall enough for the gap, `RoundRobinLive` applied at counts one and
  two with both clauses non-vacuous and verdicts pinned through
  `agree`.
