# lean-dag — Liveness

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Design notes for the liveness results. Separate from `spec.md` because the
approach is exploratory and because liveness needs modelling primitives the
static development deliberately lacks. Things graduate into `spec.md` once
they settle.

## 1. The original notes

> Traditional proofs of liveness assume some synchrony on a message per
> message basis. Something like after GST messages between honest parties
> arrive within a bound Δ. This is awkward as it requires us to think of the
> mechanics of how the DAG is transmitted in terms of messages.
>
> I would like to make a higher level assumption, which we could call
> **"Eventual DAG synchrony"**. I would state it as: after a Global
> stabilization time (GST), then if a correct validator has a view V1, then
> within a time bound Δ all correct validator views will contain V1 (as a
> subset of their view). Outside GST this sync only happens eventually
> (maybe not within time Δ).
>
> This should allow us to prove a few results:
>
> - After GST, within Δ if a correct validator commits all will commit.
> - From round 0 onwards correct validators have enough (`n−f`) references to
>   previous rounds to build blocks, always.
> - After GST if validators wait to build these blocks they will commit.

## 2. Why the abstraction fits

The assumption is stated in terms of **views**, and `View` is already a
first-class structure in the development: a downward-closed subset of the
universe, sharing `U.block`. So `V₁ ⊆ V₂` is already meaningful, and every
safety result is already view-relative. The assumption composes with what
exists rather than sitting beside it.

It also abstracts the right thing. Nothing in the development cares *how*
blocks propagate, only that they do — and the assumption is realisable by
ordinary gossip, so it cannot be quietly inconsistent.

**But views carry only half of it.** View convergence gives L3 directly: the
common view *is* `View.full` (§4.2). It gives honest-to-honest coverage only
once a **build rule** is added — propagation puts the blocks in hand, and a
timeout long enough to wait for them is what gets them referenced (§4.3, S6).
And since a block's references are fixed at build time, what the argument needs
is what a validator held *at that moment*, which `View` does not record. That
is why `Synchronised` is stated on `refs`, and why the delivery layer indexes
`held` by round — the one place the notes' framing does not reach on its own.

## 3. What must be added

Liveness needs three primitives the static model does not have, and it is
worth being explicit about what kind of thing each is: (a) and (c) are
**protocol behaviour**; (b) is an **outcome** the protocol produces but cannot
name. None of the three is a DAG property.

**(a) Correct validators produce blocks.** `Correct` currently means only
*does not equivocate* — a purely negative condition, satisfied by a validator
that crashes at round 0 and never speaks again. That is deliberate: it is what
lets every safety result hold for crashed validators too. But it makes every
liveness statement vacuous without a positive rule:

> up to a horizon `N`, a correct validator has a round-`(r+1)` block once it
> **holds** round-`r` blocks from `n−f` validators

**"Holds", not "exist".** A validator builds after a timeout, on a quorum
that is in *its own view* — it cannot act on blocks it has never received.
That needs a notion the static model lacks, so rule (a) is stated against
`Delivery.held` (§5). The timeout itself leaves no trace beyond that: with no
clock, waiting longer can only show up as a larger `held`.

This splits into two assumptions of different kinds, which is the point:
`builds` is **protocol** (hold a quorum, build), while `DeliversQuorum` is
**network** (a quorum that exists is eventually held). Both are
**asynchrony-only** — they need eventual delivery, not synchrony, and they are
what makes the pre-GST results go through.

**The horizon is not optional** — see §4.4. Without the bound `r < N` this
rule forces infinitely many distinct blocks into `U.ids`, which is a
`Finset`, so *no universe satisfies it* and every theorem assuming it is
vacuous. That was found by trying to build the witness model.

**(b) Correct blocks cover the correct blocks below them.** Distinct from
(a), and pulling the other way: (a) is a **floor** on production — a validator
must eventually build (`Timing.prompt`) — while (b) is a **delay**, requiring
it not build too early (`Timing.waits`). After GST, every correct block
references every correct block of the round below. Without (b) correct
validators race ahead under perfect synchrony and never vote for the leader,
so nothing commits — which is why the waiting rule is a protocol obligation
and not a performance tweak. This is the
**synchrony** assumption, and §5's `Synchronised` is where it lives — for
now; §9's S4 splits it into an implementable rule and a delivery
assumption. It is not leader-specific: catching the leader's block is *why*
we want it, not what it says.

**This is an outcome, not an instruction.** A validator cannot tell which of
its peers are correct, so "wait for the correct blocks" is not something it
can execute. What it can do is wait on a **timeout** and build with whatever
arrived — and raise that timeout when commits stop arriving. After GST a long
enough timeout delivers every correct block of the round below. The coverage
is what synchrony plus backoff *produces*; the protocol never names it. See
§4.3.

The restriction to correct blocks is likewise not a simplification. A
validator cannot wait for Byzantine blocks, because they may never come.

**(c) Correct leaders recur.** `Slots.leader` is an arbitrary function, so
nothing currently stops a schedule from naming Byzantine validators forever —
and then nothing ever commits, however synchronous the network. Any statement
that commits *recur* needs a fairness condition:

> for every slot `k` there is a slot `k' ≥ k` whose leader lies in `T`

where `T` is the correct quorum L4 counts (S5). Round-robin over the `n`
validators supplies the `T := Correct` case, since at least `n−f` of every
`n` leaders are correct. But the `Slots` class does not require
round-robin, so this has to be assumed separately — and Q4 records that the `∃
k' ≥ k` form gives liveness without giving any *rate*.

## 4. The phases

The three phases the protocol actually passes through, and what each one
supports. This is the part where the abstraction has to be handled carefully:
one of the phases is invisible, and saying so precisely is what
keeps the framing honest.

§4.4 is **not** a fourth phase. It records why `U` is finite and what that
costs — a modelling constraint that cuts across all three.

### 4.1 Before GST — the DAG still grows

Messages are delayed arbitrarily, so correct validators sit at wildly
different rounds: one whose incoming traffic is delayed is stuck at round 0
while others race ahead. Nothing rules that out, and nothing needs to.

Two things still hold.

**L0 needs no assumptions whatever.** Validity alone forces the DAG to be
*dense* below its frontier — see §6. The interesting content is not that the
DAG grows but that it **cannot grow tall and thin**: a single block high up
forces a quorum of authors at every round beneath it.

**L1 needs only asynchrony.** With rule (a) and eventual delivery, every
correct validator eventually has a block at every round up to the horizon
(§4.4). No synchrony.

**Round spread is not a theorem.** That correct validators may be far apart in
round number is a *negative* fact — an absence of any bound — so it belongs in
a test model as an exhibit, not as a statement to prove.

Building that exhibit is **impossible at `f = 1`**, which is itself
informative: with `n = 3f+1 = 4` validators and `|Correct| = 3 = n−f`
exactly, every correct validator is needed for a quorum and none can lag. A
spread exhibit that still commits needs `f ≥ 2`. See S7 — it is S5's combined
budget appearing as a concrete obstruction rather than an inequality.

### 4.2 The transition — invisible to this framing, and that is the honest report

At GST the slow validators hold stale views, receive everything, and burst
forward through the rounds they missed. In wall-clock terms this catch-up is
real and takes time.

**The snapshot cannot see it.** Up to the horizon every correct validator has
a block at every round (L1). The only question the snapshot can ask of a block
is *whether it references every correct block of the round below*, and that is
a property of the round it was built at — not of when it was built.

So GST and the end of catch-up are **indistinguishable** here: both are "some
round from which correct blocks see every correct block below them".

**`U` is the common view as of the snapshot.** Eventual DAG synchrony says
anything one correct validator holds, all eventually hold. So the union of the
correct validators' views *is* `U`, and every correct validator's view of the
snapshot is the **full** view — `ids := U.ids`, downward-closed by `U.complete`.

That is the crispest form the assumption takes here, and it is what makes L3
a theorem rather than an appeal: "eventually all agree" becomes "L2
instantiated at the full view". It also fixes what `U` *means* — not "every
block anyone ever wrote", but "every block some correct validator ever held".
A Byzantine block revealed to nobody is simply not in the universe.

**(assumption)** `R` is therefore *not* the GST round. It is defined as the
round from which synchrony has fully taken effect — GST plus however long
catch-up ran. What this framing gives up is any bound on `R − GST`, which is
precisely the quantitative content already dropped with Δ (§4.3). It is not
evasion: the framing is correctly reporting that the distinction is not
observable in it.

### 4.3 After R — honest-to-honest coverage, and why views do not give it

The final phase is *"all correct blocks contain all other correct blocks
because of the sufficient delay"*.

**Honest-to-honest only.** The assumption says a *correct* block references
every *correct* block of the round below, and both restrictions are
indispensable:

- **Nothing may be assumed about Byzantine blocks existing.** A Byzantine
  validator can publish nothing at all, so there is no round-`n` block of
  theirs to reference. It can equally publish and reveal to only some
  validators, so even correct validators cannot be assumed to hold it.
- **Nothing needs to be.** L4 counts only correct certificates, and there are
  `n−f` correct validators — a quorum — so the argument never asks whether a
  Byzantine block was seen.
- **Well-formedness survives.** A correct block referencing every correct
  block of the round below already names `≥ n−f` distinct creators, so
  validity's quorum condition is met without any Byzantine reference. Nothing
  is lost by the restriction.

Getting this wrong in the *strong* direction — assuming all blocks are
referenced — would be assuming Byzantine validators behave, which is exactly
what a fault model must not do.

This does not follow from view convergence **alone**, and what has to be
added is set out below.

**Coverage is delivery plus a build rule.** Fast propagation puts every
correct round-`n` block into every correct validator's hands; a validator that
then waits long enough before building at `n+1` references all of them. That
is the mechanism, and it *is* formalized — `Timing.synchronisedOn_of_timing`
(S6) derives `SynchronisedOn` from exactly this. What view convergence supplies
by itself is only the delivery half. A network that propagates perfectly still
commits nothing if validators build on the quorum-completing arrival, which is why
`Timing.waits` is a field and not a remark.

**But views need a build-time index, and that is what `held` is.** A block's
references are fixed when it is built, so what matters is not what a validator
holds *eventually* but what it held *at that moment*. `View` records no time,
so a view-convergence statement cannot be plugged in directly. `Delivery.held
v n` is precisely "what `v` held from round `n` when it built its round-`(n+1)`
block", and with that index L7a is one line (`synchronised_of_delivery`). This
is a modelling point, not a claim about the mechanism: the static model has no
clock, so the outcome has to be phrased on `refs`.

**The timeout must exceed `delay + D`, not `delay`.** Validators enter round
`n` at different times, so `v`'s wait has to cover both the propagation bound
and the spread `D` between entries. That is `hbackoff` in S6, and `D` is
derived rather than assumed (`driftFrom_of_prompt`).

**The mechanism is an adaptive timeout, and the gap matters.** A correct
validator cannot identify which of its peers are correct, so it cannot wait
*for the correct blocks*. It waits a fixed period and builds on whatever
arrived. Before GST no period is long enough, and nothing lets the validator
detect that directly — what it observes is that **commits have stopped**.
Raising the timeout when commits stall is what eventually pushes the period
past the true delay.

`Synchronised R` is therefore the *outcome* of that feedback loop once the
network settles, not a rule any validator follows. It is stated in terms the
protocol cannot itself observe, and the loop that delivers it is driven by
liveness failure — the very thing being proved away.

It also welds two unlike things into one object: the network guarantee and
rule (3b). That is a modelling defect rather than a necessity, and open
§9's S4 records the split — `Synchronised` becomes a **theorem**, derived
from an implementable protocol rule plus a delivery assumption. The timeout
story above then attaches to something real: a timeout governs what a
validator *holds*, which is a notion the split introduces and `refs` alone
cannot express.

What the split does **not** do is make anything unconditional. There is no
time model here, so the chain bottoms out at delivery: the timing content
still enters as an assumption, only a cleaner one. And this section's argument
is untouched either way — coverage needs a build rule and a build-time index
on top of delivery, however the assumption is packaged.

**(assumption)** No wall clock and **no Δ**. Δ would force views indexed by an
instant and every statement quantified over instants, for no proof content:
the theorems are *"all will commit"* and *"never gets stuck"*, and Δ is a
performance claim layered on top. Flag if the quantitative bound is wanted —
it brings back the time model and should be scoped separately.

### 4.4 The horizon — why `U` is finite, and what that costs

`BlockUniverse.ids` is a **`Finset`**. Every universe holds finitely many
blocks. That is not incidental: it is what makes `authorsAt` have a
cardinality at all, and every quorum argument in the development counts one.

`Live` as first stated ignored this. It said a correct validator has a
block at round 0 and another at every round after — infinitely many distinct
blocks, in a `Finset`. So **no universe satisfied it**, and L1, though
proved, said nothing. This is checked, not argued — writing `Live⁰` for that
unbounded draft:

```lean
theorem not_live (U : BlockUniverse Validator BlockId Payload) : ¬ Live⁰ U
```

The proof is three lines: pick a correct validator, collect its blocks at
rounds `0 … |U.ids|`, and note they are `|U.ids| + 1` distinct members of
`U.ids`. It is not in the repository — `Live` now carries the horizon, so
there is nothing left to refute — but the same argument applies to any field
that names a block at every round, which is why `Timing` carries a horizon
too (§7).

The fix is a **horizon** `N`: `builds` fires only for `r < N`, so the DAG
reaches round `N` and stops. Three things follow.

**`N` is a demand on the DAG, not a bound on it.** `Live U D N` requires that
correct validators *actually have* blocks at every round up to `N`. A larger
`N` is a **stronger** hypothesis satisfied by **fewer** DAGs — it is not
slack, and picking it enormous does not make the theorems cover more. What
makes them cover everything is that they are universally quantified over `N`:
a DAG of height `h` is handled at `N = h`, whatever `h` is. There is no
feasibility ceiling and no constant to choose.

**Two independent axes.** `N` measures *extent* — how far the DAG reaches.
`R` measures *quality* — from which round correct blocks cover the correct
blocks below. Neither implies the other, and all four combinations are real:

| | `R` small | `R` large, or never |
|---|---|---|
| **`N` large** | tall and synchronous — commits | tall but asynchronous — grows, commits nothing |
| **`N` small** | synchronous but short — nothing to commit yet | short and asynchronous |

Neither is a clock. `R` is a round index and `N` a round count; Δ stays
dropped (§4.3).

**Unboundedness moves to the family.** No finite snapshot contains infinitely
many commits, and the claim that one could was the bug. "The
ledger grows without bound" is now a statement across horizons: for every `N`
there is a DAG reaching it (`Ugrow`), and for every slot there is a later one
that commits (L6). That is the honest form of the claim when the object is a
`Finset`.

**What this does *not* touch.** L4 needs correct blocks at three consecutive
rounds — a local, finite requirement. It takes `Populated` at `r`, `r+1` and
`r+2` and never mentions `N`, growth, or a limit. The horizon appears only in
L1, which manufactures `Populated` from growth, and in L6, which chains them.
The only real proof in the plan is untouched by any of this.

## 5. Definitions

Mirrors `LeanDag/Liveness.lean` and `LeanDag/Timing.lean`, in file order.
Several predicates come in two forms: a general one over a validator set `T`,
and an abbreviation at `T := Correct` that recovers the original statement.
The generalisation is S5; it is what lets L4 need only a *quorum* of reliable
validators rather than every one of them.

```lean
/-- What L4 needs of a round: every validator in `T` has a block there.
Local and finite — no growth, no horizon. Keeping `N` out of L4 is the point
(§4.4). -/
def PopulatedOn (U) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

abbrev Populated (U) (r : ℕ) : Prop := PopulatedOn U Correct r

/-- Antitone: a smaller set is easier to populate. This is what lets L1 keep
concluding about all of `Correct` while L4 consumes only a quorum. -/
theorem PopulatedOn.mono (hsub : T ⊆ T') :
  PopulatedOn U T' r → PopulatedOn U T r

/-- What each validator had in hand, one round at a time — the layer the
static model lacks. Note what it does **not** contain: a clock. -/
structure Delivery (U) where
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- **Protocol rule.** A correct validator references everything it held.
  Implementable and observable, unlike `Synchronised` itself. -/
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids, (U.block b).creator = v →
    (U.block b).round = n + 1 → held v n ⊆ (U.block b).refs

/-- **Asynchrony.** A quorum that *exists* is eventually *held*. Conditional
on existence, since unconditionally it would assert the block production L1
sets out to prove. No round bound — this holds before GST too. -/
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, 2 * F.f + 1 ≤ (authorsAt U n).card →
    ∀ v ∈ Correct, 2 * F.f + 1 ≤ (creatorsOf U.block (D.held v n)).card

/-- The positive protocol behaviour liveness needs. `N` is the **horizon**:
without it `U.ids` would have to be infinite, and it is a `Finset` (§4.4). -/
structure Live (U) (D : Delivery U) (N : ℕ) where
  genesis : Populated U 0
  builds  : ∀ r < N, ∀ v ∈ Correct,
    2 * F.f + 1 ≤ (creatorsOf U.block (D.held v r)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1

/-- From round `R` on, a `T`-block references every `T`-block of the round
below. `R` is **not** GST (§4.2); it is a round index, not a clock. -/
def SynchronisedOn (U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs

abbrev Synchronised (U) (R : ℕ) : Prop := SynchronisedOn U Correct R

/-- Antitone too, so existing witnesses feed the quorum-relative L4. -/
theorem SynchronisedOn.mono (hsub : T ⊆ T') :
  SynchronisedOn U T' R → SynchronisedOn U T R

/-- **Synchrony, at the delivery layer.** After `R` the *whole* correct round
is held — not merely a quorum of it, which is what `DeliversQuorum` gives
unconditionally. With `Delivery.includes` this yields `Synchronised` (L7). -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ Correct, ∀ a ∈ U.ids, (U.block a).round = n →
    (U.block a).creator ∈ Correct → a ∈ D.held v n

/-- Every correct validator's eventual view (§4.2). Downward-closed by
`U.complete`. -/
def View.full (U) : View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete

/-- The schedule names a `T`-leader arbitrarily far out (§3c). Without it no
recurrence statement holds: `Slots.leader` is an arbitrary function and could
name Byzantine validators forever. -/
def FairScheduleOn (T : Finset Validator) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T

abbrev FairSchedule : Prop := FairScheduleOn Correct
```

### The timing layer

`LeanDag/Timing.lean`. Everything above treats `SynchronisedOn` as a
hypothesis; this is where it is earned (S6).

```lean
/-- When each validator built each block, and what the network guarantees.
`gst`, `delay` and `timeout` are fields rather than parameters because they
belong to the execution, not to the statement. -/
structure Timing (U) (T : Finset Validator) (N : ℕ) where
  blk : Validator → ℕ → BlockId          -- `v`'s round-`n` block
  built : Validator → ℕ → ℕ              -- when `v` built it
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ                              -- Δ
  /-- The universe stops at the horizon. Without this the structure is
  **unsatisfiable**, exactly as the first `Live` was (§4.4). -/
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids
  blk_creator : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v
  blk_round : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n
  /-- **Build no earlier** (protocol). A *full timeout* after entering the
  round — **not** as soon as a quorum is in hand (S6). -/
  waits : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  /-- **Delivery** (network). This is GST, and where the chain bottoms out. -/
  covers : ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, gst ≤ built w n →
    built w n + delay ≤ built v (n + 1) →
    blk w n ∈ (U.block (blk v (n + 1))).refs
  /-- The last time any `T`-validator built at round `n`. An explicit max, so
  no `Finset.max'` machinery is needed. -/
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  /-- `latest` is **attained**, not merely an upper bound. As a bare bound it
  would carry no information and S6's second case would fail. -/
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **Build no later** (protocol). Once the timeout has elapsed *and* the
  round below has arrived, a validator builds. The counterpart to `waits`,
  and what makes drift derivable rather than assumed (S6). -/
  prompt : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)

/-- `T`-validators are never more than `D` apart at the same round, from
round `n₀` on. **Derived**, not assumed — see S6. -/
def Timing.DriftFrom (tm : Timing U T N) (n₀ D : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, n₀ ≤ n → n ≤ N →
    tm.built w n ≤ tm.built v n + D
```

### The rated layer

`LeanDag/Quantitative.lean`. Three optional hypotheses, each strengthening one
already in play, and each yielding a bound the weak form cannot give (S8, S9).
Nothing above depends on them.

```lean
/-- A backoff growing at least as fast as the round index. Strengthens the
`hub` of `exists_backoff_ge`, and needs no `Monotone`. -/
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n

/-- A `T`-leader within every window of `w` slots. The rated `FairScheduleOn`;
round-robin over `n` gives `w = f + 1`. -/
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T

/-- Slots at most `s` rounds apart — the upper companion to `Slots.spacing`,
which bounds them from below. Safety never asks for this direction; a latency
claim needs exactly it. -/
def BoundedSpacing (s : ℕ) : Prop := ∀ k, S.slotRound (k + 1) ≤ S.slotRound k + s
```

The wait bound (L9) needs none of these — only a round-`0` spread `D₀` and a
constant timeout of at least `D₀ + Δ`.

## 6. The results

### Without synchrony

- **L0 — The DAG is dense below its frontier.** If any block exists at round
  `r`, then every round `n < r` has at least `n−f` distinct authors.

  A round-`r` block references `n−f` distinct round-`(r-1)` creators, so round
  `r-1` carries a quorum of authors; that round is then nonempty, so the same
  argument applies below it. Downward induction.

  **No assumptions at all** — not `Live`, not `Synchronised`. This is validity
  alone, and both ingredients already exist (`creators_quorum`,
  `creators_refs_subset_authorsAt`). It is the precise form of *"the DAG grows
  regardless"*, and it says more than growth: the DAG cannot be tall and thin.

- **L1 — No stall.** Given `Live U D N` and `DeliversQuorum D`, every correct
  validator has a block at every round up to `N`: `r ≤ N → Populated U r`.

  Induction on `r`. Base is `genesis`. The step takes **two** hops, because
  `builds` is view-relative: the induction hypothesis puts every correct
  validator in `authorsAt U r`, so a quorum *exists*; `DeliversQuorum` turns
  that into each correct validator *holding* a quorum; only then does `builds`
  apply. Still **no synchrony** — the notes' *"from round 0 onwards,
  always"*, now qualified by the horizon (§4.4).

  This is where `card_correct` (`n−f ≤ |Correct|`) finally gets used.
  `spec.md` §2 has carried it as unused-but-kept-for-liveness from the start.

  L1 is the **only** result where `N` does real work: its whole job is to turn
  a growth assumption into the local `Populated` facts L4 consumes.

### View growth

- **L2 — Decisions are monotone in the view.** If `V ⊆ V'` then
  `Decided U V k v → Decided U V' k v`.

  Induction on the derivation. `DirectCommitIn` and `DirectSkipIn` are both
  monotone — intersecting the certificate or blame set with a larger view can
  only grow the creator set — and the indirect cases follow inductively.

  **This works only because `CertifiedIn` is universe-level.** The
  `indirectSkip` case carries a *negative* premise — no candidate is certified
  in reach of the anchor. Had the indirect check been view-relative, that
  premise would be **anti**-monotone: growing the view could reveal a
  certificate and flip a skip into a commit, and L2 would be false. C1 defined
  `CertifiedIn` over `U` rather than `V`, with T6a
  (`certifiedIn_iff_of_view`) showing the view-restricted computation agrees.
  That is what keeps the negative premise stable.

  Worth having independently of liveness: combined with M1 it says a validator
  **never revises a decision** as its view grows. The safety results so far say
  decisions do not *conflict*; they do not say decisions do not *change*.

- **L3 — Commit propagation.** If any validator decides slot `k` on any view,
  the same verdict holds on the **full** view:
  `Decided U V k v → Decided U (View.full U) k v`.

  L2 instantiated at `V' = View.full U`. Since every correct validator's
  eventual view is the full view (§4.2), this *is* "all correct validators
  eventually reach the same decision" — with the informal "eventually"
  discharged by the framing rather than waved at.

### After R

- **L4 — A leader in a correct quorum commits.** Write `r = slotRound k`.
  Given a validator set `T` with `n−f ≤ |T|`, `PopulatedOn U T` at `r`,
  `r+1` and `r+2`, `SynchronisedOn U T R`, `R ≤ r`, and `leader k ∈ T`, the
  leader's block is directly committed
  (`directCommit_of_leader_mem`). `directCommit_of_correct_leader` is the
  `T := Correct` instance.

  **`T` is a quorum, not all of `Correct`** (S5). The proof counts to `n−f`
  and never higher, so `Correct` enters at exactly one point —
  `card_correct` — and everything after is a subset argument. Demanding all
  of `Correct` would make the theorem lapse when one correct validator misses
  one round, though the protocol still commits.

  **Population is not optional here.** `SynchronisedOn` says `T`-blocks
  *reference* `T`-blocks; it says nothing about blocks *existing*. Without
  it the theorem is satisfied vacuously by an empty DAG.

  **But growth is.** The three hypotheses are local and finite — no `Live`,
  no `N`, no limit universe. L1 supplies them from `Live U D N` when
  `r + 2 ≤ N`, but L4 does not care where they come from. That is what keeps
  the only hard proof in the plan independent of the horizon question
  (§4.4).

  Every `T`-authored round-`(r+1)` block references `L` by coverage — `L` is
  `T`-authored — so the supporters include all of `T`, at least `n−f`. Every
  `T`-authored round-`(r+2)` block then references all of *those*, so its
  `votesIn` has `n−f` distinct creators and it certifies `L`. The
  certificates therefore also come from `n−f` distinct creators, which is
  `DirectCommit`. Both steps are the same `SynchronisedOn` applied at adjacent
  rounds — `certifies_of_synchronisedOn` is literally both at once.

  **Only correct-to-correct coverage is used.** The argument never asks
  whether any Byzantine block was produced or seen, which is what lets
  `Synchronised` stay restricted to correct authors on both sides (§4.3).

  The conclusion is the *universe-level* `DirectCommit`. It becomes an actual
  decision through the full view: `DirectCommitIn` there is `DirectCommit`,
  so `Decided U (View.full U) k (some L)` follows — which is what L6 needs and
  what L3 propagates.

- **L5 — An absent leader is skipped.** If `leader k` has no
  round-`slotRound k` block, the slot is decided `none`.

  Immediate, and it is what a C1 decision was drawn for: `Decided.directSkip` takes the
  premise `∀ L, IsLeaderBlock U k L → DirectSkipIn U V L …`, which is
  **vacuously true** when the leader published nothing. Choosing the `∀` form
  over naming a candidate block is what makes this case disappear.

- **L6 — Commits recur.** Given a `FairScheduleOn T`, for every slot `k` there is
  a slot `k' ≥ k` such that **every** sufficiently grown synchronous DAG
  commits it:

  > `∀ k, ∃ k' ≥ k, R ≤ slotRound k' ∧`
  > `  ∀ U D N, Live U D N → DeliversQuorum D → SynchronisedOn U T R →`
  > `    slotRound k' + 2 ≤ N → slot k' commits`

  given `T ⊆ Correct`, `n−f ≤ |T|` and `FairScheduleOn T`
  (`commits_recur_on`; `commits_recur` is the `T := Correct` instance).

  **This is where `T ⊆ Correct` earns its place.** L4 alone does not need it —
  its counting cares only about `|T|`. L6 does, because its population comes
  from L1, which knows only about correct validators. That is also the
  *modelling* reason it must hold: withholding is free for the adversary, so
  any argument counting Byzantine-authored blocks is defeated by doing
  nothing (S5).

  **The quantifier order is the whole content, and getting it wrong makes the
  statement false.** The tempting form — *given `Live U D N`, for every `k`
  there is a committing `k' ≥ k` with `slotRound k' + 2 ≤ N`* — is not
  provable. Fairness promises a correct leader *somewhere* beyond `k`, and
  that slot may lie past the horizon; nothing lets you ask for a nearer one.
  Fixing `U` and `N` first therefore caps how far fairness may reach.

  Stated as above the problem disappears, because `k'` depends only on the
  **schedule** — `FairSchedule` and `slotRound` are properties of the `Slots`
  instance, not of any DAG. So the slot is named first and the DAG grows to
  it second, which is also the correct reading of *"the ledger grows without
  bound"*: not that one DAG commits infinitely often, but that no slot is the
  last one a DAG can be grown far enough to commit.

  Fairness names a correct leader at some `k' ≥ max(k, k_R)`, where `k_R` is
  any slot with `R ≤ slotRound k_R`; L1 then populates its three rounds and L4
  commits it.

  Such a `k_R` exists because `slotRound` is unbounded — the `Slots` spacing
  condition gives `slotRound k + 3 ≤ slotRound (k+1)`, so rounds grow without
  limit. Small, but it is a real proof obligation rather than an aside.

  **The two side conditions read as they should.** `R ≤ slotRound k'` is
  *this slot is after synchrony took hold*; `slotRound k' + 2 ≤ N` is *the
  DAG has grown past this slot's certificate rounds*. A DAG with `R > N`
  satisfies neither for any slot and commits nothing — correct, since it
  stopped growing before synchrony arrived.

  **Unboundedness lives across horizons, not inside one.** No finite snapshot
  holds infinitely many commits. Read L6 together with `ugrow_live` — for
  every `N` a DAG reaches it, and for every slot a later one commits (§4.4).

  **Not "every slot decides".** That is the natural stronger claim, and it
is false. L4 needs a *correct* leader and L5 an *absent* one; a Byzantine
  leader that publishes a block and reveals it to only some validators falls
  in neither gap. `Synchronised` is honest-to-honest, so it says nothing about
  whether correct validators reference a Byzantine-authored block — some will,
  some will not, and the slot stays undecided.

  That case is exactly why the indirect rule exists, and why M4/M6 are **not**
  made redundant by liveness. Recurrence is the right shape for the statement:
  not "the machinery for undecided slots becomes unreachable" but "undecided
  slots cannot delay the ledger indefinitely, because a correct leader is
  always coming".

### Earning `Synchronised`

- **L7 — `Synchronised`, derived.** Two layers, each removing one assumption.

  `synchronised_of_delivery : Delivery U → EventuallyDelivers D R →
  Synchronised U R`. The proof is `refs ⊇ held ⊇ every correct block below` —
  a single term. It splits one welded assumption into an implementable
  protocol rule and a pure network one (S4), but makes nothing
  unconditional.

  `Timing.synchronisedOn_of_timing` and `exists_synchronisedOn_of_backoff` go
  one layer further, deriving `SynchronisedOn U T R` from **GST plus an
  unbounded backoff** (S6). The argument is four inequalities: drift bounds
  how far apart `T`-validators are at a round, the backoff pushes the timeout
  past `drift + delay`, `waits` turns that into "everything a peer built one
  round below has arrived", and `covers` turns arrival into a reference.

  Drift is itself a theorem (`driftFrom_of_prompt`), not a hypothesis: pairing
  `waits` with `prompt` keeps the spread between `T`-validators from growing
  once `delay ≤ timeout`, so a bound at one round is a bound at all later
  ones. What the layer assumes is GST, the two build rules, and a backoff that
  never stops growing.

  Non-equivocation finishes it. `SynchronisedOn` quantifies over *every*
  `T`-authored block, and T1 identifies each with the one `Timing` names —
  which is why `T ⊆ Correct` is needed there. A Byzantine author could have
  several blocks in a round, and `blk` names only one.

  **Nothing above L7 changed when either layer landed.** L4 and L6 still take
  `SynchronisedOn` as a hypothesis; these supply it. That is the payoff of
  staging L7 last (§7).

### Bounds

`LeanDag/Quantitative.lean`. Every result here strengthens one above, and each
requires a strengthened hypothesis (S8, S9). Nothing imports the file, so
the weak forms remain available untouched.

- **L8a — `R` made explicit.** `synchronisedOn_of_rate` replaces
  `∃ R, SynchronisedOn U T R` with

  `SynchronisedOn U T (max (max (D + delay) n₀) gst)`

  given `Rated timeout` (`∀ n, n ≤ timeout n`). It drops `Monotone`, which
  `exists_backoff_ge` needs and `backoff_ge_of_rate` does not.

- **L8b — the committing slot bounded.** `commits_recur_within` puts it within
  `w` slots of `max k R` under `FairWithin T w`; `commits_recur_by_round` then
  bounds its *round* under `BoundedSpacing s`, the upper companion to
  `Slots.spacing` that the class never carried because no safety result asks
  for it.

- **L9 — the wait bound.** `directCommit_of_wait`: after GST, if every
  `T`-validator waits at least `D₀ + Δ` before building, every correct leader
  is committed — where `D₀` bounds the round-`0` spread. So
  **`Delay(Δ) = D₀ + Δ`**, and `2Δ` when `D₀ ≤ Δ`
  (`directCommit_of_wait_two_delay`), with `decided_of_wait` the decision form.

  The timeout here is a **constant**: no backoff, no `Rated`, no `Monotone`, no
  existential. That is what the backoff is for — it exists only because Δ is
  unknown.

  `Timing.populatedOn` supplies L4's three population facts from `Timing`
  itself, so these statements need no `Live`, no `DeliversQuorum` and no L1.

## 7. Staging

| | | risk | |
|---|---|---|---|
| L0 | density below the frontier | low — existing lemmas, no new primitives | ✓ `card_authorsAt_of_lt` |
| L2 | view-monotonicity of `Decided` | low — mirrors `decided_unique`'s induction | ✓ `decided_mono` |
| L3 | `View.full`, then L2 instantiated | low | ✓ `decided_full` |
| — | **`Ugrow`: a family satisfying `Live`, `DeliversQuorum` and `Synchronised` at every `N`** | low, and required **first** | ✓ `ugrow_live`, `ugrow_deliversQuorum`, `ugrow_synchronised` |
| L1 | `Live U D N` + `DeliversQuorum D`, then induction on rounds | low | ✓ `no_stall` |
| L4 | `PopulatedOn` ×3 + `SynchronisedOn`, then the two-layer argument | medium — the only real proof | ✓ `directCommit_of_leader_mem` |
| L5 | vacuity of the `∀`-over-candidates premise | low | ✓ `decided_none_of_leader_absent` |
| L6 | `FairScheduleOn`, then L1 and L4 | low — but see the quantifier order | ✓ `commits_recur_on` |
| L7a | `Delivery`, then `Synchronised` as a theorem | low — see S4 | ✓ `synchronised_of_delivery` |
| — | **`ugrowTiming`: a `Timing` witness at every horizon** | low, and required **first** | ✓ `ugrowTiming` |
| — | **`ugrowHonest`, `ugrowSkew`: non-degenerate witnesses** | low — see S7 | ✓ `LeanDagTest/Partial.lean` |
| L7b | `Timing`, then `SynchronisedOn` from GST + backoff | medium — see S6 | ✓ `exists_synchronisedOn_of_backoff` |
| L8a | `Rated`, then `R` read off instead of extracted | low — see S8 | ✓ `synchronisedOn_of_rate` |
| L8b | `FairWithin` and `BoundedSpacing`, then L6 rebounded | low — see S8 | ✓ `commits_recur_by_round` |
| — | **`rrSlots`: a round-robin schedule, window `f+1`** | low, and required **first** | ✓ `rrSlots_fairWithin` |
| L9 | round-`0` spread + a constant wait, then L4 | low — see S9 | ✓ `directCommit_of_wait` |

L0, L2 and L3 come first because none needs a new primitive: L0 is pure DAG
structure, L2 and L3 are pure view reasoning. That defers every modelling
decision until something is already proved.

**Every definition gets a witness before anything is proved from it.**
Staging the model before L4 rather than before L1 is what permits an
unsatisfiable `Live` to be *proved against* before anyone tries to satisfy
it — `U.ids` is a `Finset`, and the rule forced infinitely many blocks. The
rule applies three more times:

- `Timing` had the **identical flaw** — `blk` at every round again forces
  infinitely many blocks — and writing `ugrowTiming` caught it, so `Timing`
  carries a horizon too.
- Writing `ugrow_synchronised` revealed that `Synchronised` had never been
  **defined in Lean at all**; it existed only in this document.
- Writing `ugrowSkew` (S7) found that the constants making S6's two branches
  both reachable sit in a **one-point window**, which no lockstep witness
  could have shown.
- `FairWithin` (S8) could not reuse `fairSlots` at all: its leader is
  *constant*, so it satisfies `FairWithin T 1` and exercises nothing. `rrSlots`
  is a real rotation, and it is what makes the window `f + 1` meaningful.

**The witness is a family, not a model.** One model shows `Live` holds at one
horizon; the claim needed is that every horizon is reachable. `Ugrow N` takes
`BlockId := ℕ` with round `b / 4`, creator `b % 4`, and refs the whole round
below — finite at each `N`, unbounded across them. The `U`–`U7` models of
`LeanDagTest/Model.lean` cannot serve: all are `Fin n` and of fixed height.

It also satisfies `Synchronised` at `R = 0`, since its blocks reference the
entire round below. That matters because `Live` and `Synchronised` being
*jointly* unsatisfiable would leave L4–L6 vacuous even if each held alone —
so one family settles both.

**L7 came last deliberately, and that was right — but it was not "purely
additive" as predicted.** The reasoning for staging it late held up: L4–L6
keep taking `Synchronised` unchanged, and each new layer simply supplies it
another way. Doing it first would have meant guessing which shape of `held`
L4 wanted.

What was not foreseen is how much it unlocked. Once `Delivery` existed it made
S2 settleable, and settling S2 changed `Live`, which now takes the `Delivery`
it is stated against. And the seam it cut — *assume `Synchronised` above,
supply it below* — is exactly where the timing layer (L7b, S6) then slotted
in, one level further down, again with nothing above it changing.

So the layer is additive *downstream* of `Synchronised` and a *prerequisite*
upstream of it. The visible consequence: **proof order and file order differ.**
`Delivery` sits near the top of `Liveness.lean`, ahead of `Live`, though
`synchronised_of_delivery` was proved long after — and `Timing.lean` is
logically the bottom of the stack while being the last file written. Worth
flagging, since the table above reads as a file order and is not one.

### Where it lives

The liveness development is three library files, plus four of witnesses. Read
top-down, each layer *assumes* what the one below it *supplies*.

| file | contents |
|---|---|
| `LeanDag/Liveness.lean` | L0–L6, plus `Populated`, `Live`, `Delivery`, `Synchronised`, `FairScheduleOn`, and L7a |
| `LeanDag/Timing.lean` | L7b — `Timing`, `DriftFrom`, and `SynchronisedOn` earned from GST |
| `LeanDag/Quantitative.lean` | S8 — `Rated`, `FairWithin`, `BoundedSpacing`; S9 — the wait bound `Delay(Δ)` |
| `LeanDagTest/Growth.lean` | `Ugrow`, `ugrowDelivery`, `ugrowTiming` — satisfiability at every horizon |
| `LeanDagTest/Partial.lean` | `ugrowHonest`, `ugrowSkew` — the partial and skewed cases (S7) |
| `LeanDagTest/Quantitative.lean` | `rrSlots` — round-robin, and the rated hypotheses witnessed (S8) |
| `LeanDagTest/Model.lean` | the `Fin n` safety models; L0, L2 and L3 are exercised here |

Note the inversion: `Timing.lean` is logically the **bottom** of the stack and
was the **last** file written. Proof order and file order differ, and §7
explains why. `Quantitative.lean` sits **beside** the stack rather than in it:
nothing imports it, and every theorem in it is a strengthening of one below,
requiring a strengthened hypothesis.

## 8. Open questions

Ordered by **importance** — whether a real deployment could be hurt if the
question goes unanswered — not by how easy each is to settle. Cost is listed
separately, because the cheapest item here is not the most important one.

| | question | why it matters | cost |
|---|---|---|---|
| **Q3** | How far should the quantitative version go? | no operational bound of any kind | high |
| **Q4** | Should `FairScheduleOn` be round-robin? | no throughput bound; leader predictability unmodelled | medium |
| **Q5** | Is a partial-view model needed? | *settled* — §9 S7 | — |
| **Q6** | Should L1 hold from round 0, or only after `R`? | presentational | low |

Q1 (*does a timeout deliver coverage?*), Q2 (*is `Populated` too strong?*)
and Q5 (*is a partial-view model needed?*) are **settled** — §9, S6, S5 and
S7. Q1 and Q2 were the two highest-importance entries on the list. Numbering
is left alone so earlier references still resolve.

What remains is the residue of Q3 and Q4 after S8 settled their main halves,
and one presentational question (Q6). Nothing open now affects whether the
existing theorems are true — only how much they say.

### Q3 — How far should the quantitative version go?

**Mostly settled by S8 and S9.** S8 bounds `R` in rounds; S9 answers the
operational form — *what should a validator set its timer to?* — with
`Delay(Δ) = D₀ + Δ`, a constant, and `2Δ` in the headline case. What remains:

- **No proof the adaptive *loop* converges.** S8 assumes a rated backoff; it
  does not derive one from the feedback mechanism §4.3 describes. And
  `Timing.timeout : ℕ → ℕ` is indexed by round, **common to `T`** — a real
  per-validator backoff, where validators raise at different moments, cannot
  even be stated, let alone shown to converge. That needs a richer `Timing`.
- **No wall-clock latency.** `le_built` relates rounds to time in one
  direction only (`n ≤ built v n`), which is the weakest possible clock. S8's
  bounds are in **rounds and slots**, not seconds; converting needs the reverse
  relation, derivable from `prompt` but not derived.
- **No bound for a Byzantine leader's slot.** Direct commit is `r+2`, but a
  Byzantine leader pushes the work onto the indirect rule with no bound on how
  distant the anchor is. S8 bounds the wait for the next *`T`-leader*, which
  sidesteps rather than answers this.

§4.3 drops Δ, and the layer it attaches to now exists: `held`, not `refs` (S4).

### Q4 — Should `FairScheduleOn` be round-robin?

**Mostly settled by S8.** `FairWithin T w` is the rated form, `rrSlots`
witnesses it at `w = f + 1`, and `commits_recur_by_round` turns it into a round
bound. What remains is the *other* issue this question always carried:

**Leader predictability is unmodelled.** `Slots.leader` is an arbitrary
function, so nothing distinguishes a schedule an adversary can predict from
one it cannot. An adversary who knows who leads slot `k` can attack them
before their round — a standard attack on this protocol family, and entirely
invisible here. `FairWithin` does not help: it constrains *when* good leaders
appear, not whether the adversary can see them coming.

### Q6 — Should L1 hold from round 0, or only after `R`?

As stated it holds from round 0 with no synchrony, which is stronger and
matches the notes. It does assume correct validators never stop before the
horizon — but a correct validator that stops is a *crash* fault, and crash
faults are a subset of Byzantine, so the `f` budget already covers it.
Presentational. Note this is independent of §4.4: the horizon bounds *how far*
L1 reaches, not *where it starts*.

## 9. Settled questions

Kept because each was decided against a defensible alternative, and the
reasoning is what a later reader will want.

### S1 — `Live` is an explicit argument, not a class

`Faults` is a class because it is *universal*: every theorem in the development
carries it, so hiding it loses no
information. `Live` is not — L0, L2
and L3 do without it and L1 does not. When an assumption separates the
unconditional results from the conditional ones, hiding it is exactly
backwards; a reader could no longer tell which is which from a signature.

Folding `Live` into `Faults` was considered and is impossible anyway: the
dependency runs the wrong way, since `Live` mentions a `BlockUniverse`
whose own type requires `Faults`. It would also be undesirable if it were
possible — every safety theorem would acquire a liveness hypothesis it does
not use, and `decided_unique` currently holds *even if correct validators
crash*. That is the standard safety/liveness split, and it is worth
keeping.

### S2 — `builds` is stated on `held`, not on existence

The first form said a correct validator builds once *any* `n−f`
validators have round-`r` blocks. That is not something a validator can
act on: it cannot build on blocks it has never received. The real rule is
a **timeout plus a quorum in its own view**.

Once S4's `Delivery` layer existed, `held` was exactly the missing
notion, so `builds` is now measured against `D.held v r`. The condition
splits cleanly in two, which is the gain: `builds` is protocol (hold a
quorum, build) and `DeliversQuorum` is network (a quorum that exists is
eventually held). Both are asynchrony-only, so L1 still needs no synchrony
— its step simply takes two hops instead of one.

The **timeout leaves no trace** beyond this. With no clock, waiting longer
can only show up as a larger `held`; `builds` therefore asks for a quorum
in view and nothing more, and `EventuallyDelivers` is what demands the
*whole* correct round after `R`.

### S3 — `Live` is finite, with a horizon `N`

Recorded because the alternative is defensible and was rejected on cost,
not on principle. Making `BlockUniverse.ids` a `Set` would let `U` be the
genuine limit and would state unbounded growth inside a single universe —
which is what §4.2 originally claimed. It was rejected because it reopens a
*finished and verified* safety development: `blocksAt`/`authorsAt` would
need per-round finiteness as a new `BlockUniverse` field (not derivable —
`no_equivocation` constrains only correct authors, so a Byzantine validator
may author unboundedly many blocks in one round), and `Set` membership is
undecidable, so all 135 `by decide` proofs in `LeanDagTest` would need
rework across 72 `.ids` sites.

That `decide` infrastructure is what has caught every vacuity bug in this
project — including the one that forced this question. Trading it away to
make a paragraph literally true is the wrong exchange.

A third option — `builds` firing only when round `r+1` is already nonempty
— was rejected for saying nothing about the DAG getting *taller*, which
discards the notes' *"from round 0 onwards, always"* entirely.

### S4 — `Synchronised` is derived, not assumed

`Synchronised` welds two unlike things together: a protocol rule and a
network guarantee. It cannot be derived from anything in the model as it
stands, because the model is a static `BlockUniverse` — blocks and refs,
no time, no delivery, no record of what a validator *held* when it built.
`Synchronised` is stated on `refs` because `refs` is all there is.

Adding that missing layer splits it:

```lean
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- **Protocol rule.** A correct validator references everything it held. -/
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids, (U.block b).creator = v →
    (U.block b).round = n + 1 → held v n ⊆ (U.block b).refs

/-- **Network assumption.** After `R`, correct blocks reach correct
validators in time to be built on. This is eventual DAG synchrony. -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop := ...

theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R
```

The proof is `refs ⊇ held ⊇ all correct blocks below` — a few lines. **The
gain is not logical.** One assumption becomes two, and nothing turns
unconditional. The gain is that each piece is a single kind of thing:
`includes` is implementable and observable, which is exactly what §3(b)
notes `Synchronised` fails to be; `EventuallyDelivers` is pure network.

It also puts the timeout in the right place. A timeout governs *when you
build*, i.e. what lands in `held` — it has nothing to do with `refs`. §4.3
currently explains the backoff next to a definition that structurally
cannot express it. And if the quantitative version (Q3) is ever
wanted, Δ attaches to `held`, not to `refs`: that is the layer where a
time bound means anything.

`Synchronised` keeps its exact statement. It stops being a hypothesis one
assumes and becomes one that can be discharged, so L4–L6 are untouched.

### S5 — L4 and L6 take a quorum of correct validators, not all of them

`PopulatedOn` and `SynchronisedOn` now take a validator set `T`; `Populated`
and `Synchronised` are the `T := Correct` abbreviations, so nothing downstream
moved. Both are **antitone** in `T`, which is what lets L1 keep concluding
about all of `Correct` while L4 consumes only a quorum, and lets the existing
`Ugrow` witnesses feed the generalised statements unchanged.

L4's proof needed no change beyond replacing `card_correct` with the
hypothesis `n−f ≤ T.card` — `Correct` entered at exactly that one point, and
everything after was a subset argument.

**Where `T ⊆ Correct` is and is not needed.** L4 alone does not need it: the
counting cares only about `T.card`. It *is* needed in L6, because L6's
population comes from L1, which knows only about correct validators. That is
the principled home for the hypothesis — and it is also the modelling reason
it must hold, since a `T` containing Byzantine validators would make
`SynchronisedOn` unjustifiable: withholding is free for the adversary, so any
argument counting Byzantine-authored blocks is defeated by doing nothing.

**One honest limit.** `n−f ≤ |T|` and `|T| ≤ |Correct| = n − actual
Byzantine` together force

> `actual_byzantine + slow_correct ≤ f`

Progress-with-the-fast-ones spends from the same budget as Byzantine faults.
At exactly `f` Byzantine, `T = Correct` necessarily and no correct validator
may lag.

### S6 — `Synchronised` is earned from GST, drift included

**The problem this answers** — originally Q1, the highest-importance entry on
the open list:

> A correct validator waits on a timeout and builds on whatever arrived; it
> cannot tell correct peers from Byzantine ones (§3b). If Byzantine validators
> respond *fast* while some correct ones are slow, a validator can fill its
> quorum with Byzantine blocks and miss correct ones — **violating
> `Synchronised` even after GST**. §4.3, as then written, called the
> justification "a timing argument this development does not formalize" — a
> line this section made stale and which §4.3 no longer carries.

`LeanDag/Timing.lean` settles it, adding the layer beneath `Delivery`:

```
GST + Δ delivery  ──▶  SynchronisedOn U T R  ──L4/L6──▶  commits
   (Timing.lean)          (was assumed)
```

**Two things the formalisation corrected.** The dichotomy *"either Byzantine
validators participate and commits happen, or the timeout grows"* does not
work: a Byzantine *leader* can publish and reveal selectively, leaving its
slot undecided however long anyone waits. The argument that does work never
mentions the adversary — it quantifies over `T` only, which is better, since
no reasoning about strategy is needed.

And it puts an obligation on implementations: `waits` says a validator builds
a **full timeout** after entering the round, *not* as soon as it holds `n−f`
blocks. An adversary answering instantly can fill an early quorum with
Byzantine blocks and crowd out the correct ones — including the leader's — so
building on the first `n−f` makes the backoff accomplish nothing.

**Drift, the last assumption.** `Timing` first carried `Drift` as a field:
`T`-validators are never more than `D` apart in real time at the same round.
It is now a theorem.

The idea — *once one correct validator reaches round `r`, the others follow
within a bounded time* — needed one correction. It does **not** give a fixed
`2Δ` bound, because every validator's clock advances by the same timeout: the
spread is **preserved**, not compressed. That is enough: the coverage
argument needs drift *bounded*, not small.

Pairing `waits` (build no *earlier* than a full timeout) with a new `prompt`
field (build no *later* than the timeout elapsing and the round below
arriving) makes the induction go through, splitting on `prompt`'s `max`:

- **timeout-limited** — the validator advanced by exactly the same
  `timeout n` as everyone else, so the spread is unchanged;
- **delivery-limited** — it finished by `latest n + delay`, and `latest` is
  *attained* by some `T`-validator, so the inductive bound applies to that one
  and `delay ≤ timeout n` absorbs the rest.

`latest` being attained rather than a free upper bound is what makes the
second case work; as a bare bound it would carry no information.

So `driftFrom_of_prompt` turns a spread bound at **one** round into a bound at
every later one, and `DriftFrom` is stated from a round rather than from 0 for
exactly that reason — while the backoff is still below `delay`, drift may grow.

What the whole chain now assumes: GST (`covers`), the two protocol rules
(`waits`, `prompt`), and an unbounded monotone backoff. Nothing else.

### S7 — the witnesses now exercise the partial cases

`Ugrow` and `ugrowTiming` showed the liveness definitions are *satisfiable*,
but satisfied them in the easiest possible way. `ugrowDelivery` set `held v n`
to **every** round-`n` block, so the delivery hop added by S2 never met a
partial view; `ugrowTiming` had `delay = 0` and zero drift, so S6's two-case
induction only ever took the **timeout-limited** branch. Partial views are the
normal case, and a branch no witness reaches is a branch where a mistake would
hide.

`LeanDagTest/Partial.lean` supplies both over the same `Ugrow N` universe.

**`ugrowHonest`** — the Byzantine validator withholds, so correct validators
hold only the three correct blocks of each round. `ugrowHonest_partial` shows
validator `0`'s block exists in the universe and is held by nobody, and
`ugrowHonest_deliversQuorum` shows a quorum survives anyway. That is §3(b)'s
scenario made concrete: withholding is free, and the argument does not care.

**`ugrowSkew`** — validator `v` builds at `v + 4n`, so `T = {1,2,3}` is spread
across drift `2`, with `delay = 2` against `timeout = 4`.

Those constants are forced, and the pinch is the interesting part:

- `synchronisedOn_of_timing` needs `D + delay ≤ timeout`, so `timeout ≥ 4`;
- the delivery-limited branch fires for `w` only when
  `w + timeout ≤ 3 + delay`, so for `w = 1` it needs `timeout ≤ 4`.

At `timeout = 4` both hold, with equality on each side — `w = 1` takes the
**delivery** branch and `w = 3` the **timeout** branch, so both are live. A
first attempt used `timeout = 3`, satisfied the second constraint and failed
the first. That is exactly the check a degenerate witness cannot perform, and
finding the window is narrow is itself worth knowing.

**Not done: the round-spread exhibit** §4.1 asks for, for the following
reason. At `f = 1`, `n = 3f+1 = 4` there are four validators and `|Correct| = 3 =
n−f` exactly, so *every* correct validator is needed for a quorum and none
can lag. Exhibiting round spread alongside commits needs `f ≥ 2` — seven
validators with one Byzantine, leaving six correct and room for one to fall
behind. That is S5's combined budget (`actual_byzantine + slow_correct ≤ f`)
showing up as a concrete obstruction rather than an inequality.

### S8 — the bounds are available, from rated hypotheses

Q3 and Q4 both asked for a number and got an existential. The reason was the
same in each case, and it is not a weakness of the proofs: **the hypotheses
are themselves bare existentials**, so no bound is derivable from them.

- `hub : ∀ m, ∃ n, m ≤ tm.timeout n` — the backoff clears any threshold
  eventually, at no stated rate. Take `timeout n = ⌊log₂ (n+1)⌋`: monotone,
  unbounded, admissible, and it needs `n ≥ 2 ^ (D + delay) - 1`. Slower
  schedules push `R` out without limit.
- `FairScheduleOn T : ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T` — a schedule naming
  `T`-leaders at slots `0, 10, 1000, …` is fair, with unbounded gaps.

So the fix is a **rated** hypothesis, and `LeanDag/Quantitative.lean` supplies
three. Nothing below it changes; every existing theorem keeps its weak
hypotheses and stays available.

| weak | rated | gives |
|---|---|---|
| `hub` | `Rated timeout` — `∀ n, n ≤ timeout n` | `R = max (max (D + delay) n₀) gst` |
| `FairScheduleOn T` | `FairWithin T w` | the committing slot within `w` of `max k R` |
| *(none)* | `BoundedSpacing s` | that slot's **round**, and an explicit horizon |

**A hypothesis is dropped, not merely added.** `backoff_ge_of_rate` needs no
monotonicity — the bound at `n` comes from `n` itself, so it cannot lapse —
where `exists_backoff_ge` needs `Monotone` to propagate one clearing round
upward. And `Rated` implies `hub` (`unbounded_of_rated`), so this is a genuine
strengthening of one assumption plus a deletion of another, not a sideways
move.

**`BoundedSpacing` has no weak counterpart, and that is the point.**
`Slots.spacing` bounds slot rounds from *below*, which is what safety needs —
M4's anchor must sit at least three rounds up. A latency claim wants the
opposite bound, and the class never had one, because no safety result asks.
Adding it is what turns a slot bound into a round bound.

**The witnesses matter more than usual here**, since a rated hypothesis is
strong enough to be unsatisfiable — in which case the bounds are bounds on
nothing, exactly as the unbounded `Live` and `Timing` were. All three are
witnessed in `LeanDagTest/Quantitative.lean`:

- `ugrowTiming_rated` — the `2 ^ n` backoff is rated, and drives `R` to `0`;
- `rrSlots_fairWithin` — genuine round-robin, window `f + 1 = 2`. `fairSlots`
  could not serve: its leader is *constant*, so it satisfies `FairWithin T 1`
  and exercises nothing;
- `rrSlots_boundedSpacing` at `s = 3`, which `Slots.spacing` already forces to
  be the tightest legal value.

Composed, `ugrow_commits_by_round` reads: for every slot `k` there is a
committing slot at round `≤ 3k + 6`, in every `Ugrow` grown to `3k + 8`. That
is the concrete latency figure Q4 asked for.

**What this does not settle** is recorded in Q3: the backoff *loop* is still
assumed rather than derived, `Timing.timeout` is common to `T` so a
per-validator backoff cannot be stated, and every bound here is in **rounds and
slots** rather than seconds — `le_built` relates the two in one direction only.

### S9 — the wait bound: `Delay(Δ) = 2Δ`

Q3 asked how long after GST liveness resumes. S8 answered it in **rounds**, via
a bound on `R`. This answers the operational question instead: *what should a
validator set its timer to?*

> After GST, if every `T`-validator waits at least `D₀ + Δ` before building,
> every correct leader is committed — where `D₀` bounds the spread at round `0`.

`directCommit_of_wait`, with `decided_of_wait` as the decision form and
`directCommit_of_wait_two_delay` the headline case `D₀ ≤ Δ`, giving
**`Delay(Δ) = 2Δ`**.

**The timeout is a constant.** No backoff, no `Rated`, no `Monotone`, no
existential `R`. That is the point, and it says what the backoff is *for*: the
backoff exists only because Δ is unknown. A validator that knows the delivery
bound needs no adaptation at all.

**Where `D₀` comes from — and why the drift obstacle is not in the way.** The
natural instinct is to derive `D ≤ Δ` post-GST: everyone sees a quorum within Δ,
so everyone enters the next round within Δ. **`Timing` cannot prove that**, and
the reason is `waits`: a lagging validator may not catch up faster than its own
timeout, which is deliberate (§7 — an adversary answering instantly would
otherwise fill an early quorum with Byzantine blocks). Drift is preserved, not
compressed, and S6 records that.

The way past it is not to derive the bound but to **take it at round `0`**,
where it is a claim about how far apart validators *started* — and
`driftFrom_of_prompt` then carries it forward unchanged forever. A system whose
validators start together has `D₀ = 0` and `Delay(Δ) = Δ`; one started by a
common broadcast has `D₀ ≤ Δ`, since the signal itself takes at most Δ to
arrive. **The factor of two is the price of not having synchronised clocks.**

**`Timing` populates rounds by itself** (`Timing.populatedOn`), since it already
asserts a block per `T`-validator per round below the horizon. So these
statements need no `Live`, no `DeliversQuorum` and no L1 — the only hypotheses
about time are the start spread, the wait, and the slot being past GST.

**The witness sits on the boundary.** `ugrowSkew`, built for S7 to exercise both
drift branches, has round-`0` spread `2`, `delay = 2` and `timeout = 4` — so
`D₀ = delay` and `2 * delay = timeout`, and **every inequality holds with
equality**. `ugrowSkew_directCommit_of_wait` applies the `2Δ` form at exactly
that point, which is what shows the constant `2` is the right one rather than a
safe over-estimate. A witness with slack would not.

**What remains** is the conversion to wall-clock. `Delay(Δ) = 2Δ` is a
*duration*, so this part is genuinely in time units — but the number of rounds
to a commit is still bounded only by S8's round count, and turning "`3k + 8`
rounds, each at least `2Δ`" into an elapsed-time figure needs an upper bound
accumulating `prompt` across rounds, which nothing supplies. Q3 keeps that.
