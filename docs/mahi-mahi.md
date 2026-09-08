# lean-dag — Mahi-Mahi: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their _intended_ meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Mahi-Mahi** arc, written
before the development: the definitions and theorems below are a plan,
and every Lean signature is a proposal until the phase that owns it
freezes it (§10). The question is whether the commit rule of Mahi-Mahi — Mysticeti's rule stretched to a wave of four or five
rounds, with votes counted through the causal cone — is safe on the
unmodified DAG layer, and under what hypothesis it is live **without any
synchrony assumption**. The answer proposed here is a single clause on
the pair (schedule, DAG), `UnpredictableWithin`, which states the
outcome of a late-revealed leader without naming the mechanism that
reveals it. Results will carry **MM**-labels. Everything lives in
`LeanDag/MahiMahi/` with witnesses in `LeanDagTest/MahiMahi/`,
consuming the core read-only like every other arc, and under the
statement/proof discipline of §9, which is new to this repository.

## 0. Overview

**The protocol, as the reference implementation defines it.** The
source of truth for the rule is `crates/consensus/src/protocol.rs` in
the `mysticeti` repository (`Protocol::mahi_mahi`), together with
`base.rs` and `wave.rs`. Relative to Mysticeti it changes three things
and nothing else:

|                                            | Mysticeti                             | Mahi-Mahi                                                     |
| :----------------------------------------- | :------------------------------------ | :------------------------------------------------------------ |
| wave length `w`                            | 3                                     | 4 or 5                                                        |
| voting round                               | `r + 1`                               | `r + w − 2`                                                   |
| decision round                             | `r + 2`                               | `r + w − 1`                                                   |
| a vote for `L`                             | a round-`(r+1)` block referencing `L` | a voting-round block whose **causal cone** supports `L`       |
| direct commit / skip / certificate quorums | `n − f`                               | `n − f`                                                       |
| waiting for the leader before proposing    | yes                                   | **no** (`leader_wait: false`)                                 |
| leader election                            | round-robin                           | round-robin in the implementation; in the paper a common coin reconstructed from `n − f` decision-round blocks, naming `ℓ` ordered slots per round |

The thresholds, the anchor rule, the indirect decision and pipelining
are unchanged. The implementation does not contain the coin: it runs the
Mahi-Mahi rule under round-robin, and is correct when run under partial
synchrony. The coin is what the paper adds for asynchrony, and it is the
one ingredient this arc models _by its effect_ rather than by its
mechanism.

**Why the arc exists.** The core's liveness rests on one structural
hypothesis, `SynchronisedOn` (`liveness.md` §5): after some round every
reliable block references every reliable block of the round below. That
hypothesis is earnable only after GST, and it is consumed at exactly one
place, `certifies_of_synchronisedOn` (`Liveness.lean`). Under asynchrony
it is false for every slot whose leader the adversary knows in advance
(§5.1 gives the pattern). Mahi-Mahi's claim is that with the leader
revealed only at the end of the wave the adversary cannot aim, and the
arc's purpose is to state precisely what "cannot aim" amounts to as a
hypothesis on a DAG, and to prove liveness from that hypothesis alone.

**The results.**

- **MM1 — safety at wave `w`** (§3): the `w`-round rules agree across
  views and routes, for `w ≥ 2`, with `w = 3` collapsing onto the core's
  `Decided`. The paper's Lemmas C.1–C.6.
- **MM2 — the counting lemma** (§4), generic in `w ≥ 4`: in every
  populated wave of any valid DAG, some correct validator's block is
  directly committed; at `w ≥ 5` at least `n − f − |byzantine|` correct
  validators' blocks are. No network hypothesis of any kind. The paper's
  Lemmas C.12–C.14 and C.19, with the `w ≥ 5` count corrected for
  equivocating authors (§4.2).
- **MM2b — deterministic commits under multiple leaders** (§4.3): with
  `2f + 1` distinct leaders at a round and `w ≥ 5`, one of those slots is
  directly committed, for _every_ schedule — no randomness clause at
  all; at `w ≥ 4` with every validator leading, likewise.
- **MM3 — liveness under `UnpredictableWithin`** (§6): if in every
  window of `c` waves the schedule names a committed candidate, commits
  recur; and under the run form of the clause every slot is decided, in
  every reliable validator's own view. `SynchronisedOn`, `Δ`, `gst` and
  timeouts appear nowhere. The paper's Lemma C.16, whose slot-chain
  argument is what fixes the form of the clause (§5.5).
- **MM4 — two refutations on data** (§5.3, §8): round-robin satisfies
  the core's fairness and violates `UnpredictableWithin` on a valid,
  populated DAG — so Mahi-Mahi under a predictable schedule is not
  asynchronously live, which is the reason the coin exists; and
  `UnpredictableWithin` is not implied by `FairScheduleOn`. Witnesses,
  not theorems: they live in `LeanDagTest/MahiMahi/`.
- **MM5 — partial synchrony recovered** (§7): under `SynchronisedOn`
  the clause is derived, not assumed.

### 0.1 Correspondence with the paper's Appendix C

| paper | here | remark |
| :--- | :--- | :--- |
| Lemma C.1 (certificates persist upward) | core `exists_certificate_reaches_of_directCommit`, restated at wave `w` | used by MM1c's indirect cases |
| Observation 1 (one vote per block, by DFS order) | canonical support, §2 | the paper's order is depth-first "following the sequence of block hashes"; here, least block in the cone |
| Lemma C.2 (one certified block per slot) | MM1b | |
| Lemmas C.3, C.4 (commit excludes skip) | MM1a and the indirect cases of MM1c | |
| Lemmas C.5, C.6 (agreement) | MM1c | |
| Lemma C.12 (common core at `r`, reached from `r + 2`) | `commonCore`, §4.1 | the lemma that carries every liveness result |
| Lemmas C.13, C.14 (`w = 5`: `n − f` committable) | MM2 at `w ≥ 5` | the count holds for the references by non-equivocating authors; §4.2 |
| Lemma C.19 (`w = 4`: one committable) | MM2 at `w ≥ 4` | |
| Lemmas C.15, C.20 (probability per wave) | MM2b for the deterministic cases; the probabilistic cases are prose over MM2 | the deterministic threshold is `2f + 1` slots, not `ℓ > f`; §4.3 |
| Lemma C.16 / C.23 (every slot eventually decided) | MM3c | §5.5 on what the chain argument needs |
| note on `w = 3` (safe, not live) | MM1d, and §5.1 | the core's rule, which is why the core assumes synchrony |

## 1. The rule at wave `w`

Fix a `Slots` instance as in the core (`slotRound`, `leader`); the slot
`k` is proposed at `r = slotRound k`. The arc is parameterised by the
wave length `w ≥ 2`, carried as an explicit argument rather than a
class, so that the `w = 3` conservativity statement can mention both
sides.

| round       | name     | what is counted there              |
| :---------- | :------- | :--------------------------------- |
| `r`         | proposal | the candidate blocks of `leader k` |
| `r + w − 2` | voting   | votes and blames                   |
| `r + w − 1` | decision | certificates                       |

At `w = 2` the voting and decision rounds coincide, as in the
Odontoceti, Hybrid and Nemo arcs; at `w = 3` both rounds are the core's.

**Support through the cone.** A voting-round block `q` votes for a
candidate `L` at `(a, r)` when `L` is the block `q`'s cone supports at
`(a, r)` — §2 says which block that is. A block that supports no block
at `(a, r)` blames the slot. Certificates, direct commit and direct skip
are then the core's definitions with the rounds moved:

```lean
-- proposals; Model/Rules.lean
def supportsAt (U) (q : BlockId) (a : Validator) (r : ℕ) : Option BlockId   -- §2
def Votes     (U) (q L : BlockId) : Prop := supportsAt U q (U.block L).creator (U.block L).round = some L
def Blames    (U) (q : BlockId) (a : Validator) (r : ℕ) : Prop := supportsAt U q a r = none

def votesIn   (U) (C L : BlockId) : Finset BlockId := (U.block C).refs.filter (Votes U · L)
def Certifies (U) (C L : BlockId) : Prop := quorumCard Validator ≤ (creatorsOf U.block (votesIn U C L)).card
def certificates (U) (w : ℕ) (L : BlockId) (r : ℕ) : Finset BlockId :=
  (blocksAt U (r + w - 1)).filter (Certifies U · L)
def DirectCommit (U) (w : ℕ) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U w L r)).card
def DirectSkip (U) (w : ℕ) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block ((blocksAt U (r + w - 2)).filter (Blames U · a r))).card
```

Two remarks on fidelity to the implementation. `is_certificate` in
`base.rs` counts votes among the _references_ of the decision-round
block, as `votesIn` does. And `DirectSkip` is stated on the slot `(a, r)`
rather than on a block, as `enough_leader_blame` is: a blame is the
absence of any supported block at the slot, not a vote against a
particular twin — which is also how the core's `directSkip` constructor
quantifies over candidates.

## 2. Canonical support — the design decision of Phase 1

At `w = 3` a vote is a direct reference, and `ValidWrt.distinct_creators`
makes "a block votes for at most one candidate of a slot" a consequence
of validity. At `w ≥ 4` a voting-round block's cone may contain **two
twins** of a Byzantine leader, reached through different paths. Safety
(M5 in the core, MM1 here) consumes exactly one property: _a voter votes
for at most one candidate per slot_. Without it two twins each gather a
certificate from overlapping voters, and agreement fails — the same
configuration the Odontoceti arc records as finding F1
(`odontoceti.md` §6).

The implementation resolves it by order: `find_support` walks the
voter's includes in their stored order and returns the first block it
meets at `(a, r)`; the paper's Observation 1 states the same rule as a
depth-first traversal "following the sequence of block hashes". That
order is part of the block's data, so every node computes the same vote
for a given block. In this development `refs` is
a `Finset` and carries no order, so the choice must be made by another
canonical rule. Two candidates, with the recommendation first:

**(A) Least in the cone** — `supportsAt U q a r` is the least block, in a
`[LinearOrder BlockId]`, among the blocks at `(a, r)` in `q`'s cone
(`historyUptoFrom`, `Causality.lean`), or `none` if there is none. This
is the device the Odontoceti arc already uses for candidate selection,
and for a correct author it is the unique block at `(a, r)`, so it
agrees with any other rule wherever the rule matters for liveness. It
is decidable on a concrete universe and needs no change to `Block`.

**(B) A support function as data** — a field `support : BlockId →
Validator → ℕ → Option BlockId` on a structure extending
`BlockUniverse`, with the one axiom "if the cone holds exactly one block
at `(a, r)`, `support` returns it". Closer to the implementation's
first-seen rule, since it abstracts over every deterministic order; but
it adds a structure the other arcs do not have, and nothing downstream
uses the generality.

**Decision (Phase 0): (A).** The property MM1 consumes is uniqueness of
the vote, not its identity, so any canonical rule yields the same
theorems; (A) is the one that costs the least in new structure. The
deviation from the implementation is recorded in §9 as a modelling
choice, with the observation — which holds for the implementation too —
that **the support order is consensus-critical only through
uniqueness**: two nodes that compute different supports for the same
block would break agreement, but which block a shared rule picks is
immaterial.

## 3. The decision relation and safety (MM1)

`decisionRound k = slotRound k + w − 1`, `Eligible k j :=
decisionRound k < slotRound j` — the core's definitions with the wave
length substituted, which is what the core's docstring anticipated
(`Mysticeti.lean`, `Eligible`). The relation `Decided` has the core's
four constructors, reading `DirectCommitIn`, `DirectSkipIn` and
`CertifiedIn` at wave `w`; the indirect rules' anchor test is
`CertifiedIn U A L r`: some certificate for `L` in the cone of the
anchor `A`, exactly as in the core.

The statements, one file (`Safety/Statement.lean`):

- **MM1a, skip excludes certificates.** `DirectSkip U w a r → ∀ L` at
  `(a, r)`, `certificates U w L r = ∅`. Counting at the voting round: a
  blamer and a voter for `L` are distinct creators, and `n − f` of each
  do not fit in `n` unless `f` equivocators sit on both sides, which
  `distinct_creators` of the certificate's references forbids.
- **MM1b, certificate uniqueness.** Two certificates at one slot name
  the same candidate. Two `n − f` voter sets meet in a correct validator
  with a unique voting-round block, and that block votes for one
  candidate (§2).
- **MM1c, agreement.** `Decided U V₁ k v₁ → Decided U V₂ k v₂ → v₁ = v₂`,
  for any two views — the core's M6 argument, which is entirely a
  consequence of MM1a, MM1b and eligibility, and is expected to
  transcribe.
- **MM1d, conservativity.** At `w = 3` a derivation of the rule's
  `Decided` is a derivation of the core's, and the direct commit
  predicates coincide on every candidate at its own round. One direction
  only: the core's `directSkip` quantifies over the candidates — a quorum
  of blames _per twin_ — where this arc's, like the implementation's
  `enough_leader_blame`, blames the _slot_, a quorum of voting blocks
  supporting no twin at all. The arc's premise is the stronger one; the
  converse fails when a leader equivocates and its twins' blaming quorums
  differ, and the two coincide on any slot with at most one candidate.
  The core's rule is safe either way, but it skips in a corner where the
  implementation leaves the slot undecided. A statement about
  definitions, not about any commit occurring: at `w = 3` commits need
  the core's synchrony hypothesis (§4.2).

## 4. `good` and the counting lemma (MM2)

```lean
-- proposal; Model/Good.lean
/-- The slot-`k` candidates the DAG directly commits at wave `w`. A property of `U` alone. -/
def good (U) (w k : ℕ) : Finset Validator :=
  Finset.univ.filter (fun v => ∃ L ∈ U.ids,
    (U.block L).round = S.slotRound k ∧ (U.block L).creator = v ∧ DirectCommit U w L (S.slotRound k))
```

### 4.1 The common core

Everything below rests on one lemma, the paper's Lemma C.12, stated on
its own because MM2, MM2b and MM5 all consume it:

**`commonCore`.** Under the fault model, `ValidWrt`, `no_equivocation`
and `Populated U (r + 1)`, there is a correct round-`r` block `b` that
lies in the cone of **every** valid block at every round `≥ r + 2`.

The argument: each correct round-`(r+1)` block references `n − f`
distinct creators, at most `f` Byzantine, hence at least `n − 2f`
correct round-`r` blocks; counting over the `≥ n − f` correct
round-`(r+1)` blocks, some correct round-`r` block `b` has at least
`f + 1` correct supporters (the pigeonhole count is
`(n−f)(n−3f)/(n−2f)` such blocks, at least two at `n = 3f + 1`). A
round-`(r+2)` block's `n − f` reference creators meet those `f + 1`,
and a correct supporter has one round-`(r+1)` block (`no_equivocation`
is consumed here), which references `b`. Rounds above `r + 2` follow
by induction: a block references a round below, which already reaches
`b`. Whether the statement carries the closed-form count or only
existence is a Phase 3 planning item; existence is what every consumer
needs.

### 4.2 The counting lemma, generic in `w`

**MM2.** Under the fault model, `ValidWrt`, `no_equivocation`, and
population by a reliable set `T` (`T ⊆ Correct`, a quorum) at **two**
rounds — the round that supplies the common core's existence and the
decision round `r + w − 1`:

- for every `w ≥ 4`, with `T` populating `r + 2`:
  `(goodAt U w r ∩ Correct).Nonempty` — the common core of round `r` is
  voted for by every voting-round block (round `r + w − 2 ≥ r + 2`), so
  every decision-round block certifies it, and the `T`-authored ones are
  a quorum;
- for every `w ≥ 5`, with `T` populating `r + 3`:
  `n − f ≤ (goodAt U w r ∩ Correct).card + |byzantine|` — the common core
  `b` of round `r + 1` is reached by every block at round `≥ r + 3`, and
  through `b` so is each of the `n − f` distinct-creator round-`r` blocks
  it references; those by correct authors are voted for by every
  voting-round block and certified by every decision-round block.

Both bounds are stated for all `w` above the threshold, and the proofs
are the same for every `w` in range since `commonCore` reaches every
higher round. At `w = 3` the voting round is `r + 1` and the common-core
argument has no room, which is the paper's closing note and the core's
reason for `SynchronisedOn`.

**The `w ≥ 5` count.** The paper's Lemma C.13 counts all `n − f`
references of the round-`(r+1)` common core as committable. A reference
by an equivocating author is not: a voting block whose cone also holds a
second twin votes for whichever its support rule orders first, and the
adversary can expose the other twin to part of the voters so that no twin
of that author gathers a quorum. What the argument proves is the bound on
the correct references — at `n = 3f + 1` and `|byzantine| = f`, `f + 1`
good correct validators, a commit probability of at least `1/3` per wave
under a uniform draw rather than the paper's `2/3`. The paper's count is
recovered in any wave whose round-`r` authors do not equivocate, which is
the hypothesis under which Cordial Miners states the same `2/3`; a
statement with that hypothesis is a possible follow-up. The protocol's
liveness is unaffected: a constant fraction is all Lemma C.16 needs.

### 4.3 Deterministic commits under multiple leaders (MM2b)

The core's `Slots.uniform 1 m` models `m` distinct leaders per round.
MM2 gives, with no clause on the schedule: at `w ≥ 5`, if `2f + 1`
distinct validators lead slots at a round, one of those slots is good
(`f + 1` good correct validators and `2f + 1` leaders cannot be disjoint
in `3f + 1`); at `w ≥ 4`, if every validator leads, `GoodNonempty` is the
statement. The paper's Lemma C.15 has `ℓ > f` for the five-round case,
which the corrected count does not support: with `f + 1 ≤ ℓ ≤ 2f` slots
the draw may name `f` equivocators and `ℓ − f` starved correct
validators. These results hold for round-robin, for an adversarial
schedule, for any `Slots` instance with distinct leaders at the round.
They do not make every slot decided (§5.5), but they make commits recur
unconditionally.

## 5. `UnpredictableWithin`

### 5.1 What the clause has to exclude

Take `w = 4` and round-robin, so the adversary knows `leader k` before
round `r`. Under asynchrony it delays the leader's round-`r` block so
that at most `f` correct validators hold it when they build at `r + 1`;
they build on `n − f` other blocks, which validity permits. The
candidate then has at most `f` correct supporters, a round-`(r+2)`
block can reference `n − f` distinct creators while avoiding all of
them, the candidate leaves those cones, and the adversary arranges
fewer than `n − f` certificates. Every slot is treated this way. This is
the formal content of "Mysticeti's rule is not live under asynchrony",
and it applies unchanged to Mahi-Mahi's rule with a known leader.

MM2 says the same adversary cannot do this to _every_ candidate of a
wave: whatever the delivery pattern, at least two survive. So the whole
content of "the leader is revealed late" is that **the adversary cannot
aim** — its reference pattern for the wave is fixed without knowledge of
`leader k`. The model has no adversary and no time, so that sentence
cannot be stated directly. What can be stated is its observable
consequence on the pair (schedule, DAG).

### 5.2 The clause, in words and in Lean

In words: _in every stretch of `c` consecutive waves, at least once the
schedule names a validator whose block the DAG actually committed._

```lean
-- Model/Unpredictable.lean
def UnpredictableWithin (U) (w c N : ℕ) : Prop :=
  ∀ k, decisionRound Validator w (k + c) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U w k'
```

The horizon `N` is part of the definition: `U.ids` is a `Finset`, so
`good` is empty past some round and no finite DAG satisfies an unbounded
`∀ k`; the clause quantifies over the windows whose decision rounds lie
below `N`, and every liveness statement carries the same bound.

Compare the core's `FairScheduleOn T := ∀ k, ∃ k' ≥ k, leader k' ∈ T`
and its rated form `FairWithin T c`. The shape is the same; the target
set `T` — fixed, a property of the schedule alone — has become `good U
w k'`, a property of the DAG. Under partial synchrony the schedule need
only hit a _correct_ validator, because synchrony then guarantees that
validator's block commits (L4), so fairness can be discharged by
round-robin once and for all. Under asynchrony nothing about a
validator guarantees its block commits; only the DAG's actual shape
does, so the hypothesis must relate the schedule to the DAG. No clause
on the schedule alone can serve: §5.1 refutes every deterministic
schedule.

### 5.3 What it says, what it does not, and what makes it honest

It says one thing: the leader keeps landing on committed candidates, at
least once per window. It carries no probability, no independence, no
mechanism and no "round 4". Those live elsewhere:

- _Agreement_ on the leader — every correct validator computes the same
  one — is `Slots.leader` being a function, which safety consumes
  (`keyed`, `IsLeaderBlock`). This is also why the leader cannot be a
  function of the wave's own DAG: round-`(r + w − 1)` data is not
  agreed, and two views computing different leaders would break MM1c.
  A coin supplies agreement cryptographically; the model assumes it.
- _Unpredictability_ is this clause.
- _Uniformity_ turns the clause into a probability: a uniform draw lands
  in `good U w k` with probability `|good U w k| / n`, MM2 bounds that
  below by a constant `p`, and `c` consecutive misses have probability
  `(1 − p)^c`. The measure stays in prose, exactly as GST does in the
  core; MM2′ is the independence statement it would rest on.

Anything with the three properties instantiates the clause — a
threshold-signature coin, a VRF beacon, a trusted randomness source.
Round-robin has the first and not the second, and MM4 proves it.

Three witnesses keep the clause honest, all `decide`-able on four
validators (§8):

- **Satisfiable.** On a fully connected populated DAG, `good = Correct`
  at every wave, so round-robin satisfies `UnpredictableWithin` at any
  `c ≥ 1`. The clause does not collapse into "the DAG is synchronous",
  because the next witness has the same schedule and fails it.
- **Refutable with a deterministic schedule (MM4a).** The pattern of
  §5.1 as a concrete valid, populated DAG with round-robin, on which
  `leader k ∉ good U 4 k` at every wave of the horizon. This is the
  mechanised form of "Mahi-Mahi under round-robin is not asynchronously
  live".
- **Independent of fairness (MM4b).** The same DAG satisfies
  `FairScheduleOn Correct` (round-robin names correct validators) and
  violates `UnpredictableWithin`, so the two clauses are distinct
  hypotheses and neither implies the other.

### 5.4 Two consequences for how liveness is stated

**The horizon.** `U.ids` is a `Finset`, so `good U w k = ∅` past the
horizon and no finite DAG satisfies an unbounded `∀ k, ∃ k' ≥ k`. The
core met the same wall with production (`liveness.md` §4.4). The rated
form with the horizon in its definition is the one that survives (§5.2),
and every liveness theorem carries the same side condition.

**Quantifier order.** The core's `commits_recur_on` names the committing
slot _before_ `U` and `N` are introduced, and its docstring explains
why the reversed form is unprovable there. With `good` depending on
`U` that order is no longer available, and the theorems below quantify
`U` first. Which slot commits now depends on the DAG, which is the
situation being modelled.

### 5.5 The eligibility chain, and the run form of the clause

A directly committed slot `j` does not decide every slot below it. A
slot `i` is decided indirectly through its **lowest eligible** slot —
the first slot `j` with `slotRound i + w ≤ slotRound j` — if that slot
is committed, or through the next one if it is skipped; an undecided
lowest-eligible slot leaves `i` undecided (the core's `indirectCommit`
premise quantifies over the eligible slots between). So commits that
recur without pattern may never decide a given slot: with one leader
per round and `w = 4`, direct commits at rounds `10, 20, 30, …` leave
slot `17` undecided forever, because its chain `17, 21, 25, 29, …`
avoids every one of them. The core meets this with `SpansEligible c`
and a _run_ of `c` consecutive committed leaders
(`all_decided_below_of_fairRun`); the paper's Lemma C.16 meets it by
following the chain of anchors and arguing that an infinite chain with
no direct commit has probability zero under the coin.

The single-hit clause of §5.2 therefore gives MM3b and not MM3c. Two
renderings of the chain argument are possible:

- **Per-chain clause** — every slot's anchor chain eventually meets a
  good slot. Faithful to Lemma C.16, but the chain depends on the
  verdicts themselves (it advances past skipped slots), so the clause
  would mention `Decided`, which is the thing being proved.
- **Run form** — in every window of `c` waves there is a run of `d`
  consecutive good slots, with `d` spanning eligibility:

  ```lean
  def UnpredictableRunWithin (U) (w c d N : ℕ) : Prop :=
    ∀ k, decisionRound Validator w (k + c + d - 1) ≤ N →
      ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ good U w (k' + i)
  ```

  This is the rated analogue of the core's `FairRunOn`, it plugs into
  the existing run machinery, and its probabilistic reading is as
  plain as the single-hit one: a run of `d` good slots has probability
  at least `p^d` per attempt, so `c` attempts all failing has
  probability at most `(1 − p^d)^c`.

**Decision (Phase 0): the run form**, with the single-hit clause kept
for MM3b. Both are properties of the pair (schedule, DAG); the `aim4`
witness refutes both, and shows the run form strictly stronger (§8).

A remark the author may want to check against the paper: Lemma C.16
bounds the chain by "the probability of an infinite sequence of rounds
with no directly committed slots", but the chain advances on the
_earliest_ slot of a round that is committed or undecided, so what
the bound needs is that the earliest-ordered slot of each chain round
is good, not that some slot of the round is. Under the coin's random
ordering that has probability at least `(n − f)/n` at `w = 5`, so the
conclusion stands; but for `ℓ > f` the quantity `p⋆ = 1` of Lemma C.15
is not the one the chain uses, and MM2b's deterministic commit-per-round
does not by itself yield "every slot decided". The `chain` witness
(§8) pins the gap on data.

## 6. Liveness (MM3)

All statements at wave `w` (`Liveness/Statement.lean`), with no
`SynchronisedOn`, `EventuallyDelivers`, `gst`, `delay` or `timeout` among
the hypotheses.

- **MM3a, the leader commits when it is good.** `S.leader k ∈ good U w k
  → ∃ L, IsLeaderBlock U k L ∧ Decided w U (View.full U) k (some L)` —
  L4's role, and the unfolding of `good`.
- **MM3b, commits within the window.** Under `UnpredictableWithin U w c N`,
  every window below the horizon contains a committed slot. The clause
  restated through MM3a, and nothing more: the window is assumed, not
  derived, as in the core's rated `commits_recur_within`.
- **MM3c, every slot decided.** Under `UnpredictableRunWithin U w c d N`
  with `SpansEligible w d` and `1 ≤ w`, for every window below the
  horizon there is a slot `b ≥ k` below which every slot is decided — the
  core's descent `decided_below_of_committed_run` transcribed at wave `w`,
  with the run supplied by the clause instead of by fairness and
  synchrony. The descent consumes one property of eligibility, that an
  eligible anchor lies strictly above the slot, which needs `1 ≤ w`.
- **MM3d, local liveness.** On any pacing structure `PaceCore U T N` with
  `T` a quorum, a candidate certified by every `T`-authored decision-round
  block is decided on each reliable validator's own view at the explicit
  time `max (latest d) gst + delay`. The premise is universal
  certification rather than a bare `DirectCommit`: a quorum of
  certificates by arbitrary authors need not reach a reliable view,
  whereas reliable blocks do (`holds_roundBlocks`); the counting lemma
  supplies the premise for the common-core candidates. The structure's
  convergence is consumed as eventual delivery only — no `gst ≤ R`, no
  backoff — and its production needs no timing.

Not stated: an analogue of the core's L5, "an absent leader is skipped".
The arc's `directSkip` blames the slot with a real quorum, so the core's
vacuous-skip route does not exist here; no liveness result needs it.

## 7. Partial synchrony, recovered (MM5)

The arc must remain usable by the rest of the development, which is
partially synchronous. One lemma does it: for a correct leader,
`SynchronisedOn U T R` at the single round `r → r + 1` already places
the candidate in every later cone (step 3 of §4 with coverage in place
of counting), so

    SynchronisedOn U T R → R ≤ slotRound k → leader k ∈ T → Populated … → leader k ∈ good U w k.

Hence under synchrony from round `0` and population through the
horizon, `UnpredictableWithin` is _derived_ from the core's rated
`FairWithin T c` (`Synchrony/Statement.lean`), and the partially
synchronous route instantiates with the clause as a theorem. This is conservativity in the liveness direction, and it
records a small fact about Mahi-Mahi's rule: at `w ≥ 4` it needs
coverage at one round where Mysticeti's needs it at two.

## 8. Witnesses (`LeanDagTest/MahiMahi/`)

Four validators, `f = 1`, `n = 4`, `quorumCard = 3`, `w = 4` unless stated;
the schedules are local instances, round-robin with one leader per round
unless stated. Every definition is settled by `decide` before anything is
proved from it, and every witness is a default build target.

| file | witness | what it pins |
| :-- | :-- | :-- |
| `Model.lean` | `full4` | six fully connected rounds: the wave arithmetic; `candidatesAt`, `Votes`, `Blames`; certificates and `DirectCommit` at `w = 4` and `w = 5`; `Eligible`; `Decided` by its constructors; a `CertifiedIn` witness |
| `Model.lean` | `twin4` | a Byzantine leader's two round-`0` twins in one voter's cone: `Votes` picks the least and only the least; without the minimality clause both are candidates |
| `Model.lean` | `w3` | at `w = 3` the direct predicates, `certificates`, `votesIn` and `Eligible` agree with the core's on `full4`, and slot `1` is decided by both relations (MM1d on data) |
| `Counting.lean` | `aim4` | the aiming pattern of §5.1 against slot `1`: the target is not committed and directly skipped at `w = 4`; `goodAt aim4 4 1 = {0, 2, 3}` — round-robin names exactly the validator that is not good; the common core on data; at `w = 5` the starved block is reached again and `goodAt = univ`; the statement hypotheses hold; `GoodCard`'s inequality on data |
| `Counting.lean` | `multi` | `Slots.uniform 1 3`, three distinct leaders per round: slot `3` at round `1` is good at both wave lengths, the `∃ k` of `MultiLeader` exhibited |
| `Liveness.lean` | satisfiable | both forms of the clause hold on `full4` under round-robin |
| `Liveness.lean` | MM4a | `¬ UnpredictableWithin aim4 4 1 5`: the one window that matters names the starved validator |
| `Liveness.lean` | MM4b | `FairScheduleOn Correct` for the same schedule, so the clause is not a consequence of fairness |
| `Liveness.lean` | run form | `UnpredictableWithin aim4 4 2 5` holds while `UnpredictableRunWithin aim4 4 1 2 5` fails: the two forms are distinct hypotheses |
| `Liveness.lean` | `SpansEligible` | at one leader per round a run of `w` slots spans eligibility |
| `Axioms.lean` | — | every `holds` depends on the three standard axioms |

The regress of §5.5 is not pinned as an undecidability proof — that would
need inversion over the relation for every slot of a model — and is
recorded in prose; the run-form witness is what the tests carry.

## 9. Layout and discipline

This arc adopts the statement/proof partition of the `hydrozoan-paper`
formalisation, which is new to this repository; the other arcs keep
their conventions.

```
LeanDag/MahiMahi/
  Model/         definitions only, theorem-free: Rules, Decision, Good, Unpredictable
                 (decidable instances by `inferInstanceAs` included: definitions, not proofs)
  Helpers/       generated lemma infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ only; definitions, prose, `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
LeanDagTest/MahiMahi/       witness models; the instantiations are audited
scripts/check-arc-holes.py         sorry/admit/axiom/native_decide/unsafe/partial absent;
                                   Statement.lean files proof-free; Model/ files theorem-free
```

The audit surface is `Model/`, every `Statement.lean`, the witness
instantiations and the checker. Results: `Safety` (MM1), `Counting`
(`CommonCore`, MM2, MM2b), `Liveness` (MM3, MM2′), `Synchrony` (MM5).
MM4 is witnesses, in `LeanDagTest/MahiMahi/Liveness.lean`.

**The freeze protocol.** For each phase: statements are written; the
author reviews them; they are discussed until agreed; from then on they
are **frozen** — no edit to `Model/` or to a `Statement.lean` without
an explicit notice to the author, however small the edit or however
clearly a proof seems to need it. If a proof needs a statement changed,
the proof stops and the need is raised. Proofs are then written until
they verify, the hole checker and `#print axioms` are clean, and the
phase is committed.

**Relation to the core.** The core is consumed read-only: `Block`,
`BlockDag`, `Causality`, `Support`, `Validators`, `Schedule`,
`Liveness` (for `Populated`, `Live`, `Delivery`, the fairness clauses)
and `ViewPace` (for MM3d). If a phase finds that it needs a change to
the core, that is a finding to report, not a refactor to perform.

**Modelling choices recorded.** (i) Canonical support by least block in
the cone rather than the implementation's and the paper's depth-first
hash order (§2). (ii) `DirectSkip` on the slot, as `enough_leader_blame`
has it, which is what makes MM1d one-directional (§3). (iii) The leader
mechanism is abstract; its effect is `UnpredictableWithin` and its run
form, both carrying the horizon (§5). (iv) The wave length is an
explicit parameter, not a class, and every statement is generic in `w`
above its threshold. (v) `Votes` reads the candidate's own author and
round, so `certificates U w L r` does not by itself pin `L`'s round to
`r`; every use goes through `IsLeaderBlock`, which does, and the
statements that need it carry the round as a hypothesis.

## 10. Phases

| phase | deliverable | commit |
| :-- | :-- | :-- |
| 0 | this record | `e79b54f` |
| 1 | `Model/Rules.lean`, `Model/Decision.lean`; `full4`, `twin4`, `w3`; the hole checker | `fbfc555` |
| 2 | `Safety/` (MM1a–d) | `f3fd531` |
| 3 | `Model/Good.lean`, `Counting/` (`CommonCore`, MM2, MM2b); `aim4`, `multi` | `0257c8e` |
| 4 | `Model/Unpredictable.lean`, `Liveness/` (MM3a–d, MM2′); the clause witnesses | `544eeda` |
| 5 | `Synchrony/` (MM5) | `72dea05` |
| 6 | this record brought to the final position; report §17; `related.md` §4.1; README | done |

Each phase ran as statements → review → freeze → proofs → commit; phases
1, 3 and 4 were planned before their statements were written.

## 11. Decisions, and what the development changed

Settled in Phase 0: canonical support is (A), least in the cone (§2);
every statement is generic in `w` above its threshold, `w ≥ 3` for
safety, `w ≥ 4` for existence and `w ≥ 5` for the cardinality bound
(§4); local liveness is in scope; the window `c` is a free parameter
throughout; the clause has a single-hit form for MM3b and a run form for
MM3c (§5.5); the regress witness is a test, not a reported finding; the
common core is stated as existence.

What the proofs changed against the plan, each recorded where it
applies: population at two rounds rather than every round of the wave
(§4.2); the `w ≥ 5` bound counts correct references only, with the
`2f + 1` leader threshold for MM2b (§4.2, §4.3); the clause carries the
horizon in its definition (§5.2); MM1d is one-directional (§3); MM3d's
premise is universal certification, on `PaceCore` with convergence read
as eventual delivery (§6); MM4 lives in the witnesses, and no
`Refutation/` file exists (§9); no L5 at wave `w` (§6).

The core is unchanged: the arc consumes `Block`, `BlockDag`,
`Causality`, `History`, `Support`, `CommonCore`, `Validators`,
`Mysticeti`, `Liveness`, `Quantitative` and `ViewPace` read-only. The
paper's Lemma C.12 was already in the core as T3c
(`exists_common_correct_ancestor`), which is why the counting phase
needed no new counting.
