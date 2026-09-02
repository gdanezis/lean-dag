# lean-dag — Hydrozoan: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Hydrozoan** arc: the
dual-path commit rule of the Hydrozoan paper (`\sysname` in the
manuscript; `DagHydrangea` in the reference implementation,
`asonnino/mysticeti`), under the hybrid fault model of DagHydrangea —
`n ≥ 3f + 2c + k + 1` replicas, at most `f` Byzantine, at most `c`
crashed, `k` a tunable slack. A leader is committed in two message
delays by a fast quorum of votes or in three by a quorum of
certificates, skipped by a quorum of blames, or decided later through
an anchor by a graded rule with three rungs. The arc proves the rule
safe — no two views ever decide one slot differently, whatever the
routes, and committed sequences are prefix-consistent — and live above a
structural rendering of eventual synchrony, and grounds the liveness
hypotheses by exhibiting them. The development was carried out in the
paper's repository and then in `asonnino/mysticeti` (`lean/`, PR #230)
before being ported here; its Optimal-Hydrozoan variant, which imports
this arc, is the `OptimalHydrozoan` arc (`optimal-hydrozoan.md`).
Results carry **HZ**-labels; everything lives in `LeanDag/Hydrozoan/`
under the statement/proof partition (§10), with `decide` witnesses in
`LeanDagTest/Hydrozoan/`, consuming nothing from the core.

## 0. Overview

The protocol runs on an uncertified DAG. Replicas proceed in rounds;
every block references at least `q = n − f − c` blocks of distinct
authors from the round below. A *slot* is one leader-decision instance:
slot `k` is proposed at its propose round by its leader, voted on one
round later, and settled at the decision round two rounds later. Three
direct rules read a slot off the DAG. The **fast path** commits the
leader's block on `q_fast = n − p` votes at the voting round, where
`p = ⌊(c + k)/2⌋` is how many of the round's votes the path can do
without. The **slow path** commits it on `q_slow = 2f + c + 1`
certificates at the decision round, a certificate being a decision-round
block carrying `q_cert = ⌈(n + f + 1)/2⌉` votes among its parents. The
**skip** rule discards the slot on `q_fast` blames at the voting round.
A slot none of the three settles is decided from the nearest committed
slot far enough above it — the *anchor* — by a **graded rule**: commit
if the anchor's causal history holds a certificate for a candidate,
else commit the least candidate with `q_weak = f + p + 1` anchor-linked
votes, else skip.

The arc's one structural observation is that **the fast path and the
slow path are held together by counting alone**. The paper's two-case
consistency argument — a fast commit leaves a *weak footprint* that
every anchor sees, so the indirect rule can neither skip the slot nor
commit a rival — is six inequalities on five thresholds, and the six
hold for every fault configuration the class admits, with no cap on the
slack `k` (§6). The seam between the paths is therefore a theorem of
the thresholds, not of the schedule or the network, and the whole of
safety quantifies over every schedule.

Three consequences shape the arc.

- **Safety has no schedule content.** The slot schedule is an abstract
  class — a monotone unbounded propose round and a leader per slot,
  keyed injectively — and multi-leader rounds are slots sharing a
  round. Pipelining is a witness instance, never a proof obligation.
- **The guaranteed liveness path is the slow one.** With `c` crashes and
  `f` silent Byzantine replicas only `q` voters are certain, and
  `q < q_fast` in general; `q_cert ≤ q` and `q_slow ≤ q` make the slow
  path reachable by the guaranteed quorum alone. The fast path and the
  direct skip are *opportunistic*: they fire exactly when the actual
  faults fit `p`, and the arc states them outside its liveness claim as
  performance facts (§7).
- **Fairness is a hypothesis on the schedule, and per-slot rotation
  does not provide it at the hybrid bound.** Liveness needs three
  consecutive correct-led slots; a per-slot round robin can be starved
  of them by crashed replicas spaced one every three, inside the
  bound. The wave-aligned rotation — one leader per wave — is fair with
  no premise at all, and is what grounding exhibits (§8).

### 0.1 Correspondence with the paper

| Paper (`hydrozoan-paper/sections/`) | Lean |
|:---|:---|
| Model and thresholds (`algorithms.tex`) | `Model/Faults.lean` — `Faults`, `p`, `q`, `qFast`, `qCert`, `qSlow`, `qWeak`, `Correct`, `NonByzantine` |
| DAG-building layer (`algorithms.tex`) | `Model/Block.lean` (`ValidWrt`), `Model/BlockUniverse.lean`, `Model/View.lean` |
| `Link` | `Model/CausalHistory.lean` — `Reaches` |
| Waves and pipelining, `ProposeRound`, `VotingRound`, `DecisionRound`, `GetLeaderBlocks` | `Model/Slots.lean` — `Slots`, `votingRound`, `decisionRound`, `IsLeaderBlock` |
| `IsVote`, `IsCertificate`, `FastCommittedLeader`, `SlowCommittedLeader`, `SkippedLeader` | `Model/DirectRules.lean` |
| `TryIndirectDecide`, `DecideFromAnchor` | `Model/IndirectRules.lean` (`EligibleAsAnchor`, `CertifiedIn`, `WeakLinked`), `Model/Decided.lean` (`Decided`) |
| after GST | `Model/Liveness.lean` — `PopulatedOn`, `SynchronisedOn`, `View.full`, `View.CoversUpto` |
| `lem:thresholds` (the slack-cap table) | `ThresholdArithmetic/` (HZ1) |
| slot safety, the two-case consistency argument | `DirectSafety/` (HZ2), `SlotAgreement/` (HZ3) |
| `ExtendCommitSeq`, `LinearizeSubDags`, prefix consistency | `PrefixAgreement/` (HZ4) |
| liveness | `DirectLiveness/` (HZ5), `IndirectLiveness/` (HZ6), `EventualDecision/` (HZ7), `Grounding/` (HZ8) |

Names follow the paper's: `qFast` for $q_{\mathit{fast}}$ and so on;
faulty replicas are Byzantine or crashed, the rest correct.

## 1. The fault model and the thresholds

`Faults` carries the bounds `f`, `c`, `k`, the *actual* Byzantine and
crashed sets of a run, their disjointness, `3f + 2c + k + 1 ≤ n`, and
the two cardinality bounds. Two pools are read off it and nothing else
is: `Correct`, the complement of both sets, which availability and
liveness count; and `NonByzantine`, the complement of the Byzantine set,
which uniqueness counts — a crashed replica never equivocates. A static
universe has no behaviour, so the classes enter only through which pool
a hypothesis mentions.

```lean
def p : ℕ := (F.c + F.k) / 2
def q : ℕ := Fintype.card Replica - F.f - F.c
def qFast : ℕ := Fintype.card Replica - p Replica
def qCert : ℕ := (Fintype.card Replica + F.f) / 2 + 1
def qSlow : ℕ := 2 * F.f + F.c + 1
def qWeak : ℕ := F.f + p Replica + 1
```

`p` is derived, never an input: the design makes a too-large fast
allowance unrepresentable rather than assumed away. `q_cert` is written
as the smallest strict majority of `n + f`, so that `2·q_cert > n + f`
is immediate.

## 2. Blocks, the universe, views, causal history

A block is its round, its author, and the ids of its parents; ids are
resolved through a total lookup `blk : BlockId → Block`, so validity is
a predicate on `(blk, b)`:

```lean
structure ValidWrt (blk : BlockId → Block Replica BlockId)
    (b : Block Replica BlockId) : Prop where
  predecessor : ∀ i ∈ b.parents, (blk i).round + 1 = b.round
  distinct_authors : ∀ i ∈ b.parents, ∀ j ∈ b.parents,
    (blk i).author = (blk j).author → i = j
  quorum : 0 < b.round → q Replica ≤ (authors blk b).card
```

The predecessor condition is additive, so the genesis case is derivable
and no natural-number subtraction appears; the quorum counts authors,
which is what every counting argument consumes. The universe is every
block accepted by the DAG-building layer — Byzantine ones included, since
malformed emissions are filtered before entering any DAG — closed under
references, valid throughout, and non-equivocating for non-Byzantine
authors. Non-equivocation is stated at the universe, not per view: two
well-formed local DAGs holding different blocks of one honest author in
one round is exactly that author equivocating. A view is a
reference-closed subset of the universe's ids sharing its lookup, so
replicas disagree only about which blocks they hold. `Reaches` is the
reflexive-transitive closure of the parent relation — the paper's
`Link`, arguments in walking order — and the only reachability notion
the model uses.

Two fidelity gaps are stated once, on the definitions: parents point
only to the immediately preceding round (no weak links), and a vote is
the direct reference `L ∈ parents` rather than the paper's depth-first
traversal — at wave length 3 the two coincide for the blocks the rules
inspect, and the argument is in prose, not in Lean.

## 3. Slots and schedules

```lean
class Slots (Replica : Type*) where
  slotRound : ℕ → ℕ
  leader : ℕ → Replica
  mono : Monotone slotRound
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  keyed : Function.Injective fun k => (slotRound k, leader k)
```

There is no `leadersPerRound` constant: several leaders in a round are
several slots at one round, and the paper's ranked iteration over
`(round, leaderOffset)` is enumeration by slot index. A candidate for
slot `k` is a block of the universe at `slotRound k` by `leader k`;
because Byzantine leaders equivocate, several blocks can be candidates
for one slot, and the rules count authors.

## 4. The direct rules

Every rule is a cardinality comparison counting authors against the
thresholds of §1, primary at the universe and read by a view through
`∩ V.ids` — a view can under-report a rule, never exceed it.

```lean
def FastCommit (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qFast Replica ≤ (supporters U L (r + 1)).card
def SlowCommit (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qSlow Replica ≤ (certifiers U L r).card
def SkippedLeader (U : BlockUniverse Replica BlockId) (k : ℕ) : Prop :=
  qFast Replica ≤ (blames U k).card
```

`supporters U L r` are the authors of round-`r` blocks with `L` among
their parents; `certifiers U L r` the authors of decision-round blocks
whose votes for `L` come from `q_cert` distinct authors; `blames U k`
the authors of voting-round blocks none of whose parents is a candidate
for `k` — blames target the slot, so a vote for any equivocating copy is
not a blame. The commit rules take the propose round; only the skip
takes the slot.

## 5. The indirect rule and the decision relation

Slot `j` may anchor slot `k` when `j`'s propose round lies strictly past
`k`'s decision round. Rung 1 asks for a certificate in the anchor's
causal history; rung 2 for `q_weak` anchor-reachable votes, stated over
an explicit witness set of vote blocks so that the trusted core never
decides reachability:

```lean
def CertifiedIn (U : BlockUniverse Replica BlockId) (A L : BlockId)
    (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C
def WeakLinked (U : BlockUniverse Replica BlockId) (A L : BlockId)
    (r : ℕ) : Prop :=
  ∃ s : Finset BlockId,
    (∀ b ∈ s, b ∈ blocksAt U (r + 1) ∧ IsVote U b L ∧ Reaches U A b) ∧
    qWeak Replica ≤ (authorsOf U.block s).card
```

`Decided U V k v` is an inductive relation with six constructors: the
three direct routes and the three rungs. It is order-free between
constructors — the paper checks skip before commit operationally, but
any justifiable verdict is derivable and safety proves the routes never
disagree — while the strict grading *inside* the indirect rule is
encoded: the weak rung fires only when no candidate has an anchor-linked
certificate, the indirect skip only when both rungs are empty for every
candidate, and the anchor is the nearest eligible committed slot, every
eligible slot between skipped. The weak rung commits the least
qualifying candidate under a `LinearOrder` on ids — the paper's
`argmin digest` tie-break, since equivocating copies may tie. Undecided
is the absence of a derivation.

## 6. Safety

**HZ1 — the threshold table** (`ThresholdArithmetic/`). Six
inequalities, one per row of the paper's table, stated subtraction-free
over every `Faults` instance:

```lean
def Statement : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica] [Faults Replica],
    CertUniqueness Replica ∧ FastUniqueness Replica ∧ FastStarvation Replica ∧
      SlowCollectible Replica ∧ AnchorSeesSlow Replica ∧ AnchorSeesFast Replica
```

`2·q_cert > n + f`, `2·q_fast > n + f`, `q_fast + q_weak > n + f`,
`q_cert ≤ q`, `q + q_slow > n + f`, and `n + q_weak ≤ q_fast + q`. The
paper's Theorem 1 caps the slack (`k ≤ 2f + c − 4` for even `c`); the
class assumes only the committee bound, and the table holds for every
`k ≥ 0` — nothing in the DAG argument needs the cap (§11).

**HZ2 — direct-rule safety** (`DirectSafety/`). Five pairings across
views: fast/fast, certificate/certificate (universe-level, no views),
slow/slow, fast/slow, and commit/skip exclusion. Fast/slow is the one
the fast path's starvation row carries: a fast commit leaves every
conflicting candidate at most `f + p < q_weak ≤ q_cert` supporters.

**HZ3 — slot agreement** (`SlotAgreement/`), the two-case consistency
argument in one statement:

```lean
def DecidedUnique (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : View U) (k : ℕ) (v₁ v₂ : Option BlockId),
    Decided U V₁ k v₁ → Decided U V₂ k v₂ → v₁ = v₂
```

Its proof consumes a *strengthened* form of the "anchor sees the fast
footprint" row, `q_fast + q − n − f ≥ q_weak`: a Byzantine author's
block in the anchor's history may be its non-voting equivocation, so
only the non-Byzantine overlap contributes anchor-linked votes. The
table's row is stated in the weaker form the paper gives; the
strengthening is a helper lemma (§11).

**HZ4 — prefix agreement** (`PrefixAgreement/`). `commitSeq` is the
committed leaders below a horizon in slot order, skips dropped — the
shape of `ExtendCommitSeq` — and `ledger` flattens each through a
linearizer. Equal horizons give equal sequences, different horizons a
prefix, and ledgers inherit the prefix for the abstracted linearizer;
`DecidesBelow` demands a derivation for every slot below the horizon,
so the claims speak exactly where replicas have produced output.

## 7. Liveness

Safety assumed nothing of the network. Liveness is exactly as strong as
the package of `Model/Liveness.lean`, which renders "after GST"
structurally and is the arc's audit centre of gravity: `PopulatedOn U T r`
— every member of `T` authors a block at round `r` — and
`SynchronisedOn U T R` — from round `R` on, every `T`-authored block
references every `T`-authored block of the round below. Both are
`T`-relative, deliberately: liveness counts to quorums, and demanding
all of `Correct` would void the theorems whenever one correct replica
misses one round. `T ⊆ Correct` and `q ≤ |T|` are hypotheses of the
consuming theorems, never of the predicates. `R` is a round index, not
GST; no clock and no `Δ` appear. `SynchronisedOn` is an assumption and
recorded as one: a replica building on the first quorum it holds can
miss a slow correct block forever, and what makes the property true in
good periods is the protocol's waiting rule, whose derivation from
delivery primitives is out of scope (§12).

**HZ5 — direct liveness** (`DirectLiveness/`). A quorum-sized correct
`T`, synchronised from some `R` at or before the wave and populated
through its three rounds, commits its correct leader through the slow
path, and the verdict is derivable on any view caught up to the
decision round (`View.CoversUpto` — the certificates sit there, so a
caught-up view holds them; the eventual view is caught up to every
horizon, so the whole-universe reading is the special case):

```lean
def CommitLiveness (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ),
    T ⊆ (Correct : Finset Replica) →
    q Replica ≤ T.card →
    SynchronisedOn U T R →
    R ≤ S.slotRound k →
    PopulatedOn U T (S.slotRound k) →
    PopulatedOn U T (S.slotRound k + 1) →
    PopulatedOn U T (S.slotRound k + 2) →
    S.leader k ∈ T →
    ∀ V : View U,
      V.CoversUpto (S.slotRound k + 2) →
    ∃ L, IsLeaderBlock U k L ∧
      SlowCommit U L (S.slotRound k) ∧
      Decided U V k (some L)
```

`FastLatency` and `SkipLatency` are stated in the same file and kept
**outside** `Statement`: when the actual faults fit `p`, the fast path
fires in two rounds and a candidate-less slot skips directly at the
voting round. Both need all of `Correct`, not a quorum-sized `T`, and
both are performance characterisations — the design decision the phase
verifies is that the guaranteed path is the slow one.

**HZ6 — indirect liveness** (`IndirectLiveness/`), pure
decision-relation combinatorics with no synchrony, population or fault
hypothesis. `AnchoredTotality`: once a nearest eligible committed anchor
exists, some rung fires. `DecidedBelowRun`: `c` consecutive committed
slots, long enough that the run's end anchors everything below
(`SpansEligible`, which the pipelined schedule satisfies exactly at
`c ≥ 3`), decide every slot below the run. One committed slot does not
suffice — the slots just below it cannot use it as an anchor — a
three-round run does.

**HZ7 — eventual decision** (`EventualDecision/`), the composition.
`RunDecidesBelow` is the per-universe workhorse with the run's location
explicit; `RunsRecur` is the schedule-only claim that fairness places a
`T`-led run past any slot and any round, from

```lean
def FairRunOn (T : Finset Replica) (c : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T
```

The composed form — for every slot `k` a bound `b ≥ k` with every slot
below `b` decided on any view caught up to the run's last decision
round — is `ledgerProgress` on the proof side; the audited content is
the two Props.

## 8. Grounding

The liveness arc consumes three kinds of assumed hypotheses; HZ8
(`Grounding/`) grounds them by exhibition. `WaveRobinFair`: the
wave-aligned rotation on `n` replicas — slot `k` at round `k`, the
leader holding for three consecutive slots before the rotation advances
— satisfies `FairRunOn Correct 3` with no premise beyond the fault
model, since one correct leader's wave is a full run and the bounds
guarantee a correct replica. `HypothesesRealizable`: for every
quorum-sized `T` and horizon `N`, some universe authored by `T` alone
is `T`-populated to `N` and `T`-synchronised from round 0 — the good
period is a consistent scenario of the model at every scale, and the
`T`-only clause is what earns the `q ≤ |T|` premise, since a `T`-only
universe cannot validly populate a round below quorum size.
`GroundedProgress`: under the wave-aligned rotation, past every slot
some universe commits a bound with every slot below it decided, on any
view caught up to the bound's decision round. The last is an
achievability claim — satisfiability of the conclusion, not the
route — and its universe is not constrained to correct authors (§11).

## 9. Witnesses (`LeanDagTest/Hydrozoan/`)

Every definition is exercised by `decide` before anything is proved
from it, and every `holds` is applied end to end so that a silently
strengthened hypothesis fails the build by arity or type.

- **The fault model and the table.** `sevenReplicas` — `Fin 7`,
  `f = c = k = 1`, replica 0 Byzantine, replica 1 crashed — and the
  tight instances at `f = 10, c = 34` for `k ∈ {0, 1, 2, 4, 10}`, the
  three quorums pinned row by row as they fan out with `k`.
- **The universe and the rules.** A two-round universe in which
  replica 0 equivocates and replica 1 halts after genesis, each
  `ValidWrt` field rejecting a malformed block; a three-round table with
  a view that withholds; the direct rules under the pipelined
  single-leader schedule, the fast path firing exactly at quorum with a
  single certificate far short of `q_slow`; a five-round table
  exercising fast commit, direct skip and rung 1 anchored on it.
- **The fast path without a certificate.** A universe in which a slot
  fast-commits while zero certificates exist anywhere — the anti-vacuity
  guard for fast/slow agreement and the consistency argument's first
  case made structural through equivocation.
- **The hardening universe** `U5`, `Fin 39` ids with junk outside the
  universe, an eligible skipped slot between candidate and anchor whose
  `Decided … none` sub-derivation is real, and the output sequences
  `[2, 31]` and their prefixes.
- **The liveness package.** Four universes over `sevenReplicas` with
  `Correct` exactly quorum-sized: the synchronised one, valid *because*
  of full referencing; one with an unreferenced Byzantine block, the
  `T`-restriction doing visible work; one synchronised from round 2 and
  provably not from 0, the frozen-references failure in miniature.
- **Liveness end to end.** The slow path on the frozen universe where
  the fast path provably cannot fire (five supporters, `q_fast = 6`);
  the fast path on a low-fault `Fin 4` at exact quorum; totality on
  `U5`; the descent on the first table with three consecutive
  committed slots, its decisive slot led by the crashed replica
  with no candidate at all; `RunDecidesBelow` fully concrete over an
  eight-round table; fairness proved for the pipelined schedule and
  refuted for a singleton.
- **The hardening batch.** A proper-subset `T` at eight replicas whose
  actual faults undershoot the bounds, killing the strengthenings
  `T = Correct` and synchrony-on-all-of-`Correct`, both pinned false.
- **Grounding.** The wave-aligned schedule pinned pointwise, fairness
  and realizability applied at two configurations including `T = univ`
  (a `T` holding the Byzantine and the crashed replica), progress past
  slot 5, and the pigeonhole contrast: per-slot rotation at `n = 5`,
  `f = 0`, `c = 2`, crashed at positions 0 and 3, provably starves every
  correct three-run.
- **The axioms tripwire** (`Axioms.lean`): every `holds` pinned by
  `#guard_msgs` to its exact axiom list, within `propext`,
  `Classical.choice`, `Quot.sound` — a build failure, not a script, on
  drift.

## 10. Layout and discipline

The arc adopts the statement/proof partition of the Mahi-Mahi, Black
Marlin and Barnacle arcs (`mahi-mahi.md` §9) and is its origin: the
partition was designed for this formalisation in the paper's
repository, and `barnacle.md` §10 names its `Model/` bar as the one to
meet. `Hydrozoan` is in `ARCS` of `scripts/check-arc-holes.py`.

```
LeanDag/Hydrozoan/
  Model/         definitions only — no theorem and no proof term:
                 Faults (§1), Block, BlockUniverse, View, CausalHistory (§2),
                 Slots (§3), DirectRules (§4), IndirectRules, Decided (§5),
                 Liveness (§7)
  Helpers/       lemma and construction infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ only; `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
LeanDagTest/Hydrozoan/  witness models; audited
```

Results: `ThresholdArithmetic` (HZ1), `DirectSafety` (HZ2),
`SlotAgreement` (HZ3), `PrefixAgreement` (HZ4), `DirectLiveness` (HZ5),
`IndirectLiveness` (HZ6), `EventualDecision` (HZ7), `Grounding` (HZ8).
Auxiliary predicates a claim needs but the core should not carry
(`SpansEligible`, `FairRunOn`, `commitSeq`) are defined in the
`Statement.lean` that needs them, on the audited side.

**The freeze protocol.** For each phase, the audit surface — `Model/`
definitions, `Statement.lean`, witness instantiations — is written
first, in its own files, reviewed, and frozen on the author's go; proofs
are then written until they verify, with a cold-context reviewing agent
over the frozen files and the witnesses in parallel, hunting vacuous
claims and missing witnesses; its findings are relayed, fixes to frozen
files need the go again, and the phase is committed green. Human-readable
and machine-checked content never share a file.

**Relation to the core.** None consumed: the arc carries its own fault
model — the hybrid `(f, c, k)` model is not the core's single fault set
— and its own universe, views and reachability, so that its trusted
core is exactly the paper's model and nothing else. The modelling style
is the core's (a structural block universe, `Finset` counting discharged
by `omega`), and the process is `joachimneu/auto-impossibility-experiment`'s.

**The axioms tripwire** uses `#guard_msgs` around `#print axioms`, so
that a change in the axiom list is a build error rather than a line to
notice in a script's output; the rest of the repository prints the list
bare. **Instance diamonds**: several witness files declare `Faults (Fin n)`
instances for one `n` with different parameters; a file importing two
resolves a threshold against whichever wins, so no witness file imports
two, and where two are in scope a table names its instance explicitly.

## 11. Findings for the paper

- **The slack cap is not needed by the DAG argument.** Theorem 1 of
  Hydrangea caps `k`; the six inequalities the consistency argument
  rests on hold for every `k ≥ 0` under the committee bound alone
  (HZ1). Whatever the cap is for, it is not slot safety.
- **The fast footprint row is consumed in a strengthened form.** The
  table's "anchor sees the fast footprint" row counts the overlap of a
  fast quorum and an anchor's parents; the proof of HZ3 needs the
  *non-Byzantine* overlap, `q_fast + q − n − f ≥ q_weak`, because a
  Byzantine author's block in the anchor's history may be its
  non-voting equivocation. The strengthened form holds, and the paper's
  argument should count it.
- **The guaranteed path is the slow one.** The fast path cannot be
  guaranteed above `p` actual faults; the paper's liveness argument
  should route through the slow path and state the two-round latency as
  conditional on the actual fault count, as `FastLatency` does.
- **Per-slot rotation is not fair at the hybrid bound.** Liveness needs
  three consecutive correct-led slots, and a per-slot round robin needs
  `n` to exceed three times the actual fault count to guarantee them —
  false inside the bound at `n = 5`, `f = 0`, `c = 2` (the witness). The
  wave-aligned rotation is fair unconditionally. The paper's leader
  election should say which.
- **A fast commit frequently leaves no slow path**, structurally and not
  only in time: with equivocation, a slot can fast-commit while no
  certificate for it exists anywhere (the `DirectSafety` witness). The
  indirect rule's weak rung is therefore necessary, not a
  convenience.
- **Two docstring gaps, recorded and left.** `PrefixAgreement`'s ledger
  claim says "for any linearizer whatsoever" where the abstraction is a
  memoryless per-leader function, while the paper's `LinearizeSubDags`
  is stateful; and `GroundedProgress` does not constrain its universe's
  authors, so a universe in which every faulty replica behaves
  satisfies it — the proof uses the correct-authored universe, but the
  statement does not say so. Both are fixed in the `OptimalHydrozoan`
  arc's mirrored statements and left here as findings against the
  frozen core.

## 12. Out of scope

- **Delivery, GST, timeouts.** `SynchronisedOn` records that deriving
  synchrony from delivery primitives and the waiting rule is future
  work; the arc grounds satisfiability, not operational realizability.
- **Weak links**, and the DFS reading of a vote; both fidelity gaps are
  stated on the definitions.
- **Round-jumping recovery.** `T` is fixed across a synchrony suffix; a
  replica that rejoins by jumping to the frontier round sits outside `T`
  for good. A wave-scoped `SynchronisedAt` would readmit it.
- **The DAG-building layer's filtering** of malformed emissions, assumed
  from Mysticeti.
- **Optimal-Hydrozoan**, the variant at Hydrangea's lower bound on the
  fast allowance: its own arc, importing this one.

## 13. Phases

The arc was developed in the paper's repository and in
`asonnino/mysticeti` (`lean/`, PR #230), and ported here with its
namespaces re-homed under `LeanDag.Hydrozoan` and no other change.

| phase | deliverable |
| :-- | :-- |
| 1 | `Model/Faults.lean`; the seven-replica model and the threshold table |
| 2 | `ThresholdArithmetic/` (HZ1) |
| 3 | `Model/{Block,BlockUniverse,View,CausalHistory}.lean`; the equivocation and view witnesses |
| 4 | `Model/{Slots,DirectRules,IndirectRules,Decided}.lean`; the decision-route witnesses |
| 5 | `DirectSafety/` (HZ2); the fast-commit-without-certificate universe |
| 6 | `SlotAgreement/` (HZ3); the hardening universe `U5` |
| 7 | `PrefixAgreement/` (HZ4); the axioms tripwire |
| 8–10 | `Model/Liveness.lean`; `DirectLiveness/`, `IndirectLiveness/`, `EventualDecision/` (HZ5–HZ7); the liveness hardening batch |
| 11 | `Grounding/` (HZ8) |
| 12 | this record; report §22; the reference pipeline |

Each phase ran as statements → review → freeze → proofs → witnesses →
a reviewing agent over the frozen files → commit.
