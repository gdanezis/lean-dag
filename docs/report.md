---
title: "Eventual DAG Synchrony: a machine-checked account of safety and liveness for uncertified DAG consensus"
author: "Code and prose in this project were co-written with heavy LLM assistance. The Lean proofs are machine-checked — the kernel verifies every theorem against its stated form — but whether the definitions and theorem statements capture their *intended* meaning, and whether the surrounding prose is faithful to what is proved, has only human-plus-LLM review behind it. Read critically."
---

## Abstract

DAG-based Byzantine fault-tolerant protocols are widely deployed, yet their
liveness arguments are conventionally stated in terms of per-message delivery
bounds, which obliges the entire proof to carry a time model that the commit
rule itself never mentions. We propose **eventual DAG synchrony** — a
structural condition on the DAG: beyond some round, every correct block
references every correct block of the round below — and give a machine-checked
development, in Lean 4, of safety and liveness for a Mysticeti-style commit
rule above this condition, in which no liveness theorem mentions time. Safety
assumes nothing about the network at all. The structural condition is derived
rather than assumed, and the whole of what the network must supply reduces to
a single clause of **view convergence** — after stabilisation, whatever one
correct validator holds reaches every correct validator within Δ — from which
both coverage and block production follow by the protocol's own build rules.
The quantitative form states that a correct leader is committed once correct
validators wait `2Δ`; a catch-up clause collapses any start spread between
validators in a single post-stabilisation round, so the threshold `2Δ + proc`
holds with no assumption about how the deployment began.

We further prove what the committed ledger *contains*: every commit
carries, at every round below it, blocks from at least half of the
correct validators — with no synchrony assumption — and once the DAG is
synchronous every correct block enters the agreed ledger within a
schedule-window of its creation, while a six-validator counterexample
shows the same correct validator can be censored for ever without
synchrony, so the upgrade from aggregate to individual inclusion
genuinely costs the synchrony assumption.

On the same foundation, unchanged, we develop eight further machine-checked
accounts, and then compose them. First, **denial-of-service resistance**: safety is shown
independent of any anti-equivocation condition, and a correct validator's
storage is bounded under an enforceable, author-blind *novelty budget* — with
a matching construction showing that any bound from reference-validity
conditions alone carries a constant exponential in the fault bound `f`.
Second, **garbage collection**: a per-validator horizon below which nothing
is retained, with commit verdicts invariant across the cut, storage constant
at a lag, and bootstrap by an `(f+1)`-sampled attested base — no consensus on
the cut anywhere. Third, the two-round protocol **Odontoceti**: safety and
liveness of its commit rule, generalized from the published `n = 5f+1` to
`n ≥ 5f+1`, where the formalization surfaces a gap in the published agreement
argument — two equivocating candidates can both pass the indirect commit test
at one anchor, realized on a concrete six-validator counterexample — and
repairs it with a canonical-candidate rule. Fourth, **reactive
schedules**: both commit rules remain live when validators wait only
until they hold the leader's block — or, under Mysticeti, until they can
certify — with the timeout as a fallback; latency is bounded by actual
propagation with the timeout appearing nowhere, and when delivery
undercuts the timeout no timeout ever fires. Fifth, **safe skip**: a
crashed validator rejoins with one constant-size message denoting a block
for every missed round — a donor's references plus a forced self
reference — with production restored, no commit conjured for slots the
network already passed, and every verdict reached before the fill
re-derived and agreed after it. Sixth, **adaptive leader schedules**:
Hammerhead-style reassignment of the leaders ahead, computed from the
agreed prefix, is proved safe unconditionally — the schedule-and-verdict
fixpoint is unique under no synchrony assumption, for arbitrary adapted
policies — and live exactly when the policy keeps placing runs of
reliable leaders. Seventh, **hybrid fault tolerance**: separating `fb`
Byzantine from `fc` crash-prone validators, the two-round rule is
proved safe and live at `n ≥ 5fb + 3fc + 1` — four validators suffice
for two-round finality under a single crash — with the committee bound
shown to *be* the existence of a working indirect threshold, and
necessary: one validator short, agreement fails on data at every
threshold. Eighth, **crash-fault consensus**: the same commit rule at a
bare majority quorum — the protocol Nemo-Nemo, `n ≥ 2f + 1` with `f`
halting faults — proved safe with *no* fault bound and no side
conditions, and live at the classical bound under a fairness clause the
mechanisation sharpens: a lone committed leader settles almost nothing
below it, and progress requires committed leaders at adjacent rounds.

Finally we ask whether the first seven compose, and answer it by
naming the invariants each consumes and proving the two universe
transformers preserve them: a validator running four mechanisms at once
still cannot disagree about a verdict. What is visible only from the
composition is a set of deployment constraints no single account can
state — a garbage-collection lag bounds the outage a one-message
recovery can span, a horizon must fall on an epoch boundary of an
adaptive schedule, and a validator pruned past its own history is a
reader until it re-genesises, counting against the fault budget
meanwhile.

The development comprises roughly 26,500 lines of Lean 4 over Mathlib. Every
principal result depends on exactly Lean's three standard axioms; every
definition is exercised on concrete models by `decide` before anything is
proved from it. All displayed Lean in this report is drawn from the source
and type-checks against the built library.

---

## 1. Introduction

Byzantine fault-tolerant consensus built over block DAGs has moved from
research prototypes to production blockchains: validators exchange
round-indexed blocks, each referencing a quorum of the previous round, and
read commitment out of the resulting graph. The latest generation of these
protocols — Mysticeti and its descendants — is *uncertified*: no certificate
is ever constructed or sent, and every consensus-relevant fact is a counting
pattern in the graph itself. This makes the protocols unusually well suited
to mechanised verification — the commit rule is finite-set arithmetic — and
unusually exposed to subtle error, because equivocation and availability,
which certification used to discharge, become the reader's problem in every
proof. This report is a machine-checked account, in Lean 4 over Mathlib, of
this protocol family: a core development of safety and liveness organised
around a structural liveness condition we call *eventual DAG synchrony*,
a chain-quality account of what the committed ledger contains, and, on
that unchanged foundation, eight further developments, seven of them composed at the
end — storage bounds
under adversarial equivocation; garbage collection without consensus on
the cut; the safety and liveness of the two-round protocol Odontoceti,
including a repair its published argument requires; reactive schedules
under which consensus proceeds at network speed, with the timeout as a
fallback that a fast network never triggers; and Safe Skip, by which a
crashed validator rejoins production with a single message, with every
prior verdict proved to survive the recovery; adaptive leader
schedules, with the reassignment fixpoint proved unique — safety
needing no synchrony at all — and live under a run-placing policy; and
hybrid fault tolerance, separating Byzantine from crash faults, with
the tight two-round committee bound machine-checked in both
directions; and an integration account in which the arcs are shown to
compose, together with the deployment conditions that only their
composition reveals — including a recovery path for a validator whose
whole history has been pruned, and a choice of message target that
makes recovery transmit nothing at all.

### 1.1 DAG-based consensus

Validators broadcast round-indexed blocks, each referencing a quorum of blocks
from the round below. The resulting structure is a directed acyclic graph, and
consensus is obtained by reading that graph rather than by running a separate
voting protocol.

The variant treated here is *uncertified* in the sense of Mysticeti: there is no
explicit certificate round and no certificate message. A block two rounds above a
leader constitutes a certificate for it precisely when the block's own references
happen to contain a quorum of blocks that reference the leader. Certification is
therefore a property of the graph, discovered by the reader, rather than an
action taken by a writer. This is what permits the entire commit rule to be
expressed as cardinality comparisons over finite sets, and it is what makes the
development below possible with no cryptographic layer.

### 1.2 The synchrony assumption in liveness arguments

Liveness for protocols of this family is conventionally established under a
partial-synchrony assumption stated per message: after a global stabilisation
time, a message between correct parties arrives within a bound Δ. Such an
assumption obliges the argument to reason about the mechanics by which the DAG
is transmitted, in terms of individual messages, when the object being reasoned
about is the DAG itself.

Two costs follow. First, a message-level assumption obliges every subsequent
statement to be quantified over instants, and every lemma to re-establish that
enough has arrived. Second, and more fundamentally, the commit rule does not
mention time at all: it counts references. The resulting mismatch is substantial
proof effort with no corresponding proof content.

### 1.3 Contributions

1. **Eventual DAG synchrony**, formulated structurally as `SynchronisedOn`:
   beyond round `R`, every correct block references every correct block of the
   round below. The statement mentions no clock, no message and no Δ, and it is
   a *derived* property of executions rather than an assumption (§4.4).

2. A machine-checked **safety** development — agreement, uniqueness of the
   committed leader sequence, and non-retraction of the ledger — which assumes
   nothing whatsoever about the network, not even eventual delivery.

3. A machine-checked **liveness** development above the structural condition, in
   which no theorem mentions time. Priority is not claimed: Qiu, Xiao and Shao
   [QXS26] give machine-checked safety and liveness for Mysticeti in Rocq, by
   refinement into LiDO-DAG. What is claimed is the *form* of the account —
   theirs is operational, quantified over traces and instants; here liveness is
   stated as a condition on the DAG, and the dependence on time is
   confined below a `Prop`-valued interface (§6.7, §21).

4. **A derivation** of the structural property from **view convergence**
   (§6.9), together with the protocol's build rules, and nothing beyond
   standard partial synchrony — the network's contribution stated in a
   form containing no clause about what validators do. On the same
   foundation, production is derived too, from round `0` with genesis
   the only seed (`ViewPace.populatedOn` (V17)), so the entire liveness
   account rests on one view-shaped assumption, over a build schedule in
   which *stuck* is expressible.

5. A precise account of the **trust boundary** (§4). What is assumed reduces to
   the fault bound and a single network condition — view convergence — serving
   coverage and production alike; every other condition is a clause of the
   protocol, which a designer controls. In particular reference coverage
   is derived rather than assumed, and the one point at which a network parameter
   constrains the specification is the wait threshold of §20.1.

6. **Quantitative forms** (§6.10): the round from which coverage holds, given
   explicitly; a bound on the slot at which the next commit occurs; and an
   operational statement — a correct leader is committed once every correct
   validator waits `2Δ + proc`, a constant of the network and the
   implementation. No start-spread or deployment quantity appears anywhere:
   the pacemaker's catch-up rule collapses drift to `Δ + proc` at the first
   fully-post-GST round whatever the start spread (§6.11), and at
   instantaneous entry (`proc = 0`) the threshold is the deployed `2Δ`
   timer.

7. **Chain quality** (§7): every commit's flush carries, at every round
   below it, blocks from at least half of the correct validators —
   proved with no synchrony assumption of any kind — and, once the DAG
   is synchronous, every correct block enters the agreed ledger within
   a schedule-window of its creation (`chain_quality`); a
   counterexample shows the aggregate guarantee provably does not
   imply the individual one without synchrony.

8. **Denial-of-service resistance** (§8): with safety shown independent of
   any anti-equivocation condition, storage is bounded twice over — a general
   per-cone bound under an exposure condition on references, with a matching
   construction showing its exponential constant is essentially forced, and a
   **novelty budget** under which a correct validator's store grows linearly
   forever, stated under enforceable, author-blind conditions only
   (`dos_resistance`).

9. **Garbage collection without consensus** (§9): a horizon below which
   stores retain nothing, with commit verdicts proved invariant across the cut
   under a single premise, storage made *constant* at a lag, bootstrap by an
   `f+1`-sampled attested base rather than any agreement on the cut, and the
   lag envelope pinned theorem by theorem.

10. **Odontoceti, formalized and repaired** (§10): safety and liveness of the
   two-round commit rule, generalized from the paper's fixed `n = 5f+1` to
   `n ≥ 5f+1`, on the unmodified DAG layer — together with four findings about
   the paper's safety argument, one of which (agreement among indirect commits
   resting on candidate-iteration order) is refutable on data without a
   canonicity repair the formalisation supplies.

11. **Reactive liveness** (§11): both commit rules proved live under a
   schedule that waits only as long as it must — react on holding the
   leader (or, under Mysticeti, a certificate), fall back to the timeout
   otherwise. The fast path is quantified: round latency is bounded by
   drift, delivery and processing with the timeout absent, and below the
   timeout the fallback branch is never taken.

12. **Safe Skip** (§12): crash recovery in one message. A recovering
   validator's fill — one denoted block per missed round, the donor's
   references plus a self reference the validity clause P3′ forces — is
   proved a block universe; production is restored at every missed round,
   a filled leader candidate is directly skipped, and every verdict
   reached before the fill re-derives and agrees after it
   (`SkipMsg.decided_fill_agree` (SS6)). The fill is moreover *derived,
   not transmitted*: the donor line is the self-parent chain below its
   tip, so the whole denotation is a function of two block names that
   every receiver elaborates locally
   (`JumpMsg.denote_eq_of_core` (SS10)) — round jumping at one message
   of constant size (§12.7).

13. **Adaptive leaders** (§13): a Hammerhead-style schedule — the leaders
   ahead recomputed from the agreed prefix — proved safe and live for both
   commit rules. Safety is uniqueness of the schedule-and-verdict fixpoint,
   with no synchrony or fairness hypothesis of any kind
   (`adaptiveRun_agree` (AL3)); liveness is its existence under the one
   clause that prices the policy (`adaptiveRun_exists` (AL5)); and the
   layer is rule-agnostic, its two-round mirror consuming the policy
   objects unchanged (AL7).

14. **Hybrid fault tolerance** (§14): the two-round rule proved safe and
   live under `fb` Byzantine and `fc` crash-prone validators at
   `n ≥ 5·fb + 3·fc + 1` (Orcaella's bound [KS26]), for every indirect
   threshold in an admissible interval whose nonemptiness *is* the
   committee bound — and the bound proved necessary: one validator
   short, one view derives conflicting verdicts at every threshold
   (`hybrid_bound_necessary` (H10)). Crash-proneness costs no new
   behavioural clause: a crash is absence, and the class enters through
   the cardinality arithmetic and one strengthened non-equivocation
   clause alone.

15. **Crash-fault consensus** (§15): Nemo-Nemo's majority-quorum rule
   [Ker+26] — outside the base fault model, whose committees every other
   arc only tightens — restated over a self-contained crash universe and
   proved safe with no fault bound and no side conditions
   (`Nemo.decided_unique` (NN5)): universal non-equivocation retires the
   twin machinery, and agreement consumes the quorum exactly once.
   Liveness holds at `n ≥ 2f + 1` (`Nemo.all_decided_below_of_fairRun`
   (NN8)) under a fairness clause the mechanisation sharpens: with no
   failure detector the indirect rule cannot settle past an undecided
   slot, a lone committed leader settles only the slot two rounds down,
   and progress requires committed leaders at *adjacent* rounds — which
   round-robin over `2f + 1` supplies by counting.

16. **Integration** (§16): the arcs are shown to compose, by naming the
   invariants each consumes and proving preservation for the two
   universe transformers rather than settling a quadratic matrix — with
   a capstone in which a validator recovered by Safe Skip, then
   truncated, read in the hybrid model under an adaptive schedule still
   cannot disagree about a verdict (`hybrid_agree_stack` (I7)). Four
   kinds of result are visible only here. Coverage is refuted under the
   fill, with an exact boundary and for the same reason the fill is
   safe (I4). Three conditions constrain where a horizon may fall
   (I5, I6). A **re-genesis** provision restores a validator whose
   history was pruned entirely — needing no exemption from P3′, since
   truncation makes the retained layer genesis, and no agreement on the
   cut, since each validator derives its own (I10, I11) — after which
   bootstrap, re-genesis and Safe Skip compose into a full recovery
   (I12). And the storage account is sharpened: the reference
   discipline of §8.4 is stated more tightly than its own bound
   requires (I17), while a fill drawn against a common-core target
   carries no material its recipients lack (I19).

17. **Mahi-Mahi** (§17): the asynchronous protocol's rule — the core's
   at a wave of `w` rounds, votes through the cone — proved safe at every
   `w ≥ 3` and collapsing onto the core at `w = 3` (`MahiMahi.Safety.holds`
   (MM1)), and live with **no synchrony hypothesis** under one clause on
   the schedule and the DAG (`MahiMahi.Liveness.holds` (MM3)): the
   late-revealed leader keeps landing among the candidates the DAG
   commits, a set the core's own common-core lemma bounds below at every
   wave (`MahiMahi.Counting.holds` (MM2)) and synchrony derives from
   fairness (`MahiMahi.Synchrony.holds` (MM5)). The five-round count
   holds for non-equivocating authors only — `1/3` per wave, not the
   paper's `2/3` — and the core's per-candidate skip rule is weaker than
   the implementation's slot blame.

### 1.4 Scope and non-goals

The development is deliberately bounded in four respects — a fifth, the
restriction to unpipelined schedules, has since been lifted and is recorded
first.

- **Pipelining and multiple leaders enter through the schedule, not the
  rule.** The schedule class constrains only monotonicity, unboundedness and
  keying (§3.4); anchoring is governed by per-pair eligibility. Mysticeti's
  every-round pipelining and its multi-leader rounds are instances, with the
  interleaving of simultaneously undecided slots handled by the committed-run
  results (`decided_of_committed_above` (L8d), `decided_below_of_committed_run` (L8e),
  `all_decided_below_of_fairRun` (L10)); `pipelining-and-multi-leader.md` is the
  companion document. A Cordial-Miners-like three-round spacing is the
  special case in which every later slot is eligible
  (`eligible_of_lt_of_spacing`).
- **No cryptography.** Signatures, authentication and equivocation detection are
  outside the model. Non-equivocation of correct validators is a clause of the
  protocol (§4.1), recorded structurally (§2.3) and not enforced by a mechanism.
- **No executions.** The object of study is a DAG together with invariants, not
  a transition system with traces. What an operational model would establish as a
  reachability invariant of the protocol is here recorded as a structural
  condition.
- **No intra-flush ordering.** The committed-leader sequence and the ledger *set*
  are shown agreed; totally ordering the blocks released by a single commit
  requires a tie-break which the development declines to assume (§5.6).
- **No wall-clock latency.** The wait bound of §6.11 is a duration, but the total
  elapsed time to a commit is not derived (§20.6).

### 1.5 Organisation

§2 gives the system model and §3 the commit rule; §4 draws the trust
boundary, separating what is assumed from what the protocol enforces. §5
develops safety (culminating in agreement, `decided_agree`, and the agreed
ledger) and §6 liveness, grounded on view convergence (culminating in
recurring commits, `commits_recur_on`, the three derivations of eventual
DAG synchrony, and the quantitative wait bound). §7 proves the chain-quality account — coverage
without synchrony, inclusion with it (`chain_quality`,
`committed_of_correct_block`).

§§8–15 present eight further developments on that foundation:
denial-of-service resistance (`dos_resistance`); garbage collection
(`decided_agree_chop`, `card_retained_le`, `bootstrap_agree`);
Odontoceti (`Odontoceti.decided_unique`,
`Odontoceti.all_decided_below_of_fairRun`); the reactive schedule
(`ReactiveM.decided` (RS2), `Odontoceti.reactive_decided` (RS3),
`ReactivePace.no_timeout_of_fast` (RS4)); safe-skip recovery
(`SkipMsg.decided_fill_agree` (SS6)); adaptive leader schedules
(`adaptiveRun_agree` (AL3), `adaptiveRun_exists` (AL5)); and hybrid
fault tolerance (`Hybrid.decided_unique` (H6),
`hybrid_bound_necessary` (H10)); and crash-fault consensus
(`Nemo.decided_unique` (NN5), `Nemo.all_decided_below_of_fairRun`
(NN8)). §16 composes the first seven
(`hybrid_agree_stack` (I7)) and collects the deployment conditions
their composition reveals.

§18 exhibits the witness models. §19 describes the mechanisation, §20
discusses the formulation, the lessons of the extensions, and the
limitations, §21 surveys related work, and §22 concludes. Appendix A indexes every
principal statement against its Lean name and module. Throughout, displayed
Lean is drawn from the source; binders are occasionally elided for layout,
and `…` marks an elision.


---

## 2. System model

### 2.1 Validators and the fault model

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  byzantine : Finset Validator
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  card_byzantine : byzantine.card ≤ f

def Correct : Finset Validator := (F.byzantine)ᶜ
```

A quorum is `n − f` for `n ≥ 3f+1` validators — the familiar `2f+1` at the
boundary `n = 3f+1`, where every witness sits. The derived fact
`card_correct : n − f ≤ Correct.card`
records that the correct validators themselves form a quorum. The liveness
development consumes it wherever a `T`-relative result is specialised to
`T := Correct`, and in the production inductions of §6.3 and §6.9.

As a set, `Correct` is a complement and carries no behavioural content. Membership
is satisfied, in particular, by a validator that crashes at round 0 and never
speaks again. This is deliberate: it allows every safety result to hold of
crashed validators. The behaviour of a correct validator is supplied separately,
by the protocol clauses of §4.1, and the reader should keep the two apart —
`Correct` names *which* validators execute the algorithm, while §4.1 says *what*
the algorithm is. Since a crashed validator satisfies the first and not the
second, the liveness development must invoke the protocol clauses explicitly
(§6.0).

### 2.2 Blocks and validity

```lean
structure Block (Validator BlockId Payload : Type*) where
  round : ℕ
  creator : Validator
  refs : Finset BlockId
  payload : Payload
```

Blocks are addressed by identifier: `refs : Finset BlockId` rather than
`Finset Block`. A view and the universe consequently share a single
interpretation function `U.block`, so two validators may disagree about which
blocks they hold but never about what an identifier denotes. `Payload` is opaque
and plays no role.

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card
  self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator
```

Four aspects of the formulation are consequential.

The predecessor condition is stated additively rather than as
`(blk i).round = b.round - 1`. Besides avoiding truncated subtraction on `ℕ`,
this makes the genesis case derivable rather than a separate branch: at round 0
the equation `(blk i).round + 1 = 0` is unsatisfiable, so `refs = ∅` follows
(`ValidWrt.refs_empty_of_round_zero`).

The quorum condition is stated on the *creator set*, not on `refs.card`. This is
the faithful reading of "references a quorum of blocks of the previous
round", which means `n−f` distinct *validators*; `ValidWrt.card_creators` and `ValidWrt.card_refs` relate the two
under the distinctness condition.

`distinct_creators` is consumed by certificate uniqueness (§5.4) and, in the
two-round setting, by twin uniqueness (§10).

`self_parent` — a non-genesis block references *some* block by its own
creator, not a unique one: an equivocator's blocks form a forest of
predecessor chains, and the condition does not collapse it. Mysticeti and
Odontoceti both mandate the clause. The safety development never consumes it, and on the
liveness side it has exactly one consumer: the rotation backbone of the
reactive schedule (RS5, §11.5), whose whole argument is the self-parent
chain. It is indispensable to §8, where that same
chain is what turns per-acceptance budgets into per-round rates and a correct
block's cone into a complete record of its author's acceptances. In §12 the
clause is consumed in the other direction: the safe-skip fill's added self
reference exists to satisfy it.

### 2.3 The block universe and views

```lean
structure BlockUniverse (Validator BlockId Payload : Type*) … where
  ids : Finset BlockId
  block : BlockId → Block Validator BlockId Payload
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ Correct →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j
```

Non-equivocation is stated at the level of the universe, and must be. A
per-view formulation is strictly weaker: two views could each satisfy "at most
one block per correct author per round" while holding *different* such blocks,
which is precisely a correct validator equivocating, with both views
well-formed. Every cross-view result requires the two blocks to be identified as
a single identifier, and only a universe-level statement delivers this. Views
inherit the property, which is why `View` carries no corresponding field.

The condition is independent of the others: duplicating a correct-authored block
under a fresh identifier preserves `complete` and `valid` and violates only
`no_equivocation`.

It is also the sole point at which the behaviour of a correct validator is
recorded on the safety side, and it is a clause of the protocol rather than an
assumption (P5): a correct validator produces one block per round because the
algorithm so directs. Since the object of study is a DAG rather than an
execution (§1.4), the clause appears as a structural condition on the universe;
in an operational model it would be established as an invariant of reachable
states.

```lean
structure View (Validator BlockId Payload : Type*) … (U : BlockUniverse …) where
  ids : Finset BlockId
  subset_ids : ids ⊆ U.ids
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

A view is a downward-closed subset of the universe sharing its interpretation
function, and inherits validity and non-equivocation.

Both `ids` fields are finite sets. Finiteness is not incidental: it is what gives
`authorsAt` a cardinality, and every quorum argument in the development counts
one. It also determines the shape of the growth clause P8 (§6.3).

### 2.4 Causal history

```lean
def RefStepFrom (blk) (i j : BlockId) : Prop := j ∈ (blk i).refs
def ReachesFrom (blk) : BlockId → BlockId → Prop := Relation.ReflTransGen (RefStepFrom blk)
def Reaches (U) : BlockId → BlockId → Prop := ReachesFrom U.block
```

The walk is stated over the block assignment rather than over a universe
type, because it consumes nothing else: `Causality.lean` proves it once, and
both the Byzantine universe here and the crash universe of §15 read it at
their own data. What each supplies is a `CausalStructure` — references stay
inside the population, and a reference sits one round below — which is
everything reachability and the finite cone need. The same hoist serves
production and coverage (§6.3).

### 2.5 Notation, and the labelling scheme

Global symbols, fixed for the whole report:

| Symbol | Meaning |
|:---|:---|
| `n`, `f` | committee size and fault bound; `n ≥ 3f+1` throughout, `n ≥ 5f+1` in §10 |
| `n − f` | the quorum size; `2f+1` at the boundary `n = 3f+1`; spelled `quorumCard Validator` in the Lean (§4.2) |
| `Correct` | the complement of the Byzantine set (§2.1) |
| `r`, `k` | a round; a slot index (§3.4) |
| `U`, `V`, `D` | the block universe, a view, a delivery layer (§2.3, §6.2) |
| `H(b)`, `history U b` | the causal history (cone) of block `b` (§2.4) |
| `Δ`, GST | the post-stabilisation delivery bound and stabilisation time of partial synchrony (§6.8) |
| `R` | the round from which eventual DAG synchrony holds (§6.4) |
| `N` | the growth horizon: production is demanded up to it (§6.3) |
| `κ`, `T` | the novelty budget: analysis-side (guarded) and mechanism-side (author-blind) constants (§8.4) |
| `G`, `Λ` | a garbage-collection horizon round, and its lag behind the current round (§9) |

Results carry alphanumeric labels by area: **T** (structural theorems, §2 and
§5.1–§5.2), **M** (the commit rule, §5.3–§5.6), **L** (liveness, §6), **P**
and **N** and **R** (protocol, network and rate clauses of the trust
boundary, §4), **CQ** (chain quality, §7),
**D**/**C**/**B** (the denial-of-service development, §8),
**G** (garbage collection, §9), **O** (Odontoceti, §10), **RS** (the
reactive schedule, §11), **SS** (safe skip, §12), and **AL** (adaptive
leaders, §13), **H** (hybrid fault tolerance, §14), **NN**
(crash-fault consensus, §15), **I** (integration, §16), and **MM**
(Mahi-Mahi, §17). The labels match
the companion documents and the source comments; Appendix A maps each to its Lean
name and module.

Counting vocabulary:

| Notation | Meaning |
|:---|:---|
| `blocksAt U n` | the identifiers in `U` at round `n` |
| `authorsAt U n` | their creators |
| `creatorsOf U.block s` | the creators of an arbitrary set of identifiers |
| `supporters U b n` | round-`n` authors whose blocks reference `b` |
| `correctSupporters U b n` | those among them that are correct |
| `blames U L n` | round-`n` authors whose blocks omit `L` |

`creatorsOf` is defined on an arbitrary `Finset BlockId` rather than on a
block's references, since the persistence theorem, the commit rule and the
block-level intersection lemma all quantify over identifier sets that are not
any block's references. Such sets carry no distinctness invariant of their own,
which is why every quorum hypothesis in the development is stated on the creator
set: a Byzantine author could otherwise inflate a set with equivocating blocks.

---

## 3. The commit rule

Validators emit a single kind of object, the block of §2.2. Every role described
below is assigned by the reader of the DAG, not by its writer.

### 3.1 Certificates

```lean
def votesIn (U) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => L ∈ (U.block q).refs)

def Certifies (U) (C L : BlockId) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (votesIn U C L)).card

def certificates (U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)
```

A round-`(r+2)` block certifies a round-`r` block `L` exactly when its own
references contain blocks by a quorum of distinct validators, each of which
references `L`.


### 3.2 The direct rules

```lean
def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card
```

A validator applies these to what it holds. The view-relative forms
`DirectCommitIn` and `DirectSkipIn` intersect the relevant sets with `V.ids`;
`directCommit_of_directCommitIn` and `directSkip_of_directSkipIn` record that a
view can only under-report, so that a local judgement is always a genuine
universe-level one and the universe-level theorems apply without recounting.

### 3.3 The indirect rule

A slot which the direct rules leave undecided is settled by examining the causal
history of a later, committed *anchor*.

```lean
def CertifiedIn (U) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C
```

This test is universe-level by design. `certifiedIn_iff_of_view` establishes that
restricting the search to a view holding the anchor yields the same answer, so
nothing is lost; and the universe-level formulation is what makes decisions
monotone under view growth (§6.5). Were the test view-relative, the premise of
the indirect *skip* rule would be anti-monotone, and enlarging a view could
convert a skip into a commit.

### 3.4 The slot schedule

```lean
class Slots (Validator : Type*) where
  slotRound : ℕ → ℕ
  leader : ℕ → Validator
  mono : Monotone slotRound
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  keyed : Function.Injective (fun k => (slotRound k, leader k))

def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

def IsLeaderBlock (U) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

The class constrains the schedule only to be monotone, unbounded in round, and
*keyed* — distinct slots differ in round or in leader. What safety actually
requires of anchoring is per-pair **eligibility**: an anchor's proposal must
clear the slot's decision round, which is Algorithm 3's filter
`r_decision < s.round`. Under the older formalisation's three-round spacing,
every later slot is eligible (`eligible_of_lt_of_spacing`), so the general
relation is conservative over it; and pipelined and multi-leader schedules —
Mysticeti as published — are instances (`Slots.uniform p m`,
`Slots.uniformSingle`), though a backlog of undecided slots is
cleared by a *run* of consecutive commits rather than any single one
(`decided_below_of_committed_run` (L8e), `all_decided_below_of_fairRun` (L10); the design
record is `pipelining-and-multi-leader.md`).

`IsLeaderBlock` characterises the *candidates* for a slot rather than selecting
one. A Byzantine leader may have several; a correct leader has at most one, by
non-equivocation. Quantifying over candidates is what allows the case of an
absent leader to be discharged vacuously (§6.6).

### 3.5 The decision relation

```lean
inductive Decided (U) (V : View …) : ℕ → Option BlockId → Prop
  | directCommit {k L} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  | directSkip {k} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  | indirectCommit {k j A L} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  | indirectSkip {k j A} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

Here `some L` records a commitment and `none` a skip.

The relation is not a function. A decision procedure would recurse upward in
slot index with no *a priori* bound, requiring fuel or partiality for no benefit,
since nothing in the development needs to compute.

The two indirect cases anchor on the nearest **eligible** committed slot above
`k` — not simply the nearest one. Under pipelining the slots immediately above
`k` sit one and two rounds up, where no certificate for `k` is reachable, and
anchoring there would turn one validator's direct commit into another's
indirect skip; the anchor must clear `k`'s decision round (§3.4), which is
Algorithm 3's own filter. For the same reason the intermediate premise
quantifies over the eligible slots between `k` and the anchor only: the
ineligible ones are routinely committed under pipelining, and requiring them
skipped would leave `k` undecidable forever.

The direct reading of "nearest" — that no eligible slot strictly between is
committed — is a negative premise, which an inductive definition cannot carry.
It is stated positively, as the requirement that every eligible slot strictly
between be decided `none`. The two are equivalent, since the sweep decides
every slot it passes, and the positive form keeps every recursive occurrence
strictly positive; guarding the occurrence behind `Eligible` preserves that,
`Eligible` being a predicate on two naturals which does not mention `Decided`.
This formulation is consumed directly in the principal case of the agreement
proof (§5.5).

### 3.6 The ledger

```lean
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g

def ledgerSet (U) (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}

def OutputAt (U) (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b
```

Committing the leader of a slot releases its entire causal history. `OutputAt`
identifies the slot at which a block first enters the ledger. Here `g` ranges
over a validator's assignment of verdicts to slots.

---

## 4. The trust boundary

Three kinds of condition appear in the development, and the report distinguishes
them throughout, because they differ in who controls them.

**Specification.** A *correct* validator is by definition one that executes the
algorithm. The clauses of §4.1 are therefore not hypotheses about an uncertain
world; they are the algorithm, and a designer is free to choose them.

**Fault model.** How many validators fail to execute the algorithm, and how
their number is bounded (§4.2). Assumed.

**Network.** Delivery. The network is adversarial and lies outside the trusted
computing base (§4.3). Assumed.

Logically all of these are antecedents: each is a field of a structure or class,
and every theorem quantifying over a block universe or over the relevant
instances carries it. None is an axiom in the sense of §19, and their joint
satisfiability is a proof obligation discharged by exhibition (§18) rather than
something the logic must be trusted for. The distinction drawn here is
epistemic, not logical, and it is what determines where the trust boundary of
the system actually falls.

### 4.1 The protocol

| | Clause | Formalisation |
|:---|:---|:---|
| P1 | references lie one round below | `ValidWrt.predecessor` |
| P2 | no block cites one author twice | `ValidWrt.distinct_creators` |
| P3 | non-genesis blocks cite `n−f` distinct authors | `ValidWrt.quorum` |
| P3′ | non-genesis blocks cite a block by their own creator | `ValidWrt.self_parent` |
| P4 | a block is held only with its causal history | `BlockUniverse.complete` |
| P5 | one block per round: correct validators do not equivocate | `BlockUniverse.no_equivocation` |
| P6 | the slot schedule is monotone, unbounded and keyed | `Slots.mono`, `Slots.unbounded`, `Slots.keyed` |
| P7 | a validator references everything it accepted | `Delivery.includes` (storage side); `ViewPace.references` (liveness side) |
| P8 | a validator has a genesis block, and builds on holding a quorum | `ViewPace.built_of_le_top` (genesis, at `n = 0`), `ViewPace.advances` |
| P9 | a validator waits a full timeout before building | `ViewPace.waits` |
| P10 | the leader schedule names reliable validators arbitrarily far out | `FairScheduleOn` |
| P11 | seeing a round is entering it: past GST, a held round-`n` block forces entry within `proc` | `PaceCore.catchup` |

The liveness development adds a **store model** — five clauses about a
validator's own holdings, which is the third thing (beside the protocol and
the network) an implementation must supply. They are not bookkeeping: each
excludes a behaviour a deployment could exhibit, and the last two were added
because omitting them let the model describe runs no implementation could
produce (§6.12).

| | Clause | Formalisation |
|:---|:---|:---|
| S1 | a validator holds only blocks that exist | `PaceCore.holds_sub` |
| S2 | holdings are causally closed: a held block's references are held | `PaceCore.holds_closed` |
| S3 | a block references only what its author held when it built | `PaceCore.refs_held` |
| S4 | a validator holds its own block from the moment it built it | `PaceCore.holds_own` |
| S5 | holdings only grow | `PaceCore.holds_mono` |

S4 fails for a validator that crashes before persisting its own block, and S5
for one that garbage collects inside the liveness window — which is why §9's
results are stated over explicit windows. S2 is P4 as a *store* property: a
block whose history is missing can be neither validated (P3 and P3′ read the
referenced blocks) nor built upon, so without the clause the model would
oblige a validator to advance on evidence no implementation could act on, and
adding it therefore *weakens* what is asked. S3 is the converse of P7, and it
is what makes the delivery layer of §8 derivable rather than postulated
(§6.12).

P1–P6 are consumed by the safety development, P7–P11 additionally by liveness;
P3′ by safety never, and by liveness exactly once (RS5, §11.5) — it is indispensable to §8, and consumed again by the fill of §12.

P10 is a joint condition rather than a pure specification: the schedule is the
designer's, but which validators are reliable is not. Round-robin discharges it
whenever the reliable set is of quorum size, since at most `f` of every `n`
consecutive leaders then lie outside it; `rrSlots` witnesses this with a window
of `f + 1` (§18).

**P8 deserves the most emphasis of any clause here**, and is easily mistaken for
a routine one. It states that a correct validator holding a quorum at round `r`
*has* a block at round `r+1`; equivalently, that correct validators do not
advance past a round without building in it. Qiu, Xiao and Shao [QXS26] show
this clause cannot be dropped: with honest validators free to jump over rounds,
they exhibit an infinite execution of Mysticeti in which at most `2f`
certificates are ever created for any round, so no slot is directly committed
and — direct commitment being what the indirect rule rests on — nothing is
committed at all. Their fix is a restriction on round-jumping; Starfish [PMV25]
adds the same condition as pacemaker rule A2, requiring a validator to have
created its round-`(r-1)` block before advancing to round `r`. The clause is also
not automatic in practice: [QXS26] audited the Sui implementation and found it
susceptible to exactly this attack.

So P8 is the point at which the liveness development is conditional on something
that deployed code has been observed not to satisfy. It is nonetheless a clause
of the protocol in the sense of this section — a designer can implement it, and
both cited works tell one how — which is why it appears here rather than in §4.3.
The clause is split into its two halves: `built_of_le_top` at `n = 0` is
genesis, and `advances` is the progress rule. The shape answers [QXS26]
in their own terms, and is worth drawing out. Earlier incarnations of the
clause stated P8 as *block production at a round*: hold a quorum, and a
block exists one round up. `ViewPace` states it as *round advancement*:
hold a quorum at any time, and the validator gets past the round
(`advances`); and every round it reached, it built in
(`built_of_le_top`), with none above (`le_top_of_built`). That pair is
Starfish's pacemaker rule A2 as a structural invariant rather than a side
condition — a validator has its round-`(r−1)` block before advancing to round
`r`, because in this model reaching a round *is* having built there. It is
what makes round-jumping inexpressible rather than merely excluded: the
counterexample of [QXS26] has honest validators skipping rounds, and no
`ViewPace` describes such a run.

The form assumed here remains stronger than either published fix, which
excuse a validator that has already decided round `r'-2` and admit a
*global catchup time* before which the rule need not hold;
`ViewPace.advances` names no deadline but allows no exception. No
minimality is claimed for the clause.

P2 is a second place where the model does not simply transcribe the protocol.
Mysticeti's validity check requires a block to cite `n−f` *distinct* authors at
the round below but does not forbid citing an equivocating author's second block
as well; uniqueness of support is recovered instead by defining a supporter to be
one that references the *first* leader-slot block among its references. P2
forbids the duplicate citation outright, and uniqueness then follows without a
tie-break — this is P2's sole use, in M5′ (§5.4). The two devices agree in
effect, but P2 is the stronger requirement, and a reader comparing the model
against a deployed implementation will find a validity condition Mysticeti does
not impose.

P5 deserves emphasis, since it is conventionally described as an assumption. It
is a clause of the algorithm — a correct validator produces one block per round
because that is what it was told to do — and it is the sole point at which the
behaviour of a correct validator is recorded on the safety side. Nothing else in
the model constrains it, `Correct` being a set complement (§2.1).

P9 is the clause whose *sufficiency* is not under the designer's control: the
timeout may be chosen freely, but whether the chosen value is long enough
depends on the network. §6.10 determines the threshold it must meet — the
constant `2Δ + proc` — and §20.1 discusses the consequences.

P11 is the second pacemaker rule, and the counterpart of `advances`: where
P8 forces a validator forward on a *quorum*, P11 forces it forward on a
*single sighted block*, within the processing bound `proc`. It is the rule
real pacemakers run — Starfish's rule B2 requires a validator to broadcast
and align on advancing a round, not only on creating a block — and it is
what makes drift a derived quantity rather than an assumed one: whatever
the spread between validators' clocks, one post-GST round contracts it to
`Δ + proc` (§6.11), so no start-spread hypothesis survives anywhere in the
development. The clause cannot be exploited by a validator that does not
wait: any valid block certifies a reliable validator that paid the full
timeout bill for every round below it (CU5, §6.11), so the author-blind
form a deployment runs never pulls anyone past the honest schedule.

Like `converges`, the clause is asserted only from `gst` — and for the
same reason. No validator knows GST or `T`; what it runs is the GST-free
clamped rule, *enter a sighted round within `proc`, never before your
own floor*. Past GST the floor provably never delays the entry, so the
clause holds of the run; before GST it may, so an unconditional clause
would over-claim about every real implementation. The gate places the
condition where partial synchrony always places it: on the guarantee,
not on the validator.

### 4.2 The fault model

| | Assumption | Formalisation |
|:---|:---|:---|
| A1 | there are `n ≥ 3f+1` validators | `Faults.card_validators` |
| A2 | at most `f` are Byzantine | `Faults.card_byzantine` |

Byzantine validators are unconstrained: they may publish nothing, publish
selectively, or equivocate freely.

The quorum size `n − f` is written `quorumCard Validator` throughout the
development — notation rather than a definition, deliberately: the term
*is* `Fintype.card Validator - F.f`, so every lemma and every arithmetic
tactic sees the subtraction it always saw, while statements read and
print as the quantity they mean.

**The combined budget.** The principal liveness argument counts to `n−f` and no
higher, so what it requires is a quorum of validators that are both correct and
timely, rather than the participation of every correct one. Formulating this as
`T ⊆ Correct` with `n−f ≤ T.card` — a hypothesis of L4 and L6 — yields the
operative budget:

> `actual_byzantine + persistently_slow_correct ≤ f`

A correct validator which is persistently slow consumes budget exactly as a
Byzantine one does. This is a hybrid condition: correctness is a fault-model
matter, timeliness a network one. At `f = 1` there are four validators and
`|Correct| = 3 = n−f` exactly, so no margin exists and every correct validator
must be timely; margin appears only when fewer than `f` validators are in fact
faulty, and the `T`-parameterised statements make it available automatically.
The specialisations at `T := Correct` (`directCommit_of_correct_leader`,
`decided_of_correct_leader` (L4′), `commits_recur`) recover the conventional
statements.

### 4.3 The network

The development asks the environment for two *things*, and each admits
several *formulations*. Keeping those apart is what this section is for:
the roles are fixed, the formulations are a modelling choice, and two of
the formulations are not as pure as their names suggest.

| Role | What is wanted | Formulation |
|:---|:---|:---|
| **Production** | what exists is eventually obtained, so the DAG keeps growing | view convergence (`converges`, from GST on), with genesis as the only seed |
| **Coverage** | after stabilisation, delivery is prompt enough that blocks reference one another | N2, as `converges` — one sentence about views; `EventuallyDelivers` survives only as the storage arcs' delivery premise |

Safety (§5) uses **none** of them: it holds under arbitrary asynchrony,
arbitrary loss and arbitrarily divergent views.

#### The vehicles

The formulations do not all range over the same object, and the
differences matter more than they appear to.

| Field | Indexed by | Structure |
|:---|:---|:---|
| `held v n` | the **round** `v` is building over | `Delivery` (§6.2), the storage model |
| `holds v t` | the **instant** `t` | `ViewPace` (§6.9), the liveness structure |

`held v n` is what `v` had in hand *at the moment it built its
round-`(n+1)` block* — not what it eventually receives. That build-time
index is the essential modelling device (§20.1): a block's references are
frozen at construction, so what bears on the DAG's shape is what was held
when the builder acted. `View.ids` is a finite set of identifiers with no
index of either kind, which is why no formulation is stated over it.

#### Production

Production is derived, not assumed. The liveness results consume it as a
`PopulatedOn` hypothesis, and `ViewPace.populatedOn` discharges it from
genesis, view convergence and the pacemaker's progress rule (§6.9),
at every round from `0`. The network contributes nothing to production
beyond the one convergence clause it already supplies for coverage; the
only production assumed outright is a round-`0` block, which a validator
produces alone.

#### Coverage: N2, as view convergence

```lean
converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
```

`converges` is partial synchrony as one would state it in words — *after
GST, whatever a correct validator holds reaches every correct validator
within Δ* — and mentions no block, no round and no reference. It is the
whole of what is assumed of the network. The fused shape the retired
timing layer carried as its network row — *a block built after GST and
early enough is referenced* — is derived from it by applying the
protocol's referencing clause P7 (`ViewPace.covers_of_converges` (V1)),
which is where the claim that the network's contribution is one sentence
about views is discharged.

`EventuallyDelivers` concludes about `held v n` — the *build-time*
index — and so presupposes that the builder waited; it carries protocol
content a network assumption should not, which is one reason the routes
stated over it are retired. It survives because the storage arguments of
§§8–9 genuinely consume a post-`R` delivery premise, and for a store —
unlike for coverage — the build-time index is the honest one.

Two further relations, both proved in §6.9. The bound factors out:
convergence within Δ is exactly eventual convergence whose lag is
uniformly bounded after GST (`convergesWithin_iff_bounded` (V4)), so *view
convergence under synchrony = view convergence + a bound*. And eventual
convergence **alone** yields nothing: an unbounded lag cannot be compared
with a timeout, so no argument places the block in the builder's hands
before it builds. The missing ingredient is not a stronger network but
the protocol's waiting rule — which is why P9 stands beside N2 in §4.1
rather than inside it.

#### What none of them says

- **Nothing about Byzantine senders.** A Byzantine validator may deliver
  to some correct validators and not others, may send equivocating blocks
  to two of them, or may publish nothing. Every formulation quantifies
  over *correct* authors only, and safety tolerates the rest
  unconditionally — a Byzantine block reaching one view and not another is
  exactly what the cross-view theorems of §5 are stated to survive.
- **Nothing about which blocks arrive**, beyond correct ones after `R`.
- **Nothing before GST**: arbitrary delay, reordering and loss are
  permitted there, and every safety result continues to hold.

#### Where they are consumed

Neither role is discharged where its name suggests, and the extracted
support graph (§19) makes the pattern checkable rather than asserted.

Production is consumed as a `PopulatedOn` hypothesis: L6, the
committed-run results, the quantitative results and the capstones of
§§7–10 never reach for the assumption that supplies it, and
`ViewPace.populatedOn` discharges it at the point of application.

**`EventuallyDelivers` is consumed by stores, not by coverage**: the
view-gap constant C3′ and hence the budget sandwich of §8.4; the
accepted-quorum lemma (`card_creators_accepted_of_eventuallyDelivers`);
the bound placing the attested base inside a correct peer's retained
store (G6b, §9.3); and the one-round universalisation of possession
(G9, §9.5). All four are facts about **stores**, where coverage is a
fact about **references** — and coverage never reads it.

#### What is actually trusted

Collecting the qualifications, what the environment is trusted with is
narrower than the two-role summary suggests.

*For coverage*, one condition on the environment: view convergence,
bounded after GST.

*For production*, the same condition again, and the deployed behaviour
it rests on is the ordinary one: hold a quorum of distinct authors,
advance — which is precisely `ViewPace`'s `advances`, from which
production at every round follows with genesis the only seed
(`ViewPace.populatedOn`, §6.9). No delivery premise, no clock condition
and no per-round production assumption appears anywhere in it.

*And nothing else.* No condition on the environment appears in the
development beyond these two roles, in one of the formulations above; the
remaining hypotheses of §4.1 are clauses of the algorithm, which a
designer controls. Reference coverage itself — the condition all of
liveness rests on — is not a further assumption but a consequence, which
is the subject of §4.4.

### 4.4 Derived, not assumed

Eventual DAG synchrony is not an assumption of the development. It is a
property of executions, obtained from the network assumption of §4.3
together with clauses of the protocol:

| | From | Result |
|:---|:---|:---|
| Coverage | N2 (`converges`) with P7, P8, P9 and P11 | `ViewPace.synchronisedOn_of_converges` (L7) |
| Production | N2 (`converges`) with P8 and genesis | `ViewPace.populatedOn` (V17) |

It is stated as a hypothesis of L4 and L6 in order to keep those arguments free
of temporal notions (§6.8), and supplied to them by the results above. §20
discusses the formulation.

**What "derived" does and does not mean here.** Coverage is derived
from the network assumption *together with clauses of the protocol* —
P7 and P9, with the pacemaker rules P8 and P11 supplying the drift bound
the race is run against — and is consumed by L4 alongside production,
which comes from P8 and genesis. The claim is therefore not that eventual DAG synchrony holds
in any execution of any DAG protocol; it is that it need not be *postulated*
separately, because the network assumption already standard in this literature,
combined with build rules a designer controls, entails it.

The distinction matters because the corresponding claims in the source literature
have not survived scrutiny. Mysticeti's Lemma 8 and Cordial Miners' Proposition
38 both assert that honest validators are synchronised after GST; [PMV25] reports
that both leave gaps, and [QXS26] shows the gap is not merely expositional — with
round-jumping unrestricted the conclusion is false. The present development is
not exposed to that counterexample, but the reason is P8, which excludes
round-jumping outright (§4.1). Properly read, this is the stronger position: it
identifies precisely which protocol clause the structural condition depends
on, rather than asserting the condition and leaving the price implicit.

### 4.5 Quantitative clauses

The results of §6.10 require the following in addition. All four are further
specification, strengthening clauses already present; none is an assumption
about the world, and no quantity in any of them is set by deployment.

| | Clause | Kind | Yields |
|:---|:---|:---|:---|
| R1 | `Rated timeout`: `∀ n, n ≤ timeout n` | specification | an explicit round `R` |
| R2 | `FairWithin T w`: a `T`-leader within every window of `w` slots | specification | a bounded committing slot |
| R3 | `BoundedSpacing s`: slots at most `s` rounds apart | specification | that slot's round, and a horizon |
| R4 | `∀ n, 2Δ + proc ≤ timeout n` | specification | the wait bound `Delay(Δ)` |

Every result of §5 and §6.1–§6.10 stands without them.

**No deployment quantity exists in the development.** Earlier formulations
carried one: with drift *preserved* rather than established by the schedule,
a bound `D₀` on the round-`0` spread had to be supplied from outside, and it
entered the wait threshold permanently as `Delay(Δ) = D₀ + Δ` — the one
quantity whose value depended on how validators were started rather than on
the network or the specification. The pacemaker's catch-up rule (P11)
eliminates it: the spread collapses to `Δ + proc` at the first
fully-post-GST round whatever its starting value (§6.11), so the threshold
is the constant `2Δ + proc` and nothing anywhere states how the validators
started. Starfish [PMV25] obtains the corresponding statement — its Lemma 4,
that honest validators enter every round past GST within Δ of each other —
from its rule B2 in the same way: a consequence of a pacemaker clause, not a
hypothesis about deployment.

### 4.6 What the adversary may do

The clauses above say what correct validators do and what the network
provides. This section states the complement: the behaviour a Byzantine
validator is permitted, which is everything not excluded above. An
implementation that defends against less than this is defending against
the wrong adversary.

**Equivocate.** P5 (`BlockUniverse.no_equivocation`) quantifies over
`Correct` alone, so a Byzantine author may publish any number of distinct
blocks for one round. Nothing in the safety development limits how many:
§8.1 shows the equivocation degree enters no safety statement, and the
`Utwin6` (O11) model exhibits two blocks by one author each passing
Odontoceti's indirect test against a third (§10.5).

**Withhold entirely.** No clause obliges a Byzantine validator to publish
anything. A Byzantine *leader* may therefore leave its slot undecided,
which is why P10 asks only that reliable leaders recur, and why L5
(skipping) exists.

**Send selectively.** A Byzantine author may deliver a block to some
correct validators and not others, at any time. Every network formulation
in §4.3 is restricted to correct-authored blocks for exactly this reason:
`ViewsConverge` carries the restriction in its statement, and a
formulation that dropped it would be assuming Byzantine validators
behave, which is not an assumption anyone can implement against.

**Reveal late.** Delivery bounds apply from GST and to correct authors. A
Byzantine validator may release a block long after building it, and the
commit rules must — and do — treat a late block as a block.

**Lead any slot.** `Slots.leader` is an arbitrary function; the schedule
is not assumed to favour correct validators. P10 asks only that reliable
leaders appear arbitrarily far out, which a round-robin schedule
discharges whenever the reliable set is of quorum size.

**What the adversary may not do** is exactly three things, and each is
either cryptographic or a counting bound. It may not forge a block under
another validator's name — authorship is taken as authenticated, the one
cryptographic assumption in the development and the only clause of §4
with no Lean counterpart. It may not exceed `f` in number (`Faults`,
§4.2). And under the DoS conditions of §4.7 it may not force a correct
validator to store more than the stated bound.

**The limits are witnessed, not merely stated.** Three models show that
weakening a network hypothesis does not merely block a proof but makes
the conclusion false: `bound_is_necessary_pace` (V10) (the delivery bound cannot be
dropped for coverage), `gst_is_forced_pace` (V11) (the starting round
cannot be dropped), and `reliable_set_is_forced_pace` (V12) (coverage over the
reliable set does not extend to `Correct`). §6.9 gives them in full.

### 4.7 The denial-of-service conditions

§8 assumes four further conditions, none of them about the network. Two
are enforceable by a correct validator acting alone, which is the
property that makes them deployable; the other two are structural.

```lean
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

**D (`DoSValid`) — do not build on an exposed author.** A block never
references a block whose author is already exposed as an equivocator
within the referencing block's own history. Checkable locally, since
exposure is a fact about the cone a validator already holds.

```lean
def UniformBudget (D : Delivery U) (τ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤ τ
```

**The novelty budget — accept nothing that costs more than `T` new
blocks.** `UniformBudget` is the author-blind form and the one an
implementation should use: it consults no identity, so a validator can
enforce it without knowing who is correct. `ByzBudget κ` is the same
bound imposed only on Byzantine-authored blocks; it is what the theory
needs, and `uniform_of_byzBudget` (B6) shows the enforceable form implies it.

```lean
def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n
```

**The reference discipline — reference only what you accepted.** The
converse of P7, and equally a clause an implementation executes. It is
stated more tightly than the storage bound needs: §16.7 shows the pool
argument requires only that a block's references lie inside *some*
correct validator's acceptances, its author's or not.

The distinction matters for deployment: `DoSValid`, `UniformBudget` and
`RefsAccepted` are conduct a validator can follow unilaterally, so the
storage bound of §8.5 rests on nothing an operator must trust others to
do. `ByzBudget` is not, and appears only as the weaker hypothesis the
enforceable one discharges.

### 4.8 Where each assumption is consumed

Extracted from the compiled development rather than compiled by hand: a
result appears against a clause when its proof reaches that clause, by
any path. Read down a column to see what an implementation puts at risk
by violating a clause; read across to see what a result depends on.

| | Clause | Consumed by |
|:---|:---|:---|
| P1 | `ValidWrt.predecessor` | T2, T3, T3a, T3c, M1, M2, M3, M4, M5′, M5, M6, L0, CQ3, CQ5, CQ6, CQ7, C2, D15a, C1′, C3′, B4, B, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G10, G11, G12, G8, G9, SS1, SS2, SS3, SS4, SS5, SS6, SS10, AL3, AL5, AL6, I1, I2, I4–I17, I19 |
| P2 | `ValidWrt.distinct_creators` | M5′, M5, M6, C1′, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G12, G8, O1′, O4′, O5, O6, SS1, SS2, SS3, SS4, SS5, SS6, SS8, SS9, SS10, AL3, AL5, AL6, AL7, H2, H5, H6, I1, I2, I4–I16 |
| P3 | `ValidWrt.quorum` | T3, T3a, T3c, M2, M4, M6, L0, CQ5, CQ6, CQ7, D15a, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G10, G11, G12, G8, SS1, SS2, SS3, SS4, SS5, SS6, AL3, AL5, AL6, I1, I2, I4–I16, I19 |
| P3′ | `ValidWrt.self_parent` | RS5; C1′, C3′, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G11, G12, G8, G9, SS1, SS2, SS3, SS4, SS5, SS6, SS8, SS9, SS10, I1, I2, I4–I17 |
| P4 | `BlockUniverse.complete` | T2, T3, T3a, T3c, M1, M2, M3, M4, M5′, M5, M6, L0, L3, L6, L8b, CQ3, CQ5, CQ6, CQ7, C2, D15a, C1′, C3′, B4, B, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G10, G11, G12, G8, G9, O7, O10, SS1, SS2, SS3, SS4, SS5, SS6, SS10, AL3, AL5, AL6, AL7, H7, I1, I2, I4–I17, I19 |
| P5 | `BlockUniverse.no_equivocation` | T1, T3, T3a, T3c, M1, M2, M3, M4, M5′, M5, M6, RS5, C2, D15a, C1′, B4, B, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G12, G8, O1, O1′, O2, O4′, O5, O6, SS1, SS2, SS3, SS4, SS5, SS6, AL3, AL5, AL6, AL7, I1, I2, I4–I16, I19 |
| P7 | `Delivery.includes` | C3′, B5, G6, G6b, G7, G11, G12, G9; on the liveness side `ViewPace.references`, feeding L7 and V17 |
| P8 | `ViewPace.advances` | V17, and through it every liveness capstone; L11, through `reached` |
| P9 | `ViewPace.waits` | L7, L8a, L9, L11, V17 |
| P10 | `FairScheduleOn` | L6, CQ6 |
| P11 | `PaceCore.catchup` | L11 (CU2), and through it L7, L8a, L9, RS1–RS3, RS5 |
| N2a | `EventuallyDelivers` | C3′, G6b, G7, G9 — store facts only (§4.3) |
| N2 | `ViewPace.converges` | L7, V17, and through them every liveness capstone |
| S1 | `PaceCore.holds_sub` | V18, V19 |
| S2 | `PaceCore.holds_closed` | V18 (`viewAt_ids`) |
| S3 | `PaceCore.refs_held` | V19, V20 |
| S4 | `PaceCore.holds_own` | L7, V17, V18, and through them every liveness capstone |
| S5 | `PaceCore.holds_mono` | L7, V17, V18, and through them every liveness capstone |

Three readings are worth drawing out. **P8's consumers are the
production derivation**: the liveness results take production as a
`PopulatedOn` hypothesis rather than deriving it inline, so the clause is
reached only through `ViewPace.populatedOn` (V17). **P3′ is absent from safety
entirely**, and on the liveness side feeds exactly one result — the
rotation backbone RS5 (§11.5) — beside the DoS, garbage-collection,
safe-skip and integration arcs; the report's claim to that effect is
this table row. **P5 has left the coverage path**: the route's clauses
are stated over any authored block, so non-equivocation identifies
nothing there, and its one liveness consumer is likewise RS5, whose
self-parent chain lands by T1 on the block it claims.

Two absences in the integration column are worth reading. **I3 appears
in no row**: it is the schedule layer, which §16.1 calls universe-
independent, and a clause table over universe conditions is exactly
where a universe-independent result should fail to appear. **I18 is
likewise absent** from every row, being a statement about production
rather than about validity. Neither is an omission; both are the
layering showing through. §16.7 locates the clause's cost as
well as its uses: it is what makes a cone a complete record of its
author's acceptances in §8, and what obliges the fill of §12 to enlarge
a cone past what the donor vouched for. And **P4 and P5 appear almost everywhere**, which is the honest
shape of the development: causal closure and non-equivocation are what
the DAG is, not conditions imposed on it.

---

## 5. Safety

### 5.1 Quorum intersection and non-equivocation

**T0.**
```lean
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : quorumCard Validator ≤ Q₁.card)
    (h₂ : quorumCard Validator ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator)
```

Its block-level counterpart T0′ (`exists_correct_mem_creators_inter`) states that
two identifier sets whose creator sets are quorums share a correct author.

**T1.**
```lean
theorem BlockUniverse.eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ Correct)
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j
```

The statement is organised around the author `v` rather than around
`(U.block i).creator`, since that is the form in which every use site arrives: a
quorum intersection yields a correct validator, and T1 converts two blocks known
to be authored by it into a single identifier.

The composite `BlockUniverse.exists_common_mem_of_quorums` combines the two: two quorum-backed
sets of round-`n` blocks share a *block*. This is the recurring step by which one
layer of certification is removed.

**T2** (`round_le_of_reaches`) states that causal history is non-increasing in
round.

**T6a.**
```lean
theorem View.mem_of_reaches (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids
theorem View.exists_reaches_iff (hc : c ∈ V.ids) :
    (∃ b, b ∈ V.ids ∧ P b ∧ Reaches U c b) ↔ (∃ b, P b ∧ Reaches U c b)
```

Causal history does not escape a view. The second form is what makes a
view-relative certificate search well defined: two validators holding different
views but the same anchor cannot disagree about its outcome.

### 5.2 Persistence

**T3.**
```lean
theorem reaches_of_quorum_support
    {b : BlockId} {r : ℕ} {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : quorumCard Validator ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b
```

Once a quorum of round-`(r+1)` blocks references `b`, every block from round
`r+2` onwards has `b` in its causal history. Neither membership of `b` in the
universe nor its round need be assumed; both follow from the quorum hypothesis
(`mem_ids_and_round_of_quorum_support`).

The bound `r+2` is tight. At `r+1` there is a counterexample: with `f = 1`
and validators `{A,B,C,D}`, let `b` be `A`'s round-`r` block, referenced by
the round-`(r+1)` blocks of `A`, `B` and `C`; `D`'s round-`(r+1)` block may
reference `{B,C,D}`'s round-`r` blocks instead, and since all its references
lie at round `r`, it does not reach `b`. Quorum intersection requires two
reference quorums to compare, and `r+2` is the first round that supplies
them.

Quorum intersection is used exactly once, in the base case; height above that
layer is carried by transitivity alone (`reaches_pred_of_round_le`).

**T3c.**
```lean
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ Correct ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw
```

The sole premise is that some round-`(r+2)` block exists — a fact about the DAG
in hand rather than an assumption that any party makes progress. The proof rests
on a double-counting argument (T3a, `exists_correct_common_support`).

The counting: with `b ≤ f` the number of Byzantine validators, each correct
round-`(r+1)` block names at least `n−f−b` correct round-`r` authors, and
there are `l ≥ 1` such blocks spread over `c = n−b` correct authors, so some
round-`r` author collects support from at least `l(n−f−b)/c` of them. Were
that always below the needed threshold, the arithmetic obligation would
reduce to `c² ≤ f(l+c)`, which `l ≤ c` converts to `c ≤ 2f` — contradicting
`c ≥ n − f ≥ 2f+1`.

### 5.3 Consistency of the direct rules

**M3** (`certificates_eq_empty_of_directSkip`). A directly skipped block has no
certificate anywhere in the universe, not merely none within some view. Given
`n−f` blamers, and since a correct validator cannot appear on both sides
(`blames_inter_supporters_subset_byzantine`), the supporters number at most `2f`
(`card_supporters_le_of_card_blames`), one short of a quorum.

The universe-wide strength is what allows a skip to require no anchor to justify
it, and it is what makes the skip half of M4 unconditional.

**M1** (`not_directCommit_of_directSkip`) follows immediately.

**M2** (`exists_certificate_reaches_of_directCommit`). Once a block is directly
committed, its certificate is unavoidable: every block from round `r+3` onwards
has one in its causal history. The bound is tight, since a round-`(r+2)` block
which is not itself a certificate reaches none. This is the origin of P6.

**M4** (`indirect_agrees_with_direct`). Where the direct rule decides, the
indirect rule agrees. The two halves are asymmetric: the commit half requires the
anchor to lie at round `≥ r+3`, since the certificate must be reachable, whereas
the skip half requires no hypothesis at all, since by M3 no certificate exists
anywhere to be reached.

### 5.4 Certificate uniqueness

**M5′.**
```lean
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

A slot admits at most one certifiable block. This is stronger than the
corresponding statement about direct commits, and it is the form the indirect
rule requires, since that rule commits on the strength of a single certificate
lying in reach rather than of a quorum of them.

The proof requires no relationship between the two certificates. Each names
`n−f` distinct voters, so the voter sets intersect in a correct validator `w`
(T0′); `w`'s unique round-`(r+1)` block votes for both (T1); and P2 forbids one
block from referencing two round-`r` blocks by a single author. This is P2's
only use in the safety development; §4.8's row records where the arcs
consume it.

**M5** (`eq_of_directCommit_of_creator_eq`) follows as a corollary.

### 5.5 Agreement

**M6.**
```lean
theorem decided_agree {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) :
    v₁ = v₂
```

No two validators reach conflicting decisions for a slot, whatever views they
hold and by whichever route they decided. As is conventional, this is a
*no-conflicting-decision* statement: a validator which has not yet decided is not
in disagreement.

The proof (`decided_unique`) is by structural induction on the first derivation.
Of the sixteen pairings of constructors, fifteen close directly — commitment
against commitment by M5′, and the crossings of direct against indirect by the
cross-view form of M1, by `certifiedIn_of_directCommitIn`, or by M3. The
remaining case, indirect commitment against indirect skip, is settled by
trichotomy on the two anchors, and it is here that the positive formulation of
"nearest anchor" (§3.5) is consumed: the negative reading supplies no
sub-derivation on which the induction could rest.


Two corollaries are stated in the form applications require:
`eq_of_decided_commit` (M6′) (no two validators commit different blocks for a slot) and
`not_decided_skip_of_decided_commit` (no validator skips a slot another has
committed).

### 5.6 Ledger stability

**M7.**
```lean
theorem commitSeq_agree
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n

theorem ledgerSet_mono  (h : n ≤ m) : ledgerSet U g n ⊆ ledgerSet U g m
theorem ledgerSet_agree …             : ledgerSet U g₁ n = ledgerSet U g₂ n
theorem outputAt_unique (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂
theorem outputAt_agree  … (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k
```

Two validators which have settled the first `n` slots read off the same sequence
of committed leaders; the ledger grows monotonically; the two validators output
the same set of blocks; and each block enters at exactly one slot, on which they
agree.

None of these statements mentions an order on identifiers. Ordering the blocks
released by a single commit requires a tie-break — a linear order on identifiers
or an equivalent — which the development deliberately does not assume. Whether
and when a block is output requires no order, and it is precisely these
properties that retraction would violate.

---

## 6. Liveness

### 6.0 What liveness requires beyond membership of `Correct`

Membership of `Correct` says which validators execute the algorithm; it says
nothing about what the algorithm does (§2.1). Liveness statements are therefore
vacuous until the relevant protocol clauses are invoked, and three are:

- **(a)** validators produce blocks (P8);
- **(b)** validators wait before building, and enter a round they have
  seen (P9, P11);
- **(c)** the schedule names reliable leaders arbitrarily far out (P10).

Clauses (a) and (b) act in opposition, and the pair P9/P11 brackets them
precisely: `waits` is a floor, requiring that a validator not build too
early; `catchup` is a ceiling, requiring that one which has seen a round
enter it within the processing bound.

Reference coverage is not among them. It is not a clause a validator could
execute, since it refers to `Correct`, which no validator can observe; it is
what (a) and (b) *produce* against a synchronous network, and it is derived
accordingly (§4.4, §20.2).

The chapter is organised around two interface predicates, and every
result above them consumes them as hypotheses rather than reaching for a
network assumption: **production** (`Populated`, §6.3) and **coverage**
(`SynchronisedOn`, §6.4). Both are discharged from a single network
clause, view convergence, in §6.7–§6.9 — by either pacing discipline,
the full-timeout one through coverage and the reactive one (§11) through
the targeted predicates of §6.6.

### 6.1 Density

**L0.**
```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    quorumCard Validator ≤ (authorsAt U n).card
```

If any block exists at round `r`, every round below `r` has at least `n−f`
distinct authors. The result requires no assumption beyond validity. Its content
is not that the DAG grows, but that it cannot grow tall and thin: a single block
high in the DAG forces a quorum of authors at every round beneath it.

### 6.2 The delivery layer

```lean
structure Delivery (U) where
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  accepted : Validator → ℕ → Finset BlockId
  accepted_sub : ∀ v n, accepted v n ⊆ held v n
  accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
    (U.block i).creator = (U.block j).creator → i = j
  accepts_correct : ∀ v ∈ Correct, ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ Correct → a ∈ accepted v n
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs
```

The indexing of `held` is essential: `held v n` denotes what `v` had in hand *at
the moment it built its round-`(n+1)` block*, not what `v` eventually receives.
This is the build-time index which a view cannot supply (§20.1). Between holding
and referencing sits **acceptance** — at most one block per author, correct
blocks always taken — which is deliberately where the protocol may refuse:
the DoS arc's novelty budget (§8) is a rule about `accepted`, and the
liveness development reads only `accepted`.

The structure contains no clock. In the absence of a time model, "waited longer"
can manifest only as a larger `held`.

**This structure carries no liveness.** It is the storage and acceptance
model: the DoS arc's budgets (§8) and the garbage-collection windows (§9)
are stated over it, `EventuallyDelivers` (§6.4) feeds their post-`R`
increments, and P7's untimed incarnation is its `includes` clause. The
liveness development never reads it — production and coverage come from
the timed route of §6.9, whose `holds` is indexed by *time* rather than by
round, which is exactly the index this structure cannot supply (§20.1).

### 6.3 Progress, and the horizon

```lean
def PopulatedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ ids, (blk b).creator = v ∧ (blk b).round = r

def PopulatedOn (U) (T : Finset Validator) (r : ℕ) : Prop :=
  PopulatedFrom U.block U.ids T r
```

The predicate is stated over a raw block assignment and id population
(`Participation.lean`), neither of which mentions validity, quorums or a
fault model, so every universe type instantiates one definition rather
than restating it: `PopulatedOn` is the `BlockUniverse` instance, and the
crash universe of §15 takes the same predicate.

`PopulatedOn` is the production half of the liveness interface (§6.7):
every result above this section takes production as a hypothesis — over
`T`, from the synchrony round on — and it is discharged by the derivation
of §6.9, which runs the pacemaker's progress rule against blocks that
convergence places in the builder's hands, from a seed that is genesis
alone.

The horizon `N` is not a technical convenience. Since `U.ids` is finite, a
formulation demanding blocks at every round unconditionally would require
infinitely many distinct blocks in a finite set, so that no universe
satisfies it and every theorem assuming it is vacuous. An early
formulation of the production clause had exactly that flaw, caught by
sitting down to write its witness (§18).

Three consequences follow.

First, `N` is a demand upon the DAG rather than a bound upon it:
production to horizon `N` requires that correct validators actually
possess blocks at every round up to `N`, so that a larger `N` is a
*stronger* hypothesis satisfied by *fewer* universes. Generality is
obtained by universal quantification over `N`, not by choosing it large.

Second, `N` and `R` measure independent quantities — extent and quality
respectively — and all four combinations occur.

All four combinations occur: `N` large with `R` small is a tall,
synchronous DAG that commits; `N` large with `R` large (or with coverage
never holding) grows for ever and commits nothing; `N` small with `R` small
is synchronous but too short to commit; `N` small with `R` large is short
and asynchronous.

Third, unboundedness becomes a property of a *family* of universes. The assertion
that the ledger grows without bound is not that one DAG commits infinitely often
— no finite DAG can — but that no slot is the last one which some sufficiently
grown DAG commits.

The horizon is consumed exactly where production is derived — the
induction of §6.9; L4 itself never mentions `N`.

### 6.4 Eventual DAG synchrony

```lean
def SynchronisedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ ids, (blk b).round = n + 1 → (blk b).creator ∈ T →
    ∀ a ∈ ids, (blk a).round = n → (blk a).creator ∈ T → a ∈ (blk b).refs

def SynchronisedOn (U) (T : Finset Validator) (R : ℕ) : Prop :=
  SynchronisedFrom U.block U.ids T R
```

Coverage is hoisted for the same reason as production, and instantiated
the same way.

The condition is restricted to correct authors on both sides, and both
restrictions are consequential.

Nothing may be assumed about the existence of Byzantine blocks: a Byzantine
validator may publish nothing, or publish and reveal selectively, so no argument
may depend upon its blocks being available. Nothing need be assumed either, since
the commitment argument counts only correct certificates and the correct
validators form a quorum. The stronger reading — that every block is referenced —
would amount to assuming that Byzantine validators behave.

Well-formedness survives the restriction: a correct block referencing every
correct block of the round below already names at least `n−f` distinct creators,
so P3 is satisfied without any Byzantine reference.

The predicate is antitone in `T` (`SynchronisedOn.mono`), which allows results
established at `T := Correct` to be supplied to the quorum-relative statements of
§6.6.

The condition is derived, not assumed (§4.4); §20 discusses its formulation.

### 6.5 Monotonicity and propagation

**L2.**
```lean
theorem decided_mono (hsub : V.ids ⊆ V'.ids) (h : Decided U V k v) : Decided U V' k v
```

A validator never revises a decision as its view grows. This is to be
distinguished from the safety results: those establish that decisions do not
*conflict*, whereas this establishes that they do not *change*. The proof rests on
the universe-level formulation of the indirect test (§3.3).

**L3.**
```lean
def View.full (U) : View Validator BlockId Payload U   -- ids := U.ids
theorem decided_full (h : Decided U V k v) : Decided U (View.full U) k v
```

Every verdict reached on any view holds on the full view. Since the full view is
every correct validator's eventual view, this is the formal content of the
informal claim that all correct validators eventually reach the same decision. It
also fixes the interpretation of `U`: not every block anyone ever wrote, but every
block some correct validator ever held. A Byzantine block revealed to nobody is
simply not in the universe.

### 6.6 Commitment, skipping and recurrence

**L4.**
```lean
theorem directCommit_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

with `decided_of_leader_mem` giving the corresponding statement about `Decided`.

The intermediate step, `certifies_of_synchronisedOn` — a correct round-`(r+2)`
block certifies any correct round-`r` block — is the statement appearing as Lemma
10 of Mysticeti, that after GST every honest validator eventually creates a
certificate for a leader block created by an honest validator. That lemma is the
one Sailfish identified as flawed and [QXS26] refuted outright. It is a theorem
here, and its hypotheses show why: `PopulatedOn` at rounds `r+1` and `r+2`
requires *every* validator of `T` to have a block at those rounds, and the
counterexample of [QXS26] is precisely a countermodel to that, arranging for only
`f+2` to `f+3` of the `2f+1` honest validators to build in any given round. The
counterexample therefore refutes neither L4 nor anything else below; what it
refutes is the availability of L4's hypothesis under Mysticeti as published, and
so, in the terms of §4.1, it refutes P8 (§4.4).

The argument consists of two applications of coverage and nothing further. Every
correct round-`(r+1)` block references `L`, since `L` is correct-authored and
coverage applies at round `r`; every correct round-`(r+2)` block references all
of those, so its votes for `L` originate with every correct validator and hence
with a quorum, and it certifies (`certifies_of_synchronisedOn`); and since the
correct validators form a quorum, the certificates themselves do. The round-level
form `directCommit_of_synchronisedOn` is stated without reference to `Slots`,
since nothing in the argument depends on `L` being a leader block.

The hypotheses are three local population facts. Neither the horizon, nor growth,
nor any limiting construction appears.

**The commit argument is factored through what the rule counts.** Two
predicates name the targeted half of coverage — the only part the commit
rules read:

```lean
def VotesAt (U) (T) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 1 → L ∈ (U.block c).refs

def CertifiesAt (U) (T) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 2 → Certifies U c L
```

and one counting theorem per rule consumes them —
`directCommit_of_certifiesAt` here, `directCommit_of_votesAt` for the
two-round rule of §10 — with production supplying the blocks counted.
Coverage implies both predicates (`votesAt_of_synchronisedOn`,
`certifiesAt_of_synchronisedOn`), which is how L4's proof runs; and the
reactive schedule of §11 supplies them *directly*, without coverage, from
its wait clauses. The two pacing disciplines therefore meet at this
interface: one commit argument, two suppliers.

**L5.**
```lean
theorem decided_none_of_leader_absent {V : View …}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none
```

If the leader of a slot published nothing, every view decides `none`. The premise
of `Decided.directSkip` quantifies over candidates and is therefore satisfied
vacuously; a formulation which selected a distinguished leader block would have
had nothing to select.

**L6.**
```lean
def FairScheduleOn (T : Finset Validator) : Prop := ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T

def CommitsAt (BlockId) (Payload) (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ U N, (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)

theorem commits_recur_on (hT : T ⊆ Correct)
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧ CommitsAt BlockId Payload T R k'
```

The order of quantification carries the content. The alternative reading — that
given a universe populated to `N`, for every `k` there exists a committing
`k' ≥ k` with `slotRound k' + 2 ≤ N` — is false: fairness promises a correct
leader somewhere beyond `k`, and that slot may lie beyond the horizon, with
nothing to license requesting a nearer one. As stated, `k'` depends only upon
the schedule, which is a property of the `Slots` instance and not of any DAG;
the universe is then required to have grown far enough. This is also the
correct reading of the claim that the ledger grows without bound (§6.3).

The unboundedness of slot rounds required by the proof is `Slots.unbounded`,
with `Slots.mono` carrying it past the fair slot; three-round spacing, which
once supplied both, is not assumed (§3.4).

### 6.7 The interface: production and coverage

Every liveness result above this line consumes exactly two conditions,
and names no route to either:

```lean
def CommitsAt (BlockId) [DecidableEq BlockId] (Payload) [S : Slots Validator]
    (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ U N, (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

Production over `T` from the synchrony round on, and coverage over `T`
from the same round — both `Prop`s about a block universe, so the
interface is a statement rather than a module boundary. §6.9 derives
both; everything in §6.6 consumes them; and the two quantified halves
are relative to the *same* `T`, which is what lets the whole account run
at any quorum-sized reliable set rather than at all of `Correct`
(§6.9's closing discussion).

Both pacing disciplines supply the interface: the full-timeout
discipline of §6.9 derives coverage and production outright, and the
reactive discipline of §11 derives production and the targeted
predicates of §6.6, which the commit arguments consume in coverage's
place.

`Delivery` (§6.2) is the storage and acceptance model — no longer an
independent assumption, since a pacing structure induces one (V19, §6.12) —
the DoS budgets
of §8 and the garbage-collection windows of §9 are stated over it — and
`EventuallyDelivers` is the post-`R` delivery premise of their
incremental bounds. Neither is consumed by any liveness result.

### 6.8 The layering

![**The core account: what supports what.** Every arrow is extracted from the compiled Lean environment — `A → B` means `A` is used in the proof of `B`, directly or through unlabelled lemmas, with arrows implied by longer paths removed. Assumptions occupy the left column; each further column is one step from them. A box with no incoming arrow depends only on definitions and unlabelled lemmas; L4 is the notable case, taking its quorum as a hypothesis rather than from the fault model. §19 describes the extraction; a version carrying each result's Lean name is in `docs/depgraph/`.](depgraph/support-core-compact.svg)

No theorem above `SynchronisedOn` mentions time, and no theorem below it
mentions certificates. The diagram also locates the trust boundary: the
leftmost column is the whole of what is assumed, and it divides into the
one assumption about an adversarial network (N2, as `converges`) and
clauses of the algorithm (P1–P10).

**Three separations, different in kind.** The development draws three
lines; only the first is the one usually meant by "confining the time
model".

*Time from graph structure* — the interface of §6.7. Everything above it
is finite combinatorics over a DAG; everything that mentions an instant
lies below. Extraction confirms the division: every labelled result that
mentions a clock lies below the interface — the view-pace family
(V1–V17), catch-up (CU1–CU4) and the reactive schedule (RS1–RS5) — and
none above it does. Every theorem of `ViewPace.lean` that concludes
anything used above the line does so by first establishing
`SynchronisedOn` or `PopulatedOn`. This is the separation the report's
title claims, and the diagram shows it as a column that every liveness
result passes through.

*Network from protocol* — the interface is the pair
`converges` / `references` of §6.9. `converges` mentions no blocks,
rounds or references — it is one sentence about views — and the step
from views to references is the protocol's clause P7. That the fused
covers-shape is derivable from the pair is V1
(`ViewPace.covers_of_converges`), and it is where §4.3's claim that the
network's whole contribution is one sentence about views is discharged.

*Assumed from derived* — production. The structure carries no block
function: `built_of_le_top` at `n = 0` is genesis, which a validator
satisfies alone, and every round above is a consequence of the progress
rule and convergence (`ViewPace.reached`, §6.9). Production is assumed
at one round, and that round needs no network.

### 6.9 The route: view convergence over a partial schedule

*(module `LeanDag/ViewPace.lean`; witnesses in `LeanDagTest/ViewPace.lean`)*

The network assumption is **view convergence** — after GST, whatever a
correct validator holds reaches every correct validator within `delay` —
and it is stated over a build schedule that can be *stuck*:

```lean
structure PaceCore (U) (T : Finset Validator) (N : ℕ) where
  top : Validator → ℕ
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  le_top_of_built : ∀ v ∈ T, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round ≤ top v
  holds : Validator → ℕ → Finset BlockId
  holds_sub : ∀ v, ∀ t, holds v t ⊆ U.ids
  holds_closed : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t,
    ∀ j ∈ (U.block b).refs, j ∈ holds v t
  refs_held : ∀ v ∈ T, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ holds v (built v (n + 1))
  holds_own : …
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  advances : ∀ v ∈ T, ∀ n < N, ∀ t,
    quorumCard Validator ≤ (authorsIn U (holds v t) n).card → n < top v
  proc : ℕ
  catchup : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator ∈ T → (U.block b).round = n →
    ∀ t, gst ≤ t → b ∈ holds v t → n ≤ top v ∧ built v n ≤ t + proc

structure ViewPace (U) (T : Finset Validator) (N : ℕ) extends PaceCore U T N where
  waits : ∀ v ∈ T, ∀ n < top v, built v n + timeout n ≤ built v (n + 1)
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs
```

(`timeout_pos`, `latest` and `built_le_latest` are elided; `latest` is an
upper bound production reads for a common time, and nothing else
consults it.)

The split is by role, and it is the trunk both pacing disciplines
share. `PaceCore` carries what production and drift consume — the
partial schedule, the views, the network's clause, and the pacemaker's
two rules: `advances` (P8), forcing a validator forward on a quorum, and
`catchup` (P11), forcing it forward on a single sighted block within the
processing bound `proc` — and nothing about *when* a validator chooses
to build within a round; `reached`, `populatedOn` and the drift collapse
are proved on it, once. `ViewPace` is the full-timeout discipline: the
waiting floor P9 and global referencing. The reactive schedule (§11)
extends the same trunk with a deadline in place of the floor, and
inherits production and drift rather than assuming them.

`top v` is the highest round `v` reached; `built v n` is read only at
`n ≤ top v`, and rounds above were never built. The two `top` clauses
say `v`'s blocks are exactly rounds `0` through `top v` — at `n = 0` the
first is genesis, which needs no network. The schedule clause `waits`
(P9) is guarded by `n < top v`, since a round never reached has no build
time worth constraining.

**Stuck is expressible, and that is why the structure exists.** A total
build schedule assigns a time to every round whether or not the
validator could build there, so it cannot distinguish *stuck at round
`n`* from *built round `n+1` with no quorum*, and a coverage argument
over it requires a side condition on the round straddling GST. The
pacemaker's own rule replaces it: `advances` says a
validator holding a quorum of distinct round-`n` authors — **at any time
whatever** — gets past round `n`. Its trigger is
`authorsIn U (holds v t) n`, the distinct authors of the round-`n`
blocks among `v`'s holdings — an image, so an equivocator's duplicates
collapse and the count is of validators, not blocks. Over the whole
universe the same measure is `authorsAt`
(`authorsAt_eq_authorsIn`), so L0's density and the progress rule's
trigger are one quantity read off two sets. Conditional on the quorum, so it
asserts no production; naming no time, so there is no deadline to miss
and nothing for a schedule hypothesis to protect. A validator racing
ahead of the network before GST is not excluded by assumption; it is not
expressible, since one that never held a quorum at round `n` never
reached round `n+1`. `ugrowStuckPace_stuck` exhibits the state the total
schedule could not: a `ViewPace` satisfied by an execution that has
genuinely halted — horizon `5`, `top = 0`, round `1` unpopulated — with
the quorum bound the only thing keeping it out of the production
theorem, its `T` being a single validator.

`advances` and `built_of_le_top` together are P8, and this incarnation
answers [QXS26] in their own terms (§4.1): reaching a round *is* having
built there, so Starfish's pacemaker rule A2 holds as a structural
invariant and the round-jumping counterexample is inexpressible.

**The separation, V1.** The fused covers-shape — *a `T`-block built
after GST and early enough is referenced*, a network guarantee and a
protocol clause in one sentence — is derivable from `converges` and
`references` alone:

```lean
theorem covers_of_converges {n : ℕ} (hn : n < N)
    (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T) (hcr : (U.block c).round = n + 1)
    (ha : a ∈ U.ids) (haT : (U.block a).creator ∈ T) (har : (U.block a).round = n)
    (hgst : vp.gst ≤ vp.built ((U.block a).creator) n)
    (hearly : vp.built ((U.block a).creator) n + vp.delay ≤
      vp.built ((U.block c).creator) (n + 1)) :
    a ∈ (U.block c).refs
```

The block is in its author's hands when built (`holds_own`), reaches the
builder within `delay` (`converges`), is still there when the builder
acts (`holds_mono`), and is therefore referenced (`references`). No
counting, no drift, no waiting rule — those enter only to discharge the
arrival-before-build hypothesis, which is the race the drift argument
wins. Because `references` and `holds_own` are stated over any block a
validator authored, there is nothing to identify by non-equivocation,
and `T ⊆ Correct` is not consumed anywhere in the coverage half.

**Coverage — drift-free.**

```lean
theorem synchronisedOn_of_converges {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    SynchronisedOn U T R
```

read as: *after GST, once the timeout clears `2Δ + proc`*. Only
`gst ≤ R` is the network's; no drift bound and no start spread appear,
because drift is **derived** from catch-up —

```lean
theorem driftOn_of_catchup (vp : ViewPace U T N) {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R) :
    DriftOn vp.built T R (vp.delay + vp.proc) N
```

— the collapsed spread `Δ + proc`, from any `R` past GST, with no
hypothesis about the start (§6.11 gives the collapse itself, on the
trunk). The race is then run against that constant by the coverage
engine `synchronisedOn_of_driftOn`, which takes an *arbitrary* drift
bound `D` and the backoff `D + delay ≤ timeout`. The engine consumes
neither production, nor the quorum bound, nor `T ⊆ Correct`; the
headline consumes the quorum, which is what feeds the collapse — and the
engine stays public precisely for reliable sets below the quorum, where
drift must be supplied from outside (V12 below runs on a two-member
`T`). The round guards that the partial schedule imposes are discharged
by `reached` (below) rather than assumed.

"After GST" alone is **not** the hypothesis, and the factoring makes the
reason precise. `converges` is partial synchrony in its usual two-part
shape: qualitatively, holdings converge at all (`ConvergesEventually`);
quantitatively, from `gst` on the lag is uniformly at most `delay`
(`ConvergesWithin`), and `convergesWithin_iff_bounded` (V4) is the
factoring. The bound is not decoration — a lag that merely exists cannot
be compared with a timeout, and `D + delay ≤ timeout n` is where the
comparison happens.

**Production — on the trunk, once.**

```lean
theorem PaceCore.reached (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, ∀ v ∈ T, n ≤ pc.top v

theorem PaceCore.populatedOn (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, PopulatedOn U T n
```

Stated on `PaceCore`, so every pacing discipline inherits both — the
full-timeout one below, the reactive one in §11. From genesis,
convergence and the progress rule, and from nothing else:
no drift, no backoff, not even `timeout`, since with no deadline there
is nothing to beat. The induction: each `w ∈ T` reached round `n`, so
holds its own block there; `holds_mono` carries it to a common time past
`gst`; `converges` puts a quorum of distinct round-`n` authors in `v`'s
hands; `advances` fires. `reached` is also the answer to what a wait
bound means on a schedule that can be stuck: with `T` a quorum and the
progress rule, no `T`-validator is stuck below the horizon — as a
theorem, where the total schedule had it as the shape of a field.

**The spine.**

```lean
theorem commits_recur_via_pace (hT : T ⊆ Correct)
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ U N (vp : ViewPace U T N),
        vp.gst ≤ R →
        (∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L)
```

The chain

    view convergence + P7 + P8 + P9 + P11  ⟹  production and coverage  ⟹  commits

is the proof: production and coverage are derived and handed to L6
(`commits_recur_on`), whose quantifier order is preserved — the slot is
fixed by the schedule and the bound alone, before any execution is
named.

`T` need not be all of `Correct`. What is required of the world is that
**some `n − f` correct validators converge in view** — the rest may be
starved, partitioned or silent for the whole run. That is weaker than
partial synchrony in its usual form, which stabilises every
correct-to-correct link, and the gap is real (V12 below). It is a
genuine weakening only below full fault load: `reliable_eq_correct`
shows that at `|byzantine| = f` the conditions `T ⊆ Correct` and
`n − f ≤ T.card` force `T = Correct`, so the `T := Correct`
instantiation is not a restriction but the one always available.

**The limits are witnessed, not merely stated.** Three models — each a
`ViewPace` over the `Uomit` construction, certifying every clause field
by field — show that weakening a hypothesis does not merely block the
proof but makes the conclusion false:

* **V10** (`bound_is_necessary_pace`): holdings converge from time `0`
  over all of `Correct` (`ugapPace_convergesEventually`), every clause
  holds, and coverage fails at every round below the horizon. The bound
  in `converges` is what carries coverage; the qualitative half alone
  carries none of it.
* **V11** (`gst_is_forced_pace`): the same instance satisfies the drift
  and backoff hypotheses of the coverage engine at `R = 0` outright —
  spread `3`, `3 + 1 ≤ 4` — and the headline's quorum bound too; coverage
  at `0` is false, and only `gst ≤ 0` fails, so the GST side condition is
  the working hypothesis, forced rather than chosen.
* **V12** (`reliable_set_is_forced_pace`): with `T = {1, 2}` a proper
  subset of `Correct` over a DAG withholding validator `3`'s blocks from
  everyone's references, coverage over `T` is *derived* — through a
  route that asks neither `T ⊆ Correct` nor a quorum for that half —
  and coverage over `Correct` is *false*, the second statement being
  about the DAG alone. The `T`-relativisation is a property of the
  setting, and the weakening above has content.

### 6.10 Quantitative results

The structure-free rated hypotheses live in `Quantitative.lean`; the
results they pin are stated over the structure in `ViewPace.lean`. Each
strengthens a result above under a strengthened clause (§4.5); a reader
declining those clauses retains §6.1–§6.9 intact.

**The weak hypotheses admit no bound.** The recurrence results conclude
with a bare existential, and this is not a deficiency of the proofs:
each governing hypothesis has the same form, and under such hypotheses
no bound exists. A backoff clearing every threshold *eventually* admits
`timeout n = ⌊log₂(n+1)⌋`, which needs `n ≥ 2^(D+delay) − 1` to clear
the threshold; `FairScheduleOn T` admits a schedule naming `T`-leaders
at slots `0, 10, 1000, …`. A bound therefore requires a *rated*
hypothesis rather than a better proof.

**The round of coverage.**
```lean
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n

theorem synchronisedOn_of_rate (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hrate : Rated vp.timeout) :
    SynchronisedOn U T (max (2 * vp.delay + vp.proc) vp.gst)
```

Each term of the maximum is interpretable: the threshold the timeout
must clear, and GST — no base round and no measured spread, since the
rated timeout clears the constant threshold from the round the threshold
itself names. A hypothesis is removed as well as added —
`backoff_ge_of_rate` requires no monotonicity, the bound at `n` deriving
from `n` itself and so being incapable of lapsing — and
`unbounded_of_rated` confirms that `Rated` strengthens the hypothesis it
replaces.

**The committing slot, and its round.**
```lean
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T

theorem commits_recur_within … (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k R ≤ k' ∧ k' < max k R + w ∧ R ≤ S.slotRound k' ∧ …

theorem commits_recur_by_round … (hs : BoundedSpacing s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k R) + s * w ∧ …
      S.slotRound (max k R) + s * w + 2 ≤ N → …
```

`FairWithin.fairScheduleOn` records that the rated schedule is a fair
one, so that L6 applies unchanged.

`BoundedSpacing` has no counterpart among the weak hypotheses.
Eligibility bounds an anchor's round from *below*, which is what safety
requires, the anchor of M4 being obliged to clear the decision round. A
latency claim requires the opposite bound, and the class provides none,
no safety result having occasion to ask for one. Supplying the mirror
image is what converts a bound on the slot index into a bound on its
round.

**The wait bound.**
```lean
theorem directCommit_of_wait (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

> Beyond GST, if every reliable validator waits at least `2Δ + proc`
> before building, every correct leader is committed.

Thus `Delay(Δ) = 2Δ + proc`, a constant of the network and the
implementation, with nothing anywhere stating how the validators
started; `decided_of_wait` gives the corresponding statement about
`Decided`. Production is derived, so nothing asserts blocks above round
`0`, and `T ⊆ Correct` is not consumed.

The timeout is here a *constant*: no backoff, no rate condition, no
monotonicity and no existential round appear. This locates the role of
the backoff precisely. A backoff is required only because Δ is unknown;
a validator in possession of the delivery bound requires no adaptation
whatever.

The shape of the constant merits comment. `Δ + proc` is the collapsed
spread — what catch-up leaves between any two validators' entries into a
post-GST round (§6.11) — and the further `Δ` is the delivery of the
block to be referenced; the threshold is their sum, and it degrades
linearly in the processing bound and in nothing else. At instantaneous
entry it admits an external check: `directCommit_of_wait_two_delay`
specialises `proc = 0` to a threshold of `2Δ` — and Starfish [PMV25],
designing a pacemaker for this family rather than deriving a threshold,
fixes its block-creation timeout at `δ_TO = 2Δ`, Mysticeti's own
creation rule using a `2Δ` timer likewise. The constant obtained here as
a derived requirement is the one independently arrived at as a design
choice, met by the deployed timers exactly when processing is negligible
against delivery.

### 6.11 Catch-up: the drift collapse

*(clause and collapse in `LeanDag/ViewPace.lean`; witnesses in
`LeanDagTest/Catchup.lean`, `LeanDagTest/Collapse.lean`)*

The schedule alone does not contract drift. Under `waits` every clock
advances by the same timeout, so the spread between validators is
preserved, not compressed — the intuition that it shrinks as the
protocol reaches synchrony is false of the timeout discipline by itself,
since the network converging moves nobody's clock. What contracts it is
the trunk's second pacemaker rule, `catchup` (P11, displayed in §6.9):
*seeing evidence of a round is entering it*, stated off any `T`-authored
block and saying one thing more than a total schedule could — seeing a
round means **reaching** it, which is exactly what a real pacemaker's
catch-up does. The collapse is immediate and total, proved on the trunk
so both pacing disciplines inherit it:

**CU2.**
```lean
theorem drift_collapse {n : ℕ} (hn : n ≤ N)
    (htop : ∀ u ∈ T, n ≤ pc.top u)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    ∀ v ∈ T, ∀ w ∈ T, pc.built v n ≤ pc.built w n + (pc.delay + pc.proc)
```

No hypothesis mentions the previous spread. The laggard cannot stay
behind: the earliest builder's block reaches it within `Δ`, and catch-up
converts the sighting into entry within `proc`. The contraction happens
in one round, not gradually, and `driftOn_of_catchup` (L11) puts it in
the form the coverage engine consumes — `DriftOn` at the constant
`Δ + proc`, from any `R` past GST, the quorum bound discharging the
round guards through `reached`. This is what makes every headline of
§6.9–§6.10 drift-free: the spread the race is run against is a derived
constant, not an assumed quantity (CU3, the deployment-free threshold
`2Δ + proc`, is thereby the main line's own wait bound, L9).

**The bound is exact from both sides.** `ugrowSkew_spread_constant`
(CU1) shows the running witness carrying a spread of exactly
`Δ + proc = 2` at every round, for ever: the collapse contracts any
larger spread down to the bound, and nothing contracts past it. And
`ugrowLag` (CU4) shows the contraction itself: a round-`0` spread of
`10` — admissible because GST has not yet arrived and no evidence has
crossed — collapsing to exactly `Δ + proc = 3` at round `1`, where the
laggard's `waits` floor and its catch-up deadline meet with no slack
(`ugrowLag_collapse`). The same run commits a slot at timeout
`5 = 2Δ + proc` (`ugrowLag_decided`), the spread of `10` appearing in no
hypothesis. This also settles that `catchup` and `waits` are jointly
satisfiable *from* a large spread, not only near synchrony: the floor
and the deadline are in genuine tension — one holds a validator back,
the other pulls it forward — and the witness threads both exactly.

**The rush bound: the clause cannot be exploited (CU5).** The pacemaker
rules are stated over `T`, but `T` is an analysis-side object no
validator can test membership of, so a deployment runs the author-blind
strengthening: catch up on *any* valid block sighted. The worry that
raises is being rushed — a Byzantine validator, by not waiting, dragging
correct validators past their own timeouts with manufactured evidence of
a far-future round. It cannot: a block of round `n + 1` references a
quorum of distinct round-`n` authors (P3), a quorum meets any
quorum-sized `T` (`exists_reliable_parent`, with `n − 2f ≥ f + 1`
members to spare), and by `waits` that parent's author has paid the full
timeout bill for every round below:

```lean
theorem exists_honest_floor (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) {n : ℕ}
    (hbr : (U.block b).round = n + 1) :
    ∃ u ∈ T, n ≤ vp.top u ∧
      vp.built u 0 + (∑ i ∈ Finset.range n, vp.timeout i) ≤ vp.built u n
```

Evidence of a round cannot exist before the honest schedule permits the
round: catch-up only ever pulls a validator to where a reliable peer
already is, and the adversary's whole freedom is the single layer it may
build the instant a quorum forms beneath it —
`PaceCore.round_le_top_succ`: no valid block's round exceeds some
reliable `top` by more than one. On the running witness the floor is met
with equality (§18).

The clause itself is asserted only from `gst` (§4.1), so what it demands
coincides with what the clamped author-blind rule delivers: pre-GST it
demands nothing — matching a network that may deliver nothing and a
floor that may bind — and post-GST the collapse arithmetic puts every
catch-up deadline at or past the holder's own floor, `ugrowLag`
exhibiting the two meeting with no slack. One caveat is recorded
honestly: the model does not axiomatise that a block cannot be *held*
before it exists — `holds` is constrained only by `holds_own`,
monotonicity and `converges` — so the statement mechanised is about the
block's existence certifying the floor, with arrival-time realism
carried by the satisfiability witnesses.

**What catch-up does not supply is coverage.** A validator entering a
round on evidence has not waited for the round below to assemble, so its
own block may reference little; the coverage argument still runs through
`waits`, from the collapsed spread onward. Catch-up supplies the *base*
of the drift argument, not the argument — which is also why it composes
with the reactive schedule of §11 rather than replacing it: the two
clauses cut different waits, entry into a round and exit from it.

### 6.12 The view a validator holds

*(module `LeanDag/PaceDelivery.lean`; `viewAt` and the local commit in
`ViewPace.lean`)*

Two objects in this development mean *what a validator has*, and until now
nothing connected them. The commit rules are view-relative — `Decided U V k v`
over a refs-closed `View` — while the pacing line reasons about
`holds : Validator → ℕ → Finset BlockId`, a time-indexed set tied to the
universe by nothing at all. The storage arcs add a third, `Delivery.held`,
indexed by round. This section closes both gaps, and each needs one clause.

**The store clauses.** Two clauses tie `holds` to the universe, and they are
what the section rests on. `holds_sub` says a validator holds only blocks that
exist; `holds_closed` says holdings are causally closed — P4 as a *store*
property. The second is not bookkeeping. A block whose history is missing
cannot be validated, since P3 and P3′ read the referenced blocks, and cannot
be built upon; without the clause the model would oblige a validator to
advance on evidence no implementation could act on, and `viewAt` below would
be the closure of a validator's fragments rather than its view. Adding it
*weakens* what is assumed of an implementation.

Two witnesses had to be repaired to satisfy it, and the repairs are
instructive. `ugapPace` (V10, V11) had validators holding their own blocks
while lacking the round below those blocks were built on; it now delivers
every non-starved block one tick after its build, which leaves validator `2`
starved exactly as before and `converges` binding only from its late GST.
`ugrowLag` (CU4) had its leaders building round `1` at time `12` while the
round-`0` blocks they reference arrived at `14`; they now build at `14`, the
laggard's catch-up deadline moves from `15` to `17`, and the collapse is
still met with equality — spread `10` at round `0`, exactly `Δ + proc = 3`
above. A counterexample that could not physically occur is weaker evidence
than one that could, so both witnesses are better for the change.

**Liveness is local (V18).** With the store clauses a validator's holdings
generate a view: `viewAt v t` is the causal closure of `holds v t`, free by
the `View.ofAccepted` argument, and under `holds_closed` that closure is a
no-op — `viewAt_ids` proves `(viewAt v t).ids = holds v t` for reliable `v`,
so the view *is* the holdings and the statement below is about the blocks the
validator actually has. With `holds_roundBlocks` (past GST every reliable
validator holds every `T`-authored round-`n` block by `latest n + delay`), the
counting of L4 runs *inside* that view:

```lean
theorem decided_local (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (vp.viewAt v (vp.latest (S.slotRound k + 2) + vp.delay)) k (some L)
```

The hypotheses are the main line's exactly — GST and the constant backoff, and
nothing further. This strengthens every liveness statement above: those
conclude `Decided U (View.full U) k (some L)`, the verdict of a view no
deployed validator ever holds, and `decided_of_local` recovers that form
through L3. The argument is proved on the trunk
(`PaceCore.decided_local_of_certifiesAt`), so the reactive discipline inherits
it with its own certificate supplier and no coverage anywhere
(`ReactiveM.decided_local`).

The spine follows in the same form. `commits_recur_local` keeps the
quantifier order of §6.9's `commits_recur_via_pace` — the slot is fixed by
the schedule and the round bound before any execution is named — and
concludes locally at that slot, the slot-selection skeleton being pure
schedule reasoning independent of what is proved there. One hypothesis
drops: `T ⊆ Correct` is not needed. The global spine threads it through
`commits_recur_on`, whose production comes from L1 over `Correct`; here
production is the pacing structure's own, over `T` directly, so the
hypothesis has nothing left to do. The local spine is weaker in hypotheses
and stronger in conclusion.

**The delivery layer is induced (V19).** `Delivery.held` is the same notion
read at the build instant, and defining it so discharges every field of the
structure:

```lean
def heldOf (v : Validator) (n : ℕ) : Finset BlockId :=
  if n < N then (vp.holds v (vp.built v (n + 1))).filter (fun b => (U.block b).round = n)
  else ∅

def acceptedOf (v : Validator) (n : ℕ) : Finset BlockId :=
  if v ∈ (Correct : Finset Validator) then vp.heldOf v n else ∅

def toDelivery : Delivery U
```

— for `vp : ViewPace U (Correct : Finset Validator) N`, which
`reliable_eq_correct` shows is the instantiation always available at full
fault load.

One field is worth naming. `accepted_inj` — the acceptance rule, at most one
block per author — was an assumption of the storage development, and its own
docstring said it was "forced by `distinct_creators`". It is: P7 obliges a
builder to reference every round-`n` block it holds, and P2 forbids citing one
author twice, so a correct validator cannot be holding two blocks by one author
when it builds (`heldOf_inj`). What the DoS arc assumed about acceptance is a
consequence of the reference discipline.

**The reference discipline, both ways (V20).** The storage arcs take one
hypothesis beyond `Delivery`: `RefsAccepted`, that a correct validator
references *only* what it accepted. P7 does not give it — `references`
obliges a builder to include what it holds and says nothing about what else
its block may cite — so the trunk carries the converse directly, as
`refs_held` (S5).

The clause was first tried and rejected. The collapse witness `ugrowLag`
(CU4) failed it, its leaders building round `1` at time `12` while the
round-`0` blocks they reference arrived at `14`. That was evidence against
the *witness*, not the clause: it described a run no implementation could
produce, and the same incoherence had to be fixed for causal closure
anyway. With the leaders now building at `14`, every witness in the
development satisfies `refs_held` — the eight were checked one by one — and
the collapse remains exact. A clause that every model satisfies, and whose
absence let models be physically impossible, belongs on the trunk.

The composition capstone is then unconditional:

```lean
theorem dos_resistance_of_pace {κ : ℕ}
    (hu : UniformBudget vp.toDelivery κ) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto vp.toDelivery v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ)))
```

One structure yields both halves of §8's capstone, and the **only** thing
assumed beyond the pacing structure is the acceptance budget — the mechanism
a validator runs. Production comes from genesis and the pacemaker's rules;
the reference discipline, in both directions, from P7 and S5.

Nor is the correspondence an equivalence: a `Delivery` has no instants, so it
cannot determine a schedule, and it remains the right object for arcs that never
mention time.

---

## 7. Chain quality: coverage and inclusion

*(companion document: `chain-quality.md`; modules `LeanDag/Quality/`)*

Every protocol of this family claims that leader rotation prevents
censorship; this section proves what the ledger actually contains. A
commit does not append one block — it flushes the entire causal cone of
the committed leader (§3.6) — and two families of theorems, split
exactly along the trust boundary, say whose blocks the flush carries:
**coverage**, an aggregate guarantee that holds with no synchrony
assumption anywhere; and **inclusion**, an individual guarantee that
genuinely costs the synchrony round `R`, with a witness model proving
the cost is real.

The metric is **distinct correct authors per round**, not a block-count
fraction: an equivocator can inflate a cone with any number of blocks
per round, so the conventional fraction is adversary-deflatable, while
the author count is what the quorum structure bounds.

```lean
def coveredAt (U) (b : BlockId) (δ : ℕ) : Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ
```

**Coverage (CQ1–CQ3), asynchronous.** Density (D25, §8) forces every
layer of every valid cone to carry all but at most `f` correct
authors, and a committed leader's block is in particular valid — any
commit route, any view:

```lean
theorem card_coveredAt_ge_of_decided (h : Decided U V k (some L))
    (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card - F.f ≤ (coveredAt U L δ).card

theorem card_correct_le_two_mul_coveredAt_of_decided …
    (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card
```

— **every commit carries, at every round below it, blocks from at
least half of the correct validators** (`|Correct| ≥ 2f+1` makes
`|Correct| − f` at least half), and the cumulative ledger form
(`ledger_coverage`) exhibits, for any verdict assignment covering a
committed slot, a set of at least `|Correct| − f` correct validators
each with a round-`δ` block in `ledgerSet`. No synchrony, no delivery
model, no populated rounds appear in any hypothesis.

**The boundary, witnessed.** Aggregate coverage is *not* individual
inclusion. The witness model `Ucens` (CQ8) (§18) runs six rounds in which
three validators reference only each other and commit with the full
certificate pattern, while a fourth — correct, building validly, never
referenced — is the missing author of **every** layer of **every**
flush: `missingAt = {3}` throughout, so CQ1's `≤ f` is exactly tight,
and `Synchronised` fails at every round while the commit stands. The
same correct validator can be censored for ever under asynchrony; no
validity, delivery or liveness clause objects.

**Inclusion (CQ5–CQ7), post-`R`.** After the DAG synchronises, the
backbone (§8.2) puts every correct block in the cone of every
correct-led commit at any later round
(`mem_history_of_decided_commit`), and fairness supplies such a commit:

```lean
def IncludesAt (BlockId) (Payload) (R m k : ℕ) : Prop :=
  ∀ U N, (∀ r ≤ N, Populated U r) → Synchronised U R →
    S.slotRound k + 2 ≤ N →
    ∃ L, Decided U (View.full U) k (some L) ∧
      ∀ b ∈ U.ids, (U.block b).creator ∈ Correct →
        (U.block b).round = m →
        b ∈ history U L ∧
        ∀ g n, g k = some L → k < n → b ∈ ledgerSet U g n

theorem committed_of_correct_block (hT : T ⊆ Correct)
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt BlockId Payload R m k'
```

— for every round `m ≥ R` the schedule fixes, *before the universe is
quantified*, a committed slot whose flush contains every correct
round-`m` block. (`commits_recur_on` does not
expose the committed leader's membership in `T`, which the backbone
needs, so the proof composes from the fair schedule and L4 against the
production hypothesis directly, mirroring L6's own proof.) The quantitative forms pin the
slot to a window: under `FairWithin T w` the committing slot lies
within `w` slots of the first slot above round `m`
(`committed_of_correct_block_within`), and under `BoundedSpacing s` its
round within `s·w` rounds (`committed_of_correct_block_by_round`) — *a
correct block is committed within a schedule-window of its creation,
once the DAG is synchronous*. The capstone `chain_quality` packages
both halves under enforceable or standard conditions only.

The backbone consumes full coverage, so this route is proper to the
full-timeout discipline. The reactive schedule, which forgoes coverage,
recovers the inclusion conclusion by a different backbone at a different
latency — one leadership rotation instead of one round (§11.5, RS5).

A block-count purity variant was considered and rejected: under `DoSValid`
alone the per-author block count carries the exponential constant of §8.3,
and under the budget the cone-level Byzantine count is a whole-store
bound. Neither yields an informative ratio, and the author-coverage
metric is the appropriate one.

---

## 8. Denial of service: equivocation, growth, and the novelty budget

*(companion document: `dos-equivocation-and-growth.md`; modules `LeanDag/DoS/`)*

Safety needs no protection from equivocation: every result of §5 holds with no
anti-equivocation condition anywhere in its hypotheses, and the independence is
itself recorded — a witness model satisfies safety while violating every
storage condition of this section (`LeanDagTest/DoS/SafetyUnderDoS.lean`).
*Storage* is another matter. An uncertified DAG admits Byzantine blocks into
correct views by design, an equivocator may produce arbitrarily many blocks
per round, and a correct validator that retains the cones of what it accepts
can be made to retain material injected by an adversary. This
section bounds that growth in two ways: first under a *reference-validity* condition (exposure),
whose bound is shown essentially optimal yet exponential in `f`; then under a
*rate-limiting* condition (the novelty budget), which is enforceable,
author-blind, and yields the linear result `dos_resistance`. The two
compose: the budget limits the rate at which an equivocator can inject
material, and exposure terminates it.

### 8.1 The store, and what growth means

A validator's store is the accumulation of the cones of everything it
accepted (§6.2 introduced acceptance):

```lean
def viewUpto (D : Delivery U) (v : Validator) : ℕ → Finset BlockId
  | 0 => (D.accepted v 0).biUnion (history U)
  | n + 1 => viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
```

`viewUpto D v n` is everything `v` has retained by round `n`: accepting a
block means holding its entire causal history — that is what downward
closure of views (§2.3) demands. Growth questions are questions about
`(viewUpto D v n).card`, and since correct production alone contributes
`|Correct|` blocks per round, *linear in `n`* is the best attainable;
the question is the constant, and whether the Byzantine share can exceed it.

The *novelty* of an arriving block is what its cone adds over the store:

```lean
def novelty (U) (V : Finset BlockId) (b : BlockId) : Finset BlockId :=
  history U b \ V
```

Novelty is antitone in the store — the more a validator already holds, the
smaller the novelty of any arriving block — the monotonicity on which every
argument below depends.

### 8.2 Exposure, and the DoS-validity condition

An author is *exposed* in a cone that holds two of its blocks from one
round; the DoS condition forbids building on the exposed:

```lean
def EquivPair (U) (X : Validator) (i j : BlockId) : Prop :=
  i ≠ j ∧ (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round

def ExposedIn (U) (b : BlockId) (X : Validator) : Prop :=
  ∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j

def DoSValid (U) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

Exposure is objective — a property of the cone, checkable by any holder —
and *monotone up the DAG*: a cone containing an exposing cone is exposing.
Only the guilty are ever exposed (a correct author has one block per round,
by non-equivocation), and at most `f` authors are exposed in any one cone:

```lean
theorem card_exposedTo_le (hb : b ∈ U.ids) : (exposedTo U b).card ≤ F.f
```

Exclusion costs quorum *margin*, not liveness. At the extreme — every
Byzantine validator caught — the condition pins references exactly:

```lean
theorem creators_refs_eq_correct (hdos : DoSValid U) (hb : b ∈ U.ids)
    (hround : 0 < (U.block b).round) (hk : F.f ≤ (exposedTo U b).card) :
    creatorsOf U.block (U.block b).refs = (Correct : Finset Validator)
```

— the references of every later block are precisely the correct validators,
and the commit chain still operates over
them: the witness model `Uexcl` carries a
direct commit whose three rounds all lie after the exclusion of its
equivocator (§18). Nor does exclusion depend on favourable circumstances:
*density* establishes that a
cone can be selectively blind to at most `f` correct authors per round, even
below Byzantine blocks, because the quorum clause forces every layer of
every valid cone to carry `n − f` distinct authors:

```lean
theorem card_missingAt_le (hb : b ∈ U.ids) (hδ : δ < (U.block b).round) :
    (missingAt U b δ).card ≤ F.f
```

where `missingAt U b δ` is the set of correct authors with no round-`δ`
block in `H(b)`.

### 8.3 Growth under the condition alone: the exponential wall

How large can one cone be under `DoSValid` alone? Byzantine authors are
excluded only *after* both halves of an equivocation meet in one cone; until
then, distinct branches may carry distinct halves, and `e` cooperating
equivocators can chain reveals so that each unexposed author doubles the
mass a branch may adopt. The general upper bound is proved through
*pedigrees* — for each exposed author, the chain of adoption events by which
its blocks entered the cone — and is linear in the round with a constant
exponential in `f`:

```lean
theorem card_history_le' (hdos : DoSValid U) (hb : b ∈ U.ids) :
    (history U b).card
      ≤ (Fintype.card Validator + (Fintype.card Validator - 1) * F.f ^ F.f) *
          ((U.block b).round + 1)
```

The exponential constant is not an artefact of the proof: a matching family of
witnesses (`Udouble` (C5), §18) realises `2^(e−2)` growth from `e` equivocators,
so any bound obtainable from reference-validity conditions alone carries a
constant exponential in `f`. This is the assessment of the exposure
mechanism as a *storage* defence: it is the right accountability layer — it
identifies and permanently retires equivocators at the cost of quorum
margin — but no practical storage bound can rest upon it. Rate limiting is
required, and is orthogonal to it.

### 8.4 The novelty budget

The budget is a rule about acceptance, and deliberately about nothing else.
Two formulations are related. The analysis-side form guards on the author
being Byzantine; the mechanism-side form is the rule a validator can
actually run — **author-blind**, since correct validators cannot in general
tell who is Byzantine:

```lean
def ByzBudget (D : Delivery U) (κ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (U.block b).creator ∉ (Correct : Finset Validator) →
    (novelty U (viewUpto D v n) b).card ≤ κ

def UniformBudget (D : Delivery U) (T : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤ T

def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n
```

`RefsAccepted` is the converse of `includes` (§6.2): together they say a
correct block's references are *exactly* its author's acceptances — local,
observable conduct. The blind and guarded formulations bound each other to
within a factor of `f`:

* `UniformBudget.byzBudget : UniformBudget D T → ByzBudget D T` — dropping
  a guard weakens nothing; and conversely
* `uniform_of_byzBudget` (B6) — post-`R`, under `ByzBudget κ`, *every*
  acceptance (correct authors included) adds at most `f·κ + 1`.

The converse direction is the substantive one, and the mechanism behind it
should be stated. Why would a *correct* author's block have small novelty? Because a
correct block's cone is a complete record of everything its author ever
accepted — `includes` puts each round's acceptances among the next block's
references, and the self-parent chain (P3′) carries every earlier round
forward:

**B7.**
```lean
theorem viewUpto_subset_history (hw : w ∈ Correct) (hb : b ∈ U.ids)
    (hbc : (U.block b).creator = w) (hbr : (U.block b).round = n + 1) :
    viewUpto D w n ⊆ history U b
```

One delivered block therefore erases the entire standing gap between two
correct stores — the DAG is its own repair channel, and no cone-exchange
protocol needs modelling. Quantitatively, the gap between correct stores is
a *constant*, not a drift (`card_viewGap_succ_le`): post-`R` it is at most
`f·κ`, one round of Byzantine budget, however long the system has run.

The same self-parent mechanism yields a purely structural form: if
every correct block adds at most `κ'` over its self-parent (`StepNovelty`),
then correct cones are linear outright,
`|H(b)| ≤ κ'·round(b) + 1` (`card_history_le_of_stepNovelty` (C4)) — a telescope
along the self-parent chain, with no delivery model at all.

### 8.5 The principal result, and the composition

Under the guarded budget the Byzantine share of a correct store is priced
through a global object, the *pool* — the Byzantine-authored blocks any
correct validator retains:

```lean
def byzPool (D : Delivery U) (n : ℕ) : Finset BlockId :=
  (Correct : Finset Validator).biUnion fun w =>
    (viewUpto D w n).filter fun i => (U.block i).creator ∉ Correct
```

A Byzantine block enters the pool only as a direct budgeted acceptance — if
it arrived inside a correct block's cone, `RefsAccepted` places it in that
author's *earlier* store — so the pool grows by at most `|Correct|·f·κ` per
round (`card_byzPool_le`), and the store bound follows:

```lean
theorem card_viewUpto_le (hbyz : ByzBudget D κ) (hra : RefsAccepted D)
    (hv : v ∈ Correct) (n : ℕ) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          n * ((Correct : Finset Validator).card * (F.f * κ)))
```

— correct production, a Byzantine genesis allowance, and a Byzantine rate.
The capstone quotes **enforceable conduct only** — the author-blind budget
and the reference rule — and carries production through alongside the
storage bound, so both hold of the same execution. Production itself is a
hypothesis rather than a premise of the DoS argument: any of the routes of
§§6.7–6.9 discharges it (§4.3):

```lean
theorem dos_resistance {τ N : ℕ} {P : Finset Validator}
    (hpop : ∀ r ≤ N, PopulatedOn U P r)
    (hu : UniformBudget D τ) (hra : RefsAccepted D) :
    (∀ r ≤ N, PopulatedOn U P r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * τ)))
```

with a post-`R` incremental form (`dos_resistance'`) in which the slope is
per-round and the pre-`R` prefix is a single opaque constant. Note what the
hypotheses do *not* contain: no `DoSValid`, no exposure, no appeal to
identifying the Byzantine — the budget alone suffices for the linear bound.

The two conditions then compose. Once every equivocator stands exposed to
every correct validator (`AllExposed U m`), `DoSValid` blocks all further
Byzantine acceptances, the pool freezes at its round-`m` value, and the
store's slope decays to the correct-production rate:

```lean
theorem card_viewUpto_le_of_allExposed' (hdos : DoSValid U)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) (hexp : AllExposed U m) …
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          (m + 1) * ((Correct : Finset Validator).card * (F.f * κ)))
```

— the budget limits the rate at which an author can inject material;
exclusion terminates it. On data,
the budget is satisfiable at its exact constant: the witness schedule
`Dtwin` satisfies `UniformBudget 3` with its costliest acceptance costing
exactly `3`, and `ByzBudget 0` — nothing Byzantine accepted after the
genesis round (§18).

How should the parameter `T` be set? Any `T ≥ 1` admits every correct block
post-`R` (the sandwich's `f·κ + 1` with `κ = 0` would be the correct-only
floor); smaller `T` tightens the Byzantine rate and defers — never refuses —
correct blocks of high novelty, deferral being a rate limit rather than a
refusal, since novelty is antitone in the growing store.

---

## 9. Garbage collection: the horizon

*(companion document: `garbage.md`; modules `LeanDag/GC/`)*

The DoS results end at linear-forever storage, and linear still diverges: a
validator that runs for years retains years of history, and a joining
validator must fetch it. The remedy is a **horizon** — a round `G`, chosen
per validator, below which nothing is retained, requested, or served — with
theorems that commit safety, commit liveness, bounded storage, and bootstrap
all survive above it, and that **no consensus on the horizon is ever
needed**. Throughout, `G` denotes a horizon round and `Λ` (the *lag*) how far
a horizon trails the current round; both are per-validator quantities.

One scoping fact first: garbage collection bounds *stores*, not the
universe. `U` — every block any correct validator ever held — keeps growing
as an analysis object; the theorems live at the level of what a validator
retains (`viewUpto`, §8.1) and what a joiner must fetch.

### 9.1 Truncation as rebasing

The model-side operator keeps the blocks at rounds `≥ G`, rebases rounds by
`−G`, and empties the reference sets of the new base layer — the round-`G`
layer becomes the new genesis layer:

```lean
def chopBlock (U) (G : ℕ) (i : BlockId) : Block Validator BlockId Payload :=
  if (U.block i).round ≤ G then
    { U.block i with round := (U.block i).round - G, refs := ∅ }
  else
    { U.block i with round := (U.block i).round - G }

def chop (U) (G : ℕ) : BlockUniverse Validator BlockId Payload where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlock U G
  …
```

Every validity clause of §2.2 constrains only rounds `> 0`, and the old
genesis special case applies verbatim to the new base — so `chop U G` is a
bona-fide `BlockUniverse`, and **every theorem of this report applies to it
unchanged**. This is the design in its entirety: the task is never to re-prove the
theory above the cut, only relating verdicts *across* the cut and choosing
the cut. (In an implementation, block identity is a hash over references, so
emptying the base layer's references is not a re-hash of history: it is the
checkpoint reinterpreting those identifiers as opaque geneses — a rule about
what the sync layer serves.)

The DoS condition crosses the cut one way (`dosValid_chop`): cones shrink
under truncation, so exposure shrinks, so the per-block condition weakens.
The converse fails *by design*, and the failure is the **statute of
limitations**: an equivocation whose witnessing pair falls strictly below
the cut is forgiven — in `chop U G` its author is no longer exposed — while
a pair *at* the cut survives into the base layer. §9.5 prices the
forgiveness; the witness file exhibits it on data, an exposure present in
the full universe and absent from its truncation (§18).

### 9.2 Verdicts survive the cut

Every commit-rule notion of §3 for a slot above the cut is invariant — the
rules read a window of rounds that truncation does not touch:

```lean
theorem certificates_chop (s : ℕ) :
    certificates (chop U G) L s = certificates U L (G + s)
```

and likewise `supporters_chop`, `blames_chop`, `directCommit_chop`,
`directSkip_chop`, and the indirect test `certifiedIn_chop`. The full
decision relation follows under an *induced schedule*: slots re-indexed
from a base slot `d` whose round clears the horizon, with
`Slots.chop S G d hd` given by `slotRound' k = slotRound (d + k) − G` (the
condition `hd : G ≤ S.slotRound d` is what keeps the re-based rounds above
zero, where subtraction is faithful and the schedule's keying survives).
Views truncate by the same filter (`View.chop`), and:

```lean
theorem decided_chop (hd : G ≤ S.slotRound d) :
    Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v ↔
      Decided U V (d + k) v
```

— a validator re-running the protocol on the truncation decides slot `k`
exactly as it decided slot `d + k` on the full universe, by structural
induction through anchors and intermediate skips, in both directions. The
**only hypothesis is the base-slot condition**: no synchrony, no liveness,
no lag bound, no DoS condition. Cross-cut agreement is deliberately
asymmetric:

```lean
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) : w = v
```

Here `W` is an **arbitrary** view of the truncation — not a truncated
full-history view. The asymmetry matters because a joiner's view is never of
the form `V.chop`: lifted to `U` it would not be downward closed, its base
layer having lost its references. The proof plays the agreement theorem of
§5.5 *inside* the truncation against a truncated view, and carries the
verdict across the cut through `decided_chop`. So a validator that joined
from the truncation and never saw the pruned prefix agrees with every
full-history validator, slot for slot.

### 9.3 Windowed storage: constant at a lag

Liveness transfers with the offset. Production on the truncation is
production upstream with the round index shifted — a round-`r` block of
`chop U G` is a round-`(G+r)` block of `U` — so `populated_chop` (G5)
takes the `Populated` hypothesis every liveness result consumes and
re-establishes it above the cut, consuming no network assumption of its
own. Stores correspond exactly —

```lean
theorem viewUpto_chopD (m : ℕ) :
    viewUpto (chopD D G) v m =
      (viewUpto D v (G + m)).filter fun i => G ≤ (U.block i).round
```

— pruning a store below `G` yields precisely the store of the induced
delivery, which is what lets §8's bound `card_viewUpto_le` be read on the
truncated universe. Two prerequisites make this legitimate over a *sequence*
of cuts. The budget must be measured on the truncated universe — otherwise
pruning would make every arriving block's novelty explode with the
discarded prefix — and windowed novelty is *antitone under cut-advance*
(`novelty_chop_anti`): as the window slides, pruning only decreases novelty,
so a block within the budget never falls outside it. The budget conditions
themselves descend to the window (`byzBudget_chopD`, `refsAccepted_chopD`).

The principal storage result is stated per time, because a validator's life
is a
sequence of cuts:

```lean
theorem card_retained_le {κ Λ t : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ Correct) (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    ((viewUpto D v t).filter fun i => G ≤ (U.block i).round).card ≤
      (Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ)))
```

— **constant in `t`**: at lag `Λ`, the retained store is bounded
independently of how long the system has run. The same constant bounds a
joiner's entire fetch — the attested base plus the window is a *subset of
one correct peer's retained store* (`card_joinIds_le`) — and, plus one, a
correct author's serving obligation: everything it can be asked to serve
for its block is its own retained store above its own horizon, plus the
block itself (`card_serve_le`, via `RefsAccepted` one step down and the
self-parent chain the rest of the way). Garbage collection bounds sync
cost as well as storage, and the obligation on correct validators is bounded
likewise.

### 9.4 Bootstrap: the attested base

A validator so far behind that its needs predate every peer's horizon
cannot fetch the prefix; it must adopt a genesis layer from others. Requiring
`f+1` *identical* checkpoints would be wrong — correct validators' layers
share the correct core exactly but differ in Byzantine fringe — so the
primitive is an **inexact certificate**, filtered per block: attest the
layer, keep what `f+1` distinct authors attest. In this model an
attestation *is* a block — its cone is its objective, unforgeable statement
of what the layer contains — so the certificate is DAG-internal, decidable,
and needs no signatures:

```lean
def attesters (U) (t : ℕ) (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)

def Base (U) (t G : ℕ) : Finset BlockId :=
  (blocksAt U G).filter fun y => F.f + 1 ≤ (attesters U t y).card
```

The base is **sandwiched** between the shared correct layer and the union of
correct cones: everything in it has a correct attester, so the adversary
cannot smuggle fabrications in (`exists_correct_attester_of_mem_base`);
post-`R`, every correct round-`G` block is in every correct attestation, so
nothing of the correct layer can be filtered out, by anyone
(`correct_mem_base`). Completeness in fact extends to everything
*obtainable* — Byzantine-authored included:

```lean
theorem accepted_mem_base (hs : Synchronised U R) (hv : v ∈ Correct)
    (hy : y ∈ viewUpto D v m) (hyr : (U.block y).round = G)
    (hcar : Populated U (m + 1)) (hpop : Populated U t)
    (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    y ∈ Base U t G
```

— every round-`G` block a correct validator accepted into its window by `m`
is in the base attested at any `t ≥ m + 2`: acceptance puts the block in a
correct store, the store rides into its keeper's next block
(`viewUpto_subset_history` (B7), §8.4), and the backbone carries that block into
every correct round-`t` cone — a cone *is* an attestation. The lag is tight
on data: at `t = m + 1` the witness exhibits an accepted equivocation half
missing from the base (§18). Consequently the joiner's assembly — base as
genesis layer plus a correct peer's window strictly above the cut — is a
bona-fide view of the truncation (`joinView`; downward closure is the
content: window references above the cut stay in the window, references *at*
the cut are exactly the blocks `accepted_mem_base` puts in the base), and:

```lean
theorem bootstrap_agree … (hJ : Decided … (joinView …) k jv)
    (hV : Decided U V (d + k) fv) : jv = fv
```

— any decision reached from base-plus-window equals any full-history
validator's. Inexact certificates, exact decisions; bases sampled from
different peers need never agree, exactly as horizons need not.

### 9.5 Horizons without consensus, and the lag envelope

Each validator sets its own horizon by a local rule — trail the decided
frontier by `Λ`, or trail the current round by `Λ` — and three theorems make
the heterogeneity safe. Verdicts at different horizons are equal outright
(`decided_agree_horizons`, matching slots through their absolute index). A
a deeper cut is again a cut:

```lean
theorem chop_chop (hG : G₁ ≤ G₂) :
    chop (chop U G₁) (G₂ - G₁) = chop U G₂
```

so validators at different horizons sit on one tower of truncations, never
in incomparable worlds. And post-`R` possession universalises in **one**
round (`viewUpto_subset_viewUpto_succ`): everything any correct validator
retains by round `m` is in every correct store by `m + 1` — the keeper's
next block carries its whole store, and that block is delivered and
accepted — so pruning at depth `≥ 1` below a correct frontier discards
nothing any correct peer still lacks (`pruned_subset_peer_store`).

The constraints on the lag are best set out theorem by theorem, since
*safety constrains it not at all*:

| bound | source | what breaks below it |
|:---|:---|:---|
| — (any `G` is safe) | `decided_chop`, `decided_agree_chop`, `bootstrap_agree` | nothing — commit safety carries no lag hypothesis; its only premise is `G ≤ slotRound d` |
| `Λ ≥ 0` vs the *decided* frontier | ledger totality | a slot reads rounds `slotRound k … +2`; cutting above an undecided slot discards its certificates and the slot is undecidable forever — output stalls, safety unharmed |
| `Λ ≥ 1` | `viewUpto_subset_viewUpto_succ` | peer no-desync: possession universalises in exactly one round |
| `Λ ≥ 2` | `accepted_mem_base` (tight) | base completeness for joiners |
| upper bound: none | the §9.3 constants | nothing breaks; storage, join and relay grow linearly in `Λ` |

Finally, the statute of limitations is a bounded-rate, priced phenomenon
rather than a cliff. Within an epoch the entire exposure economy of §8.2
applies to the truncation verbatim, the truncation being simply another
universe. Across a
cut, a forgiven author must equivocate *again, inside the new window*, to
be debarred again — one reveal per author per epoch — and the re-entry runs
under the windowed budget: `Λ·f·κ` of injected material per correct store per
epoch,
a term the `card_retained_le` constant already carries. Commit safety never
depended on any of it: the cross-cut results above carry no exclusion,
budget, or exposure hypothesis. A world that forgives every equivocation
still commits the same blocks; it merely retains more.

---

## 10. Odontoceti: two-round commitment

*(companion document: `odontoceti.md`; modules `LeanDag/Odontoceti/`)*

Odontoceti [Van25] commits in **two** communication rounds: a leader block
at round `r` is decided by the supports and blames of round `r+1` alone,
with no certificate round anywhere. The price is a larger committee,
`n = 5f+1`. This section proves safety and liveness of the two-round rule at
the *generalization* `n ≥ 5f+1` — direct thresholds `n − f`, indirect
threshold `n − 3f`, specializing to the published `4f+1` and `2f+1` at the
boundary — and reports four findings about the published safety argument,
one of which is a genuine gap that the formalized rule must repair (§10.4).

### 10.1 The reuse boundary

At `n = 5f+1` Odontoceti's quorums *are* `n − f`: the DAG quorum `4f+1`,
and both direct thresholds. Its validity rules coincide with `ValidWrt`
clause for clause — including the mandatory self-parent (P3′) — and its
support/blame primitives are the `supporters`/`blames` of §3. The entire
DAG layer of this report therefore applies verbatim, and only the rule
layer is new; the fault bound is an *extension*,

```lean
class Faults5 (Validator) extends Faults Validator where
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator
```

so a `Faults5` instance is a `Faults` instance and every existing theorem
continues to apply to the same types. The stronger bound is consumed in
exactly two proofs (O2 and O4′ below) — the two-round rule's *direct* safety
already holds at `3f+1`. The witness file proves the reuse claim as a
computation: a quorum-5 universe over six validators satisfies the untouched
`BlockUniverse` by `decide` (§18). Nothing outside `LeanDag/Odontoceti/`
was modified.

### 10.2 The rule layer, and the arithmetic core

```lean
def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L (r + 1)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card

def coneSupports (U) (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    ((blocksAt U (r + 1)).filter
      (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A))

def ThickLink (U) (A L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - 3 * F.f) ≤ (coneSupports U A L r).card
```

`ThickLink` is the indirect test: enough supports for `L` visible in an
anchor's cone. It counts **distinct authors** of in-cone support blocks,
not raw blocks — the published rule says "`2f+1` supports in the history of
the anchor" without disambiguating, and the block count is
adversary-inflatable (an equivocating supporter can plant any number of
support-twins in one cone), while the author count is the one the
arithmetic on both sides actually bounds. Four counting theorems carry
safety, and they identify precisely where the committee of size `5f+1` is
required:

**O1 (commit versus skip; needs only `n ≥ 3f+1`).**
`not_directSkip_of_directCommit`: no block is both directly committed and
directly skipped. Two `(n−f)`-quorums over `n` authors share
`n − 2f ≥ f+1`; an author both supporting and blaming has two distinct
decision-round blocks, so every member of the intersection is an
equivocator — one more than exist.

**O1′ (twin uniqueness; `n ≥ 3f+1`).** `eq_of_directCommit`: two directly
committed same-author blocks are equal. Same intersection; an author
supporting two distinct twins is an equivocator, because one block cannot
cite an author twice (`distinct_creators`) and two supporting blocks are an
equivocation.

**O2 (a skipped leader fails the test everywhere; the first use of the
fifth `f`).**
`card_supporters_le_of_directSkip`: a directly skipped leader's supporters —
anywhere in the universe, hence in any cone — number at most `2f`; and
`2f < n − 3f` exactly when `n ≥ 5f+1`
(`not_thickLink_of_directSkip`). The proof requires the **exact complement
identity** `|Correct| = n − |byzantine|`: correct supporters and correct
blamers are disjoint, correct blamers number at least
`(n−f) − |byzantine|`, and the `|byzantine|` cancels, leaving correct
supporters at most `f`. Bounding `|Correct| ≤ n` instead degrades the
estimate to `3f`, which does *not* clear the threshold at the boundary —
the natural loose count fails, and only the exact one proves the published
lemma.

**O3 (propagation — every anchor's cone is the certificate).**
`thickLink_of_directCommit`: if `L` is directly committed, then *every*
block from two rounds above it onward — Byzantine-authored included,
validity being structural — carries at least `n − 3f` distinct authors of
support blocks in its cone. One hop: a round-`(r+2)` block's `n − f`
distinct-author parents meet the `n − f` supporters in `n − 2f` authors, of
whom up to `f` are Byzantine equivocators whose *referenced* parent may be
a non-supporting twin; the remaining `≥ n − 3f` are correct, and a correct
author's unique decision-round block is both supporting and in the cone.
Depth: cones are monotone through any single parent, so the bound never
decays. This is the two-round replacement for M2/M4: there is no
certificate object, so its rôle is played by the support pattern that every
later cone is forced to contain.

**O4′ (a direct commit excludes every rival; the second use of the fifth
`f`).** `eq_of_directCommit_of_thickLink`: a directly committed block is
the *only* same-author block that can pass the indirect test, at any
anchor — `n − f` supporters of `L₁` and `n − 3f` in-cone supporters of a
twin `L₂` would overlap in `n − 5f ≥ 1` correct authors, each supporting
two twins. This lemma has no counterpart in the published argument, and
§10.4 explains why it had to exist.

### 10.3 The decision relation, and agreement

Eligibility contracts by one round —
`decisionRound k = slotRound k + 1` and
`Eligible k j ↔ slotRound k + 2 ≤ slotRound j` — and the view-relative
direct rules lift to universe level exactly as in §3.2. The decision
relation mirrors §3.5 constructor for constructor, with one new premise:

```lean
| indirectCommit :
    k < j → Eligible Validator k j → Decided U V j (some A) →
    (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
    IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
    (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) → ¬ L' < L) →
    Decided U V k (some L)
```

The final premise — the committed candidate is the `≤`-least one passing
the test at the anchor, under `[LinearOrder BlockId]` — is the *canonicity*
of §10.4. With it, agreement and safety follow the pattern of §5.5:

```lean
theorem decided_unique (h₁ : Decided U V₁ k v₁) :
    ∀ V₂ v₂, Decided U V₂ k v₂ → v₁ = v₂

theorem safety (h₁ : Decided U V₁ k (some L₁))
    (h₂ : Decided U V₂ k (some L₂)) : L₁ = L₂
```

The induction closes case by case: the direct/direct diagonal by O1 and
O1′; every direct/indirect crossing by O2, O3 and O4′; and the
indirect/indirect case by the anchor trichotomy of §5.5, with a shared
anchor yielding a shared verdict — skip-versus-commit by the skip
constructor's universal premise, commit-versus-commit by canonicity.

### 10.4 The finding: agreement needs a canonical candidate

The published agreement proof (its Lemma 5) handles the indirect/indirect
case by arguing that both validators use the same anchor and that "the
indirect decision rule solely depends on the causal history of the anchor".
That is true of the *test* — but the rule must also **choose a candidate**,
and nothing in the quorum arithmetic prevents two equivocating candidates
from both passing the test at one anchor. The counting that would be needed
— two `(n−3f)`-sized in-cone supporter sets overlapping in more than the
`f` equivocators — requires `2(n−3f) − f > n`, that is `n > 7f`, which
**fails** at `n = 5f+1`. The configuration is moreover realisable: on a
valid six-validator universe, a Byzantine leader's two round-0 twins each
gather exactly three supporters (disjoint correct pairs plus the
equivocator's own split), and a round-3 block sees all of round 1 — **both
twins pass `ThickLink` against it**, by `decide` (`utwin6_both_pass` (O11), §18).
An indirect rule that commits "some passing candidate" therefore admits
derivations committing either twin: agreement is *refutable*.

What arbitrates in practice is the iteration order of the implementation's
candidate loop — every honest node examines candidates in the same,
unspecified but deterministic, order. The formalized rule states that
determinism as mathematics: commit the least passing candidate in a fixed
linear order on block identifiers (block hash, in an implementation). Under
that premise agreement is a theorem; without it, false. The premise is
consumed *exactly* where the published argument is silent — O4′ shows a
directly committed block is the unique candidate passing the test anywhere,
so every other pairing closes by counting, and canonicity arbitrates only
the indirect-versus-indirect case with a shared anchor and an equivocating
leader.

For implementers: **the candidate-iteration order of the indirect rule is
consensus-critical**. Two honest nodes iterating in different orders (for
instance, arrival order) can commit different blocks for one slot at
`n = 5f+1`; any fixed shared order restores agreement, and "first seen"
does not. The remaining findings are recorded in the design document: a
missing lemma (O4′, assumed tacitly by the published case analysis), the
blocks-versus-authors ambiguity in the indirect test (only the author count
is provable), and the exact-complement subtlety in the published Lemma 2
(§10.2, O2).

### 10.5 Liveness, one round shorter

Liveness follows the §6 development with every hypothesis one round
shorter — the protocol's latency advantage made visible as proof
structure:

* **O7.** Post-`R`, a correct-led slot commits *directly* from **two**
  populated rounds and one synchronised step
  (`Odontoceti.decided_of_leader_mem`): coverage makes every correct
  decision-round block reference the leader's block, and `Correct` carries
  a quorum. The §6.6 analogue needed three populated rounds.
* **O8.** Under a pipelined identity-round schedule, a run of **two**
  consecutive committed slots spans eligibility for everything below
  (`spansEligible_two`): a slot cannot anchor on the round immediately
  above it, but the second slot of the run clears `slotRound + 2`. Two
  consecutive correct leaders is the published Lemma 10, now visible as
  arithmetic.
* **O9.** A committed run of eligible span clears every slot below it
  (`Odontoceti.decided_below_of_committed_run`), by the
  nearest-eligible-committed-anchor induction of §6.6, with the indirect
  commit taking the minimum of the passing candidates — the constructive
  face of the canonicity premise.
* **O10.** The composition, under enforceable hypotheses only:

**L10.**
```lean
theorem all_decided_below_of_fairRun (hc : 0 < c) (hT : T ⊆ Correct)
    (hcard : quorumCard Validator ≤ T.card)
    (hspan : SpansEligible Validator c) (fair : FairRunOn T c) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ U N, (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v
```

Note the horizon: the run's last slot needs rounds up to `slotRound + 1` —
one round of certificates fewer than the §6 analogue, again the two-round
structure showing through.

---

## 11. The reactive schedule

*(modules `LeanDag/Reactive/`)*

The full-timeout discipline of §6.9 directs a validator to wait a full
timeout in every round, so latency is a multiple of the timeout however
fast the network happens to be. A **reactive** validator waits only as
long as it must: at the round above a leader it builds as soon as it
holds the leader's block and enough references, falling back to the
timeout only if the leader does not arrive; under Mysticeti a validator
that voted likewise waits at the next round only until it can certify.
When leaders propagate faster than the timeout, consensus proceeds at
network speed — and if every reliable validator is fast, no timeout ever
fires (§11.3).

The two disciplines share everything but the pacing. Both extend
`PaceCore` (§6.9), so the assumptions of the trunk — the partial
schedule, the views, `converges`, the progress rule — and the derived
production are common property; they differ in the clauses that say
*when* a validator builds within a round, and in what each supplies to
the commit arguments: the full-timeout discipline derives coverage, the
reactive one the targeted predicates of §6.6 and not coverage itself —
what that forgoes, and what survives it, is §11.5. The commit
rules, the decision relations and the whole safety development are
consumed as found; only the schedule changes.

### 11.1 The reactive dichotomy

`ReactivePace` is the schedule and network layer both protocols share,
and it **extends the same trunk as the full-timeout discipline**:
`PaceCore` (§6.9) supplies the partial schedule, the views, `converges`
and the progress rule, so production is inherited
(`PaceCore.populatedOn`) rather than assumed — the reactive arc carries
no block function, and every block its statements name is produced by
the derivation of §6.9. Relative to `ViewPace`, the full-timeout floor
`waits` is gone; in its place:

```lean
structure ReactivePace (U) (T : Finset Validator) (N : ℕ)
    extends PaceCore U T N where
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  deadline : ∀ v ∈ T, ∀ n < top v, built v (n + 1) ≤ built v n + timeout n
  vote_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 1 →
    L ∈ (U.block c).refs ∨
      (built v (S.slotRound k) + timeout (S.slotRound k)
          ≤ built v (S.slotRound k + 1) ∧
        (L ∈ holds v (built v (S.slotRound k + 1)) → L ∈ (U.block c).refs))
  prompt_vote : …
```

`deadline` is the ceiling — a validator never waits *past* the timeout —
and `built_lt` the only remaining floor, both over the rounds the
validator reached. `vote_or_wait` is the reactive dichotomy: at the
round above a reliable leader, any `T`-authored block either references
the leader (the reactive exit), or its builder waited the full timeout
and references any leader block it holds (the fallback). Building early
*without* the leader is thereby excluded, which is the entire
discipline: the schedule accelerates only where acceleration cannot cost
the vote. The clauses are stated over any authored block, as everywhere
on the pace line, so non-equivocation is never consulted.

The clause is stated for slots whose leader lies in `T`. For a Byzantine
leader nothing useful can be said — it may equivocate, and P2 forbids
referencing two of its blocks — and no liveness statement concerns such
slots.

The reference coverage of the main line is deliberately unavailable
here: a reactive builder omits whatever had not arrived when its exit
condition was met, so `SynchronisedOn` fails in general. It is also
unneeded — the exit conditions are chosen so that exactly the references
the commit rule counts are present, early exit and fallback alike — and
the extraction confirms that neither liveness result below reaches
`SynchronisedOn`.

### 11.2 Liveness, both protocols

The vote is the shared step:

**RS1.**
```lean
theorem votes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    VotesAt U T (S.slotRound k) L
```

The fallback case is the whole argument, and it is the chain of
`covers_of_converges` (V1) aimed at a single block: the leader holds its
own block when it builds, convergence carries it across within `delay`,
and the collapsed drift plus the full timeout place the arrival before
the waiter's build, where the fallback clause obliges the vote. The
reactive exit needs nothing — it *is* the vote. No drift hypothesis is
taken: the reactive discipline inherits the trunk's collapse like the
timed one, with `le_built` supplied by `built_lt` rather than by the
floor, so the backoff is the same constant `2Δ + proc` — which is why
the quorum bound now appears, feeding the collapse.

The conclusion is `VotesAt` — the targeted interface of §6.6 — and this
is where the two pacing disciplines meet. The full-timeout discipline
derives the same predicate from coverage
(`votesAt_of_synchronisedOn`); the commit is then one counting theorem
either way (`directCommit_of_votesAt`, `directCommit_of_certifiesAt`),
proved once and fed by whichever supplier the schedule provides.

Under Mysticeti, `ReactiveM` adds the certificate stage as the analogous
dichotomy `cert_or_wait` — a round-`(r+2)` block either already
certifies, or its builder waited the full timeout and references every
reliable vote it holds. `ReactiveM.certifies` concludes `CertifiesAt`,
the second targeted predicate, and the liveness statement mirrors L4's
conclusion with the coverage hypothesis replaced by the two wait
clauses:

**RS2.**
```lean
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

The leader block's existence is a conclusion rather than a hypothesis —
supplied by the trunk's derived production, as are the vote and
certificate blocks the proof counts.

Odontoceti requires **no new structure at all**. With no certificates,
the vote stage is the whole protocol: a vote is a support, `T` is a
quorum of supporters, and `Odontoceti.reactive_decided` (RS3) concludes from
`ReactivePace` alone. The two-round rule is the natural home of the
reactive discipline — one delivery separates a fast leader from its
commit.

### 11.3 The fast path, quantified

The claim that reactive execution tracks the network is a theorem, not a
design intention. `prompt_vote` bounds the reactive exit by the trunk's
processing constant `proc` — the same bound catch-up entry carries: once
a validator past its round entry holds the leader and every reliable
round-`r` block, it builds within `proc` — and the latency of a round is
then bounded with the timeout appearing nowhere:

**RS4.**
```lean
theorem no_timeout_of_fast {δ : ℕ}
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator))
    (hfast : D + δ + rc.proc < rc.timeout (S.slotRound k)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      < rc.built v (S.slotRound k) + rc.timeout (S.slotRound k)
```

`δ` is the *actual* per-block propagation bound of the run — a premise
about this execution, not an assumption about the network — and the
conclusion degrades continuously as it approaches the timeout. Below it,
every reliable validator builds strictly before its deadline: the
fallback branch of the dichotomy is never taken, and consensus proceeds
at the pace of `built_succ_le_of_fast` (RS4)'s bound, drift plus delivery plus
processing per round.

### 11.4 The witness, and a constant it corrected

`ugrowReactive` (§18) runs the Mysticeti structure on the round-robin
schedule at build spacing `6` inside a timeout of `9 = 2Δ + proc` — the
drift-free backoff met with equality: every fallback branch untaken, the
commit, the latency bound and the strictly-inside-deadline conclusion
all exhibited on data. Its
processing constant is honest rather than generous: `proc = 5` is the
least value `prompt_vote` admits on this model, because a validator's
shortcut to its *own* round-`r` block lets the trigger fire one tick
before the slowest peer's block would force it. The witness refused to
compile at `4` — the house rule of §18 catching an over-tight constant
in a clause that read as obviously right.

### 11.5 Inclusion without coverage: the rotation backbone

Chain quality's inclusion results (§7) run on full reference coverage,
and the reactive discipline deliberately does without it: an early exit
omits whatever had not arrived, so a straggler's block may be referenced
by nobody at the round above — `SynchronisedOn` is false, and CQ5's
per-round backbone with it.

Inclusion survives anyway, by a different backbone. A correct author's
blocks form a single descending chain under the self-parent clause P3′
(`reaches_self_ancestor`): each block references its author's previous
one, existence at every step coming from completeness rather than from
any production hypothesis, and uniqueness from T1. A straggler's block
therefore lies below every later block of its *own author* — and when
that author leads a slot, the reactive vote discipline commits the
leader block, pulling the whole chain into the common cone at once.

The schedule must return to the author in particular, which is a
strictly stronger fairness than `FairScheduleOn` promises:

```lean
def FairToEach (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ k, ∃ k', k ≤ k' ∧ S.leader k' = v
```

Round-robin supplies it (`rrSlots_fairToEach`). The result then has
CQ6's quantifier order — the slot is fixed by the schedule, before any
execution is named:

**RS5.**
```lean
theorem committed_of_correct_block
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairToEach (S := S) T) {u : Validator} (hu : u ∈ T) (R m : ℕ)
    (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧ S.leader k' = u ∧
      ∀ U N (rm : ReactiveM U T N),
        rm.gst ≤ R →
        (∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∀ b ∈ U.ids, (U.block b).creator = u → (U.block b).round = m →
          ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) ∧
            Reaches U L b ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n
```

No coverage appears among the hypotheses — they are `ReactiveM.decided`'s,
plus the per-validator fairness. So the reactive system trades the
inclusion *latency*, not the guarantee: where full coverage puts a
correct round-`m` block in every correct cone one round later (CQ5), the
reactive discipline puts it in the agreed ledger one leadership rotation
later. Commit latency at network speed, inclusion latency at rotation
speed — and both halves of that sentence are theorems.

This is also where the self-parent clause P3′ acquires its first
liveness consumer: everywhere else it serves storage and recovery
(§§8, 12), and the tables of §§2.2 and 4.8 record the shift.

`ugrowReactive` exhibits the result on data: validator `2`'s round-`1`
block enters the ledger through a slot led by `2` itself, the reach
running down `2`'s own self-parent chain.

---

## 12. Safe Skip: crash recovery in one message

*(modules `LeanDag/SafeSkip/`)*

A validator that crashes and recovers faces a re-entry problem. Every
liveness result rests on production — P8, correct validators building in
every round — so a validator that simply resumes at the current round
leaves a gap that the liveness account does not tolerate, while
rebuilding the missed blocks one at a time costs a round trip per round
of downtime. **Safe Skip** closes the gap with a single message. The
recovering validator `v1` names its own last block `B1` and a block at
round `r` on a donor validator `v2`'s history line; the message
*denotes* one block per missed round, deterministically given the DAG:
at each gap round the filled block carries the references of `v2`'s
block at that round, plus one added self reference to `v1`'s block of
the round below — `B1` at the boundary, the previous filled block above
it. The message is constant-size; the fill is as large as the outage.

The added self reference is a validity requirement rather than a design
choice: P3′ demands that every non-genesis block reference a block by
its own creator, and the donor's references cannot supply one, `v1`
having authored nothing in the gap. The clause that §2.2 records as
absent from safety and liveness is here consumed for the first time
outside the storage arcs — the fill exists in the shape it does because
P3′ forces it.

What is proved: the denotation is a block universe extending `U` with
every old block untouched (SS1), production is restored at every gap
round (SS2), the fill cannot conjure a commit for a slot the network
already passed (SS3) — and every verdict reached before the fill
re-derives after it, so recovery cannot disturb a decision (SS5, SS6).

### 12.1 The message and its denotation

`SkipMsg` packages the message's content with the hypotheses its
receiver verifies against its own DAG:

```lean
structure SkipMsg (U : BlockUniverse Validator BlockId Payload) where
  v1 : Validator
  B1 : BlockId
  v2 : Validator
  r : ℕ
  line : ℕ → BlockId
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  …
  hgap : ∀ b ∈ U.ids, (U.block b).creator = v1 →
    (U.block B1).round < (U.block b).round → (U.block b).round ≤ r → False
```

`line` is the donor's history line — one block per round from
`r0 := round B1` up to `r`, each referencing the one below, which is the
chain the message's pinned block determines by following self-parents —
and `fresh` supplies unused identifiers for the filled blocks, with
`idx` their decoder. The elided clauses record what the receiver checks:
`v1` is distinct from `v2`, `B1` is `v1`'s block *and its only one at
that round* (`hB1uniq`), the line has the stated creators, rounds and
chaining, and the fresh identifiers are new. `hgap` is the crash
itself: `v1` authored nothing strictly between `B1` and `r`.

`hB1uniq` is stated as the uniqueness fact rather than as
`v1 ∈ Correct`, from which it would follow by non-equivocation
(`hB1uniq_of_correct`). The two are not interchangeable in every fault
model: the hybrid model of §14 splits `Correct` into honest and
available, and a *crash-prone* validator — the one Safe Skip exists to
serve — is honest but outside `Correct`. Stating the fact the boundary
argument actually uses is what lets the same structure describe both
(§14's `hB1uniq_of_crash`).

The filled block at gap round `k` is the donor's references plus the
forced self reference:

```lean
def prev (k : ℕ) : BlockId :=
  if k = sk.r0 + 1 then sk.B1 else sk.fresh (k - 1)
```

```lean
def fillBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := insert (sk.prev k) (U.block (sk.line k)).refs
  payload := (U.block (sk.line k)).payload
```

and the denotation is the extension, with every old identifier looked up
unchanged:

**SS1.**
```lean
def skipFill : BlockUniverse Validator BlockId Payload where
  ids := U.ids ∪ sk.freshIds
  block b := if b ∈ U.ids then U.block b else sk.fillBlock (sk.idx b)
  …
```

That `skipFill` *is* a `BlockUniverse` is the substance of SS1: every
clause of §2.2 must survive the fill. The predecessor clause P1 holds
because the copied references sit one round below by the line's own P1
and the self reference is placed there by construction. P2, distinct
creators, is the delicate clause: the copied references must not already
contain a `v1`-authored block. Inside the gap the crash (`hgap`)
forbids one; at the boundary round the only candidate is `B1` itself,
pinned by non-equivocation (T1) — so the self reference collides with
nothing. The reference quorum P3 only grows, P3′ holds by the inserted
reference, and non-equivocation P5 survives because a filled block
equal in author and round to an old one would contradict the crash. The
companion fact is conservativity —

```lean
@[simp] theorem skipFill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    sk.skipFill.block b = U.block b
```

— so every store, view and certificate built on `U` reads the same in
the extension.

### 12.2 Production restored, consensus untouched

Production is what the mechanism exists to restore, and it is restored
exactly:

**SS2.**
```lean
theorem skipFill_populatedOn {T : Finset Validator} {k : ℕ}
    (hpop : PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    PopulatedOn sk.skipFill (insert sk.v1 T) k
```

With `v1` restored to the reliable set, every gap round carries a `v1`
block — and `PopulatedOn` is the production hypothesis the liveness
results of §6 consume, so the recovering validator re-enters the
liveness account at the round after its anchor, from one message.

The converse concern is that a filled block might *create* consensus
where there was none: a gap round may be a leader round for `v1`, and
the fill then supplies a leader block for a slot the network already
passed. It cannot be committed:

**SS3.**
```lean
theorem directSkip_fresh {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hv1T : sk.v1 ∉ T)
    (hpop : PopulatedOn U T (k + 1)) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    DirectSkip sk.skipFill (sk.fresh k) k
```

No old block references a fresh identifier — the filled blocks did not
exist when the old blocks were built, and completeness (P4) keeps old
reference sets inside the old identifiers — so every reliable
validator's block at the round above blames the filled candidate, and a
quorum of blames is a direct skip. The hypothesis `sk.v1 ∉ T` records
that the blaming quorum is drawn from the validators that were live
through the gap; the recovering validator is not asked to blame its own
fill.

The clause the crash violates is exactly P8 (§4.4): a correct validator
holding a quorum builds the following round unconditionally, and
[QXS26] show that dropping it lets round-skipping starve certificate
formation altogether — an infinite execution in which at most `2f`
certificates are ever formed for any round, because production never
recovers. Safe Skip does not weaken P8 to accommodate the crash; it
keeps the base development's unconditional form and repairs the
hypothesis after the fact, once, over the closed gap `hgap` bounds.
That boundedness is what distinguishes the two situations: [QXS26]'s
counterexample needs skipping to be permitted indefinitely, with
nothing pulling validators back into lockstep, where the fill's gap has
a fixed right endpoint and SS3 forbids exploiting it — a filled
candidate is always directly skipped, never committed.

### 12.3 Verdict invariance

The two theorems above concern rounds inside the gap. What remains is
every slot the network decided *before* the fill: a verdict is a
statement about a view of `U`, and after recovery the network's views
extend `skipFill` instead. The garbage-collection arc met the same
question for truncation and answered it with `decided_chop` (G3);
Safe Skip is the extension-side analogue.

The route is conservativity sharpened to the rule layer. Every set the
four rules of §3 count — votes, certificates, blames — is drawn from a
view's blocks, all of them old, whose references the fill preserves; and
a fresh identifier can appear in none of those references, so even for a
*fresh* candidate the vote and certificate sets are empty on both sides
of the fill. The certificate and blame sets a view holds are therefore
equal across the fill for every candidate (SS4,
`certificatesIn_fill` and `blameSetIn_fill`), and reachability from an
old block never leaves the old identifiers (`reaches_fill_old`), so
certification transports both ways for old anchors and fails outright
for fresh candidates (`not_certifiedIn_fresh`).

One obligation is genuinely new. `Decided.directSkip` quantifies over
the universe's leader blocks, and the fill may create a candidate where
there was none — a filled block landing on a leader slot of the
recovering validator, the situation of SS3. The old verdict skipped
that slot *vacuously*; the new derivation must skip it by counting, and
the count is the single hypothesis of the theorem:

**SS5.**
```lean
theorem decided_fill {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId}
    (hq : ∀ n, sk.r0 < n → n ≤ sk.r →
      quorumCard Validator ≤
        (creatorsOf U.block ((blocksAt U (n + 1)) ∩ V.ids)).card)
    (h : Decided U V k v) :
    Decided sk.skipFill (sk.liftView V) k v
```

`hq` asks that the view hold a quorum of authors at the round above
each gap round — SS3's count, relativised to the view. It is consumed at
exactly one point of the induction, the fresh-candidate case of the
direct skip, and it is not an artefact of the proof: a view too sparse
to blame the filled candidate genuinely cannot re-derive the skip. The
indirect cases transport along SS4, and the indirect *skip* against a
fresh candidate is unconditional — no anchor certifies a block that
nothing reaches.

Composing with agreement in the extension (M6) yields the statement
deployment relies on — no verdict moves across a recovery, whatever
view either side held:

**SS6.**
```lean
def QuorateOverGap (V : View Validator BlockId Payload U) : Prop :=
  ∀ n, sk.r0 < n → n ≤ sk.r →
    quorumCard Validator ≤
      (creatorsOf U.block ((blocksAt U (n + 1)) ∩ V.ids)).card
theorem decided_fill_agree {V : View Validator BlockId Payload U}
    {W : View Validator BlockId Payload sk.skipFill} {k : ℕ}
    {v w : Option BlockId}
    (hq : sk.QuorateOverGap V)
    (hv : Decided U V k v) (hw : Decided sk.skipFill W k w) : v = w
```

### 12.4 The witness

`Ucrash N` (SS7, §18) is the round-robin family with validator `3`
crashed after its genesis block: three validators run full lines whose
references omit the absent author, and `3` owns exactly one block. The
message `ucrashMsg` targets validator `1`'s line, and the development's
house rule is exercised end to end: the fill's reference sets and
cardinality are computed by `decide`, the gap is populated, the filled
leader candidate is directly skipped, and `decided_fill` is applied to
the full view with `hq` discharged by counting the three live authors.

### 12.5 How the mechanism should be used

Three constraints on Safe Skip are not visible from this section, since
each arises only against another arc. §16 proves them; they are
collected here because they are what an implementer of §12 needs.

**Recover within the garbage-collection lag.** The fill needs its
anchor, and a horizon that has passed the crash round has pruned it. So
a fill is available exactly for outages no longer than the lag (§16.4);
beyond it the validator's chain is severed, and it recovers by the
longer route of §12.6.

**Draw the donor line from the common core.** §5.2's T3c supplies, at
every round and under no assumption, a correct-authored block that
every block two rounds later reaches. A donor line chosen from such
blocks cites only material every recipient already holds (§16.7), so
the message needs to carry nothing but the target's name — which is the
property the mechanism was designed for, and which §12.7 proves: the
line, and the whole fill, are derived from that name alone (SS8, SS9) —
and the recovering validator
holds what it cites, rather than pointing at history it cannot serve.

**Check the fill before accepting it.** The self reference P3′ obliges
enlarges a filled block's cone past the donor's, so the exposure
condition of §8.2 must be re-established rather than inherited. The
check is local to the fill and needs no identity oracle (§16.7), and
against a covered donor line it reduces to reachability.

### 12.6 When the fill is not available

A validator down longer than the lag is in a worse position than unable
to fill: P3′ requires every non-genesis block to cite a block by its own
creator, so a validator with nothing in the retained layer can produce
nothing at all (§16.6). Bootstrapping by §9.5's attested base makes it a
correct *reader* — its verdicts agree with everyone's — and not a
producer.

Recovery is then three steps rather than one: bootstrap to read,
**re-genesis** to write, and a fill to catch up, the last anchored on
the re-genesis block and spanning the retained window (§16.6). The
middle step needs no exemption from P3′, the retained layer being
genesis after truncation. Until it completes, the validator counts
against the fault budget however well caught up it is, which prices the
recovery window (§16.6).

### 12.7 Round jumping: the fill is derived, not transmitted

*(results in `LeanDag/SafeSkip/Jump.lean`; witness in
`LeanDagTest/SafeSkip.lean`)*

A slow validator at round `r` that sights a quorum at round `R ≫ r`
wants its next block at `R + 1`, not `R − r` blocks of catch-up. The
pacemaker already permits the jump — P11 turns evidence of a round into
entry into it (§6.11) — and what pins the DAG is P3′: a block at
`R + 1` must reference a block by its own creator at round `R`, and the
laggard has none above `r`. The fill is exactly what closes that gap,
so the question is what the jump *costs*, and §12.5 already claimed the
answer in prose: the message "needs to carry nothing but the target's
name". This section makes the claim a theorem — the fill is not data
but a *denotation*, derived by every receiver from a message of
constant size.

The first step is that the donor line was never free data. P2 admits at
most one reference per author and P3′ guarantees one by the block's
own, so "the self-parent" is a well-defined function (`selfParent`, its
uniqueness `eq_selfParent_of_mem` being P2 verbatim), and the chain
descending from the message's pinned target is the only line there is:

**SS8.**
```lean
theorem SkipMsg.line_eq_lineOf (sk : SkipMsg U) :
    ∀ k, sk.r0 ≤ k → k ≤ sk.r → sk.line k = lineOf U (sk.line sk.r) k
```

Any `line` satisfying a `SkipMsg`'s four clauses coincides, on the
whole interval the clauses govern, with the derived chain `lineOf` —
the self-parent iterated down from the top block. The message's largest
field is thereby redundant, and with it the two validator names: the
anchor determines `v1` (`v1_eq_of_B1`) and the target determines `v2`.
What remains is the compact core, and the denotation is a function
of it:

**SS9.**
```lean
theorem SkipMsg.skipFill_eq_of_core (sk₁ sk₂ : SkipMsg U)
    (hB1 : sk₁.B1 = sk₂.B1) (hr : sk₁.r = sk₂.r)
    (htop : sk₁.line sk₁.r = sk₂.line sk₂.r) (hfresh : sk₁.fresh = sk₂.fresh) :
    sk₁.skipFill.ids = sk₂.skipFill.ids
      ∧ ∀ b ∈ sk₁.skipFill.ids, sk₁.skipFill.block b = sk₂.skipFill.block b
```

Two messages naming the same anchor and the same target denote
observationally equal universes — equal identifiers, equal blocks at
every one of them, the statement shaped like `regenesis_converges`
(I11) because the two objects differ only on junk nothing reads. The
decoder `idx` needs no hypothesis: `block` consults it only at fresh
identifiers, where `hidx` pins both decoders. The `hfresh` hypothesis
is the model's rendering of content addressing — deployments name
blocks by hash, so two parties deriving the same blocks assign the same
identifiers.

`JumpMsg` packages the core as the message a recovering validator
actually sends — four names and the fresh-identifier supply, no line —
and its elaboration `JumpMsg.toSkipMsg` rebuilds the `SkipMsg` with
`lineOf` as the line, every clause discharged by the derivation lemmas.
`JumpMsg.denote`, the elaboration's fill, is the round jump: the
universe in which the sender produces at `R + 1`. Being a `skipFill`,
everything §12.1–§12.3 proved — SS1 through SS6 — applies to it
verbatim.

The last step is that receivers can run the elaboration at all, and
here the view structure of §2.3 pays off twice. Views are closed
downward, so a view holding the target holds the entire derived line —
the message points at nothing a receiver lacks; and views share
`U.block`, so all parties derive the *same* fill:

**SS10.**
```lean
theorem lineOf_mem_view (V : View Validator BlockId Payload U) {B2 : BlockId}
    (hB2 : B2 ∈ U.ids) (hB2V : B2 ∈ V.ids) :
    ∀ k, k ≤ (U.block B2).round → lineOf U B2 k ∈ V.ids
theorem JumpMsg.denote_eq_of_core (j₁ j₂ : JumpMsg U)
    (hB1 : j₁.B1 = j₂.B1) (hB2 : j₁.B2 = j₂.B2) (hfresh : j₁.fresh = j₂.fresh) :
    j₁.denote.ids = j₂.denote.ids
      ∧ ∀ b ∈ j₁.denote.ids, j₁.denote.block b = j₂.denote.block b
```

This is I11's move — *derive rather than transmit, so nothing is sent
and nothing can be rejected* — applied to the whole fill rather than to
one genesis block, and it is what licenses reading Safe Skip as round
jumping: the wire carries a constant-size message, the gap blocks exist
only as the denotation every party reconstructs identically, and the
laggard produces at `R + 1` after one message rather than `R − r`
round trips.

**The witness (SS11).** `ucrashJump` is `ucrashMsg`'s compact core —
the same four names, no line — and the two theorems are exercised
against the hand-built original: the elaboration reproduces the line
`ucrashMsg` wrote by hand (`ucrashJump_line_eq`, SS8 on data), and the
two denotations agree on identifiers and blocks
(`ucrashJump_denote_eq`, SS9 on data). The jump and the hand-built fill
are the same universe.

What is deliberately not claimed: the *logical* universe still grows by
one block per gap round, so the counting results of §8 and §9 read
unchanged. The theorems price the wire and the derivation, not the
denotation — and the gap itself stays bounded by the
garbage-collection lag, since an outage longer than the lag recovers
by §12.6's longer route, whose fill spans at most the retained window.

---

## 13. Adaptive leaders: the schedule as a fixpoint

*(modules `LeanDag/Adaptive/`; the design record is `adaptive-leaders.md`)*

Deployed systems do not run the blind rotation the `Slots` instance
models: Hammerhead-style implementations [Tsi+23] consult the agreed
prefix after a commit and reassign the leaders ahead, demoting
validators whose slots were skipped. The intuition for safety is this
development's own agreement theorem — the verdict sequence is agreed
(M6, M7), so any function of it is agreed, and every correct validator
derives the same revised schedule. Turning the intuition into a proof
meets a circularity the base development does not have. In the decision
relation verdicts flow *downward*: a slot is decided indirectly by
anchoring on a committed slot above it, arbitrarily far up. An adaptive
schedule makes leader identity flow *upward*: the leaders of a high
slot depend on verdicts below. Composed without restriction, the
verdict of a slot may depend on the leader of its own anchor, whose
identity depends on that verdict — and nothing rules out two
*self-justifying* schedules, an agreement failure manufactured by the
mechanism itself.

The arc stratifies the dependency and proves the fixpoint forced:
**safety is unconditional** — any two adaptive fixpoints agree, under
no synchrony or fairness hypothesis, for arbitrary, even adversarial,
adapted policies (AL3) — while **liveness prices the policy's
choices** through one clause, the adaptive counterpart of the run
fairness the fixed schedule assumes (AL5). Both hold for both commit
rules: the adaptive layer is rule-agnostic, and its two-round mirror
consumes the policy objects unchanged (AL7).

### 13.1 Epochs, the lag, and the bounded relation

Slots are grouped into epochs of `W` consecutive slots
(`epochOf W k := k / W`); the schedule of an epoch is a function of the
verdicts of epochs at least two below it, and an epoch's verdicts must
be derivable with anchors strictly below the start of the epoch two
above. The dependency is then well-founded — each stage consults
strictly earlier data than the stage above it produces — and the lag of
two is the least that works: with lag one, the slots at the top of an
epoch would have no eligible anchors inside their window. This mirrors
what deployments do, applying reputation to leader selection after a
pipeline delay.

The stratification cannot be expressed with `Decided`, whose
derivations record no bound on their anchors — the relation is a
`Prop`, and a derivation's anchors cannot be recovered from it. The
bound therefore lives in the statement (AL2):

```lean
inductive DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop
  …
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  …
```

Two structural lemmas carry the whole arc. `DecidedWithin.toDecided`
forgets the bound, so every safety theorem of the base development
applies to bounded verdicts without restatement — agreement for the new
relation *is* M6. And congruence: the relation reads the schedule's
`leader` only at slots below `B` (only `IsLeaderBlock` consults it; the
round structure is fixed), so two assignments agreeing below the bound
derive exactly the same verdicts —

```lean
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    DecidedWithin (S := slotsOf hinj a₂) U V B k v
```

— which is what permits judging an epoch against a schedule only
partially determined. `slotsOf` (AL1) is the `Slots` instance a leader
assignment induces over the base round structure; one leader per round
(`slotRound` injective) makes its `keyed` clause a lemma, where under
multi-leader rounds a reassignment could collide two slots of one round
onto one validator and the policy would owe the distinctness clause
itself. The multi-leader obligation is recorded and not pursued.

### 13.2 The policy and the run

`AdaptivePolicy` packages the reassignment rule with the clauses it
owes:

```lean
structure AdaptivePolicy (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] (BlockId : Type*)
    [DecidableEq BlockId] (Payload : Type*) [S : Slots Validator] where
  W : ℕ
  …
  pick : BlockUniverse Validator BlockId Payload →
    (ℕ → Option BlockId) → ℕ → Validator
  adapted : ∀ U v w k,
    (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
    pick U v k = pick U w k
  base_prefix : ∀ U v k, epochOf W k < 2 → pick U v k = S.leader k
```

`adapted` is the measurability clause and the heart of the safety
argument: the leader of slot `k` is a function of the verdicts of
epochs `≤ epochOf k − 2` and of nothing else. `pick` receives the
universe so that a reputation rule may consult the committed blocks
themselves — certification patterns, payload contents — and not merely
the verdict vector; in this model the universe is the shared ground
truth, so no agreement question arises from that argument. What a
*deployed* validator may consult is its committed prefix only: as with
the enforceability discussion of §4.7, the model states the
mathematical condition and the implementation owes the discipline.
Fairness is deliberately absent from the structure — safety must hold
for policies that violate it.

The central object is a schedule-and-verdict pair coherent with the
policy, every slot decided inside its epoch window against the schedule
the policy computes from the verdicts themselves:

```lean
structure AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  assign : ℕ → Validator
  vdct : ℕ → Option BlockId
  closed : ∀ k, DecidedWithin (S := slotsOf P.inj assign) U V
    (P.W * (epochOf P.W k + 2)) k (vdct k)
  coherent : ∀ m, assign m = P.pick U vdct m
```

Existence and uniqueness are deliberately separated, mirroring the
base development's split between the `Decided` relation and
`decided_unique`: **uniqueness is the safety theorem, existence is the
liveness theorem.** A partial variant (`PartialRun`, closed up to an
epoch height) states what a validator holds mid-execution.

### 13.3 Safety: the fixpoint is unique

**AL3.**
```lean
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    (∀ k, R₁.vdct k = R₂.vdct k) ∧ (∀ m, R₁.assign m = R₂.assign m)
```

Two adaptive fixpoints over one universe — derived from *any* two
views, under *no* synchrony or fairness hypothesis — hold the same
verdicts and run the same schedule. The proof is a strong induction on
epochs in which nothing about counting is ever re-proved: verdict
agreement below an epoch forces the two assignments to agree through
the epoch above it (`adapted`), which places both runs' derivations in
the *same* `Slots` instance (`decidedWithin_congr`), where agreement is
M6 through the embedding. The induction is carried by the partial-run
form (`partialRun_agree`), so validators that have not decided equally
far agree on their common prefix. Two corollaries: the commit sequence
read from any two runs is the same list (`adaptive_commitSeq_agree`,
AL6, the shape of M7), and under the constant policy a run's verdicts
are ordinary `Decided` verdicts of the base schedule
(`AdaptivePolicy.const_run_decided`, AL4) — the anchor demanded by the
house rule that a new relation must instantiate to the old one.

### 13.4 Liveness: the fixpoint exists

Existence consumes the standard interface — `SynchronisedOn` and
`Populated`, both untouched by reassignment, since neither mentions a
leader — plus the one clause that prices the policy:

```lean
def PlacesRuns (P : AdaptivePolicy Validator BlockId Payload)
    (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (v : ℕ → Option BlockId)
    (e : ℕ), ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → P.pick U v (b + i) ∈ T
```

Every assignment the policy can emit places, in each epoch past the
base prefix, a run of `c` consecutive `T`-led slots — `FairRunOn`,
relativised to the policy's outputs. Hammerhead's purpose lands on this
clause: a policy that reacts to observed skips satisfies it by
construction where a blind rotation satisfies it by assumption — but
which validators are reliable is not the designer's to know, so it
remains a joint condition exactly as P10 is.

**AL5.**
```lean
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r) :
    Nonempty (AdaptiveRun P U (View.full U))
```

The construction instantiates the base machinery once per epoch and
counts nothing anew: the run `PlacesRuns` puts in epoch `e + 1` commits
directly (L4 at the induced instance), the committed-run descent —
restated with the anchors' bound carried through, the base proof
already anchoring at or below the run's top — clears the epoch below
it, and `exists_partialRun` stacks epochs under a finite horizon,
re-reading the schedule off the verdicts so far at each stage. Partial
runs at every height then glue into a total run along the diagonal,
with `partialRun_agree` supplying the coherence that the
stage-by-stage choices need not. A total run decides every slot there
is, which is why its growth hypothesis is `∀ r, Populated U r`; the
finite-horizon statement is `exists_partialRun`, and it is the
witnessable form.

Hammerhead [Tsi+23] — the reputation-based schedule deployed in Sui
mainnet since v1.9.1 — proves an analogous result by a different route.
Validators may run different schedules concurrently there, and safety
is recovered by proving the schedules necessarily *reconverge*, via
quorum intersection between anchors committed under different
schedules, interleaved with the base protocol's own liveness — its
safety corollary is stated to follow from its liveness lemma directly.
The account here separates the two questions instead: `DecidedWithin`'s
bound makes divergence unstatable rather than something to reconverge
from, so `adaptiveRun_agree` needs no synchrony assumption at all, and
liveness is the independent question of whether the fixpoint the bound
describes exists.

### 13.5 Schedules and pruning

A policy reading the committed prefix meets garbage collection, which
prunes it. §16.4 states the two conditions that keep the two
compatible: the policy must be **horizon-stable**, computing on a
truncated prefix what it would compute on the full one, and a
garbage-collection base slot must be a whole number of epochs.
Otherwise two validators can agree on who leads every slot and still
disagree about which verdicts the policy was entitled to read.

### 13.6 The two-round mirror

The Odontoceti development (AL7) exhibits that the layer is
rule-agnostic. `AdaptivePolicy` and `PlacesRuns` are consumed as found
— they are protocol-free — and only the decision relation is mirrored:
`Odontoceti.DecidedWithin` carries the canonicity clause of the
two-round indirect commit through the bound, and its congruence
transports the clause in both directions, the candidate set reading
the schedule only through `IsLeaderBlock`, which the protocols share.
Per epoch, agreement is O5 through the embedding exactly as the
three-round side used M6, and existence consumes O7 and the bounded
two-round descent with its least-candidate selection — two populated
rounds where Mysticeti needs three:

```lean
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    ∀ k, R₁.vdct k = R₂.vdct k
```

`Faults5` supplies the `Faults` instance the shared policy layer
expects, so nothing is restated on the way.

### 13.7 The witness, and what remains

`demotePolicy` (AL8, §18) is genuinely adaptive at epoch length one —
a slot whose verdict two below was a skip is handed to a fixed
replacement — and the witness exhibits the phenomena the theorems govern:
the same DAG under a reassigned leader commits a *different block* for
a slot, on both rules; a vacuous skip moves a later slot's leader off
the base rotation; two total runs over distinct views are constructed
and shown verdict- and schedule-identical by AL3; and the two-round
indirect commit carries its canonicity clause through the bound on
data.

One question from the design record remains open (AL9): whether the
anchor bound is *necessary* — a model with two self-justifying runs
under unbounded anchors would justify the stratification the way the
`bound_is_necessary_pace` witness justified the convergence bound. The
interaction between an anchor's leader and the verdict it anchors is
delicate, and the answer may need more than four validators.

---

## 14. Hybrid fault tolerance: Byzantine and crash faults apart

*(modules `LeanDag/Hybrid/`; the design record is `hybrid-plan.md`; the
protocol is Orcaella's DAG instantiation [KS26])*

Treating every fault as Byzantine is pessimistic: crashes are common,
equivocation is expensive. The hybrid fault model separates the two —
`fb` Byzantine validators, who may equivocate, and `fc` crash-prone
validators, who are honest but may halt — and [KS26] derives the tight
committee for two-round commitment under it:

    n ≥ 5·fb + 3·fc + 1,   q = n − fb − fc,   k = 2·fb + fc + 1

for the committee, the direct threshold and the indirect threshold. At
`fc = 0` this is Odontoceti's `5f + 1`; the point of the model is what
it yields at the other end: at `fb = 0, fc = 1` the committee is **four
validators with two-round finality**, where tolerating the same single
fault as Byzantine costs six. This section machine-checks both
directions of that result for the DAG rules: safety and liveness at
the generalized bound (H1–H8), and a data refutation one validator
short (H10).

### 14.1 The model: one honest class, one correct class

In the base development `Correct` does two jobs at once — it is the
population that does not equivocate (P5 binds its creators) and the
population liveness may rely on. The hybrid model splits them.
**Honest** (`≥ n − fb`) is the complement of the Byzantine set alone:
a crash-prone validator's block is one block, identical to all
recipients, so it counts for safety. **Correct** (`≥ n − fb − fc`)
is honest *and* available: only it counts for liveness.

```lean
class HybridFaults (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] where
  fb : ℕ
  fc : ℕ
  byzantine : Finset Validator
  crash : Finset Validator
  disjoint : Disjoint byzantine crash
  card_byzantine : byzantine.card ≤ fb
  card_crash : crash.card ≤ fc
  …
```

Two devices keep the arc small. First, crashing is *invisible to a
structural model*: the object of study is a DAG with invariants, not a
transition system, so "halts at time `t`" cannot even be expressed. A
crash is absence — the validator's blocks stop — and the crash class
therefore needs no behavioural clause at all: it enters only through
the cardinality arithmetic and its exclusion from liveness's reliable
set, which the `T`-relativised interface of §6 was already built to
express. Second, the **derived instance**: `HybridFaults.toFaults`
places the union class `byzantine ∪ crash` in the base `Faults`
structure, so the base quorum `n − F.f` *is* the hybrid quorum `q` and
every quorum-shaped clause of the DAG layer — validity P3, views, the
counting vocabulary — instantiates verbatim.

What the derived instance gets wrong is exactly one clause: its P5
binds only the fully-correct class. The strengthening is the arc's one
genuinely new assumption, threaded through the safety theorems the way
`DoSValid` is:

```lean
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator ∉ H.byzantine →
    (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j
```

That crash-prone validators do not equivocate is a clause of the
*fault model* — the honesty of a class, like the Byzantine bound
itself — not conduct the protocol enforces. The counting core the
conflict arguments route through is H1 (`exists_honest_mem_inter`):
two author sets whose sizes sum past `n + fb` share an honest member.
The extraction records the division of labour: the H-family consumes
P2 and P4 exactly where the Odontoceti family does, with
`HonestNoEquiv` standing in the place P5 occupies there.

### 14.2 The rules, and the admissible interval

The rules are Odontoceti's shape at the hybrid constants: direct
commit and skip at `q` distinct authors, the indirect test `ThickLink`
at `k` distinct in-cone authors — with `k` carried as a *parameter*.
The development does not fix [KS26]'s constant; it proves the theorems
for every threshold in an interval:

```lean
def Admissible (k : ℕ) : Prop :=
  2 * H.fb + H.fc + 1 ≤ k ∧ k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator
```

The lower end is what the skip-side conflicts consume — a directly
skipped leader's supporters number at most `2·fb + fc` anywhere in the
universe (H3), one honest validator below it — and the upper end is
what link integrity supplies: every valid block from two rounds above a
directly committed leader carries at least `2q − n − fb = n − 3·fb −
2·fc` support authors in its cone (H4), the interval's upper end with
equality. Twin uniqueness and the exclusion of rival candidates (H2,
H5) complete the Odontoceti mirror, each discounting against `Honest`
where the pure-Byzantine proofs discount against `Correct`.

The interval is nonempty **exactly when** `n ≥ 5·fb + 3·fc + 1` — the
committee bound *is* the existence of a working threshold
(`committee_bound_of_admissible` states the converse), and this is the
form in which the bound enters every theorem: the `HybridFaults` class
itself carries only the base `3·(fb + fc) + 1` clause the derived
instance needs, which is what makes the one-short committee
expressible for §14.6. [KS26]'s `k = 2·fb + fc + 1` and the
house-style `n − 3·fb − 2·fc` are the two named instantiations
(`kTight`, `kRel`), coinciding at the minimal committee.

### 14.3 Agreement

The decision relation mirrors Odontoceti's, canonicity clause included
— a *Byzantine* leader can still plant two passing candidates in one
anchor's cone, and nothing about the crash class closes that gap — and
agreement is the same sixteen-case induction as O5 and M6, at every
admissible threshold:

**H6.**
```lean
theorem decided_unique (hne : HonestNoEquiv U)
    (hk : Admissible Validator k)
    {V₁ : View Validator BlockId Payload U} {s : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided k U V₁ s v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided k U V₂ s v₂ → v₁ = v₂
```

A remark on the source protocol is owed here. [KS26] proves safety for
its core vote-counting protocol, whose view change selects among tied
digests deterministically (`min`); the DAG instantiation's indirect
rule, as published, does not carry that tie-break, and its correctness
is argued by correspondence with the core conditions. The
correspondence is not complete on this point: in the core protocol the
tied selection feeds a re-proposal that must re-earn `q` votes, while
the DAG rule commits outright — and without a canonical selection,
agreement between indirect commits is refutable on data in the
pure-Byzantine case (`utwin6_both_pass`, §10.3), an arithmetic the
hybrid parameters do not close. The relation verified here therefore
retains the canonical-candidate premise, the same repair §10 supplies
for Odontoceti.

### 14.4 Liveness

Liveness consumes the `T`-relativised interface exactly as the base
development states it — `T ⊆ Correct` now excludes the crash-prone
through the derived instance, and coverage and production never
mention a leader or a fault class:

**H7.**
```lean
theorem decided_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided k U (View.full U) s (some L)
```

with the run machinery (`decided_below_of_committed_run`,
`all_decided_below_of_fairRun`) composing as in §10. Two facts are
worth drawing out. `HonestNoEquiv` appears in **no** liveness theorem —
no liveness argument counts an equivocator — and every statement holds
at *every* threshold `k`: only agreement prices the interval. And the
tight committee has no slack: at `n = 5·fb + 3·fc + 1` the correct
class numbers exactly `q`, so the reliable set must be all of it — the
hybrid analogue of §18's remark that at `f = 1` every correct
validator is needed for a quorum.

### 14.5 Conservativity

At `fc = 0` the thresholds are Odontoceti's (`q = n − f`,
`kRel = n − 3f`, the interval anchored at `2f + 1`), and the fault
models identify: every `Faults5` committee is a crash-free hybrid one
(`Faults5.toHybrid`), and the two derived `Faults` instances are
**equal** (`toHybrid_toFaults`), so a block universe over one is a
block universe over the other with no transport (H8).

### 14.6 The bound is necessary

**H10.**
```lean
theorem hybrid_bound_necessary (k : ℕ) :
    ∃ (U : BlockUniverse (Fin 8) (Fin 29) Unit) (L : Fin 29),
      HonestNoEquiv U ∧
      Hybrid.Decided k U (View.full U) 0 (some L) ∧
      Hybrid.Decided k U (View.full U) 0 none
```

One validator short — `fb = 1, fc = 1, n = 8`, where the would-be
interval `[4, 3]` is empty — agreement fails **at every threshold**,
and the two ends of the interval name the two attacks. For `k ≤ 3`,
indirect safety fails: six blame authors directly skip the candidate
while an anchor's cone carries three support authors (two honest, one
Byzantine twin), and the indirect rule commits what the direct rule
skipped. For `k ≥ 4`, link integrity fails: six support authors
directly commit the candidate while a perfectly *valid* anchor packs
its six references with all three available blame authors, leaving
three supports in its cone. In both universes the conflicting
derivations come from the **same full view** — one validator short,
the rule set itself is inconsistent — and both universes are lawful,
`HonestNoEquiv` included: the only twins are the Byzantine
validator's. Each attack fails by exactly one honest validator, which
is the bound being tight rather than convenient.

With H1–H8 this machine-checks both directions of [KS26]'s Theorem 1
for the DAG rules: the committee bound is sufficient, and it is the
least sufficient committee.

### 14.7 The witnesses

`Uhyb4` (H9, §18) is the arc's principal witness: `fb = 0, fc = 1,
n = 4` — the classical `3f + 1` committee with two-round finality when
the single tolerated fault is a crash. Validator `3` halts after its
genesis block; the survivors run three rounds at quorum `3`, slots
commit directly in one delivery, and the crashed validator's slot is
skipped vacuously. `Uhyb9` is the tight genuinely hybrid committee
(`fb = 1, fc = 1, n = 9`): one equivocator, one halted line,
`HonestNoEquiv` holding on data with the twins Byzantine-authored, and
a slot committed on eight supporting authors.

---

## 15. Nemo-Nemo: crash-fault consensus in two rounds

*(modules `LeanDag/Nemo/`; the protocol is Nemo-Nemo [Ker+26], the
Mysticeti rule under crash faults)*

Nemo-Nemo transplants the uncertified-DAG commit rule to the
crash-fault setting: `n ≥ 2f + 1` validators of which at most `f` may
halt and none equivocates, and every quorum a bare majority. The arc is
self-contained: it restates the DAG vocabulary over its own universe
and consumes only the fault-agnostic core — `Block` and the creator
sets, the schedule class `Slots`, the anchor comparison (`anchor_eq`),
the ledger reader `commitSeq`, and the participation predicates, which
this arc moves to `Participation.lean` (`PopulatedFrom`,
`SynchronisedFrom`), stated over a raw block assignment so that the
Byzantine and the crash universes instantiate one definition. The
extraction records that the arc consumes no clause of §4's trust
boundary: its universe carries its own. What it proves: agreement with
no fault bound and no side conditions (NN5), a ledger that is agreed
and never retracted (NN6), and liveness at the classical crash bound
(NN8), under a fairness clause the mechanisation sharpens to
_committed leaders at adjacent rounds_ (§15.4).

### 15.1 The model: safety with no fault class

The quorum is the strict majority,

```lean
def majority (Validator : Type*) [Fintype Validator] : ℕ :=
  Fintype.card Validator / 2 + 1
```

and the arc's whole counting core is **NN1** (`exists_mem_inter`): two
majorities intersect. Where the Byzantine core must find a _correct_
member in the overlap, and the hybrid arc an _honest_ one (H1), here
any member serves — which is the crash model itself, stated as the
universe's non-equivocation clause with no correctness guard: one
block per author per round, for every author. Crashing needs no
behavioural clause for the reason §14.1 gives — a crash is absence —
and under crash the simplification reaches further than it does there:
no fault set exists on the safety side at all. Validity is two
clauses,

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  quorum : 0 < b.round → majority Validator ≤ (creators blk b).card
```

exactly the pair the protocol's block verifier enforces. The base
model's remaining clauses are not weakened but _derived_: distinct
creators among a block's references follow from non-equivocation one
round below (`eq_of_mem_refs_of_creator_eq`), and no self-parent
clause is imposed — the verifier imposes none, and no crash proof
consumes one.

### 15.2 The rules at wave length two

At wave length two the voting round and the decision round coincide,
and the certificate collapses onto the vote: a certificate for a
leader block `L` at round `r` is a round-`(r + 1)` block that
references it. The rules are two definitions:

```lean
def DirectCommit (U : Universe Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  majority Validator ≤ (supporters U L (r + 1)).card
```

```lean
def CertifiedIn (U : Universe Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ p ∈ history U A, (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs
```

The indirect test is the two-round arcs' in-cone support (O2's and
H4's object) at link size **one**: a single anchor-visible vote
suffices, because a vote's author is honest and twins do not exist, so
the counted `Finset` degenerates to an existential — stated over the
finite cone `history`, which makes it decidable. The hitting lemma
**NN2** (`exists_mem_refs_of_correct_support_of_card`) meets a
majority of backers against a valid block's majority of parents, and
link integrity **NN3** (`certifiedIn_of_directCommit`) carries a
direct commit into the cone of every block two or more rounds above,
by the generic propagation lemma rather than a bespoke descent.

### 15.3 Agreement, without hypotheses

The decision relation has three constructors — direct commit, indirect
commit, indirect skip — anchored as in §5.6, with the nearest eligible
committed slot stated positively. Two clauses present elsewhere are
absent here. There is no canonicity premise and no order on block ids:
a slot has at most one candidate before commitment is even asked
(**NN4**, `isLeaderBlock_unique`), non-equivocation applied at the
slot's own round, so the tie-break O5 and H6 require has nothing to
select among. And agreement carries no side condition at all:

**NN5.**

```lean
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂
```

Of the nine constructor pairings, every commit-against-commit case
closes by NN4 with no counting; the direct-against-indirect crossings
close by the visibility lemma — the one place in the agreement proof
that consumes the quorum — and the one substantive case compares the
two anchors through the core's `anchor_eq`, consumed verbatim. The
ledger layer restates M7–M9 over the crash relation (**NN6**:
`Nemo.commitSeq_agree`, `Nemo.ledgerSet_agree`, `Nemo.outputAt_agree`):
two views output identical ledgers, and a block, once written, stays
written, in the same place.

### 15.4 Liveness: the bound, and the two adjacent commits

The fault bound enters the arc here, and nowhere else:

```lean
class CrashFaults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  crashed : Finset Validator
  card_crashed : crashed.card ≤ f
  card_validators : 2 * f + 1 ≤ Fintype.card Validator
```

`Live` is the complement of the crashed set, and one inequality —
`majority_le_card_live`, from `n − f ≥ n/2 + 1` — is the whole of what
the bound contributes. The chain is §14.4's at the majority: a
reliable-led slot commits from two populated rounds and one coverage
step,

**NN7.**

```lean
theorem decided_of_leader_mem
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided U (View.full U) s (some L)
```

and the composed statement **NN8** (`all_decided_below_of_fairRun`,
with `all_decided_below_of_fairRun_live` at `T := Live`) settles every
slot below a recurring run of **two consecutive** reliable-led slots.

The run length is forced, not convenient. Because a crashed validator
cannot be distinguished from a slow one, the indirect rule may not
settle a slot past an undecided one — the nearest-anchor premise that
agreement itself stands on — and an anchor must sit two rounds above
the slot it settles. A committed leader at round `r` therefore settles
nothing at round `r − 1`: that slot's anchor must lie at `r + 1` or
above. For a commit set with no two members at adjacent rounds, the
decided slots are exactly the commits and their round-minus-two
neighbours — commits at every even round, both pipeline offsets
committing for ever, settle no odd slot — while two commits at
adjacent rounds settle everything below them: the upper one anchors
the round below the lower with no eligible slot between, and the round
below the upper _is_ the lower. Round-robin at the tight committee
satisfies the clause by counting: `f + 1` live validators cannot be
pairwise non-adjacent on a cycle of `2f + 1`.

### 15.5 The witness

`Unemo` (NN9, §18) is the arc on data: three validators at the tight
committee, fourteen blocks, validator `2` authoring rounds 0–1 and
then halting, the live pair carrying the DAG to round 5 with the
parent quorum at exactly `majority` from round 3 on. Slots 0, 1, 3
and 4 commit directly by `decide`; slot 2, whose leader left no
candidate, is settled by `indirectSkip` anchored on slot 4 — slot 3 is
not eligible for it at wave length two, so the intermediate premise is
vacuous — and slot 5, with no anchor above it, is claimed by nothing.
`Populated` holds to the horizon and fails past it; `FairRunOn` at
run length two is proved for the round-robin schedule — the counting
argument of §15.4, on data — and the composed theorem is instantiated
at the concrete schedule. The DAG is the protocol's good-case
transcript with one crash, and the decision procedure of [Ker+26]'s
implementation computes the same five verdicts on it.

---

## 16. Integration: composing the arcs

*(modules `LeanDag/Integration/`; the design record is `integration.md`)*

Each arc of §§7–14 was built additively, consuming the core read-only
and modifying no other. That discipline secured independence and left a
question unanswered: **do the arcs compose with each other?** A
validator that garbage-collects below a horizon, recovers from a crash
by Safe Skip, runs an adaptive leader schedule and tolerates hybrid
faults is running four mechanisms at once, and nothing above says the
four are jointly consistent.

The composition matrix must not be settled cell by cell — eight arcs
pair into twenty-eight combinations, and triples into far more. This
section takes the other route: name the invariants each arc consumes,
prove that each transformer preserves them, and let composition follow.
The cost is then linear in the arcs rather than quadratic, and the
capstone (I8) confirms that the ingredients do compose.

The section is organised by what composition produced. §16.1 and §16.2
are the method — the invariant interface, and the preservation lemmas
that make composition linear. §16.3 to §16.6 are what the method
found: a refutation with an exact boundary, the conditions on where a
horizon may fall, the capstone, and a recovery route for a validator
pruned past its own history. §16.7 and §16.8 settle the interaction
with §8's storage account.

What came out are results no single arc could state. Coverage is
**refuted** under the Safe Skip fill, with an exact boundary and for
the same reason the fill is safe (I4). *Placement conditions* say where
a garbage-collection horizon may be put (I5, I6). A composition that
did not fit exposed a hypothesis stated more strongly than its use
(I9). A validator pruned past its own history can be restored, by a
provision costing no exemption from P3′ and no agreement on the cut
(I10–I12). And §8's storage account is sharpened twice over: its
reference discipline is stated more tightly than its own bound needs
(I17), and a fill drawn against a common-core target carries no
material its recipients lack (I19).

### 16.1 Three layers, and what can break them

The invariants do not all live at one level, and the level determines
which mechanism can disturb them.

| Layer | Object | Disturbed by |
|:---|:---|:---|
| U | `BlockUniverse` | `chop` (§9), `skipFill` (§12) |
| D | `Delivery U`, indexed by the universe | `chopD` (§9) |
| S | `Slots Validator`, independent of the universe | `Slots.chop` (§9), `slotsOf` (§13) |

At layer U the invariants are the DAG laws (§2.2), `PopulatedOn` and
`SynchronisedOn` (§6.3–§6.4), `DoSValid` (§8.2), `HonestNoEquiv`
(§14.1) and the verdict facts of §3.5. At layer D they are the
delivery conditions and the storage budgets of §8.4. At layer S they
are `FairScheduleOn` and `FairRunOn` (§6.6), `SpansEligible`, and
§13.4's `PlacesRuns`.

That every theorem of §§5–14 is stated against some subset of this list
is checked rather than assumed: the extraction of §19 is queried for
hypothesis-position identifiers of thirteen capstones, and the
dependency is that the layering is closed. Two corrections came out of
that check. The schedule layer appears in five capstones and belongs in
the list; and layer D is *universe-indexed*, so a universe transformer
needs a delivery transformer of its own before layer-D invariants can
be stated for it at all — which `chop` has (`chopD`) and `skipFill`
does not.

### 16.2 Preservation

Each cell of the table below is one lemma of the shape `I U → I (F U)`,
after which every property stated against named invariants transfers to
`F U` with no further proof.

| Invariant | `chop U G` | `skipFill` |
|:---|:---|:---|
| DAG laws | definitional | definitional (SS1) |
| `PopulatedOn` | `populated_chop` | SS2 |
| `SynchronisedOn` | I2 `synchronisedOn_chop` | **refuted** (I4) |
| `DoSValid` | `dosValid_chop` | open (§16.7) |
| `HonestNoEquiv` | I1 `honestNoEquiv_chop` | I1 `honestNoEquiv_skipFill` |
| verdicts | G3 `decided_chop` | SS5 `decided_fill` |

**I1** is what lets §14's hybrid model be used inside §9's truncation
and across §12's fill: a hybrid universe stays one on both sides. The
fill's half is the argument `skipFill`'s own non-equivocation field
makes for the correct class, at the wider honest class, and it consumes
the same clause — `hgap`, the crash itself.

**I2** needs only the horizon offset `R ≤ G + R'`, with no base-layer
exception. Coverage constrains a block at chopped round `n + 1`, which
lies above the cut by construction, so `chop` retains its references
and the original clause applies unchanged. A condition that quantifies *upward* transports through truncation with
fewer side conditions than one pinned at a fixed round.

At layer S, **I3** carries fairness and shape through `Slots.chop`
(`fairScheduleOn_chop`, `fairRunOn_chop`, `spansEligible_chop`), which
is what gives a validator joining from a truncation a schedule that is
fair and spanning in its own right. The corresponding cell for
`slotsOf` is empty on purpose: an adaptive policy changes who leads, so
fairness of the induced instance cannot follow from the base
schedule's, and §13.4's `PlacesRuns` is the replacement. That contrast
explains its otherwise peculiar shape — it quantifies over every
verdict function the policy might see, because no fact about the base
schedule survives reassignment.

### 16.3 Coverage under the fill

Coverage behaves in three ways under the Safe Skip fill, and the
division is the result.

**It fails for a reliable set containing the recovering validator, at
the rounds that validator slept through.**

**I4.**
```lean
theorem not_synchronisedOn_skipFill (sk : SkipMsg U) {T : Finset Validator}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ SynchronisedOn sk.skipFill T R
```

The failure needs no hypotheses beyond the ones SS2 itself creates, and
its reason is the fact that makes Safe Skip **safe**. SS3 concludes
that a filled candidate is always directly skipped *because no old
block references a fresh identifier*; coverage asks the opposite, that
every reliable block at round `n+1` reference every reliable block at
round `n`. One fact, two consequences: the fill can manufacture neither
a commit nor coverage. The hypotheses are exhibited satisfiable on
`Ucrash` (§18), so the refutation is not vacuous.

**It is preserved for any reliable set that excludes the recovering
validator** (`synchronisedOn_skipFill_of_notMem`). The filled blocks
are that validator's alone, so a clause quantified over the others
never encounters them.

**It returns strictly above the fill**
(`synchronisedOn_skipFill_above`), for any set. The strictness is not
slack: at the target round the lower block may still be the last filled
one, and the refutation reaches there too.

So the fill composes with the liveness account of §6, and what it
cannot support is the claim that a validator was covered at rounds
during which it was absent — which §12 does not make. §12's claim is
that the fill restores *production*, which is the hypothesis liveness
consumes and which SS2 supplies. The reading for a deployment is that
a recovering validator is outside the covered set for the duration of
its gap, consistent with §16.6's account of what it costs to be absent,
and an ordinary participant from the round above the fill onward.

### 16.4 Where a horizon may be put

Three conditions constrain the placement of a garbage-collection
horizon relative to the mechanisms running above it. None is visible
from a single arc.

**I5 — the joiner's two obligations.** §13's adaptive schedule is a
function of the committed verdicts, and §9 prunes verdicts below a
horizon; a validator joining from the truncation may not hold what the
policy reads. The schedule half of the question is settled by
computation: truncating an adaptive schedule and adapting a truncated
one give the same rounds and the same leaders, `slotsChop_slotsOf`
closing by `rfl` provided the assignment used inside the truncation is
the original one shifted past the base slot. All the content lies in
whether a joiner can *produce* that shifted assignment, which is

```lean
def HorizonStable (P : AdaptivePolicy Validator BlockId Payload) (d G : ℕ)
    (pick' : BlockUniverse Validator BlockId Payload →
      (ℕ → Option BlockId) → ℕ → Validator) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (v : ℕ → Option BlockId)
    (k : ℕ), pick' (chop U G) (fun m => v (d + m)) k = P.pick U v (d + k)
```

Under it a joiner computes exactly the leaders the network is using
(`joiner_assign_agree`), so the two run one schedule seen from two
origins. The obligation is stated on the policy's *rule* rather than on
an `AdaptivePolicy`, because a policy is indexed by its `Slots`
instance and a joiner's inhabits a different type; the rule is the part
that survives re-indexing.

A second obligation is independent of the policy. Horizon-stability
aligns leaders, not *epochs*: a joiner's slot `k` is the network's
`d + k`, so the numberings correspond only when the base slot is a
whole number of epochs (`epochOf_add_of_dvd`), and the example beneath
it shows the correspondence failing otherwise. **A
garbage-collection base slot must be a multiple of the adaptive epoch
width** — without it two validators can agree on who leads every slot
and still disagree about which verdicts the policy was entitled to
read.

**I6 — the lag bounds the recoverable outage.** A `SkipMsg` requires
its anchor in the universe, and `chop` retains the anchor exactly when
the horizon has not passed the round at which the validator crashed.
`anchor_pruned` states the constraint and `chopMsg` shows it is the
only one: with the anchor retained the whole message rebases, every
field shifted by `−G`. Composed with §9's lag envelope:

```lean
theorem outage_bounded_by_lag (sk : SkipMsg U) {Λ : ℕ}
    (hlag : G + Λ = sk.r) (hr : sk.r0 ≤ sk.r) :
    G ≤ sk.r0 ↔ sk.r - sk.r0 ≤ Λ
```

> Garbage collection at lag `Λ` supports Safe Skip recovery from
> outages of up to `Λ` rounds, and no more.

Beyond it the validator's last block is gone, and §16.6 says what
happens then.

### 16.5 Composition, and a hypothesis that did not fit

**I7 — the capstone.** A validator running the whole stack — recovered
by Safe Skip, then truncated, read in the hybrid fault model under an
adaptive schedule — satisfies every invariant its arcs require, by
chains of the lemmas of §16.2 with no new argument. The end-to-end
statement:

```lean
theorem hybrid_agree_stack [LinearOrder BlockId] [S : Slots Validator]
    (sk : SkipMsg U) (hne : HonestNoEquiv U) {k : ℕ}
    (hk : Hybrid.Admissible Validator k)
    …
    (h₁ : Hybrid.Decided k (stack sk G) V₁ s v₁)
    (h₂ : Hybrid.Decided k (stack sk G) V₂ s v₂) : v₁ = v₂
```

A validator that recovered from a crash and then pruned still cannot
disagree with anyone about a verdict. Its proof is §14's agreement
theorem applied to a different universe, with the one hypothesis
discharged by the chained preservation lemma.

The order is asymmetric, and the order deployments take is the
unconstrained one. Filling then truncating is well formed at every
horizon, because the fill has already happened when the cut is made;
truncating then filling needs the anchor retained, which is I6's
condition. The schedule layer composes with no compatibility lemma at
all, since `Slots.chop` and `slotsOf` read a `Slots` instance and
nothing else, which is what the layering of §16.1 was drawn for: one of
its three layers does not interact with the others at all.

**I9 — the composition that did not fit.** §14 splits `Correct` into
honest and available, and a crash-prone validator — precisely the one
Safe Skip serves — is honest but not correct. `SkipMsg` carried
`v1 ∈ Correct`, so the structure could not describe its own motivating
case. The hypothesis was stronger than its use: it appeared once,
pinning `v1`'s round-`r0` block to the anchor at the fill's boundary.
§12.1 now carries that fact directly as `hB1uniq`, with
`hB1uniq_of_correct` recovering the base model's route and
`hB1uniq_of_crash` supplying §14's from `HonestNoEquiv`. Neither arc
was mistaken; one stated a hypothesis in terms of a class the other
splits.

The lifecycle then composes without further work. A halted validator's
slot is skipped by L5 — whose hypothesis says nothing about *why* the
leader is absent, so a crash-prone leader, a withholding Byzantine
leader and a correct leader that has not yet built are
indistinguishable there — and after recovery SS2 restores production
with the validator back in the reliable set. No lemma relates
`AdaptivePolicy` to `HybridFaults`, and none is needed: the crash class
is invisible in verdicts, which is all a policy reads.

### 16.6 Re-genesis, and the long outage

A validator whose whole history falls below a horizon is worse off than
unable to fill. P3′ requires every non-genesis block to reference a
block by its own creator, so `no_blocks_of_no_genesis` shows that a
validator with no block in a universe's genesis layer can produce
nothing in it at all — the self-parent chain walks every block down to
genesis, and a severed chain cannot restart. `severed_of_pruned_anchor`
applies this to the truncation: **any** attempt to resume is blocked,
not merely Safe Skip.

The repair is to start a fresh chain *at the cut*, and it needs no
exemption from P3′. Truncation rebases the retained layer to round `0`,
where P1, P3 and P3′ are guarded by `0 < round` and P2 is vacuous for
an empty reference set — which is how `chop`'s own validity proof
discharges that layer. A re-genesis block is therefore indistinguishable,
to the validity rules, from a block the cut flattened.

**I10.**
```lean
def addGenesis (V : BlockUniverse Validator BlockId Payload) (v : Validator)
    (g : BlockId) (p : Payload) (hg : g ∉ V.ids)
    (hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v) :
    BlockUniverse Validator BlockId Payload where
  ids := insert g V.ids
  block b := if b ∈ V.ids then V.block b else ⟨0, v, ∅, p⟩
  …
```

The non-equivocation obligation needs no further hypothesis: adding a
genesis block
would normally risk a twin at round `0`, and the absence that stranded
the validator is what makes the new block unambiguous.
`populatedOn_addGenesis` puts it back in the genesis layer, which is
P8's hypothesis at round `0`.

**I11 — heterogeneous horizons need no agreement.** A re-genesis block
is valid in the truncation and not in the universe it came from: at a
positive round of the original, a reference-free block violates P3. It
would therefore be acceptable only to validators that have pruned at
least as far — which §9 cannot promise, since its horizons are
per-validator by design. The resolution is to **derive** the block
rather than transmit it: each validator synthesises a genesis for any
validator absent from its own retained layer, so nothing is sent and
nothing can be rejected. What that needs is that the derivations
converge, and they do. A validator's own derived genesis sits at round
`0` and is pruned by any further cut, leaving exactly the base a
more-truncated validator holds:

```lean
theorem regenesis_converges {U : BlockUniverse Validator BlockId Payload}
    {G₁ G₂ : ℕ} (hG : G₁ < G₂) … :
    (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).ids
        = (chop U G₂).ids
      ∧ ∀ b ∈ (chop U G₂).ids,
          (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).block b
            = (chop U G₂).block b
```

Both then derive the same genesis from the same base, so §9's central
claim — no agreement on the cut anywhere — survives the provision
intact. The statements are observational: identifier sets equal, and
blocks equal at those identifiers, the two universes differing only on
material outside their identifier sets that nothing reads.

**I12 — the three mechanisms are complementary.** A long outage uses
all of them, in order: **bootstrap** to read, since §9.5's attested
base yields a view whose verdicts agree with everyone's
(`bootstrap_agree`) but no ability to produce; **re-genesis** to write,
restoring the validator to the genesis layer, which is what P3′ was
blocking; and **Safe Skip** to catch up, one message denoting every
block from the cut to the current round — §12's mechanism doing the job
it was built for, at a gap that now begins at the horizon rather than
at the crash.

The third step needs an anchor and the re-genesis block is one
(`recoveryMsg`). The closure is exact: `hsev`, the total absence that
licensed re-genesis, is what discharges the anchor's uniqueness
clause — a validator with no other block anywhere cannot have a second
at that round — and the same absence discharges `hgap`. Nothing extra
is assumed. What every party needs for the fill to denote anything is
the retained history including the donor's line up to the target, which
is `SkipMsg`'s standing requirement and, after garbage collection,
exactly the window everyone keeps.

So the earlier reading — that Safe Skip's fast path *avoids* bootstrap
and re-genesis — holds only while the anchor survives (§16.4's lag
bound). Past that the three compose, and Safe Skip's contribution is
undiminished: it remains the succinct encoding of the many blocks
missing inside the retained window.

**I18 — and the interval between the phases is priced.** A severed
validator can read once bootstrapped but cannot produce, and the
reliable sets liveness quantifies over are defined by production, so it
belongs to none of them (`notMem_of_no_blocks`). Since liveness needs a
reliable set of quorum size, at most `f` validators may be severed at
once (`card_severed_le`). **The horizon lag is therefore a
liveness-margin parameter and not only a storage one**: a shorter lag
saves storage and lengthens the window in which a returning validator,
however honest and however well caught up on the ledger, counts against
the fault budget.

### 16.7 The exposure condition under both mechanisms

The two recovery mechanisms part company at the exposure condition, and
the reason is structural.

**I13.**
```lean
theorem dosValid_addGenesis (hdos : DoSValid V) :
    DoSValid (addGenesis V v g p hg hsev)
```

Re-genesis adds a block with **no references**. It cannot cite an
exposed author — the clause is vacuous for it — and it enters no other
block's cone, since nothing reaches what nothing references. §8's
per-cone bound therefore applies to a re-genesised universe unchanged,
and the concern that re-genesis severs the chain §8 relies on does not reach
the condition: what §8 forbids is *citing* an
exposed author.

The fill does the reverse. P3′ obliges `fillBlock` to insert a self
reference, so the first filled block reaches the anchor and with it the
whole of `v1`'s pre-crash history (`history_B1_subset_fill`). Its
citations are inherited unchanged from the donor while its cone is
strictly larger, and `DoSValid` forbids citing an author exposed *in
one's own cone* — so a citation innocuous in the donor's smaller cone
can be a violation in the filled block's larger one.

So the clause §2.2 records as consumed by neither safety nor liveness
is doubly implicated: the self-parent chain is what makes a cone a
complete record of its author's acceptances in §8, and the self
reference §12 must add is what pushes a cone past what the donor
vouched for.

The disturbance is nonetheless **local**, which is what makes it
addressable. A fill copies a donor block's references, and `DoSValid U`
already vouches for those citations in the donor's cone; what the fill
adds affects no other block, because an old block's cone contains no
filled block — SS3's observation once more. Exposure at an old block is
therefore unchanged in both directions
(`exposedIn_skipFill_old`), and the condition decomposes:

**I14.**
```lean
theorem dosValid_skipFill (hdos : DoSValid U)
    (hnew : ∀ k, sk.r0 < k → k ≤ sk.r →
      ∀ i ∈ (sk.skipFill.block (sk.fresh k)).refs,
        ¬ ExposedIn sk.skipFill (sk.fresh k) (sk.skipFill.block i).creator) :
    DoSValid sk.skipFill
```

The extension satisfies the exposure condition as soon as its own
blocks do. That second half is a property of the fill alone, so a
recipient establishes it by computing the fill and inspecting it,
consulting no identity oracle and nothing beyond the message and its
own DAG — enforceable in the sense §4.7 requires, and admissible as a
clause of the mechanism rather than an assumption about the network. A
fill whose enlarged cone exposes one of the donor's citations fails the
check and is refused, rather than accepted and unsound.

The check itself reduces to **reachability** in the ordinary case.

**I15.**
```lean
theorem dosValid_skipFill_of_covered (hdos : DoSValid U)
    (hcov : ∀ k, sk.r0 < k → k ≤ sk.r → sk.B1 ∈ history U (sk.line k))
    (hv1ne : ∀ p ∈ U.ids, ∀ q ∈ U.ids, (U.block p).creator = sk.v1 →
      (U.block q).creator = sk.v1 → (U.block p).round = (U.block q).round → p = q) :
    DoSValid sk.skipFill
```

If each donor block already reaches the anchor, the fill's cone adds
nothing but `v1`'s own new blocks (`fill_cone_subset`) — and those
cannot form an equivocating pair, since they sit at distinct rounds,
`hgap` excludes an old `v1` block at any of them, and `hB1uniq` pins
the anchor's round. What is left is the donor's own cone, for which
`DoSValid U` already vouches. So a recipient verifies one reachability
query per gap round against its own DAG, and needs no exposure
computation over the extension at all.

The covering hypothesis is what a donor line satisfies whenever it
referenced `v1`'s last block, which is the ordinary case: `v1` was
producing at `r0`. The second hypothesis is forced rather than chosen —
`SkipMsg` records only that the anchor is `v1`'s unique block *at its
own round*, leaving open that `v1` equivocated before crashing, and the
fill's self reference would then cite an exposed author. It is what the
base model's correctness and §14's honesty each supply.

### 16.8 Storage: the delivery layer, and what settles it

§8.4's budgets range over a `Delivery U` rather than over `U`, so they
cannot be *stated* for the fill until it has a delivery structure of
its own — the dependency §16.1 records for layer D, which garbage
collection satisfies with `chopD`.

The transformer is smaller than it appears. A `Delivery` records what
validators held and accepted **when they built their blocks**, and
nobody received the fill at the time: the filled blocks reconstruct
what the recovering validator would have produced. `skipFillD`
therefore changes nothing, and the one obligation with content is
`includes`, which now quantifies over filled blocks and asks that they
reference what `v1` accepted below. The hypothesis that discharges it
is that `v1` accepted nothing while down — the acceptance-side
counterpart of `hgap`, which says as much of production.

**I16.** The author-blind budget then transfers at the same constant
(`uniformBudget_skipFillD`), with no arithmetic: every accepted block
is old, so views and novelty are literally the same finite sets
(`viewUpto_skipFillD`).

The reference discipline does **not** transfer, and the failure
describes the mechanism rather than the transformer
(`not_refsAccepted_skipFillD`). `RefsAccepted` is `includes`'
converse — a correct validator cites *only* what it accepted — and a
filled block cites the donor's blocks, which the recovering validator
did not accept, having been down. A retroactive reconstruction cannot
satisfy both under a delivery structure that records what actually
arrived.

The alternative is to model recovery as acceptance *at recovery time*:
`v1` obtains the donor's blocks when it rejoins and accepts exactly
what its filled blocks cite, whereupon both clauses hold by
construction, `accepted_inj` following from the P2 clause `skipFill`
already establishes for `fillBlock`. What that model does not concede
is the budget — the novelty of the newly accepted blocks becomes a
property of the fill, to be checked as in §16.7 rather than inherited.

**I17 — and the choice does not affect the budget.** §8.4's
`RefsAccepted` attributes a block's cone to *its own author's* view, and the pool argument does not need that. Its component lemmas are
already stated at the right generality: novelty is bounded by the gap
toward whichever validator's acceptances contain the references
(`card_novelty_le_viewGap_add_one`), and that gap is bounded as soon as
the validator **has a block at the round**
(`card_viewGap_succ_le`) — which a donor line does at every gap round.
Composing them at a `w` other than the author gives

```lean
theorem card_novelty_le_of_donor {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted w (n + 1))
    {c : BlockId} (hc : c ∈ U.ids) (hcc : (U.block c).creator = w)
    (hcr : (U.block c).round = n + 1) :
    (novelty U (viewUpto D v (n + 1)) b).card ≤ F.f * κ + 1
```

So a filled block respects the budget with the **donor** in the role
the author would ordinarily play, whether or not the recovering
validator ever accepted the material. The modelling question is
therefore about which clause of §8.4 one wishes to state, not about
whether the storage bound holds: it holds either way. The discipline is
stated more tightly than the bound requires, and the fill is the case
that shows the difference.

**I19 — and choosing the target from the common core settles the rest.**
What the storage argument does not address is *availability*: a
validator citing blocks it does not hold cannot serve them. Selecting
the fill's donor line from the **common core** removes that at its
source. §5.2's T3c produces, at every round and under no assumption
whatever, a correct-authored block that every block two rounds later
reaches (`exists_commonAt`) — so cones nest and its references lie in
the causal past of every validator holding a block two rounds up:

```lean
theorem fill_refs_available (sk : SkipMsg U)
    (hcom : ∀ k, sk.r0 < k → k ≤ sk.r → CommonAt U (sk.line k) k)
    {k : ℕ} (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = k + 2)
    {i : BlockId} (hi : i ∈ (U.block (sk.line k)).refs) :
    i ∈ history U c
```

Three things follow. **Nothing needs transmitting**: the message names
the target and every recipient reconstructs the filled blocks from its
own DAG. **The recovering validator holds what it cites**, having the
common core like everyone else once bootstrapped, so the tight
author-attributed discipline is satisfiable rather than something to
weaken. And the choice above stops mattering in practice, both clauses
being met.

This is a restriction on how a message picks its target, not on the
executions the protocol admits: T3c is a counting theorem with no
synchrony and no progress hypothesis, so a common target exists at
every round of every universe.

---

## 17. Mahi-Mahi: the asynchronous rule, and the clause

*(modules `LeanDag/MahiMahi/`; the protocol is Mahi-Mahi [Jov+24], the
Mysticeti rule stretched to a wave of four or five rounds with the
leader revealed only after the wave)*

Mahi-Mahi is the asynchronous member of the family. Its rule is the
core's with three changes: the wave has `w` rounds, a candidate
proposed at `r` being voted on at `r + w − 2` and decided at
`r + w − 1`; a vote is counted through the voting block's causal cone
rather than among its direct references; and the leader of a round is
named by a common coin reconstructed from the decision round's blocks,
so that an adversary scheduling deliveries during the wave does not
know whose block to starve. The thresholds, the anchor rule and the
indirect decision are unchanged, and the reference implementation runs
the rule at `w ∈ {4, 5}` under round-robin, leaving the coin to the
paper.

The arc asks two questions. Is the rule at wave `w` safe on the
unmodified DAG layer — and is `w = 3` the core? And under what
hypothesis is it live with **no synchrony assumption**, given that the
model has neither an adversary nor a clock in which "revealed late"
could be said? The answer to the second is a single clause on the pair
(schedule, DAG), stated in §17.3, which the counting of §17.2 makes
non-vacuous and which synchrony derives from the core's fairness
(§17.4). The arc is also the first in this development built under a
statement/proof partition (§17.5): definitions and statements are the
audited surface, proofs are generated, and a checker enforces the
split.

### 17.1 The rule at wave `w`, and safety

At `w = 3` a vote is a direct reference and validity's distinct-creator
clause makes "a block votes for at most one candidate of a slot" a
consequence of validity. At `w ≥ 4` a voting block's cone may hold two
twins of a Byzantine leader, reached by different paths, so the vote
must be a choice. The implementation chooses the first block of the
slot met in a depth-first walk over the block's stored references; this
development's references carry no order, so the choice is the least
block of the author and round in the cone under a `LinearOrder` on
identifiers — hash order, in a deployment:

```lean
def Votes (U : BlockUniverse Validator BlockId Payload) (q L : BlockId) : Prop :=
  L ∈ candidatesAt U q (U.block L).creator (U.block L).round ∧
    ∀ L' ∈ candidatesAt U q (U.block L).creator (U.block L).round, ¬ L' < L
```

Safety consumes only that the choice is unique per block; which block a
shared rule picks is immaterial, and the support order of the
implementation is consensus-critical exactly through that uniqueness. A
blame is on the slot, as the implementation's `enough_leader_blame` has
it: a voting block that supports no twin of the slot's author. The
decision relation `MahiMahi.Decided` has the core's four constructors
with the wave length substituted, and the generic anchor comparison
`anchor_eq` of §5.6 closes its agreement proof as it does the core's.

**MM1** (`MahiMahi.Safety.holds`) states, for every `w ≥ 3`: a skipped
slot has no certificate for any of its candidates
(`MahiMahi.certificates_eq_empty_of_directSkip`); two certified
candidates of one author and round coincide
(`MahiMahi.eq_of_certificates_nonempty`); two views deciding one slot
agree (`MahiMahi.decided_unique`); and conservativity at `w = 3` — a
derivation of the arc's relation is a derivation of the core's
(`MahiMahi.core_decided_of_decided`), and the direct commit predicates
coincide on every candidate at its own round. Conservativity holds in
one direction, and the reason is a finding about the core: the core's
`directSkip` quantifies over the candidates, a quorum of blames *per
twin*, whereas the implementation and this arc blame the *slot*. The
arc's premise is the stronger, so its derivations are the core's; the
converse fails when a leader equivocates and its twins' blaming quorums
differ. The core's rule is safe either way — its proofs go through per
twin — but it skips in a corner where the implementation leaves the
slot undecided. On a slot with at most one candidate the two coincide.

### 17.2 What a wave commits, with no network hypothesis

`goodAt U w r` is the set of validators whose round-`r` block is
directly committed at wave `w`; `good U w k` is the same at a slot's
round. A property of the DAG alone. The counting results bound it from
below under the fault model, validity, and population by a reliable
quorum `T` at **two** rounds — the one that supplies a common core and
the decision round — and nothing else.

The common core is the core's own T3c: if any round-`(r+2)` block
exists, a correct round-`r` block lies in the cone of every block at
every round `≥ r + 2` (`MahiMahi.exists_commonCore`, which is
`exists_common_correct_ancestor` carried upward). The paper's Lemma
C.12 was therefore already in this development. From it, **MM2**
(`MahiMahi.Counting.holds`): at every `w ≥ 4` some correct validator's
round-`r` block is directly committed — every voting-round block
reaches the common core, so every decision-round block certifies it
(`MahiMahi.goodNonempty`); at every `w ≥ 5`,

    n − f ≤ |goodAt U w r ∩ Correct| + |byzantine|

(`MahiMahi.goodCard`) — the round-`(r+1)` common core is reached by
every voting-round block, and through it each of the `n − f`
distinct-creator round-`r` blocks it references; those by correct
authors are voted for by everyone. And **MM2b**
(`MahiMahi.multiLeader`): with `2f + 1` distinct validators leading
slots at a round and `w ≥ 5`, one of those slots is good, for every
schedule and with no randomness clause.

The `w ≥ 5` count differs from the paper's. Lemma C.13 there counts all
`n − f` references of the common core as committable; a reference by an
equivocating author is not, since a voting block whose cone also holds a
second twin votes for whichever its support rule orders first, and the
adversary can expose the other twin to part of the voters so that no
twin of that author gathers a quorum. What the argument proves is the
bound on the correct references: at `n = 3f + 1` with `f` equivocators,
`f + 1` good correct validators, a commit probability of at least `1/3`
per wave under a uniform draw rather than `2/3`, and `2f + 1` leader
slots for a deterministic commit where Lemma C.15 has `f + 1`. The
paper's count holds in any wave whose round-`r` authors do not
equivocate, which is the hypothesis under which Cordial Miners states
the same `2/3`; the protocol's liveness needs only a constant fraction
and is unaffected. The `aim4` witness (§17.5) shows the four-round count
tight: an adversary aiming at slot `1` leaves `goodAt = {0, 2, 3}` on
four validators, and round-robin names exactly the validator that is
not good; at `w = 5` the same DAG has every validator good.

### 17.3 The clause, and liveness under it

The model has no adversary and no time, so "the leader is revealed
after the wave" cannot be said directly. What can be said is its
observable consequence on the pair (schedule, DAG): the leader keeps
landing among the committed candidates.

```lean
def UnpredictableWithin (U : BlockUniverse Validator BlockId Payload)
    (w c N : ℕ) : Prop :=
  ∀ k,
    decisionRound Validator w (k + c) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U w k'
```

In words: in every window of `c` consecutive slots below the horizon
`N`, the schedule names a validator whose block the DAG actually
committed. Compare the core's `FairScheduleOn` and its rated form
`FairWithin`: the shape is the same, and the fixed target set `T` has
become `good U w k'`, a property of the DAG. Under partial synchrony the
schedule need only hit a *correct* validator, because synchrony then
guarantees that validator's block commits (L4); under asynchrony nothing
about a validator guarantees that, so the hypothesis must relate the
schedule to the DAG. No clause on the schedule alone can serve: for
every deterministic schedule the adversary starves the named leader's
block, which is the aiming pattern of `aim4`. The horizon `N` is in the
definition because identifiers form a `Finset`, so `good` is empty past
some round and no finite DAG satisfies an unbounded `∀ k`. The clause
says nothing about how the leader is chosen, and carries no probability:
a uniform draw after the wave lands in `good` with probability at least
the bound of MM2, so `c` consecutive misses have probability at most
`(1 − p)^c`, and the clause holds with probability one; any mechanism
with the same effect qualifies, and the measure stays in prose exactly
as GST does for the core.

A commit does not decide every slot below it: a slot is decided through
its lowest eligible slot, and an undecided slot there blocks it, so
commits at rounds `10, 20, 30, …` leave slot `17` undecided forever at
`w = 4`. Deciding every slot needs a *run* of consecutive committed
slots spanning eligibility — the core's `FairRunOn` and
`SpansEligible` under synchrony — and the clause has a run form,
`UnpredictableRunWithin`, accordingly. **MM3**
(`MahiMahi.Liveness.holds`): a good leader's slot is committed in the
full view (`MahiMahi.decided_of_mem_good`); under the single-hit clause
every window below the horizon commits a slot; under the run form with a
spanning run length every slot below the run is decided
(`MahiMahi.allDecidedBelow`, the core's descent transcribed at wave
`w`); and every reliable validator commits a candidate certified by
every reliable decision-round block on its own view, at the explicit
time `max (latest d) gst + delay` (`MahiMahi.localCommit`), the pacing
structure's convergence read as eventual delivery — no `gst ≤ R`, no
backoff. **MM2′** (`MahiMahi.AgreeUpto.goodAt_eq`) is the measurability
fact the informal "revealed in the last round of the wave" rests on:
two universes agreeing on the blocks at rounds up to the decision round
have the same `good`.

On data (§17.5): round-robin satisfies both forms of the clause on the
fully connected universe; on the aiming pattern it satisfies the core's
`FairScheduleOn Correct` and violates the clause — so the clause is not
a consequence of fairness, and Mahi-Mahi under a predictable schedule
is not asynchronously live, which is the reason the coin exists; and
the single-hit clause holds where the run form fails, so the two are
distinct hypotheses.

### 17.4 Partial synchrony, recovered

The arc remains usable by the partially synchronous development. **MM5**
(`MahiMahi.Synchrony.holds`): under the core's coverage hypothesis
`SynchronisedOn` at a slot's round, a reliable leader's block is a
committed candidate at `w ≥ 4` (`MahiMahi.good_of_synchronisedOn`) —
coverage at **one** round suffices, where L4 needs it at two, since once
every reliable round-`(r+1)` block references the candidate every block
two rounds up reaches it through its reference quorum; and hence under
coverage from the start and population through the horizon the clause
is *derived* from `FairWithin`
(`MahiMahi.unpredictableWithin_of_synchronisedOn`). The two liveness
accounts are one: under synchrony the clause is discharged by fairness,
under asynchrony by the coin.

### 17.5 The partition, and the witnesses

The arc is laid out as `Model/` (definitions only, theorem-free),
`<Result>/Statement.lean` (definitions and a `def Statement : Prop`,
never a proof), `<Result>/Proof.lean` and `Helpers/` (generated,
unaudited), with `scripts/check-mahi-mahi-holes.py` rejecting proof
holes anywhere in the arc, proofs in a statement file, and theorems in a
model file. The audited surface is the model files, the four statement
files and the witness instantiations; each phase ran as statements →
review → freeze → proofs, and every `holds` depends on the three
standard axioms. The witnesses (`LeanDagTest/MahiMahi/`) are four
validators with one Byzantine: `full4`, six fully connected rounds, on
which every predicate is settled by `decide` at `w = 4` and `w = 5` and
the `w = 3` predicates agree with the core's; `twin4`, two twins in one
voter's cone, where the vote goes to the least and only the least;
`aim4`, the aiming pattern, with the common core, `goodAt` at both wave
lengths and the statement hypotheses pinned; `multi`, three leaders per
round; and the clause witnesses of §17.3.

## 18. Satisfiability

Every structure carrying conditions is exhibited satisfiable by a concrete model
over four validators at `f = 1`. This is a substantive component of the
development rather than a testing exercise: an unsatisfiable hypothesis renders
every theorem above it vacuous, and vacuity is not otherwise detectable.

| Model | Satisfies |
|:---|:---|
| `Ugrow N` | `Populated` and `Synchronised`, at every horizon `N` |
| `ugrowHonest` | `Delivery` with a genuinely partial view: the Byzantine validator withholds, and a quorum nonetheless survives |
| `ugrowTimingPace` | `ViewPace` in lockstep, with a rated `2^n` backoff |
| `ugrowSkewPace` | `ViewPace` with nonzero drift and delay, its spread pinned at the collapse bound `Δ + proc` (CU1) |
| `ugrowStuckPace` | `ViewPace` genuinely stuck: `top = 0` under a horizon of `5`, round `1` unpopulated |
| `ugrowLag` | `ViewPace` from a spread of ten, collapsing to exactly `Δ + proc` (CU4) |
| `ugrowSkewCorrect`, `ugrowSkewDelivery` | a pacing structure over `Correct`, and the `Delivery` it induces (V19) |
| `Dtwin` | `UniformBudget Dtwin 3` and `ByzBudget Dtwin 0`: the acceptance budget, on a schedule with a real equivocation |
| `rrSlots` | `Slots`, round-robin, satisfying `FairWithin T (f+1)` and `BoundedSpacing 3` |
| `waveRobin n` | `Slots` at *every* `n`: the wave-aligned rotation, whose `FairRunOn Correct 3` and `SpansEligible 3` are theorems with no premise beyond the fault model (L12) — the one schedule family not pinned to a committee |
| `Model.lean` | six `BlockUniverse` instances exercising the safety definitions |
| `Ucrash N`, `ucrashMsg` | `SkipMsg`: a crashed line, the message against it, and the fill (SS7) |
| `ucrashJump` | `JumpMsg`: the compact core of `ucrashMsg`, elaborating to the same fill (SS11) |
| `demotePolicy`, `run7` | `AdaptivePolicy`, `AdaptiveRun`, `PlacesRuns`: a genuinely adapting policy and its total runs (AL8) |
| `Uhyb4`, `Uhyb9` | `HybridFaults`, `HonestNoEquiv`: one crash at four validators; the tight hybrid committee (H9) |
| `UtightA`, `UtightB` | the one-short committee: agreement refuted at every threshold (H10) |
| `Unemo` | `CrashFaults` at the tight crash committee: three validators, one halted line, every decidable rule settled by `decide` (NN9) |
| `skTight` | the fill of `Ucrash` at which coverage is refuted (I4) |
| `Ucut`, `Uregen`, `urecover` | the severed validator, its re-genesis, and the catch-up message over it |

Three of the models are tight, which is what renders the constants meaningful.

- `ugrow_not_populated_succ` establishes `¬ Populated (Ugrow N) (N+1)`: the family
  reaches round `N` and stops, so the horizon is exact.
- `ugrowSkewPace` lies on the boundary of the wait bound. Its spread is `2`,
  its `delay` is `2`, its `proc` is `0` and its `timeout` is `4`, so that
  the spread equals the collapse bound `Δ + proc` and
  `2Δ + proc = timeout`: every inequality of the wait bound holds with
  equality, and the accumulated honest floor of the rush bound (CU5) is
  met with equality on the same schedule. The constant is therefore
  exact rather than a conservative estimate.
- `rrSlots_fairWithin` gives the window `f + 1 = 2`, and `f + 1` is forced, the
  validators outside the reliable set being permitted to occupy consecutive
  positions in the rotation.

One negative observation should be recorded. A model exhibiting *round spread* —
correct validators separated by many rounds — while still committing is impossible
at `f = 1`, since `|Correct| = 3 = n−f` exactly, so that every correct validator
is required for a quorum and none may lag. Such a model requires `f ≥ 2`. This is
the combined fault budget of §4.2 appearing as a concrete obstruction rather than
as an inequality.

The conditions of §§7–15 are witnessed in the same style, at their own
boundary instances: chain quality on `Ucens` (CQ8) — the one model that is
simultaneously CQ1's tightness witness (`missingAt = {3}` at every layer
of the committed cone, exactly `f`) and the censorship exhibit
(`Synchronised` fails at every round while the commit stands); `DoSValid` satisfiable and biting (`Uexcl`, with the exclusion
chain and a commit after it), the budget satisfiable at its exact constant
(`UniformBudget Dtwin 3` with `ByzBudget Dtwin 0`), the horizon computed and
its statute of limitations exhibited (`chop Uexcl 2`, `chop Umerge 1`), the
attested base sandwich tight at the bottom (`Base Utwin 1 0 = {1,2,3}`), and
every Odontoceti rule and all four `Decided` constructors at `n = 6, f = 1`
(`Uodo`, `Uskip`, `Utwin6`), including the two-twin configuration that
motivates the canonicity premise (`utwin6_both_pass` (O11)). The reactive
schedule is witnessed at §11.4's `ugrowReactive`, and Safe Skip on `Ucrash`
(SS7): the fill's reference sets and cardinality computed by `decide`, the
gap populated, the filled candidate skipped, and `decided_fill` applied to
the full view with its quorum hypothesis discharged by counting the three
live authors. The jump message is witnessed on the same family (SS11):
`ucrashJump` carries `ucrashMsg`'s four names and no line, its
elaboration reproduces the hand-written line (`ucrashJump_line_eq`),
and the two denotations agree (`ucrashJump_denote_eq`). Adaptive leaders are witnessed on `demotePolicy` (AL8): the
same DAG under a reassigned leader commits a different block on both
rules, a vacuous skip moves a later slot's leader off the base rotation,
and two views' total runs are constructed and shown identical by AL3.
The hybrid model is witnessed at both of §14.7's committees (H9), and
the one-short committee's two attack universes carry the tightness
refutation (H10). The crash arc is witnessed on `Unemo` (NN9), §15.5's
three-validator committee with one halted line: the crashed slot is
settled by `indirectSkip` off two adjacent commits, `Populated` fails
past the horizon, and the round-robin fairness clause is proved rather
than assumed.

The integration constructions are witnessed on the scenario they all
describe: validator `3` of `Ucrash`, crashed after its genesis block
and severed by a horizon at round `1`. `Ucut` is the truncation and
`ucut_severed` confirms by `decide` that the validator has no block in
it at all; `Uregen` adds the derived genesis, with its uniqueness
clause and `dosValid_addGenesis` checked over it; and `urecover` builds
the catch-up message anchored on that block, so the composite recovery
of §16.6 is exhibited end to end rather than assumed composable. The
refutation of §16.3 is witnessed on the same family
(`ucrash_not_synchronisedOn`), which is what makes it a refutation
rather than an unsatisfiable hypothesis.

---

## 19. Mechanisation

The development comprises approximately 27,000 lines of Lean 4 (v4.32.2)
against Mathlib, of which some 18,000 constitute the library and 7,500 the
models of §18 and the witness files of the arcs. A full build reports no
errors.

**Axiom audit.** Every principal result — among them
`reaches_of_quorum_support`, `exists_common_correct_ancestor`,
`decided_agree`, `commitSeq_agree` (M7), `outputAt_agree` (M9), `ViewPace.populatedOn` (V17),
`commits_recur_on`, `ViewPace.commits_recur_via_pace`,
`all_decided_below_of_fairRun` (L10), `card_history_le'`, `dos_resistance`,
`decided_chop`, `decided_agree_chop`, `card_retained_le`, `bootstrap_agree`,
`chop_chop`, `Odontoceti.decided_unique`, `Odontoceti.safety` and
`Odontoceti.all_decided_below_of_fairRun`, `chain_quality`,
`committed_of_correct_block`, `SkipMsg.decided_fill` (SS5) and
`SkipMsg.decided_fill_agree` (SS6), `SkipMsg.skipFill_eq_of_core` (SS9)
and `JumpMsg.denote_eq_of_core` (SS10), `adaptiveRun_agree` (AL3) and
`adaptiveRun_exists` (AL5), `Hybrid.decided_unique` (H6),
`Hybrid.safety`, `hybrid_bound_necessary` (H10), `Nemo.decided_unique`
(NN5), `Nemo.outputAt_agree` (NN6) and
`Nemo.all_decided_below_of_fairRun` (NN8), and
`hybrid_agree_stack` (I7) — depends on exactly `propext`,
`Classical.choice` and `Quot.sound`, which constitute the whole axiom set of
Lean 4. No result depends on `sorryAx`, on any bespoke axiom, or on
`native_decide` and the extended trusted base it entails.

**The core.**

| Module | Contents |
|:---|:---|
| `Validators.lean` | the fault model (`n ≥ 3f+1`); T0 |
| `Block.lean` | `Block`, `ValidWrt`; T0′ |
| `BlockDag.lean` | `BlockUniverse`, `View`; T1 |
| `CausalHistory.lean` | `Reaches`; T2, T6a |
| `Support.lean` | counting vocabulary; the hitting, propagation and coverage lemmas |
| `History.lean` | causal history as a `Finset` |
| `Persistence.lean` | T3 |
| `CommonCore.lean` | T3a, T3c |
| `Mysticeti.lean` | the commit rule; eligibility; M1–M6; the ledger |
| `Schedule.lean` | concrete schedules (`uniform`, `uniformSingle`); conservativity |
| `Liveness.lean` | L0, L2–L6; the committed-run results |
| `Network/Quorum.lean` | the DoS capstones, production bundled with the storage bound |
| `ViewPace.lean` | the route (§6.9): the structure, V1, V4, coverage, production, the spine, and the quantitative results L8a, L9, L11 |
| `Quantitative.lean` | the rated hypotheses; L8b |

**The arcs** (§§7–15). All but the last consume the core read-only; §16 weakens one hypothesis of §12, for the reason given there:

| Module | Contents |
|:---|:---|
| `DoS/Exposure.lean` | `ExposedIn`, `DoSValid`; exposure ≤ `f` per cone |
| `DoS/Acceptance.lean`, `DoS/Counting.lean` | the acceptance rule; view size from history size |
| `DoS/SelfParent.lean`, `DoS/Adoption.lean`, `DoS/Pedigree.lean` | the adoption collapse; pedigrees; the general per-cone bound |
| `DoS/Density.lean` | histories are almost all of the correct past |
| `DoS/Novelty.lean` | the novelty budget; the budget sandwich; `dos_resistance` |
| `DoS/Composition.lean` | the two conditions composed; the pool freezes |
| `DoS/Exclusion.lean` | liveness survives exclusion; the correct backbone |
| `GC/Chop.lean` | the horizon operator; per-slot verdict invariance |
| `GC/ChopDecided.lean` | the induced schedule; `decided_chop`, `decided_agree_chop` |
| `GC/Window.lean` | windowed novelty and stores; `card_retained_le` |
| `GC/AttestedBase.lean` | the inexact certificate, sandwiched |
| `GC/Bootstrap.lean` | window completeness; the joiner's view; `bootstrap_agree` |
| `GC/Horizon.lean` | `chop_chop`; heterogeneous-horizon agreement; the depth rule |
| `Odontoceti/Rules.lean` | the two-round rules; the arithmetic core O1–O4′ |
| `Odontoceti/Decision.lean` | the decision relation with canonicity; agreement |
| `Odontoceti/Liveness.lean` | O7–O10 |
| `Reactive/Basic.lean` | the reactive dichotomy; the vote; the fast path |
| `Reactive/Mysticeti.lean` | the certificate stage; reactive liveness, three rounds |
| `Reactive/Odontoceti.lean` | reactive liveness, two rounds, from the core alone |
| `Drift/Catchup.lean` | the catch-up clause; the collapse; the deployment-free threshold |
| `SafeSkip/Basic.lean` | the message and its denotation; the fill is a universe; production restored; the filled candidate skipped |
| `SafeSkip/Invariance.lean` | conservativity at the rule layer; verdict invariance; agreement across a recovery |
| `SafeSkip/Jump.lean` | the self-parent function; the derived line; the jump message and its elaboration |
| `Adaptive/Basic.lean` | epochs; the induced instance; the bounded relation, its embedding and congruence |
| `Adaptive/Policy.lean` | the reassignment policy and its clauses |
| `Adaptive/Run.lean` | the adaptive run; safety as uniqueness; conservativity; the agreed ledger |
| `Adaptive/Liveness.lean` | the bounded descent; the fairness clause; existence |
| `Adaptive/Odontoceti.lean` | the two-round mirror |
| `Hybrid/Faults.lean` | the hybrid model; the derived instance; `HonestNoEquiv`; the counting core |
| `Hybrid/Rules.lean` | the rules at the admissible interval; the arithmetic core H2–H5 |
| `Hybrid/Decision.lean` | the decision relation with canonicity; agreement |
| `Hybrid/Liveness.lean` | the liveness chain at quorum `q` |
| `Hybrid/Conservativity.lean` | the crash-free collapse onto Odontoceti |
| `Integration/Preservation.lean` | the layer-U preservation lemmas |
| `Integration/Coverage.lean` | coverage refuted under the fill, and recovered above it |
| `Integration/ScheduleShape.lean` | fairness and shape under truncation |
| `Integration/Joiner.lean` | horizon-stability; epoch alignment |
| `Integration/Retention.lean` | anchor retention; the outage bound; the severed chain |
| `Integration/ReGenesis.lean` | re-genesis at the cut; convergence; the exposure condition |
| `Integration/Stack.lean` | the composition capstone |
| `Integration/Lifecycle.lean` | the crash-prone lifecycle |
| `Integration/Exposure.lean` | the fill's cone growth; the enforceable exposure check |
| `Integration/DeliveryFill.lean` | the fill's delivery layer, and the budgets over it |
| `Integration/Margin.lean` | the budget without the author; severance and the fault budget |
| `Integration/CommonTarget.lean` | fills against a common-core target |
| `Nemo/Basic.lean` | the majority quorum and its intersection; crash validity; the universe with universal non-equivocation |
| `Nemo/CausalHistory.lean`, `Nemo/History.lean` | reachability and the finite cone, restated over the crash universe |
| `Nemo/Support.lean` | the hitting, coverage and propagation lemmas at the majority |
| `Nemo/Rules.lean` | the wave-two rules: the vote is the certificate; link integrity |
| `Nemo/Decision.lean` | the three-constructor decision relation; agreement without hypotheses; the ledger |
| `Nemo/Liveness.lean` | the crash bound and its bridge; the commit half; the descent |
| `MahiMahi/Model/Rules.lean`, `MahiMahi/Model/Decision.lean` | the rule at wave `w`: canonical support, certificates, the direct rules, the decision relation |
| `MahiMahi/Model/Good.lean`, `MahiMahi/Model/Unpredictable.lean` | the committed candidates of a wave; the clause in both forms; agreement below a round |
| `MahiMahi/Safety/`, `MahiMahi/Counting/`, `MahiMahi/Liveness/`, `MahiMahi/Synchrony/` | the four statements and their proofs (MM1, MM2, MM3, MM5) |
| `MahiMahi/Helpers/` | the generated lemma layer |
| `Quality/Coverage.lean` | `coveredAt`; per-commit and ledger coverage (CQ1–CQ3) |
| `Quality/Inclusion.lean` | post-`R` inclusion (CQ5, CQ6) |
| `Quality/Capstone.lean` | the windowed bounds and `chain_quality` (CQ7) |
| `LeanDagTest/` | the models of §18 and the witness files of every arc |

**The support graph, extracted.** The dependency structure of the
development is not documented by hand: `scripts/DepGraph.lean` walks
`Environment.constants` and records, for every declaration, the constants
appearing in its type **and in its body** — for a theorem, that body is
the proof term, so the edges are the real proof structure rather than the
statement's signature. `scripts/depgraph.py` then takes its node set from
Appendix A of this report, contracts paths running through unlabelled
lemmas, takes the transitive reduction, and renders the result. The full
graph is ≈900 declarations and ≈7,700 edges; the two views drawn here are
the §6.10 figure and the one below.

Two details govern the extraction. `ConstantInfo.value?` returns `none`
for *imported* theorems in this Lean version, proofs being loaded
lazily, so the proof term is reached by matching `.thmInfo` explicitly;
otherwise only statement-level dependencies appear. Private declarations
and compiler-generated auxiliaries are kept as pass-through nodes, since
a labelled result frequently reaches another only through one of them.
Mathlib and core constants are dropped, and safely: they never mention a
constant of this development, so no path between two of its results can
run through them.

![**The whole development.** The same extraction over every principal result, including the arcs. Reading the columns: the core account occupies the left half, and each arc attaches to it at the results it consumes rather than at the top — the garbage-collection operator (G1) sits beside the structural theorems it re-uses, and Odontoceti's counting core (O1–O4′) is independent of Mysticeti's, converging only at its own agreement theorem. Lean names are omitted for legibility; the full-detail rendering is in `docs/depgraph/`.](depgraph/support-full-compact.svg)

The extracted edges are also an independent check on this report's prose,
and three of its claims come out exactly as written. `P3′`, the
self-parent clause, feeds C1′, B7, G1, SS1 and — since the rotation
backbone — RS5, which is §2.2's assertion that safety never consumes it,
that its one liveness consumer is §11.5's, and that it is indispensable
to the denial-of-service, garbage-collection and safe-skip arcs. `L7 ← N2, P7,
P9` reproduces the §4.4 table row for row — coverage drawing on the
network column and the two protocol clauses, with non-equivocation
nowhere in it, since the route's referencing clause is stated over any
authored block and leaves nothing to identify. And
`O5 ← O1, O1′, O2, O3, O4′` confirms that Odontoceti's agreement rests on
exactly the four counting theorems plus twin uniqueness (§10.3), with
`O4′` — the lemma the published argument lacks — evidently indispensable.

Ten companion documents accompany the development and carry the design
rationale in more detail than a report admits: `spec.md` (safety),
`liveness.md` (liveness), `pipelining-and-multi-leader.md` (the schedule
generalisation), `chain-quality.md` (§7),
`dos-equivocation-and-growth.md` (§8), `garbage.md` (§9),
`odontoceti.md` (§10), `adaptive-leaders.md` (§13),
`hybrid-plan.md` (§14) and `integration.md` (§16), with `related.md`
surveying the surrounding
literature. Every statement in this report is drawn from the source.

---

## 20. Discussion

The first four subsections concern the core account's central design
choice — where the synchrony assumption lives; §20.5 draws the lessons of
the three extensions; §20.6 records what remains open.

### 20.1 Locating the synchrony assumption

The synchrony assumption may be stated in terms of views:

> beyond GST, if a correct validator holds a view `V₁`, then within Δ the views
> of all correct validators contain `V₁`.

This is a statement about the network, and as such it is complete: it says
everything about delivery that the development requires. It is also attractive
formally, `View` being already a first-class structure with inclusion already
meaningful and every safety result already view-relative, and it yields L3
immediately, the common view being `View.full`.

What it does not do is determine what blocks *look like*. Reference coverage is
a property of blocks, and blocks are produced by validators according to the
protocol, so it depends on the specification as well as on the network. This is
not a deficiency in the assumption; it is a consequence of coverage being a
derived property rather than an assumed one (§4.4).

Three observations follow, and they are the content of the section.

**The protocol must specify a wait, and this is a design obligation rather than
a gap in the assumption.** Consider `f = 1` with validators `{A,B,C,D}`, all four
correct, and instantaneous delivery, so that the network assumption holds in its
strongest form. Suppose the specification directs a validator to build as soon as
it holds `n−f = 3` blocks of the round below, and suppose `A`, `B` and `C` are
marginally faster than `D`. Each of them then forms the quorum `{A,B,C}` and
builds before `D`'s block arrives, so no block of theirs ever references `D`'s.
Every block is valid, views converge perfectly, and `SynchronisedOn U Correct R`
fails for every `R`.

What this exhibits is a badly specified protocol under a well-behaved network.
The remedy lies in the specification: P9 directs a validator to wait a full
timeout rather than to build on the arrival of a quorum. The example is worth
including because the incorrect rule is the natural one — the quorum is exactly
what validity requires — and because it shows that promptness and coverage are
in tension, which is what P9's two halves jointly resolve.

The example does not show a view-shaped assumption to be *inadequate*.
View convergence is adequate but **incomplete**: it is the network half
of a two-part derivation whose other half is a protocol clause, and §6.9
proves both. What the counterexample shows is that the missing half
cannot be supplied by strengthening the network, which is already as
strong as it can be — delivery there is instantaneous. The gap is a
*race* between arrival and building, which only the builder's own schedule
can resolve.

**The threshold the specification must meet is `2Δ + proc`, not Δ.** This
is the one point at which a network parameter enters the protocol's
constant, and it is the substantive quantitative result (§6.10).
Validators enter a round at different times, so a wait must accommodate
the propagation bound *and* the spread between validators; the
pacemaker's catch-up rule contracts that spread to `Δ + proc` at the
first fully-post-GST round (§6.11), so the threshold is the collapsed
spread plus one delivery — with no hypothesis anywhere about how the
validators started. At instantaneous entry, `proc = 0` and the threshold
is `2Δ`.

Because Δ is not known to an implementation, no constant can be fixed in
advance. A backoff is the specification's response — a search for a sufficient
constant, written into the algorithm — and its only relevant property is that
the search terminates (§20.2).

**The network guarantee must be indexed to the moment of building.** A block's
references are fixed at its construction, so what bears on the derivation is not
what a validator holds eventually but what it held when it built. `View.ids` is a
finite set of identifiers with no temporal index, so a view-convergence statement
cannot be applied directly. `Delivery.held : Validator → ℕ → Finset BlockId`
supplies the index for the storage arcs — `held v n` denotes what `v` had
in hand when building for round `n+1` — and `ViewPace.holds` supplies it
for liveness, indexed by the instant, with `built` ordering the two. The
requirement is the index, not the vehicle. This is an observation about formalisation, and it is the
reason `SynchronisedOn` is stated on `refs`.

### 20.2 Why coverage is derived rather than specified

Reference coverage could not have been made a clause of the protocol, which is
the deeper reason it appears as a derived property. `SynchronisedOn` refers to
`Correct`, a model-level object, so an instruction to reference every correct
block of the round below would name two quantities a validator cannot determine:
which of the blocks it holds are correct-authored, and whether all of them have
arrived, a missing block being indistinguishable from one never published.

What a validator can be directed to do is wait a fixed period, build upon
whatever has arrived, enter any round it sees evidence of, and increase
the period when progress fails. These are `waits`, `catchup` and the
backoff — P9 and P11 together with R1 — all of them executable.

The signal driving the backoff is the difficulty. Before GST no period is
sufficient, and nothing permits a validator to detect this directly; what it
observes is that commits have ceased. The feedback loop which delivers coverage
is therefore driven by liveness failure, the very condition being proved away.
This is a feedback loop rather than a circularity, but it means the argument
cannot rest on modelling the loop's dynamics.

The development accordingly does not model it. What the coverage
derivation consumes is a threshold — the timeout remains above `2Δ + proc`
from some round onwards — with no condition on shape, rate, or driving
signal. §6.10 carries this to its conclusion: with Δ known, a constant
timeout of `2Δ + proc` suffices and the loop disappears.

### 20.3 Consequences of the abstraction

1. The consensus argument is purely combinatorial, involving round indices and
   finite-set cardinalities. Under a message-level assumption every statement
   would carry instants.
2. The temporal content is confined to a single module and consumed through a
   single definition.
3. The condition admits two independent derivations (§6.7, §6.8) and a third,
   quantitative route (§6.11), against an unchanged statement.
4. The condition composes with the safety development, mentioning only `U.ids`,
   `U.block` and `refs` — the vocabulary that development already employs.

### 20.4 Costs

Δ does not appear above the interface. Introducing it would require views indexed
by an instant and every statement quantified over instants, for no proof content.
The quantitative statements recover what is needed *below* the interface without
propagating time upward.

Coverage being derived rather than assumed does not make it unconditional. The
derivation rests on view convergence, and in the absence of a time model the
chain must terminate at a network assumption; what the reformulation achieves
is to place that assumption where it belongs — on the network, as one clause
over views — and to keep it out of every statement above.

### 20.5 Lessons from the extensions

Three lessons generalise beyond the particular arcs.

**Additivity is a measurement of abstraction.** Every extension of
§§7–14 was carried out without modifying a line of what it consumed:
the DoS arc took the delivery layer and the self-parent clause as
found; garbage collection took every theorem verbatim because
`chop U G` was arranged to *be* a `BlockUniverse`; Odontoceti took the
whole DAG layer because its quorums are the `n − f` the development is
parameterised by. When an abstraction is placed correctly, new
developments read like instantiations; when it is misplaced, they read
like refactors. The one refactor resisted — a rule-parameterised
decision relation shared between §3.5 and §10.3 — is the cost of that
discipline, incurred twice in mirrored proofs rather than once in
modifications to the core.

§16 is the exception, and a measured one. Composing §12 with §14
required weakening a hypothesis of §12 — `v1 ∈ Correct` to the fact
that clause was used for — because the composition was otherwise
**unstatable**: §14 splits `Correct` into honest and available, and the
crash-prone validator Safe Skip serves is honest but not correct. The
change is conservative, one field and one proof line, and it is a
different act from a refactor. The rule it suggests is that existing
code may be modified when a result cannot otherwise be stated, and not
for elegance — which is why the rule-parameterised relation above is
still resisted.

**Enforceability is a specification discipline.** The principal result of §8
(`dos_resistance`) quotes only conduct a validator can execute — an
author-blind budget, a reference rule — and no condition that consults an
identity oracle; the cost of author-blindness is a factor of `f` in a
constant, never a theorem. The same discipline shapes §9: horizons are set
by local rules, the attested base replaces agreement with `f+1` sampling,
and every hypothesis of the bootstrap theorems is checkable by the party it
binds. Conditions of this kind survive contact with implementations;
conditions that quantify over `Correct` do not.

**The value of mechanisation is concentrated where equivocation meets
counting.** All four §10
findings — the canonicity gap, the missing uniqueness lemma, the
blocks-versus-authors ambiguity, the exact-complement subtlety — live where
an equivocating author interacts with a counting argument, precisely the
territory that uncertified DAGs annexed when they discarded certificates,
and precisely where hand proofs compress the most. The counterexample
behind the canonicity gap fits in six validators and twenty-five blocks;
what was needed to find it was not scale but the obligation to state the
indirect rule precisely enough to fail to prove it.

### 20.6 Limitations

The quantitative bounds are established (§6.10). The following remain open.

**The backoff loop.** `Rated` and the threshold of R4 are stipulated as clauses
of the specification; no realistic adaptive scheme is shown to satisfy them, and
the feedback mechanism of §20.2 is not modelled. Moreover
`ViewPace.timeout : ℕ → ℕ` is indexed by round and common to the reliable set, so
that a per-validator backoff — in which validators increase their timeouts at
different moments — cannot be expressed, let alone shown to converge. This
requires a refinement of the structure.

**Wall-clock latency.** `Delay(Δ)` is a duration, but the total elapsed time to a
commit is not derived: converting a bound of the form "`3k + 8` rounds, each of
at least `2Δ`" into elapsed time requires a lemma accumulating an upper
bound on round duration — the catch-up deadline — across rounds, which is
not present. `ViewPace.le_built` relates rounds to time in one direction
only.

**Byzantine leaders.** §6.10 bounds the wait until the next reliable leader,
which sidesteps rather than answers the question of how distant an indirect
anchor may be when the leader is Byzantine.

**Leader predictability.** `Slots.leader` is an arbitrary function, so nothing
distinguishes a schedule an adversary can predict from one it cannot, and
targeted denial of service against a known future leader — the network sense,
distinct from the storage-exhaustion sense §8 bounds — is invisible to the
model. `FairWithin` constrains when reliable leaders occur, not whether they can
be anticipated.

**Block-level total order.** The blocks released by a single commit are not
ordered among themselves, for the reason given in §5.6.

**No liveness below P8.** Every liveness result here is conditional on P8, and
nothing is offered for executions violating it. [QXS26] proves a *weak liveness*
result which is not: without any restriction on round-jumping, every leader block
created by an honest validator after GST acquires at least `f+1` certificates
from honest validators, so it can never be indirectly skipped, only left
undecided. The corresponding statement is not available here, and the obstruction
is identifiable. Density (L0) yields `n−f` distinct authors at round `r+1`
whenever the DAG reaches above it, hence `f+1` *correct* authors, and coverage
makes each of their blocks reference the leader — so `f+1` correct **supporters**
is within reach from L0 and `SynchronisedOn` alone, with neither `Populated` nor
P8. A certificate, however, requires `n−f` distinct supporters, and
`SynchronisedOn` is honest-to-honest (§6.6), so the remaining `f` cannot be
obtained; reaching `n−f` supporters requires `n−f` correct authors at `r+1`,
which is `Populated` again. [QXS26] bridges the gap with a *predecessor rule* —
a validator creating a block must make it a supporter and a certificate where it
can — for which this model has no counterpart, P7 constraining what a validator
cites given what it holds but not obliging a quorum of supporters to exist. The
supporter-level statement is therefore the available result, and it is not their
theorem.

**Certified DAGs.** The certified variant, in which a certificate round is
explicit, is outside the scope of the present development.

None of these affects whether the stated theorems are true; each concerns how
much they say.

---

## 21. Related work

**Hybrid fault models.** Orcaella [KS26] derives the tight committee
`n ≥ 5f + 3c + 1` for two-round commitment under separate Byzantine
and crash caps, proves its core vote-counting protocol safe and live,
and instantiates it over an uncertified DAG (OrcDAG); the model
descends from a line of mixed-fault designs (Hydrangea, Kudzu —
surveyed in [KS26]) that provide optimistic fast paths with
PBFT-style fallbacks. §14 machine-checks both directions of its
Theorem 1 for the DAG rules — sufficiency at the generalized bound,
for every admissible threshold, and necessity on data one validator
short — and records the one point where the published DAG
instantiation is incomplete: its indirect rule needs the canonical
candidate selection the core protocol's view change already has
(§14.3), the same repair §10 supplies for Odontoceti. The additive
checkpoint arc is an assume-guarantee model: possibly forked
per-validator histories and messages are execution inputs, and from
them it machine-checks same-epoch checkpoint uniqueness, prefix
consistency, resilient finality, and highest-checkpoint recovery under
alive-but-corrupt signing faults. It does not derive an AbC-induced
fork from OrcDAG or compose checkpoint safety with the DAG proofs. It
treats `BaseSpec.lean` and `RecoverySpec.lean` as the human-reviewed
trust boundary, with derivations isolated in the two `*Proofs.lean`
modules. It
treats authenticated Byzantine broadcast through its agreement,
integrity, and correct-input delivery contract; the Dolev--Strong
implementation and executable cryptographic parsing remain outside the
model.

**Crash-fault DAG consensus.** Nemo-Nemo [Ker+26] carries the
uncertified-DAG rule to the crash-fault setting — `n ≥ 2f + 1`, a
majority quorum, wave length two, no signatures — and argues that CFT
systems built for wide-area networks should adopt the DAG structure
BFT designs converged on. §15 machine-checks the DAG rules' two
guarantees: agreement with no fault bound and no side conditions —
non-equivocation *is* the crash model — and liveness at the classical
bound, where the mechanisation sharpens the fairness requirement: the
protocol's direct-skip quorum is the full stake, so with no failure
detector every skip is indirect, a lone committed leader settles only
the slot two rounds below it, and progress requires committed leaders
at adjacent rounds (§15.4) — a clause round-robin satisfies by
counting but an arbitrary schedule need not. The protocol's deadline
deferral, multi-leader cohorts and WAN evaluation are performance
mechanisms outside the model.

**Certified and uncertified DAGs.** In a certified DAG — DAG-Rider, Narwhal with
Tusk or Bullshark [DKSS22, SGSK22], Sailfish [SSKN25] — a block is disseminated
by reliable broadcast and enters the DAG carrying a quorum of signatures, so a
reader may assume any block it sees is non-equivocated and available. The
uncertified variant descends from Hashgraph [Bai16] and Blockmania [DH18],
receives its modern form in Cordial Miners [KNPS23], and reaches its lowest
latency in Mysticeti [Bab+25], which removes the wave structure of Cordial Miners
by assigning a leader slot in every round. The trade is the one described in
§1.1: certification disappears from the critical path, and equivocation and
availability become the reader's problem.

The uncertified structure has since been reused with one parameter varied at a
time: Mahi-Mahi [Jov+24] under asynchrony, committing several leader slots per
round; Odontoceti [Van25] at `n = 5f+1`, buying a two-round commit with a weaker
fault threshold; Starfish [PMV25] with erasure-coded dissemination; Bluestreak
[PVM26] with a sparse reference structure, which abandons the rule that every
block cites a quorum below and so falls outside the present model. Shoal++
[Aru+25] argues from the certified side that certification is not the cause of
latency, and hybridises by committing anchors on `2f+1` uncertified proposals.

**Where the synchrony assumption is located.** In each of the above the
assumption is stated per message, in the sense of Dwork, Lynch and Stockmeyer
[DLS88]: beyond GST a message between correct parties arrives within Δ. The
consequence noted in §1.2 is that every subsequent statement is quantified over
instants. The present formulation instead states the assumption on the DAG, and
§6.7 and §6.8 derive it from the conventional one. The author is not aware of a
prior structural formulation, though the property itself is asserted repeatedly:
Mysticeti's Lemma 8 and Cordial Miners' Proposition 38 both claim post-GST
synchronisation of honest validators, and it is exactly these claims that
[PMV25] reports as gapped and [QXS26] refutes.

**Chain quality and fairness.** The chain-quality property originates
with the Bitcoin backbone analysis of Garay, Kiayias and Leonardos
[GKL15] — the fraction of honest blocks in any window of the chain —
and fairness claims for DAG protocols go back to Hashgraph [Bai16],
whose "fair ordering" was informal. The order-fairness line (Kelkar,
Zhang, Goldfeder, Juels [KZGJ20]) concerns transaction *ordering*
rather than inclusion and is orthogonal to §7's guarantees. The §7
statements differ from the backbone form in the direction the DAG makes
natural: coverage is per-flush and unconditional (a commit carries a
quorum-forced sample of every round below it), and inclusion is
individual and quantitative once synchrony holds — with a
counterexample separating the two, which the author has not seen stated
for this protocol family.

**Mechanised consensus.** Safety-only verification of DAG protocols exists in
TLA+ with TLAPS [Ber+24], covering DAG-Rider, Cordial Miners, Hashgraph, an
Aleph variant and eventually synchronous Bullshark, with a modular separation of
DAG construction from ordering. LiDO-DAG [QXS25] provides mechanised safety and
liveness in Rocq for Narwhal, Bullshark and Sailfish — all certified. The work
closest to the present development is [QXS26], which extends that framework to
Mysticeti itself and is discussed at length in §4.1, §4.4 and §6.6. Two
differences of method should be recorded. Theirs is an operational model: a
transition system over traces, with segmented traces encoding the unreliability
of timers before GST, and liveness reduced to safety properties of an abstract
pacemaker by refinement. The account here is structural, and no theorem above
§6.8 mentions time. The benefit of the structural style is visible in §6.6: the
dependence of liveness on the round-jumping clause surfaces as a named hypothesis
of a single lemma rather than as a condition inside a transition relation. The
cost is that the theorems of [QXS26] cannot be stated here at all, "within
bounded time" not being expressible in this vocabulary (§20.6).

---

## 22. Conclusion

This report has given a machine-checked account of uncertified DAG consensus
organised around one idea: state the liveness condition on the object the
protocol actually builds. Eventual DAG synchrony — beyond some round, every
correct block references every correct block of the round below — is a
sentence about a graph, and above it the entire consensus argument is finite
combinatorics: safety with no network assumption at all, liveness with no
mention of time, and the temporal content of partial synchrony confined to
two files beneath a `Prop`-valued interface, where the whole of the
network's contribution reduces to one clause of view convergence and the
structural condition is *derived* — three ways over (§6.7–§6.9).

The same foundation then carried three developments it was not designed for,
essentially unchanged — which is the strongest evidence the abstraction is
placed correctly. The denial-of-service account reused the delivery layer and
the self-parent clause; garbage collection reused every theorem verbatim on
the truncated universe, because truncation was arranged to be a universe; and
Odontoceti reused the entire DAG layer because its quorums are
the `n − f` the development was already parameterised by. Each arc also
returned something to the account of the trust boundary: enforceable storage
bounds, horizons
without consensus, and — in the one place the formalization diverged from a
published argument by necessity — the observation that Odontoceti's
agreement rests on a canonical candidate order that its paper never states.

What remains open is catalogued in §20.6: the backoff dynamics, wall-clock
latency, block-level total order, and liveness below the growth clause.
Beyond those, two directions suggest themselves. The commit-free,
evidence-based horizon rule sketched in the garbage-collection document
would extend pruning into asynchrony; and the decision relation, now
instantiated twice at different wavelengths with near-identical agreement
proofs, invites a rule-parameterised treatment — resisted here to keep each
development additive, but natural the third time a commit rule arrives.

---

## References

- [Aru+25] B. Arun, Z. Li, F. Suri-Payer, S. Das, A. Spiegelman. *Shoal++: High Throughput DAG BFT Can Be Fast and Robust!* NSDI 2025. arXiv:2405.20488.
- [Bab+25] K. Babel, A. Chursin, G. Danezis, A. Kichidis, L. Kokoris-Kogias, A. Koshy, A. Sonnino, M. Tian. *Mysticeti: Reaching the Limits of Latency with Uncertified DAGs.* NDSS 2025. arXiv:2310.14821.
- [Bai16] L. Baird. *The Swirlds Hashgraph Consensus Algorithm.* Swirlds Tech Report SWIRLDS-TR-2016-01, 2016.
- [Ber+24] N. Bertrand, P. Ghorpade, S. Rubin, B. Scholz, P. Subotic. *Reusable Formal Verification of DAG-based Consensus Protocols.* arXiv:2407.02167.
- [DH18] G. Danezis, D. Hrycyszyn. *Blockmania: from Block DAGs to Consensus.* arXiv:1809.01620.
- [DKSS22] G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman. *Narwhal and Tusk: a DAG-based Mempool and Efficient BFT Consensus.* EuroSys 2022.
- [DLS88] C. Dwork, N. Lynch, L. Stockmeyer. *Consensus in the Presence of Partial Synchrony.* JACM 35(2), 1988.
- [GKL15] J. Garay, A. Kiayias, N. Leonardos. *The Bitcoin Backbone Protocol: Analysis and Applications.* EUROCRYPT 2015.
- [Jov+24] P. Jovanovic, L. Kokoris-Kogias, B. Kumara, A. Sonnino, P. Tennage, I. Zablotchi. *Mahi-Mahi: Low-Latency Asynchronous BFT DAG-Based Consensus.* arXiv:2410.08670.
- [KZGJ20] M. Kelkar, F. Zhang, S. Goldfeder, A. Juels. *Order-Fairness for Byzantine Consensus.* CRYPTO 2020.
- [KNPS23] I. Keidar, O. Naor, O. Poupko, E. Shapiro. *Cordial Miners: Fast and Efficient Consensus for Every Eventuality.* DISC 2023, LIPIcs 281.
- [Ker+26] R. Kerur, P. Tennage, P. Jovanovic, D. Malkhi, A. Sonnino, I. Zablotchi. *Finding Nemo-Nemo: CFT DAG-based Consensus in the WAN.* 2026.
- [KS26] L. Kokoris-Kogias, A. Sonnino. *Orcaella: Hybrid Fault Tolerance with Client-Selectable Finality Latency.* arXiv:2607.04789.
- [PMV25] N. Polyanskii, S. Mueller, I. Vorobyev. *Making Uncertified DAG BFT Provably Live with Linear Payload and Quadratic Metadata Communication* (Starfish). IACR ePrint 2025/567.
- [PVM26] N. Polyanskii, I. Vorobyev, S. Mueller. *Bluestreak: Scaling DAG BFT by Sparsifying Metadata.* IACR ePrint 2026/898.
- [QXS25] L. Qiu, J. Xiao, J.-Y. Shin, Z. Shao. *LiDO-DAG: A Framework for Verifying Safety and Liveness of DAG-Based Consensus Protocols.* PACMPL 9(PLDI), Article 203, 2025. doi:10.1145/3729306.
- [QXS26] L. Qiu, J. Xiao, Z. Shao. *Mechanized Safety and Liveness Proofs for the Mysticeti Consensus Protocol under the LiDO-DAG Framework.* IEEE S&P 2026, 149–168.
- [SGSK22] A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias. *Bullshark: DAG BFT Protocols Made Practical.* CCS 2022.
- [SSKN25] N. Shrestha, R. Shrothrium, A. Kate, K. Nayak. *Sailfish: Towards Improving the Latency of DAG-based BFT.* IEEE S&P 2025. ePrint 2024/472.
- [Tsi+23] G. Tsimos, A. Kichidis, A. Sonnino, L. Kokoris-Kogias. *HammerHead: Leader Reputation for Dynamic Scheduling.* arXiv:2309.12713.
- [Van25] P. Vander Vos. *Odontoceti: Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis, arXiv:2510.01216.

---

## Appendix A. Statement index

Principal results only; supporting lemmas are omitted (Appendix D
indexes them).

A label — `L4`, `CQ6`, `O5` — is a cross-reference handle: the prose,
the consumption map of §4.8 and the support diagrams of §6.10 refer to
results through them. The series are alphabetic by area: T and M for
the safety core, L for liveness, V for the view-convergence family, CU
for catch-up, RS for the reactive schedule, SS for safe skip, AL for adaptive
leaders, H for the hybrid fault model, I for integration, MM for Mahi-Mahi, CQ for chain
quality, C, D,
B and E for the denial-of-service arc, G for garbage collection, O for
Odontoceti; P, N and R name clauses of the trust boundary rather than
results. Labels resolving to witness models rather than library
theorems (V10–V12, CU1, CU4, C5, CQ8, O11, SS7, SS11, AL8, H9, H10) are
excluded from the diagrams, which show the library; so is MM4. Appendix C displays every indexed
result in full.

### Safety

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| T0 | two quorums share a correct validator | `exists_correct_mem_inter` *(Validators)* |
| T0′ | two quorum-backed identifier sets share a correct author | `exists_correct_mem_creators_inter` *(Block)* |
| T1 | non-equivocation, in usable form | `BlockUniverse.eq_of_creator_eq` *(BlockDag)* |
| T6 | two quorum-backed sets of round-`n` blocks share a block | `BlockUniverse.exists_common_mem_of_quorums` *(BlockDag)* |
| T2 | causal history is non-increasing in round | `round_le_of_reaches` *(CausalHistory)* |
| T6a | causal history does not escape a view | `View.mem_of_reaches`, `View.exists_reaches_iff` *(CausalHistory)* |
| T3 | persistence | `reaches_of_quorum_support` *(Persistence)* |
| T3a | correct-support counting | `exists_correct_common_support` *(CommonCore)* |
| T3c | a common correct ancestor | `exists_common_correct_ancestor` *(CommonCore)* |
| M1 | no block is both committed and skipped | `not_directCommit_of_directSkip` *(Mysticeti)* |
| M2 | a committed block's certificate is unavoidable from `r+3` | `exists_certificate_reaches_of_directCommit` *(Mysticeti)* |
| M3 | a skipped block has no certificate anywhere | `certificates_eq_empty_of_directSkip` *(Mysticeti)* |
| M4 | the indirect rule agrees with the direct | `indirect_agrees_with_direct`, `certifiedIn_iff_of_view` *(Mysticeti)* |
| M5′ | certificate uniqueness | `eq_of_certificates_nonempty` *(Mysticeti)* |
| M5 | at most one block per slot is directly committed | `eq_of_directCommit_of_creator_eq` *(Mysticeti)* |
| M6 | agreement | `decided_unique`, `decided_agree` *(Mysticeti)* |
| M6′ | corollaries of agreement | `eq_of_decided_commit`, `not_decided_skip_of_decided_commit` *(Mysticeti)* |
| M7 | the committed-leader sequence is agreed | `commitSeq_agree` *(Mysticeti)* |
| M8 | the ledger is monotone and agreed | `ledgerSet_mono`, `ledgerSet_agree` *(Mysticeti)* |
| M9 | a block enters at one slot, agreed | `outputAt_unique`, `outputAt_agree` *(Mysticeti)* |

### Liveness

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| L0 | the DAG is dense below its frontier | `card_authorsAt_of_lt` *(Liveness)* |
| L2 | decisions are monotone in the view | `decided_mono` *(Liveness)* |
| L3 | decisions propagate to the full view | `decided_full` *(Liveness)* |
| L4 | a correct leader is committed | `directCommit_of_leader_mem`, `decided_of_leader_mem`; the targeted interface `VotesAt`, `CertifiesAt`, `directCommit_of_certifiesAt` *(Liveness)*, `directCommit_of_votesAt` *(Odontoceti/Liveness)* |
| L4′ | at `T := Correct` | `directCommit_of_correct_leader`, `decided_of_correct_leader` *(Liveness)* |
| L5 | an absent leader is skipped | `decided_none_of_leader_absent` *(Liveness)* |
| L6 | commits recur | `commits_recur_on`, `commits_recur` *(Liveness)* |
| L8c | a slot resolves through its first eligible commit | `decided_of_first_eligible_commit` *(Liveness)* |
| L8d | a committed slot above decides everything below (spaced schedules) | `decided_of_committed_above`, `all_decided_below_of_spacing` *(Liveness)* |
| L8e | a committed run of eligible span clears everything below | `decided_below_of_committed_run` *(Liveness)* |
| L10 | every slot below a fair run is decided (pipelined) | `all_decided_below_of_fairRun` *(Liveness)* |
| L12 | a schedule satisfying L10's fairness and shape hypotheses exists at every committee: the wave-aligned rotation, with no premise beyond the fault model | `waveRobin`, `waveRobin_fairRun`, `waveRobin_spansEligible`, `waveRobin_fairSchedule` *(WaveRobin)* |
| L7 | coverage from view convergence, drift-free | `ViewPace.synchronisedOn_of_converges`; the drift-parametric engine `ViewPace.synchronisedOn_of_driftOn` *(ViewPace)* |
| V1 | the referencing clause, unfused from the network's | `ViewPace.covers_of_converges` *(ViewPace)* |
| V4 | the bound factored out of convergence | `convergesWithin_iff_bounded` *(ViewPace)* |
| V10 | the bound in `converges` is necessary for coverage | `bound_is_necessary_pace`, `ugapPace_convergesEventually` *(LeanDagTest.Unbounded)* |
| V11 | and its starting round is forced, not chosen | `gst_is_forced_pace` *(LeanDagTest.Unbounded)* |
| V12 | as is its reliable set: coverage over `T` derived, over `Correct` false | `reliable_set_is_forced_pace`, `ustarvePace_synchronisedOn` *(LeanDagTest.Unbounded)* |
| V17 | a partial build schedule, in which *stuck* is expressible: the structure, production, and the spine | `ViewPace`, `ViewPace.reached`, `ViewPace.populatedOn`, `ViewPace.commits_recur_via_pace`, `ugrowStuckPace_stuck` *(ViewPace, LeanDagTest.ViewPace)* |
| L11 | drift is derived, at the collapsed constant | `ViewPace.driftOn_of_catchup`, `ReactivePace.driftOn_of_catchup` *(ViewPace, Reactive/Basic)* |
| L8a | the round of coverage, explicitly | `ViewPace.synchronisedOn_of_rate` *(ViewPace)* |
| L8b | the committing slot, and its round | `commits_recur_within`, `commits_recur_by_round` *(Quantitative)* |
| L9 | the wait bound | `ViewPace.directCommit_of_wait`, `ViewPace.decided_of_wait`, `ViewPace.directCommit_of_wait_two_delay` *(ViewPace)* |
| V18 | liveness is local: a validator decides on its own view | `PaceCore.viewAt`, `PaceCore.viewAt_ids`, `PaceCore.history_subset_holds`, `PaceCore.holds_roundBlocks`, `PaceCore.decided_local_of_certifiesAt`, `ViewPace.decided_local`, `ViewPace.decided_of_local`, `ReactiveM.decided_local` *(ViewPace, Reactive/Mysticeti)* |
| V19 | a pacing structure induces a delivery layer; the acceptance rule is derived | `ViewPace.heldOf_inj`, `ViewPace.toDelivery` *(PaceDelivery)* |
| V20 | the converse of P7 on the trunk; liveness with bounded storage from one structure | `PaceCore.refs_held`, `ViewPace.refsAccepted_toDelivery`, `ViewPace.dos_resistance_of_pace` *(ViewPace, PaceDelivery)* |

Gaps in the numbering (L1, L7a–L7c, V2, V3, V5–V9, V13–V16) are
deliberate: those labels belonged to superseded formulations and are not
reused.

### Chain quality (§7)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| CQ1 | a commit covers all but at most `f` correct authors, per round | `card_coveredAt_ge_of_decided` *(Quality/Coverage)* |
| CQ2 | at least half of the correct validators, per round | `card_correct_le_two_mul_coveredAt_of_decided` *(Quality/Coverage)* |
| CQ3 | ledger coverage, cumulative | `ledger_coverage` *(Quality/Coverage)* |
| CQ5 | post-`R`, every correct block is in every later correct-led commit | `mem_history_of_decided_commit` *(Quality/Inclusion)* |
| CQ6 | every correct block enters the agreed ledger | `committed_of_correct_block` *(Quality/Inclusion)* |
| CQ7 | within a schedule window; the capstone | `committed_of_correct_block_within`, `committed_of_correct_block_by_round`, `chain_quality` *(Quality/Capstone)* |
| CQ8 | the censorship boundary, on data | `Ucens` witnesses *(LeanDagTest/Quality/Model)* |

### Denial of service (§8)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| D11–D13 | exposure, and the DoS condition | `ExposedIn`, `DoSValid` *(DoS/Exposure)* |
| C2 | at most `f` authors exposed per cone | `card_exposedTo_le` *(DoS/Exposure)* |
| D14 | safety and the DoS condition do not interact | witness file *(LeanDagTest/DoS/SafetyUnderDoS)* |
| D15a | at zero margin, references are exactly the correct validators | `creators_refs_eq_correct` *(DoS/Exclusion)* |
| E1 | the correct backbone | `mem_history_of_correct` *(DoS/Exclusion)* |
| C1′ | the general per-cone bound | `card_history_le'` *(DoS/Pedigree)* |
| D25 | density: cones miss at most `f` per layer | `card_missingAt_le` *(DoS/Density)* |
| C5 | the doubling construction (`2^(e−2)`) | `Udouble` witnesses *(LeanDagTest/DoS/Doubling)* |
| C4 | the telescope | `card_history_le_of_stepNovelty` *(DoS/Novelty)* |
| C3′ | the view gap is a constant, not a drift | `card_viewGap_succ_le` *(DoS/Novelty)* |
| B6 | the budget sandwich | `UniformBudget.byzBudget`, `uniform_of_byzBudget` *(DoS/Novelty)* |
| B7 | a correct block carries its author's whole accepted past | `viewUpto_subset_history` *(DoS/Novelty)* |
| B4 | linear storage under the budget | `card_viewUpto_le` *(DoS/Novelty)* |
| B | the capstone, enforceable conditions only | `dos_resistance`, `dos_resistance'` *(DoS/Novelty)* |
| B5 | after exposure completes, the pool freezes | `card_viewUpto_le_of_allExposed'` *(DoS/Composition)* |

### Garbage collection (§9)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| G1 | truncation is a universe; the DoS condition crosses one way | `chop`, `dosValid_chop` *(GC/Chop)* |
| G2 | per-slot verdict invariance | `certificates_chop`, `directCommit_chop`, `certifiedIn_chop`, … *(GC/Chop)* |
| G3 | the decision relation survives the cut | `decided_chop` *(GC/ChopDecided)* |
| G4 | cross-cut agreement, arbitrary joiner views | `decided_agree_chop` *(GC/ChopDecided)* |
| G5 | liveness transfers | `populated_chop` *(GC/Window)* |
| G13, G14 | windowed novelty; store correspondence | `novelty_chop_anti`, `viewUpto_chopD` *(GC/Window)* |
| G6 | storage constant at lag `Λ` | `card_retained_le` *(GC/Window)* |
| G6b, G7 | join and relay at the same constant | `card_joinIds_le`, `card_serve_le` *(GC/Bootstrap)* |
| G10 | the attested-base sandwich | `correct_mem_base`, `exists_correct_attester_of_mem_base` *(GC/AttestedBase)* |
| G11 | window completeness, tight at lag two | `accepted_mem_base` *(GC/Bootstrap)* |
| G12 | bootstrap safety | `joinView`, `bootstrap_agree` *(GC/Bootstrap)* |
| G8 | horizons compose; heterogeneous horizons agree | `chop_chop`, `decided_agree_horizons` *(GC/Horizon)* |
| G9 | possession universalises in one round | `viewUpto_subset_viewUpto_succ`, `pruned_subset_peer_store` *(GC/Horizon)* |

### Odontoceti (§10)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| O1 | commit versus skip | `not_directSkip_of_directCommit` *(Odontoceti/Rules)* |
| O1′ | twin uniqueness for direct commits | `eq_of_directCommit` *(Odontoceti/Rules)* |
| O2 | a skipped leader fails the indirect test everywhere | `card_supporters_le_of_directSkip`, `not_thickLink_of_directSkip` *(Odontoceti/Rules)* |
| O3 | support propagation: every anchor's cone is the certificate | `thickLink_of_directCommit` *(Odontoceti/Rules)* |
| O4′ | a direct commit excludes every rival candidate | `eq_of_directCommit_of_thickLink` *(Odontoceti/Rules)* |
| O5 | agreement, under canonicity | `Odontoceti.decided_unique` *(Odontoceti/Decision)* |
| O6 | safety | `Odontoceti.safety` *(Odontoceti/Decision)* |
| O7 | a correct leader commits in one step | `Odontoceti.decided_of_leader_mem` *(Odontoceti/Liveness)* |
| O8 | a run of two spans eligibility | `Odontoceti.spansEligible_two` *(Odontoceti/Liveness)* |
| O9 | a committed run clears everything below | `Odontoceti.decided_below_of_committed_run` *(Odontoceti/Liveness)* |
| O10 | liveness | `Odontoceti.all_decided_below_of_fairRun` *(Odontoceti/Liveness)* |
| O11 | the thesis gap, on data | `utwin6_both_pass` *(LeanDagTest/Odontoceti/Model)* |

**The reactive schedule** (§11):

| Label | Statement | Lean |
|:---|:---|:---|
| RS1 | every reliable vote block votes | `ReactivePace.votes` *(Reactive/Basic)* |
| RS2 | reactive liveness, three rounds | `ReactiveM.certifies`, `ReactiveM.directCommit`, `ReactiveM.decided` *(Reactive/Mysticeti)* |
| RS3 | reactive liveness, two rounds | `Odontoceti.reactive_directCommit`, `Odontoceti.reactive_decided` *(Reactive/Odontoceti)* |
| RS4 | latency tracks delivery; the timeout never fires | `ReactivePace.built_succ_le_of_fast`, `ReactivePace.no_timeout_of_fast` *(Reactive/Basic)* |
| RS5 | inclusion without coverage: the rotation backbone | `reaches_self_ancestor` *(CausalHistory)*, `FairToEach` *(Liveness)*, `ReactiveM.committed_of_correct_block` *(Reactive/Mysticeti)* |

**Catch-up** (§6.11):

| Label | Statement | Lean |
|:---|:---|:---|
| CU1 | drift does not contract past the collapse bound | `ugrowSkew_spread_constant` *(LeanDagTest.Catchup)* |
| CU2 | drift collapses to `Δ + proc`, from any spread | `PaceCore.drift_collapse` *(ViewPace)* |
| CU3 | the deployment-free threshold `2Δ + proc` | merged into the main line: L7 (coverage) and L9 (the wait bound) |
| CU4 | the collapse exhibited from a spread of ten | `ugrowLag_collapse`, `ugrowLag_decided` *(LeanDagTest.Collapse)* |
| CU5 | the rush bound: a valid block certifies the honest floor | `exists_reliable_parent`, `PaceCore.round_le_top_succ`, `ViewPace.exists_honest_floor` *(ViewPace)* |

**Safe Skip** (§12):

| Label | Statement | Lean |
|:---|:---|:---|
| SS1 | the fill is a universe; old blocks read unchanged | `SkipMsg.skipFill`, `SkipMsg.skipFill_block_old` *(SafeSkip/Basic)* |
| SS2 | the gap is populated: production restored | `SkipMsg.skipFill_populatedOn` *(SafeSkip/Basic)* |
| SS3 | the fill cannot conjure a commit | `SkipMsg.directSkip_fresh` *(SafeSkip/Basic)* |
| SS4 | the rule-level sets are unchanged, for every candidate | `SkipMsg.certificatesIn_fill`, `SkipMsg.blameSetIn_fill` *(SafeSkip/Invariance)* |
| SS5 | verdict invariance across the fill | `SkipMsg.decided_fill` *(SafeSkip/Invariance)* |
| SS6 | agreement across a recovery | `SkipMsg.decided_fill_agree` *(SafeSkip/Invariance)* |
| SS7 | the crash, the message and the fill, on data | `Ucrash` witnesses *(LeanDagTest/SafeSkip)* |
| SS8 | the donor line is unique given its tip | `SkipMsg.line_eq_lineOf` *(SafeSkip/Jump)* |
| SS9 | the denotation is a function of the compact core | `SkipMsg.skipFill_eq_of_core` *(SafeSkip/Jump)* |
| SS10 | receivers derive the same fill, locally | `lineOf_mem_view`, `JumpMsg.denote_eq_of_core` *(SafeSkip/Jump)* |
| SS11 | the jump message and its elaboration, on data | `ucrashJump` witnesses *(LeanDagTest/SafeSkip)* |

**Adaptive leaders** (§13):

| Label | Statement | Lean |
|:---|:---|:---|
| AL1 | the induced instance; the base schedule is its own | `slotsOf`, `slotsOf_base` *(Adaptive/Basic)* |
| AL2 | the bounded relation; the embedding and the congruence | `DecidedWithin`, `DecidedWithin.toDecided`, `decidedWithin_congr` *(Adaptive/Basic)* |
| AL3 | safety: the fixpoint is unique, unconditionally | `partialRun_agree`, `adaptiveRun_agree` *(Adaptive/Run)* |
| AL4 | conservativity at the constant policy | `AdaptivePolicy.const_run_decided` *(Adaptive/Run)* |
| AL5 | liveness: the fixpoint exists, one epoch at a time | `epoch_closes`, `exists_partialRun`, `adaptiveRun_exists` *(Adaptive/Liveness)* |
| AL6 | the adaptive ledger is agreed | `adaptive_commitSeq_agree` *(Adaptive/Run)* |
| AL7 | the two-round mirror, from the same policy objects | `Odontoceti.adaptiveRun_agree`, `Odontoceti.adaptiveRun_exists` *(Adaptive/Odontoceti)* |
| AL8 | adaptivity on data: the verdict moves with the assignment | `demotePolicy` witnesses *(LeanDagTest/Adaptive)* |

**Hybrid fault tolerance** (§14):

| Label | Statement | Lean |
|:---|:---|:---|
| H1 | the counting core: overlap past `n + fb` yields an honest member | `exists_honest_mem_inter` *(Hybrid/Faults)* |
| H2 | commit versus skip; twin uniqueness | `Hybrid.not_directSkip_of_directCommit`, `Hybrid.eq_of_directCommit` *(Hybrid/Rules)* |
| H3 | a skipped leader caps at `2·fb + fc` supporters, below the interval | `Hybrid.card_supporters_le_of_directSkip`, `Hybrid.not_thickLink_of_directSkip` *(Hybrid/Rules)* |
| H4 | link integrity: every anchor carries the interval's upper end | `Hybrid.thickLink_of_directCommit` *(Hybrid/Rules)* |
| H5 | a direct commit excludes every rival candidate | `Hybrid.eq_of_directCommit_of_thickLink` *(Hybrid/Rules)* |
| H6 | agreement and safety, at every admissible threshold | `Hybrid.decided_unique`, `Hybrid.safety` *(Hybrid/Decision)* |
| H7 | liveness over the reliable-correct interface | `Hybrid.decided_of_leader_mem`, `Hybrid.all_decided_below_of_fairRun` *(Hybrid/Liveness)* |
| H8 | conservativity: the crash-free hybrid is Odontoceti | `Faults5.toHybrid`, `Hybrid.toHybrid_toFaults` *(Hybrid/Conservativity)* |
| H9 | one crash at four validators; the tight hybrid committee | `Uhyb4`, `Uhyb9` witnesses *(LeanDagTest/Hybrid)* |
| H10 | the bound is necessary, at every threshold | `hybrid_bound_necessary` *(LeanDagTest/HybridTight)* |
| NN1 | the counting core: two majorities intersect | `Nemo.exists_mem_inter` *(Nemo/Basic)* |
| NN2 | the hitting lemma: a majority of backers meets every valid block's parents | `Nemo.exists_mem_refs_of_correct_support_of_card` *(Nemo/Support)* |
| NN3 | link integrity: a direct commit is certified two rounds up, everywhere | `Nemo.certifiedIn_of_directCommit` *(Nemo/Rules)* |
| NN4 | a slot has at most one candidate | `Nemo.isLeaderBlock_unique` *(Nemo/Decision)* |
| NN5 | agreement, with no side conditions | `Nemo.decided_unique`, `Nemo.decided_agree` *(Nemo/Decision)* |
| NN6 | the ledger is agreed and never retracted | `Nemo.commitSeq_agree`, `Nemo.outputAt_agree` *(Nemo/Decision)* |
| NN7 | a reliable-led slot commits directly | `Nemo.decided_of_leader_mem` *(Nemo/Liveness)* |
| NN8 | every slot below a recurring adjacent pair is decided | `Nemo.all_decided_below_of_fairRun` *(Nemo/Liveness)* |
| NN9 | one crash at three validators; the crashed slot settled indirectly | `Unemo` witnesses *(LeanDagTest/Nemo)* |

**Mahi-Mahi** (§17):

| Label | Statement | Lean |
|:---|:---|:---|
| MM1 | safety at wave `w`: skip excludes certificates, certificate uniqueness, agreement, conservativity at `w = 3` | `MahiMahi.Safety.holds` *(MahiMahi/Safety/Proof)* |
| MM1a | a skipped slot has no certificate for any candidate | `MahiMahi.certificates_eq_empty_of_directSkip` *(MahiMahi/Helpers/Rules)* |
| MM1b | two certified candidates of one author and round coincide | `MahiMahi.eq_of_certificates_nonempty` *(MahiMahi/Helpers/Rules)* |
| MM1c | two views agree on every slot | `MahiMahi.decided_unique` *(MahiMahi/Helpers/Decision)* |
| MM1d | at `w = 3` every derivation is the core's | `MahiMahi.core_decided_of_decided` *(MahiMahi/Helpers/Decision)* |
| MM2 | the counting lemma: the common core; some correct block commits at `w ≥ 4`; `n − f − |byzantine|` of them at `w ≥ 5` | `MahiMahi.Counting.holds`, `MahiMahi.exists_commonCore`, `MahiMahi.goodNonempty`, `MahiMahi.goodCard` *(MahiMahi/Helpers/Counting)* |
| MM2b | `2f + 1` distinct leaders at a round include a good one | `MahiMahi.multiLeader` *(MahiMahi/Helpers/Counting)* |
| MM2′ | `good` depends only on the rounds up to the decision round | `MahiMahi.AgreeUpto.goodAt_eq` *(MahiMahi/Helpers/Liveness)* |
| MM3 | liveness under the clause: a good leader commits; commits within every window; every slot below a run decided; local liveness | `MahiMahi.Liveness.holds`, `MahiMahi.decided_of_mem_good`, `MahiMahi.allDecidedBelow`, `MahiMahi.localCommit` *(MahiMahi/Helpers/Liveness)* |
| MM4 | the clause is satisfiable, refuted by round-robin on the aiming pattern, and independent of fairness | `aim4`, `full4` witnesses *(LeanDagTest/MahiMahi)* |
| MM5 | under coverage at one round a reliable leader is good; the clause is derived from fairness | `MahiMahi.Synchrony.holds`, `MahiMahi.good_of_synchronisedOn`, `MahiMahi.unpredictableWithin_of_synchronisedOn` *(MahiMahi/Helpers/Synchrony)* |

**Integration** (§16):

| Label | Statement | Lean |
|:---|:---|:---|
| I1 | honest non-equivocation survives truncation and the fill | `honestNoEquiv_chop`, `honestNoEquiv_skipFill` *(Integration/Preservation)* |
| I2 | coverage survives truncation, at a horizon offset | `synchronisedOn_chop` *(Integration/Preservation)* |
| I3 | fairness and shape survive truncation | `fairScheduleOn_chop`, `fairRunOn_chop`, `spansEligible_chop` *(Integration/ScheduleShape)* |
| I4 | coverage under the fill: refuted for a set including the recovering validator, preserved otherwise, restored above the fill | `not_synchronisedOn_skipFill`, `synchronisedOn_skipFill_of_notMem`, `synchronisedOn_skipFill_above` *(Integration/Coverage)* |
| I5 | the joiner: horizon-stability, and epoch alignment | `HorizonStable`, `joiner_assign_agree`, `epochOf_add_of_dvd` *(Integration/Joiner)* |
| I6 | anchor retention, and the lag bounds the outage | `anchor_pruned`, `chopMsg`, `outage_bounded_by_lag` *(Integration/Retention)* |
| I7 | the composition capstone | `honestNoEquiv_stack`, `hybrid_agree_stack` *(Integration/Stack)* |
| I8 | a severed chain cannot restart | `no_blocks_of_no_genesis`, `severed_of_pruned_anchor` *(Integration/Retention)* |
| I9 | the crash-prone lifecycle, and the hypothesis it forced | `hB1uniq_of_crash`, `lifecycle` *(Integration/Lifecycle)* |
| I10 | re-genesis at the cut | `addGenesis`, `populatedOn_addGenesis` *(Integration/ReGenesis)* |
| I11 | local derivation converges; no agreement on the cut | `chop_addGenesis`, `regenesis_converges` *(Integration/ReGenesis)* |
| I12 | bootstrap, re-genesis and Safe Skip compose into full recovery | `hB1uniq_of_addGenesis`, `recoveryMsg` *(Integration/ReGenesis)* |
| I13 | the exposure condition survives re-genesis; the fill enlarges cones | `dosValid_addGenesis` *(Integration/ReGenesis)*; `history_B1_subset_fill` *(Integration/Exposure)* |
| I14 | the fill disturbs exposure only at its own blocks | `exposedIn_skipFill_old`, `dosValid_skipFill` *(Integration/Exposure)* |
| I15 | a covered donor line reduces the check to reachability | `fill_cone_subset`, `dosValid_skipFill_of_covered` *(Integration/Exposure)* |
| I16 | the fill's delivery layer; the budget transfers, the reference discipline does not | `skipFillD`, `uniformBudget_skipFillD`, `not_refsAccepted_skipFillD` *(Integration/DeliveryFill)* |
| I17 | the budget needs a donor, not the author | `card_novelty_le_of_donor` *(Integration/Margin)* |
| I18 | severance costs liveness margin: at most `f` at once | `notMem_of_no_blocks`, `card_severed_le` *(Integration/Margin)* |
| I19 | a common-core target makes the fill transmission-free | `CommonAt`, `exists_commonAt`, `fill_refs_available` *(Integration/CommonTarget)* |

---

<!-- BEGIN GENERATED REFERENCE -->

## Appendix B. The definition reference

Every definition and structure of the development, in the order
a reader meets them. Each entry is the source text, unabridged,
with the explanation the source carries. This appendix is
generated from the compiled development by
`scripts/gen-reference.py`; the statements are therefore the
declarations themselves rather than transcriptions of them.

Nine entries carry proofs, which can look like a
misclassification. They are not. A structure in Lean may have
fields that are propositions — `BlockUniverse` requires causal
closure, validity and non-equivocation — so *constructing* one
means discharging those obligations, and the proof is part of
the definition rather than a theorem about it. `chop`, `chopD`
and `toDelivery` are of this kind: each builds an object whose
type demands the proofs shown. A theorem, by contrast, asserts
a proposition about objects already built, and those are
Appendix C.

### The validator set and the fault model

#### `Faults`

*class, `Validators.lean`*

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The Byzantine validators. Everything else is correct. -/
  byzantine : Finset Validator
  /-- There are at least `3f+1` validators. -/
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  /-- At most `f` validators are Byzantine. -/
  card_byzantine : byzantine.card ≤ f
```

The fault model: `n ≥ 3f+1` validators, at most `f` of them Byzantine.

#### `Correct`

*def, `Validators.lean`*

```lean
def Correct : Finset Validator := (F.byzantine)ᶜ
```

The correct (non-Byzantine) validators.

### Blocks, validity, and the universe

#### `Block`

*structure, `Block.lean`*

```lean
structure Block (Validator BlockId Payload : Type*) where
  /-- The round this block was produced in. -/
  round : ℕ
  /-- The validator that authored the block. -/
  creator : Validator
  /-- Ids of the blocks this one references, all from round `round - 1`. -/
  refs : Finset BlockId
  /-- Opaque application data. Inert throughout Phase 1. -/
  payload : Payload
```

A block: its round, its author, the ids it references from the preceding round, and an opaque payload.

#### `creatorsOf`

*def, `Block.lean`*

```lean
def creatorsOf (blk : BlockId → Block Validator BlockId Payload)
    (s : Finset BlockId) : Finset Validator :=
  s.image (fun i => (blk i).creator)
```

The validators that authored a set of ids. Defined on an arbitrary `Finset BlockId`, not just on a block's refs: T3's hypothesis, T4's commit rule, and T0' all quantify over id-sets that are nobody's refs.

#### `creators`

*def, `Block.lean`*

```lean
def creators (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Finset Validator :=
  creatorsOf blk b.refs
```

The validators behind a block's references.

#### `ValidWrt`

*structure, `Block.lean`*

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- A block never cites the same author twice. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- Non-genesis blocks reference a quorum of distinct validators. -/
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card
  /-- Non-genesis blocks reference a block by their own creator — *some* such
  block, not a unique one: an equivocator's blocks form a forest of
  predecessor chains, one edge per block, and the condition does not (and
  need not) collapse the forest. Combined with `predecessor` the parent sits
  at the round immediately below, and with `distinct_creators` it is the
  *only* reference sharing the block's author. -/
  self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator
```

Block validity, relative to a lookup function.

The predecessor condition is stated additively rather than as `(blk i).round = b.round - 1`. That avoids `ℕ`-subtraction, and it makes the genesis case *derivable* rather than a separate branch: at round `0` the equation `(blk i).round + 1 = 0` is unsatisfiable, so `refs = ∅` follows (`refs_empty_of_round_zero`). Only the quorum condition needs a round guard.

The quorum is stated on the *creator set*, not on `refs.card`. That is the form every downstream proof wants, and it is the faithful reading of "2f+1 blocks from the previous round" — the protocol means 2f+1 *validators*.

#### `BlockUniverse`

*structure, `BlockDag.lean`*

```lean
structure BlockUniverse (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] [Faults Validator] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. Total, with junk outside `ids`; every statement
  below quantifies over `i ∈ ids`, so the junk is never observed. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is itself present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid. -/
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  /-- Correct validators do not equivocate: at most one block per correct
  author per round. Byzantine validators are unconstrained. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ (Correct : Finset Validator) →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j
```

Every block that exists, together with the well-formedness conditions the protocol guarantees.

#### `View`

*structure, `BlockDag.lean`*

```lean
structure View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator]
    (U : BlockUniverse Validator BlockId Payload) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed downward: it holds everything its blocks reference. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

A **view**: one validator's local DAG. A subset of the universe that is itself closed under references.

Views share `U.block`, so they disagree about *which* blocks they hold, never about what an id denotes, and they inherit validity and non-equivocation from `U` unchanged. Different correct validators may hold different views — that asymmetry is the entire point of the cross-view results.

### Causal structure

#### `CausalStructure`

*structure, `Causality.lean`*

```lean
structure CausalStructure (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) : Prop where
  /-- Every referenced block is itself present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids
  /-- A reference sits in the round immediately below its referrer. -/
  refs_round : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, (blk j).round + 1 = (blk i).round
```

**The structural core of a block DAG.** A population closed under references, whose references sit one round below. This is everything the causal-history layer consumes of a universe — no validity beyond the predecessor condition, no quorum, no fault model.

#### `RefStepFrom`

*def, `Causality.lean`*

```lean
def RefStepFrom (blk : BlockId → Block Validator BlockId Payload) (i j : BlockId) : Prop :=
  j ∈ (blk i).refs
```

One step of causal history: `j` is directly referenced by `i`.

#### `ReachesFrom`

*def, `Causality.lean`*

```lean
def ReachesFrom (blk : BlockId → Block Validator BlockId Payload) :
    BlockId → BlockId → Prop :=
  Relation.ReflTransGen (RefStepFrom blk)
```

`ReachesFrom blk c b` — `b` lies in the causal history of `c`.

#### `historyUptoFrom`

*def, `Causality.lean`*

```lean
def historyUptoFrom (blk : BlockId → Block Validator BlockId Payload) :
    ℕ → BlockId → Finset BlockId
  | 0, b => {b}
  | n + 1, b => insert b ((blk b).refs.biUnion (historyUptoFrom blk n))
```

Everything reachable from `b` in at most `n` reference steps.

#### `historyFrom`

*def, `Causality.lean`*

```lean
def historyFrom (blk : BlockId → Block Validator BlockId Payload) (b : BlockId) :
    Finset BlockId :=
  historyUptoFrom blk ((blk b).round + 1) b
```

The causal history of `b`, as a `Finset`.

#### `Reaches`

*def, `CausalHistory.lean`*

```lean
def Reaches (U : BlockUniverse Validator BlockId Payload) : BlockId → BlockId → Prop :=
  ReachesFrom U.block
```

`Reaches U c b` — `b` lies in the causal history of `c`.

#### `historyUpto`

*def, `History.lean`*

```lean
def historyUpto (U : BlockUniverse Validator BlockId Payload) :
    ℕ → BlockId → Finset BlockId :=
  historyUptoFrom U.block
```

Everything reachable from `b` in at most `n` reference steps.

Structural in the fuel `n`, so it is computable and needs no decidability hypothesis. Outside `U.ids` it still evaluates — to junk, like `U.block` itself — and every statement below quantifies over ids of the universe.

#### `history`

*def, `History.lean`*

```lean
def history (U : BlockUniverse Validator BlockId Payload) (b : BlockId) : Finset BlockId :=
  historyFrom U.block b
```

The causal history of `b`, as a `Finset`.

#### `blocksAt`

*def, `Support.lean`*

```lean
def blocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)
```

The ids present at a given round.

#### `authorsIn`

*def, `Support.lean`*

```lean
def authorsIn (U : BlockUniverse Validator BlockId Payload)
    (s : Finset BlockId) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (s.filter fun b => (U.block b).round = n)
```

The distinct authors of the round-`n` blocks in a set of ids — an image, so an equivocator's duplicates collapse: this counts validators, not blocks, which is what makes a quorum of it a real quorum. Over `U.ids` it is `authorsAt`; over a validator's holdings it is the trigger of the pacemaker's progress rule (`PaceCore.advances`).

#### `authorsAt`

*def, `Support.lean`*

```lean
def authorsAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)
```

The validators holding a block at a given round — the pool `p`.

#### `supporters`

*def, `Support.lean`*

```lean
def supporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => b ∈ (U.block q).refs))
```

The validators whose round-`n` block references `b`.

#### `correctSupporters`

*def, `Support.lean`*

```lean
def correctSupporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  supporters U b n ∩ (Correct : Finset Validator)
```

Validators that are both correct and back `b` with their round-`n` block. This is exactly what the coverage lemmas consume.

#### `blames`

*def, `Support.lean`*

```lean
def blames (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => L ∉ (U.block q).refs))
```

The validators whose round-`n` block declines to reference `L`.

The complement of `supporters U L n` *within the round-`n` author pool* — but only for correct validators. A Byzantine author can appear in both, by publishing one round-`n` block that votes and another that does not; ruling that out for correct validators is exactly what `blames_inter_supporters_subset_byzantine` does, and is the whole content of M3.

#### `correctBlocksAt`

*def, `CommonCore.lean`*

```lean
def correctBlocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  (blocksAt U n).filter (fun q => (U.block q).creator ∈ (Correct : Finset Validator))
```

The round-`n` blocks authored by *correct* validators. The counting argument ranges over these: a correct author has exactly one block per round (T1), so `creator` is injective here and blocks and authors can be counted interchangeably.

### Slots and the schedule

#### `uniform`

*def, `Schedule.lean`*

```lean
def uniform (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (elect : ℕ → Validator)
    (hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂) :
    Slots Validator where
  slotRound k := p * (k / m)
  leader k := elect k
  mono := fun _ _ hab => Nat.mul_le_mul_left p (Nat.div_le_div_right hab)
  unbounded := fun n => ⟨m * n, by
    rw [Nat.mul_div_cancel_left n hm]
    exact Nat.le_mul_of_pos_left n hp⟩
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    exact hblock k₁ k₂ (Nat.eq_of_mul_eq_mul_left hp h.1) h.2
```

**The uniform schedule**: `m` leaders in every `p`-th round, slot `k` proposed by `elect k`.

`hblock` is the one real condition — the `m` proposers sharing a round are distinct validators. Round-robin `elect k = k % n` satisfies it whenever `m ≤ n`. Without it a single block would be the candidate for two slots and the ledger would deliver it twice.

#### `uniformSingle`

*def, `Schedule.lean`*

```lean
def uniformSingle (p : ℕ) (hp : 0 < p) (elect : ℕ → Validator) : Slots Validator :=
  uniform p 1 hp Nat.one_pos elect (one_hblock elect)
```

**One leader every `p` rounds.** `p = 3` is the schedule the development had before pipelining; `p = 1` is pipelined single-leader.

### The commit rule, and the ledger

#### `votesIn`

*def, `Mysticeti.lean`*

```lean
def votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => L ∈ (U.block q).refs)
```

The references of `C` that vote for `L`.

#### `Certifies`

*def, `Mysticeti.lean`*

```lean
def Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (votesIn U C L)).card
```

A round-`(r+2)` block certifies `L` when its votes for `L` come from a quorum of distinct validators.

#### `certificates`

*def, `Mysticeti.lean`*

```lean
def certificates (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)
```

The certificates for a round-`r` block `L`: the round-`(r+2)` blocks that certify it.

#### `DirectCommit`

*def, `Mysticeti.lean`*

```lean
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card
```

`L` is directly committed when its certificates come from a quorum of distinct validators.

#### `DirectSkip`

*def, `Mysticeti.lean`*

```lean
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card
```

`L` is directly skipped when a quorum of distinct validators declined to vote for it.

#### `CertifiedIn`

*def, `Mysticeti.lean`*

```lean
def CertifiedIn (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C
```

The indirect rule's test: does a certificate for `L` lie in the causal history of the anchor block `A`?

#### `Slots`

*class, `Mysticeti.lean`*

```lean
class Slots (Validator : Type*) where
  /-- The round at which slot `k` is proposed. -/
  slotRound : ℕ → ℕ
  /-- The validator whose block is the slot-`k` candidate. -/
  leader : ℕ → Validator
  /-- Slots are enumerated in round order. -/
  mono : Monotone slotRound
  /-- Slot rounds are unbounded. -/
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  /-- Distinct slots differ in round or in leader. -/
  keyed : Function.Injective (fun k => (slotRound k, leader k))
```

The leader schedule: which validator proposes at which round, as a sequence of slots.

Slots need **not** be three rounds apart. Under pipelining consecutive slots are one round apart, and under multiple leaders per round they share a round, so all that is required of `slotRound` is that it be monotone. The three-round separation M4's commit half needs is no longer a property of *consecutive* slots and is therefore not derivable here; it is required instead of the particular pairs that use it, by `Eligible` below.

`unbounded` was a theorem under three-round spacing (`3 * k ≤ slotRound k`) and is underivable from `mono` alone — a schedule parking every slot at one round is monotone. Liveness needs it, so it is assumed.

`keyed` says distinct slots differ in round or in leader. It too held under three-round spacing, which makes `slotRound` injective outright. Under multiple leaders it is a real condition on the schedule: the proposers of a round must be distinct validators. Without it one block would be the candidate for two slots, and the ledger would deliver it twice.

#### `decisionRound`

*def, `Mysticeti.lean`*

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2
```

The round at which slot `k`'s direct rules are settled: its certificates live here. Algorithm 2's `DecisionRound`.

`Validator` is explicit because the result is a bare `ℕ`, so nothing else would fix it — the same reason the three-round spacing lemma is written `S.slotRound`.

#### `Eligible`

*def, `Mysticeti.lean`*

```lean
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j
```

**`j` may anchor `k`.** Its proposal lies past `k`'s decision round, so a block at `j`'s round can reach a certificate for `k`'s — which is exactly M4's `r + 3` hypothesis. Algorithm 3's anchor filter `r_decision < s.round`.

Stated through `decisionRound` rather than as a bare `+ 3` so that a later wavelength parameter is a change to one definition.

It is a predicate on the **pair of slots alone** — not on any view. That is what makes agreement go through: two validators deciding the same slot `k` agree on which slots may anchor it, so each one's eligibility premise is the side condition the other's intermediate-skip premise requires.

#### `IsLeaderBlock`

*def, `Mysticeti.lean`*

```lean
def IsLeaderBlock (U : BlockUniverse Validator BlockId Payload) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

`L` is a candidate block for slot `k`: the right round, the right author.

A *correct* leader has at most one such block (T1); a Byzantine one may have several, which is why the definitions below quantify over candidates rather than selecting one. M5 supplies uniqueness where it is needed.

#### `certificatesIn`

*def, `Mysticeti.lean`*

```lean
def certificatesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  certificates U L r ∩ V.ids
```

The certificates for `L` that a view actually holds.

#### `DirectCommitIn`

*def, `Mysticeti.lean`*

```lean
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificatesIn U V L r)).card
```

Direct commit, as judged from a single view.

#### `DirectSkipIn`

*def, `Mysticeti.lean`*

```lean
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤
    (creatorsOf U.block
      (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)).card
```

Direct skip, as judged from a single view.

#### `Decided`

*inductive, `Mysticeti.lean`*

```lean
inductive Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule blames every candidate — including vacuously, when the
  leader produced no block at all. -/
  | directSkip {k : ℕ} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  /-- Anchored on the nearest eligible committed slot, a certificate is in
  reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate is in
  reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

**The decision relation.** `Decided U V k v` — a validator holding the view `V` has settled slot `k`, committing the block `v = some L` or skipping it, `v = none`.

Four rules, in two pairs. The *direct* pair reads the slot's own certificates: a candidate carrying `n−f` of them is committed, and a slot whose every candidate is blamed by `n−f` is skipped. The *indirect* pair applies when the direct evidence is inconclusive, and decides `k` by looking up to an **anchor** — the nearest eligible slot above `k` that is itself committed — and asking whether a certificate for a candidate of `k` is reachable from the anchor's block.

"Nearest" is stated positively: every eligible slot strictly between `k` and the anchor is decided `none`. The negative reading — *no eligible slot between is committed* — would be a negative premise, which an inductive definition cannot carry; the positive form is equivalent, since the sweep decides every slot it passes, and it keeps every recursive occurrence strictly positive. The occurrence sits behind `Eligible`, which is a predicate on two naturals and does not mention `Decided`.

The relation is indexed by a view, so two validators may reach different verdicts by the letter of the definition; M6 (`decided_unique`) is the theorem that they cannot.

#### `commitSeq`

*def, `Mysticeti.lean`*

```lean
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g
```

The blocks committed at slots `0, …, n-1`, in slot order, with skipped slots dropped. `g` is a validator's verdict assignment.

#### `ledgerSet`

*def, `Mysticeti.lean`*

```lean
def ledgerSet (U : BlockUniverse Validator BlockId Payload)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}
```

The blocks output after settling slots `0, …, n-1`: everything in the causal history of a committed leader.

#### `OutputAt`

*def, `Mysticeti.lean`*

```lean
def OutputAt (U : BlockUniverse Validator BlockId Payload)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b
```

`b` enters the ledger at slot `k`: the first committed slot whose leader reaches it.

### Delivery, growth, and coverage

#### `PopulatedFrom`

*def, `Participation.lean`*

```lean
def PopulatedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ ids, (blk b).creator = v ∧ (blk b).round = r
```

Every validator in `T` authors a block at round `r` among `ids`.

#### `SynchronisedFrom`

*def, `Participation.lean`*

```lean
def SynchronisedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ ids, (blk b).round = n + 1 → (blk b).creator ∈ T →
    ∀ a ∈ ids, (blk a).round = n → (blk a).creator ∈ T → a ∈ (blk b).refs
```

From round `R` on, every `T`-authored block references every `T`-authored block of the round below. Both quantifiers restricted to `T`, deliberately.

#### `PopulatedOn`

*def, `Liveness.lean`*

```lean
def PopulatedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  PopulatedFrom U.block U.ids T r
```

What L4 actually needs of a round: every validator in `T` has a block there.

Local and finite — no growth, no horizon. Splitting this out is what keeps the horizon `N` out of L4 entirely, so the only hard proof in the plan is independent of how production is framed.

**Why a set `T` rather than all of `Correct`.** L4 counts to `2f+1` and never higher, so it needs a *quorum* of reliable validators, not every one of them. Demanding all of `Correct` makes the theorem lapse when a single correct validator misses a single round — a GC pause, a restart — although the protocol still commits. See `liveness.md` §8 Q2.

#### `Populated`

*abbrev, `Liveness.lean`*

```lean
abbrev Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Validator) r
```

The all-of-`Correct` case, which is what L1 produces.

#### `Delivery`

*structure, `Liveness.lean`*

```lean
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  /-- Held ids are real blocks of the stated round — what keeps `Delivery`
  meaningful, since without it `held` could be junk and `includes` would
  demand blocks reference it. -/
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- What `v` chose to build on: a subset of what it held. -/
  accepted : Validator → ℕ → Finset BlockId
  /-- You can only accept what arrived. -/
  accepted_sub : ∀ v n, accepted v n ⊆ held v n
  /-- **The acceptance rule**: at most one block per author. Forced by
  `distinct_creators` — a validator holding two blocks by one author must pick
  one, because it cannot reference both. -/
  accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
    (U.block i).creator = (U.block j).creator → i = j
  /-- A correct block is always accepted. It never conflicts with anything —
  its author has only the one block for that round (T1) — so nothing is ever
  given up by taking it, and L7 needs it. -/
  accepts_correct : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ accepted v n
  /-- **The protocol rule.** A correct validator references everything it
  accepted. Implementable and observable — unlike `Synchronised` itself. -/
  includes : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs
```

What each validator had in hand, one round at a time — and which of it it chose to build on.

**Two fields, because delivery and policy are two things.** `held` is what the network brought; `accepted` is what the validator will reference. Until equivocation nothing forces them apart, and a structure carrying only `held`, with `includes` demanding that a correct validator reference *everything* it held, would be **unsatisfiable** the moment a correct validator holds both halves of an equivocation: `distinct_creators` forbids referencing two blocks by one author, so no valid block exists and the validator cannot build at all. See `dos-equivocation-and-growth.md` §4.

`held` must *not* be deduplicated: `U` is defined as every block some correct validator held (`liveness.md` §4.2), so pruning at the delivery layer would put the second half of an equivocation outside the universe altogether. The choice of which half to accept is left unspecified, exactly as the timeout is — the model says what was in hand and what was built on, never how either was decided.

#### `SynchronisedOn`

*def, `Liveness.lean`*

```lean
def SynchronisedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  SynchronisedFrom U.block U.ids T R
```

From round `R` on, a correct block references every correct block of the round below.

`R` is **not** GST: it is the round from which synchrony has fully taken effect — GST plus however long catch-up ran (`liveness.md` §4.2). It is a round index, not a clock; there is no Δ here.

**Both quantifiers are restricted to `Correct`, and deliberately.** A Byzantine validator may publish nothing at all, or publish and reveal to only some validators, so no assumption about referencing its blocks would be sound — and none is needed: L4 counts only correct certificates, and there are `2f+1` correct validators. Getting this wrong in the *strong* direction, by demanding that all blocks be referenced, would assume Byzantine validators behave.

**This does not follow from view convergence.** A block's references are frozen when it is built: a correct validator waits for `2f+1` round-`n` blocks, and the arrival of the `2f+1`st says nothing about the rest having arrived. Views converging later does not retroactively enlarge blocks. So this is an assumption, not a theorem — see `liveness.md` §4.3, and its §8 question 8 for how it is meant to be split and derived.

#### `Synchronised`

*abbrev, `Liveness.lean`*

```lean
abbrev Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Validator) R
```

The all-of-`Correct` case.

#### `EventuallyDelivers`

*def, `Liveness.lean`*

```lean
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n
```

**The network assumption**: after `R`, correct blocks reach correct validators in time to be built on. This is eventual DAG synchrony proper — pure delivery, no protocol content.

#### `View.full`

*def, `Liveness.lean`*

```lean
def View.full (U : BlockUniverse Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete
```

Every correct validator's *eventual* view. Downward-closed by `U.complete`.

#### `VotesAt`

*def, `Liveness.lean`*

```lean
def VotesAt (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 1 → L ∈ (U.block c).refs
```

**What the two-round rules count** — the targeted half of coverage: every `T`-authored block one round above `r` references `L`. This is the meet point of the pacing disciplines (report §11): full coverage implies it outright (`votesAt_of_synchronisedOn`), and the reactive exit supplies it directly (`ReactivePace.votes`), so the commit arguments below are stated against it and proved once. Round-indexed and schedule-free, as L4's round-level forms are.

#### `CertifiesAt`

*def, `Liveness.lean`*

```lean
def CertifiesAt (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = r + 2 → Certifies U c L
```

**What the three-round rule counts**: every `T`-authored block at the decision round certifies `L`. Coverage implies it through the vote layer (`certifiesAt_of_synchronisedOn`); the reactive certificate wait supplies it directly (`ReactiveM.certifies`).

#### `CommitsAt`

*def, `Liveness.lean`*

```lean
def CommitsAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**A slot every sufficiently grown synchronous execution commits.**

The conclusion the recurrence results share. Naming it keeps their quantifier order visible — the slot is fixed by the schedule alone, before any execution is named — and keeps production and coverage as the two separate hypotheses they are, rather than bundling them.

**Both hypotheses are relative to the same `T`.** They were not: production was asked over all of `Correct` while coverage was asked over `T`, which is strictly more than anything downstream consumes — `decided_of_leader_of_populated` discarded the excess immediately. Asking both over `T` makes this a statement about *any* quorum-sized set of reliable validators: the correct validators outside `T` may be permanently starved and the slot still commits. That is not a vacuous generality — `reliable_set_is_forced_pace` (V12) exhibits a DAG in which coverage over a proper subset of `Correct` holds and coverage over `Correct` fails. It is a genuine weakening only below full fault load, since `|byzantine| = f` forces `T = Correct` (`reliable_eq_correct`).

**Production is asked for only from `R` on.** The rule reads it off at three rounds, all of them at or above `R`, so rounds below the synchrony round were never consumed. Dropping them matters because that is exactly the range a structure carrying the *build rule* rather than a total block function can supply. With the hypothesis cut to the range that is used, P8 in its conditional form reaches liveness — `ViewPace.commits_recur_via_pace`.

#### `FairScheduleOn`

*def, `Liveness.lean`*

```lean
def FairScheduleOn (T : Finset Validator) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T
```

The schedule names a correct leader arbitrarily far out. Without it no recurrence statement holds: `Slots.leader` is an arbitrary function and could name Byzantine validators forever, however synchronous the network.

#### `FairSchedule`

*abbrev, `Liveness.lean`*

```lean
abbrev FairSchedule : Prop := FairScheduleOn (Correct : Finset Validator)
```

The all-of-`Correct` case.

#### `FairToEach`

*def, `Liveness.lean`*

```lean
def FairToEach (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ k, ∃ k', k ≤ k' ∧ S.leader k' = v
```

**Every member of `T` leads arbitrarily far out** — per-validator fairness, strictly stronger than `FairScheduleOn`, which promises only *some* `T`-leader. Round-robin supplies it (`rrSlots_fairToEach`), and the rotation-inclusion result of report §11.5 is what consumes it: a straggler's block enters the ledger when its *own author* leads, so the schedule must return to that author in particular.

#### `FairRunOn`

*def, `Liveness.lean`*

```lean
def FairRunOn (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T
```

**The schedule puts `c` consecutive `T`-led slots arbitrarily far out.**

Stronger than `FairScheduleOn`, which promises one `T`-led slot and no more, and it is what P7′ needs: `decided_below_of_committed_run` is fed a *run* of commits, and L4 turns a run of `T`-led slots into one.

Round-robin over `3f+1` satisfies it with `c = 3` for every `f ≥ 1`, whatever the `f` Byzantine validators are and wherever they sit in the rotation. The `f` of them cut the cycle into at most `f` arcs holding `2f+1` correct slots between them, so some arc has at least `⌈(2f+1)/f⌉ = 3` — the ceiling being `3` for all `f ≥ 1` since `(2f+1)/f = 2 + 1/f`. Three is exactly what pipelining asks for, which is a pleasant coincidence rather than a designed one.

Like `FairScheduleOn` this is an assumption about the schedule, not a theorem: `Slots.leader` is arbitrary and could name Byzantine validators for ever.

#### `SpansEligible`

*def, `Liveness.lean`*

```lean
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)
```

**A run of `c` slots reaches three rounds past everything below it.**

This is the one place the schedule's *shape* enters P7′, and it is what makes `decided_below_of_committed_run`'s `hspan` available: the last slot of a run starting at `b` is an eligible anchor for every slot below `b`.

It holds with `c = 1` under three-round spacing and with `c = 3` under pipelining — one commit against three consecutive, which is the entire cost pipelining imposes on this property.

#### `slotAt`

*def, `Liveness.lean`*

```lean
def slotAt (n : ℕ) : ℕ := Nat.find (S.unbounded n)
```

The least slot proposed at or after round `n`.

A three-round-spaced schedule needs no such thing: `3 * k ≤ slotRound k` made slot `n` itself sit past round `n`, so `n` could be used as its own slot index. That coincidence is gone — under multiple leaders slot `n` may still be far below round `n` — so the slot has to be named.

### Time: GST, and the rated bounds

#### `Rated`

*def, `Quantitative.lean`*

```lean
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n
```

A backoff that grows **at least as fast as the round index**.

Weaker than it may look, and deliberately so: it fixes no shape, and any schedule dominating the identity qualifies — linear, exponential, or a step function that jumps early and then plateaus high. What it rules out is exactly what `hub` permits: growth so slow that clearing a fixed threshold takes unboundedly many rounds.

#### `FairWithin`

*def, `Quantitative.lean`*

```lean
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T
```

The schedule names a `T`-leader **within every window of `w` slots**.

The rated form of `FairScheduleOn`. Note `w` is a property of the schedule alone — no DAG, no network — which is what keeps L6's quantifier order intact: the slot is still fixed before any universe is mentioned.

#### `BoundedSpacing`

*def, `Quantitative.lean`*

```lean
def BoundedSpacing (s : ℕ) : Prop := ∀ k, S.slotRound (k + 1) ≤ S.slotRound k + s
```

Consecutive slots are at most `s` rounds apart — the upper companion to such a field. Every real schedule has one; the class omits it because no safety result ever asks.

### The pacing structures, and the delivery they induce

#### `DriftOn`

*def, `ViewPace.lean`*

```lean
def DriftOn (built : Validator → ℕ → ℕ) (T : Finset Validator)
    (R D N : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, R ≤ n → n ≤ N → built w n ≤ built v n + D
```

Drift over a build schedule alone: `T`-validators are never more than `D` apart in real time at the same round, from `R` on.

#### `ConvergesEventually`

*def, `ViewPace.lean`*

```lean
def ConvergesEventually (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, ∃ d, holds w t ⊆ holds v (t + d)
```

**The qualitative half.** Holdings converge: whatever `w` holds at `t`, `v` holds at some later time. No bound and no GST.

#### `ConvergesWithin`

*def, `ViewPace.lean`*

```lean
def ConvergesWithin (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) (gst bound : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + bound)
```

**The quantitative half.** From `gst` on, that lag is at most `bound` — and uniformly so, in the validators and in the time. This is exactly the `converges` field of `ViewPace`.

#### `PaceCore`

*structure, `ViewPace.lean`*

```lean
structure PaceCore (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- The highest round `v` reached. Rounds above it were never built. -/
  top : Validator → ℕ
  /-- When `v` built its round-`n` block — read only at `n ≤ top v`. -/
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  /-- **Every round `v` reached, it built in.** At `n = 0` this is
  genesis — a validator produces its genesis block alone, so this
  much needs no network at all. Above `0` it is the reading of `top`: the
  validator got there, which is to say it built there. -/
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  /-- **And no round above it.** Together with the previous clause, `v`'s
  blocks are exactly rounds `0` through `top v`. -/
  le_top_of_built : ∀ v ∈ T, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round ≤ top v
  timeout_pos : ∀ n, 1 ≤ timeout n
  /-- An upper bound on when round `n` was built, over `T`. Only an upper
  bound is ever needed: production reads it for the common time at which
  `converges` assembles the quorum, and nothing else consults it. -/
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  holds : Validator → ℕ → Finset BlockId
  /-- **S3.** A validator holds only blocks that exist. Nothing else ties
  `holds` to the universe: the liveness development never needs it, and the
  clause is stated here only so that a validator's holdings generate a
  `View` (`viewAt`), which is what connects the pacing line to the
  view-relative decision rules. -/
  holds_sub : ∀ v, ∀ t, holds v t ⊆ U.ids
  /-- **S4.** Holdings are causally closed: a validator that holds a block
  holds everything it references. This is P4 as a *store* property — the
  universe-level version is already assumed, and this says a validator
  receives blocks the same way it stores them. A block whose history is
  missing cannot be validated (P3, P3′ read the referenced blocks) and
  cannot be built upon, so an implementation that admitted one could not
  act on it; the clause is what stops the model obliging a validator to
  advance on evidence no implementation could use, and it is what makes
  `viewAt` a validator's own view rather than the closure of its
  fragments (`viewAt_ids`). -/
  holds_closed : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t,
    ∀ j ∈ (U.block b).refs, j ∈ holds v t
  /-- **S5.** A validator's block references only what it held when it
  built --- the converse of P7, and like it implementable and observable.
  It sits on the trunk rather than in a timeout discipline because it is
  discipline-independent: a reactive builder omits what it holds, but no
  builder can cite what it never held. -/
  refs_held : ∀ v ∈ T, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ holds v (built v (n + 1))
  /-- A validator holds every block it authored, from the time it built it. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P8, as the pacemaker's progress rule** (protocol). A validator that
  holds a quorum of distinct round-`n` authors — *at any time whatever* —
  gets past round `n`.

  This is the clause a total schedule cannot carry honestly. There, the
  quorum had to be in hand at the one time `built v (n+1)` names, so the
  rule either missed it (and the round stayed empty for ever) or, stated as
  a converse, forced the quorum to exist. Here there is no such time: the
  hypothesis is that `v` ever holds a quorum, and the conclusion is that it
  advances. It asserts no production, since it says nothing until a quorum
  is in hand. -/
  advances : ∀ v ∈ T, ∀ n < N, ∀ t,
    quorumCard Validator ≤ (authorsIn U (holds v t) n).card → n < top v
  /-- The processing bound: how long round entry may lag evidence. -/
  proc : ℕ
  /-- **Catch-up** (protocol). Seeing a round is entering it: any
  `T`-authored block of round `n` in hand at a post-GST time `t` means
  the holder reached round `n` and built its own block there by
  `t + proc`. This is the rule real pacemakers run, and it is what makes
  drift a *derived* quantity: the spread at any post-GST round is at
  most `delay + proc`, whatever it was at the start (`drift_collapse`),
  so no start-spread hypothesis survives into the headline statements.

  The clause is asserted only from `gst` — like `converges`, and for the
  same reason: what a validator runs is the GST-free clamped rule (enter
  a sighted round within `proc`, never before the own floor), and past
  GST the floor provably never delays it, while before GST it may. An
  unconditional clause would over-claim about every real
  implementation; the gated one asserts exactly what the clamped rule
  delivers. -/
  catchup : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator ∈ T → (U.block b).round = n →
    ∀ t, gst ≤ t → b ∈ holds v t → n ≤ top v ∧ built v n ≤ t + proc
```

**The shared trunk of every pacing discipline**, over a **partial** build schedule.

`top v` is the highest round `v` reached. Its two clauses say that `v`'s blocks are exactly the rounds `0` through `top v`: `built_of_le_top` supplies one at each of them, and `le_top_of_built` says there are none above. Neither is an assumption about the network — the first at `n = 0` is genesis, which a validator satisfies alone, and the rest of it is the definition of how far the validator got. The schedule clauses of the extensions are guarded by `n < top v`, since a round the validator never reached has no build time worth constraining.

The trunk carries the schedule data, the views, the network's convergence clause, and the pacemaker's two rules — `advances` (a quorum in hand means the round is passed) and `catchup` (a round sighted is a round entered, within `proc`) — everything production and drift consume, and nothing about *when* a validator chooses to build within a round. The timeout disciplines extend it: `ViewPace` adds the full-timeout floor (P9) with global referencing (P7); the reactive schedule (report §11) adds the deadline and the vote clauses in their place. Production (`PaceCore.populatedOn`) and the drift collapse (`drift_collapse`) are proved here, once, and inherited by both.

#### `viewAt`

*def, `ViewPace.lean`*

```lean
def viewAt (pc : PaceCore U T N) (v : Validator) (t : ℕ) :
    View Validator BlockId Payload U where
  ids := (pc.holds v t).biUnion (history U)
  subset_ids := by
    intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    exact history_subset_ids (pc.holds_sub v t ha) hia
  complete := by
    intro i hi j hj
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    have ha_ids : a ∈ U.ids := pc.holds_sub v t ha
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    exact (mem_history_iff ha_ids).mpr
      (((mem_history_iff ha_ids).mp hia).trans (Reaches.single hj))
```

**The view a validator's holdings generate.** The causal closure of what `v` holds at `t` — a legitimate `View`, so the decision rules of the safety development apply to it directly. Closure is discharged by transitivity of `Reaches`, exactly as for `View.ofAccepted`: a union of causal histories is downward closed, and no closure obligation is met by hand.

This is the object that connects the two halves of the development. The pacing line reasons about `holds`, a time-indexed set with no structure; the commit rules reason about a `View`. `viewAt` is the bridge, and it is what lets liveness be stated about a validator's *own* view rather than about the full universe.

#### `ViewPace`

*structure, `ViewPace.lean`*

```lean
structure ViewPace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends PaceCore U T N where
  /-- **P9, the waiting rule** (protocol), over the rounds `v` reached. -/
  waits : ∀ v ∈ T, ∀ n < top v, built v n + timeout n ≤ built v (n + 1)
  /-- **P7, referencing** (protocol), over any block the validator authors. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs
```

The full-timeout discipline: `PaceCore` with P9 — the waiting floor — and the global referencing clause P7. This is the structure the coverage derivation and the quantitative results run on; the reactive schedule (report §11) extends the same trunk with a deadline in place of the floor.

No promptness ceiling and no attainment clause appear: drift is derived from the trunk's catch-up rule (`driftOn_of_catchup`), which needs neither — the collapse argument runs on `converges`, `holds_own` and `catchup` alone.

#### `heldOf`

*def, `PaceDelivery.lean`*

```lean
def heldOf (v : Validator) (n : ℕ) : Finset BlockId :=
  if n < N then (vp.holds v (vp.built v (n + 1))).filter (fun b => (U.block b).round = n)
  else ∅
```

**The round-indexed reading of `holds`**: what `v` held of round `n` at the instant it built its round-`(n+1)` block. Above the horizon there is no build to read, and the set is empty.

#### `acceptedOf`

*def, `PaceDelivery.lean`*

```lean
def acceptedOf (v : Validator) (n : ℕ) : Finset BlockId :=
  if v ∈ (Correct : Finset Validator) then vp.heldOf v n else ∅
```

What a validator builds on. A correct validator builds on everything it held --- it has no reason to discard, and P7 obliges it to reference all of it; nothing is claimed of a Byzantine validator, whose acceptance is left empty because no clause of the pacing structure constrains it.

#### `toDelivery`

*def, `PaceDelivery.lean`*

```lean
def toDelivery : Delivery U where
  held := vp.heldOf
  held_spec := by
    intro v n i hi
    by_cases hn : n < N
    · obtain ⟨hhold, hround⟩ := (vp.mem_heldOf hn).mp hi
      exact ⟨vp.holds_sub v _ hhold, hround⟩
    · simp [heldOf, hn] at hi
  accepted := vp.acceptedOf
  accepted_sub := by
    intro v n
    unfold acceptedOf
    split
    · exact Finset.Subset.rfl
    · exact Finset.empty_subset _
  accepted_inj := by
    intro v n i hi j hj hij
    unfold acceptedOf at hi hj
    split at hi
    · rename_i hv
      by_cases hn : n < N
      · exact vp.heldOf_inj hv hn hi (by simpa [acceptedOf, hv] using hj) hij
      · simp [heldOf, hn] at hi
    · simp at hi
  accepts_correct := by
    intro v hv n a ha _
    simpa [acceptedOf, hv] using ha
  includes := by
    intro v hv n b hb hbc hbr
    unfold acceptedOf
    rw [if_pos hv]
    intro a ha
    by_cases hn : n < N
    · obtain ⟨hhold, hround⟩ := (vp.mem_heldOf hn).mp ha
      exact vp.references v hv n hn b hb hbc hbr a hhold hround
    · simp [heldOf, hn] at ha
```

**A pacing structure induces a delivery layer** (V19). Every field is discharged from the pacing clauses: `held_spec` from `holds_sub` and the round filter, `accepted_inj` from P7 with P2 (`heldOf_inj`), and `includes` from P7 read at the build instant. The storage arcs of report §§8--9 can therefore be run over an execution the liveness development produces, rather than over a separately postulated layer.

### Chain quality

#### `coveredAt`

*def, `Quality.Coverage.lean`*

```lean
def coveredAt (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) (δ : ℕ) : Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ
```

The correct validators whose round-`δ` block a cone carries — the complement, within `Correct`, of `missingAt`.

#### `IncludesAt`

*def, `Quality.Inclusion.lean`*

```lean
def IncludesAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (R m k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r ≤ N, Populated U r) → Synchronised U R →
    S.slotRound k + 2 ≤ N →
    ∃ L, Decided U (View.full U) k (some L) ∧
      ∀ b ∈ U.ids,
        (U.block b).creator ∈ (Correct : Finset Validator) →
        (U.block b).round = m →
        b ∈ history U L ∧
        ∀ (g : ℕ → Option BlockId) (n : ℕ), g k = some L → k < n →
          b ∈ ledgerSet U g n
```

**A slot whose commit carries a whole round into the ledger.**

The conclusion CQ6 and its refinements share: in any sufficiently grown synchronous execution, slot `k` commits a leader whose history contains every correct round-`m` block, and every such block is in the agreed ledger from any later position. Naming it keeps the quantifier order visible — `k` is fixed by the schedule before an execution is named — as `CommitsAt` does for the recurrence results.

### Denial of service

#### `EquivPair`

*def, `DoS.Exposure.lean`*

```lean
def EquivPair (U : BlockUniverse Validator BlockId Payload) (X : Validator) (i j : BlockId) :
    Prop :=
  i ≠ j ∧ (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round
```

Two ids witnessing an equivocation by `X`: distinct, both authored by `X`, both at one round.

Split out from `ExposedIn` so that D13 can quantify over the *same* witness condition with and without a view restriction.

#### `ExposedIn`

*def, `DoS.Exposure.lean`*

```lean
def ExposedIn (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Prop :=
  ∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j
```

**`X` is exposed in `b`'s history**: two distinct blocks by `X` at one round lie below `b`.

Stated over `history` rather than over `Reaches` so that it is decidable and countable; `exposedIn_iff_reaches` gives the `Reaches` form for a block of the universe.

#### `DoSValid`

*def, `DoS.Exposure.lean`*

```lean
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

**The DoS-protection condition** (`dos-equivocation-and-growth.md` §3): a block may not reference an author exposed in its own history.

A predicate on the universe, deliberately **not** a field of `ValidWrt`. Every safety and liveness theorem in the development applies verbatim under it, because none of them mention it; results that need it take it as an extra hypothesis.

#### `historyBlocksOf`

*def, `DoS.Exposure.lean`*

```lean
def historyBlocksOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId)
    (X : Validator) (n : ℕ) : Finset BlockId :=
  (history U b).filter (fun i => (U.block i).creator = X ∧ (U.block i).round = n)
```

The blocks of `b`'s history authored by `X` at round `n`. The thing the size results count.

#### `exposedTo`

*def, `DoS.Exposure.lean`*

```lean
def exposedTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) : Finset Validator :=
  Finset.univ.filter (fun X => ExposedIn U b X)
```

The authors a block's history has caught.

#### `missingAt`

*def, `DoS.Density.lean`*

```lean
def missingAt (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (δ : ℕ) :
    Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ)
```

The correct validators with no block at round `δ` in `b`'s history.

#### `atRound`

*def, `DoS.Counting.lean`*

```lean
def atRound (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) (n : ℕ) :
    Finset BlockId :=
  s.filter (fun i => (U.block i).round = n)
```

The blocks of `s` at round `n`. Generalises `blocksAt`, which is this at `s := U.ids`.

#### `EquivFree`

*def, `DoS.Counting.lean`*

```lean
def EquivFree (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j
```

No two distinct blocks of `s` share an author and a round.

A property of the **set**, not of the universe: `U` may be full of equivocations while a particular `s` is free of them, which is exactly the situation D8a describes.

#### `topsOf`

*def, `DoS.Adoption.lean`*

```lean
def topsOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Finset BlockId :=
  (history U b).filter fun t => (U.block t).creator = X ∧
    ∀ c ∈ history U b, (U.block c).creator = X → t ∉ (U.block c).refs
```

The chain tops of author `X` in `b`'s history: `X`-blocks with no `X`-authored child there. Chains being priced exactly (D22/D23), tops are what remains to count.

#### `AdoptedUnder`

*def, `DoS.Pedigree.lean`*

```lean
def AdoptedUnder (U : BlockUniverse Validator BlockId Payload) (b t T : BlockId) : Prop :=
  ∃ j ∈ history U b, j ∈ history U T ∧
    (U.block j).creator = (U.block T).creator ∧ t ∈ (U.block j).refs
```

`t` is adopted under `T`: some block of `T`'s own author, inside `T`'s history, references `t`. By D21/D22 such a block sits on `T`'s chain, so per (`T`, author-of-`t`) the adopted top is unique (`top_eq_of_mem_namer_history`).

#### `PedigreeTo`

*inductive, `DoS.Pedigree.lean`*

```lean
inductive PedigreeTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → List Validator → Prop
  | base : PedigreeTo U b b []
  | step {t T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator →
      AdoptedUnder U b t T →
      PedigreeTo U b T l →
      PedigreeTo U b t ((U.block T).creator :: l)
```

An adoption pedigree: the climb from a top to `b`, recording the adopters' authors.

#### `PedigreeVia`

*inductive, `DoS.Pedigree.lean`*

```lean
inductive PedigreeVia (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → BlockId → List Validator → Prop
  | base {t T : BlockId} :
      t ∈ topsOf U b (U.block t).creator → AdoptedUnder U b t T →
      PedigreeVia U b t T []
  | step {t T₁ T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator → AdoptedUnder U b t T₁ →
      PedigreeVia U b T₁ T l →
      PedigreeVia U b t T ((U.block T₁).creator :: l)
```

A pedigree anchored at an arbitrary block `T` rather than at `b`, recording only the *intermediate* adopters' authors.

#### `encodeList`

*def, `DoS.Pedigree.lean`*

```lean
def encodeList (E' : Finset Validator) (m : ℕ) (l : List Validator) :
    Fin m → Option {W // W ∈ E'} :=
  fun k => if hk : (k : ℕ) < l.length then
      if hmem : l[(k : ℕ)] ∈ E' then some ⟨l[(k : ℕ)], hmem⟩ else none
    else none
```

The padded encoding of a list of at most `m` members of `E'`: entry `k` is the `k`-th element when there is one, and `none` past the end.

Used to count lists by counting functions — a `Finset` of lists of bounded length has no convenient cardinality, whereas `Fin m → Option _` does.

#### `DoSAccepting`

*def, `DoS.Exclusion.lean`*

```lean
def DoSAccepting (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    ∀ i ∈ D.accepted v n, ¬ ExposedIn U b (U.block i).creator
```

The policy: nothing a correct validator accepts is exposed to the block it goes on to build.

#### `ReferencesAccepted`

*def, `DoS.Exclusion.lean`*

```lean
def ReferencesAccepted (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted v n
```

The tight half of `includes`: a correct validator references *exactly* what it accepted, no more. `Delivery.includes` gives the other inclusion, and D3's sharp bound wants both.

#### `HeldByCorrect`

*def, `DoS.Exclusion.lean`*

```lean
def HeldByCorrect (D : Delivery U) : Prop :=
  ∀ i ∈ U.ids, ∃ v ∈ (Correct : Finset Validator), i ∈ D.held v (U.block i).round
```

**What `U` means, made explicit.** §4.2 of `liveness.md` defines `U` as every block some correct validator held; the model has never said so.

#### `AcceptsSome`

*def, `DoS.Exclusion.lean`*

```lean
def AcceptsSome (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ D.held v n,
    ∃ i ∈ D.accepted v n, (U.block i).creator = (U.block a).creator
```

**A stronger acceptance policy**: a validator that holds a block by some author accepts *some* block by that author. `Delivery.accepts_correct` demands this only of correct authors.

#### `Accepted`

*structure, `DoS.Acceptance.lean`*

```lean
structure Accepted (U : BlockUniverse Validator BlockId Payload)
    (A : Finset BlockId) (n : ℕ) : Prop where
  /-- Only real blocks are accepted. -/
  subset_ids : A ⊆ U.ids
  /-- One round: the frontier. -/
  round_eq : ∀ i ∈ A, (U.block i).round = n
  /-- At most one block per author — the rule. -/
  inj : ∀ i ∈ A, ∀ j ∈ A, (U.block i).creator = (U.block j).creator → i = j
```

What a validator has accepted at round `n`: real blocks of that round, at most one per author.

The injectivity field is the acceptance rule, and it is the only one D2 uses — the round field is what makes `A` a *frontier* rather than an accumulation, and is used by D3.

#### `View.ofAccepted`

*def, `DoS.Acceptance.lean`*

```lean
def View.ofAccepted (h : Accepted U A n) : View Validator BlockId Payload U where
  ids := A.biUnion (history U)
  subset_ids := by
    intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    exact history_subset_ids (h.subset_ids ha) hia
  complete := by
    intro i hi j hj
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    have ha_ids : a ∈ U.ids := h.subset_ids ha
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    exact (mem_history_iff ha_ids).mpr
      (((mem_history_iff ha_ids).mp hia).trans (Reaches.single hj))
```

**D1 — the view an accepted set generates.**

That this typechecks *is* the result: `complete` is discharged by transitivity of `Reaches`, so a union of causal histories is downward closed and no closure obligation has to be met by hand.

#### `novelty`

*def, `DoS.Novelty.lean`*

```lean
def novelty (U : BlockUniverse Validator BlockId Payload) (V : Finset BlockId)
    (b : BlockId) : Finset BlockId :=
  history U b \ V
```

What accepting `b` would newly bring into the view `V`.

#### `StepNovelty`

*def, `DoS.Novelty.lean`*

```lean
def StepNovelty (U : BlockUniverse Validator BlockId Payload) (κ' : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ p ∈ (U.block b).refs, (U.block p).creator = (U.block b).creator →
      (novelty U (history U p) b).card ≤ κ'
```

Stepwise novelty: every correct block adds at most `κ'` blocks over the history of its self-parent. For a correct author the self-parent is unique (`no_equivocation`), so the `∀` is free of content.

#### `viewUpto`

*def, `DoS.Novelty.lean`*

```lean
def viewUpto (D : Delivery U) (v : Validator) : ℕ → Finset BlockId
  | 0 => (D.accepted v 0).biUnion (history U)
  | n + 1 => viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
```

Everything `v` has retained by round `n`: the whole histories of everything it accepted at any round up to `n` — the retained view of S1, accumulated. This is what novelty is measured against, and the reason C3 works: accepting a block means holding its entire cone.

#### `ByzBudget`

*def, `DoS.Novelty.lean`*

```lean
def ByzBudget (D : Delivery U) (κ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (U.block b).creator ∉ (Correct : Finset Validator) →
    (novelty U (viewUpto D v n) b).card ≤ κ
```

The **analysis-side budget**: only the Byzantine clause. This is the weakest thing the theorems need — Byzantine-authored acceptances were within the budget — and the correct clause is *derived* from it (`card_novelty_le_of_byzBudget`): a schedule keeping Byzantine acceptances under `κ` never carries a correct block over `f·κ + 1`. The creator guard is bookkeeping, never something a validator evaluates; the enforced form is `UniformBudget` below.

#### `UniformBudget`

*def, `DoS.Novelty.lean`*

```lean
def UniformBudget (D : Delivery U) (τ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤ τ
```

**The mechanism-side budget** — the rule a validator actually runs: a guard-free cap on every acceptance, author-blind. Enforcing the cap on everyone enforces it on the Byzantine authors (`UniformBudget.byzBudget`), and post-`R` the converse holds at `f·κ + 1` (`uniform_of_byzBudget` below) — the two formulations sandwich within one factor of `f`, the exact price of author-blindness.

#### `viewGap`

*def, `DoS.Novelty.lean`*

```lean
def viewGap (D : Delivery U) (v w : Validator) (n : ℕ) : Finset BlockId :=
  viewUpto D w n \ viewUpto D v n
```

The standing divergence between two correct validators' retained views: what `w` holds that `v` does not.

#### `RefsAccepted`

*def, `DoS.Novelty.lean`*

```lean
def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n
```

D3's ordinary case as a protocol property: a correct validator's block references **only** what it accepted — the converse of `includes`; together they say `refs = accepted`.

#### `byzPool`

*def, `DoS.Novelty.lean`*

```lean
def byzPool (D : Delivery U) (n : ℕ) : Finset BlockId :=
  (Correct : Finset Validator).biUnion fun w =>
    (viewUpto D w n).filter
      fun i => (U.block i).creator ∉ (Correct : Finset Validator)
```

The **global Byzantine pool**: every Byzantine-authored block sitting in any correct validator's retained view.

#### `AllExposed`

*def, `DoS.Composition.lean`*

```lean
def AllExposed (U : BlockUniverse Validator BlockId Payload) (m : ℕ) : Prop :=
  ∀ X : Validator, X ∉ (Correct : Finset Validator) →
    ∀ c ∈ U.ids, (U.block c).round = m + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X
```

**Exposure-complete at `m`**: every correct block of round `m+1` is exposed to every Byzantine author — the state D16 manufactures once all `f` authors have equivocated toward the correct population.

### Garbage collection

#### `chopBlock`

*def, `GC.Chop.lean`*

```lean
def chopBlock (U : BlockUniverse Validator BlockId Payload) (G : ℕ)
    (i : BlockId) : Block Validator BlockId Payload :=
  if (U.block i).round ≤ G then
    { U.block i with round := (U.block i).round - G, refs := ∅ }
  else
    { U.block i with round := (U.block i).round - G }
```

One block of the truncation: the round is rebased by `−G`, and blocks at or below the cut — the new base layer, plus junk — lose their references.

#### `chop`

*def, `GC.Chop.lean`*

```lean
def chop (U : BlockUniverse Validator BlockId Payload) (G : ℕ) :
    BlockUniverse Validator BlockId Payload where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlock U G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlock_refs_of_lt h] at hj
      have hj_ids := U.complete i hi.1 j hj
      have hj_round := U.round_of_mem_refs hi.1 hj
      exact Finset.mem_filter.mpr ⟨hj_ids, by omega⟩
    · rw [chopBlock_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hv := U.valid i hi.1
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    swap
    · -- the new base layer (and junk): no references, nothing to prove
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro j hj
             rw [chopBlock_refs_of_le h] at hj
             exact absurd hj (Finset.notMem_empty j))
          | (intro hr
             rw [chopBlock_round] at hr
             omega)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- predecessor, rebased
        intro j hj
        rw [chopBlock_refs_of_lt h] at hj
        have := hv.predecessor j hj
        rw [chopBlock_round, chopBlock_round]
        omega
      · -- distinct creators, untouched
        intro a ha b hb hab
        rw [chopBlock_refs_of_lt h] at ha hb
        rw [chopBlock_creator, chopBlock_creator] at hab
        exact hv.distinct_creators a ha b hb hab
      · -- quorum, untouched
        intro _
        have hcr : creators (chopBlock U G) (chopBlock U G i) =
            creators U.block (U.block i) := by
          unfold creators
          rw [chopBlock_refs_of_lt h, creatorsOf_chopBlock]
        rw [hcr]
        exact hv.quorum (by omega)
      · -- self-parent, untouched
        intro _
        obtain ⟨p, hp, hpc⟩ := hv.self_parent (by omega)
        refine ⟨p, ?_, ?_⟩
        · rw [chopBlock_refs_of_lt h]; exact hp
        · rw [chopBlock_creator, chopBlock_creator]; exact hpc
  no_equivocation := by
    intro i hi j hj hic hcreator hround
    rw [Finset.mem_filter] at hi hj
    rw [chopBlock_creator] at hic hcreator
    rw [chopBlock_creator] at hcreator
    rw [chopBlock_round, chopBlock_round] at hround
    exact U.no_equivocation i hi.1 j hj.1 hic hcreator (by omega)
```

**The horizon** (`garbage.md` §2): the universe above the cut, rounds rebased, the round-`G` layer as the new geneses.

#### `View.chop`

*def, `GC.ChopDecided.lean`*

```lean
def View.chop (V : View Validator BlockId Payload U) (G : ℕ) :
    View Validator BlockId Payload (chop U G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chop_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rw [chop_block_eq] at hj
    rcases Nat.lt_or_ge G (U.block i).round with hlt | hge
    · rw [chopBlock_refs_of_lt hlt] at hj
      have := U.round_of_mem_refs (V.subset_ids hi.1) hj
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj, by omega⟩
    · rw [chopBlock_refs_of_le hge] at hj
      simp at hj
```

A validator's view, truncated at the horizon: keep what clears the cut. Closure survives: a retained block's references sit one round below it, hence at or above the cut — except at the base layer, where they are gone.

#### `Slots.chop`

*def, `GC.ChopDecided.lean`*

```lean
def Slots.chop (S : Slots Validator) (G d : ℕ) (hd : G ≤ S.slotRound d) :
    Slots Validator where
  slotRound k := S.slotRound (d + k) - G
  leader k := S.leader (d + k)
  mono _ _ h := Nat.sub_le_sub_right (S.mono (Nat.add_le_add_left h d)) G
  unbounded := by
    intro n
    obtain ⟨k, hk⟩ := S.unbounded (G + n)
    rcases Nat.le_total k d with hkd | hdk
    · refine ⟨0, ?_⟩
      have := S.mono hkd
      simp only [Nat.add_zero]
      omega
    · refine ⟨k - d, ?_⟩
      have hcancel : d + (k - d) = k := by omega
      simp only [hcancel]
      omega
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have h₁ := hd.trans (S.mono (Nat.le_add_right d k₁))
    have h₂ := hd.trans (S.mono (Nat.le_add_right d k₂))
    have hpair : (S.slotRound (d + k₁), S.leader (d + k₁))
        = (S.slotRound (d + k₂), S.leader (d + k₂)) := by
      have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
      rw [this, hl]
    have := S.keyed hpair
    omega
```

The truncation's slot schedule: slots re-indexed from a base slot `d` whose round clears the horizon, rounds rebased by `−G`. The base-slot condition keeps subtraction faithful, which is what keying needs.

#### `chopD`

*def, `GC.Window.lean`*

```lean
def chopD (D : Delivery U) (G : ℕ) : Delivery (chop U G) where
  held v m := D.held v (G + m)
  held_spec := by
    intro v m i hi
    obtain ⟨h1, h2⟩ := D.held_spec v (G + m) i hi
    refine ⟨mem_chop_ids.mpr ⟨h1, by omega⟩, ?_⟩
    rw [chop_block_eq, chopBlock_round]
    omega
  accepted v m := D.accepted v (G + m)
  accepted_sub v m := D.accepted_sub v (G + m)
  accepted_inj := by
    intro v m i hi j hj hij
    rw [chop_block_eq, chopBlock_creator, chopBlock_creator] at hij
    exact D.accepted_inj v (G + m) i hi j hj hij
  accepts_correct := by
    intro v hv m a ha hac
    rw [chop_block_eq, chopBlock_creator] at hac
    exact D.accepts_correct v hv (G + m) a ha hac
  includes := by
    intro v hv m b hb hbc hbr
    rw [mem_chop_ids] at hb
    rw [chop_block_eq, chopBlock_creator] at hbc
    rw [chop_block_eq, chopBlock_round] at hbr
    have hsub := D.includes v hv (G + m) b hb.1 hbc (by omega)
    intro i hi
    rw [chop_block_eq, chopBlock_refs_of_lt (by omega)]
    exact hsub hi
```

A delivery for the truncation: round `m` of the window is round `G + m` of the original. Nothing below the cut is consulted.

#### `attesters`

*def, `GC.AttestedBase.lean`*

```lean
def attesters (U : BlockUniverse Validator BlockId Payload) (t : ℕ)
    (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)
```

The authors attesting `y` at round `t`: those with a round-`t` block whose cone holds `y`. An author's block *is* its attestation.

#### `Base`

*def, `GC.AttestedBase.lean`*

```lean
def Base (U : BlockUniverse Validator BlockId Payload) (t G : ℕ) :
    Finset BlockId :=
  (blocksAt U G).filter fun y => F.f + 1 ≤ (attesters U t y).card
```

**The inexact certificate**: the round-`G` blocks attested by more than `f` distinct authors at round `t`.

#### `joinIds`

*def, `GC.Bootstrap.lean`*

```lean
def joinIds (D : Delivery U) (w : Validator) (m t G : ℕ) : Finset BlockId :=
  Base U t G ∪ ((viewUpto D w m).filter fun i => G < (U.block i).round)
```

What a joiner fetches: the attested base as its genesis layer, plus a correct peer's window strictly above the cut, up to frontier `m`. The round-`G` layer comes **only** from the base — that is the rebasing.

#### `joinView`

*def, `GC.Bootstrap.lean`*

```lean
def joinView {R m t : ℕ} (hs : Synchronised U R)
    (hw : w ∈ (Correct : Finset Validator)) (hcar : Populated U (m + 1))
    (hpop : Populated U t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    View Validator BlockId Payload (chop U G) where
  ids := joinIds D w m t G
  subset_ids := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨⟨hids, hround⟩, -⟩ := mem_base.mp h
      exact mem_chop_ids.mpr ⟨hids, by omega⟩
    · obtain ⟨hiv, hround⟩ := Finset.mem_filter.mp h
      exact mem_chop_ids.mpr ⟨viewUpto_subset_ids hiv, by omega⟩
  complete := by
    intro i hi j hj
    rw [chop_block_eq] at hj
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨⟨hids, hround⟩, -⟩ := mem_base.mp h
      rw [chopBlock_refs_of_le (by omega)] at hj
      simp at hj
    · obtain ⟨hiv, hround⟩ := Finset.mem_filter.mp h
      have hiids : i ∈ U.ids := viewUpto_subset_ids hiv
      rw [chopBlock_refs_of_lt hround] at hj
      have hjv : j ∈ viewUpto D w m := mem_viewUpto_of_mem_refs hiv hj
      have hjr : (U.block j).round + 1 = (U.block i).round :=
        U.round_of_mem_refs hiids hj
      rcases Nat.lt_or_ge G (U.block j).round with hlt | hge
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjv, hlt⟩)
      · exact Finset.mem_union_left _
          (accepted_mem_base hs hw hjv (by omega) hcar hpop hR hmt)
```

**G12, the assembly.** Base plus window is a bona-fide view of the truncation. Closure is the whole content: a window reference above the cut is in the window (stores are reference-closed), and a window reference *at* the cut is a round-`G` block the peer accepted — which is exactly what G11 puts in the base. The base layer itself has no references to chase: `chop` made it the genesis layer.

### Odontoceti

#### `Faults5`

*class, `Odontoceti.Rules.lean`*

```lean
class Faults5 (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    extends Faults Validator where
  /-- There are at least `5f+1` validators. -/
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator
```

The Odontoceti committee: `n ≥ 5f+1`. An extension of `Faults`, so every existing theorem applies to the same types unchanged; the new bound is consumed only where the two-round arithmetic needs it.

#### `DirectCommit`

*def, `Odontoceti.Rules.lean`*

```lean
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L (r + 1)).card
```

**Direct commit**: a quorum of distinct authors support `L` at its decision round.

#### `DirectSkip`

*def, `Odontoceti.Rules.lean`*

```lean
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card
```

**Direct skip**: a quorum of distinct authors blame `L` at its decision round.

#### `coneSupports`

*def, `Odontoceti.Rules.lean`*

```lean
def coneSupports (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    ((blocksAt U (r + 1)).filter
      (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A))
```

The authors of decision-round support blocks for `L` visible in `A`'s cone. Counted by **distinct authors**, not raw blocks: an equivocating supporter can plant any number of support-twins in a cone, so the block count is adversary-inflatable; the author count is the one the arithmetic on both sides actually bounds.

#### `ThickLink`

*def, `Odontoceti.Rules.lean`*

```lean
def ThickLink (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - 3 * F.f) ≤ (coneSupports U A L r).card
```

**The indirect test** (the thesis's ThickLink): at least `n − 3f` distinct authors of support blocks for `L` in the anchor's cone. At `n = 5f+1` this is the thesis's `2f+1`.

#### `decisionRound`

*def, `Odontoceti.Decision.lean`*

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1
```

The round at which a slot's verdict is settled: its supports live here. One round, not two — there is no certificate round.

#### `Eligible`

*def, `Odontoceti.Decision.lean`*

```lean
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j
```

`j` may anchor `k`: its proposal lies past `k`'s decision round. A predicate on the slot pair alone — which is what lets the agreement induction match two validators' premises against each other.

#### `supportersIn`

*def, `Odontoceti.Decision.lean`*

```lean
def supportersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun q => L ∈ (U.block q).refs)) ∩ V.ids)
```

The supporters a view actually holds.

#### `blamesIn`

*def, `Odontoceti.Decision.lean`*

```lean
def blamesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)
```

The blamers a view actually holds.

#### `DirectCommitIn`

*def, `Odontoceti.Decision.lean`*

```lean
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supportersIn U V L r).card
```

Direct commit, as judged from a single view.

#### `DirectSkipIn`

*def, `Odontoceti.Decision.lean`*

```lean
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamesIn U V L r).card
```

Direct skip, as judged from a single view.

#### `Decided`

*inductive, `Odontoceti.Decision.lean`*

```lean
inductive Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule blames every candidate — vacuously, when the
  leader produced nothing. -/
  | directSkip {k : ℕ} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  /-- Anchored on the nearest eligible committed slot, the least
  candidate passing the indirect test is committed. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) →
        ¬ L' < L) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate
  passes the indirect test. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ ThickLink U A L (S.slotRound k)) →
      Decided U V k none
```

`Decided U V k v` — a validator holding `V` has settled slot `k`.

Mirrors Mysticeti's relation: the anchor is the **nearest eligible** committed slot (the intermediate premise, stated positively), and the skip case quantifies over all candidate blocks. The one new element is the canonicity premise on `indirectCommit` — the committed candidate is the `≤`-least one passing the test at the anchor — which is the implementation's deterministic iteration order made explicit; see the module docstring for why agreement is unprovable without it.

#### `SpansEligible`

*def, `Odontoceti.Liveness.lean`*

```lean
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)
```

A run of `c` slots reaches past everything below it: the last slot of a run starting at `b` is an eligible anchor for every slot below `b`.

### The reactive schedule

#### `ReactivePace`

*structure, `Reactive.Basic.lean`*

```lean
structure ReactivePace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends PaceCore U T N where
  /-- Time advances with rounds — the only lower bound a reactive
  schedule keeps, over the rounds `v` reached. -/
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- **The reactive ceiling.** A validator never waits past the
  timeout; it may build any time before it. -/
  deadline : ∀ v ∈ T, ∀ n < top v, built v (n + 1) ≤ built v n + timeout n
  /-- **The leader wait.** At the round above a reliable leader, any
  `T`-authored block either votes (the reactive exit), or its builder
  waited the full timeout and votes for any leader block it holds (the
  fallback). -/
  vote_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 1 →
    L ∈ (U.block c).refs ∨
      (built v (S.slotRound k) + timeout (S.slotRound k)
          ≤ built v (S.slotRound k + 1) ∧
        (L ∈ holds v (built v (S.slotRound k + 1)) → L ∈ (U.block c).refs))
  /-- **The reactive exit is prompt.** Once a validator past its round
  entry holds the leader and every reliable round-`r` block, it builds
  within `proc`. Consumed only by the fast-path results. -/
  prompt_vote : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L → ∀ t, built v (S.slotRound k) ≤ t →
    L ∈ holds v t →
    (∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = S.slotRound k →
      b ∈ holds v t) →
    built v (S.slotRound k + 1) ≤ t + proc
```

The reactive schedule and network layer, shared by both protocols: `PaceCore` with the reactive discipline in place of the full-timeout one.

Relative to `ViewPace`, the floor `waits` is replaced by `deadline`, `built_lt`, `vote_or_wait` and `prompt_vote`, and the referencing clause is carried inside `vote_or_wait`'s fallback rather than stated globally — a reactive builder deliberately does *not* reference everything it holds. The processing bound `proc` is the trunk's: the same constant bounds catch-up entry and the reactive exit.

#### `ReactiveM`

*structure, `Reactive.Mysticeti.lean`*

```lean
structure ReactiveM (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ReactivePace U T N where
  /-- **The certificate wait.** At two rounds above a reliable leader,
  any `T`-authored block either already certifies (the reactive exit —
  its references carry a quorum of votes), or its builder waited the
  full timeout and references every reliable vote it holds (the
  fallback). -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 2 →
    Certifies U c L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1)
          ≤ built v (S.slotRound k + 2) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + 1 →
          b ∈ holds v (built v (S.slotRound k + 2)) →
          L ∈ (U.block b).refs → b ∈ (U.block c).refs)
```

The reactive three-round schedule: `ReactivePace`'s vote stage, plus the certificate wait, stated over any `T`-authored block.

### Safe Skip: crash recovery in one message

#### `SkipMsg`

*structure, `SafeSkip.Basic.lean`*

```lean
structure SkipMsg (U : BlockUniverse Validator BlockId Payload) where
  /-- The recovering validator. -/
  v1 : Validator
  /-- Its last block before the crash. -/
  B1 : BlockId
  /-- The donor of the reference structure. -/
  v2 : Validator
  /-- The target round — the round of the pinned block `B2 = line r`. -/
  r : ℕ
  /-- `v2`'s history line, meaningful on rounds `[round B1, r]`. -/
  line : ℕ → BlockId
  /-- Fresh ids for the filled blocks, and their decoder. -/
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  /-- `B1` is `v1`'s only block at its round — the whole of what the
  boundary argument needs. Stated directly rather than as `v1 ∈ Correct`
  because the two are not interchangeable in every fault model:
  non-equivocation gives it for a correct `v1` (`hB1uniq_of_correct`),
  and the hybrid model of report §14 gives it for a *crash-prone* one,
  which is the case Safe Skip exists to serve. -/
  hB1uniq : ∀ j ∈ U.ids, (U.block j).creator = v1 →
    (U.block j).round = (U.block B1).round → j = B1
  hv12 : v1 ≠ v2
  hB1 : B1 ∈ U.ids
  hB1c : (U.block B1).creator = v1
  hline_mem : ∀ k, (U.block B1).round ≤ k → k ≤ r → line k ∈ U.ids
  hline_creator : ∀ k, (U.block B1).round ≤ k → k ≤ r →
    (U.block (line k)).creator = v2
  hline_round : ∀ k, (U.block B1).round ≤ k → k ≤ r →
    (U.block (line k)).round = k
  hline_chain : ∀ k, (U.block B1).round < k → k ≤ r →
    line (k - 1) ∈ (U.block (line k)).refs
  hfresh_new : ∀ k, fresh k ∉ U.ids
  hidx : ∀ k, idx (fresh k) = k
  /-- The crash: `v1` authored nothing in the gap. -/
  hgap : ∀ b ∈ U.ids, (U.block b).creator = v1 →
    (U.block B1).round < (U.block b).round → (U.block b).round ≤ r → False
```

The denotation of a Safe Skip message, together with the freshness data an implementation supplies (new ids for the filled blocks and their decoder).

`line` is `v2`'s history line: one block per round from `r0 := round B1` up to `r`, each referencing the one below — the chain the message's `B2` pins by following self-parents. `hgap` is the crash itself: `v1` authored nothing strictly between `B1` and `r`.

#### `r0`

*def, `SafeSkip.Basic.lean`*

```lean
def r0 : ℕ := (U.block sk.B1).round
```

The round of the anchor block — the bottom of the gap.

#### `prev`

*def, `SafeSkip.Basic.lean`*

```lean
def prev (k : ℕ) : BlockId :=
  if k = sk.r0 + 1 then sk.B1 else sk.fresh (k - 1)
```

The self reference of the filled block at round `k`: the anchor at the boundary, the previous filled block above it.

#### `fillBlock`

*def, `SafeSkip.Basic.lean`*

```lean
def fillBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := insert (sk.prev k) (U.block (sk.line k)).refs
  payload := (U.block (sk.line k)).payload
```

The filled block at gap round `k`: `v2`'s references at that round, plus the added self reference.

#### `gap`

*def, `SafeSkip.Basic.lean`*

```lean
def gap : Finset ℕ := (Finset.range (sk.r + 1)).filter (fun k => sk.r0 < k)
```

The gap rounds, as a `Finset`.

#### `freshIds`

*def, `SafeSkip.Basic.lean`*

```lean
def freshIds : Finset BlockId := sk.gap.image sk.fresh
```

The ids of the filled blocks.

#### `skipFill`

*def, `SafeSkip.Basic.lean`*

```lean
def skipFill : BlockUniverse Validator BlockId Payload where
  ids := U.ids ∪ sk.freshIds
  block b := if b ∈ U.ids then U.block b else sk.fillBlock (sk.idx b)
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho] at hj
      exact Finset.mem_union_left _ (U.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hj
      simp only [fillBlock, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · -- the self reference: the anchor, or the previous filled block
        by_cases hb : k = sk.r0 + 1
        · simp only [prev, if_pos hb]
          exact Finset.mem_union_left _ sk.hB1
        · simp only [prev, if_neg hb]
          refine Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k - 1, ?_, ?_, rfl⟩)
          · omega
          · omega
      · -- a copied reference: old, by completeness of `U` at the line
        exact Finset.mem_union_left _
          (U.complete _ (sk.hline_mem k (by omega) hk2) j hj)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · -- old blocks: `U`'s validity, reference lookups unchanged
      rw [if_pos ho]
      have hv := U.valid i ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (U.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro j hj l hl
        rw [if_pos (U.complete i ho j hj), if_pos (U.complete i ho l hl)]
        exact hv.distinct_creators j hj l hl
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete i ho j hj)]
        exact hjc
      · intro hr
        obtain ⟨j, hj, hjc⟩ := hv.self_parent hr
        exact ⟨j, hj, by rw [if_pos (U.complete i ho j hj)]; exact hjc⟩
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx]
      have hlm := sk.hline_mem k (by omega) hk2
      have hlv := U.valid _ hlm
      have hlr := sk.hline_round k (by omega) hk2
      -- the self reference is an old id at round `k − 1` with creator `v1`
      have hprev_old : sk.prev k ∈ U.ids ∨ sk.prev k = sk.fresh (k - 1) := by
        by_cases hb : k = sk.r0 + 1
        · exact Or.inl (by simp only [prev, if_pos hb]; exact sk.hB1)
        · exact Or.inr (by simp only [prev, if_neg hb])
      have hprev_round : (if sk.prev k ∈ U.ids then U.block (sk.prev k)
          else sk.fillBlock (sk.idx (sk.prev k))).round = k - 1 := by
        by_cases hb : k = sk.r0 + 1
        · simp only [prev, if_pos hb, if_pos sk.hB1]
          show (U.block sk.B1).round = k - 1
          omega
        · simp only [prev, if_neg hb, if_neg (sk.hfresh_new (k - 1)), sk.hidx]
          rfl
      have hprev_creator : (if sk.prev k ∈ U.ids then U.block (sk.prev k)
          else sk.fillBlock (sk.idx (sk.prev k))).creator = sk.v1 := by
        by_cases hb : k = sk.r0 + 1
        · simp only [prev, if_pos hb, if_pos sk.hB1]
          exact sk.hB1c
        · simp only [prev, if_neg hb, if_neg (sk.hfresh_new (k - 1)), sk.hidx]
          rfl
      -- no copied reference is `v1`-authored, except possibly the anchor itself
      have hno_v1 : ∀ j ∈ (U.block (sk.line k)).refs,
          (U.block j).creator = sk.v1 → j = sk.prev k := by
        intro j hj hjc
        have hjo := U.complete _ hlm j hj
        have hjr : (U.block j).round = k - 1 := by
          have := hlv.predecessor j hj
          omega
        by_cases hb : k = sk.r0 + 1
        · -- boundary: non-equivocation pins it to the anchor
          simp only [prev, if_pos hb]
          exact sk.hB1uniq j hjo hjc (by omega)
        · -- inside the gap: the crash forbids it
          exact (sk.hgap j hjo hjc (by omega) (by omega)).elim
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- P1: the self reference and every copied reference sit at `k − 1`
        intro j hj
        simp only [fillBlock, Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · rw [hprev_round]; show k - 1 + 1 = k; omega
        · rw [if_pos (U.complete _ hlm j hj)]
          have := hlv.predecessor j hj
          show (U.block j).round + 1 = k
          omega
      · -- P2: copied references are distinct by the line's P2; the self
        -- reference's author appears nowhere else
        intro j hj l hl hjl
        simp only [fillBlock, Finset.mem_insert] at hj hl
        rcases hj with rfl | hj <;> rcases hl with rfl | hl
        · rfl
        · rw [hprev_creator] at hjl
          rw [if_pos (U.complete _ hlm l hl)] at hjl
          exact (hno_v1 l hl hjl.symm).symm
        · rw [hprev_creator] at hjl
          rw [if_pos (U.complete _ hlm j hj)] at hjl
          exact hno_v1 j hj hjl
        · rw [if_pos (U.complete _ hlm j hj), if_pos (U.complete _ hlm l hl)] at hjl
          exact hlv.distinct_creators j hj l hl hjl
      · -- P3: the copied quorum survives, since lookups of old ids agree
        intro _
        have hq := hlv.quorum (by show 0 < (U.block (sk.line k)).round; omega)
        refine le_trans hq ?_
        refine Finset.card_le_card ?_
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · simp only [fillBlock, Finset.mem_insert]
          exact Or.inr hj
        · simp only
          rw [if_pos (U.complete _ hlm j hj)]
          exact hjc
      · -- P3′: the added self reference
        intro _
        exact ⟨sk.prev k, Finset.mem_insert_self _ _, hprev_creator⟩
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rcases Finset.mem_union.mp hi with ho | hf <;>
      rcases Finset.mem_union.mp hj with ho' | hf'
    · rw [if_pos ho] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact U.no_equivocation i ho j ho' hic hcc hrr
    · -- an old block equal in author and round to a filled one: the
      -- author is `v1`, and the crash forbids it
      obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_pos ho] at hic hcc hrr
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      exact (sk.hgap i ho hcc
        (by simp only [fillBlock] at hrr; omega)
        (by simp only [fillBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact (sk.hgap j ho' hcc.symm
        (by simp only [fillBlock] at hrr; omega)
        (by simp only [fillBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hrr
      rw [if_neg (sk.hfresh_new l), sk.hidx] at hrr
      simp only [fillBlock] at hrr
      exact hrr ▸ rfl
```

**The denotation.** `U`, extended with one filled block per gap round; every old block looked up unchanged.

#### `liftView`

*def, `SafeSkip.Invariance.lean`*

```lean
def liftView (V : View Validator BlockId Payload U) :
    View Validator BlockId Payload sk.skipFill where
  ids := V.ids
  subset_ids := V.subset_ids.trans sk.ids_subset_skipFill
  complete := by
    intro i hi j hj
    rw [sk.skipFill_block_old (V.subset_ids hi)] at hj
    exact V.complete i hi j hj
```

A view of `U` is a view of the extension, unchanged: its blocks are old, and old references are preserved.

#### `QuorateOverGap`

*def, `SafeSkip.Invariance.lean`*

```lean
def QuorateOverGap (V : View Validator BlockId Payload U) : Prop :=
  ∀ n, sk.r0 < n → n ≤ sk.r →
    quorumCard Validator ≤
      (creatorsOf U.block ((blocksAt U (n + 1)) ∩ V.ids)).card
```

**The view is quorate over the gap**: at every gap round it holds blocks from a quorum of distinct authors at the round above. This is the condition the agreement result below consumes --- the recovering validator may be counted on only where the pre-crash view could already have decided.

#### `selfParent`

*def, `SafeSkip.Jump.lean`*

```lean
noncomputable def selfParent (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) : BlockId :=
  if h : ∃ i ∈ (U.block b).refs, (U.block i).creator = (U.block b).creator then
    h.choose
  else b
```

The self-parent of a block: its unique reference by its own creator. Total, with the block itself as junk value when no such reference exists (a genesis block, or an identifier outside the universe); every lemma below assumes the good case.

#### `lineOf`

*def, `SafeSkip.Jump.lean`*

```lean
noncomputable def lineOf (U : BlockUniverse Validator BlockId Payload)
    (B2 : BlockId) (k : ℕ) : BlockId :=
  (selfParent U)^[(U.block B2).round - k] B2
```

The self-parent chain below `B2`, indexed by round: `lineOf U B2 k` is the ancestor of `B2` at round `k` on its self-parent line. Junk above `B2`'s round or off a valid chain, as usual.

#### `JumpMsg`

*structure, `SafeSkip.Jump.lean`*

```lean
structure JumpMsg (U : BlockUniverse Validator BlockId Payload) where
  /-- The recovering validator. -/
  v1 : Validator
  /-- Its last block before the crash — the anchor. -/
  B1 : BlockId
  /-- The donor of the reference structure. -/
  v2 : Validator
  /-- The pinned target block on the donor's line. -/
  B2 : BlockId
  /-- Fresh ids for the filled blocks, and their decoder. -/
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  /-- The anchor is `v1`'s only block at its round (see
  `SkipMsg.hB1uniq` for why this is a field rather than derived from
  correctness). -/
  hB1uniq : ∀ j ∈ U.ids, (U.block j).creator = v1 →
    (U.block j).round = (U.block B1).round → j = B1
  hv12 : v1 ≠ v2
  hB1 : B1 ∈ U.ids
  hB1c : (U.block B1).creator = v1
  hB2 : B2 ∈ U.ids
  hB2c : (U.block B2).creator = v2
  hB2r : (U.block B1).round ≤ (U.block B2).round
  hfresh_new : ∀ k, fresh k ∉ U.ids
  hidx : ∀ k, idx (fresh k) = k
  /-- The crash: `v1` authored nothing in the gap. -/
  hgap : ∀ b ∈ U.ids, (U.block b).creator = v1 →
    (U.block B1).round < (U.block b).round →
    (U.block b).round ≤ (U.block B2).round → False
```

**The jump message**: the compact core a recovering validator actually sends — its own name and anchor, the target block and its author — together with the fresh-identifier supply and the semantic clauses a `SkipMsg` carries about them. No line: the line is derived.

`hB2r` places the target at or above the anchor; the gap may be empty, in which case the denotation is `U` plus nothing.

#### `toSkipMsg`

*def, `SafeSkip.Jump.lean`*

```lean
noncomputable def toSkipMsg : SkipMsg U where
  v1 := j.v1
  B1 := j.B1
  v2 := j.v2
  r := (U.block j.B2).round
  line := lineOf U j.B2
  fresh := j.fresh
  idx := j.idx
  hB1uniq := j.hB1uniq
  hv12 := j.hv12
  hB1 := j.hB1
  hB1c := j.hB1c
  hline_mem := fun _ _ hk2 => lineOf_mem j.hB2 hk2
  hline_creator := fun _ _ hk2 => (lineOf_creator j.hB2 hk2).trans j.hB2c
  hline_round := fun _ _ hk2 => lineOf_round j.hB2 hk2
  hline_chain := fun _ hk1 hk2 =>
    lineOf_chain j.hB2 hk2 (by omega)
  hfresh_new := j.hfresh_new
  hidx := j.hidx
  hgap := j.hgap
```

**The elaboration.** The `SkipMsg` a jump message denotes: target round the target's round, line the derived chain. Every line clause is discharged by the `lineOf` lemmas — the receiver holds no data the sender chose.

#### `denote`

*def, `SafeSkip.Jump.lean`*

```lean
noncomputable def denote [DecidableEq BlockId] : BlockUniverse Validator BlockId Payload :=
  j.toSkipMsg.skipFill
```

**The round jump.** The universe in which the sender produces at the round above the target: the fill, elaborated from the compact message. Being a `skipFill`, everything proved of the fill — SS1 through SS6 — applies to it verbatim.

### Integration: composing the arcs

#### `HorizonStable`

*def, `Integration.Joiner.lean`*

```lean
def HorizonStable (P : AdaptivePolicy Validator BlockId Payload) (d G : ℕ)
    (pick' : BlockUniverse Validator BlockId Payload →
      (ℕ → Option BlockId) → ℕ → Validator) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (v : ℕ → Option BlockId)
    (k : ℕ), pick' (chop U G) (fun m => v (d + m)) k = P.pick U v (d + k)
```

**Horizon-stability.** The joiner's rule, run on the truncation with the joiner's own slot indices, returns what the network's policy returns on the full history at the corresponding slot.

Read as a deployment obligation: *a validator that pruned below `G` and re-indexed from `d` must still compute the leaders everyone else is using.* A policy that reads arbitrarily far back into committed history cannot satisfy this, which is the substantive content — such a policy is incompatible with garbage collection, and saying so precisely is the point of I9.

#### `chopMsg`

*def, `Integration.Retention.lean`*

```lean
def chopMsg (sk : SkipMsg U) (hG : G ≤ (U.block sk.B1).round)
    (hGr : G ≤ sk.r) : SkipMsg (chop U G) where
  v1 := sk.v1
  B1 := sk.B1
  v2 := sk.v2
  r := sk.r - G
  line k := sk.line (G + k)
  fresh k := sk.fresh (G + k)
  idx b := sk.idx b - G
  hB1uniq := by
    intro j hj hjc hjr
    rw [mem_chop_ids] at hj
    simp only [chop_block_eq, chopBlock_creator] at hjc
    simp only [chop_block_eq, chopBlock_round] at hjr
    exact sk.hB1uniq j hj.1 hjc (by omega)
  hv12 := sk.hv12
  hB1 := mem_chop_ids.mpr ⟨sk.hB1, hG⟩
  hB1c := by simp only [chop_block_eq, chopBlock_creator]; exact sk.hB1c
  hline_mem := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1
    have hlm := sk.hline_mem (G + k) (by omega) (by omega)
    have hlr := sk.hline_round (G + k) (by omega) (by omega)
    exact mem_chop_ids.mpr ⟨hlm, by omega⟩
  hline_creator := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1
    simp only [chop_block_eq, chopBlock_creator]
    exact sk.hline_creator (G + k) (by omega) (by omega)
  hline_round := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1 ⊢
    rw [sk.hline_round (G + k) (by omega) (by omega)]
    omega
  hline_chain := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1
    -- the line block sits strictly above the cut, so its references survive
    have hlm := sk.hline_mem (G + k) (by omega) (by omega)
    have hlr := sk.hline_round (G + k) (by omega) (by omega)
    have hgt : G < (U.block (sk.line (G + k))).round := by omega
    rw [chop_block_eq, chopBlock_refs_of_lt hgt]
    have := sk.hline_chain (G + k) (by omega) (by omega)
    have hidx : G + k - 1 = G + (k - 1) := by omega
    rwa [hidx] at this
  hfresh_new := by
    intro k
    rw [mem_chop_ids]
    intro h
    exact sk.hfresh_new (G + k) h.1
  hidx := by
    intro k
    rw [sk.hidx (G + k)]
    omega
  hgap := by
    intro b hb hbc hb1 hb2
    rw [mem_chop_ids] at hb
    simp only [chop_block_eq, chopBlock_creator] at hbc
    simp only [chop_block_eq, chopBlock_round] at hb1 hb2
    exact sk.hgap b hb.1 hbc (by omega) (by omega)
```

**I7b.** With the anchor retained, a Safe Skip message over the original universe induces one over the truncation: same validators, same anchor, every round rebased by `−G`. A validator that pruned can still rejoin with one message.

#### `addGenesis`

*def, `Integration.ReGenesis.lean`*

```lean
def addGenesis (V : BlockUniverse Validator BlockId Payload) (v : Validator)
    (g : BlockId) (p : Payload) (hg : g ∉ V.ids)
    (hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v) :
    BlockUniverse Validator BlockId Payload where
  ids := insert g V.ids
  block b := if b ∈ V.ids then V.block b else ⟨0, v, ∅, p⟩
  complete := by
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with rfl | ho
    · -- the new block references nothing
      rw [if_neg hg] at hj
      exact absurd hj (Finset.notMem_empty j)
    · rw [if_pos ho] at hj
      exact Finset.mem_insert_of_mem (V.complete i ho j hj)
  valid := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | ho
    · -- round `0` with no references: every clause is vacuous
      rw [if_neg hg]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro j hj; exact absurd hj (Finset.notMem_empty j))
          | (intro hr; exact absurd hr (by simp))
    · rw [if_pos ho]
      have hv := V.valid i ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (V.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro a ha b hb hab
        rw [if_pos (V.complete i ho a ha), if_pos (V.complete i ho b hb)] at hab
        exact hv.distinct_creators a ha b hb hab
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (V.complete i ho j hj)]
        exact hjc
      · intro hr
        obtain ⟨j, hj, hjc⟩ := hv.self_parent hr
        exact ⟨j, hj, by rw [if_pos (V.complete i ho j hj)]; exact hjc⟩
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rcases Finset.mem_insert.mp hi with rfl | ho <;>
      rcases Finset.mem_insert.mp hj with rfl | ho'
    · rfl
    · -- the new block against an old one: the old author cannot be `v`
      rw [if_neg hg] at hcc
      rw [if_pos ho'] at hcc
      exact absurd hcc.symm (hsev j ho')
    · rw [if_pos ho] at hcc
      rw [if_neg hg] at hcc
      exact absurd hcc (hsev i ho)
    · rw [if_pos ho] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact V.no_equivocation i ho j ho' hic hcc hrr
```

**Re-genesis.** A universe extended with one reference-free block at round `0`, for a validator that has none.

The hypotheses are exactly what the construction needs and no more: the identifier must be fresh, and the validator must be absent — which for a stranded validator is `severed_of_pruned_anchor`.

#### `addGenesis_of_severed`

*def, `Integration.ReGenesis.lean`*

```lean
def addGenesis_of_severed {U : BlockUniverse Validator BlockId Payload}
    {G : ℕ} (sk : SkipMsg U) (hG1 : sk.r0 < G) (hG2 : G ≤ sk.r)
    (g : BlockId) (p : Payload) (hg : g ∉ (chop U G).ids) :
    BlockUniverse Validator BlockId Payload :=
  addGenesis (chop U G) sk.v1 g p hg (severed_of_pruned_anchor sk hG1 hG2)
```

Re-genesis is available exactly to a stranded validator: the absence hypothesis it needs is what `severed_of_pruned_anchor` supplies. The composite says a validator pruned past its own history can restart at the cut — the provision report §12 lacks.

#### `recoveryMsg`

*def, `Integration.ReGenesis.lean`*

```lean
def recoveryMsg (r : ℕ) (line fresh : ℕ → BlockId) (idx : BlockId → ℕ)
    (v2 : Validator) (hv12 : v ≠ v2)
    (hline_mem : ∀ k, k ≤ r → line k ∈ V.ids)
    (hline_creator : ∀ k, k ≤ r → (V.block (line k)).creator = v2)
    (hline_round : ∀ k, k ≤ r →
      (V.block (line k)).round = ((addGenesis V v g p hg hsev).block g).round + k)
    (hline_chain : ∀ k, 0 < k → k ≤ r → line (k - 1) ∈ (V.block (line k)).refs)
    (hfresh_new : ∀ k, fresh k ∉ (addGenesis V v g p hg hsev).ids)
    (hidx : ∀ k, idx (fresh k) = k) :
    SkipMsg (addGenesis V v g p hg hsev) where
  v1 := v
  B1 := g
  v2 := v2
  r := ((addGenesis V v g p hg hsev).block g).round + r
  line k := line (k - ((addGenesis V v g p hg hsev).block g).round)
  fresh := fresh
  idx := idx
  hB1uniq := hB1uniq_of_addGenesis
  hv12 := hv12
  hB1 := mem_addGenesis
  hB1c := by rw [addGenesis_block_new]
  hline_mem := by
    intro k hk1 hk2
    exact Finset.mem_insert_of_mem (hline_mem _ (by omega))
  hline_creator := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    exact hline_creator _ (by omega)
  hline_round := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    rw [hline_round _ (by omega)]
    omega
  hline_chain := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    have := hline_chain (k - ((addGenesis V v g p hg hsev).block g).round)
      (by omega) (by omega)
    have hidx' : k - ((addGenesis V v g p hg hsev).block g).round - 1
        = k - 1 - ((addGenesis V v g p hg hsev).block g).round := by omega
    rwa [hidx'] at this
  hfresh_new := hfresh_new
  hidx := hidx
  hgap := by
    intro b hb hbc _ _
    rcases Finset.mem_insert.mp hb with rfl | ho
    · rw [addGenesis_block_new] at *
      omega
    · rw [addGenesis_block_old ho] at hbc
      exact absurd hbc (hsev b ho)
```

**The catch-up fill.** After re-genesis the returning validator rejoins production with one message: a `SkipMsg` anchored on its new genesis block, filling every round from the cut to the target.

The donor data is the ordinary requirement — a line of `v2` blocks from the anchor's round to the target, each citing the one below, all of them in the retained window that every validator holds. The two clauses peculiar to recovery come at no cost: `hB1uniq` from `hB1uniq_of_addGenesis`, and `hgap` from the absence itself, since a validator with no blocks authored none during the gap either.

#### `stack`

*abbrev, `Integration.Stack.lean`*

```lean
abbrev stack (sk : SkipMsg U) (G : ℕ) : BlockUniverse Validator BlockId Payload :=
  chop sk.skipFill G
```

**The stacked universe**: filled, then truncated.

#### `skipFillD`

*def, `Integration.DeliveryFill.lean`*

```lean
def skipFillD (sk : SkipMsg U) (D : Delivery U)
    (hdown : ∀ m, sk.r0 ≤ m → m < sk.r → D.accepted sk.v1 m = ∅) :
    Delivery sk.skipFill where
  held := D.held
  held_spec := by
    intro v n i hi
    obtain ⟨h1, h2⟩ := D.held_spec v n i hi
    exact ⟨sk.ids_subset_skipFill h1, by rw [sk.skipFill_block_old h1]; exact h2⟩
  accepted := D.accepted
  accepted_sub := D.accepted_sub
  accepted_inj := by
    intro v n i hi j hj hij
    have hio := (D.held_spec v n i (D.accepted_sub v n hi)).1
    have hjo := (D.held_spec v n j (D.accepted_sub v n hj)).1
    rw [sk.skipFill_block_old hio, sk.skipFill_block_old hjo] at hij
    exact D.accepted_inj v n i hi j hj hij
  accepts_correct := by
    intro v hv n a ha hac
    have hao := (D.held_spec v n a ha).1
    rw [sk.skipFill_block_old hao] at hac
    exact D.accepts_correct v hv n a ha hac
  includes := by
    intro v hv n b hb hbc hbr
    rcases Finset.mem_union.mp hb with ho | hf
    · -- an old block references what it accepted, as before
      rw [sk.skipFill_block_old ho] at hbc hbr ⊢
      exact D.includes v hv n b ho hbc hbr
    · -- a filled block: the recovering validator accepted nothing
      obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [sk.skipFill_block_fresh] at hbc hbr
      simp only [SkipMsg.fillBlock] at hbc hbr
      subst hbc
      rw [hdown n (by omega) (by omega)]
      exact Finset.empty_subset _
```

**I15a — the delivery transformer.** The fill's delivery structure is the original's: the recovering validator's blocks were never delivered to anyone, being reconstructed after the fact.

`hdown` is the hypothesis `Delivery.includes` forces — the recovering validator accepted nothing while it was down. It is the acceptance-side counterpart of `hgap`, which says the same of production.

#### `CommonAt`

*def, `Integration.CommonTarget.lean`*

```lean
def CommonAt (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) (r : ℕ) : Prop :=
  b ∈ U.ids ∧ (U.block b).round = r ∧
    ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c b
```

A block is **common at round `r`** when every block two rounds above it reaches it. Report §5.2's T3c supplies one at every round, of correct authorship, with no assumption whatever.

### Hybrid fault tolerance: Byzantine and crash faults apart

#### `HybridFaults`

*class, `Hybrid.Faults.lean`*

```lean
class HybridFaults (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] where
  /-- The Byzantine bound. -/
  fb : ℕ
  /-- The crash bound. -/
  fc : ℕ
  /-- The Byzantine validators: may equivocate. -/
  byzantine : Finset Validator
  /-- The crash-prone validators: honest, may halt. -/
  crash : Finset Validator
  disjoint : Disjoint byzantine crash
  card_byzantine : byzantine.card ≤ fb
  card_crash : crash.card ≤ fc
  /-- The base bound — what the *derived instance* needs. The hybrid
  committee bound `n ≥ 5·fb + 3·fc + 1` deliberately does **not** live
  here: every safety theorem consumes it through the admissible
  interval, whose nonemptiness implies it — and keeping the class at
  the base bound is what lets the one-short committee `n = 5·fb + 3·fc`
  be *expressed*, so that the tightness counterexample (H10) is a
  theorem rather than an unstatable aside. -/
  card_validators : 3 * (fb + fc) + 1 ≤ Fintype.card Validator
```

The hybrid fault model: at most `fb` Byzantine, at most `fc` crash-prone. The committee bound `n ≥ 5·fb + 3·fc + 1` enters through the admissible threshold interval, not here — see `card_validators`.

#### `Honest`

*def, `Hybrid.Faults.lean`*

```lean
def Honest : Finset Validator := (H.byzantine)ᶜ
```

The honest validators: everyone outside the Byzantine set. A crash-prone validator is honest — its blocks are consistent; only its availability is in doubt.

#### `HonestNoEquiv`

*def, `Hybrid.Faults.lean`*

```lean
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator ∉ H.byzantine →
    (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j
```

**The strengthened equivocation clause.** Non-equivocation over `Honest` rather than the derived instance's `Correct`: a crash-prone validator authors at most one block per round too. This is P5's shape at the larger class — the base clause follows from it — and it is the one genuinely new assumption of the hybrid model, threaded through the safety theorems as a hypothesis the way `DoSValid` is.

#### `q`

*def, `Hybrid.Rules.lean`*

```lean
def q : ℕ := Fintype.card Validator - (H.fb + H.fc)
```

The hybrid quorum `q = n − fb − fc` — the derived instance's `n − F.f`, spelled out.

#### `kTight`

*def, `Hybrid.Rules.lean`*

```lean
def kTight : ℕ := 2 * H.fb + H.fc + 1
```

`hybrid.md`'s tight indirect threshold.

#### `kRel`

*def, `Hybrid.Rules.lean`*

```lean
def kRel : ℕ := Fintype.card Validator - (3 * H.fb + 2 * H.fc)
```

The `n`-relative indirect threshold, mirroring the house generalization of `2f + 1` to `n − 3f`; equal to `kTight` at the tight committee.

#### `Admissible`

*def, `Hybrid.Rules.lean`*

```lean
def Admissible (k : ℕ) : Prop :=
  2 * H.fb + H.fc + 1 ≤ k ∧ k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator
```

**The admissible interval.** The two inequalities the rule theorems consume; nonempty exactly when `n ≥ 5·fb + 3·fc + 1`.

#### `DirectCommit`

*def, `Hybrid.Rules.lean`*

```lean
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (supporters U L (r + 1)).card
```

**Direct commit**: `q` distinct authors support `L` at its decision round.

#### `DirectSkip`

*def, `Hybrid.Rules.lean`*

```lean
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (blames U L (r + 1)).card
```

**Direct skip**: `q` distinct authors blame `L` at its decision round.

#### `coneSupports`

*def, `Hybrid.Rules.lean`*

```lean
def coneSupports (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    ((blocksAt U (r + 1)).filter
      (fun p => L ∈ (U.block p).refs ∧ p ∈ history U A))
```

The authors of decision-round support blocks for `L` visible in `A`'s cone — by distinct authors, the count equivocation cannot inflate.

#### `ThickLink`

*def, `Hybrid.Rules.lean`*

```lean
def ThickLink (k : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Prop :=
  k ≤ (coneSupports U A L r).card
```

**The indirect test** at threshold `k`: at least `k` distinct authors of support blocks in the anchor's cone.

#### `decisionRound`

*def, `Hybrid.Decision.lean`*

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1
```

The round at which a slot's verdict is settled: its supports live here. One round — there is no certificate round.

#### `Eligible`

*def, `Hybrid.Decision.lean`*

```lean
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j
```

`j` may anchor `k`: its proposal lies past `k`'s decision round.

#### `supportersIn`

*def, `Hybrid.Decision.lean`*

```lean
def supportersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun p => L ∈ (U.block p).refs)) ∩ V.ids)
```

The supporters a view actually holds.

#### `blamesIn`

*def, `Hybrid.Decision.lean`*

```lean
def blamesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun p => L ∉ (U.block p).refs)) ∩ V.ids)
```

The blamers a view actually holds.

#### `DirectCommitIn`

*def, `Hybrid.Decision.lean`*

```lean
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (supportersIn U V L r).card
```

Direct commit, as judged from a single view.

#### `DirectSkipIn`

*def, `Hybrid.Decision.lean`*

```lean
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (blamesIn U V L r).card
```

Direct skip, as judged from a single view.

#### `Decided`

*inductive, `Hybrid.Decision.lean`*

```lean
inductive Decided (k : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {s : ℕ} {L : BlockId} :
      IsLeaderBlock U s L → DirectCommitIn U V L (S.slotRound s) →
      Decided k U V s (some L)
  /-- The direct rule blames every candidate — vacuously, when the
  leader produced nothing. -/
  | directSkip {s : ℕ} :
      (∀ L, IsLeaderBlock U s L → DirectSkipIn U V L (S.slotRound s)) →
      Decided k U V s none
  /-- Anchored on the nearest eligible committed slot, the least
  candidate passing the indirect test is committed. -/
  | indirectCommit {s j : ℕ} {A L : BlockId} :
      s < j → Eligible Validator s j → Decided k U V j (some A) →
      (∀ i, s < i → i < j → Eligible Validator s i → Decided k U V i none) →
      IsLeaderBlock U s L → ThickLink k U A L (S.slotRound s) →
      (∀ L', IsLeaderBlock U s L' → ThickLink k U A L' (S.slotRound s) →
        ¬ L' < L) →
      Decided k U V s (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate
  passes the indirect test. -/
  | indirectSkip {s j : ℕ} {A : BlockId} :
      s < j → Eligible Validator s j → Decided k U V j (some A) →
      (∀ i, s < i → i < j → Eligible Validator s i → Decided k U V i none) →
      (∀ L, IsLeaderBlock U s L → ¬ ThickLink k U A L (S.slotRound s)) →
      Decided k U V s none
```

`Decided k U V s v` — a validator holding `V` has settled slot `s`, at indirect threshold `k`. Mirrors the Odontoceti relation, canonicity clause included: a Byzantine leader can still plant two passing candidates in one anchor's cone, and the crash class does not close the gap, so the committed candidate is the `≤`-least passing one.

#### `SpansEligible`

*def, `Hybrid.Liveness.lean`*

```lean
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)
```

A run of `c` slots reaches past everything below it.

#### `_root_.LeanDag.Faults5.toHybrid`

*def, `Hybrid.Conservativity.lean`*

```lean
def _root_.LeanDag.Faults5.toHybrid [F : Faults5 Validator] :
    HybridFaults Validator where
  fb := F.f
  fc := 0
  byzantine := F.byzantine
  crash := ∅
  disjoint := Finset.disjoint_empty_right _
  card_byzantine := F.card_byzantine
  card_crash := le_refl 0
  card_validators := by have := F.card_validators5; omega
```

**Every pure-Byzantine committee is a crash-free hybrid committee.** The generalization direction of H8.

### Adaptive leaders: the schedule as a fixpoint

#### `epochOf`

*def, `Adaptive.Basic.lean`*

```lean
def epochOf (W k : ℕ) : ℕ := k / W
```

The epoch of slot `k` at width `W`: epoch `e` is slots `[W·e, W·(e+1))`.

#### `slotsOf`

*def, `Adaptive.Basic.lean`*

```lean
@[reducible] def slotsOf (hinj : Function.Injective S.slotRound) (a : ℕ → Validator) :
    Slots Validator where
  slotRound := S.slotRound
  leader := a
  mono := S.mono
  unbounded := S.unbounded
  keyed := fun _ _ h => hinj (congrArg Prod.fst h)
```

The `Slots` instance a leader assignment induces: the base round structure, the given leaders. `keyed` is where one-leader-per-round enters: with `slotRound` injective, distinct slots differ in round whatever the assignment names.

#### `DecidedWithin`

*inductive, `Adaptive.Basic.lean`*

```lean
inductive DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      k < B → IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- The direct rule blames every candidate. -/
  | directSkip {k : ℕ} :
      k < B → (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      DecidedWithin U V B k none
  /-- Anchored on the nearest eligible committed slot below the bound. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- Anchored likewise, no candidate is in reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      DecidedWithin U V B k none
```

**The bounded decision relation.** `Decided`, with every slot the derivation mentions — the decided slot, the anchor, the eligible intermediates — strictly below `B`.

The bound lives in the relation because it cannot live anywhere else: a `Decided` derivation is a proof of a `Prop` and its anchors cannot be recovered from it. The adaptive fixpoint is stratified by exactly this bound — epoch `e`'s verdicts are `DecidedWithin` the start of epoch `e + 2`, which consults leaders the schedule has already determined.

#### `AdaptivePolicy`

*structure, `Adaptive.Policy.lean`*

```lean
structure AdaptivePolicy (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] (BlockId : Type*)
    [DecidableEq BlockId] (Payload : Type*) [S : Slots Validator] where
  /-- The epoch length, in slots. -/
  W : ℕ
  W_pos : 0 < W
  /-- One leader per round, for the whole arc. -/
  inj : Function.Injective S.slotRound
  /-- The reassignment rule: from the universe and a verdict function,
  the leader of each slot. -/
  pick : BlockUniverse Validator BlockId Payload →
    (ℕ → Option BlockId) → ℕ → Validator
  /-- **Adaptedness.** The leader of slot `k` reads the verdicts of
  epochs `≤ epochOf k − 2` and nothing else. -/
  adapted : ∀ U v w k,
    (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
    pick U v k = pick U w k
  /-- Epochs `0` and `1` run the base schedule. -/
  base_prefix : ∀ U v k, epochOf W k < 2 → pick U v k = S.leader k
```

A Hammerhead-style reassignment policy: epoch length, the rule, and the clauses it owes. Fairness — the clause liveness will price — is deliberately *not* here: safety must hold for arbitrary, even adversarial, adapted policies, and stating fairness where liveness consumes it keeps that separation visible.

#### `const`

*def, `Adaptive.Policy.lean`*

```lean
def const (W : ℕ) (hW : 0 < W) (hinj : Function.Injective S.slotRound) :
    AdaptivePolicy Validator BlockId Payload where
  W := W
  W_pos := hW
  inj := hinj
  pick _ _ k := S.leader k
  adapted _ _ _ _ _ := rfl
  base_prefix _ _ _ _ := rfl
```

The constant policy: reassign nothing. The conservativity anchor — under it the adaptive development must collapse onto the base one.

#### `PartialRun`

*structure, `Adaptive.Run.lean`*

```lean
structure PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot of a closed epoch is decided inside its window: anchors
  strictly below the start of epoch `e + 2`. -/
  closed : ∀ k, epochOf P.W k < E →
    DecidedWithin (S := slotsOf P.inj assign) U V
      (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, as far as the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U vdct m
```

A run closed up to epoch height `E`: verdicts derived for every slot of epochs `< E`, the schedule coherent as far as those derivations read it (epochs `< E + 1`). What a validator holds mid-execution.

#### `AdaptiveRun`

*structure, `Adaptive.Run.lean`*

```lean
structure AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, DecidedWithin (S := slotsOf P.inj assign) U V
    (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, everywhere. -/
  coherent : ∀ m, assign m = P.pick U vdct m
```

A total run: the adaptive fixpoint itself.

#### `AdaptiveRun.toPartial`

*def, `Adaptive.Run.lean`*

```lean
def AdaptiveRun.toPartial {P : AdaptivePolicy Validator BlockId Payload}
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V) (E : ℕ) :
    PartialRun P U V E where
  assign := R.assign
  vdct := R.vdct
  closed := fun k _ => R.closed k
  coherent := fun m _ => R.coherent m
```

A total run is partial at every height.

#### `PlacesRuns`

*def, `Adaptive.Liveness.lean`*

```lean
def PlacesRuns (P : AdaptivePolicy Validator BlockId Payload)
    (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (v : ℕ → Option BlockId)
    (e : ℕ), ∃ b, P.W * (e + 1) ≤ b ∧ b + c ≤ P.W * (e + 2) ∧
      ∀ i, i < c → P.pick U v (b + i) ∈ T
```

**The adaptive fairness clause.** Every assignment the policy can emit places, in each epoch past the base prefix, a run of `c` consecutive `T`-led slots. The clause liveness prices and safety never sees: `adaptiveRun_agree` holds for policies that violate it.

#### `DecidedWithin`

*inductive, `Adaptive.Odontoceti.lean`*

```lean
inductive DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      k < B → IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- The direct rule blames every candidate. -/
  | directSkip {k : ℕ} :
      k < B → (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      DecidedWithin U V B k none
  /-- Anchored below the bound, the least candidate passing the indirect
  test is committed. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) →
        ¬ L' < L) →
      DecidedWithin U V B k (some L)
  /-- Anchored below the bound, no candidate passes. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      (∀ L, IsLeaderBlock U k L → ¬ ThickLink U A L (S.slotRound k)) →
      DecidedWithin U V B k none
```

The bounded two-round decision relation: `Odontoceti.Decided` with every slot mentioned strictly below `B`, canonicity clause included.

#### `PartialRun`

*structure, `Adaptive.Odontoceti.lean`*

```lean
structure PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot of a closed epoch is decided inside its window. -/
  closed : ∀ k, epochOf P.W k < E →
    DecidedWithin (S := slotsOf P.inj assign) U V
      (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, as far as the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U vdct m
```

A run closed up to epoch height `E`, two-round rule.

#### `AdaptiveRun`

*structure, `Adaptive.Odontoceti.lean`*

```lean
structure AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, DecidedWithin (S := slotsOf P.inj assign) U V
    (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, everywhere. -/
  coherent : ∀ m, assign m = P.pick U vdct m
```

A total run: the adaptive fixpoint, two-round rule.

#### `AdaptiveRun.toPartial`

*def, `Adaptive.Odontoceti.lean`*

```lean
def AdaptiveRun.toPartial {P : AdaptivePolicy Validator BlockId Payload}
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V) (E : ℕ) :
    PartialRun P U V E where
  assign := R.assign
  vdct := R.vdct
  closed := fun k _ => R.closed k
  coherent := fun m _ => R.coherent m
```

A total run is partial at every height.

### Nemo-Nemo: crash-fault consensus in two rounds

#### `majority`

*def, `Nemo.Basic.lean`*

```lean
def majority (Validator : Type*) [Fintype Validator] : ℕ :=
  Fintype.card Validator / 2 + 1
```

The majority quorum: strictly more than half the validators, `n/2 + 1`.

#### `ValidWrt`

*structure, `Nemo.Basic.lean`*

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- Non-genesis blocks reference a **majority** of distinct validators. -/
  quorum : 0 < b.round → majority Validator ≤ (creators blk b).card
```

Crash block validity: like the core `ValidWrt`, but the parents quorum is the majority `n/2+1` rather than `n − f`, and the core's `self_parent` and `distinct_creators` fields are gone. The implementation's block verifier imposes neither: there is no self-parent check, and duplicate-author includes are deduplicated by the stake aggregator, not rejected. Under crash the second is also derivable — universal non-equivocation makes duplicate creators among refs impossible (`Universe.eq_of_mem_refs_of_creator_eq`).

#### `Universe`

*structure, `Nemo.Basic.lean`*

```lean
structure Universe (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid (majority parents). -/
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  /-- **No validator equivocates** — one block per author per round, for everyone. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator = (block j).creator → (block i).round = (block j).round → i = j
```

The crash block universe: majority-parent validity and **universal** non-equivocation — every validator is honest, so there is no Byzantine exemption. No `Faults` instance is needed.

#### `View`

*structure, `Nemo.Basic.lean`*

```lean
structure View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] (U : Universe Validator BlockId Payload) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed under references. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

A view: one validator's local, reference-closed sub-DAG.

#### `Reaches`

*def, `Nemo.CausalHistory.lean`*

```lean
def Reaches (U : Universe Validator BlockId Payload) : BlockId → BlockId → Prop :=
  ReachesFrom U.block
```

`Reaches U c b` — `b` lies in the causal history of `c`.

#### `history`

*def, `Nemo.History.lean`*

```lean
def history (U : Universe Validator BlockId Payload) (b : BlockId) : Finset BlockId :=
  historyFrom U.block b
```

The causal history of `b`, as a `Finset`.

#### `blocksAt`

*def, `Nemo.Support.lean`*

```lean
def blocksAt (U : Universe Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)
```

The ids present at a given round.

#### `authorsAt`

*def, `Nemo.Support.lean`*

```lean
def authorsAt (U : Universe Validator BlockId Payload) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)
```

The validators holding a block at a given round — the pool `p`.

#### `supporters`

*def, `Nemo.Support.lean`*

```lean
def supporters (U : Universe Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => b ∈ (U.block q).refs))
```

The validators whose round-`n` block references `b`.

#### `DirectCommit`

*def, `Nemo.Rules.lean`*

```lean
def DirectCommit (U : Universe Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  majority Validator ≤ (supporters U L (r + 1)).card
```

**Direct commit**: a majority of round-`(r+1)` authors reference `L`. At wave length two the votes are the certificates, so the rule counts `supporters` directly.

#### `CertifiedIn`

*def, `Nemo.Rules.lean`*

```lean
def CertifiedIn (U : Universe Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ p ∈ history U A, (U.block p).round = r + 1 ∧ L ∈ (U.block p).refs
```

**The indirect test** (link size one): a round-`(r+1)` vote for `L` lies in the anchor's cone. The name keeps the core's `CertifiedIn` — under crash the vote block *is* the certificate. Stated over the `history` `Finset` rather than `Reaches`, so it is decidable.

#### `decisionRound`

*def, `Nemo.Decision.lean`*

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1
```

The round at which a slot's verdict is settled: its votes live here. One round — at wave length two the votes are the certificates.

#### `Eligible`

*def, `Nemo.Decision.lean`*

```lean
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j
```

`j` may anchor `k`: its proposal lies past `k`'s decision round.

#### `IsLeaderBlock`

*def, `Nemo.Decision.lean`*

```lean
def IsLeaderBlock (U : Universe Validator BlockId Payload) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

`L` is a candidate leader block of slot `k`.

#### `supportersIn`

*def, `Nemo.Decision.lean`*

```lean
def supportersIn (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun p => L ∈ (U.block p).refs)) ∩ V.ids)
```

The supporters a view actually holds.

#### `DirectCommitIn`

*def, `Nemo.Decision.lean`*

```lean
def DirectCommitIn (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  majority Validator ≤ (supportersIn U V L r).card
```

Direct commit, as judged from a single view.

#### `Decided`

*inductive, `Nemo.Decision.lean`*

```lean
inductive Decided (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, a vote is in reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate is in
  reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

**The decision relation.** `Decided U V k v` — a validator holding the view `V` has settled slot `k`, committing the block `v = some L` or skipping it, `v = none`.

Three rules. The *direct* rule reads the slot's own votes: a candidate carrying a majority of them is committed. The *indirect* pair applies when the direct evidence is inconclusive, and decides `k` by looking up to an **anchor** — the nearest eligible slot above `k` that is itself committed — and asking whether a vote for a candidate of `k` lies in the anchor's cone. There is no direct skip: the implementation pins its quorum to the full stake, so skips only ever arrive via an anchor.

"Nearest" is stated positively: every eligible slot strictly between `k` and the anchor is decided `none`. The negative reading would be a negative premise, which an inductive definition cannot carry; the positive form is equivalent, since the sweep decides every slot it passes, and it keeps every recursive occurrence strictly positive.

The `indirectSkip` premise still quantifies over candidates even though a slot has at most one (`isLeaderBlock_unique`): the ∀ ranges over a possibly-empty set, covering the crashed leader that produced no block.

The relation is indexed by a view, so two validators may reach different verdicts by the letter of the definition; `decided_unique` is the theorem that they cannot.

#### `ledgerSet`

*def, `Nemo.Decision.lean`*

```lean
def ledgerSet (U : Universe Validator BlockId Payload)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}
```

The blocks output after settling slots `0, …, n-1`: everything in the causal history of a committed leader.

#### `OutputAt`

*def, `Nemo.Decision.lean`*

```lean
def OutputAt (U : Universe Validator BlockId Payload)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b
```

`b` enters the ledger at slot `k`: the first committed slot whose leader reaches it.

#### `CrashFaults`

*class, `Nemo.Liveness.lean`*

```lean
class CrashFaults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The crashed validators. Everything else is live. -/
  crashed : Finset Validator
  /-- At most `f` validators crash. -/
  card_crashed : crashed.card ≤ f
  /-- There are at least `2f+1` validators. -/
  card_validators : 2 * f + 1 ≤ Fintype.card Validator
```

The crash fault model: `n ≥ 2f+1` validators, at most `f` of them crashed. A crashed validator halts — its blocks, while they lasted, are consistent (`no_equivocation` is universal); only its availability is in doubt. Safety never consults this class; it exists for liveness alone.

#### `Live`

*def, `Nemo.Liveness.lean`*

```lean
def Live : Finset Validator := (C.crashed)ᶜ
```

The live validators: everyone outside the crashed set.

#### `PopulatedOn`

*def, `Nemo.Liveness.lean`*

```lean
def PopulatedOn (U : Universe Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  PopulatedFrom U.block U.ids T r
```

Every validator in `T` has a block at round `r` — the shared `PopulatedFrom` at the crash universe's data. A *quorum* of reliable validators, not all of `Live`: demanding the whole class would make the theorems lapse when a single live validator misses a single round.

#### `SynchronisedOn`

*def, `Nemo.Liveness.lean`*

```lean
def SynchronisedOn (U : Universe Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  SynchronisedFrom U.block U.ids T R
```

From round `R` on, every `T`-authored block references every `T`-authored block of the round below — the shared `SynchronisedFrom` at the crash universe's data, the post-GST coverage assumption.

#### `View.full`

*def, `Nemo.Liveness.lean`*

```lean
def View.full (U : Universe Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete
```

Every live validator's *eventual* view. Downward-closed by `U.complete`.

#### `SpansEligible`

*def, `Nemo.Liveness.lean`*

```lean
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)
```

A run of `c` slots reaches past everything below it.

#### `Populated`

*abbrev, `Nemo.Liveness.lean`*

```lean
abbrev Populated (U : Universe Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Live Validator) r
```

The all-of-`Live` participation case.

#### `Synchronised`

*abbrev, `Nemo.Liveness.lean`*

```lean
abbrev Synchronised (U : Universe Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Live Validator) R
```

The all-of-`Live` coverage case.

### Mahi-Mahi: the asynchronous rule at wave w

#### `votingRound`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def votingRound (w r : ℕ) : ℕ := r + w - 2
```

The round at which a candidate proposed at `r` is voted on. The last round before the decision round, as `Wave::voting_round` computes it for every `w ≥ 3`.

#### `decisionRoundAt`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def decisionRoundAt (w r : ℕ) : ℕ := r + w - 1
```

The round at which a candidate proposed at `r` is decided: its certificates live here (`Wave::decision_round`). Named with the suffix because `decisionRound`, on slots, is the name the core's schedule layer uses.

#### `candidatesAt`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def candidatesAt (U : BlockUniverse Validator BlockId Payload)
    (q : BlockId) (a : Validator) (r : ℕ) : Finset BlockId :=
  (blocksAt U r).filter (fun b => (U.block b).creator = a ∧ b ∈ history U q)
```

The blocks of author `a` at round `r` in the cone of `q` — the set the vote is chosen from. A correct author has at most one; an equivocator may have several, which is what the minimality clause of `Votes` arbitrates. Stated with `blocksAt` outermost so that membership unfolds through `mem_blocksAt`, as the Odontoceti arc's `coneSupports` does.

#### `Votes`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def Votes (U : BlockUniverse Validator BlockId Payload) (q L : BlockId) : Prop :=
  L ∈ candidatesAt U q (U.block L).creator (U.block L).round ∧
    ∀ L' ∈ candidatesAt U q (U.block L).creator (U.block L).round, ¬ L' < L
```

**`q` votes for `L`**: `L` is the least block of its own author and round in `q`'s cone. The minimality clause is the canonical-support choice (`mahi-mahi.md` §2), written `¬ L' < L` rather than `L ≤ L'` so that agreement closes by `le_antisymm` on two `not_lt`s, the form the Odontoceti arc's canonicity premise takes. `L`'s author and round are read off `L` itself, so the rules keep the proposal round `r` as a separate parameter exactly as the core does.

#### `Blames`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def Blames (U : BlockUniverse Validator BlockId Payload)
    (q : BlockId) (a : Validator) (r : ℕ) : Prop :=
  candidatesAt U q a r = ∅
```

**`q` blames the slot `(a, r)`**: no block of that author and round lies in its cone. On the slot rather than on a block, as the implementation's `enough_leader_blame` has it — a blame is the absence of any supported block, not a vote against a particular twin.

#### `votesIn`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => Votes U q L)
```

The references of `C` that vote for `L`. Counted among the *references* of the decision-round block, as `is_certificate` counts them, and not through `C`'s whole cone.

#### `Certifies`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (votesIn U C L)).card
```

A decision-round block certifies `L` when its votes for `L` come from a quorum of distinct validators. The core's definition over the new `votesIn`.

#### `certificates`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def certificates (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (L : BlockId) (r : ℕ) : Finset BlockId :=
  (blocksAt U (decisionRoundAt w r)).filter (fun C => Certifies U C L)
```

The certificates for a candidate `L` proposed at `r`: the blocks of the decision round `r + w − 1` that certify it.

#### `DirectCommit`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U w L r)).card
```

**Direct commit**: a quorum of distinct validators certify `L`.

#### `blamers`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def blamers (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (a : Validator) (r : ℕ) : Finset Validator :=
  creatorsOf U.block ((blocksAt U (votingRound w r)).filter (fun q => Blames U q a r))
```

The validators whose voting-round block blames the slot `(a, r)`.

#### `DirectSkip`

*def, `MahiMahi.Model.Rules.lean`*

```lean
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamers U w a r).card
```

**Direct skip**: a quorum of distinct validators blame the slot. On the slot `(a, r)`, not on a candidate: at `w = 3` this is the core's `DirectSkip` quantified over every candidate of the slot, which is how the core's `directSkip` constructor consumes it.

#### `certificatesIn`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def certificatesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (L : BlockId) (r : ℕ) : Finset BlockId :=
  certificates U w L r ∩ V.ids
```

The certificates for `L` that a view holds.

#### `DirectCommitIn`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificatesIn U V w L r)).card
```

Direct commit, as judged from a single view.

#### `blamersIn`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def blamersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (a : Validator) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (votingRound w r)).filter (fun q => Blames U q a r)) ∩ V.ids)
```

The blamers of the slot `(a, r)` whose voting block a view holds.

#### `DirectSkipIn`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamersIn U V w a r).card
```

Direct skip, as judged from a single view.

#### `CertifiedIn`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def CertifiedIn (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U w L r, Reaches U A C
```

**The indirect test**: a certificate for `L` lies in the causal history of the anchor `A`. The core's `CertifiedIn` at wave `w`. Not decidable as stated — `Reaches` is a `Prop` — and not made so: the witnesses exhibit the certificate.

#### `decisionRound`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def decisionRound (w k : ℕ) : ℕ := S.slotRound k + w - 1
```

The round at which slot `k`'s direct rules are settled: its certificates live at `slotRound k + w − 1`. `Validator` is explicit for the reason the core gives — the result is a bare `ℕ`.

#### `Eligible`

*def, `MahiMahi.Model.Decision.lean`*

```lean
def Eligible (w k j : ℕ) : Prop := decisionRound Validator w k < S.slotRound j
```

**`j` may anchor `k`**: `j`'s proposal lies past `k`'s decision round. A predicate on the pair of slots and the wave length alone, which is what makes agreement go through: two validators deciding one slot agree on which slots may anchor it.

#### `Decided`

*inductive, `MahiMahi.Model.Decision.lean`*

```lean
inductive Decided (w : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate: a quorum of certificates in
  view. -/
  | directCommit {k : ℕ} {L : BlockId} :
      -- L is a candidate for slot k: its round and author are the slot's
      IsLeaderBlock U k L →
      -- a quorum of distinct validators certify L at the decision round,
      -- among the blocks the view holds
      DirectCommitIn U V w L (S.slotRound k) →
      Decided w U V k (some L)
  /-- The direct rule skips the slot: a quorum of blames in view (covers
  the case of no candidate at all — blames target the slot). -/
  | directSkip {k : ℕ} :
      -- a quorum of distinct validators hold a voting-round block whose
      -- cone contains no block of the slot's leader at the slot's round
      DirectSkipIn U V w (S.leader k) (S.slotRound k) →
      Decided w U V k none
  /-- Anchored on the nearest eligible committed slot, a certificate for
  `L` is in the anchor's reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      -- the anchor slot lies ahead of k
      k < j →
      -- ... proposed past k's decision round, slotRound k + w − 1
      Eligible Validator w k j →
      -- slot j committed A, by any route
      Decided w U V j (some A) →
      -- j is the NEAREST such slot: every eligible slot in between skipped
      -- (an undecided one in between leaves this underivable — the
      -- implementation's "stop at the first undecided slot")
      (∀ i, k < i → i < j → Eligible Validator w k i → Decided w U V i none) →
      -- L is a candidate for slot k
      IsLeaderBlock U k L →
      -- a certificate for L lies in the anchor's cone
      CertifiedIn U w A L (S.slotRound k) →
      Decided w U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate has a
  certificate in the anchor's reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      -- the anchor slot lies ahead of k
      k < j →
      -- ... proposed past k's decision round
      Eligible Validator w k j →
      -- slot j committed A, by any route
      Decided w U V j (some A) →
      -- j is the nearest such slot (as in indirectCommit)
      (∀ i, k < i → i < j → Eligible Validator w k i → Decided w U V i none) →
      -- no candidate of slot k has a certificate in the anchor's cone:
      -- only then skip
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U w A L (S.slotRound k)) →
      Decided w U V k none
```

**The decision relation at wave `w`** — the verdicts a validator holding view `V` may reach on slot `k`. `Decided w U V k (some L)`: the validator may commit `L` at `k`; `Decided w U V k none`: it may skip the slot; *undecided* is the absence of any derivation.

The relation is order-free between constructors: the implementation tries the direct rule before the indirect one, but any justifiable verdict is derivable here, and the safety results prove the routes never disagree. The anchor premises follow `try_indirect_decide`: the anchor is the **nearest eligible committed** slot — `Decided … j (some A)` with every eligible slot strictly between decided `none` (a skipped slot cannot anchor; a committed one would be the nearer anchor). "Stop at the first undecided slot" needs no encoding: an undecided slot in between leaves no derivation.

The one departure from the core: `directSkip` takes the slot's blame directly, `DirectSkipIn U V w (S.leader k) (S.slotRound k)`, where the core quantifies `∀ L, IsLeaderBlock U k L → DirectSkipIn U V L …`. The skip rule is on the slot in the paper and in the implementation, and at `w = 3` the two readings agree, which the conservativity result MM1d states (`mahi-mahi.md` §3).

#### `goodAt`

*def, `MahiMahi.Model.Good.lean`*

```lean
def goodAt (U : BlockUniverse Validator BlockId Payload) (w r : ℕ) : Finset Validator :=
  Finset.univ.filter (fun v => ∃ L ∈ U.ids,
    (U.block L).round = r ∧ (U.block L).creator = v ∧ DirectCommit U w L r)
```

The validators whose round-`r` block is directly committed at wave `w`. Round-indexed and slot-free, so that the counting theorems mention no schedule; decidable on a concrete universe, as a bounded search over `U.ids` of decidable conjuncts.

#### `good`

*def, `MahiMahi.Model.Good.lean`*

```lean
def good (U : BlockUniverse Validator BlockId Payload) [S : Slots Validator]
    (w k : ℕ) : Finset Validator :=
  goodAt U w (S.slotRound k)
```

The slot-`k` candidates the DAG directly commits: `goodAt` at the slot's round. The schedule enters only through `slotRound`.

#### `AgreeUpto`

*structure, `MahiMahi.Model.Unpredictable.lean`*

```lean
structure AgreeUpto (U₁ U₂ : BlockUniverse Validator BlockId Payload) (d : ℕ) : Prop where
  /-- The ids at rounds `≤ d` coincide. -/
  ids : ∀ i, (i ∈ U₁.ids ∧ (U₁.block i).round ≤ d) ↔ (i ∈ U₂.ids ∧ (U₂.block i).round ≤ d)
  /-- And they denote the same blocks. -/
  block : ∀ i ∈ U₁.ids, (U₁.block i).round ≤ d → U₁.block i = U₂.block i
```

**Two universes agree up to round `d`**: the same ids at rounds `≤ d`, denoting the same blocks. What the measurability result MM2′ consumes — whatever decides `good` at a wave is fixed by the rounds up to its decision round, which is the round at which a deployment reveals the leader.

#### `UnpredictableWithin`

*def, `MahiMahi.Model.Unpredictable.lean`*

```lean
def UnpredictableWithin (U : BlockUniverse Validator BlockId Payload)
    (w c N : ℕ) : Prop :=
  ∀ k,
    -- the window's last decision round lies below the horizon
    decisionRound Validator w (k + c) ≤ N →
    -- some slot of the window is led by a validator whose block commits
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U w k'
```

**The single-hit form.** In every window of `c` slots whose decision rounds lie below the horizon `N`, the schedule names a committed candidate at least once.

#### `UnpredictableRunWithin`

*def, `MahiMahi.Model.Unpredictable.lean`*

```lean
def UnpredictableRunWithin (U : BlockUniverse Validator BlockId Payload)
    (w c d N : ℕ) : Prop :=
  ∀ k,
    -- the latest run's last decision round lies below the horizon
    decisionRound Validator w (k + c + d - 1) ≤ N →
    -- some run of d slots starting in the window is led by committed candidates
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ good U w (k' + i)
```

**The run form.** In every window of `c` slots below the horizon, a run of `d` consecutive slots whose leaders are all committed candidates. The bound reads the last slot of the latest possible run, `k + c + d − 1`, so that small universes are not vacuously covered.

#### `SpansEligible`

*def, `MahiMahi.Model.Unpredictable.lean`*

```lean
def SpansEligible (w c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator w i (b + c - 1)
```

**A run of `c` slots spans eligibility**: every slot below its start is eligible for its last slot. The core's `SpansEligible` at wave `w`; at one leader per round it holds for `c = w`.

#### `SkipExcludesCertificates`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def SkipExcludesCertificates (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (a : Validator) (r : ℕ) (L : BlockId),
    3 ≤ w → DirectSkip U w a r →
    L ∈ U.ids → (U.block L).creator = a → (U.block L).round = r →
    certificates U w L r = ∅
```

**MM1a, skip excludes certificates**: a directly skipped slot `(a, r)` has no certificate for any block of that author and round. The quorum of blamers and the quorum of voters behind a certificate would share a correct validator, whose unique voting block cannot both hold a candidate in its cone and hold none.

#### `CertificateUniqueness`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def CertificateUniqueness (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ : BlockId),
    3 ≤ w →
    (certificates U w L₁ r).Nonempty → (certificates U w L₂ r).Nonempty →
    (U.block L₁).creator = (U.block L₂).creator →
    (U.block L₁).round = (U.block L₂).round →
    L₁ = L₂
```

**MM1b, certificate uniqueness**: two certified blocks of one author and round are equal — universe-level, no views. Two voter quorums share a correct validator, whose unique voting block votes for the least candidate of that author and round, and only for it.

#### `Agreement`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def Agreement (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    3 ≤ w → Decided w U V₁ k v₁ → Decided w U V₂ k v₂ → v₁ = v₂
```

**MM1c, agreement**: two views deciding one slot agree on the verdict, whatever routes each took — the core's M6 at wave `w`.

#### `DecidedConservative`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def DecidedConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (k : ℕ) (v : Option BlockId),
    Decided 3 U V k v → LeanDag.Decided U V k v
```

**MM1d, conservativity of the relation**: at `w = 3` a derivation of this arc's `Decided` is a derivation of the core's. A statement about the two definitions, not about any verdict occurring: it says the three-round instance of the wave-`w` relation *is* Mysticeti's, as `uniformSingle_spacing` says for the schedule generalisation. Whether anything commits is a liveness question, and at `w = 3` the answer needs the core's synchrony hypothesis (`mahi-mahi.md` §4.2).

#### `DirectCommitConservative`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def DirectCommitConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ),
    L ∈ U.ids → (U.block L).round = r →
    (DirectCommit U 3 L r ↔ LeanDag.DirectCommit U L r)
```

**MM1d, conservativity of direct commit**: at `w = 3` the two direct commit predicates coincide on every candidate at its own round — a round-`(r+1)` block's candidates at `(a, r)` are its references by `a`. An equivalence of predicates on a given DAG, true whether or not either side holds; it does not assert that a direct commit occurs.

#### `DirectSkipConservative`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def DirectSkipConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (a : Validator) (r : ℕ),
    DirectSkip U 3 a r →
    ∀ L ∈ U.ids, (U.block L).creator = a → (U.block L).round = r →
      LeanDag.DirectSkip U L r) ∧
  (∀ (a : Validator) (r : ℕ) (L : BlockId),
    L ∈ U.ids → (U.block L).creator = a → (U.block L).round = r →
    (∀ L' ∈ U.ids, (U.block L').creator = a → (U.block L').round = r → L' = L) →
    (DirectSkip U 3 a r ↔ LeanDag.DirectSkip U L r))
```

**MM1d, conservativity of direct skip**: at `w = 3` this arc's skip implies the core's for every candidate of the slot, and the two coincide on a slot with at most one candidate.

#### `Statement`

*def, `MahiMahi.Safety.Statement.lean`*

```lean
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    SkipExcludesCertificates U w ∧ CertificateUniqueness U w ∧ Agreement U w ∧
      DecidedConservative U ∧ DirectCommitConservative U ∧ DirectSkipConservative U
```

Safety of the rule at wave `w`, over every fault configuration, schedule, block universe and wave length the model admits.

#### `CommonCore`

*def, `MahiMahi.Counting.Statement.lean`*

```lean
def CommonCore (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (c₀ : BlockId),
    -- some block exists two rounds above r (its own quorum of references
    -- is what makes the round-(r+1) author pool large enough to count)
    c₀ ∈ U.ids → (U.block c₀).round = r + 2 →
    -- then there is a round-r block b ...
    ∃ b ∈ U.ids, (U.block b).round = r ∧
      -- ... by a correct validator ...
      (U.block b).creator ∈ (Correct : Finset Validator) ∧
      -- ... in the causal history of EVERY block at round ≥ r + 2
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b
```

**The common core.** If some block exists at round `r + 2`, a correct validator's round-`r` block lies in the causal history of every block at every round `≥ r + 2`. The core's T3c (`CommonCore.lean`) at round `r + 2`, carried upward through references.

#### `GoodNonempty`

*def, `MahiMahi.Counting.Statement.lean`*

```lean
def GoodNonempty (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- at least four rounds: the voting round r + w − 2 is at or above r + 2,
    -- where the common core is reached by everyone
    4 ≤ w →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every member of T has a block at round r + 2 (so the common core
    -- exists) ...
    PopulatedOn U T (r + 2) →
    -- ... and at the decision round r + w − 1 (so the certificates form a
    -- quorum)
    PopulatedOn U T (decisionRoundAt w r) →
    -- then some correct validator's round-r block is directly committed
    (goodAt U w r ∩ (Correct : Finset Validator)).Nonempty
```

**MM2 at `w ≥ 4`.** Some correct validator's round-`r` block is directly committed. The common core of round `r` is reached by every voting-round block (`r + w − 2 ≥ r + 2`), so every decision-round block certifies it, and the reliable ones are a quorum.

#### `GoodCard`

*def, `MahiMahi.Counting.Statement.lean`*

```lean
def GoodCard (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- at least five rounds: the voting round r + w − 2 is at or above r + 3,
    -- where the common core of round r + 1 is reached by everyone
    5 ≤ w →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every member of T has a block at round r + 3 (so the round-(r+1)
    -- common core exists) ...
    PopulatedOn U T (r + 3) →
    -- ... and at the decision round r + w − 1
    PopulatedOn U T (decisionRoundAt w r) →
    -- then n − f ≤ |good ∩ Correct| + |byzantine|: the core's n − f
    -- references have distinct creators, and every correct one is good
    quorumCard Validator ≤
      (goodAt U w r ∩ (Correct : Finset Validator)).card + F.byzantine.card
```

**MM2 at `w ≥ 5`.** `n − f ≤ |good ∩ Correct| + |byzantine|`: the correct authors among the `n − f` references of the round-`(r + 1)` common core are all directly committed, since every voting-round block (`r + w − 2 ≥ r + 3`) reaches the core and, through it, each reference. At `n = 3f + 1` and `|byzantine| = f` this is `f + 1` good correct validators.

#### `MultiLeader`

*def, `MahiMahi.Counting.Statement.lean`*

```lean
def MultiLeader (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- the hypotheses of GoodCard, verbatim
    5 ≤ w →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 3) → PopulatedOn U T (decisionRoundAt w r) →
    -- M is a set of validators each of which leads some slot at round r ...
    ∀ M : Finset Validator, (∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v) →
      -- ... with at least 2f + 1 members (distinct, being a Finset)
      2 * F.f + 1 ≤ M.card →
      -- then one of those slots is led by a good validator
      ∃ k, S.slotRound k = r ∧ S.leader k ∈ good U w k
```

**MM2b, deterministic commits under multiple leaders.** If `2f + 1` distinct validators lead slots at round `r` and `w ≥ 5`, one of those slots is good — for every schedule, with no randomness clause: `f + 1` good correct validators and `2f + 1` leaders cannot be disjoint in `3f + 1`. The `w ≥ 4` analogue with every validator leading is `GoodNonempty` itself.

#### `Statement`

*def, `MahiMahi.Counting.Statement.lean`*

```lean
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    CommonCore U ∧ GoodNonempty U w ∧ GoodCard U w ∧ MultiLeader U w
```

The counting lemma, over every fault configuration, schedule, block universe and wave length the model admits.

#### `GoodCommits`

*def, `MahiMahi.Liveness.Statement.lean`*

```lean
def GoodCommits (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ k,
    -- the slot's leader is a committed candidate of its round
    S.leader k ∈ good U w k →
    -- then its block is a candidate, decided as committed from the full view
    ∃ L, IsLeaderBlock U k L ∧ Decided w U (View.full U) k (some L)
```

**MM3a, a good leader commits.**

#### `CommitsWithin`

*def, `MahiMahi.Liveness.Statement.lean`*

```lean
def CommitsWithin (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (c N : ℕ),
    -- the single-hit clause, with window c below horizon N
    UnpredictableWithin U w c N →
    -- for every window below the horizon ...
    ∀ k, decisionRound Validator w (k + c) ≤ N →
      -- ... some slot of it commits
      ∃ k', k ≤ k' ∧ k' < k + c ∧
        ∃ L, IsLeaderBlock U k' L ∧ Decided w U (View.full U) k' (some L)
```

**MM3b, commits within every window.**

#### `AllDecidedBelow`

*def, `MahiMahi.Liveness.Statement.lean`*

```lean
def AllDecidedBelow (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (c d N : ℕ),
    -- a wave has at least one round (what `k < j` for an eligible anchor needs)
    1 ≤ w →
    -- a run of d slots spans eligibility
    SpansEligible Validator w d →
    -- the run form of the clause
    UnpredictableRunWithin U w c d N →
    -- for every window below the horizon ...
    ∀ k, decisionRound Validator w (k + c + d - 1) ≤ N →
      -- ... there is a slot b at or past k below which every slot is decided
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, Decided w U (View.full U) i v
```

**MM3c, every slot below a run is decided.**

#### `LocalCommit`

*def, `MahiMahi.Liveness.Statement.lean`*

```lean
def LocalCommit (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (N : ℕ) (pc : PaceCore U T N),
    -- T is a quorum (its correctness is the pacing structure's own)
    quorumCard Validator ≤ T.card →
    ∀ (k : ℕ) (L : BlockId),
      -- L is slot k's candidate, and its decision round is within the horizon
      IsLeaderBlock U k L → decisionRound Validator w k ≤ N →
      -- every reliable decision-round block certifies L
      (∀ u ∈ T, ∀ C ∈ U.ids, (U.block C).creator = u →
        (U.block C).round = decisionRound Validator w k → Certifies U C L) →
      -- then every reliable validator commits L on its own view, by the time
      -- the decision round's reliable blocks have converged
      ∀ v ∈ T, Decided w U
        (pc.viewAt v (max (pc.latest (decisionRound Validator w k)) pc.gst + pc.delay))
        k (some L)
```

**MM3d, local liveness.**

#### `GoodMeasurable`

*def, `MahiMahi.Liveness.Statement.lean`*

```lean
def GoodMeasurable : Prop :=
  ∀ (U₁ U₂ : BlockUniverse Validator BlockId Payload) (w r : ℕ),
    -- the voting round is at or above the proposal round
    2 ≤ w →
    -- the two universes agree up to the decision round ...
    AgreeUpto U₁ U₂ (decisionRoundAt w r) →
    -- ... so they commit the same candidates there
    goodAt U₁ w r = goodAt U₂ w r
```

**MM2′, measurability of `good`.**

#### `Statement`

*def, `MahiMahi.Liveness.Statement.lean`*

```lean
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    GoodCommits U w ∧ CommitsWithin U w ∧ AllDecidedBelow U w ∧ LocalCommit U w ∧
      GoodMeasurable (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
```

Liveness under the clause, over every fault configuration, schedule, block universe and wave length the model admits.

#### `GoodOfSynchrony`

*def, `MahiMahi.Synchrony.Statement.lean`*

```lean
def GoodOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (R k : ℕ),
    -- four rounds: the voting round is at or above r + 2, where every block
    -- reaches a candidate referenced by every reliable round-(r+1) block
    4 ≤ w →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the core's coverage hypothesis, in force at the slot's round
    SynchronisedOn U T R → R ≤ S.slotRound k →
    -- T populates the proposal round, the round above it, and the decision round
    PopulatedOn U T (S.slotRound k) → PopulatedOn U T (S.slotRound k + 1) →
    PopulatedOn U T (decisionRound Validator w k) →
    -- the slot's leader is reliable
    S.leader k ∈ T →
    -- then the leader is a committed candidate of its round
    S.leader k ∈ good U w k
```

**MM5a, a reliable leader is good under coverage at one round.**

#### `ClauseOfSynchrony`

*def, `MahiMahi.Synchrony.Statement.lean`*

```lean
def ClauseOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (c N : ℕ),
    4 ≤ w →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- coverage from round 0 and population through the horizon
    SynchronisedOn U T 0 → (∀ n, n ≤ N → PopulatedOn U T n) →
    -- the core's rated fairness: a T-leader in every window of c slots
    FairWithin T c →
    -- then the single-hit clause holds with the same window
    UnpredictableWithin U w c N
```

**MM5b, the clause is derived under synchrony.**

#### `Statement`

*def, `MahiMahi.Synchrony.Statement.lean`*

```lean
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    GoodOfSynchrony U w ∧ ClauseOfSynchrony U w
```

Partial synchrony recovered, over every fault configuration, schedule, block universe and wave length the model admits.

### Not otherwise grouped

#### `SoundOn`

*structure, `Integration.Sound.lean`*

```lean
structure SoundOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop where
  /-- No correct validator has two blocks at one round. -/
  honest : HonestNoEquiv U
  /-- Every `T`-authored block references every `T`-authored block of the
  round below, from `R` on. -/
  covered : SynchronisedOn U T R
```

**What a universe must still supply after being transformed.** The two conditions every safety result of the hybrid arc consumes: correct validators do not equivocate, and the DAG is covered from round `R` on.

#### `waveRobin`

*def, `WaveRobin.lean`*

```lean
def waveRobin (n : ℕ) (hn : 0 < n) : Slots (Fin n) :=
  Slots.uniformSingle 1 Nat.one_pos (fun k => ⟨k / 3 % n, Nat.mod_lt _ hn⟩)
```

**The wave-aligned round-robin schedule** on `n` validators: pipelined (one slot per round), with the leader holding for a whole wave — three consecutive slots — before the rotation advances.

Built from `Slots.uniformSingle` rather than by hand, so the class fields need no new proofs; only the electorate function is new. A `def` rather than an `instance`, like `rrSlots` in the witness files: a second `Slots` instance on the same type would make synthesis ambiguous, so every use passes `(S := waveRobin n hn)` explicitly.


---

## Appendix C. The theorem reference

The 442 theorems that either another module of the
development depends on, or that Appendix A indexes as principal
results — the second clause because the capstones are consumed
by nothing, being endpoints. Each is the source statement,
unabridged. Generated with Appendix B.

### The validator set and the fault model

#### `mem_correct`

*theorem, `Validators.lean`*

```lean
theorem mem_correct {v : Validator} : v ∈ (Correct : Finset Validator) ↔ v ∉ F.byzantine
```

Correctness is the complement of the Byzantine set.

#### `card_correct_add_byzantine`

*theorem, `Validators.lean`*

```lean
theorem card_correct_add_byzantine :
    (Correct : Finset Validator).card + F.byzantine.card = Fintype.card Validator
```

The correct and Byzantine validators partition the whole set.

Stated additively so it yields both bounds without ℕ subtraction. The *upper* bound on `Correct.card` is the one the counting arguments need — they divide an incidence count by the number of correct validators, for which a lower bound is useless.

#### `faults_arith`

*theorem, `Validators.lean`*

```lean
theorem faults_arith :
    (Correct : Finset Validator).card + F.byzantine.card = Fintype.card Validator ∧
      F.byzantine.card ≤ F.f ∧ 3 * F.f + 1 ≤ Fintype.card Validator
```

**The standing arithmetic of the fault model**, in the form `omega` consumes it: the correct and Byzantine sets partition the validators, at most `f` are Byzantine, and there are at least `3f+1` in all.

A conjunction because the three are always wanted together — every counting argument in the development opens by introducing them, and naming the bundle says that these, and only these, are what the fault model contributes to an arithmetic step.

#### `card_correct`

*theorem, `Validators.lean`*

```lean
theorem card_correct : quorumCard Validator ≤ (Correct : Finset Validator).card
```

The correct validators alone meet the quorum threshold: at least `n − f` of them. This is what the threshold `n − f` is *for* — the correct pool suffices on its own.

#### `two_f_add_one_le_card_correct`

*theorem, `Validators.lean`*

```lean
theorem two_f_add_one_le_card_correct :
    2 * F.f + 1 ≤ (Correct : Finset Validator).card
```

At least `2f+1` validators are correct — the `n = 3f+1` reading of `card_correct`, kept for arguments that count in `f` alone.

#### `exists_correct_of_card`

*theorem, `Validators.lean`*

```lean
theorem exists_correct_of_card {S : Finset Validator} (h : F.f + 1 ≤ S.card) :
    ∃ v ∈ S, v ∈ (Correct : Finset Validator)
```

Any set of more than `f` validators contains a correct one, since the Byzantine validators number at most `f`.

#### `card_le_card_inter_correct_add_byzantine`

*theorem, `Validators.lean`*

```lean
theorem card_le_card_inter_correct_add_byzantine (S : Finset Validator) :
    S.card ≤ (S ∩ (Correct : Finset Validator)).card + F.byzantine.card
```

Byzantine validators can absorb at most `f` of any set: removing the correct members of `S` leaves something no bigger than the Byzantine set.

The workhorse behind "a quorum still contains many correct validators". Stated additively so it composes without ℕ subtraction.

#### `card_inter_correct_of_quorum`

*theorem, `Validators.lean`*

```lean
theorem card_inter_correct_of_quorum {S : Finset Validator}
    (h : quorumCard Validator ≤ S.card) :
    F.f + 1 ≤ (S ∩ (Correct : Finset Validator)).card
```

A quorum contains at least `f+1` *correct* validators: `(n − f) − f = n − 2f ≥ f+1`.

The cardinality strengthening of `exists_correct_of_card`, which only produces one.

#### `exists_correct_mem_inter`

*theorem, `Validators.lean`*

```lean
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : quorumCard Validator ≤ Q₁.card)
    (h₂ : quorumCard Validator ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator)
```

**T0.** Two quorums always share a *correct* validator. This is the form every later proof cites.

### Blocks, validity, and the universe

#### `mem_creatorsOf`

*theorem, `Block.lean`*

```lean
theorem mem_creatorsOf {blk : BlockId → Block Validator BlockId Payload}
    {s : Finset BlockId} {v : Validator} :
    v ∈ creatorsOf blk s ↔ ∃ i ∈ s, (blk i).creator = v
```

Membership in `creatorsOf`, unfolded: a validator is a creator of a set of ids exactly when it authored one of them.

#### `nonempty_of_creatorsOf_card_pos`

*theorem, `Block.lean`*

```lean
theorem nonempty_of_creatorsOf_card_pos {blk : BlockId → Block Validator BlockId Payload}
    {s : Finset BlockId} (h : 0 < (creatorsOf blk s).card) : s.Nonempty
```

A nonempty creator set can only come from a nonempty set of ids: the image of `∅` is `∅`.

Small, but it was inlined in three places — `ValidWrt.refs_nonempty` here, and the two "a quorum implies at least one block" steps in `Persistence` and `Mysticeti`.

#### `refs_empty_of_round_zero`

*theorem, `Block.lean`*

```lean
theorem refs_empty_of_round_zero (h : ValidWrt blk b) (h0 : b.round = 0) : b.refs = ∅
```

Genesis blocks have no references — derived from the predecessor condition, not assumed.

#### `refs_nonempty`

*theorem, `Block.lean`*

```lean
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty
```

A non-genesis block has at least one reference. Used by T3's inductive step, which needs only this much of validity.

Proved from the quorum condition **alone**, deliberately not via `card_refs`: the image of `∅` is `∅`, so an empty `refs` would give an empty creator set. Routing through `card_refs` would drag `distinct_creators` onto T3's dependency path, and the whole point of `spec.md` §3.2's analysis is that Phase 1 and 1b never need it.

#### `exists_correct_mem_creators_inter`

*theorem, `Block.lean`*

```lean
theorem exists_correct_mem_creators_inter
    {blk : BlockId → Block Validator BlockId Payload} {s t : Finset BlockId}
    (hs : quorumCard Validator ≤ (creatorsOf blk s).card)
    (ht : quorumCard Validator ≤ (creatorsOf blk t).card) :
    ∃ v ∈ creatorsOf blk s ∩ creatorsOf blk t, v ∈ (Correct : Finset Validator)
```

**T0'.** Two id-sets whose creator sets are quorums share a *correct* author.

Stated on bare `Finset BlockId`s rather than on blocks, because that is what every call site needs: T3 intersects a block's refs with an arbitrary set `Q`, and T5 intersects two arbitrary sets, neither of which is any block's refs. For a block, apply it with `s := b.refs` and discharge the hypothesis with `ValidWrt.quorum`.

#### `eq_of_creator_eq`

*theorem, `BlockDag.lean`*

```lean
theorem eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ (Correct : Finset Validator))
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) :
    i = j
```

**T1.** A correct validator authors at most one block per round, so two ids in the universe with the same correct author and the same round are the *same id*.

Phrased around the author `v` rather than around `(U.block i).creator`, because that is how every use site arrives: a quorum intersection yields a correct validator, and T1 turns two blocks known to be authored by it into a single concrete id.

#### `round_of_mem_refs`

*theorem, `BlockDag.lean`*

```lean
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round
```

A reference sits in the round immediately below its referrer.

#### `creators_quorum`

*theorem, `BlockDag.lean`*

```lean
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    quorumCard Validator ≤ (creatorsOf U.block (U.block i).refs).card
```

References of a non-genesis block carry a quorum of distinct authors. This is the hypothesis T0' consumes.

#### `refs_nonempty`

*theorem, `BlockDag.lean`*

```lean
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (U.block i).refs.Nonempty
```

A non-genesis block references at least one block.

#### `exists_common_mem_of_quorums`

*theorem, `BlockDag.lean`*

```lean
theorem exists_common_mem_of_quorums {s t : Finset BlockId} {n : ℕ}
    (hs : ∀ q ∈ s, q ∈ U.ids ∧ (U.block q).round = n)
    (ht : ∀ q ∈ t, q ∈ U.ids ∧ (U.block q).round = n)
    (hsq : quorumCard Validator ≤ (creatorsOf U.block s).card)
    (htq : quorumCard Validator ≤ (creatorsOf U.block t).card) :
    ∃ q, q ∈ s ∧ q ∈ t
```

**Two quorum-backed sets of round-`n` blocks must share a block.**

T0' gives a correct author common to both creator sets, and T1 makes that author's round-`n` block unique — so the two blocks it contributes coincide.

This is the recurring "peel off one certification layer" step: it is exactly what M5′ does to two certificates' vote sets, and what M5 would otherwise do a second time to two certificate sets.

### Causal structure

#### `refl`

*theorem, `Causality.lean`*

```lean
theorem refl {c : BlockId} : ReachesFrom blk c c
```

Every block is in its own causal history.

#### `single`

*theorem, `Causality.lean`*

```lean
theorem single {i j : BlockId} (h : j ∈ (blk i).refs) : ReachesFrom blk i j
```

A direct reference is one step of causal history.

#### `trans`

*theorem, `Causality.lean`*

```lean
theorem trans {a b c : BlockId} (h₁ : ReachesFrom blk a b) (h₂ : ReachesFrom blk b c) :
    ReachesFrom blk a c
```

Causal history composes.

#### `of_mem_refs`

*theorem, `Causality.lean`*

```lean
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (blk i).refs) (hjb : ReachesFrom blk j b) :
    ReachesFrom blk i b
```

Prepend a direct reference.

#### `mem_of_reaches_of_closed`

*theorem, `Causality.lean`*

```lean
theorem mem_of_reaches_of_closed {S : Finset BlockId}
    (hS : ∀ i ∈ S, ∀ j ∈ (blk i).refs, j ∈ S) {c b : BlockId}
    (hc : c ∈ S) (h : ReachesFrom blk c b) : b ∈ S
```

**Causal history never leaves a reference-closed set.** Stated over any such set, so one lemma serves both the population of a universe and the holdings of a view.

#### `mem_ids_of_reaches`

*theorem, `Causality.lean`*

```lean
theorem mem_ids_of_reaches (C : CausalStructure blk ids)
    {c b : BlockId} (hc : c ∈ ids) (h : ReachesFrom blk c b) :
    b ∈ ids
```

Causal history stays inside the population.

#### `refs_empty_of_round_zero`

*theorem, `Causality.lean`*

```lean
theorem refs_empty_of_round_zero (C : CausalStructure blk ids)
    {b : BlockId} (hb : b ∈ ids) (hround : (blk b).round = 0) :
    (blk b).refs = ∅
```

**A genesis block has no references** — one would have to sit a round below round `0`. Derived, so no validity clause is needed for it here.

#### `round_le_of_reaches`

*theorem, `Causality.lean`*

```lean
theorem round_le_of_reaches (C : CausalStructure blk ids)
    {c b : BlockId} (hc : c ∈ ids) (h : ReachesFrom blk c b) :
    (blk b).round ≤ (blk c).round
```

**Causal history runs downward in rounds.**

#### `not_reaches_of_round_lt`

*theorem, `Causality.lean`*

```lean
theorem not_reaches_of_round_lt (C : CausalStructure blk ids) {c b : BlockId} (hc : c ∈ ids)
    (h : (blk c).round < (blk b).round) : ¬ ReachesFrom blk c b
```

A block cannot reach anything strictly above it.

#### `mem_historyUptoFrom_succ`

*theorem, `Causality.lean`*

```lean
theorem mem_historyUptoFrom_succ {n : ℕ} {b i : BlockId} :
    i ∈ historyUptoFrom blk (n + 1) b ↔
      i = b ∨ ∃ j ∈ (blk b).refs, i ∈ historyUptoFrom blk n j
```

#### `mem_historyUptoFrom_self`

*theorem, `Causality.lean`*

```lean
theorem mem_historyUptoFrom_self {n : ℕ} {b : BlockId} : b ∈ historyUptoFrom blk n b
```

#### `historyUptoFrom_mono`

*theorem, `Causality.lean`*

```lean
theorem historyUptoFrom_mono {m n : ℕ} (h : m ≤ n) (b : BlockId) :
    historyUptoFrom blk m b ⊆ historyUptoFrom blk n b
```

More fuel never loses anything.

#### `reaches_of_mem_historyUptoFrom`

*theorem, `Causality.lean`*

```lean
theorem reaches_of_mem_historyUptoFrom {n : ℕ} {b i : BlockId}
    (h : i ∈ historyUptoFrom blk n b) : ReachesFrom blk b i
```

**Soundness.** Anything the fuelled search finds really is reachable.

#### `mem_historyFrom_self`

*theorem, `Causality.lean`*

```lean
theorem mem_historyFrom_self {b : BlockId} : b ∈ historyFrom blk b
```

A block lies in its own causal history.

#### `mem_historyUpto_of_reaches`

*theorem, `Causality.lean`*

```lean
theorem mem_historyUpto_of_reaches (C : CausalStructure blk ids)
    {n : ℕ} {b i : BlockId} (hb : b ∈ ids)
    (hn : (blk b).round ≤ n) (h : ReachesFrom blk b i) :
    i ∈ historyUptoFrom blk n b
```

**Completeness**, with the fuel accounted for. A path drops the round by one per step, so `round b` steps exhaust it; the base case is the derived `refs_empty_of_round_zero`.

#### `mem_history_iff`

*theorem, `Causality.lean`*

```lean
theorem mem_history_iff (C : CausalStructure blk ids) {b i : BlockId} (hb : b ∈ ids) :
    i ∈ historyFrom blk b ↔ ReachesFrom blk b i
```

**The representation is faithful.** For a block of the population, membership of `historyFrom` and reachability are the same thing.

#### `history_subset_ids`

*theorem, `Causality.lean`*

```lean
theorem history_subset_ids (C : CausalStructure blk ids)
    {b : BlockId} (hb : b ∈ ids) : historyFrom blk b ⊆ ids
```

Histories stay inside the population.

#### `history_subset_of_reaches`

*theorem, `Causality.lean`*

```lean
theorem history_subset_of_reaches (C : CausalStructure blk ids) {c b : BlockId} (hc : c ∈ ids)
    (h : ReachesFrom blk c b) : historyFrom blk b ⊆ historyFrom blk c
```

Histories nest along reachability.

#### `mem_history_succ_iff`

*theorem, `Causality.lean`*

```lean
theorem mem_history_succ_iff (C : CausalStructure blk ids)
    {b : BlockId} (hb : b ∈ ids) {i : BlockId} :
    i ∈ historyFrom blk b ↔ i = b ∨ ∃ j ∈ (blk b).refs, i ∈ historyFrom blk j
```

The one-step unfolding: a history is its block, plus the histories of its references. The predecessor condition reconciles the fuel.

#### `round_le_of_mem_history`

*theorem, `Causality.lean`*

```lean
theorem round_le_of_mem_history (C : CausalStructure blk ids) {b i : BlockId} (hb : b ∈ ids)
    (hi : i ∈ historyFrom blk b) : (blk i).round ≤ (blk b).round
```

Causal history runs downward, in the `Finset` form.

#### `eq_of_mem_history_of_round_eq`

*theorem, `Causality.lean`*

```lean
theorem eq_of_mem_history_of_round_eq (C : CausalStructure blk ids) {b i : BlockId} (hb : b ∈ ids)
    (hi : i ∈ historyFrom blk b) (hround : (blk i).round = (blk b).round) : i = b
```

Nothing in a block's history sits at the block's own round except the block itself.

#### `mem_refs_of_mem_history_of_round_succ`

*theorem, `Causality.lean`*

```lean
theorem mem_refs_of_mem_history_of_round_succ (C : CausalStructure blk ids)
    {b i : BlockId} (hb : b ∈ ids)
    (hi : i ∈ historyFrom blk b) (hround : (blk i).round + 1 = (blk b).round) :
    i ∈ (blk b).refs
```

**The layer one below is exactly the reference set.**

#### `mem_history_of_mem_refs`

*theorem, `Causality.lean`*

```lean
theorem mem_history_of_mem_refs (C : CausalStructure blk ids) {b j : BlockId} (hb : b ∈ ids)
    (hj : j ∈ (blk b).refs) : j ∈ historyFrom blk b
```

A block's references lie in its history, one step down.

#### `refl`

*theorem, `CausalHistory.lean`*

```lean
theorem refl {c : BlockId} : Reaches U c c
```

Every block is in its own causal history.

#### `single`

*theorem, `CausalHistory.lean`*

```lean
theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j
```

A direct reference is one step of causal history.

#### `trans`

*theorem, `CausalHistory.lean`*

```lean
theorem trans {a b c : BlockId} (h₁ : Reaches U a b) (h₂ : Reaches U b c) : Reaches U a c
```

Causal history composes. This is what glues `c → i` onto `i` reaches `b` at the end of both branches of T3.

#### `of_mem_refs`

*theorem, `CausalHistory.lean`*

```lean
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b
```

Prepend a direct reference: if `i` references `j` and `j` reaches `b`, then `i` reaches `b`. The exact shape T3's inductive step needs.

#### `mem_ids_of_reaches`

*theorem, `CausalHistory.lean`*

```lean
theorem mem_ids_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) : b ∈ U.ids
```

Causal history stays inside the universe: completeness propagates along every step.

#### `reaches_self_ancestor`

*theorem, `CausalHistory.lean`*

```lean
theorem reaches_self_ancestor {u : Validator}
    (hu : u ∈ (Correct : Finset Validator)) {c b : BlockId}
    (hc : c ∈ U.ids) (hb : b ∈ U.ids)
    (hcc : (U.block c).creator = u) (hbc : (U.block b).creator = u)
    (hle : (U.block b).round ≤ (U.block c).round) :
    Reaches U c b
```

**The self-parent chain.** A correct author's blocks form a single descending chain under P3′: any of its blocks reaches any earlier one.

The walk needs no production hypothesis — each step's target *exists* because the reference exists (P3′ supplies a same-creator reference, P1 puts it one round down, completeness keeps it in the universe) — and it lands on the right block because a correct author has only one block per round (T1). This is the backbone of the rotation-inclusion argument (report §11.5): a straggler's block is woven into the common cone not by per-round coverage but by its author's own chain, the moment the author leads a slot.

This is the one result here the structural layer cannot state: it consumes the self-parent clause and non-equivocation, both of which are properties of the *Byzantine* validity notion.

#### `round_le_of_reaches`

*theorem, `CausalHistory.lean`*

```lean
theorem round_le_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round
```

**T2.** Causal history runs downward in rounds: anything `c` reaches sits at a round no greater than `c`'s.

This is the substantive half of T2 — reflexivity, single steps and transitivity are inherited from `ReflTransGen`. It rests on `spec.md` §3.2's predecessor condition, which is the second field of the universe's `CausalStructure`.

#### `View.mem_of_reaches`

*theorem, `CausalHistory.lean`*

```lean
theorem View.mem_of_reaches {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {c b : BlockId}
    (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids
```

**T6a.** Causal history never escapes a view.

#### `View.exists_reaches_iff`

*theorem, `CausalHistory.lean`*

```lean
theorem View.exists_reaches_iff {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {P : BlockId → Prop} {c : BlockId}
    (hc : c ∈ V.ids) :
    (∃ b, b ∈ V.ids ∧ P b ∧ Reaches U c b) ↔ (∃ b, P b ∧ Reaches U c b)
```

**T6a, in the form the commit rules consume.** Asking "is there a `P`-block in `c`'s causal history?" gives the same answer whether or not the search is confined to the view. Restricting to `V` changes nothing, because the answer could never have lain outside it.

This is what makes a view-relative certificate check well defined: two validators with different views but the same anchor cannot disagree.

#### `mem_history_iff`

*theorem, `History.lean`*

```lean
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i
```

**The representation is faithful** (`dos-equivocation-and-growth.md` §7 S6). For a block of the universe, membership of `history` and reachability are the same thing.

#### `mem_history_self`

*theorem, `History.lean`*

```lean
theorem mem_history_self {b : BlockId} : b ∈ history U b
```

A block lies in its own causal history.

#### `history_subset_ids`

*theorem, `History.lean`*

```lean
theorem history_subset_ids {b : BlockId} (hb : b ∈ U.ids) : history U b ⊆ U.ids
```

Histories stay inside the universe.

#### `history_subset_of_reaches`

*theorem, `History.lean`*

```lean
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c
```

Histories nest along reachability — the `Finset` form of transitivity, and what makes D12 one line.

#### `mem_history_succ_iff`

*theorem, `History.lean`*

```lean
theorem mem_history_succ_iff {b : BlockId} (hb : b ∈ U.ids) {i : BlockId} :
    i ∈ history U b ↔ i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ history U j
```

The one-step unfolding: a history is its block, plus the histories of its references. The fuel bookkeeping is what makes this need a proof rather than `rfl` — the recursion hands out `round b` steps, and each reference wants `round + 1` of its own, which the predecessor condition reconciles.

#### `round_le_of_mem_history`

*theorem, `History.lean`*

```lean
theorem round_le_of_mem_history {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b) :
    (U.block i).round ≤ (U.block b).round
```

Causal history runs downward (T2), in the `Finset` form.

#### `eq_of_mem_history_of_round_eq`

*theorem, `History.lean`*

```lean
theorem eq_of_mem_history_of_round_eq {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round = (U.block b).round) : i = b
```

Nothing in a block's history sits at the block's own round except the block itself: a reference step drops the round strictly.

#### `mem_refs_of_mem_history_of_round_succ`

*theorem, `History.lean`*

```lean
theorem mem_refs_of_mem_history_of_round_succ {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round + 1 = (U.block b).round) :
    i ∈ (U.block b).refs
```

**The layer one below is exactly the reference set.** Anything in `b`'s history at round `round b - 1` is a direct reference of `b`.

#### `mem_history_of_mem_refs`

*theorem, `History.lean`*

```lean
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b
```

A block's references lie in its history, one step down.

#### `mem_authorsIn`

*theorem, `Support.lean`*

```lean
theorem mem_authorsIn {s : Finset BlockId} {v : Validator} {n : ℕ} :
    v ∈ authorsIn U s n ↔ ∃ b ∈ s, (U.block b).round = n ∧ (U.block b).creator = v
```

Membership in `authorsIn`, unfolded.

#### `mem_blocksAt`

*theorem, `Support.lean`*

```lean
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n
```

Membership in `blocksAt`, unfolded.

#### `mem_authorsAt`

*theorem, `Support.lean`*

```lean
theorem mem_authorsAt {v : Validator} {n : ℕ} :
    v ∈ authorsAt U n ↔ ∃ i ∈ U.ids, (U.block i).round = n ∧ (U.block i).creator = v
```

Membership in `authorsAt`, unfolded: an author of a round is anyone with a block there.

#### `creators_refs_subset_authorsAt`

*theorem, `Support.lean`*

```lean
theorem creators_refs_subset_authorsAt {c : BlockId} {n : ℕ}
    (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    creatorsOf U.block (U.block c).refs ⊆ authorsAt U n
```

The creators of a round-`(n+1)` block's references all hold round-`n` blocks. This is what confines a round-`(r+2)` block's choices to the same pool the threshold is measured against.

#### `exists_mem_refs_of_correct_support_of_card`

*theorem, `Support.lean`*

```lean
theorem exists_mem_refs_of_correct_support_of_card
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hT_correct : ∀ v ∈ T, v ∈ (Correct : Finset Validator))
    (hcard : F.f + 1 ≤ T.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q
```

**The hitting lemma, uniform form.** `f+1` correct backers always suffice: a round-`(n+1)` block names `n - f` of at most `n` participating authors, so it misses at most `f`.

#### `reaches_pred_of_round_le`

*theorem, `Support.lean`*

```lean
theorem reaches_pred_of_round_le {P : BlockId → Prop} {N : ℕ}
    (hbase : ∀ c ∈ U.ids, (U.block c).round = N → ∃ b, P b ∧ Reaches U c b)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : N ≤ (U.block c).round) :
    ∃ b, P b ∧ Reaches U c b
```

**Propagation.** Reaching something is inherited upward: if every block at round `N` reaches a `P`-block, so does every block above `N`.

Shared by T3 and M2, both of which are otherwise just a base case. The step needs nothing but nonempty references and transitivity — height is carried by `Reaches` alone.

#### `reaches_of_correct_support`

*theorem, `Support.lean`*

```lean
theorem reaches_of_correct_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hp : (authorsAt U (r + 1)).card + F.f + 1 ≤ S.card + Fintype.card Validator)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b
```

**Coverage, participation-sensitive form.** A block backed by `p + f + 1 - n` correct round-`(r+1)` validators is reached by every round-`(r+2)` block.

The `P`-instance of the hitting lemma where every target references `b`.

#### `reaches_of_correct_support_of_card`

*theorem, `Support.lean`*

```lean
theorem reaches_of_correct_support_of_card
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hcard : F.f + 1 ≤ S.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b
```

**Coverage, uniform form.** `f+1` correct supporters always suffice.

This is the form to use when supporters come from a quorum rather than from counting — see T3, where n−f distinct creators contain `f+1` correct ones by `card_inter_correct_of_quorum`.

#### `mem_supporters`

*theorem, `Support.lean`*

```lean
theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v
```

Membership in `supporters`, unfolded: a supporter has a round-`n` block referencing `b`.

#### `correctSupporters_subset`

*theorem, `Support.lean`*

```lean
theorem correctSupporters_subset {b : BlockId} {n : ℕ} :
    correctSupporters U b n ⊆ supporters U b n
```

Correct supporters are supporters.

#### `correctSupporters_correct`

*theorem, `Support.lean`*

```lean
theorem correctSupporters_correct {b : BlockId} {n : ℕ} {v : Validator}
    (hv : v ∈ correctSupporters U b n) : v ∈ (Correct : Finset Validator)
```

And they are correct.

#### `mem_blames`

*theorem, `Support.lean`*

```lean
theorem mem_blames {L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ blames U L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∉ (U.block q).refs ∧ (U.block q).creator = v
```

Membership in `blames`, unfolded: a blamer has a round-`n` block that omits `L`.

#### `card_supporters_le_of_card_blames`

*theorem, `Support.lean`*

```lean
theorem card_supporters_le_of_card_blames {L : BlockId} {n : ℕ}
    (h : quorumCard Validator ≤ (blames U L n).card) :
    (supporters U L n).card ≤ 2 * F.f
```

**The counting core of M3.** A quorum of blamers caps the supporters at `2f`, one short of a quorum.

A correct validator sits on at most one side, so the overlap is confined to the Byzantine set: `|supporters| ≤ (3f+1) − (2f+1) + f = 2f`. Nothing about certificates enters, which is why this belongs here rather than beside the commit rules that consume it.

#### `mem_correctBlocksAt`

*theorem, `CommonCore.lean`*

```lean
theorem mem_correctBlocksAt {i : BlockId} {n : ℕ} :
    i ∈ correctBlocksAt U n ↔
      i ∈ U.ids ∧ (U.block i).round = n ∧ (U.block i).creator ∈ (Correct : Finset Validator)
```

Membership in `correctBlocksAt`, unfolded.

#### `exists_correct_common_support`

*theorem, `CommonCore.lean`*

```lean
theorem exists_correct_common_support {r : ℕ}
    (hp : quorumCard Validator ≤ (authorsAt U (r + 1)).card) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      (authorsAt U (r + 1)).card + F.f + 1
        ≤ (correctSupporters U bw (r + 1)).card + Fintype.card Validator
```

**T3a (Correct-support counting).** Some correct validator's round-`r` block is backed by enough correct round-`(r+1)` validators to satisfy the `p - 2f` coverage threshold.

Double counting: each correct round-`(r+1)` block names at least `(n-f) - b` correct round-`r` authors, and there are `l` such blocks spread over `c = n - b` correct validators, so some author `w` collects at least `l(n-f-b)/c`. The arithmetic obligation reduces to `c² ≤ f(l+c)`, which `l ≤ c` turns into `c ≤ 2f` — impossible, since `b ≤ f` and `n ≥ 3f+1` force `c ≥ 2f+1`. The same contradiction as at `n = 3f+1`, verbatim.

#### `exists_common_correct_ancestor`

*theorem, `CommonCore.lean`*

```lean
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw
```

**T3c (Common correct ancestor).** If any block exists at round `r+2`, some correct validator's round-`r` block lies in the causal history of *every* round-`(r+2)` block.

The only premise is that a round-`(r+2)` block exists — a fact about the DAG in hand, not an assumption that anyone makes progress. Its own reference quorum supplies the `2f+1` author bound T3a needs.

Note the statement mentions no `Finset BlockId` operation, so unlike T3a it does **not** require decidable equality on ids; the proof supplies that classically.

#### `reaches_of_quorum_support`

*theorem, `Persistence.lean`*

```lean
theorem reaches_of_quorum_support
    {b : BlockId} {r : ℕ}
    {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : quorumCard Validator ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b
```

**T3 (Persistence).** If `b` is referenced by a quorum of round-`(r+1)` blocks, every block at round `r+2` or later has `b` in its causal history.

Neither `b ∈ U.ids` nor `(U.block b).round = r` is assumed: both follow from the quorum hypothesis (`mem_ids_and_round_of_quorum_support`).

### The commit rule, and the ledger

#### `mem_certificates`

*theorem, `Mysticeti.lean`*

```lean
theorem mem_certificates {C L : BlockId} {r : ℕ} :
    C ∈ certificates U L r ↔ C ∈ U.ids ∧ (U.block C).round = r + 2 ∧ Certifies U C L
```

Membership in `certificates`, unfolded: a round-`r+2` block that certifies `L`.

#### `certificates_eq_empty_of_directSkip`

*theorem, `Mysticeti.lean`*

```lean
theorem certificates_eq_empty_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : certificates U L r = ∅
```

**M3.** A directly skipped block has **no certificate anywhere** in the universe — not merely none in some view.

With `2f+1` blamers, and correct validators unable to sit on both sides, the supporters number at most `(3f+1) - (2f+1) + f = 2f`. A certificate needs `2f+1` distinct vote-creators, and every voter among a round-`(r+2)` block's references is a genuine supporter, so no such block can exist.

Universe-wide is the right strength: it is why a skip needs no anchor to justify it, and it is what makes the indirect rule agree with the direct one (M4).

#### `not_directCommit_of_directSkip`

*theorem, `Mysticeti.lean`*

```lean
theorem not_directCommit_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : ¬ DirectCommit U L r
```

**M1.** No block is both directly committed and directly skipped.

Immediate from M3: a skip leaves no certificates at all, and a commit needs `2f+1` distinct certificate authors.

#### `exists_certificate_reaches_of_directCommit`

*theorem, `Mysticeti.lean`*

```lean
theorem exists_certificate_reaches_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 3 ≤ (U.block c).round) :
    ∃ C ∈ certificates U L r, Reaches U c C
```

**M2.** Once a block is directly committed, its certificate becomes unavoidable: every block from round `r+3` on has one in its causal history.

The bound is `r+3` and it is **tight**. Certificates sit at round `r+2`, and a round-`(r+2)` block's own references sit at `r+1`, so a round-`(r+2)` block that is not itself a certificate reaches none. One round above the certificates is needed before the intersection argument bites — the same phenomenon as T3's `r+2`.

This is what makes the indirect rule agree with the direct one, and it is why the slot schedule must space leaders at least 3 rounds apart: that is exactly what puts every anchor at round `≥ r+3`.

#### `certificates_nonempty_of_directCommit`

*theorem, `Mysticeti.lean`*

```lean
theorem certificates_nonempty_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r) : (certificates U L r).Nonempty
```

A direct commit needs `2f+1` distinct certificate authors, so in particular at least one certificate.

#### `eq_of_certificates_nonempty`

*theorem, `Mysticeti.lean`*

```lean
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂
```

**M5′ (certificate uniqueness).** A slot admits at most one *certifiable* block: if certificates exist for two round-`r` blocks by the same author, those blocks coincide.

Stronger than M5, and the form the indirect rule needs — the indirect rule commits on the strength of a *single* certificate lying in reach, not on a quorum of them.

The proof needs no relationship between the two certificates. Each names n−f distinct voters, so the two voter sets intersect in a correct `w` (T0'); `w`'s single round-`(r+1)` block votes for both (T1); and **distinctness** forbids one block referencing two round-`r` blocks by one author. That last step is the one place in the development where distinctness is indispensable.

The rounds need no hypothesis: a voter for `L₁` sits at round `r+1` and references it, which pins `L₁` to round `r`, and likewise for `L₂`.

#### `eq_of_directCommit_of_creator_eq`

*theorem, `Mysticeti.lean`*

```lean
theorem eq_of_directCommit_of_creator_eq {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂
```

**M5.** At most one block per slot is directly committed.

Now a corollary of M5′: a direct commit implies a certificate exists. Note the outer certificate-quorum intersection this proof used to perform is not needed — M5′ never requires the two certificates to be the same block.

#### `certificates_nonempty_of_certifiedIn`

*theorem, `Mysticeti.lean`*

```lean
theorem certificates_nonempty_of_certifiedIn {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U A L r) : (certificates U L r).Nonempty
```

A certificate in reach is, in particular, a certificate that exists. This is what lets M5′ compare an *indirect* commit against anything else.

#### `certifiedIn_of_directCommit`

*theorem, `Mysticeti.lean`*

```lean
theorem certifiedIn_of_directCommit {L : BlockId} {r : ℕ} (h : DirectCommit U L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    CertifiedIn U A L r
```

**M4, commit half.** A directly committed block is found by *every* anchor from round `r+3` on. This is M2 restated as the indirect rule's test, and it is why the slot schedule must space leaders at least three rounds apart — that spacing is exactly what puts every anchor in range.

#### `indirect_agrees_with_direct`

*theorem, `Mysticeti.lean`*

```lean
theorem indirect_agrees_with_direct {L : BlockId} {r : ℕ}
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    (DirectCommit U L r → CertifiedIn U A L r) ∧
      (DirectSkip U L r → ¬ CertifiedIn U A L r)
```

**M4.** Where the direct rule decides, the indirect rule agrees.

The asymmetry between the halves is worth noting. Commit needs the anchor to be far enough along (`r+3`), since the certificate must be *reachable*. Skip needs nothing at all, since there is no certificate anywhere to reach.

#### `certifiedIn_iff_of_view`

*theorem, `Mysticeti.lean`*

```lean
theorem certifiedIn_iff_of_view {V : View Validator BlockId Payload U} {A L : BlockId} {r : ℕ}
    (hA : A ∈ V.ids) :
    (∃ C, C ∈ V.ids ∧ C ∈ certificates U L r ∧ Reaches U A C) ↔ CertifiedIn U A L r
```

The indirect test is **view-independent**: a validator holding the anchor computes the same verdict from its own local DAG as from the whole universe.

T6a in action — the certificate could never have lain outside the view, so confining the search to it changes nothing. This is what stops two validators with different views but the same anchor from disagreeing.

#### `eligible_iff`

*theorem, `Mysticeti.lean`*

```lean
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 3 ≤ S.slotRound j
```

Eligibility, unfolded: an anchor must sit three rounds above the slot it decides — one for votes, one for certificates, one to separate them.

#### `lt_of_eligible`

*theorem, `Mysticeti.lean`*

```lean
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j
```

An eligible anchor is a later slot. Monotonicity is what carries it: were `j ≤ k`, the anchor's round could not exceed `k`'s, let alone clear its decision round.

This makes the `k < j` premises of `Decided` redundant. They are kept anyway: `decided_unique` recurses on them and hands them to `lt_trichotomy`, and re-deriving them at each use would be noise.

#### `eligible_of_lt_of_spacing`

*theorem, `Mysticeti.lean`*

```lean
theorem eligible_of_lt_of_spacing (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    {k j : ℕ} (h : k < j) : Eligible Validator k j
```

**Conservativity.** Under a schedule whose consecutive slots are three rounds apart — the `spacing` field this class used to carry — *every* later slot is eligible to anchor an earlier one, and the generalised premise implies the three-round one.

So the generalised `Decided` has exactly the constructors the three-round form has whenever three-round spacing holds: no derivation available before the change is unavailable after it. This is the three-round spacing bound, demoted from a consequence of the class to a consequence of a hypothesis.

#### `directCommit_of_directCommitIn`

*theorem, `Mysticeti.lean`*

```lean
theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectCommitIn U V L r) : DirectCommit U L r
```

**A view can only under-report.** Everything it sees is real, so a view-relative direct commit is a genuine one.

This one line is what lets all of Stage A be reused unchanged: M2, M4 and M5 are stated universe-level, and a validator's local judgement feeds straight into them.

#### `isLeaderBlock_of_decided`

*theorem, `Mysticeti.lean`*

```lean
theorem isLeaderBlock_of_decided {V : View Validator BlockId Payload U} {j : ℕ} {A : BlockId}
    (h : Decided U V j (some A)) : IsLeaderBlock U j A
```

Whatever route it took, a committed verdict names a genuine candidate for that slot. Needed because the agreement proof must feed another validator's anchor into the visibility lemma, which wants its round.

#### `anchor_eq`

*theorem, `Mysticeti.lean`*

```lean
theorem anchor_eq {W : Type*} {Dec : W → ℕ → Option BlockId → Prop}
    {Elig : ℕ → Prop} {k j j₂ : ℕ} {A A₂ : BlockId} {V₂ : W}
    (hkj : k < j) (helig : Elig j) (hkj₂ : k < j₂) (helig₂ : Elig j₂)
    (hj₂ : Dec V₂ j₂ (some A₂))
    (hmid₂ : ∀ i, k < i → i < j₂ → Elig i → Dec V₂ i none)
    (ihj : ∀ V v, Dec V j v → some A = v)
    (ihmid : ∀ i, k < i → i < j → Elig i → ∀ V v, Dec V i v → none = v) :
    j = j₂ ∧ A = A₂
```

**The anchor comparison.** Two indirect decisions for one slot each name an anchor, together with the premise that every eligible slot strictly between the slot and that anchor was decided `none`. Whichever anchor is the earlier is then decided `none` by the other side and `some` by its own, so the anchors coincide — and with them the blocks they name.

The statement carries no consensus content: `Dec` and `Elig` are arbitrary predicates, and the argument is only that two searches for the first decided slot above `k` cannot disagree when each certifies that nothing eligible below its own find was decided. Both commit rules consume it, five times between them, and stating it separately is what keeps their case analyses to one line per case.

#### `decided_unique`

*theorem, `Mysticeti.lean`*

```lean
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂
```

**M6 (agreement).** No two validators reach conflicting decisions for a slot, whatever views they hold and whichever routes they took.

As with T5 this is *no-conflicting-decision*: a validator that has not yet decided is not in disagreement.

Structural induction on the first derivation. Of the sixteen constructor pairings, fifteen close outright — every commit-versus-commit case by M5′, and the direct-versus-indirect crossings by cross-view M1, the visibility lemma, or M3. The one real case is *indirect commit against indirect skip*, settled by comparing the two anchors: if they coincide the IH forces the same anchor block, and otherwise the earlier anchor is covered by the *other* validator's intermediate-skip premise, which is exactly the sub-derivation the IH needs.

That is why "nearest anchor" had to be stated positively. The negative reading would carry no sub-derivation here, and the induction would have nothing to stand on.

**Why eligibility may not be view-relative.** Since the intermediate premise now ranges over eligible slots only, invoking the other validator's copy of it needs `Eligible k j` as a side condition — and what discharges it is *this* validator's own eligibility premise for the same pair. The two match because `Eligible` is a predicate on the slot pair alone: both derivations concern the same `k`, so they agree on which slots may anchor it. Were eligibility indexed by the decider — "an anchor far enough ahead *as far as I can see*" — the premises would not meet and this case would not close.

#### `decided_agree`

*theorem, `Mysticeti.lean`*

```lean
theorem decided_agree {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) :
    v₁ = v₂
```

**M6**, in the shape callers want: two validators' verdicts for a slot agree.

#### `eq_of_decided_commit`

*theorem, `Mysticeti.lean`*

```lean
theorem eq_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided U V₁ k (some L₁)) (h₂ : Decided U V₂ k (some L₂)) :
    L₁ = L₂
```

No two validators commit *different* blocks for one slot.

#### `not_decided_skip_of_decided_commit`

*theorem, `Mysticeti.lean`*

```lean
theorem not_decided_skip_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (h₁ : Decided U V₁ k (some L)) (h₂ : Decided U V₂ k none) :
    False
```

No validator commits a slot another has skipped. This is the shape that matters operationally: a committed block never has to be retracted.

#### `commitSeq_agree`

*theorem, `Mysticeti.lean`*

```lean
theorem commitSeq_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n
```

**The committed-leader sequence is agreed.** Two validators that have settled the first `n` slots — on whatever views, by whatever mix of direct and indirect routes — read off the same list of committed blocks.

#### `ledgerSet_mono`

*theorem, `Mysticeti.lean`*

```lean
theorem ledgerSet_mono {g : ℕ → Option BlockId} {n m : ℕ} (h : n ≤ m) :
    ledgerSet U g n ⊆ ledgerSet U g m
```

**Nothing is ever dropped.** The ledger only grows as more slots settle.

#### `ledgerSet_agree`

*theorem, `Mysticeti.lean`*

```lean
theorem ledgerSet_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    ledgerSet U g₁ n = ledgerSet U g₂ n
```

**Two validators output the same blocks.**

#### `outputAt_unique`

*theorem, `Mysticeti.lean`*

```lean
theorem outputAt_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂
```

**A block enters the ledger once.** Its position is not merely stable over time — there is no second slot it could have entered at.

#### `outputAt_agree`

*theorem, `Mysticeti.lean`*

```lean
theorem outputAt_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId} {b : BlockId} {k : ℕ}
    (h₁ : ∀ j, j < n → Decided U V₁ j (g₁ j))
    (h₂ : ∀ j, j < n → Decided U V₂ j (g₂ j))
    (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k
```

**And validators agree on which slot that is.**

### Delivery, growth, and coverage

#### `card_authorsAt_of_lt`

*theorem, `Liveness.lean`*

```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    quorumCard Validator ≤ (authorsAt U n).card
```

**L0 — the DAG is dense below its frontier.** If any block exists at round `r`, then *every* round `n < r` has at least `2f+1` distinct authors.

Downward induction on the gap `r - n`. The step is where the two lemmas above meet: the inductive hypothesis gives a quorum of authors one round higher, that quorum is nonempty so some block sits there, and `card_authorsAt_of_succ` walks it down one more round.

The induction runs on the gap rather than on `r` itself because the statement is not about `r`: nothing distinguishes the block's own round, and generalising over `n` is what lets the step re-enter at `n+1`.

#### `decided_mono`

*theorem, `Liveness.lean`*

```lean
theorem decided_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {v : Option BlockId} (h : Decided U V k v) :
    Decided U V' k v
```

**L2 — decisions are monotone in the view.** If `V ⊆ V'` then `Decided U V k v → Decided U V' k v`.

Induction on the derivation. The two direct cases are the monotonicity lemmas above; the two indirect cases rebuild themselves from the inductive hypotheses, carrying their `CertifiedIn` premises across unchanged.

#### `decided_full`

*theorem, `Liveness.lean`*

```lean
theorem decided_full {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided U V k v) : Decided U (View.full U) k v
```

**L3 — commit propagation.** Whatever any validator decides on any view, the same verdict holds on the full view.

Since the full view is every correct validator's eventual view (`liveness.md` §4.2), this *is* "all correct validators eventually reach the same decision".

#### `votesAt_of_synchronisedOn`

*theorem, `Liveness.lean`*

```lean
theorem votesAt_of_synchronisedOn (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) :
    VotesAt U T r L
```

Coverage gives the votes: the instantiation of `SynchronisedOn` at `n = r`, with `L` the one block singled out.

#### `certifiesAt_of_synchronisedOn`

*theorem, `Liveness.lean`*

```lean
theorem certifiesAt_of_synchronisedOn
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ T) :
    CertifiesAt U T r L
```

Coverage gives the certificates, through the vote layer: the `CertifiesAt` form of the lemma above.

#### `directCommit_of_certifiesAt`

*theorem, `Liveness.lean`*

```lean
theorem directCommit_of_certifiesAt
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2))
    (hc : CertifiesAt U T r L) :
    DirectCommit U L r
```

**The commit argument, stated once.** A quorum-sized `T` whose decision-round blocks all certify `L` directly commits it: each `v ∈ T` has a round-`(r+2)` block by production, it certifies by hypothesis, and `T`'s cardinality does the counting. Both pacing disciplines end here — the full-timeout one arriving through `certifiesAt_of_synchronisedOn`, the reactive one through `ReactiveM.certifies`.

#### `directCommit_of_leader_mem`

*theorem, `Liveness.lean`*

```lean
theorem directCommit_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**L4.** A slot with a correct leader, whose three rounds are populated and which sits after synchrony, is directly committed.

#### `directCommit_of_correct_leader`

*theorem, `Liveness.lean`*

```lean
theorem directCommit_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**L4 at `T := Correct`.** The original statement, recovered.

#### `directCommitIn_full`

*theorem, `Liveness.lean`*

```lean
theorem directCommitIn_full (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r
```

A universe-level direct commit is one the full view also sees.

#### `decided_of_leader_mem`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_leader_mem (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**L4, as a decision.** What L6 consumes and L3 propagates.

#### `decided_of_leader_of_populated`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_leader_of_populated (_hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**L4, against a horizon.** The form every capstone uses: production is available as a single hypothesis up to a horizon, and the three rounds L4 needs are read off it.

Stated separately because the capstones of report §§6–10 all reach L4 the same way — read production off at `slotRound k`, `+1` and `+2` — and doing that inline obscures which hypothesis is actually being consumed.

**Production is asked for over `T`, not over `Correct`.** The rule consumes only `T`-authored blocks, so requiring a block from every correct validator would be asking for more than is used; `PopulatedOn.mono` bridges the two for callers holding the stronger `Populated`. The weaker hypothesis is what lets the recurrence results run at a `T` that is a *proper* subset of `Correct` — correct validators outside `T` may be starved, partitioned or silent, and the ledger still commits, provided `T` itself is a quorum.

The subset hypothesis is now unused: with production asked over `T`, L4 needs nothing but the cardinality of `T`, which is what `commits_recur_on`'s comment already observed. It is kept in the signature because every capstone has it to hand and threading it documents the setting.

#### `decided_of_correct_leader`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

The same at `T := Correct`.

#### `decided_none_of_leader_absent`

*theorem, `Liveness.lean`*

```lean
theorem decided_none_of_leader_absent {V : View Validator BlockId Payload U}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none
```

**L5 — an absent leader is skipped.** If the slot-`k` leader has no block at its round, every view decides `none`.

#### `le_slotRound_slotAt`

*theorem, `Liveness.lean`*

```lean
theorem le_slotRound_slotAt (n : ℕ) : n ≤ S.slotRound (slotAt Validator n)
```

`slotAt n` names a slot at or past round `n` — the defining property of the index.

#### `slotAt_zero`

*theorem, `Liveness.lean`*

```lean
theorem slotAt_zero : slotAt Validator 0 = 0
```

Round `0` is served by slot `0`.

#### `commits_recur_on`

*theorem, `Liveness.lean`*

```lean
theorem commits_recur_on (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload T R k'
```

**L6 — commits recur.** For every slot `k` there is a later slot `k'` that **every** sufficiently grown synchronous DAG commits.

Note the conclusion quantifies over `U` and `N` *inside* the existential: the slot is fixed by the schedule alone, and any DAG grown past it commits it.

#### `commits_recur`

*theorem, `Liveness.lean`*

```lean
theorem commits_recur (fair : FairSchedule (Validator := Validator)) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload (Correct : Finset Validator) R k'
```

**L6 at `T := Correct`.** The original statement, recovered.

#### `decided_of_first_eligible_commit`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_first_eligible_commit {V : View Validator BlockId Payload U}
    {k j : ℕ} {A : BlockId}
    (helig : Eligible Validator k j)
    (hfirst : ∀ i, k < i → i < j → ¬ Eligible Validator k i)
    (hj : Decided U V j (some A)) :
    ∃ v, Decided U V k v
```

**The escape.** If `j` is committed and *nothing strictly between `k` and `j` is eligible to anchor `k`*, then `k` is decided outright: the intermediate-skip premise is vacuous, so there is no induction and no appeal to nearestness.

This is the fact that keeps pipelining live, and the one most easily overlooked. Slot `j - 1` sitting immediately below a committed `j` cannot anchor on `j` — one round on, inside its decision round — but it *can* anchor on `j + 2`, and neither `j` nor `j + 1` is eligible for it, so the premise is empty and the slot resolves at once. Under fair leader election `j + 2` is committed whenever `j` is, correct validators holding runs of `2f+1 ≥ 3` consecutive slots.

No hypothesis on the schedule, and none on synchrony: like L8 this is pure decision-relation combinatorics.

#### `decided_of_committed_above`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_committed_above
    (helig : ∀ a b : ℕ, a < b → Eligible Validator a b)
    {V : View Validator BlockId Payload U} {n : ℕ} {A : BlockId}
    (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → ∃ v, Decided U V i v
```

**L8.** Given a committed slot, every slot below it is decided — provided every later slot may anchor an earlier one.

No synchrony, no timing, no fairness: this is pure decision-relation combinatorics, which is why it is worth isolating. The work is choosing the *nearest* committed slot above `i` and reading the intermediate premise off the induction hypothesis — an intermediate slot is decided by induction, and cannot be decided `some` without contradicting nearestness, so it is decided `none`.

Note the proof never consults the direct rules. It does not need to: where the direct rule commits, M2 puts the certificate in reach of the anchor, so the indirect branch taken here agrees with it — and M6 guarantees as much in any case.

#### `all_decided_below_of_spacing`

*theorem, `Liveness.lean`*

```lean
theorem all_decided_below_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ n, k ≤ n ∧ R ≤ S.slotRound n ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound n + 2 ≤ N →
        ∀ i, i ≤ n → ∃ v, Decided U (View.full U) i v
```

**L8 under the old three-round spacing.** Combining L6 with L8: for every slot `k` there is a slot `n ≥ k` such that a sufficiently grown synchronous DAG decides *every* slot up to `n` — so the ledger does not stall below it.

`hsp` is the field the `Slots` class used to carry. A pipelined or multi-leader schedule does not satisfy it, and the counterexample above is why this is stated conditionally rather than dropped.

#### `decided_below_of_committed_run`

*theorem, `Liveness.lean`*

```lean
theorem decided_below_of_committed_run {V : View Validator BlockId Payload U} {b n : ℕ}
    (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided U V i v
```

**P7′ — a committed run decides everything below it.**

This is L8 with `helig` removed, and it is the shape liveness actually needs. The hypotheses are:

* `hrun` — the slots `b … n` are all committed; * `hspan` — every slot below `b` has `n` as an *eligible* anchor, which under pipelining just says the run spans three rounds, i.e. `n ≥ b + 2`.

Then every slot below `b` is decided. No synchrony, no timing, no fairness, and no hypothesis on the schedule — those enter only when discharging `hrun`, which L4 does for a run of `T`-led slots.

Two changes from L8 make it work. The anchor is the nearest **eligible** committed slot rather than the nearest committed one, which is what removes `helig`; and an eligible intermediate is shown to lie below `b` — if it were in `b … n` it would be committed by `hrun`, contradicting minimality — which is what lets the induction hypothesis reach it.

That second step is the whole content. It is why three consecutive commits suffice and why a *single* commit does not: the slots just below `b` have no eligible intermediates at all (their eligible range starts inside the run), so they resolve outright, and everything lower descends onto them.

#### `all_decided_below_of_fairRun`

*theorem, `Liveness.lean`*

```lean
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hspan : SpansEligible (Validator := Validator) c)
    (fair : FairRunOn T c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v
```

**L10.** For every slot `k` there is a `b ≥ k` such that every slot below `b` is decided, in any sufficiently grown synchronous DAG.

This is what "the ledger does not stall" means operationally: `commitSeq` reads verdicts in slot order and halts at the first undecided slot, so a prefix of decided slots growing without bound is exactly the ledger advancing. Contrast L6, which gives infinitely many *commits* while saying nothing about the gaps between them.

### Time: GST, and the rated bounds

#### `backoff_ge_of_rate`

*theorem, `Quantitative.lean`*

```lean
theorem backoff_ge_of_rate {timeout : ℕ → ℕ} (hrate : Rated timeout) (m : ℕ) :
    ∀ n, m ≤ n → m ≤ timeout n
```

**A rated backoff clears any threshold by the threshold itself.**

Monotonicity is not used here — the bound at `n` comes from `n` itself, so it cannot lapse afterwards — where the retired existential form needed `Monotone` to turn one clearing round into all later ones.

#### `commits_recur_within`

*theorem, `Quantitative.lean`*

```lean
theorem commits_recur_within (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k (slotAt Validator R) ≤ k' ∧ k' < max k (slotAt Validator R) + w ∧
      R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload T R k'
```

**Q4, the schedule half.** L6 with the committing slot **bounded**.

L6 says a committing slot exists beyond any `k`; this says it lies within `w` slots of `max k R`. Everything else is unchanged — the quantifier order, the `∀ U D N` inside the existential, the horizon condition — and the DAG-facing content is `commits_recur_on`'s, reproduced here only because the slot has to be named by `FairWithin` rather than `FairScheduleOn`.

The starting point is not slack: the slot must clear both the caller's `k` and the synchrony round `R`. The old statement wrote that as `max k R`, relying on `3 * k ≤ slotRound k` to make slot `R` sit past round `R`. A monotone schedule gives no such coincidence — under `m` leaders per round slot `R` is around round `R / m` — so the slot past round `R` is named explicitly by `slotAt Validator R`. Under three-round spacing `slotAt R ≤ R`, so the bound is no weaker than it was.

#### `slotRound_le_of_boundedSpacing`

*theorem, `Quantitative.lean`*

```lean
theorem slotRound_le_of_boundedSpacing {s : ℕ}
    (hs : BoundedSpacing (Validator := Validator) s) (k d : ℕ) :
    S.slotRound (k + d) ≤ S.slotRound k + s * d
```

Bounded spacing accumulates: `d` slots on costs at most `s * d` rounds.

#### `commits_recur_by_round`

*theorem, `Quantitative.lean`*

```lean
theorem commits_recur_by_round {s : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (fair : FairWithin T w)
    (hs : BoundedSpacing (Validator := Validator) s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k (slotAt Validator R)) + s * w ∧
      R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (max k (slotAt Validator R)) + s * w + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L)
```

**Q4 in rounds.** The committing slot's round is bounded, so the horizon a DAG must reach before it is guaranteed to commit becomes an explicit number rather than "far enough".

Read the two summands: `slotRound (max k (slotAt R))` is where the search starts, and `s * w` is the worst-case cost of walking to the next `T`-leader. The `+ 2` is the certificate round — L4's `r + 2`, unchanged.

At the standard settings — round-robin over `3f+1` so `w = f + 1`, and slots every three rounds so `s = 3` — this reads `3 * (f + 1)` rounds past the starting slot, which is the concrete latency figure `liveness.md` §8 Q4 asks for.

**This bound is blind to multiple leaders.** `BoundedSpacing s` says consecutive slots are at most `s` rounds apart, and with `m` leaders sharing a round that is still `s = 1`, not `0` — only one step in `m` advances the round, which `BoundedSpacing` cannot see. So `s * w` reads `w` rounds for `w` slots however large `m` is. A bound that improves with `m` needs the schedule to expose it, which `Slots.uniform` does; this statement is kept because it is the only one that says anything about an irregular schedule.

### The pacing structures, and the delivery they induce

#### `convergesWithin_iff_bounded`

*theorem, `ViewPace.lean`*

```lean
theorem convergesWithin_iff_bounded
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t) :
    ConvergesWithin holds T gst bound ↔
      (∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t →
        ∃ d ≤ bound, holds w t ⊆ holds v (t + d))
```

**The factoring.** Under monotone holdings, convergence within a bound and bounded eventual convergence are the same condition.

#### `reached`

*theorem, `ViewPace.lean`*

```lean
theorem reached (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, ∀ v ∈ T, n ≤ pc.top v
```

**Every reliable validator reaches every round below the horizon** — with `T` a quorum, nobody in `T` is stuck. The induction: each `w ∈ T` reached round `n`, so holds its own block there; `holds_mono` carries it to the common time `max (latest n) gst`; `converges` puts a quorum of distinct round-`n` authors in `v`'s hands; `advances` fires.

Proved on the trunk, so every pacing discipline inherits it: nothing here mentions a floor, a ceiling, or a timeout.

#### `populatedOn`

*theorem, `ViewPace.lean`*

```lean
theorem populatedOn (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, PopulatedOn U T n
```

**Production, once for every discipline**: a round a validator got to is a round it built in.

#### `history_subset_holds`

*theorem, `ViewPace.lean`*

```lean
theorem history_subset_holds (pc : PaceCore U T N) {v : Validator} (hv : v ∈ T)
    {t : ℕ} {b : BlockId} (hb : b ∈ pc.holds v t) :
    history U b ⊆ pc.holds v t
```

**Closure, iterated**: a held block's whole causal cone is held. The step is `holds_closed`; the induction runs along the reachability chain.

#### `mem_viewAt`

*theorem, `ViewPace.lean`*

```lean
theorem mem_viewAt (pc : PaceCore U T N) {v : Validator} {t : ℕ} {b : BlockId}
    (hb : b ∈ pc.holds v t) : b ∈ (pc.viewAt v t).ids
```

What a validator holds is in the view it generates.

#### `viewAt_ids`

*theorem, `ViewPace.lean`*

```lean
theorem viewAt_ids (pc : PaceCore U T N) {v : Validator} (hv : v ∈ T) (t : ℕ) :
    (pc.viewAt v t).ids = pc.holds v t
```

**The view a validator holds is exactly what it holds.** Under closure the causal closure is a no-op, so `viewAt` adds nothing: a reliable validator's view *is* its holdings, and the local liveness statement is about the blocks the validator actually has. Without `holds_closed` the inclusion runs one way only, and `viewAt` would be the closure of a validator's fragments rather than its view.

#### `holds_roundBlocks`

*theorem, `ViewPace.lean`*

```lean
theorem holds_roundBlocks (pc : PaceCore U T N) {n : ℕ} (hn : n ≤ N)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = n →
      b ∈ pc.holds v (pc.latest n + pc.delay)
```

**Delivery, in the form the local argument consumes.** Past GST, every reliable validator holds every `T`-authored round-`n` block by `latest n + delay`: its author holds it when built, `latest` is a common time for the whole round, and convergence carries it across.

#### `decided_local_of_certifiesAt`

*theorem, `ViewPace.lean`*

```lean
theorem decided_local_of_certifiesAt [S : Slots Validator] {k : ℕ} {L : BlockId}
    (pc : PaceCore U T N) (hcard : quorumCard Validator ≤ T.card)
    (hN : S.slotRound k + 2 ≤ N)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u (S.slotRound k + 2))
    (hL : IsLeaderBlock U k L) (hcert : CertifiesAt U T (S.slotRound k) L) :
    ∀ v ∈ T,
      Decided U (pc.viewAt v (pc.latest (S.slotRound k + 2) + pc.delay)) k (some L)
```

**The local commit argument, stated once.** Given a leader block, a quorum-sized `T` whose decision-round blocks all certify it, and post-GST builds, every reliable validator decides the slot **on its own view**: the counting of `directCommit_of_certifiesAt` run inside `viewAt v t` rather than inside the universe, with the delivery lemma putting the certificates there.

Stated on the trunk, so both pacing disciplines inherit it — the full-timeout one supplying `CertifiesAt` through coverage, the reactive one through its certificate wait.

#### `drift_collapse`

*theorem, `ViewPace.lean`*

```lean
theorem drift_collapse {n : ℕ} (hn : n ≤ N)
    (htop : ∀ u ∈ T, n ≤ pc.top u)
    (hg : ∀ u ∈ T, pc.gst ≤ pc.built u n) :
    ∀ v ∈ T, ∀ w ∈ T, pc.built v n ≤ pc.built w n + (pc.delay + pc.proc)
```

**Drift collapses, from any starting value.** At any round whose builds all lie past GST, the spread is at most `delay + proc`, whatever it was before: the earliest builder's block reaches the laggard within `delay`, and catch-up converts the sighting into entry within `proc`. `htop` guards the rounds the statement reads; `driftOn_of_catchup` discharges it from the quorum bound.

#### `driftOn_of_catchup`

*theorem, `ViewPace.lean`*

```lean
theorem driftOn_of_catchup {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : pc.gst ≤ R)
    (hle : ∀ u ∈ T, ∀ n ≤ pc.top u, n ≤ pc.built u n) :
    DriftOn pc.built T R (pc.delay + pc.proc) N
```

The collapsed spread, in the form the coverage argument consumes — with no base hypothesis anywhere. `hle` is the discipline's `le_built` (rounds advance real time), which each extension proves from its own schedule clauses; everything else is the trunk's.

#### `covers_of_converges`

*theorem, `ViewPace.lean`*

```lean
theorem covers_of_converges {n : ℕ} (hn : n < N)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = n + 1)
    {a : BlockId} (ha : a ∈ U.ids) (haT : (U.block a).creator ∈ T)
    (har : (U.block a).round = n)
    (hgst : vp.gst ≤ vp.built ((U.block a).creator) n)
    (hearly : vp.built ((U.block a).creator) n + vp.delay ≤
      vp.built ((U.block c).creator) (n + 1)) :
    a ∈ (U.block c).refs
```

**The separation, on this route** — V1's content over the partial schedule. The fused covers-shape (*a `T`-block built after GST and early enough is referenced*) is derivable from `converges` and `references` alone: the block is in its author's hands when built (`holds_own`), reaches the builder within `delay` (`converges`), is still there when the builder acts (`holds_mono`), and is therefore referenced (`references`). No counting, no drift, no waiting rule — those enter only when the *hypothesis* `built … + delay ≤ built … (n+1)` must itself be discharged, which is the race the drift argument wins.

This is where report §4.3's claim that the network's whole contribution is one sentence about views is discharged on the route the development keeps: `converges` mentions no blocks, rounds or references, and the step from views to references is the protocol's clause P7.

#### `reached`

*theorem, `ViewPace.lean`*

```lean
theorem reached (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, ∀ v ∈ T, n ≤ vp.top v
```

**Production, with no deadline to beat.** Every round below the horizon is populated, from genesis, view convergence and the progress rule — and from nothing else. No drift, no backoff, no `timeout`, and no schedule side condition of any kind.

The step is the familiar one with the deadline removed. Each `w ∈ T` reached round `n` (induction hypothesis), so it has a block there and holds it from `built w n`; `holds_mono` carries that forward to `max (latest n) gst`, a single time serving every `w` at once; `converges` puts all of them in `v`'s hands by `max (latest n) gst + delay`. That is a quorum of distinct authors, so `advances` fires and `v` is past round `n` — whereupon `built_of_le_top` supplies its round-`n+1` block.

**Why no side condition survives.** Over a total build schedule the quorum must arrive by `built v (n+1)`, a time fixed before the run, and a condition on the round straddling GST is what makes that deadline meetable. Here the arrival time is not compared with anything: `advances` takes the quorum at whatever time it appears. A schedule that raced ahead of the network pre-GST is not excluded by hypothesis — it is not expressible, because a validator that never held a quorum at round `n` never reached round `n+1`.

#### `populatedOn`

*theorem, `ViewPace.lean`*

```lean
theorem populatedOn (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) :
    ∀ n ≤ N, PopulatedOn U T n
```

**Production**, inherited from the trunk (`PaceCore.populatedOn`).

#### `driftOn_of_catchup`

*theorem, `ViewPace.lean`*

```lean
theorem driftOn_of_catchup (vp : ViewPace U T N) {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R) :
    DriftOn vp.built T R (vp.delay + vp.proc) N
```

**Drift is derived**, from the trunk's catch-up rule: the collapsed spread `delay + proc`, from any `R` past GST, with **no hypothesis about the start**. The quorum bound enters because the collapse reads builds at rounds every `T`-validator reached, which is `reached`'s conclusion; the schedule contributes only `le_built` (rounds advance real time), placing those builds past GST.

#### `synchronisedOn_of_driftOn`

*theorem, `ViewPace.lean`*

```lean
theorem synchronisedOn_of_driftOn {R D : ℕ}
    (hD : DriftOn vp.built T R D N) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vp.delay ≤ vp.timeout n) :
    SynchronisedOn U T R
```

**The coverage engine** — the race, run against an *arbitrary* drift bound `D`. The guards come out of `le_top_of_built`: a block at round `n+1` authored by `v` puts `n + 1 ≤ top v`, so `waits` and `le_built` apply where they are used, and the straddling case cannot arise — coverage is claimed only from `R`, and `gst ≤ R ≤ n ≤ built w n`.

This needs neither production, nor the quorum bound, nor `T ⊆ Correct`: `references` and `holds_own` are stated over any block a validator authored, so there is nothing to identify by non-equivocation. The headline (`synchronisedOn_of_converges`) discharges `hD` internally from catch-up, which costs the quorum; this form is kept for reliable sets below the quorum, where drift must be supplied from outside (`reliable_set_is_forced_pace` runs on a two-member `T`).

#### `synchronisedOn_of_converges`

*theorem, `ViewPace.lean`*

```lean
theorem synchronisedOn_of_converges {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    SynchronisedOn U T R
```

**Reference coverage, drift-free.** From any `R` past GST, once the timeout clears `2Δ + proc`, every reliable round-`n+1` block references every reliable round-`n` block. No drift hypothesis and no start spread: the spread at `R` is whatever catch-up left, which is `delay + proc` (`driftOn_of_catchup`), and the race of the engine is run against that constant. The quorum bound is consumed here — the collapse reads builds at rounds `reached` guarantees — where the engine alone needs none.

#### `commits_recur_via_pace`

*theorem, `ViewPace.lean`*

```lean
theorem commits_recur_via_pace (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (vp : ViewPace U T N),
        vp.gst ≤ R →
        (∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L)
```

**The liveness spine** (V17): commits recur, with the seed at round `0`, where it is genesis, and no schedule side condition of any kind.

What is assumed divides cleanly. The network contributes `converges` and `vp.gst ≤ R`. The protocol contributes `built_of_le_top` at round `0` (genesis), `advances` (the pacemaker does not stall), `catchup` (seeing a round is entering it), `references` (P7) and `waits` (P9). No drift appears: the backoff clears the constant `2Δ + proc`, and the spread — whatever it was at the start — is the collapsed `Δ + proc` by the time coverage reads it. Production needs none of the timing clauses.

#### `decided_local`

*theorem, `ViewPace.lean`*

```lean
theorem decided_local (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (vp.viewAt v (vp.latest (S.slotRound k + 2) + vp.delay)) k (some L)
```

**Liveness is local** (V18): past GST, every reliable validator decides the slot **on its own view**, by an explicit time.

The hypotheses are those of the main line — GST and the constant backoff — and nothing further. The proof is the counting argument of L4 run inside `viewAt v t` rather than inside the universe: coverage makes every `T`-authored decision-round block a certificate (`certifiesAt_of_synchronisedOn`), production supplies one per reliable validator, and the delivery lemma puts all of them in `v`'s view at once. `decided_full` recovers the global statement, so this strictly strengthens it.

#### `commits_recur_local`

*theorem, `ViewPace.lean`*

```lean
theorem commits_recur_local (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ) (vp : ViewPace U T N),
        vp.gst ≤ R → (∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ ∀ v ∈ T,
          Decided U (vp.viewAt v (vp.latest (S.slotRound k' + 2) + vp.delay))
            k' (some L)
```

**The liveness spine, localised** (V18): commits recur, and at the recurring slot every reliable validator decides **on its own view**.

The quantifier order of `commits_recur_via_pace` is preserved --- the slot is fixed by the schedule and the round bound alone, before any execution is named --- and the conclusion is the local one. Note what is absent: `T ⊆ Correct` is not needed. The global spine threads it through `commits_recur_on`, whose production comes from L1 over `Correct`; here production is the pacing structure's own, over `T` directly, so the hypothesis has nothing left to do.

#### `decided_of_local`

*theorem, `ViewPace.lean`*

```lean
theorem decided_of_local (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**The global statement is a corollary**, so V18 strictly strengthens the main line: a reliable validator exists (the quorum bound is nonvacuous), it decides locally, and `decided_full` (L3) lifts its verdict to the full view. `decided_of_leader_mem` reaches the same conclusion without ever naming a validator's own view; this route names one.

#### `exists_reliable_parent`

*theorem, `ViewPace.lean`*

```lean
theorem exists_reliable_parent
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) (hr : 0 < (U.block b).round) :
    ∃ a ∈ (U.block b).refs, a ∈ U.ids ∧ (U.block a).creator ∈ T ∧
      (U.block a).round + 1 = (U.block b).round
```

**Every valid non-genesis block carries a reliable parent.** Its reference quorum has at least `n − 2f ≥ f + 1` authors in any quorum-sized `T`; one is exhibited. Nothing about pacing enters: this is a fact about validity and cardinalities alone.

#### `PaceCore.round_le_top_succ`

*theorem, `ViewPace.lean`*

```lean
theorem PaceCore.round_le_top_succ (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) :
    ∃ u ∈ T, (U.block b).round ≤ pc.top u + 1
```

**No block outruns the reliable frontier by more than one round.** Whatever a Byzantine validator publishes, some `T`-validator has reached the round below it — the adversary's whole freedom is the single layer it may build the instant a quorum forms beneath it.

#### `ViewPace.exists_honest_floor`

*theorem, `ViewPace.lean`*

```lean
theorem ViewPace.exists_honest_floor (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    {b : BlockId} (hb : b ∈ U.ids) {n : ℕ}
    (hbr : (U.block b).round = n + 1) :
    ∃ u ∈ T, n ≤ vp.top u ∧
      vp.built u 0 + (∑ i ∈ Finset.range n, vp.timeout i) ≤ vp.built u n
```

**The honest floor** (CU5): a valid block of round `n + 1` certifies that some reliable validator reached round `n` having genuinely waited out all `n` timeouts. Evidence of a round cannot exist before the honest schedule permits the round, so the author-blind catch-up a deployment runs is executable: it never pulls a validator past where a reliable peer already is, and the obligation `catchup` states over `T`-authored blocks is the analysis-side restriction of a rule that is safe over all of them.

#### `synchronisedOn_of_rate`

*theorem, `ViewPace.lean`*

```lean
theorem synchronisedOn_of_rate (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hrate : Rated vp.timeout) :
    SynchronisedOn U T (max (2 * vp.delay + vp.proc) vp.gst)
```

**Q3 on this route** — coverage from an explicit round, under a rated backoff: `R = max (2Δ + proc) gst`, each summand what it looks like. The rated timeout clears the constant threshold from the round named by the threshold itself, and no start spread or base round appears.

#### `directCommit_of_wait`

*theorem, `ViewPace.lean`*

```lean
theorem directCommit_of_wait (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**The wait bound** (Q2 headline, report §6.10): a constant timeout of `2Δ + proc` commits every reliable-led slot past GST. The threshold is a constant of the network and the implementation — no start spread appears in any hypothesis, because catch-up collapses whatever spread the deployment began with. Production is derived, so nothing asserts blocks above round `0`, and `T ⊆ Correct` is not consumed.

#### `decided_of_wait`

*theorem, `ViewPace.lean`*

```lean
theorem decided_of_wait (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**The wait bound, as a decision.**

#### `directCommit_of_wait_two_delay`

*theorem, `ViewPace.lean`*

```lean
theorem directCommit_of_wait_two_delay (vp : ViewPace U T N)
    (hcard : quorumCard Validator ≤ T.card)
    (hproc : vp.proc = 0) (hgst : vp.gst ≤ R)
    (hwait : ∀ n, R ≤ n → 2 * vp.delay ≤ vp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**`Delay(Δ) = 2Δ`** — the threshold at instantaneous entry: when `proc = 0`, the constant is twice the delivery bound, the timer deployed implementations run. The general threshold degrades linearly in the processing bound and in nothing else.

#### `heldOf_inj`

*theorem, `PaceDelivery.lean`*

```lean
theorem heldOf_inj {v : Validator} (hv : v ∈ (Correct : Finset Validator))
    {n : ℕ} (hn : n < N) {i j : BlockId}
    (hi : i ∈ vp.heldOf v n) (hj : j ∈ vp.heldOf v n)
    (hij : (U.block i).creator = (U.block j).creator) : i = j
```

**The acceptance rule is derived** (V19). A correct validator never holds two blocks by one author at a build instant --- not because it deduplicates, but because P7 would oblige its block to reference both and P2 forbids that. The hypothesis is production at the round above, which the pacing structure supplies.

This is the field the storage development assumes; here it is a theorem about the reference discipline.

#### `refsAccepted_toDelivery`

*theorem, `PaceDelivery.lean`*

```lean
theorem refsAccepted_toDelivery : RefsAccepted vp.toDelivery
```

**The reference discipline transfers** to the induced layer: a correct validator's block references only what it accepted, because `accepted` is what it held and `refs_held` says its references are among those. The round bound is free --- a referenced block sits one round below (P1), and the referring block is inside the horizon.

#### `dos_resistance_of_pace`

*theorem, `PaceDelivery.lean`*

```lean
theorem dos_resistance_of_pace {κ : ℕ}
    (hu : UniformBudget vp.toDelivery κ) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto vp.toDelivery v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ)))
```

**Liveness and bounded storage, from one structure** (V20). A pacing structure run under the enforceable acceptance budget gives the denial-of-service capstone of report §8 outright: no correct validator stalls, and no correct validator's retained view grows faster than linearly in the round.

Production and the reference discipline are *derived* --- the first from genesis and the pacemaker's rules, the second from S5 through the induced layer --- so the only thing assumed beyond the pacing structure is the budget itself, which is the mechanism a validator runs. The two conclusions do not compete: liveness never needs a Byzantine block, and enforcing the budget never defers a correct one.

### Chain quality

#### `card_coveredAt_ge_of_decided`

*theorem, `Quality.Coverage.lean`*

```lean
theorem card_coveredAt_ge_of_decided {V : View Validator BlockId Payload U}
    {k : ℕ} (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card - F.f ≤ (coveredAt U L δ).card
```

**CQ1.** A committed leader's flush covers all but at most `f` of the correct validators at every round below it — any route, any view, no synchrony.

#### `card_correct_le_two_mul_coveredAt_of_decided`

*theorem, `Quality.Coverage.lean`*

```lean
theorem card_correct_le_two_mul_coveredAt_of_decided
    {V : View Validator BlockId Payload U} {k : ℕ}
    (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card
```

**CQ2 (the half, exactly).** Every commit carries, at every round below it, blocks from at least half of the correct validators: `|Correct| ≤ 2·|covered|`, since `|Correct| ≥ 2f + 1`.

#### `mem_ledgerSet_of_mem_history`

*theorem, `Quality.Coverage.lean`*

```lean
theorem mem_ledgerSet_of_mem_history {g : ℕ → Option BlockId} {n k : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ U.ids)
    (hb : b ∈ history U L) : b ∈ ledgerSet U g n
```

A cone block of a committed slot is in the ledger — the one unfolding both CQ3 and CQ6 rest on.

#### `ledger_coverage`

*theorem, `Quality.Coverage.lean`*

```lean
theorem ledger_coverage {V : View Validator BlockId Payload U}
    {g : ℕ → Option BlockId} {n k : ℕ}
    (hdec : Decided U V k (some L)) (hg : g k = some L) (hk : k < n)
    (hδ : δ < (U.block L).round) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      (Correct : Finset Validator).card - F.f ≤ S.card ∧
      ∀ v ∈ S, ∃ i ∈ ledgerSet U g n,
        (U.block i).creator = v ∧ (U.block i).round = δ
```

**CQ3 (ledger coverage, cumulative).** For a verdict assignment `g` of a view with a committed slot `k < n` whose leader sits at round `r`: for every `δ < r`, at least `|Correct| − f` correct validators each have a round-`δ` block in the ledger `ledgerSet U g n`. The set is exhibited (`coveredAt`), so no choice and no decidability of the ledger is needed; view-independence is `ledgerSet_agree`.

#### `mem_history_of_decided_commit`

*theorem, `Quality.Inclusion.lean`*

```lean
theorem mem_history_of_decided_commit (hs : Synchronised U R)
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hdec : Decided U V k (some L))
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hb : b ∈ U.ids) (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hR : R ≤ (U.block b).round)
    (hlt : (U.block b).round < (U.block L).round) :
    b ∈ history U L
```

**CQ5.** Post-`R`, every correct block is in the cone of **every** committed leader block with a correct author at a later round — any commit route, any view. The backbone does all the work.

#### `committed_of_correct_block`

*theorem, `Quality.Inclusion.lean`*

```lean
theorem committed_of_correct_block (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k'
```

**CQ6 (inclusion liveness).** Under a fair schedule over reliable validators and post-`R` synchrony, for every round `m ≥ R` there is a committed slot — above `m`, led by a correct validator — whose flush contains **every** correct round-`m` block; hence every such block is in the agreed ledger of any verdict assignment covering that slot.

The slot is produced *before* the universe is quantified, exactly as in L6: the schedule fixes it, and any sufficiently grown synchronous DAG then commits it.

#### `committed_of_correct_block_within`

*theorem, `Quality.Capstone.lean`*

```lean
theorem committed_of_correct_block_within
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairWithin T w) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', slotAt Validator (m + 1) ≤ k' ∧
      k' < slotAt Validator (m + 1) + w ∧
      m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k'
```

**CQ7, windowed.** Under a windowed-fair schedule, the committing slot for round-`m` blocks lies within `w` slots of the first slot above round `m`.

#### `committed_of_correct_block_by_round`

*theorem, `Quality.Capstone.lean`*

```lean
theorem committed_of_correct_block_by_round
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairWithin T w) (hs : BoundedSpacing (Validator := Validator) s)
    (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧
      S.slotRound k' ≤ S.slotRound (slotAt Validator (m + 1)) + s * w ∧
      R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k'
```

**CQ7, by round.** With bounded slot spacing, the committing slot's round is within `s·w` rounds of the first slot above `m`: a correct block is committed within a schedule-window of rounds of its creation, once the DAG is synchronous.

#### `chain_quality`

*theorem, `Quality.Capstone.lean`*

```lean
theorem chain_quality (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    (∀ (U : BlockUniverse Validator BlockId Payload)
        (V : View Validator BlockId Payload U) (k : ℕ) (L : BlockId)
        (δ : ℕ), Decided U V k (some L) → δ < (U.block L).round →
        (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card) ∧
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k'
```

**CQ7 (the capstone).** Chain quality in one statement, enforceable or standard conditions only. Unconditionally: every commit's flush covers at least half of the correct validators at every round below it. Post-`R`, under a fair schedule: every correct block is in the flush of a committed slot fixed in advance by the schedule.

### Denial of service

#### `mem_historyBlocksOf`

*theorem, `DoS.Exposure.lean`*

```lean
theorem mem_historyBlocksOf {b i : BlockId} {X : Validator} {n : ℕ} :
    i ∈ historyBlocksOf U b X n ↔
      i ∈ history U b ∧ (U.block i).creator = X ∧ (U.block i).round = n
```

Membership in `historyBlocksOf`, unfolded.

#### `not_exposedIn_iff_card_le_one`

*theorem, `DoS.Exposure.lean`*

```lean
theorem not_exposedIn_iff_card_le_one {b : BlockId} {X : Validator} :
    ¬ ExposedIn U b X ↔ ∀ n, (historyBlocksOf U b X n).card ≤ 1
```

**Not exposed** and **at most one block per round** are the same condition.

The counting form of `ExposedIn`, and the whole content of D11: an author that is never exposed in `b`'s history contributes at most one block per round to it, so the equivocation achieved nothing.

#### `not_exposedIn_of_round_le_one`

*theorem, `DoS.Exposure.lean`*

```lean
theorem not_exposedIn_of_round_le_one {b : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hr : (U.block b).round ≤ 1) : ¬ ExposedIn U b X
```

Nothing is exposed below round 2: there is not room for a merge.

#### `mem_exposedTo`

*theorem, `DoS.Exposure.lean`*

```lean
theorem mem_exposedTo {b : BlockId} {X : Validator} :
    X ∈ exposedTo U b ↔ ExposedIn U b X
```

`exposedTo` collects exactly the authors exposed in the block's history — the `Finset` form of `ExposedIn`.

#### `card_exposedTo_le`

*theorem, `DoS.Exposure.lean`*

```lean
theorem card_exposedTo_le {b : BlockId} (hb : b ∈ U.ids) : (exposedTo U b).card ≤ F.f
```

**At most `f` authors can be exposed**, since exposure requires equivocation and only Byzantine validators equivocate.

#### `creators_refs_eq_correct`

*theorem, `DoS.Exposure.lean`*

```lean
theorem creators_refs_eq_correct (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (hround : 0 < (U.block b).round) (hk : F.f ≤ (exposedTo U b).card) :
    creatorsOf U.block (U.block b).refs = (Correct : Finset Validator)
```

**D15a at the bound.** Once a block has caught the whole fault budget, its references are *exactly* the correct validators — every one of them.

The margin is gone, and this is what it means concretely: with `f` authors excluded the admissible set is `Correct`, which numbers exactly `2f+1`, so a block that must name `n−f` distinct admissible authors must name all of them.

#### `exists_self_ancestor`

*theorem, `DoS.SelfParent.lean`*

```lean
theorem exists_self_ancestor {b : BlockId} (hb : b ∈ U.ids) {t : ℕ}
    (ht : t ≤ (U.block b).round) :
    ∃ i ∈ history U b,
      (U.block i).creator = (U.block b).creator ∧ (U.block i).round = t
```

**D20 (chains reach the ground).** A block's history holds a block by its own author at *every* round below it. Contiguity is the content: an author cannot appear at round `t` without a full pedigree at `t-1, …, 0`.

#### `not_exposedIn_self_creator`

*theorem, `DoS.SelfParent.lean`*

```lean
theorem not_exposedIn_self_creator (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ¬ ExposedIn U b (U.block b).creator
```

**D21 (no self-laundering).** Under the DoS condition no valid block is exposed to its own author. A block cites its self-parent, and `DoSValid` forbids citing an exposed author — so once an author's equivocation is visible in some history, that author can never build on that history again.

This is the indispensable half of D20: the fresh "carrier" block that adopts an equivocation branch while carrying none of its author's past — the mechanism of every super-linear history family — cannot exist.

#### `mem_missingAt`

*theorem, `DoS.Density.lean`*

```lean
theorem mem_missingAt {b : BlockId} {δ : ℕ} {v : Validator} :
    v ∈ missingAt U b δ ↔ v ∈ (Correct : Finset Validator) ∧
      ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ)
```

Membership in `missingAt`, unfolded: a correct validator is missing at depth `δ` when the history contains none of its blocks there.

#### `card_missingAt_le`

*theorem, `DoS.Density.lean`*

```lean
theorem card_missingAt_le {b : BlockId} (hb : b ∈ U.ids) {δ : ℕ}
    (hδ : δ < (U.block b).round) : (missingAt U b δ).card ≤ F.f
```

**D25 (density).** A valid block's history contains a block by all but at most `f` of the correct validators at every round strictly below it.

#### `card_filter_creator_le`

*theorem, `DoS.Counting.lean`*

```lean
theorem card_filter_creator_le (hb : b ∈ U.ids) (h : ¬ ExposedIn U b X) :
    ((history U b).filter (fun j => (U.block j).creator = X)).card ≤ (U.block b).round + 1
```

An author not exposed in `b`'s history contributes at most one block per round to it, hence at most `round b + 1` in all.

#### `eq_of_not_exposedIn`

*theorem, `DoS.Adoption.lean`*

```lean
theorem eq_of_not_exposedIn {c i j : BlockId} {X : Validator} (h : ¬ ExposedIn U c X)
    (hi : i ∈ history U c) (hj : j ∈ history U c)
    (hic : (U.block i).creator = X) (hjc : (U.block j).creator = X)
    (hround : (U.block i).round = (U.block j).round) : i = j
```

The pointwise form of D11's counting: two blocks by an author unexposed in a history, at one round of it, are equal.

#### `exists_referencer`

*theorem, `DoS.Adoption.lean`*

```lean
theorem exists_referencer {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b)
    (hne : i ≠ b) : ∃ j ∈ history U b, i ∈ (U.block j).refs
```

Everything in a history except the block itself is referenced from within the history.

#### `mem_history_of_creator_eq_of_not_exposedIn`

*theorem, `DoS.Adoption.lean`*

```lean
theorem mem_history_of_creator_eq_of_not_exposedIn {b i j : BlockId} {X : Validator}
    (hb : b ∈ U.ids) (hX : ¬ ExposedIn U b X)
    (hi : i ∈ history U b) (hj : j ∈ history U b)
    (hic : (U.block i).creator = X) (hjc : (U.block j).creator = X)
    (hround : (U.block i).round ≤ (U.block j).round) : i ∈ history U j
```

**Unexposed means one chain.** Two same-author blocks of a history, the author unexposed there, are chain-related: the lower lies in the higher one's history. With D20 this says an unexposed author's content *is* a single self-parent chain.

#### `mem_topsOf`

*theorem, `DoS.Adoption.lean`*

```lean
theorem mem_topsOf {b t : BlockId} {X : Validator} :
    t ∈ topsOf U b X ↔ t ∈ history U b ∧ (U.block t).creator = X ∧
      ∀ c ∈ history U b, (U.block c).creator = X → t ∉ (U.block c).refs
```

Membership in `topsOf`, unfolded: a top is a block of `X` in the history with no later block of `X` reachable above it.

#### `exists_top_of_mem_history`

*theorem, `DoS.Adoption.lean`*

```lean
theorem exists_top_of_mem_history {b i : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hic : (U.block i).creator = X) :
    ∃ t ∈ topsOf U b X, i ∈ history U t
```

Every `X`-block of a history lies in some top's history: walk up `X`-children as far as they go.

#### `card_filter_creator_le_card_topsOf`

*theorem, `DoS.Adoption.lean`*

```lean
theorem card_filter_creator_le_card_topsOf (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) (X : Validator) :
    ((history U b).filter fun i => (U.block i).creator = X).card
      ≤ (topsOf U b X).card * ((U.block b).round + 1)
```

An author's whole content is at most one block per (top, round) pair: each block sits on the chain of some top, and a top's own history holds one `X`-block per round (D21 applied to the top itself).

#### `top_eq_of_mem_namer_history`

*theorem, `DoS.Adoption.lean`*

```lean
theorem top_eq_of_mem_namer_history (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {X : Validator} {t₁ t₂ j : BlockId}
    (ht₁ : t₁ ∈ topsOf U b X) (ht₂ : t₂ ∈ topsOf U b X)
    (hj : j ∈ history U b) (hjref : t₂ ∈ (U.block j).refs)
    (h₁j : t₁ ∈ history U j) : t₁ = t₂
```

**The adoption collapse.** Two tops, one lying inside the history of a block that references the other, coincide: a namer's history has room for only one `X`-chain, and a named `X`-block strictly below another has an `X`-child there — so it was no top.

#### `card_history_le'`

*theorem, `DoS.Pedigree.lean`*

```lean
theorem card_history_le' (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    (history U b).card
      ≤ (Fintype.card Validator + (Fintype.card Validator - 1) * F.f ^ F.f) * ((U.block b).round + 1)
```

**The tightened total.** `|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`: the unexposed authors contribute one chain each, the at-most-`f` exposed ones at most `3f·f^(f-1)` chains each. At `f = 1` this is `7(r+1)`, recovering the adoption theorem's constant exactly.

#### `not_mem_creators_refs_of_correct_exposed`

*theorem, `DoS.Exclusion.lean`*

```lean
theorem not_mem_creators_refs_of_correct_exposed (hdos : DoSValid U) {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ U.ids, (U.block c).round = n + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X)
    {b : BlockId} (hb : b ∈ U.ids) (hbr : n + 2 ≤ (U.block b).round) :
    X ∉ creatorsOf U.block (U.block b).refs
```

The form the condition consumes: from `n+2` on, nobody may name `X`.

#### `mem_history_of_correct`

*theorem, `DoS.Exclusion.lean`*

```lean
theorem mem_history_of_correct {R : ℕ} (hs : SynchronisedOn U (Correct : Finset Validator) R) :
    ∀ d : ℕ, ∀ c ∈ U.ids, ∀ a ∈ U.ids,
      (U.block c).creator ∈ (Correct : Finset Validator) →
      (U.block a).creator ∈ (Correct : Finset Validator) →
      R ≤ (U.block a).round → (U.block a).round + 1 + d = (U.block c).round →
      a ∈ history U c
```

**The backbone lemma.** After `R`, correct histories contain the whole correct past.

#### `mem_novelty`

*theorem, `DoS.Novelty.lean`*

```lean
theorem mem_novelty : i ∈ novelty U V b ↔ i ∈ history U b ∧ i ∉ V
```

Membership in `novelty`, unfolded: the novel blocks are those in the history and not already in the view.

#### `card_history_le_of_stepNovelty`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_history_le_of_stepNovelty {κ' : ℕ} (hstep : StepNovelty U κ')
    (hb : b ∈ U.ids) (hcorr : (U.block b).creator ∈ (Correct : Finset Validator)) :
    (history U b).card ≤ κ' * (U.block b).round + 1
```

**The telescope.** Under `StepNovelty`, a correct author's history is linear: `|H(b)| ≤ κ'·r + 1`. Descent along the self-parent chain (S10), one budget per round.

#### `viewUpto_succ`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_succ (n : ℕ) :
    viewUpto D v (n + 1) =
      viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
```

The view after round `n+1` is the previous view together with the histories of everything newly accepted.

#### `viewUpto_mono`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_mono (h : m ≤ n) : viewUpto D v m ⊆ viewUpto D v n
```

Views only grow with the round index.

#### `history_subset_viewUpto`

*theorem, `DoS.Novelty.lean`*

```lean
theorem history_subset_viewUpto {a : BlockId} (hmn : m ≤ n)
    (ha : a ∈ D.accepted v m) : history U a ⊆ viewUpto D v n
```

An accepted block's whole history is retained.

#### `UniformBudget.byzBudget`

*theorem, `DoS.Novelty.lean`*

```lean
theorem UniformBudget.byzBudget {τ : ℕ} (h : UniformBudget D τ) :
    ByzBudget D τ
```

Dropping a guard weakens nothing: the author-blind cap implies the Byzantine-side budget with the same constant.

#### `card_novelty_le_viewGap_add_one`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_novelty_le_viewGap_add_one {R : ℕ} (hED : EventuallyDelivers D R)
    (hn : R ≤ n) (hv : v ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted w n) :
    (novelty U (viewUpto D v n) b).card ≤ (viewGap D v w n).card + 1
```

**C3a.** After `R`, a block built from `w`'s acceptances is, at any correct `v`, at most one plus the gap toward `w`: its correct references are shared (delivered and accepted at `v` too), and its Byzantine references sit whole inside `w`'s view.

#### `viewUpto_subset_history`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_subset_history (hw : w ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) :
    viewUpto D w n ⊆ history U b
```

A correct validator's block carries everything its author ever accepted: `includes` per round, chained by the self-parent (S10).

#### `card_viewGap_succ_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewGap_succ_le {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {c : BlockId} (hc : c ∈ U.ids)
    (hcc : (U.block c).creator = w) (hcr : (U.block c).round = n + 1) :
    (viewGap D v w (n + 1)).card ≤ F.f * κ
```

**C3′ — the gap is constant, not a drift.** After `R`, as long as the author has a current block (which L1 supplies), the divergence between two correct validators' views is at most **one round of Byzantine budget**: `w`'s round-`(n+1)` block hands `v` all of `viewUpto w n` at once, and the remainder is `w`'s budgeted Byzantine frontier.

#### `uniform_of_byzBudget`

*theorem, `DoS.Novelty.lean`*

```lean
theorem uniform_of_byzBudget {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hra : RefsAccepted D)
    (hv : v ∈ (Correct : Finset Validator)) {n : ℕ} (hn : R ≤ n + 1)
    (hb : b ∈ D.accepted v (n + 2)) :
    (novelty U (viewUpto D v (n + 1)) b).card ≤ F.f * κ + 1
```

**The sandwich, converse direction.** After `R`, a `ByzBudget κ` schedule is uniformly budgeted at `f·κ + 1` with **no creator guard**: Byzantine acceptances by enforcement, correct ones by C3″. Together with `UniformBudget.byzBudget` this makes the guard-free and guarded formulations equivalent up to one factor of `f` — a validator that runs the author-blind cap loses only constants, never theorems.

#### `card_viewUpto_le'`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewUpto_le' {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hra : RefsAccepted D)
    (hv : v ∈ (Correct : Finset Validator)) {n : ℕ} (hn : R + 1 ≤ n) :
    (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
      (n - (R + 1)) *
        ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ)
```

**B3′ — linear storage from the enforceable rule alone.** After `R`, a correct validator's view grows by at most `|Correct|·(f·κ + 1) + f·κ` per round, under nothing but the Byzantine budget and the reference discipline: the correct side is supplied by C3″.

#### `viewUpto_subset_ids`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_subset_ids : viewUpto D v n ⊆ U.ids
```

A view holds real blocks.

#### `card_viewUpto_filter_correct_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewUpto_filter_correct_le (v : Validator) (n : ℕ) :
    ((viewUpto D v n).filter
      fun i => (U.block i).creator ∈ (Correct : Finset Validator)).card ≤
      (Correct : Finset Validator).card * (n + 1)
```

The correct part of a view counts itself: one block per correct author per round (`no_equivocation`), so at most `|Correct|·(n+1)`.

#### `mem_byzPool`

*theorem, `DoS.Novelty.lean`*

```lean
theorem mem_byzPool {i : BlockId} :
    i ∈ byzPool D n ↔ ∃ w ∈ (Correct : Finset Validator),
      i ∈ viewUpto D w n ∧
        (U.block i).creator ∉ (Correct : Finset Validator)
```

Membership in `byzPool`, unfolded: a Byzantine-authored block that some correct validator's view already contains.

#### `card_byzPool_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_byzPool_le {κ : ℕ} (hbyz : ByzBudget D κ) (hra : RefsAccepted D)
    (n : ℕ) :
    (byzPool D n).card ≤ (Correct : Finset Validator).card * F.f +
      n * ((Correct : Finset Validator).card * (F.f * κ))
```

The pool, telescoped: linear from round 0.

#### `card_viewUpto_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewUpto_le {κ : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ (Correct : Finset Validator)) (n : ℕ) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          n * ((Correct : Finset Validator).card * (F.f * κ)))
```

**B4 — unconditional linear storage.** Under nothing but the enforceable budget and the reference discipline — no synchrony, no `R`, no delivery guarantee — every correct validator's retained view is linear in the round: at most one block per correct author per round, plus the global Byzantine pool. This is `dos-equivocation-and-growth.md` §6's pre-`R` conjecture, closed: the base the capstone measures from is itself linear, so the DoS bound holds from round 0 under full asynchrony.

#### `dos_resistance`

*theorem, `DoS.Novelty.lean`*

```lean
theorem dos_resistance {τ N : ℕ} {P : Finset Validator}
    (hpop : ∀ r ≤ N, PopulatedOn U P r)
    (hu : UniformBudget D τ) (hra : RefsAccepted D) :
    (∀ r ≤ N, PopulatedOn U P r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * τ)))
```

**DoS resistance, from enforceable conditions only.** Liveness and linear storage from round 0 under full asynchrony; every hypothesis is local protocol conduct or a pure network assumption, and the author-blind cap replaces every creator-guarded budget.

#### `dos_resistance'`

*theorem, `DoS.Novelty.lean`*

```lean
theorem dos_resistance' {τ R N : ℕ} {P : Finset Validator}
    (hpop : ∀ r ≤ N, PopulatedOn U P r)
    (hED : EventuallyDelivers D R) (hu : UniformBudget D τ)
    (hra : RefsAccepted D) :
    (∀ r ≤ N, PopulatedOn U P r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n, R + 1 ≤ n →
        (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
          (n - (R + 1)) *
            ((Correct : Finset Validator).card * (F.f * τ + 1) + F.f * τ)
```

The post-`R` incremental form of the headline: the same enforceable conduct, plus the network's `EventuallyDelivers`.

#### `card_viewUpto_le_of_allExposed'`

*theorem, `DoS.Composition.lean`*

```lean
theorem card_viewUpto_le_of_allExposed' {κ : ℕ} (hdos : DoSValid U)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) (hexp : AllExposed U m)
    (hv : v ∈ (Correct : Finset Validator)) (hn : m + 1 ≤ n)
    (hpop : ∀ r, m + 3 ≤ r → r ≤ n + 1 → Populated U r) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          (m + 1) * ((Correct : Finset Validator).card * (F.f * κ)))
```

**B5, with the constant made explicit by the budget**: the frozen pool is at most `|Correct|·f·(1 + (m+1)·κ)`. The budget paces what an author can inject before being caught; exclusion ends it — one theorem.

### Garbage collection

#### `chopBlock_creator`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_creator :
    (chopBlock U G i).creator = (U.block i).creator
```

Truncation leaves authorship unchanged.

#### `chopBlock_round`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_round :
    (chopBlock U G i).round = (U.block i).round - G
```

Truncation rebases rounds by the cut.

#### `chopBlock_payload`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_payload :
    (chopBlock U G i).payload = (U.block i).payload
```

Truncation leaves payloads unchanged.

#### `chopBlock_refs_of_le`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_refs_of_le (h : (U.block i).round ≤ G) :
    (chopBlock U G i).refs = ∅
```

At or below the cut a block becomes a genesis: its references are dropped.

#### `chopBlock_refs_of_lt`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_refs_of_lt (h : G < (U.block i).round) :
    (chopBlock U G i).refs = (U.block i).refs
```

Above the cut references are untouched.

#### `creatorsOf_chopBlock`

*theorem, `GC.Chop.lean`*

```lean
theorem creatorsOf_chopBlock (s : Finset BlockId) :
    creatorsOf (chopBlock U G) s = creatorsOf U.block s
```

Creators are untouched, so creator sets are, pointwise.

#### `mem_chop_ids`

*theorem, `GC.Chop.lean`*

```lean
theorem mem_chop_ids :
    i ∈ (chop U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round
```

The truncated universe holds exactly the blocks at or above the cut.

#### `chop_block_eq`

*theorem, `GC.Chop.lean`*

```lean
theorem chop_block_eq : (chop U G).block = chopBlock U G
```

The truncated universe looks blocks up through `chopBlock`.

#### `blocksAt_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem blocksAt_chop (m : ℕ) :
    blocksAt (chop U G) m = blocksAt U (G + m)
```

Round `m` of the truncation is round `G + m` of the original.

#### `history_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem history_chop (hb : b ∈ (chop U G).ids) :
    history (chop U G) b =
      (history U b).filter fun i => G ≤ (U.block i).round
```

**The cone above the cut**: truncation intersects every cone with the window. This is the lemma the windowed budget (`garbage.md` G13) and the statute of limitations both run on.

#### `dosValid_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem dosValid_chop (hdos : DoSValid U) : DoSValid (chop U G)
```

**G1, DoS half — the one-way door.** The condition survives truncation; the converse fails by design (the statute of limitations, witnessed in `LeanDagTest/GC/Chop.lean`).

#### `certificates_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem certificates_chop {L : BlockId} (s : ℕ) :
    certificates (chop U G) L s = certificates U L (G + s)
```

Certificates for the slot at rebased round `s` are the original slot's certificates, verbatim.

#### `directCommit_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem directCommit_chop {L : BlockId} (s : ℕ) :
    DirectCommit (chop U G) L s ↔ DirectCommit U L (G + s)
```

#### `certifiedIn_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem certifiedIn_chop {A L : BlockId} (hA : A ∈ (chop U G).ids) (s : ℕ) :
    CertifiedIn (chop U G) A L s ↔ CertifiedIn U A L (G + s)
```

**The indirect test survives the cut**: an anchor above the horizon certifies a slot above the horizon in the truncation exactly when it did in the original. With `directCommit_chop`/`directSkip_chop` this is the per-slot decision invariance of `garbage.md` G3 — the indirect verdict is a property of the anchor's cone, and never consults the pruned prefix.

#### `decided_chop`

*theorem, `GC.ChopDecided.lean`*

```lean
theorem decided_chop (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v ↔
      Decided U V (d + k) v
```

**G3.** The decision relation survives the cut, both ways: a validator re-running Mysticeti on the truncation, from its truncated view, decides slot `k` exactly as it decided slot `d + k` on the full universe. The only condition is that the base slot clears the horizon — no synchrony, no liveness, nothing about the prefix.

#### `decided_agree_chop`

*theorem, `GC.ChopDecided.lean`*

```lean
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) :
    w = v
```

**G4.** A validator that joined from the truncation — holding an **arbitrary** view `W` of `chop U G`, with no history below the cut and no relation to any full-history view — agrees slot for slot with every full-history validator. `decided_unique` runs inside the truncation against the truncated full-history view, and `decided_chop` carries the verdict across the cut.

#### `mem_viewUpto`

*theorem, `GC.Window.lean`*

```lean
theorem mem_viewUpto {t : ℕ} :
    x ∈ viewUpto D v t ↔
      ∃ k, k ≤ t ∧ ∃ a ∈ D.accepted v k, x ∈ history U a
```

Membership in the accumulated store, unrolled: something accepted at some round up to `t` carries `x` in its cone.

#### `viewUpto_chopD`

*theorem, `GC.Window.lean`*

```lean
theorem viewUpto_chopD (m : ℕ) :
    viewUpto (chopD D G) v m =
      (viewUpto D v (G + m)).filter fun i => G ≤ (U.block i).round
```

**G14.** The truncated store *is* the store of the truncation: pruning below `G` and accumulating in the window agree exactly.

#### `novelty_chop_anti`

*theorem, `GC.Window.lean`*

```lean
theorem novelty_chop_anti {G' : ℕ} (hGG : G ≤ G') (hb : b ∈ (chop U G').ids)
    (V : Finset BlockId) :
    novelty (chop U G') V b ⊆ novelty (chop U G) V b
```

…so it only shrinks novelty: **pruning cheapens blocks** — an block within the budget never falls outside it as the window slides, and no deferral decision ever flips the wrong way.

#### `populated_chop`

*theorem, `GC.Window.lean`*

```lean
theorem populated_chop {N : ℕ} (hpop : ∀ r ≤ N, Populated U r) (hG : G ≤ N) :
    ∀ r ≤ N - G, Populated (chop U G) r
```

**G5.** The truncated universe never stalls above the cut.

Production upstream is all this needs: a round-`r` block of `chop U G` is a round-`(G+r)` block of `U`, so the statement is the hypothesis with its index shifted. It consumes no network assumption, and any of the three production routes discharges it.

#### `card_retained_le`

*theorem, `GC.Window.lean`*

```lean
theorem card_retained_le {κ Λ t : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ (Correct : Finset Validator))
    (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    ((viewUpto D v t).filter fun i => G ≤ (U.block i).round).card ≤
      (Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ)))
```

**G6.** A validator whose horizon `G` trails its current round `t` by at most `Λ` retains a **constant** number of blocks — independent of `t`, hence of how long the system has run. B4 gave linear-forever; the horizon makes it constant-at-lag-`Λ`. Stated per time: the retained store is the truncated store (G14), which B4 bounds on `chop U G` at window depth `t − G ≤ Λ`.

#### `mem_attesters`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem mem_attesters {v : Validator} :
    v ∈ attesters U t y ↔
      ∃ a ∈ U.ids, (U.block a).round = t ∧ y ∈ history U a ∧
        (U.block a).creator = v
```

Membership in `attesters`, unfolded: an attester is a correct author of a round-`t` block whose history reaches `y`.

#### `mem_base`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem mem_base :
    y ∈ Base U t G ↔
      (y ∈ U.ids ∧ (U.block y).round = G) ∧
        F.f + 1 ≤ (attesters U t y).card
```

Membership in `Base`, unfolded: a round-`G` block attested by at least `f+1` validators.

#### `exists_correct_attester_of_mem_base`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem exists_correct_attester_of_mem_base (hy : y ∈ Base U t G) :
    ∃ a ∈ U.ids, (U.block a).round = t ∧
      (U.block a).creator ∈ (Correct : Finset Validator) ∧
      y ∈ history U a
```

**G10, soundness.** Everything in the base has a correct attester — `f+1` authors always include one — and so lies in a correct cone. The adversary cannot smuggle fabrications into anyone's base.

#### `correct_mem_base`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem correct_mem_base {R : ℕ} (hs : Synchronised U R) (hR : R ≤ G)
    (hGt : G < t) (hpop : Populated U t) (hy : y ∈ U.ids)
    (hyr : (U.block y).round = G)
    (hyc : (U.block y).creator ∈ (Correct : Finset Validator)) :
    y ∈ Base U t G
```

**G10, completeness.** Post-`R`, every correct block of the layer is in every correct attestation (the backbone), so it clears the `f+1` bar in *every* sample — the shared correct layer `C` is in every base, and the adversary cannot filter it out.

#### `accepted_mem_base`

*theorem, `GC.Bootstrap.lean`*

```lean
theorem accepted_mem_base {R m t : ℕ} (hs : Synchronised U R)
    (hv : v ∈ (Correct : Finset Validator)) (hy : y ∈ viewUpto D v m)
    (hyr : (U.block y).round = G) (hcar : Populated U (m + 1))
    (hpop : Populated U t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    y ∈ Base U t G
```

**G11.** Every round-`G` block a correct validator accepted into its window by `m` — Byzantine-authored included — is in the base attested at any `t ≥ m + 2`. Acceptance → the keeper's round-`(m+1)` block carries it (`viewUpto_subset_history`) → the backbone hands that block to every correct round-`t` cone → every correct author attests it, clearing `f + 1` in **every** sample. Nothing obtainable is ever filtered out.

#### `card_joinIds_le`

*theorem, `GC.Bootstrap.lean`*

```lean
theorem card_joinIds_le {κ Λ R m t : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hED : EventuallyDelivers D R)
    (hw : w ∈ (Correct : Finset Validator)) (hR : R ≤ t) (hmt : m ≤ t)
    (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    (joinIds D w m t G).card ≤
      (Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ)))
```

**G6b.** The joiner's entire fetch is inside one correct peer's retained store, hence bounded by the G6 constant: sync cost, not just storage, is constant at lag `Λ`.

#### `bootstrap_agree`

*theorem, `GC.Bootstrap.lean`*

```lean
theorem bootstrap_agree [S : Slots Validator] {d : ℕ}
    (hd : G ≤ S.slotRound d) {R m t : ℕ} (hs : Synchronised U R)
    (hw : w ∈ (Correct : Finset Validator)) (hcar : Populated U (m + 1))
    (hpop : Populated U t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t)
    {V : View Validator BlockId Payload U} {k : ℕ} {jv fv : Option BlockId}
    (hJ : Decided (S := S.chop G d hd) (chop U G)
      (joinView (D := D) hs hw hcar hpop hR hmt) k jv)
    (hV : Decided U V (d + k) fv) :
    jv = fv
```

**G12 (bootstrap safety).** A joiner that assembles its view from the attested base and a correct peer's window, and runs Mysticeti on the truncation, never conflicts with any full-history validator on any slot. The composition *is* the proof: `joinView` is a view of `chop U G`, and `decided_agree_chop` never asked whose view it was.

#### `card_serve_le`

*theorem, `GC.Bootstrap.lean`*

```lean
theorem card_serve_le {κ Λ n : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hw : w ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) (hG : G ≤ n) (hΛ : n ≤ G + Λ) :
    (history (chop U G) b).card ≤
      ((Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ)))) + 1
```

**G7, priced.** Serving cost is the G6 constant plus one.

#### `chop_chop`

*theorem, `GC.Horizon.lean`*

```lean
theorem chop_chop {G₁ G₂ : ℕ} (hG : G₁ ≤ G₂) :
    chop (chop U G₁) (G₂ - G₁) = chop U G₂
```

**G8, the composition law.** A deeper cut is just another cut: two admissible horizons are always related by the one operator, so every transfer theorem composes along the tower of truncations.

#### `decided_agree_horizons`

*theorem, `GC.Horizon.lean`*

```lean
theorem decided_agree_horizons [S : Slots Validator]
    {G₁ G₂ d₁ d₂ : ℕ} (hd₁ : G₁ ≤ S.slotRound d₁) (hd₂ : G₂ ≤ S.slotRound d₂)
    {W₁ : View Validator BlockId Payload (chop U G₁)}
    {W₂ : View Validator BlockId Payload (chop U G₂)}
    {V : View Validator BlockId Payload U}
    {k₁ k₂ : ℕ} (halign : d₁ + k₁ = d₂ + k₂) {w₁ w₂ fv : Option BlockId}
    (hW₁ : Decided (S := S.chop G₁ d₁ hd₁) (chop U G₁) W₁ k₁ w₁)
    (hW₂ : Decided (S := S.chop G₂ d₂ hd₂) (chop U G₂) W₂ k₂ w₂)
    (hV : Decided U V (d₁ + k₁) fv) :
    w₁ = w₂
```

**G8.** Validators truncated at *different* horizons agree on every shared slot, from arbitrary views of their respective truncations — matched through the absolute slot index. The full-history verdict both are compared against is supplied under liveness by L8/L10. Horizons need never be negotiated: each admissible cut sees the same ledger.

#### `viewUpto_subset_viewUpto_succ`

*theorem, `GC.Horizon.lean`*

```lean
theorem viewUpto_subset_viewUpto_succ {R m : ℕ}
    (hED : EventuallyDelivers D R) (hcar : Populated U (m + 1))
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hR : R ≤ m + 1) :
    viewUpto D v m ⊆ viewUpto D w (m + 1)
```

**G9, the engine.** Post-`R`, everything **any** correct validator retains by round `m` is in **every** correct validator's store by `m + 1`: the keeper's round-`(m + 1)` block carries its whole store (`viewUpto_subset_history`, S10 + `includes`), and post-`R` that block is delivered to and accepted by every correct validator. Possession is universal one round deep.

#### `pruned_subset_peer_store`

*theorem, `GC.Horizon.lean`*

```lean
theorem pruned_subset_peer_store {R m : ℕ}
    (hED : EventuallyDelivers D R) (hcar : Populated U (m + 1))
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hR : R ≤ m + 1) :
    (viewUpto D v m).filter (fun i => (U.block i).round < G) ⊆
      viewUpto D w (m + 1)
```

**G9 (no desync).** What a validator prunes at any horizon, every correct peer already holds one round later: pruning below a correct frontier at depth `Λ ≥ 1` discards nothing a correct peer still lacks. A validator outside the envelope is on the bootstrap path, where the attested base takes over (G10–G12).

### Odontoceti

#### `not_directSkip_of_directCommit`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem not_directSkip_of_directCommit (hc : DirectCommit U L r)
    (hk : DirectSkip U L r) : False
```

**O1 (thesis Lemma 1).** No leader block is both directly committed and directly skipped: the two quorums share `n − 2f ≥ f+1` authors, all equivocators — one too many. Needs only `n ≥ 3f+1`.

#### `eq_of_directCommit`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem eq_of_directCommit {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

**O1′ (M5 analogue).** Two directly committed blocks by one author at one round are equal: their support quorums share `n − 2f ≥ f+1` authors, each supporting both — all equivocators. Needs only `n ≥ 3f+1`.

#### `card_supporters_le_of_directSkip`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem card_supporters_le_of_directSkip (hk : DirectSkip U L r) :
    (supporters U L (r + 1)).card ≤ 2 * F.f
```

**O2, the counting half.** A directly skipped leader's supporters — anywhere in the universe — number at most `2f`. The proof needs the exact complement identity `|Correct| = n − |byzantine|` (`card_correct_add_byzantine`): correct supporters and correct blamers are disjoint, correct blamers number at least `(n−f) − |byzantine|`, and the `|byzantine|` cancels.

#### `not_thickLink_of_directSkip`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem not_thickLink_of_directSkip (hk : DirectSkip U L r)
    (A : BlockId) : ¬ ThickLink U A L r
```

**O2 (thesis Lemma 2).** A directly skipped leader fails the indirect test against **every** anchor: `≤ 2f < n − 3f`. This is where `n ≥ 5f+1` is used.

#### `thickLink_of_directCommit`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem thickLink_of_directCommit (h : DirectCommit U L r) {A : BlockId}
    (hA : A ∈ U.ids) (hround : r + 2 ≤ (U.block A).round) :
    ThickLink U A L r
```

**O3 (thesis Lemma 3) — propagation, the heart.** If `L` is directly committed, then **every** block from two rounds above it on — Byzantine-authored included, validity is structural — carries at least `n − 3f` distinct authors of support blocks in its cone. One hop is quorum intersection minus the twin discount; depth is cone monotonicity. Every anchor's cone *is* the certificate.

#### `eq_of_directCommit_of_thickLink`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem eq_of_directCommit_of_thickLink {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : ThickLink U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

**O4′.** A directly committed block is the **only** same-author block that can pass the indirect test, at any anchor: `n−f` supporters of `L₁` and `n−3f` in-cone supporters of `L₂` would overlap in `≥ n−5f ≥ 1` correct authors, each supporting two twins — impossible. The second place `n ≥ 5f+1` bites, and the replacement for Mysticeti's M5′ in every direct-versus-indirect crossing.

#### `eligible_iff`

*theorem, `Odontoceti.Decision.lean`*

```lean
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j
```

Eligibility, unfolded. Two rounds rather than Mysticeti's three, which is what the stronger committee affords.

#### `lt_of_eligible`

*theorem, `Odontoceti.Decision.lean`*

```lean
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j
```

An eligible anchor is a later slot.

#### `decided_unique`

*theorem, `Odontoceti.Decision.lean`*

```lean
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂
```

**O5 (thesis Lemma 5; the M6 analogue).** No two validators reach conflicting decisions for a slot, whatever views they hold and whichever routes they took.

Structural induction on the first derivation, exactly M6's shape. The direct/direct diagonal closes by O1/O1′; every direct-versus-indirect crossing closes by O2/O3/O4′ — the two-round replacements for M2/M3/M4/M5′; and the one real case, indirect against indirect, closes by the anchor trichotomy: an earlier anchor is covered by the *other* validator's intermediate-skip premise, and a shared anchor forces a shared verdict — skip against commit by the `hnone` premise, commit against commit by canonicity, which is the step the thesis's Lemma 5 takes silently.

#### `safety`

*theorem, `Odontoceti.Decision.lean`*

```lean
theorem safety {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided U V₁ k (some L₁))
    (h₂ : Decided U V₂ k (some L₂)) : L₁ = L₂
```

**O6 (safety).** Two committed blocks for one slot are the same block, across any two views and any two routes.

#### `directCommit_of_votesAt`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem directCommit_of_votesAt {r : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1))
    (hv : VotesAt U T r L) :
    DirectCommit U L r
```

**The commit argument, stated once** — the two-round counterpart of `directCommit_of_certifiesAt`. A quorum-sized `T` whose blocks one round above `r` all vote for `L` directly commits it: a vote *is* a support, each `v ∈ T` has a supporting block by production, and `T`'s cardinality does the counting. Both pacing disciplines end here — the full-timeout one arriving through `votesAt_of_synchronisedOn`, the reactive one through `ReactivePace.votes`.

#### `directCommit_of_leader_mem`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem directCommit_of_leader_mem
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**O7, commit half (thesis Lemma 8 + Corollary 9).** Post-`R`, a `T`-led slot is directly committed: `SynchronisedOn` makes every `T` block at the decision round reference the leader's block, and `T` carries a quorum. Two populated rounds — propose and decide — and one synchronised step, routed through the targeted interface.

#### `directCommitIn_full`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem directCommitIn_full {r : ℕ} (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r
```

#### `decided_of_leader_mem`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem decided_of_leader_mem
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**O7, as a decision.**

#### `decided_of_correct_leader`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

The same at `T := Correct`.

#### `spansEligible_two`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem spansEligible_two (hid : ∀ k, S.slotRound k = k) :
    SpansEligible Validator 2
```

**O8.** Under a pipelined identity-round schedule, `c = 2` spans: slot `b − 1` cannot anchor on slot `b` — one round is one too close — but slot `b + 1` clears `slotRound + 2`. This is why the thesis's Lemma 10 asks for **two consecutive** honest leaders.

#### `decided_below_of_committed_run`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem decided_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided U V i v
```

**O9 (thesis Lemma 11).** Every slot below a committed run of eligible span is decided: walk down from the run, anchoring each slot on the nearest eligible committed slot above it — whose intermediate premise the induction supplies — and commit the **least** candidate passing the indirect test, exactly what the canonicity premise asks for.

#### `all_decided_below_of_fairRun`

*theorem, `Odontoceti.Liveness.lean`*

```lean
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v
```

**O10 (thesis Theorem 12).** Under production and post-`R` synchrony, a recurring run of `c` correct-led slots decides every slot below it — with the run placed past both the target and `R` by fairness. Note the horizon: the run's last slot needs rounds up to its `slotRound + 1` only.

### The reactive schedule

#### `le_built`

*theorem, `Reactive.Basic.lean`*

```lean
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ rc.top v, n ≤ rc.built v n
```

Rounds advance real time, over the rounds a validator reached.

#### `driftOn_of_catchup`

*theorem, `Reactive.Basic.lean`*

```lean
theorem driftOn_of_catchup
    (hcard : quorumCard Validator ≤ T.card) (hgst : rc.gst ≤ R) :
    DriftOn rc.built T R (rc.delay + rc.proc) N
```

**Drift is derived here too**, from the trunk's catch-up rule — the same collapse the timed discipline uses, with `le_built` supplied by `built_lt` rather than by the waiting floor.

#### `votes`

*theorem, `Reactive.Basic.lean`*

```lean
theorem votes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    VotesAt U T (S.slotRound k) L
```

**Every reliable vote block votes.** Past GST, with the timeout clearing `2Δ + proc`, every `T`-authored block at the round above a reliable leader references the leader's block — whether by the reactive exit or by the fallback.

The fallback case is the only argument: the leader holds its own block when it builds, convergence carries it across within `delay`, the collapsed drift (`driftOn_of_catchup` — no drift hypothesis is taken) and the full timeout place that arrival before the waiter's build, and the fallback clause then obliges the vote. The reactive exit needs nothing: it *is* the vote. Stated over any `T`-authored block, so non-equivocation is never consulted.

#### `built_succ_le_of_fast`

*theorem, `Reactive.Basic.lean`*

```lean
theorem built_succ_le_of_fast {δ : ℕ}
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      ≤ rc.built v (S.slotRound k) + D + δ + rc.proc
```

**Latency tracks delivery.** If every reliable round-`r` block — the leader's among them — reaches every reliable validator within `δ` of its build, then the round above is built within `D + δ + proc` of round entry: drift to the last builder, `δ` to arrive, `proc` to build. The timeout does not appear.

#### `no_timeout_of_fast`

*theorem, `Reactive.Basic.lean`*

```lean
theorem no_timeout_of_fast {δ : ℕ}
    (hδ : ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = S.slotRound k →
      b ∈ rc.holds v (rc.built ((U.block b).creator) (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator))
    (hfast : D + δ + rc.proc < rc.timeout (S.slotRound k)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      < rc.built v (S.slotRound k) + rc.timeout (S.slotRound k)
```

**The timeout never fires.** When delivery, drift and processing together undercut the timeout, every reliable validator builds strictly before its deadline — the fallback branch of `vote_or_wait` is never taken, and consensus proceeds at network speed.

#### `certifies`

*theorem, `Reactive.Mysticeti.lean`*

```lean
theorem certifies (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    CertifiesAt U T (S.slotRound k) L
```

**Every reliable certificate block certifies.** In the reactive exit the block certifies by construction. In the fallback, every reliable vote has arrived — each voter holds its own vote when it builds, convergence carries it across, and drift plus the full timeout place the arrival before the fallback build — so the block references all of `T`'s votes, and `T` is a quorum of distinct authors.

The vote blocks themselves come from the trunk's derived production (`PaceCore.populatedOn`): nothing here assumes a block exists.

#### `directCommit`

*theorem, `Reactive.Mysticeti.lean`*

```lean
theorem directCommit (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k)
```

**The reactive direct commit** — the shared counting theorem (`directCommit_of_certifiesAt`) fed by the reactive certificate supplier, with the certificate blocks from derived production. One application; the argument lives in `Liveness.lean`, once.

#### `decided`

*theorem, `Reactive.Mysticeti.lean`*

```lean
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**Reactive liveness (Mysticeti).** A reliable-led slot past GST is committed by every view — the conclusion of `decided_of_leader_mem`, with reference coverage replaced by the two reactive wait clauses and the leader block supplied by derived production.

#### `decided_local`

*theorem, `Reactive.Mysticeti.lean`*

```lean
theorem decided_local (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (rm.viewAt v (rm.latest (S.slotRound k + 2) + rm.delay)) k (some L)
```

**Reactive liveness is local too** (V18, reactive). Every reliable validator decides the slot on its own view, by the same explicit time as the timed discipline. The trunk supplies the argument (`decided_local_of_certifiesAt`); the reactive side supplies only its certificate stage, exactly as for the global statement. Reference coverage appears nowhere.

#### `committed_of_correct_block`

*theorem, `Reactive.Mysticeti.lean`*

```lean
theorem committed_of_correct_block
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairToEach (S := S) T) {u : Validator} (hu : u ∈ T) (R m : ℕ)
    (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧ S.leader k' = u ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (rm : ReactiveM U T N),
        rm.gst ≤ R →
        (∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∀ b ∈ U.ids, (U.block b).creator = u → (U.block b).round = m →
          ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) ∧
            Reaches U L b ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n
```

**RS5 — reactive inclusion.** For every round `m` and author `u ∈ T`, the schedule fixes a `u`-led slot above `m` before any execution is named, and every sufficiently grown reactive execution commits that slot with a leader block whose cone contains `u`'s round-`m` block — which is therefore in the agreed ledger of any verdict assignment covering the slot.

No coverage appears: the hypotheses are the reactive wait clauses, GST and the backoff, exactly as in `ReactiveM.decided`. What is added is only `FairToEach` — the schedule must return to `u` itself — and the self-parent chain does the rest.

#### `reactive_directCommit`

*theorem, `Reactive.Odontoceti.lean`*

```lean
theorem reactive_directCommit (rc : ReactivePace U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k)
```

**The reactive direct commit (Odontoceti)** — the shared counting theorem (`directCommit_of_votesAt`) fed by the reactive vote supplier, with the vote blocks from derived production. One application; the argument lives with O7, once.

#### `reactive_decided`

*theorem, `Reactive.Odontoceti.lean`*

```lean
theorem reactive_decided (rc : ReactivePace U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**Reactive liveness (Odontoceti).** A reliable-led slot past GST is committed by every view — the conclusion of the two-round `decided_of_leader_mem`, from the single reactive wait clause and the trunk's derived production. One delivery separates a fast leader from its commit.

### Safe Skip: crash recovery in one message

#### `hB1uniq_of_correct`

*theorem, `SafeSkip.Basic.lean`*

```lean
theorem hB1uniq_of_correct {v1 : Validator} {B1 : BlockId}
    (hB1 : B1 ∈ U.ids) (hB1c : (U.block B1).creator = v1)
    (hv1 : v1 ∈ (Correct : Finset Validator)) :
    ∀ j ∈ U.ids, (U.block j).creator = v1 →
      (U.block j).round = (U.block B1).round → j = B1
```

**The boundary condition from correctness.** For a `v1` outside the ambient model's Byzantine set, non-equivocation pins its round-`r0` block to `B1`. This is how a `SkipMsg` is built in the base fault model, and it is what the `hB1uniq` field generalises: report §14's hybrid model discharges the same field for a *crash-prone* `v1`, whom `Correct` excludes.

#### `mem_freshIds`

*theorem, `SafeSkip.Basic.lean`*

```lean
theorem mem_freshIds {b : BlockId} :
    b ∈ sk.freshIds ↔ ∃ k, sk.r0 < k ∧ k ≤ sk.r ∧ b = sk.fresh k
```

#### `skipFill_block_old`

*theorem, `SafeSkip.Basic.lean`*

```lean
@[simp] theorem skipFill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    sk.skipFill.block b = U.block b
```

Old blocks read unchanged: every store, view and certificate built on `U` sees the same data in the extension.

#### `skipFill_block_fresh`

*theorem, `SafeSkip.Basic.lean`*

```lean
@[simp] theorem skipFill_block_fresh {k : ℕ} :
    sk.skipFill.block (sk.fresh k) = sk.fillBlock k
```

#### `ids_subset_skipFill`

*theorem, `SafeSkip.Basic.lean`*

```lean
theorem ids_subset_skipFill : U.ids ⊆ sk.skipFill.ids
```

#### `skipFill_populatedOn`

*theorem, `SafeSkip.Basic.lean`*

```lean
theorem skipFill_populatedOn {T : Finset Validator} {k : ℕ}
    (hpop : PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    PopulatedOn sk.skipFill (insert sk.v1 T) k
```

**The gap is populated.** With `v1` restored to the reliable set, every gap round carries a `v1` block — the production hypothesis liveness consumes, recovered from one message.

#### `directSkip_fresh`

*theorem, `SafeSkip.Basic.lean`*

```lean
theorem directSkip_fresh {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hv1T : sk.v1 ∉ T)
    (hpop : PopulatedOn U T (k + 1)) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    DirectSkip sk.skipFill (sk.fresh k) k
```

**The fill cannot conjure a commit.** A filled block landing on a leader slot is directly skipped: no old block references a fresh id, so every reliable validator's block at the round above blames it. The mechanism restores production without touching the slots the network already passed.

#### `certificatesIn_fill`

*theorem, `SafeSkip.Invariance.lean`*

```lean
theorem certificatesIn_fill (V : View Validator BlockId Payload U)
    {L : BlockId} {r : ℕ} :
    certificatesIn sk.skipFill (sk.liftView V) L r = certificatesIn U V L r
```

Certificates a view holds read identically — again for every candidate.

#### `blameSetIn_fill`

*theorem, `SafeSkip.Invariance.lean`*

```lean
theorem blameSetIn_fill (V : View Validator BlockId Payload U)
    {L : BlockId} {r : ℕ} :
    ((blocksAt sk.skipFill (r + 1)).filter
        (fun q => L ∉ (sk.skipFill.block q).refs)) ∩ (sk.liftView V).ids =
      ((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids
```

The blocks a view holds that blame a candidate read identically — for every candidate, a fresh id lying in no old reference set.

#### `reaches_fill_old`

*theorem, `SafeSkip.Invariance.lean`*

```lean
theorem reaches_fill_old {a b : BlockId} (ha : a ∈ U.ids) :
    Reaches sk.skipFill a b ↔ b ∈ U.ids ∧ Reaches U a b
```

Reachability from an old block never leaves the old ids, in either universe, and coincides between them.

#### `decided_fill`

*theorem, `SafeSkip.Invariance.lean`*

```lean
theorem decided_fill {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId}
    (hq : ∀ n, sk.r0 < n → n ≤ sk.r →
      quorumCard Validator ≤
        (creatorsOf U.block ((blocksAt U (n + 1)) ∩ V.ids)).card)
    (h : Decided U V k v) :
    Decided sk.skipFill (sk.liftView V) k v
```

**Verdict invariance.** Every verdict a view reached in `U` re-derives, for the lifted view, in the extension.

The hypothesis `hq` is consumed at exactly one point: a slot of the recovering validator inside the gap, previously skipped for want of any candidate, must now be skipped by counting blames against the filled candidate — and the count is the view's quorum at the round above.

#### `decided_fill_agree`

*theorem, `SafeSkip.Invariance.lean`*

```lean
theorem decided_fill_agree {V : View Validator BlockId Payload U}
    {W : View Validator BlockId Payload sk.skipFill} {k : ℕ}
    {v w : Option BlockId}
    (hq : sk.QuorateOverGap V)
    (hv : Decided U V k v) (hw : Decided sk.skipFill W k w) : v = w
```

**Agreement across a recovery.** A verdict reached before the fill agrees with any verdict reached after it, whatever view either side held — verdict invariance composed with agreement in the extension.

#### `SkipMsg.line_eq_lineOf`

*theorem, `SafeSkip.Jump.lean`*

```lean
theorem SkipMsg.line_eq_lineOf (sk : SkipMsg U) :
    ∀ k, sk.r0 ≤ k → k ≤ sk.r → sk.line k = lineOf U (sk.line sk.r) k
```

**SS8.** A `SkipMsg`'s donor line is determined by its top block: on the whole interval the message's clauses govern, `line` coincides with the chain derived by following self-parents down from `line r`. The step is P2 through `eq_selfParent_of_mem`: the chain clause hands the line's next block to the one above as an own-creator reference, and there is only one of those.

#### `SkipMsg.skipFill_eq_of_core`

*theorem, `SafeSkip.Jump.lean`*

```lean
theorem SkipMsg.skipFill_eq_of_core [DecidableEq BlockId] (sk₁ sk₂ : SkipMsg U)
    (hB1 : sk₁.B1 = sk₂.B1) (hr : sk₁.r = sk₂.r)
    (htop : sk₁.line sk₁.r = sk₂.line sk₂.r) (hfresh : sk₁.fresh = sk₂.fresh) :
    sk₁.skipFill.ids = sk₂.skipFill.ids
      ∧ ∀ b ∈ sk₁.skipFill.ids, sk₁.skipFill.block b = sk₂.skipFill.block b
```

**SS9.** Two messages naming the same anchor and the same target, drawing fresh identifiers from the same supply, denote observationally equal universes: the identifier sets are equal and the blocks agree at every member. Stated in the style of `regenesis_converges` — the two objects may differ on junk outside their identifiers, which nothing reads.

The decoder needs no hypothesis: `block` consults `idx` only at fresh identifiers, where `hidx` pins both decoders to the same index.

#### `toSkipMsg_top`

*theorem, `SafeSkip.Jump.lean`*

```lean
@[simp] theorem toSkipMsg_top : j.toSkipMsg.line j.toSkipMsg.r = j.B2
```

#### `lineOf_mem_view`

*theorem, `SafeSkip.Jump.lean`*

```lean
theorem lineOf_mem_view (V : View Validator BlockId Payload U) {B2 : BlockId}
    (hB2 : B2 ∈ U.ids) (hB2V : B2 ∈ V.ids) :
    ∀ k, k ≤ (U.block B2).round → lineOf U B2 k ∈ V.ids
```

**SS10a: the receiver holds everything the elaboration reads.** Views are closed downward, so a view holding the target holds the whole derived line — the sender's message points at nothing a receiver lacks.

#### `JumpMsg.denote_eq_of_core`

*theorem, `SafeSkip.Jump.lean`*

```lean
theorem JumpMsg.denote_eq_of_core [DecidableEq BlockId] (j₁ j₂ : JumpMsg U)
    (hB1 : j₁.B1 = j₂.B1) (hB2 : j₁.B2 = j₂.B2) (hfresh : j₁.fresh = j₂.fresh) :
    j₁.denote.ids = j₂.denote.ids
      ∧ ∀ b ∈ j₁.denote.ids, j₁.denote.block b = j₂.denote.block b
```

**SS10b: derivations converge.** Two jump messages with the same compact core denote observationally equal universes — since views share `U.block`, every receiver elaborating the message arrives at this one object. The elaborated lines both being the derived chain, this is SS9 applied to the elaborations.

### Integration: composing the arcs

#### `honestNoEquiv_chop`

*theorem, `Integration.Preservation.lean`*

```lean
theorem honestNoEquiv_chop (hne : HonestNoEquiv U) :
    HonestNoEquiv (chop U G)
```

**I2.** Truncation preserves honest non-equivocation.

#### `synchronisedOn_chop`

*theorem, `Integration.Preservation.lean`*

```lean
theorem synchronisedOn_chop (hs : SynchronisedOn U T R) (hGR : R ≤ G + R') :
    SynchronisedOn (chop U G) T R'
```

**I4.** Truncation preserves coverage, with the horizon offset.

The referencing block sits at chopped round `n + 1`, hence at original round `G + n + 1`, strictly above the cut — so `chop` retains its references verbatim and the original clause applies directly.

#### `honestNoEquiv_skipFill`

*theorem, `Integration.Preservation.lean`*

```lean
theorem honestNoEquiv_skipFill (sk : SkipMsg U) (hne : HonestNoEquiv U) :
    HonestNoEquiv sk.skipFill
```

**I3.** The Safe Skip fill preserves honest non-equivocation.

#### `not_synchronisedOn_skipFill`

*theorem, `Integration.Coverage.lean`*

```lean
theorem not_synchronisedOn_skipFill (sk : SkipMsg U) {T : Finset Validator}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ SynchronisedOn sk.skipFill T R
```

**I5, refuted.** The fill does not restore coverage. If the recovering validator is counted reliable — which is exactly what SS2 does — then at any gap round `k` above the coverage round, an old reliable block at `k+1` fails to reference the filled block at `k`, because no old block references a fresh identifier.

The hypotheses are the situation SS2 creates, not a contrived one: `hv1` puts `v1` in the reliable set, `hk` places the gap round in the covered range, and `hb` asks only that some reliable validator built at the round above — which `PopulatedOn` supplies.

#### `synchronisedOn_skipFill_of_notMem`

*theorem, `Integration.Coverage.lean`*

```lean
theorem synchronisedOn_skipFill_of_notMem (sk : SkipMsg U) {T : Finset Validator}
    {R : ℕ} (hs : SynchronisedOn U T R) (hv1 : sk.v1 ∉ T) :
    SynchronisedOn sk.skipFill T R
```

**The refutation is narrow: it is about counting the recovering validator reliable during the gap it slept through.** Exclude it from the reliable set and coverage is untouched — the fill's blocks are its alone, so the clause never quantifies over them.

Together with `not_synchronisedOn_skipFill` and `synchronisedOn_skipFill_above` this is the whole picture. Coverage fails only where it should: over a set that includes the recovering validator, at rounds during which it was absent. It holds for every other set, and for every set above the fill.

#### `synchronisedOn_skipFill_above`

*theorem, `Integration.Coverage.lean`*

```lean
theorem synchronisedOn_skipFill_above (sk : SkipMsg U) {T : Finset Validator}
    {R R' : ℕ} (hs : SynchronisedOn U T R) (hR : R ≤ R') (hR' : sk.r < R') :
    SynchronisedOn sk.skipFill T R'
```

**I5, positively.** Coverage holds *strictly* above the fill: past the target round every block is old, references are preserved, and the original condition applies unchanged. This is the form a liveness argument after recovery consumes — the recovered validator is building its own blocks again, and the network covers them in the ordinary way.

The strictness is not slack in the proof. At `n = sk.r` the lower block may still be the last filled one, and `not_synchronisedOn_skipFill` refutes coverage there; `sk.r < R'` is exactly the first round at which every block in play is old.

#### `le_slotRound_add`

*theorem, `Integration.ScheduleShape.lean`*

```lean
theorem le_slotRound_add (S : Slots Validator) (hd : G ≤ S.slotRound d) (k : ℕ) :
    G ≤ S.slotRound (d + k)
```

Every slot at or above the base slot has its round above the cut — the fact that makes the rebasing subtraction faithful.

#### `fairScheduleOn_chop`

*theorem, `Integration.ScheduleShape.lean`*

```lean
theorem fairScheduleOn_chop (S : Slots Validator) (hd : G ≤ S.slotRound d)
    (h : FairScheduleOn (S := S) T) :
    FairScheduleOn (S := S.chop G d hd) T
```

**I13.** Truncation preserves schedule fairness: a reliable leader arbitrarily far out in the original schedule is one arbitrarily far out in the re-indexed one, found by shifting the search past the base slot.

#### `fairRunOn_chop`

*theorem, `Integration.ScheduleShape.lean`*

```lean
theorem fairRunOn_chop (S : Slots Validator) (hd : G ≤ S.slotRound d)
    (h : FairRunOn (S := S) T c) :
    FairRunOn (S := S.chop G d hd) T c
```

**I13, run form.** The same for runs of `c` consecutive reliable-led slots, which is what the liveness capstones consume.

#### `spansEligible_chop`

*theorem, `Integration.ScheduleShape.lean`*

```lean
theorem spansEligible_chop (S : Slots Validator) (hd : G ≤ S.slotRound d)
    (h : SpansEligible (Validator := Validator) (S := S) c) :
    SpansEligible (Validator := Validator) (S := S.chop G d hd) c
```

**I15.** Truncation preserves the spanning property. Eligibility is a statement about rounds, which the truncation rebases by `−G`; the base-slot condition keeps every round in play above the cut, where the subtraction is faithful and the original inequality transfers.

#### `joiner_assign_agree`

*theorem, `Integration.Joiner.lean`*

```lean
theorem joiner_assign_agree {V : View Validator BlockId Payload U}
    {pick' : BlockUniverse Validator BlockId Payload →
      (ℕ → Option BlockId) → ℕ → Validator}
    (hs : HorizonStable P d G pick') (R : AdaptiveRun P U V) (k : ℕ) :
    pick' (chop U G) (fun m => R.vdct (d + m)) k = R.assign (d + k)
```

**I9, the assignment half.** Under a horizon-stable rule a joiner computes exactly the leaders the network is using: its assignment at its own slot `k` is the full-history run's assignment at slot `d + k`.

Nothing here is about verdicts — it is the statement that the two validators do not *disagree about who leads*, which is the premise any agreement argument between them must have and the thing garbage collection threatened.

#### `epochOf_add_of_dvd`

*theorem, `Integration.Joiner.lean`*

```lean
theorem epochOf_add_of_dvd {W : ℕ} (hW : 0 < W) (hdvd : W ∣ d) (k : ℕ) :
    epochOf W (d + k) = d / W + epochOf W k
```

**Epoch alignment.** When the base slot is a whole number of epochs, the joiner's epoch numbering is the network's shifted by a constant, and every epoch window corresponds.

#### `anchor_pruned`

*theorem, `Integration.Retention.lean`*

```lean
theorem anchor_pruned (sk : SkipMsg U) (hG : (U.block sk.B1).round < G)
    (sk' : SkipMsg (chop U G)) : sk'.B1 ≠ sk.B1
```

**I7a.** A horizon past the crash round prunes the anchor, and a pruned anchor cannot be used: every `SkipMsg` over the truncation must name a different one. This is the constraint, stated sharply.

#### `no_blocks_of_no_genesis`

*theorem, `Integration.Retention.lean`*

```lean
theorem no_blocks_of_no_genesis {v : Validator}
    (hgen : ∀ b ∈ U.ids, (U.block b).creator = v → (U.block b).round ≠ 0) :
    ∀ b ∈ U.ids, (U.block b).creator ≠ v
```

**A severed chain cannot restart.** With no block at round `0`, a validator has no block at any round: P3′ walks every block down to genesis one round at a time, and P1 supplies the descent.

Stated for an arbitrary universe because it is not about garbage collection — it is what P3′ means. Report §2.2 records that safety and liveness never consume the clause; this is a place where its *absence* would be felt, and it is consumed here to say what the clause costs.

#### `severed_of_pruned_anchor`

*theorem, `Integration.Retention.lean`*

```lean
theorem severed_of_pruned_anchor (sk : SkipMsg U)
    (hG1 : sk.r0 < G) (hG2 : G ≤ sk.r) :
    ∀ b ∈ (chop U G).ids, ((chop U G).block b).creator ≠ sk.v1
```

**The recovering validator is severed, not merely unable to fill.** If the horizon has passed the crash round, the crashed validator has no block in the truncation's genesis layer — `hgap` says it authored nothing there — so by `no_blocks_of_no_genesis` it has no block in the truncation at all.

This is why filling only the retained rounds is not a repair: there is nothing to chain the first filled block to, and the same obstruction blocks *any* attempt to resume, Safe Skip or otherwise. Rejoining after a horizon has passed one's whole history needs a protocol provision the model does not have — a re-genesis block, exempt from P3′ — and the practical alternative is the one I7 quantifies: keep the lag longer than the outage.

#### `outage_bounded_by_lag`

*theorem, `Integration.Retention.lean`*

```lean
theorem outage_bounded_by_lag (sk : SkipMsg U) {Λ : ℕ}
    (hlag : G + Λ = sk.r) (hr : sk.r0 ≤ sk.r) :
    G ≤ sk.r0 ↔ sk.r - sk.r0 ≤ Λ
```

**The lag bounds the recoverable outage.** With the horizon trailing the recovery round by `Λ`, the anchor survives exactly when the outage did not exceed `Λ`.

So the two mechanisms are coupled by one inequality: *garbage collection at lag `Λ` supports Safe Skip recovery from outages of up to `Λ` rounds, and no more.* Beyond it the validator's last block has been pruned and it must bootstrap by report §9.5's attested base — which is why the two routes exist, and where the boundary between them falls.

#### `addGenesis_block_new`

*theorem, `Integration.ReGenesis.lean`*

```lean
@[simp] theorem addGenesis_block_new {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} :
    (addGenesis V v g p hg hsev).block g = ⟨0, v, ∅, p⟩
```

#### `populatedOn_addGenesis`

*theorem, `Integration.ReGenesis.lean`*

```lean
theorem populatedOn_addGenesis {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} {T : Finset Validator}
    (hpop : PopulatedOn V T 0) :
    PopulatedOn (addGenesis V v g p hg hsev) (insert v T) 0
```

**The chain restarts.** After re-genesis the stranded validator has a block at round `0`, so it is no longer severed: `no_blocks_of_no_genesis` no longer applies to it, and an ordinary Safe Skip anchored on the new block fills the rounds above.

Stated as the population fact liveness consumes — the validator is back in the genesis layer, which is the hypothesis P8 asks for at round `0`.

#### `dosValid_addGenesis`

*theorem, `Integration.ReGenesis.lean`*

```lean
theorem dosValid_addGenesis (hdos : DoSValid V) :
    DoSValid (addGenesis V v g p hg hsev)
```

**I19a.** Re-genesis preserves the exposure condition. A block with no references can neither cite an exposed author nor enlarge anyone else's cone, so report §8's per-cone bound applies to the extended universe unchanged.

#### `chop_addGenesis`

*theorem, `Integration.ReGenesis.lean`*

```lean
theorem chop_addGenesis (hd : 0 < d)
    {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} :
    (chop (addGenesis V v g p hg hsev) d).ids = (chop V d).ids
      ∧ ∀ b ∈ (chop V d).ids,
          (chop (addGenesis V v g p hg hsev) d).block b = (chop V d).block b
```

**A derived genesis is pruned by the next cut, without trace.** Any further truncation removes the round-`0` block and leaves the ordinary truncation of what lay beneath.

Stated observationally — identifiers, and blocks at those identifiers — because the two universes differ on the junk outside their identifier sets, which nothing consults.

#### `regenesis_converges`

*theorem, `Integration.ReGenesis.lean`*

```lean
theorem regenesis_converges {U : BlockUniverse Validator BlockId Payload}
    {G₁ G₂ : ℕ} (hG : G₁ < G₂)
    {hg : g ∉ (chop U G₁).ids}
    {hsev : ∀ b ∈ (chop U G₁).ids, ((chop U G₁).block b).creator ≠ v} :
    (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).ids
        = (chop U G₂).ids
      ∧ ∀ b ∈ (chop U G₂).ids,
          (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).block b
            = (chop U G₂).block b
```

**The convergence.** A validator at horizon `G₁`, truncating on to a later horizon `G₂`, holds exactly the blocks of a validator that cut at `G₂` directly — its derived genesis having been pruned on the way. Both then derive the same genesis from the same base, so heterogeneous horizons need no agreement.

The identifier sets are equal and the blocks agree on them; the two universes are the same object as far as anything that reads them is concerned.

#### `hB1uniq_of_addGenesis`

*theorem, `Integration.ReGenesis.lean`*

```lean
theorem hB1uniq_of_addGenesis :
    ∀ j ∈ (addGenesis V v g p hg hsev).ids,
      ((addGenesis V v g p hg hsev).block j).creator = v →
      ((addGenesis V v g p hg hsev).block j).round
        = ((addGenesis V v g p hg hsev).block g).round → j = g
```

**The re-genesis block is a lawful Safe Skip anchor.** Uniqueness at its round is immediate from the absence that licensed it.

#### `honestNoEquiv_stack`

*theorem, `Integration.Stack.lean`*

```lean
theorem honestNoEquiv_stack (sk : SkipMsg U) (hne : HonestNoEquiv U) :
    HonestNoEquiv (stack sk G)
```

**I16a.** Honest non-equivocation survives the whole stack — I3 then I2, with no new argument. This is what lets the hybrid safety development be used by a validator that both recovered and pruned.

#### `synchronisedOn_stack`

*theorem, `Integration.Stack.lean`*

```lean
theorem synchronisedOn_stack (sk : SkipMsg U) {T : Finset Validator} {R R' R'' : ℕ}
    (hs : SynchronisedOn U T R) (hR : R ≤ R') (hfill : sk.r < R')
    (hcut : R' ≤ G + R'') :
    SynchronisedOn (stack sk G) T R''
```

**I16b.** Coverage survives the stack above the fill and the cut — I5-positive then I4. The two offsets compose exactly as their statements suggest: the fill demands strictly above `sk.r`, the truncation shifts by `G`.

#### `hybrid_agree_stack`

*theorem, `Integration.Stack.lean`*

```lean
theorem hybrid_agree_stack [LinearOrder BlockId] [S : Slots Validator]
    (sk : SkipMsg U) (hne : HonestNoEquiv U) {k : ℕ}
    (hk : Hybrid.Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload (stack sk G)} {s : ℕ}
    {v₁ v₂ : Option BlockId}
    (h₁ : Hybrid.Decided k (stack sk G) V₁ s v₁)
    (h₂ : Hybrid.Decided k (stack sk G) V₂ s v₂) : v₁ = v₂
```

**I16d — the payoff.** Hybrid agreement holds in the stacked universe: a validator that recovered from a crash by Safe Skip and then pruned below a horizon still cannot disagree with anyone about a slot's verdict, at any admissible threshold.

Every hypothesis is one of report §14's own, discharged for the stack by `honestNoEquiv_stack`; the theorem body is `Hybrid.decided_unique` applied to a different universe. Nothing about the fill or the cut is re-proved, which is the thesis of this document in one statement.

#### `hB1uniq_of_crash`

*theorem, `Integration.Lifecycle.lean`*

```lean
theorem hB1uniq_of_crash (hne : HonestNoEquiv U) {v1 : Validator} {B1 : BlockId}
    (hB1 : B1 ∈ U.ids) (hB1c : (U.block B1).creator = v1)
    (hv1 : v1 ∉ H.byzantine) :
    ∀ j ∈ U.ids, (U.block j).creator = v1 →
      (U.block j).round = (U.block B1).round → j = B1
```

**I10, the enabling lemma.** In the hybrid model a *crash-prone* validator satisfies Safe Skip's boundary condition: it is honest, and `HonestNoEquiv` pins its round-`r0` block to the anchor. The base model's `hB1uniq_of_correct` cannot serve here — `Correct` excludes the crash class by construction — which is precisely why report §12's hypothesis needed to be stated as the fact rather than as membership.

#### `lifecycle`

*theorem, `Integration.Lifecycle.lean`*

```lean
theorem lifecycle {V : View Validator BlockId Payload U} {k : ℕ}
    (sk : SkipMsg U) (hne : HonestNoEquiv U) {T : Finset Validator}
    (hhalt : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k)
    {m : ℕ} (hpop : PopulatedOn U T m) (hm1 : sk.r0 < m) (hm2 : m ≤ sk.r) :
    Decided U V k none
      ∧ PopulatedOn sk.skipFill (insert sk.v1 T) m
      ∧ HonestNoEquiv sk.skipFill
```

**The lifecycle, in one statement.** A validator that halts has its slot skipped (L5, unchanged); after it rejoins by Safe Skip its gap rounds are populated with it back in the reliable set (SS2); and the resulting universe still carries honest non-equivocation (I3), so report §14's safety applies throughout.

Three arcs — the base liveness rules, Safe Skip, and the hybrid fault model — meet here without any of them mentioning another. What connects them is that all three speak about the same universe and the same verdicts, which is what report §2's invariant vocabulary was collected to make possible.

#### `history_B1_subset_fill`

*theorem, `Integration.Exposure.lean`*

```lean
theorem history_B1_subset_fill (sk : SkipMsg U) (hne : sk.r0 < sk.r) :
    history U sk.B1 ⊆ history sk.skipFill (sk.fresh (sk.r0 + 1))
```

The anchor's whole cone lies in the filled block's cone. Needs the gap to be nonempty, which is when there is anything to fill.

#### `history_skipFill_old`

*theorem, `Integration.Exposure.lean`*

```lean
theorem history_skipFill_old {b : BlockId} (hb : b ∈ U.ids) :
    history sk.skipFill b = history U b
```

An old block's cone is unchanged by the fill: reachability from an old block stays among old blocks.

#### `exposedIn_skipFill_old`

*theorem, `Integration.Exposure.lean`*

```lean
theorem exposedIn_skipFill_old {b : BlockId} (hb : b ∈ U.ids) {X : Validator} :
    ExposedIn sk.skipFill b X ↔ ExposedIn U b X
```

Exposure is unchanged at an old block, in both directions.

#### `dosValid_skipFill`

*theorem, `Integration.Exposure.lean`*

```lean
theorem dosValid_skipFill (hdos : DoSValid U)
    (hnew : ∀ k, sk.r0 < k → k ≤ sk.r →
      ∀ i ∈ (sk.skipFill.block (sk.fresh k)).refs,
        ¬ ExposedIn sk.skipFill (sk.fresh k) (sk.skipFill.block i).creator) :
    DoSValid sk.skipFill
```

**I1.** The fill can break the exposure condition only at its own blocks. Given `DoSValid U`, the extension is `DoSValid` as soon as each filled block is sound — a condition on the fill alone, which a recipient checks by computing the fill and inspecting it.

This is the form report §8 asks of its clauses: structural, author-blind, and checkable by the party it binds. The predicted failure (`history_B1_subset_fill`) is not thereby avoided — a fill whose enlarged cone exposes a donor citation simply fails the check, and is refused rather than accepted and unsound.

#### `fill_cone_subset`

*theorem, `Integration.Exposure.lean`*

```lean
theorem fill_cone_subset (sk : SkipMsg U)
    (hcov : ∀ k, sk.r0 < k → k ≤ sk.r → sk.B1 ∈ history U (sk.line k)) :
    ∀ k, sk.r0 < k → k ≤ sk.r → ∀ i, Reaches sk.skipFill (sk.fresh k) i →
      i ∈ sk.freshIds ∨ i ∈ history U (sk.line k)
```

#### `dosValid_skipFill_of_covered`

*theorem, `Integration.Exposure.lean`*

```lean
theorem dosValid_skipFill_of_covered (hdos : DoSValid U)
    (hcov : ∀ k, sk.r0 < k → k ≤ sk.r → sk.B1 ∈ history U (sk.line k))
    (hv1ne : ∀ p ∈ U.ids, ∀ q ∈ U.ids, (U.block p).creator = sk.v1 →
      (U.block q).creator = sk.v1 → (U.block p).round = (U.block q).round → p = q) :
    DoSValid sk.skipFill
```

**I14.** The enforceable check reduces to reachability. If each donor block reaches the anchor and `v1` never equivocates, the fill preserves the exposure condition outright — no exposure computation over the extension is needed.

This is the deployable form: a recipient verifies that the donor line covers the anchor, which is one reachability query per gap round against its own DAG.

#### `uniformBudget_skipFillD`

*theorem, `Integration.DeliveryFill.lean`*

```lean
theorem uniformBudget_skipFillD {T : ℕ} (hu : UniformBudget D T) :
    UniformBudget (skipFillD sk D hdown) T
```

**I15b — the budget transfers.** Novelty is measured over the cone of an accepted block against the accumulated view, and both are unchanged, so the author-blind budget holds of the fill's delivery at the same constant.

#### `not_refsAccepted_skipFillD`

*theorem, `Integration.DeliveryFill.lean`*

```lean
theorem not_refsAccepted_skipFillD (hne : sk.r0 < sk.r)
    (hv1 : sk.v1 ∈ (Correct : Finset Validator)) :
    ¬ RefsAccepted (skipFillD sk D hdown)
```

**I15c — the reference discipline does not transfer, and the failure is the mechanism's own.** `RefsAccepted` is the converse of `includes`: a correct validator references *only* what it accepted. A filled block references the donor's blocks, which the recovering validator did not accept — it was down. So the discipline fails at every filled block.

This is not a defect of the transformer but a description of what Safe Skip does. The fill asserts references on `v1`'s behalf for rounds it slept through; `RefsAccepted` says a validator cites only what reached it. The two cannot both hold of a retroactive reconstruction under the delivery structure that records what actually arrived.

The alternative is to model recovery as *acceptance at recovery time* — `v1` obtains the donor's blocks when it rejoins, and accepts exactly what its filled blocks cite. Both `includes` and `RefsAccepted` then hold by construction, `accepted_inj` following from the P2 clause `skipFill` already proves for `fillBlock`. What that model does not give away is the budget: the novelty of the newly accepted blocks is then a property of the fill, to be checked as in report §16.7 rather than inherited. Which model is right is a specification question about what a `Delivery` is meant to record, and it is recorded here rather than settled.

#### `notMem_of_no_blocks`

*theorem, `Integration.Margin.lean`*

```lean
theorem notMem_of_no_blocks {T : Finset Validator} {r : ℕ} {v : Validator}
    (hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v)
    (hpop : PopulatedOn U T r) : v ∉ T
```

A validator with no blocks belongs to no populated set: production is what membership of a reliable set asserts.

#### `card_severed_le`

*theorem, `Integration.Margin.lean`*

```lean
theorem card_severed_le {T S : Finset Validator} {r : ℕ}
    (hsev : ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).creator ≠ v)
    (hpop : PopulatedOn U T r)
    (hcard : quorumCard Validator ≤ T.card) :
    S.card ≤ F.f
```

**I17.** At most `f` validators can be severed at once without costing liveness. A reliable set of quorum size is disjoint from every severed validator, so the severed cannot number more than the fault budget — and a validator recovering from an outage longer than the horizon lag is severed until it re-genesises.

The hypothesis is the one every liveness capstone carries; the conclusion prices the recovery window.

#### `card_novelty_le_of_donor`

*theorem, `Integration.Margin.lean`*

```lean
theorem card_novelty_le_of_donor {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted w (n + 1))
    {c : BlockId} (hc : c ∈ U.ids) (hcc : (U.block c).creator = w)
    (hcr : (U.block c).round = n + 1) :
    (novelty U (viewUpto D v (n + 1)) b).card ≤ F.f * κ + 1
```

**I18.** The novelty budget holds for a block whose references lie inside **any** correct validator's acceptances, provided that validator has a block at the round — not specifically the block's own author.

Report §8.4's `RefsAccepted` asks for the author, and the pool argument uses only this. The two component lemmas were already stated at the right generality; composing them at a `w` other than the author is what had not been done.

#### `exists_commonAt`

*theorem, `Integration.CommonTarget.lean`*

```lean
theorem exists_commonAt {r : ℕ} {c₀ : BlockId} (hc₀ : c₀ ∈ U.ids)
    (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b, CommonAt U b r ∧ (U.block b).creator ∈ (Correct : Finset Validator)
```

**Common blocks exist at every round**, and are correct-authored — T3c restated in the vocabulary above. The hypothesis is only that some block exists two rounds up, which is what having a round to fill means.

#### `fill_refs_available`

*theorem, `Integration.CommonTarget.lean`*

```lean
theorem fill_refs_available (sk : SkipMsg U)
    (hcom : ∀ k, sk.r0 < k → k ≤ sk.r → CommonAt U (sk.line k) k)
    {k : ℕ} (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = k + 2)
    {i : BlockId} (hi : i ∈ (U.block (sk.line k)).refs) :
    i ∈ history U c
```

**I19 — a fill against a common donor line transmits nothing.** Every reference the fill copies at a gap round lies in the causal past of every validator holding a block two rounds above that round.

So the recipients need no blocks they lack: naming the target suffices, and each reconstructs the filled blocks from its own DAG. The `prev` reference is the recovering validator's own chain, supplied by the fill itself, so the copied references are the whole of what would otherwise have to be sent.

### Hybrid fault tolerance: Byzantine and crash faults apart

#### `mem_honest`

*theorem, `Hybrid.Faults.lean`*

```lean
theorem mem_honest {v : Validator} :
    v ∈ Honest Validator ↔ v ∉ H.byzantine
```

#### `card_honest_add_byzantine`

*theorem, `Hybrid.Faults.lean`*

```lean
theorem card_honest_add_byzantine :
    (Honest Validator).card + H.byzantine.card = Fintype.card Validator
```

The honest and Byzantine classes partition the committee — the complement identity the counting arguments cancel against.

#### `exists_honest_mem_inter`

*theorem, `Hybrid.Faults.lean`*

```lean
theorem exists_honest_mem_inter {a b : Finset Validator}
    (hab : Fintype.card Validator + H.fb < a.card + b.card) :
    ∃ v ∈ a ∩ b, v ∉ H.byzantine
```

**H1 — the counting core.** Two author sets whose sizes sum past `n + fb` share an honest member: their intersection outnumbers the Byzantine class. T0′ with the discount at `fb` rather than the derived `fb + fc`; every conflict argument of the arc is one application of this plus the observation that an honest validator's single block cannot face both ways.

#### `eq_of_creator_eq_honest`

*theorem, `Hybrid.Faults.lean`*

```lean
theorem eq_of_creator_eq_honest {U : BlockUniverse Validator BlockId Payload}
    (hne : HonestNoEquiv U) {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∉ H.byzantine)
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j
```

T1 at the honest class: two ids with one honest author and one round are one id.

#### `not_directSkip_of_directCommit`

*theorem, `Hybrid.Rules.lean`*

```lean
theorem not_directSkip_of_directCommit (hne : HonestNoEquiv U)
    (hc : DirectCommit U L r) (hk : DirectSkip U L r) : False
```

**H2 (O1's mirror).** No leader block is both directly committed and directly skipped: the two `q`-quorums overlap past the Byzantine class. Needs only `n > 3·fb + 2·fc`.

#### `eq_of_directCommit`

*theorem, `Hybrid.Rules.lean`*

```lean
theorem eq_of_directCommit (hne : HonestNoEquiv U) {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

**Twin uniqueness for direct commits (O1′'s mirror).** Needs only `n > 3·fb + 2·fc`.

#### `card_supporters_le_of_directSkip`

*theorem, `Hybrid.Rules.lean`*

```lean
theorem card_supporters_le_of_directSkip (hne : HonestNoEquiv U)
    (hk : DirectSkip U L r) :
    (supporters U L (r + 1)).card ≤ 2 * H.fb + H.fc
```

**H3, the counting half.** A directly skipped leader's supporters — anywhere in the universe — number at most `2·fb + fc`: honest supporters and honest blamers are disjoint within the `n − fb` honest validators, the blamers number at least `q − fb` of them, and the complement identity cancels.

#### `not_thickLink_of_directSkip`

*theorem, `Hybrid.Rules.lean`*

```lean
theorem not_thickLink_of_directSkip (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k) (hk : DirectSkip U L r)
    (A : BlockId) : ¬ ThickLink k U A L r
```

**H3 (O2's mirror).** A directly skipped leader fails the indirect test against every anchor, at every admissible threshold: its supporters number at most `2·fb + fc`, below the interval's lower end. This is where the lower half of admissibility is consumed.

#### `thickLink_of_directCommit`

*theorem, `Hybrid.Rules.lean`*

```lean
theorem thickLink_of_directCommit (hne : HonestNoEquiv U)
    (hkb : k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator)
    (h : DirectCommit U L r) {A : BlockId}
    (hA : A ∈ U.ids) (hround : r + 2 ≤ (U.block A).round) :
    ThickLink k U A L r
```

**H4 (O3's mirror) — link integrity.** If `L` is directly committed, every block from two rounds above it on carries at least `k` distinct support authors in its cone, for every admissible `k`: one hop is quorum intersection at `2q − n − fb = n − 3·fb − 2·fc ≥ k` — the interval's upper end, consumed exactly here — and depth is cone monotonicity.

#### `eq_of_directCommit_of_thickLink`

*theorem, `Hybrid.Rules.lean`*

```lean
theorem eq_of_directCommit_of_thickLink (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k) {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : ThickLink k U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

**H5 (O4′'s mirror).** A directly committed block is the only same-author block that can pass the indirect test at any anchor: `q` supporters of `L₁` and `k` in-cone supporters of `L₂` overlap past the Byzantine class — `q + k > n + fb` is the interval's lower end again — and an honest overlap member supports two twins, which P2 and honesty jointly forbid.

#### `eligible_iff`

*theorem, `Hybrid.Decision.lean`*

```lean
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j
```

Eligibility, unfolded: two rounds.

#### `lt_of_eligible`

*theorem, `Hybrid.Decision.lean`*

```lean
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j
```

An eligible anchor is a later slot.

#### `decided_unique`

*theorem, `Hybrid.Decision.lean`*

```lean
theorem decided_unique (hne : HonestNoEquiv U)
    (hk : Admissible Validator k)
    {V₁ : View Validator BlockId Payload U} {s : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided k U V₁ s v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided k U V₂ s v₂ → v₁ = v₂
```

**H6 (agreement; the O5 mirror).** No two validators reach conflicting decisions for a slot at any admissible threshold, whatever views they hold and whichever routes they took. The sixteen-case induction of O5 and M6: the direct diagonal by H2 and twin uniqueness, every direct-versus-indirect crossing by H3, H4 or H5, and the shared anchor forced by `anchor_eq` with canonicity arbitrating the commit-commit case.

#### `decided_agree`

*theorem, `Hybrid.Decision.lean`*

```lean
theorem decided_agree (hne : HonestNoEquiv U) (hk : Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload U} {s : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided k U V₁ s v₁)
    (h₂ : Decided k U V₂ s v₂) : v₁ = v₂
```

Agreement, in M6's binary shape.

#### `safety`

*theorem, `Hybrid.Decision.lean`*

```lean
theorem safety (hne : HonestNoEquiv U) (hk : Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload U} {s : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided k U V₁ s (some L₁))
    (h₂ : Decided k U V₂ s (some L₂)) : L₁ = L₂
```

**Safety.** Two committed blocks for one slot are the same block, across any two views and any two routes.

#### `directCommit_of_leader_mem`

*theorem, `Hybrid.Liveness.lean`*

```lean
theorem directCommit_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ DirectCommit U L (S.slotRound s)
```

**H7, commit half (O7's mirror).** Post-`R`, a `T`-led slot is directly committed: coverage makes every `T` block at the decision round reference the leader's block, and `T` carries the quorum. Two populated rounds — propose and decide.

#### `decided_of_leader_mem`

*theorem, `Hybrid.Liveness.lean`*

```lean
theorem decided_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided k U (View.full U) s (some L)
```

**H7, as a decision** — at every threshold `k`.

#### `spansEligible_two`

*theorem, `Hybrid.Liveness.lean`*

```lean
theorem spansEligible_two (hid : ∀ s, S.slotRound s = s) :
    SpansEligible Validator 2
```

Under a pipelined identity-round schedule, `c = 2` spans — two consecutive reliable leaders, exactly as in the pure-Byzantine two-round development.

#### `decided_below_of_committed_run`

*theorem, `Hybrid.Liveness.lean`*

```lean
theorem decided_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided k U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided k U V i v
```

**The committed-run descent (O9's mirror).** Every slot below a committed run of eligible span is decided, at every threshold `k`: anchor each slot on the nearest eligible committed slot above it and commit the least candidate passing the indirect test — exactly the canonicity premise.

#### `all_decided_below_of_fairRun`

*theorem, `Hybrid.Liveness.lean`*

```lean
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : q Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided k U (View.full U) i v
```

**H7 (O10's mirror).** Under post-`R` coverage, growth to the horizon, and a recurring run of `c` reliable-led slots, every slot below the run is decided — at every threshold `k`, the run placed past both the target and `R` by fairness. The reliable set excludes the crash-prone by construction: `T ⊆ Correct` reads through the derived instance.

#### `toHybrid_toFaults`

*theorem, `Hybrid.Conservativity.lean`*

```lean
theorem toHybrid_toFaults [F : Faults5 Validator] :
    (HybridFaults.toFaults (H := Faults5.toHybrid)) =
      (F.toFaults : Faults Validator)
```

The two derived instances are equal, so a block universe over the `Faults5` development *is* one over its crash-free hybrid reading, with no transport.

### Adaptive leaders: the schedule as a fixpoint

#### `epochOf_lt_iff`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem epochOf_lt_iff {W k e : ℕ} (hW : 0 < W) :
    epochOf W k < e ↔ k < W * e
```

#### `slotsOf_leader`

*theorem, `Adaptive.Basic.lean`*

```lean
@[simp] theorem slotsOf_leader (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).leader k = a k
```

#### `slotsOf_base`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem slotsOf_base (hinj : Function.Injective S.slotRound) :
    slotsOf hinj S.leader = S
```

The base schedule is its own induced instance — the anchor for conservativity: a constant policy reassigns nothing.

#### `toDecided`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem toDecided (h : DecidedWithin U V B k v) : Decided U V k v
```

Forgetting the bound: every bounded derivation is a `Decided` derivation, so the base safety development — M1–M6 in particular — applies to bounded verdicts without restatement.

#### `mono`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem mono (h : DecidedWithin U V B k v) (hBB : B ≤ B') :
    DecidedWithin U V B' k v
```

The bound relaxes upward.

#### `agree`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem agree {V₁ V₂ : View Validator BlockId Payload U} {B₁ B₂ k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : DecidedWithin U V₁ B₁ k v₁)
    (h₂ : DecidedWithin U V₂ B₂ k v₂) : v₁ = v₂
```

Two bounded verdicts agree — M6, through the embedding.

#### `isLeaderBlock_slotsOf_congr`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem isLeaderBlock_slotsOf_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {k : ℕ} {L : BlockId} (hk : a₁ k = a₂ k)
    (h : IsLeaderBlock (S := slotsOf hinj a₁) U k L) :
    IsLeaderBlock (S := slotsOf hinj a₂) U k L
```

Only the leader clause of `IsLeaderBlock` consults the assignment, at the slot itself.

#### `decidedWithin_congr`

*theorem, `Adaptive.Basic.lean`*

```lean
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    DecidedWithin (S := slotsOf hinj a₂) U V B k v
```

**Congruence below the bound.** Only `IsLeaderBlock` consults the assignment, and only at slots below `B`; the round structure — and with it eligibility, decision rounds and every counting predicate — is the base instance's. So two assignments agreeing below `B` derive the same bounded verdicts, which is what permits judging an epoch against a schedule only determined so far.

#### `partialRun_agree`

*theorem, `Adaptive.Run.lean`*

```lean
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k
```

**The master agreement lemma.** Two partial runs over one universe — whatever views, whatever heights — agree on the verdicts of their common epochs and on the assignments those verdicts determine.

The strong induction the module docstring describes: verdict agreement below an epoch forces assignment agreement through the epoch above it (`adapted`), which forces verdict agreement at the epoch itself (`decidedWithin_congr`, then M6 through the embedding).

#### `adaptiveRun_agree`

*theorem, `Adaptive.Run.lean`*

```lean
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    (∀ k, R₁.vdct k = R₂.vdct k) ∧ (∀ m, R₁.assign m = R₂.assign m)
```

**Safety: the adaptive fixpoint is unique.** Two total runs over one universe — derived from any two views, under no synchrony or fairness hypothesis — hold the same verdicts and run the same schedule. Adaptive validators cannot diverge, whatever the policy adapts to.

#### `adaptive_commitSeq_agree`

*theorem, `Adaptive.Run.lean`*

```lean
theorem adaptive_commitSeq_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) (n : ℕ) :
    commitSeq R₁.vdct n = commitSeq R₂.vdct n
```

**The adaptive ledger is agreed** — M7's shape: the committed-leader sequence read from any two runs' verdicts is the same list.

#### `const_run_decided`

*theorem, `Adaptive.Run.lean`*

```lean
theorem const_run_decided {W : ℕ} {hW : 0 < W}
    {hinj : Function.Injective S.slotRound}
    {V : View Validator BlockId Payload U}
    (R : AdaptiveRun (const (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) W hW hinj) U V) (k : ℕ) :
    Decided U V k (R.vdct k)
```

**Conservativity.** Under the constant policy a run's verdicts are ordinary `Decided` verdicts of the base schedule — the adaptive development instantiates to the base one, per the house rule that a new relation must collapse onto the old. With M6 this also pins each `vdct k` to the unique base verdict.

#### `epoch_closes`

*theorem, `Adaptive.Liveness.lean`*

```lean
theorem epoch_closes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (v : ℕ → Option BlockId) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 2)) + 2 ≤ N) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedWithin (S := slotsOf P.inj (fun m => P.pick U v m)) U
        (View.full U) (P.W * (E + 2)) k w
```

**One epoch closes.** Against the schedule an arbitrary verdict function induces, every slot of epoch `E` is decided inside its window: the run `PlacesRuns` puts in epoch `E + 1` commits directly, and the bounded descent clears everything below it.

#### `exists_partialRun`

*theorem, `Adaptive.Liveness.lean`*

```lean
theorem exists_partialRun (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 1)) + 2 ≤ N) :
    Nonempty (PartialRun P U (View.full U) E)
```

**Partial runs exist at every height** — the witnessable, finite- horizon form of existence, by induction on the height: each stage re-reads the schedule off the verdicts so far and closes one more epoch.

#### `adaptiveRun_exists`

*theorem, `Adaptive.Liveness.lean`*

```lean
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r) :
    Nonempty (AdaptiveRun P U (View.full U))
```

**AL5: the adaptive fixpoint exists.** On a DAG synchronised over a quorum of reliable validators and populated at every round, under a policy that places runs, a total adaptive run exists on the full view — partial runs at every height glued along the diagonal, `partialRun_agree` making the stage-by-stage choices cohere. With `adaptiveRun_agree` it is THE fixpoint: adaptive Mysticeti decides every slot, and uniquely.

#### `toDecided`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem toDecided (h : DecidedWithin U V B k v) : Decided U V k v
```

Forgetting the bound: agreement for the bounded relation *is* O5.

#### `decidedWithin_congr`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    DecidedWithin (S := slotsOf hinj a₂) U V B k v
```

Congruence below the bound, canonicity clause included: the candidate set reads the schedule only through `IsLeaderBlock`, which transports in both directions at the decided slot.

#### `partialRun_agree`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k
```

The master agreement lemma, two-round rule — the Mysticeti induction verbatim, with O5 where it used M6.

#### `adaptiveRun_agree`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    ∀ k, R₁.vdct k = R₂.vdct k
```

**Safety, two-round rule: the adaptive fixpoint is unique** — with no fairness, synchrony or view hypothesis, exactly as on the three-round side.

#### `epoch_closes`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem epoch_closes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible Validator c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (v : ℕ → Option BlockId) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 2)) + 1 ≤ N) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedWithin (S := slotsOf P.inj (fun m => P.pick U v m)) U
        (View.full U) (P.W * (E + 2)) k w
```

One epoch closes, two-round rule: O7 commits the placed run — two populated rounds where Mysticeti needs three — and the bounded descent clears the epoch below.

#### `exists_partialRun`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem exists_partialRun (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible Validator c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 1)) + 1 ≤ N) :
    Nonempty (PartialRun P U (View.full U) E)
```

Partial runs exist at every height, two-round rule.

#### `adaptiveRun_exists`

*theorem, `Adaptive.Odontoceti.lean`*

```lean
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible Validator c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r) :
    Nonempty (AdaptiveRun P U (View.full U))
```

**AL7: adaptive Odontoceti is safe and live.** The fixpoint exists on the full view — glued along the diagonal exactly as on the three-round side — and by `Odontoceti.adaptiveRun_agree` it is unique.

### Nemo-Nemo: crash-fault consensus in two rounds

#### `exists_mem_inter`

*theorem, `Nemo.Basic.lean`*

```lean
theorem exists_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : majority Validator ≤ Q₁.card) (h₂ : majority Validator ≤ Q₂.card) :
    (Q₁ ∩ Q₂).Nonempty
```

**The one quorum fact.** Two majorities always intersect — `(n/2+1) + (n/2+1) > n` — and, all validators being honest, the shared member is consistent. This is the crash analogue of the core's `exists_correct_mem_inter`, with the correctness filtering gone.

#### `refs_nonempty`

*theorem, `Nemo.Basic.lean`*

```lean
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty
```

A non-genesis block has at least one reference (the majority quorum is positive).

#### `eq_of_creator_eq`

*theorem, `Nemo.Basic.lean`*

```lean
theorem eq_of_creator_eq {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ U.ids)
    (hc : (U.block i).creator = (U.block j).creator)
    (hround : (U.block i).round = (U.block j).round) : i = j
```

Two ids with the same author and round are the same id — universal, no correctness hypothesis (the crash simplification of the core's T1).

#### `round_of_mem_refs`

*theorem, `Nemo.Basic.lean`*

```lean
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round
```

A reference sits in the round immediately below its referrer.

#### `creators_quorum`

*theorem, `Nemo.Basic.lean`*

```lean
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    majority Validator ≤ (creatorsOf U.block (U.block i).refs).card
```

References of a non-genesis block carry a majority of distinct authors.

#### `refs_nonempty`

*theorem, `Nemo.Basic.lean`*

```lean
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (U.block i).refs.Nonempty
```

A non-genesis block references at least one block.

#### `exists_common_mem_of_quorums`

*theorem, `Nemo.Basic.lean`*

```lean
theorem exists_common_mem_of_quorums {s t : Finset BlockId} {n : ℕ}
    (hs : ∀ q ∈ s, q ∈ U.ids ∧ (U.block q).round = n)
    (ht : ∀ q ∈ t, q ∈ U.ids ∧ (U.block q).round = n)
    (hsq : majority Validator ≤ (creatorsOf U.block s).card)
    (htq : majority Validator ≤ (creatorsOf U.block t).card) :
    ∃ q, q ∈ s ∧ q ∈ t
```

**Two majority-backed sets of round-`n` blocks share a block.** The crash analogue of the core's `exists_common_mem_of_quorums`: majority intersection (all honest) plus universal non-equivocation.

#### `single`

*theorem, `Nemo.CausalHistory.lean`*

```lean
theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j
```

A direct reference is one step of causal history.

#### `of_mem_refs`

*theorem, `Nemo.CausalHistory.lean`*

```lean
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b
```

Prepend a direct reference.

#### `mem_history_iff`

*theorem, `Nemo.History.lean`*

```lean
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i
```

**The representation is faithful.** For a block of the universe, membership of `history` and reachability are the same thing.

#### `history_subset_of_reaches`

*theorem, `Nemo.History.lean`*

```lean
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c
```

Histories nest along reachability.

#### `mem_history_of_mem_refs`

*theorem, `Nemo.History.lean`*

```lean
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b
```

A block's references lie in its history, one step down.

#### `mem_blocksAt`

*theorem, `Nemo.Support.lean`*

```lean
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n
```

Membership in `blocksAt`, unfolded.

#### `exists_mem_refs_of_correct_support_of_card`

*theorem, `Nemo.Support.lean`*

```lean
theorem exists_mem_refs_of_correct_support_of_card
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hcard : majority Validator ≤ T.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q
```

**The hitting lemma, uniform form.** A `majority` of backers always suffices: `c` names a majority of the round-`n` authors, and two majorities of the pool intersect. The crash port of `exists_mem_refs_of_correct_support_of_card`.

#### `reaches_pred_of_round_le`

*theorem, `Nemo.Support.lean`*

```lean
theorem reaches_pred_of_round_le {P : BlockId → Prop} {N : ℕ}
    (hbase : ∀ c ∈ U.ids, (U.block c).round = N → ∃ b, P b ∧ Reaches U c b)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : N ≤ (U.block c).round) :
    ∃ b, P b ∧ Reaches U c b
```

**Propagation.** Reaching something is inherited upward: if every block at round `N` reaches a `P`-block, so does every block above `N`.

A verbatim port of the core lemma of the same name: the step needs nothing but nonempty references and transitivity — height is carried by `Reaches` alone, so no quorum content is involved.

#### `mem_supporters`

*theorem, `Nemo.Support.lean`*

```lean
theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v
```

Membership in `supporters`, unfolded: a supporter has a round-`n` block referencing `b`.

#### `certifiedIn_of_directCommit`

*theorem, `Nemo.Rules.lean`*

```lean
theorem certifiedIn_of_directCommit {L A : BlockId} {r : ℕ}
    (hdc : DirectCommit U L r) (hA : A ∈ U.ids) (hAr : r + 2 ≤ (U.block A).round) :
    CertifiedIn U A L r
```

**Link integrity.** A directly committed leader is certified in every block at round `r+2` or above — in particular in every eligible anchor. The depth induction is the generic propagation lemma; the quorum intersection lives entirely in the base case.

#### `eligible_iff`

*theorem, `Nemo.Decision.lean`*

```lean
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j
```

Eligibility, unfolded: two rounds.

#### `lt_of_eligible`

*theorem, `Nemo.Decision.lean`*

```lean
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j
```

An eligible anchor is a later slot.

#### `isLeaderBlock_unique`

*theorem, `Nemo.Decision.lean`*

```lean
theorem isLeaderBlock_unique {k : ℕ} {L₁ L₂ : BlockId}
    (h₁ : IsLeaderBlock U k L₁) (h₂ : IsLeaderBlock U k L₂) : L₁ = L₂
```

**A slot has at most one candidate.** The crash simplification that retires the Byzantine arcs' twin-uniqueness machinery (M5′/H5): universal `no_equivocation` identifies two blocks sharing the slot's round and leader before any question of commitment arises.

#### `decided_unique`

*theorem, `Nemo.Decision.lean`*

```lean
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂
```

**Agreement.** No two validators reach conflicting decisions for a slot, whatever views they hold and whichever routes they took. Hypothesis-free — non-equivocation is baked into the crash `Universe`.

Structural induction on the first derivation: nine constructor pairings. Every commit-versus-commit case closes by `isLeaderBlock_unique` — no certificate counting. The direct-versus-indirect crossings close by the visibility lemma against the skipper's own anchor, and the one real case — indirect commit against indirect skip — by comparing the two anchors with the core's polymorphic `anchor_eq`.

#### `decided_agree`

*theorem, `Nemo.Decision.lean`*

```lean
theorem decided_agree {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) :
    v₁ = v₂
```

Agreement, in the shape callers want: two validators' verdicts for a slot agree.

#### `eq_of_decided_commit`

*theorem, `Nemo.Decision.lean`*

```lean
theorem eq_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided U V₁ k (some L₁)) (h₂ : Decided U V₂ k (some L₂)) :
    L₁ = L₂
```

No two validators commit *different* blocks for one slot.

#### `not_decided_skip_of_decided_commit`

*theorem, `Nemo.Decision.lean`*

```lean
theorem not_decided_skip_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (h₁ : Decided U V₁ k (some L)) (h₂ : Decided U V₂ k none) :
    False
```

No validator commits a slot another has skipped: a committed block never has to be retracted.

#### `commitSeq_agree`

*theorem, `Nemo.Decision.lean`*

```lean
theorem commitSeq_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n
```

**The committed-leader sequence is agreed.** Two validators that have settled the first `n` slots — on whatever views, by whatever mix of direct and indirect routes — read off the same list of committed blocks.

#### `ledgerSet_mono`

*theorem, `Nemo.Decision.lean`*

```lean
theorem ledgerSet_mono {g : ℕ → Option BlockId} {n m : ℕ} (h : n ≤ m) :
    ledgerSet U g n ⊆ ledgerSet U g m
```

**Nothing is ever dropped.** The ledger only grows as more slots settle.

#### `ledgerSet_agree`

*theorem, `Nemo.Decision.lean`*

```lean
theorem ledgerSet_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    ledgerSet U g₁ n = ledgerSet U g₂ n
```

**Two validators output the same blocks.**

#### `outputAt_unique`

*theorem, `Nemo.Decision.lean`*

```lean
theorem outputAt_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂
```

**A block enters the ledger once.** Its position is not merely stable over time — there is no second slot it could have entered at.

#### `outputAt_agree`

*theorem, `Nemo.Decision.lean`*

```lean
theorem outputAt_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId} {b : BlockId} {k : ℕ}
    (h₁ : ∀ j, j < n → Decided U V₁ j (g₁ j))
    (h₂ : ∀ j, j < n → Decided U V₂ j (g₂ j))
    (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k
```

**And validators agree on which slot that is.**

#### `decided_mono`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem decided_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {v : Option BlockId} (h : Decided U V k v) :
    Decided U V' k v
```

**Decisions are monotone in the view.** Induction on the derivation: the direct case is the monotonicity lemma above, and the two indirect cases rebuild themselves from the inductive hypotheses, carrying their `CertifiedIn` premises across unchanged — the indirect test is universe-level, so growth cannot disturb it.

#### `decided_full`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem decided_full {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided U V k v) : Decided U (View.full U) k v
```

**Commit propagation.** Whatever any validator decides on any view, the same verdict holds on the full view — and the full view is every live validator's eventual view, so this *is* "all live validators eventually reach the same decision".

#### `directCommit_of_leader_mem`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem directCommit_of_leader_mem
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ DirectCommit U L (S.slotRound s)
```

**The commit half.** Post-`R`, a `T`-led slot is directly committed: coverage makes every `T` block at the decision round reference the leader's block, and `T` carries the majority. Two populated rounds — propose and decide, wavelength two.

#### `decided_of_leader_mem`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem decided_of_leader_mem
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided U (View.full U) s (some L)
```

The commit half, as a decision.

#### `spansEligible_two`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem spansEligible_two (hid : ∀ s, S.slotRound s = s) :
    SpansEligible Validator 2
```

Under a pipelined identity-round schedule, `c = 2` spans — two consecutive reliable leaders suffice at wavelength two.

#### `decided_below_of_committed_run`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem decided_below_of_committed_run {V : View Validator BlockId Payload U} {b n : ℕ}
    (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided U V i v
```

**Everything below a committed run is decided.** Given a block of consecutive committed slots `b … n` whose top is eligible for everything below `b`, every slot below `b` resolves — commit or skip — by anchoring on the nearest eligible committed slot.

The core's proof, verbatim: the crash `indirectCommit` carries no canonicity premise (`isLeaderBlock_unique` leaves no twins), so the commit branch is a plain constructor application and no minimum-selection tie-break appears.

#### `all_decided_below_of_fairRun`

*theorem, `Nemo.Liveness.lean`*

```lean
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ Live Validator)
    (hcard : majority Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v
```

**Liveness.** Under post-`R` coverage, growth to the horizon, and a recurring run of `c` reliable-led slots, every slot below the run is decided — the run placed past both the target and `R` by fairness.

The quantifier order is the content: the slot `b` is fixed by the *schedule* alone, before any universe is named, so "eventually" means "any DAG grown past this schedule-fixed slot". Crashed-leader slots are settled here and only here: they descend onto the run via `indirectSkip`.

### Mahi-Mahi: the asynchronous rule at wave w

#### `mem_candidatesAt`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem mem_candidatesAt {q b : BlockId} {a : Validator} {r : ℕ} :
    b ∈ candidatesAt U q a r ↔
      b ∈ U.ids ∧ (U.block b).round = r ∧ (U.block b).creator = a ∧ b ∈ history U q
```

#### `mem_votesIn`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem mem_votesIn {C L q : BlockId} :
    q ∈ votesIn U C L ↔ q ∈ (U.block C).refs ∧ Votes U q L
```

#### `mem_certificates`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem mem_certificates {C L : BlockId} {w r : ℕ} :
    C ∈ certificates U w L r ↔
      C ∈ U.ids ∧ (U.block C).round = decisionRoundAt w r ∧ Certifies U C L
```

#### `decisionRoundAt_eq_votingRound_succ`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem decisionRoundAt_eq_votingRound_succ {w r : ℕ} (hw : 2 ≤ w) :
    decisionRoundAt w r = votingRound w r + 1
```

#### `certificates_eq_empty_of_directSkip`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem certificates_eq_empty_of_directSkip {w : ℕ} {a : Validator} {r : ℕ} {L : BlockId}
    (hw : 2 ≤ w) (h : DirectSkip U w a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    certificates U w L r = ∅
```

**Skip excludes certificates.** A quorum of blamers and a quorum of voters at the voting round share a block, which would both vote for `L` and blame its slot.

#### `eq_of_certificates_nonempty`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem eq_of_certificates_nonempty {w r : ℕ} {L₁ L₂ : BlockId} (hw : 2 ≤ w)
    (h₁ : (certificates U w L₁ r).Nonempty) (h₂ : (certificates U w L₂ r).Nonempty)
    (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂
```

**Certificate uniqueness.** Two voter quorums at the voting round share a block, which votes for one candidate of a given author and round.

#### `certificates_nonempty_of_directCommit`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem certificates_nonempty_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ}
    (h : DirectCommit U w L r) : (certificates U w L r).Nonempty
```

A direct commit needs a quorum of certificate authors, so at least one certificate.

#### `exists_certificate_reaches_of_directCommit`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem exists_certificate_reaches_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ}
    (h : DirectCommit U w L r) {c : BlockId} (hc : c ∈ U.ids)
    (hcr : decisionRoundAt w r + 1 ≤ (U.block c).round) :
    ∃ C ∈ certificates U w L r, Reaches U c C
```

**Certificates persist upward** (the paper's Lemma C.1). A block above the decision round references a certificate's correct author at the layer below, and higher blocks reach one through their references.

#### `votingRound_three`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem votingRound_three (r : ℕ) : votingRound 3 r = r + 1
```

#### `certificates_eq_of_three`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem certificates_eq_of_three {L : BlockId} {r : ℕ} (hLr : (U.block L).round = r) :
    certificates U 3 L r = LeanDag.certificates U L r
```

At wave three the certificates of a round-`r` block are the core's.

#### `not_mem_refs_of_blames`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem not_mem_refs_of_blames {q L : BlockId} {a : Validator} {r : ℕ} (hq : q ∈ U.ids)
    (hb : Blames U q a r) (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    L ∉ (U.block q).refs
```

A blame of the slot is a blame of each of its candidates.

#### `blames_of_not_mem_refs_of_unique`

*theorem, `MahiMahi.Helpers.Rules.lean`*

```lean
theorem blames_of_not_mem_refs_of_unique {q L : BlockId} {a : Validator} {r : ℕ}
    (hq : q ∈ U.ids) (hqr : (U.block q).round = r + 1)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r)
    (huniq : ∀ L' ∈ U.ids, (U.block L').creator = a → (U.block L').round = r → L' = L)
    (hL : L ∉ (U.block q).refs) : Blames U q a r
```

At wave three, a block at the voting round that does not reference the only candidate of a slot blames the slot.

#### `certifiedIn_of_directCommit`

*theorem, `MahiMahi.Helpers.Decision.lean`*

```lean
theorem certifiedIn_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ} (h : DirectCommit U w L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : decisionRoundAt w r + 1 ≤ (U.block A).round) :
    CertifiedIn U w A L r
```

The commit half of M4: a directly committed candidate is certified in the cone of every block above its decision round.

#### `decided_unique`

*theorem, `MahiMahi.Helpers.Decision.lean`*

```lean
theorem decided_unique {w : ℕ} (hw : 2 ≤ w) {V₁ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided w U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided w U V₂ k v₂ → v₁ = v₂
```

**Agreement** (the core's M6 at wave `w`): structural induction on the first derivation; the one real case compares anchors through the core's `anchor_eq`.

#### `core_decided_of_decided`

*theorem, `MahiMahi.Helpers.Decision.lean`*

```lean
theorem core_decided_of_decided {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided 3 U V k v) : LeanDag.Decided U V k v
```

At wave three every derivation is a derivation of the core's relation.

#### `mem_goodAt`

*theorem, `MahiMahi.Helpers.Counting.lean`*

```lean
theorem mem_goodAt {w r : ℕ} {v : Validator} :
    v ∈ goodAt U w r ↔ ∃ L ∈ U.ids,
      (U.block L).round = r ∧ (U.block L).creator = v ∧ DirectCommit U w L r
```

#### `exists_commonCore`

*theorem, `MahiMahi.Helpers.Counting.lean`*

```lean
theorem exists_commonCore {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b ∈ U.ids, (U.block b).round = r ∧ (U.block b).creator ∈ (Correct : Finset Validator) ∧
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b
```

The core's common correct ancestor (T3c), carried to every round `≥ r + 2` through references.

#### `directCommit_of_voting_reach`

*theorem, `MahiMahi.Helpers.Counting.lean`*

```lean
theorem directCommit_of_voting_reach {w r : ℕ} {L : BlockId} {T : Finset Validator}
    (hw : 2 ≤ w) (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T (decisionRoundAt w r))
    (hL : L ∈ U.ids) (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hreach : ∀ q ∈ U.ids, (U.block q).round = votingRound w r → Reaches U q L) :
    DirectCommit U w L r
```

If every voting-round block reaches a correct candidate, and a quorum populates the decision round, the candidate is directly committed.

#### `goodNonempty`

*theorem, `MahiMahi.Helpers.Counting.lean`*

```lean
theorem goodNonempty {w : ℕ} {T : Finset Validator} {r : ℕ} (hw : 4 ≤ w)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2)) (hpopd : PopulatedOn U T (decisionRoundAt w r)) :
    (goodAt U w r ∩ (Correct : Finset Validator)).Nonempty
```

**MM2 at `w ≥ 4`.**

#### `goodCard`

*theorem, `MahiMahi.Helpers.Counting.lean`*

```lean
theorem goodCard {w : ℕ} {T : Finset Validator} {r : ℕ} (hw : 5 ≤ w)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop3 : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (decisionRoundAt w r)) :
    quorumCard Validator ≤
      (goodAt U w r ∩ (Correct : Finset Validator)).card + F.byzantine.card
```

**MM2 at `w ≥ 5`.**

#### `multiLeader`

*theorem, `MahiMahi.Helpers.Counting.lean`*

```lean
theorem multiLeader [S : Slots Validator] {w : ℕ} {T : Finset Validator} {r : ℕ} (hw : 5 ≤ w)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop3 : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (decisionRoundAt w r))
    {M : Finset Validator} (hM : ∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v)
    (hMcard : 2 * F.f + 1 ≤ M.card) :
    ∃ k, S.slotRound k = r ∧ S.leader k ∈ good U w k
```

**MM2b.** `f + 1` good correct validators and `2f + 1` leaders cannot be disjoint in `3f + 1`.

#### `decided_of_mem_good`

*theorem, `MahiMahi.Helpers.Liveness.lean`*

```lean
theorem decided_of_mem_good {w k : ℕ} (h : S.leader k ∈ good U w k) :
    ∃ L, IsLeaderBlock U k L ∧ Decided w U (View.full U) k (some L)
```

**MM3a.**

#### `decided_below_of_committed_run`

*theorem, `MahiMahi.Helpers.Liveness.lean`*

```lean
theorem decided_below_of_committed_run {w : ℕ} (hw : 1 ≤ w)
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator w i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided w U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided w U V i v
```

**Every slot below a committed run is decided** — the core's `decided_below_of_committed_run` at wave `w`, verbatim up to the relation: strong induction on the distance to the run, each slot anchored on the nearest eligible committed slot, the eligible slots between it being skipped by the induction hypothesis.

#### `allDecidedBelow`

*theorem, `MahiMahi.Helpers.Liveness.lean`*

```lean
theorem allDecidedBelow {w c d N : ℕ} (hw : 1 ≤ w)
    (hspan : SpansEligible Validator w d) (hrun : UnpredictableRunWithin U w c d N)
    (k : ℕ) (hk : decisionRound Validator w (k + c + d - 1) ≤ N) :
    ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, Decided w U (View.full U) i v
```

**MM3c.** The run form supplies the committed run; the descent does the rest. A spanning run has at least one slot.

#### `localCommit`

*theorem, `MahiMahi.Helpers.Liveness.lean`*

```lean
theorem localCommit {w : ℕ} {T : Finset Validator} {N : ℕ} (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card) {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (hN : decisionRound Validator w k ≤ N)
    (hcert : ∀ u ∈ T, ∀ C ∈ U.ids, (U.block C).creator = u →
      (U.block C).round = decisionRound Validator w k → Certifies U C L) :
    ∀ v ∈ T, Decided w U
      (pc.viewAt v (max (pc.latest (decisionRound Validator w k)) pc.gst + pc.delay))
      k (some L)
```

**MM3d.** The counting re-run inside the view: production gives every reliable validator a decision-round block, the premise makes each a certificate, and eventual delivery puts each in the view.

#### `AgreeUpto.goodAt_eq`

*theorem, `MahiMahi.Helpers.Liveness.lean`*

```lean
theorem AgreeUpto.goodAt_eq (h : AgreeUpto U₁ U₂ d) {w r : ℕ} (hw : 1 ≤ w)
    (hd : decisionRoundAt w r ≤ d) : goodAt U₁ w r = goodAt U₂ w r
```

**MM2′.**

#### `good_of_synchronisedOn`

*theorem, `MahiMahi.Helpers.Synchrony.lean`*

```lean
theorem good_of_synchronisedOn {w : ℕ} {T : Finset Validator} {R k : ℕ} (hw : 4 ≤ w)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k)) (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpopd : PopulatedOn U T (decisionRound Validator w k))
    (hlead : S.leader k ∈ T) : S.leader k ∈ good U w k
```

**MM5a.**

#### `unpredictableWithin_of_synchronisedOn`

*theorem, `MahiMahi.Helpers.Synchrony.lean`*

```lean
theorem unpredictableWithin_of_synchronisedOn {w : ℕ} {T : Finset Validator} {c N : ℕ}
    (hw : 4 ≤ w) (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T 0) (hpop : ∀ n, n ≤ N → PopulatedOn U T n)
    (fair : FairWithin T c) : UnpredictableWithin U w c N
```

**MM5b.**

#### `holds`

*theorem, `MahiMahi.Safety.Proof.lean`*

```lean
theorem holds : Statement
```

#### `holds`

*theorem, `MahiMahi.Counting.Proof.lean`*

```lean
theorem holds : Statement
```

#### `holds`

*theorem, `MahiMahi.Liveness.Proof.lean`*

```lean
theorem holds : Statement
```

#### `holds`

*theorem, `MahiMahi.Synchrony.Proof.lean`*

```lean
theorem holds : Statement
```

### Not otherwise grouped

#### `waveRobin_fairRun`

*theorem, `WaveRobin.lean`*

```lean
theorem waveRobin_fairRun (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] :
    FairRunOn (S := waveRobin n hn) (Correct : Finset (Fin n)) 3
```

**A fair schedule exists — wave-aligned rotation, unconditionally.**

The witness for slot `k` is the correct validator `v`'s wave in the `k`-th rotation cycle: slot `3 * (v + n * k)` opens a wave led by `v`, lies past `k`, and its three slots are all `v`-led. This is `FairRunOn` produced with no premise at all, where per-slot rotation would need the pigeonhole argument recorded on `FairRunOn` — which is exactly why the wave-aligned schedule is the canonical witness.

#### `waveRobin_spansEligible`

*theorem, `WaveRobin.lean`*

```lean
theorem waveRobin_spansEligible (n : ℕ) (hn : 0 < n) :
    SpansEligible (Validator := Fin n) (S := waveRobin n hn) 3
```

**`SpansEligible 3`, the pipelined shape, at every `n`.** A run of three consecutive slots reaches three rounds past everything below it — the same arithmetic as `pipe_spansEligible`, freed of the committee.

#### `waveRobin_fairSchedule`

*theorem, `WaveRobin.lean`*

```lean
theorem waveRobin_fairSchedule (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] :
    FairScheduleOn (S := waveRobin n hn) (Correct : Finset (Fin n))
```

The wave-aligned rotation is fair in the single-slot sense too, so L6 and the `ViewPace` results apply to it unchanged.

---

## Appendix D. Index of internal lemmas

The 427 lemmas used only within the file that proves
them. They are steps of the arguments above rather than results
in their own right, so they are listed rather than displayed;
the source is the reference for their statements. One
subsection per module, in the layer order of Appendices B and C.

### `Validators.lean` (2)

| Lemma | Role |
|:---|:---|
| `card_inter_ge_of_quorum` | T0 (cardinality half). Two quorums overlap in at least `f+1` validators: `(n−f) + (n−f) − n = n − 2f ≥ f+1`. |
| `reliable_eq_correct` | At full fault load the reliable set is forced. The liveness results run at any `T ⊆ Correct` with `n - f ≤ … |

### `Block.lean` (2)

| Lemma | Role |
|:---|:---|
| `card_creators` | Distinct creators means the creator map does not collapse the refs, so the creator set has exactly as many … |
| `card_refs` | A non-genesis block references at least `2f+1` blocks. |

### `BlockDag.lean` (1)

| Lemma | Role |
|:---|:---|
| `refs_subset` | Completeness, as a subset statement. |

### `Causality.lean` (3)

| Lemma | Role |
|:---|:---|
| `eq_of_reaches_of_refs_empty` | A block with no references reaches only itself. |
| `historyUptoFrom_succ` | — |
| `historyUptoFrom_zero` | — |

### `CausalHistory.lean` (2)

| Lemma | Role |
|:---|:---|
| `BlockUniverse.causal` | A universe is a causal structure. The two facts the history layer consumes, projected out of the … |
| `not_reaches_of_round_lt` | A block cannot reach anything strictly above it. Contrapositive of T2, and the form that rules out … |

### `History.lean` (7)

| Lemma | Role |
|:---|:---|
| `historyUpto_mono` | More fuel never loses anything. Needed because `mem_history_iff` fixes the fuel at `round + 1` while the … |
| `historyUpto_succ` | — |
| `historyUpto_zero` | — |
| `mem_historyUpto_of_reaches` | Completeness, with the fuel accounted for. A path from `b` drops the round by one per step (T2), so `round … |
| `mem_historyUpto_self` | — |
| `mem_historyUpto_succ` | — |
| `reaches_of_mem_historyUpto` | Soundness. Anything the fuelled search finds really is reachable. No hypothesis on `b`: even off the … |

### `Support.lean` (5)

| Lemma | Role |
|:---|:---|
| `authorsAt_eq_authorsIn` | `authorsAt` is `authorsIn` over the whole universe: L0's density and the progress rule's trigger are one … |
| `blames_inter_supporters_subset_byzantine` | A correct validator cannot both vote for `L` and blame it: that would be two distinct round-`n` blocks by … |
| `card_authorsAt_le_univ` | The author pool never exceeds the validator set. This is what turns the `p - 2f` threshold into the … |
| `exists_mem_refs_of_correct_support` | The hitting lemma. A round-`(n+1)` block cannot avoid referencing a block satisfying `P`, once `f+1`-or-so … |
| `supporters_subset_authorsAt` | — |

### `CommonCore.lean` (5)

| Lemma | Role |
|:---|:---|
| `card_authorsAt_le` | The author pool at round `n` is covered by the correct authors together with the Byzantine validators, … |
| `card_creatorsOf_correctBlocksAt` | — |
| `creator_injOn_correctBlocksAt` | Distinct correct round-`n` blocks have distinct authors — non-equivocation (T1) in the form the count needs. |
| `creatorsOf_correctBlocksAt_subset` | — |
| `support_threshold_arith` | The arithmetic core of T3a, isolated from the combinatorics. |

### `Persistence.lean` (1)

| Lemma | Role |
|:---|:---|
| `mem_ids_and_round_of_quorum_support` | The quorum hypothesis already forces `b` into the universe at round `r`, so T3 need not assume either. A … |

### `Schedule.lean` (5)

| Lemma | Role |
|:---|:---|
| `one_hblock` | With one leader per round the distinctness condition is vacuous: slots in a round are the round, so no two … |
| `uniformSingle_slotRound` | — |
| `uniformSingle_spacing` | The old `spacing` field, recovered. Consecutive slots of `uniformSingle 3` really are three rounds apart, … |
| `uniform_leader` | — |
| `uniform_slotRound` | — |

### `Mysticeti.lean` (12)

| Lemma | Role |
|:---|:---|
| `certifiedIn_of_directCommitIn` | The engine of M6. A direct commit made in *any* view is visible from *every* later slot's leader block. A … |
| `certifiedIn_of_directCommitIn_at_anchor` | Visibility from an anchor. A slot committed directly is certified at any eligible anchor above it: the … |
| `directSkip_of_directSkipIn` | — |
| `eq_of_directCommitIn` | Cross-view M5: two validators cannot directly commit *different* blocks for one slot. Both candidates are … |
| `eq_of_hasCertificate` | Two commits for one slot agree, however each was reached. Both routes yield a certificate, so this is M5′ … |
| `mem_votesIn_spec` | A vote counted by a round-`(r+2)` certificate really is a round-`(r+1)` block of the universe that … |
| `not_certifiedIn_of_directSkip` | M4, skip half. A directly skipped block is found by *no* anchor whatsoever — no round hypothesis needed, … |
| `not_certifiedIn_of_directSkipIn` | A direct skip made in any view is invisible from every anchor — no round hypothesis needed, since M3 rules … |
| `not_directSkipIn_of_directCommitIn` | Cross-view M1: one validator cannot directly commit what another directly skips. |
| `not_directSkip_of_directCommitIn` | Direct decisions agree across views. If one validator directly commits a slot, no other validator can … |
| `slot_eq_of_decided_commit` | And so a committed block belongs to one slot. The ledger reads verdicts off in slot order, so without this … |
| `slot_eq_of_isLeaderBlock` | A block is the candidate of at most one slot. |

### `Participation.lean` (2)

| Lemma | Role |
|:---|:---|
| `PopulatedFrom.mono` | Population is antitone: a smaller set is easier to populate. |
| `SynchronisedFrom.mono` | Coverage is antitone too: mutual coverage among a larger set implies it among any subset. |

### `Liveness.lean` (19)

| Lemma | Role |
|:---|:---|
| `FairRunOn.fairScheduleOn` | A run of `c` slots contains a `T`-led slot, so `FairRunOn` refines `FairScheduleOn` and everything proved … |
| `FairToEach.fairScheduleOn` | Per-validator fairness is fairness. |
| `PopulatedOn.mono` | Population is antitone: a smaller set is easier to populate. This is what lets L1 keep concluding about … |
| `SynchronisedOn.mono` | Coverage is antitone too: mutual coverage among a larger set implies it among any subset. So existing … |
| `all_decided_below_of_fairRun_correct` | L10 at `T := Correct`. |
| `card_authorsAt_of_populated` | A populated round carries a quorum of authors — the step that feeds a production induction back into its … |
| `card_authorsAt_of_succ` | One step of L0: a block at round `n+1` forces a quorum of authors at round `n`. |
| `certificatesIn_full` | — |
| `certifies_of_synchronisedOn` | A correct round-`(r+2)` block certifies any correct round-`r` block, once round `r+1` is populated and … |
| `decided_none_of_no_candidate` | L5, in the form the `Decided` constructor wants. |
| `directCommitIn_mono` | A larger view can only see more certificates. |
| `directCommit_of_synchronisedOn` | L4, at the round level. A correct block at round `r` is directly committed, given coverage from `r` and … |
| `directSkipIn_mono` | A larger view can only see more blame. |
| `exists_eligible` | Every slot has an eligible anchor somewhere. |
| `exists_isLeaderBlock` | A correct leader has a candidate block, once its round is populated. `Populated` at the leader's own round … |
| `exists_mem_of_authorsAt_card_pos` | A round with any author at all has a block. The bridge that lets L0's induction step back down: a … |
| `exists_slotRound_ge` | Some slot sits at or beyond any given round. |
| `notMem_stuck_of_decided` | L9. Nothing in a stuck set is ever decided, on any view. |
| `stuck_empty_below_commit_of_spacing` | L8 and L9 are consistent, and their hypotheses are jointly exhaustive. |

### `Quantitative.lean` (3)

| Lemma | Role |
|:---|:---|
| `FairWithin.fairScheduleOn` | A rated schedule is a fair one, so everything already proved from `FairScheduleOn` applies to it unchanged. |
| `slotRound_le_of_lt` | A slot bound becomes a round bound. |
| `unbounded_of_rated` | Every rated backoff is unbounded, so `Rated` really is a strengthening of the retired existential … |

### `ViewPace.lean` (7)

| Lemma | Role |
|:---|:---|
| `ViewPace.built_ge_sum` | The full-timeout discipline's floor, accumulated: a validator's round-`n` entry lies at least the sum of … |
| `commits_recur_local_of_pace` | Liveness, execution first (V18′). The same result with the pacing structure fixed before the slot, which … |
| `convergesEventually` | Every `ViewPace` converges in the qualitative sense too — the bound is extra information, not a different … |
| `convergesEventually_of_within` | A bounded lag is a lag: the timed form implies the untimed one, even before `gst`, since holdings only grow. |
| `convergesWithin` | The `converges` field *is* the bounded form of the factoring above. |
| `convergesWithin_of_bounded` | And conversely: eventual convergence whose lag is uniformly bounded after `gst` *is* convergence within … |
| `le_built` | Rounds advance real time, over the rounds a validator reached. |

### `PaceDelivery.lean` (3)

| Lemma | Role |
|:---|:---|
| `dos_resistance_of_pace'` | The same bound, factored (V20′). The three summands of `dos_resistance_of_pace` are one product: a correct … |
| `mem_heldOf` | — |
| `toDelivery_held` | The induced layer reads the pacing structure's own holdings: what it records at round `n` is exactly what … |

### `Quality/Coverage.lean` (4)

| Lemma | Role |
|:---|:---|
| `card_coveredAt_ge` | CQ1, the count. A valid block's cone covers all but at most `f` of the correct validators, at every round … |
| `coveredAt_eq_sdiff` | Covered and missing partition the correct validators. |
| `coveredAt_subset_correct` | — |
| `mem_coveredAt` | — |

### `Quality/Inclusion.lean` (1)

| Lemma | Role |
|:---|:---|
| `committed_of_correct_block_correct` | CQ6 at `T := Correct`. |

### `Quality/Capstone.lean` (2)

| Lemma | Role |
|:---|:---|
| `chain_quality_of_run` | The inclusion half, in a given execution (CQ4′). `chain_quality` conjoins the unconditional coverage bound … |
| `slotAt_le_slotAt` | The least slot at or above a round is monotone in the round. |

### `DoS/Exposure.lean` (13)

| Lemma | Role |
|:---|:---|
| `EquivPair.symm` | — |
| `ExposedIn.mono` | D12. Exposure is inherited by everything above: what one block's history reveals, every block reaching it … |
| `ExposedIn.not_correct` | D15 — exclusion is sound. An exposed author is Byzantine. |
| `ExposedIn.of_mem_refs` | Exposure passes up a single reference — the form the induction in D17 will want. |
| `card_creators_refs_add_card_exposedTo_le` | D15a — the margin. The authors a block references and the authors it has caught are disjoint subsets of … |
| `card_le_one_or_not_mem_refs` | D11. Under the DoS condition, for every block and every author exactly one of two things holds: the author … |
| `creators_refs_disjoint_exposedTo` | A block never names an author its own history has caught — `DoSValid`, read as a disjointness. |
| `eq_of_mem_refs_of_creator_eq` | D7, the no-equivocation half. A block's references carry distinct authors, so the layer immediately below … |
| `exposedIn_iff_of_view` | D13. Restricting the search for an equivocation to a view that holds `b` changes nothing: the witnesses … |
| `exposedIn_iff_reaches` | — |
| `exposedTo_subset_byzantine` | — |
| `history_subset_view` | Causal history never escapes a view — T6a in `Finset` form. |
| `round_add_two_le_of_equivPair` | D8. An equivocation shows up in a history only two rounds above the round it happened at. |

### `DoS/SelfParent.lean` (6)

| Lemma | Role |
|:---|:---|
| `card_filter_creator_of_mem_refs` | D23, totalled. For any *other* author the block references, the cost is exactly `round` blocks: rounds `0` … |
| `card_filter_self_creator` | D22, totalled. The own-author content of a history is exactly `round + 1` blocks — one per round, the … |
| `card_historyBlocksOf_of_mem_refs` | D23, per round. Referencing a block puts its author into the history exactly once per round strictly below … |
| `card_historyBlocksOf_self` | D22, per round. A block's own author sits in its history *exactly once* per round: at least once by the … |
| `card_history_ge` | D24 (the floor). With self-parents, histories have a *minimum* size: a valid block at round `r` carries at … |
| `exists_self_ancestor_aux` | — |

### `DoS/Density.lean` (3)

| Lemma | Role |
|:---|:---|
| `card_missingAt_le_aux` | — |
| `card_missingAt_le_base` | The one-round case: the references themselves witness all but at most `f` of the correct validators of the … |
| `missingAt_subset_of_mem_refs` | Missing is monotone through references: what `b` lacks, its references lack. |

### `DoS/Counting.lean` (14)

| Lemma | Role |
|:---|:---|
| `EquivFree.subset` | — |
| `View.card_le_of_equivFree` | D5. A view whose blocks reach no higher than round `r`, and which holds no equivocation, holds at most … |
| `blocksAt_disjoint` | Distinct rounds hold disjoint blocks: a block sits at one round. |
| `blocksAt_eq_atRound` | — |
| `card_atRound_le` | One round of an equivocation-free set has at most one block per validator, so at most `3f+1` blocks. |
| `card_authorsAt_le_card_blocksAt` | Authors are the image of blocks, so a round has at least as many blocks as authors. |
| `card_blocksAt_of_lt` | L0 in blocks rather than authors. |
| `card_filter_creator_le_of_mem_refs` | D19b. Under the DoS condition, an author a block *references* contributes at most `round b + 1` blocks to … |
| `card_history_le_of_not_exposed` | D19a. A history exposing nobody is linear in the round: at most `(3f+1)(r+1)` blocks, which is the … |
| `card_ids_bounds` | The bounds together, on a universe with no equivocation at all: linear in the round from both sides. |
| `card_ids_ge_of_round` | D6. A universe holding a block at round `r` holds at least `(n−f)·r + 1` blocks: `2f+1` at every round … |
| `card_le_of_equivFree` | The general counting bound. An equivocation-free set spanning rounds `0…r` holds at most `(3f+1)(r+1)` blocks. |
| `equivFree_history_iff` | — |
| `mem_atRound` | — |

### `DoS/Adoption.lean` (4)

| Lemma | Role |
|:---|:---|
| `card_history_le_of_card_exposedTo_le_one` | The same bound with the hypothesis in counted form: at most one author caught in the whole history. |
| `card_history_le_of_f_le_one` | C1′ at `f ≤ 1`, unconditionally. Exposure is Byzantine (D15) and the Byzantine set has at most one member, … |
| `card_history_le_of_unique_equivocator` | The main bound, unique-equivocator regime. If at most one author is exposed in `b`'s history, the history … |
| `card_topsOf_le` | Tops are as scarce as authors. When every author other than `X` is unexposed — its blocks a single chain — … |

### `DoS/Pedigree.lean` (22)

| Lemma | Role |
|:---|:---|
| `adoptedUnder_unique` | The adoption collapse, packaged: one adopted top per (adopter, author). |
| `card_historyBlocksOf_le` | C1′, in full. Under `DoSValid` with self-parents, an author contributes at most `c(f) = (3f+2)^(3f+1)` … |
| `card_historyBlocksOf_le'` | C1′, tightened. The per-round contribution of any author to any history is at most `1 + 3f·f^(f-1)` — down … |
| `card_historyBlocksOf_le_card_topsOf` | An author's per-round contribution never exceeds its chain count: each round-`n` block sits on the chain … |
| `card_history_le` | The general bound. Every DoS-valid history is linear in its round, at every fault budget: |
| `card_topsOf_le_of_exposed` | The tightened top count. With `e := |exposedTo U b|`, an exposed author has at most `(3f+1-e) · e^(e-1)` … |
| `card_topsOf_le_one_of_not_exposedIn` | An unexposed author has at most one chain. Two tops would be chain-related, and the lower would have a … |
| `card_topsOf_le_pow` | The general top count. A top is determined by its own author and its pedigree's duplicate-free author … |
| `encodeList_injOn` | The encoding is faithful. Two lists over `E'` of length at most `m` with the same encoding are equal: the … |
| `exists_child_of_mem_history_of_creator_eq` | A same-author block strictly inside a history is on the root's chain (D21/D22), so it has a same-author … |
| `exists_pedigree` | Pedigrees exist, with fresh authors all the way. Every top climbs to `b` through adopters whose authors, … |
| `exists_pedigreeVia` | Anchored pedigrees exist. The top of an *exposed* author climbs through exposed-author adopters to the … |
| `exists_pedigree_data` | Every top has an anchored pedigree, in totalised form. |
| `pedigreeVia_cons_inv` | — |
| `pedigreeVia_deterministic` | Anchored determinism: given the anchor and the intermediate author list, the top is unique. |
| `pedigreeVia_nil_inv` | — |
| `pedigreeVia_spec` | Every recorded author is realised by a top strictly above the subject, containing it — the nesting that … |
| `pedigreeVia_top` | — |
| `pedigree_cons_inv` | Inverting one pedigree step against a cons list. |
| `pedigree_deterministic` | Pedigrees determine. Two tops of one author with the same pedigree author-list are equal: each step … |
| `pedigree_spec` | Every author on a pedigree is realised by a *top* strictly above the pedigree's base, whose history … |
| `self_mem_topsOf` | The block itself tops its own chain: nothing in its history can reference it. |

### `DoS/Exclusion.lean` (15)

| Lemma | Role |
|:---|:---|
| `card_creators_accepted_of_eventuallyDelivers` | Where the quorum comes from after `R` — and the settled answer to the plan's Q1. |
| `card_creators_correctBlocksAt` | The correct blocks of a populated round carry a quorum of authors. |
| `correctBlocksAt_admissible_quorum` | D15b — the threshold is met by the correct set alone. |
| `correct_subset_creators_correctBlocksAt` | A populated round carries every correct validator among its correct blocks' authors. |
| `creator_notMem_exposedTo_of_mem_correctBlocksAt` | No correct block's author is ever excluded — D15, in the form a builder needs. |
| `dosValid_refs_of_correctBlocksAt` | The same, phrased as the DoS condition permits it: a block whose references are correct round-`n` blocks … |
| `eq_of_both_name_of_shared` | The intersection lemma. Two blocks that both name `X` agree about `X` wherever their shared correct … |
| `exists_accepted_of_mem_ids` | What the two policies do yield: nothing an author publishes is invisible to the correct population. If any … |
| `exists_correct_mem_refs` | Every non-genesis block references a correct block of the round below. |
| `exists_shared_correct_ref` | Two blocks of the same round share a correct reference, when the correct validators are as few as the … |
| `exposedIn_of_accepted_span` | D8a. A validator whose accepted set spans two disagreeing histories exposes the author in its own next block. |
| `exposedIn_of_correct_disagree` | D16 — after `R`, agree or be exposed. If the histories of two correct round-`n` blocks between them hold … |
| `exposedIn_of_correct_exposed` | D17 — exclusion is total, and permanent. If every correct block of round `n+1` is exposed to `X`, then so … |
| `mem_history_of_pinned` | D18 — pinning. If all but at most `f` correct validators put `A` into their round-`(j+1)` block, then … |
| `not_exposedIn_refs_of_policy` | The condition is implementable. A correct validator following the policy produces blocks that satisfy the … |

### `DoS/Acceptance.lean` (9)

| Lemma | Role |
|:---|:---|
| `Accepted.card_le` | One block per author out of the `n` validators. This is the whole of what the acceptance rule contributes. |
| `View.card_ofAccepted_add_one` | D3. `|V| = |H(b)| - 1`, stated additively. |
| `View.card_ofAccepted_le` | D2 — the bridge. A view generated by an accepted set is at most `3f+1` histories wide. |
| `View.mem_ofAccepted` | — |
| `View.ofAccepted_mono` | Exclusion governs what you reference, not what you retain. Retaining more is monotone on its own, so a … |
| `View.ofAccepted_subset` | D4. If everything accepted before is reachable from something accepted now, the view has only grown. |
| `View.ofAccepted_subset_of_refs` | The form self-reference supplies: `v`'s next block is accepted at the next round and references everything … |
| `history_eq_insert_ofAccepted` | The view generated by `b`'s references is `b`'s history, less `b`. |
| `notMem_ofAccepted_self` | A block is never inside the view its own references generate: everything there sits a round lower. |

### `DoS/Novelty.lean` (13)

| Lemma | Role |
|:---|:---|
| `card_byzPool_succ_le` | The accounting step. A Byzantine block enters the pool only as a direct budgeted acceptance: if it arrived … |
| `card_byzPool_zero_le` | Round 0 seeds the pool with at most `f` Byzantine geneses per correct validator. |
| `card_filter_correct_le` | One acceptance per author: the frontier splits into at most `|Correct|` correct-authored blocks… |
| `card_filter_not_correct_le` | …and at most `f` Byzantine-authored ones. |
| `card_history_le_card_add_card_novelty` | A history costs at most the view plus the novelty. |
| `card_history_le_of_stepNovelty_aux` | — |
| `card_novelty_le_of_byzBudget` | C3″ — the correct side of the budget is a theorem. A validator enforcing only the Byzantine clause `κ` … |
| `card_viewUpto_succ_le_of_bounds` | The generic one-round step: any per-block novelty bounds on the correct and Byzantine acceptances bound … |
| `history_eq_singleton_of_round_zero` | A genesis history is a singleton — round 0 needs no budget clause. |
| `novelty_anti` | Antitone in the view — the property everything below depends on. Deferral is a rate limiter, not a … |
| `round_le_of_mem_viewUpto` | Nothing retained by round `n` sits above round `n`. |
| `sum_novelty_not_correct_le` | The Byzantine spend of one round: at most `f` acceptances, `κ` each. |
| `viewUpto_zero` | — |

### `DoS/Composition.lean` (5)

| Lemma | Role |
|:---|:---|
| `accepted_correct_of_allExposed` | After exposure-complete, a correct validator accepts nothing Byzantine-authored: its next block would have … |
| `byzPool_mono` | — |
| `byzPool_subset_of_allExposed` | The pool freezes. After exposure-complete at `m`, the global Byzantine pool never grows past its … |
| `byzPool_succ_subset` | The freeze step: a round in which every correct acceptance is correct-authored adds nothing to the pool — … |
| `card_viewUpto_le_of_allExposed` | B5 — the slope decays to the correct-production rate. After exposure-complete at `m`, a correct view is … |

### `GC/Chop.lean` (11)

| Lemma | Role |
|:---|:---|
| `authorsAt_chop` | And so are its authors. |
| `blames_chop` | — |
| `certifies_chop` | — |
| `chopBlock_refs_subset` | The truncation's references never exceed the original's. |
| `directSkip_chop` | — |
| `exposedIn_of_exposedIn_chop` | Exposure in the truncation is exposure in the original: the witnessing pair survives un-rebasing. |
| `reaches_chop_iff` | — |
| `reaches_chop_of_reaches` | A path of the original whose endpoint stays at or above the cut never dips below it, so it survives … |
| `reaches_of_reaches_chop` | A step in the truncation is a step in the original. |
| `supporters_chop` | — |
| `votesIn_chop` | — |

### `GC/ChopDecided.lean` (12)

| Lemma | Role |
|:---|:---|
| `Slots.chop_leader` | — |
| `Slots.chop_slotRound` | — |
| `View.chop_ids` | — |
| `anchor_mem_chop_ids` | The anchor of a decided slot at or past the base slot survives the cut. |
| `certificatesIn_chop` | The view filter is invisible to the certificate count: certificates for a slot above the cut live two … |
| `decided_chop_of_decided` | Backward: the original decision is reached on the truncation. Stated over an arbitrary slot `n = d + k` so … |
| `decided_of_decided_chop` | Forward: a decision reached on the truncation, from a truncated view, is the original decision. Structural … |
| `directCommitIn_chop` | — |
| `directSkipIn_chop` | — |
| `eligible_chop` | — |
| `horizon_le_slotRound` | Every slot from the base slot on clears the horizon. |
| `isLeaderBlock_chop` | — |

### `GC/Window.lean` (4)

| Lemma | Role |
|:---|:---|
| `byzBudget_chopD` | — |
| `chopD_accepted` | The truncated delivery accepts at round `m` what the original accepted at `G + m`. |
| `history_chop_anti` | Advancing the cut only shrinks cones… |
| `refsAccepted_chopD` | — |

### `GC/Bootstrap.lean` (6)

| Lemma | Role |
|:---|:---|
| `base_subset_retained` | The base is inside every correct peer's retained store: each base block sits in a correct attester's cone … |
| `card_base_le` | The base alone is bounded by the G6 constant. |
| `history_chop_subset_retained` | G7. The windowed relay obligation: everything a correct author can be asked to serve for its block — the … |
| `history_subset_insert_viewUpto` | A correct author's cone is its own retained store plus the block itself: `RefsAccepted` one step down, S10 … |
| `joinView_ids` | — |
| `mem_viewUpto_of_mem_refs` | A retained store is closed under references: whatever cone brought `i` also holds everything `i` references. |

### `GC/Horizon.lean` (3)

| Lemma | Role |
|:---|:---|
| `block_eq_of` | — |
| `chopBlock_chop` | — |
| `universe_eq_of` | — |

### `Odontoceti/Rules.lean` (6)

| Lemma | Role |
|:---|:---|
| `coneSupports_subset_of_reaches` | Cones nest, so in-cone support does. |
| `coneSupports_subset_supporters` | In-cone supporters are supporters. |
| `mem_coneSupports` | — |
| `not_correct_of_supports_and_blames` | A validator that both supports and blames `L` has two distinct blocks at the decision round, so it is not … |
| `not_correct_of_supports_two` | A validator supporting two *distinct* same-author blocks is not correct: one supporting block cannot … |
| `thickLink_of_directCommit_aux` | — |

### `Odontoceti/Decision.lean` (10)

| Lemma | Role |
|:---|:---|
| `anchor_round_le` | The anchor's round clears the slot's decision round by one — enough for O3 to read the whole certificate … |
| `directCommit_of_directCommitIn` | A view can only under-report: its direct commit is genuine. |
| `directSkip_of_directSkipIn` | A view can only under-report: its direct skip is genuine. |
| `eq_of_directCommitIn` | Cross-view O1′: two direct commits for one slot agree. |
| `eq_of_directCommitIn_of_thickLink` | O4′, from a view: a view-level direct commit is the only same-slot candidate that can pass the indirect … |
| `isLeaderBlock_of_decided` | A committed slot's block is a candidate of that slot. |
| `not_directSkipIn_of_directCommitIn` | Cross-view O1: one validator cannot directly commit what another directly skips. |
| `not_thickLink_of_directSkipIn` | O2, from a view: a view-level direct skip fails the indirect test everywhere. |
| `thickLink_of_directCommitIn` | O3, from a view: a view-level direct commit passes the indirect test at every block two rounds up. |
| `thickLink_of_directCommitIn_at_anchor` | Visibility from an anchor. A slot committed directly carries a thick link at any eligible anchor above it … |

### `Odontoceti/Liveness.lean` (3)

| Lemma | Role |
|:---|:---|
| `all_decided_below_of_fairRun_correct` | O10 at `T := Correct`. |
| `decided_of_leader_of_populated` | O7 against a horizon, the two-round counterpart of `decided_of_leader_of_populated`: the rule needs the … |
| `supportersIn_full` | The full view sees every supporter. |

### `Reactive/Basic.lean` (3)

| Lemma | Role |
|:---|:---|
| `built_succ_le_of_fast_gst` | Latency, in the deployment's own constants. Past GST, with a quorum reliable, every reliable validator … |
| `no_timeout_of_fast_gst` | When the timeout never fires, in the same constants. At the minimal timeout `2Δ + proc` the hypothesis … |
| `slotRound_le_top` | A reliable leader reached its slot's round: its block is in the universe, and `le_top_of_built` reads the … |

### `Reactive/Mysticeti.lean` (1)

| Lemma | Role |
|:---|:---|
| `committed_of_correct_block_of_run` | No reliable validator's block is censored (RS5, execution first). In a reactive run past GST whose timeout … |

### `SafeSkip/Invariance.lean` (11)

| Lemma | Role |
|:---|:---|
| `certificatesIn_subset_ids` | — |
| `certifiedIn_fill` | Certification transports both ways for an old anchor: any witness certificate reached from it is itself … |
| `certifies_fill` | — |
| `creatorsOf_fill` | Creators read identically on old blocks. |
| `inter_view_subset_ids` | — |
| `isLeaderBlock_fill` | A leader block of `U` remains one of the extension. |
| `isLeaderBlock_fill_cases` | A leader block of the extension is an old one, or a filled block on a slot of the recovering validator. |
| `liftView_ids` | — |
| `not_certifiedIn_fresh` | No old anchor certifies a fresh candidate: everything it reaches is old, and no old reference contains a … |
| `votesIn_fill` | Votes read identically on old certificates — for *every* candidate: an old block's references are … |
| `votesIn_subset_ids` | — |

### `SafeSkip/Jump.lean` (16)

| Lemma | Role |
|:---|:---|
| `SkipMsg.v1_eq_of_B1` | The recovering validator is determined by the anchor: it is the anchor's creator. |
| `eq_selfParent_of_mem` | The crux: the self-parent is unique. P2 collapses any reference carrying the block's own creator onto … |
| `lineOf_aux` | — |
| `lineOf_chain` | The derived line is a chain: each block references the one below. |
| `lineOf_creator` | The derived line carries `B2`'s creator throughout. |
| `lineOf_mem` | The derived line stays in the universe. |
| `lineOf_pred` | Peeling one step: the line at `k - 1` is the self-parent of the line at `k`. |
| `lineOf_round` | The derived line's block at index `k` sits at round `k`. |
| `lineOf_top` | The line tops out at `B2` itself. |
| `selfParent_creator` | The self-parent carries the block's own creator. |
| `selfParent_mem_ids` | The self-parent is in the universe. |
| `selfParent_mem_refs` | The self-parent is a reference of its block. |
| `selfParent_round` | The self-parent sits one round below its block. |
| `selfParent_spec` | — |
| `toSkipMsg_line` | — |
| `toSkipMsg_r` | — |

### `Integration/Coverage.lean` (1)

| Lemma | Role |
|:---|:---|
| `mem_ids_of_round_gt` | Above the fill every block is an old one: the fresh identifiers occupy gap rounds only. |

### `Integration/Joiner.lean` (4)

| Lemma | Role |
|:---|:---|
| `horizonStable_const_zero` | The constant policy is horizon-stable exactly when the base slot is the origin — which is the degenerate … |
| `injective_slotRound_chop` | Truncation preserves one-leader-per-round. Injectivity of the rebased rounds needs the base-slot … |
| `joiner_leader_agree` | The joiner's schedule *is* the network's, seen from another origin: combining the assignment agreement … |
| `slotsChop_slotsOf` | The transformers commute. Truncating an adaptive schedule and adapting a truncated one give the same … |

### `Integration/Retention.lean` (4)

| Lemma | Role |
|:---|:---|
| `chopMsg_B1` | — |
| `chopMsg_r` | — |
| `chopMsg_r0` | The rebased crash round: the truncation sees the gap starting `G` lower, as it sees every round. |
| `chopMsg_v1` | The induced message keeps the anchor and the recovering validator, and its gap is the original's shifted — … |

### `Integration/ReGenesis.lean` (8)

| Lemma | Role |
|:---|:---|
| `addGenesis_block_old` | — |
| `addGenesis_sub_stack` | Re-genesis adds nothing the truncated fill lacks. Every block of the re-genesis universe over `chop U G` … |
| `genesis_forced` | A restart is a genesis block, necessarily. If a validator has any block at all in a universe, it has one … |
| `history_addGenesis` | Cones are unchanged, so every cone-based condition reads the same. |
| `mem_addGenesis` | — |
| `reaches_addGenesis` | Reachability is unchanged among old blocks: the new block references nothing, and nothing references it. |
| `rejoin_populated` | — |
| `stack_block_fresh_horizon` | The cut turns the boundary fill block into a genesis block. At a horizon inside the gap, `v1`'s filled … |

### `Integration/Stack.lean` (2)

| Lemma | Role |
|:---|:---|
| `populated_stack` | I16c. Production survives the stack — SS2 then the truncation's own rebasing. The reliable set gains the … |
| `schedule_stack` | I16e. A validator running the stack still has a fair, spanning schedule inside its truncation, for any … |

### `Integration/Lifecycle.lean` (2)

| Lemma | Role |
|:---|:---|
| `crash_recovery_hybrid` | I10. A crash-prone validator rejoins by Safe Skip, and every guarantee of report §12 holds for its fill in … |
| `notMem_byzantine_of_mem_crash` | Membership in the crash class implies the hypothesis above: the crash-prone are honest. The bridge a … |

### `Integration/Exposure.lean` (2)

| Lemma | Role |
|:---|:---|
| `reaches_B1_of_fill` | The first filled block reaches the anchor: the self reference P3′ obliges is a reference like any other, … |
| `reaches_of_fill_of_reaches_B1` | The cone grows. Everything the anchor reaches, the first filled block reaches — so `v1`'s entire pre-crash … |

### `Integration/DeliveryFill.lean` (1)

| Lemma | Role |
|:---|:---|
| `viewUpto_skipFillD` | Accepted blocks are old, so their cones are unchanged and the accumulated view is literally the same … |

### `Integration/CommonTarget.lean` (3)

| Lemma | Role |
|:---|:---|
| `fill_refs_eq` | The filled block's own references, split: the copied ones are universally held (`fill_refs_available`), … |
| `mem_history_of_commonAt` | Everyone holds a common block. Any validator with a block two rounds above has it in its own causal past. |
| `refs_mem_history_of_commonAt` | And everything it cites. Cones nest, so a common block's references — the very blocks a fill would copy — … |

### `Hybrid/Faults.lean` (3)

| Lemma | Role |
|:---|:---|
| `correct_subset_honest` | The fully-correct class is honest: `Correct`, read through the derived instance, excludes the crash-prone … |
| `hybrid_byzantine` | — |
| `hybrid_f` | — |

### `Hybrid/Rules.lean` (10)

| Lemma | Role |
|:---|:---|
| `admissible_kRel` | — |
| `admissible_kTight` | Both named thresholds are admissible exactly at the committee bound — which is the content of the bound: a … |
| `byzantine_of_supports_and_blames` | A validator that both supports and blames `L` has two distinct blocks at the decision round, so it is … |
| `byzantine_of_supports_two` | A validator supporting two *distinct* same-author blocks is Byzantine: one supporting block cannot … |
| `committee_bound_of_admissible` | The converse: an admissible threshold forces the committee bound. Nonemptiness of the interval *is* `n ≥ … |
| `coneSupports_subset_of_reaches` | Cones nest, so in-cone support does. |
| `coneSupports_subset_supporters` | In-cone supporters are supporters. |
| `exists_admissible_iff` | The committee bound is the existence of a threshold. The admissible interval is nonempty exactly when `n ≥ … |
| `mem_coneSupports` | — |
| `thickLink_of_directCommit_aux` | — |

### `Hybrid/Decision.lean` (10)

| Lemma | Role |
|:---|:---|
| `anchor_round_le` | The anchor's round clears the slot's decision round by one — enough for H4 to read the whole certificate … |
| `directCommit_of_directCommitIn` | A view can only under-report: its direct commit is genuine. |
| `directSkip_of_directSkipIn` | A view can only under-report: its direct skip is genuine. |
| `eq_of_directCommitIn` | Cross-view twin uniqueness: two direct commits for one slot agree. |
| `eq_of_directCommitIn_of_thickLink` | H5, from a view: a view-level direct commit is the only same-slot candidate that can pass the indirect … |
| `isLeaderBlock_of_decided` | A committed slot's block is a candidate of that slot. |
| `not_directSkipIn_of_directCommitIn` | Cross-view H2: one validator cannot directly commit what another directly skips. |
| `not_thickLink_of_directSkipIn` | H3, from a view: a view-level direct skip fails the indirect test everywhere. |
| `thickLink_of_directCommitIn` | H4, from a view: a view-level direct commit passes the indirect test at every block two rounds up. |
| `thickLink_of_directCommitIn_at_anchor` | Visibility from an anchor. A slot committed directly carries a thick link at any eligible anchor above it … |

### `Hybrid/Liveness.lean` (5)

| Lemma | Role |
|:---|:---|
| `all_decided_below_of_fairRun_correct` | H7 at `T := Correct` — the whole fully-correct class, which the tight committee requires exactly. |
| `decided_of_leader_of_populated` | H7 against a horizon: two rounds read off it. |
| `directCommitIn_full` | — |
| `q_le_card_correct` | The fully-correct class carries the hybrid quorum: liveness's card hypothesis is satisfiable at `T := … |
| `supportersIn_full` | The full view sees every supporter. |

### `Hybrid/Conservativity.lean` (4)

| Lemma | Role |
|:---|:---|
| `Faults.ext'` | Two `Faults` instances with one bound and one Byzantine set are one instance: the proof fields are … |
| `kRel_eq_of_fc_zero` | At `fc = 0` the `n`-relative threshold is Odontoceti's `n − 3f`. |
| `kTight_eq_of_fc_zero` | At `fc = 0` the tight threshold is the thesis's `2f + 1`. |
| `q_eq_of_fc_zero` | At `fc = 0` the hybrid quorum is the Byzantine quorum. |

### `Adaptive/Basic.lean` (3)

| Lemma | Role |
|:---|:---|
| `epochOf_mono` | — |
| `lt_bound` | The decided slot lies below the bound. |
| `slotsOf_slotRound` | — |

### `Adaptive/Policy.lean` (1)

| Lemma | Role |
|:---|:---|
| `const_pick` | — |

### `Adaptive/Run.lean` (2)

| Lemma | Role |
|:---|:---|
| `adaptive_decided_agree` | The verdict form of uniqueness, in the shape of M6. |
| `partialRun_assign_agree` | Assignments agree wherever the common verdicts determine them. |

### `Adaptive/Liveness.lean` (2)

| Lemma | Role |
|:---|:---|
| `decidedWithin_below_of_committed_run` | The committed-run descent, bounded. The base `decided_below_of_committed_run`, restated with the anchors' … |
| `spansEligible_slotsOf` | Eligibility reads only the round structure, which reassignment fixes: the spanning property transfers to … |

### `Adaptive/Odontoceti.lean` (3)

| Lemma | Role |
|:---|:---|
| `agree` | Two bounded verdicts agree — O5, through the embedding. |
| `decidedWithin_below_of_committed_run` | The committed-run descent, bounded — the base `Odontoceti` descent with the anchor's bound carried … |
| `mono` | The bound relaxes upward. |

### `Nemo/Basic.lean` (2)

| Lemma | Role |
|:---|:---|
| `eq_of_mem_refs_of_creator_eq` | Distinct creators among references are automatic under crash: two refs of the same block sharing a creator … |
| `refs_subset` | Completeness, as a subset statement. |

### `Nemo/CausalHistory.lean` (1)

| Lemma | Role |
|:---|:---|
| `Universe.causal` | The crash universe is a causal structure. Completeness is a field; the round condition is the predecessor … |

### `Nemo/Support.lean` (7)

| Lemma | Role |
|:---|:---|
| `card_authorsAt_le_univ` | The author pool never exceeds the validator set. This is what turns the participation-sensitive threshold … |
| `creators_refs_subset_authorsAt` | The creators of a round-`(n+1)` block's references all hold round-`n` blocks. This is what confines a … |
| `exists_mem_refs_of_correct_support` | The hitting lemma. A round-`(n+1)` block cannot avoid referencing a block satisfying `P`, once enough … |
| `mem_authorsAt` | Membership in `authorsAt`, unfolded: an author of a round is anyone with a block there. |
| `reaches_of_correct_support` | Coverage, participation-sensitive form. A block backed by enough round-`(r+1)` validators is reached by … |
| `reaches_of_correct_support_of_card` | Coverage, uniform form. A `majority` of supporters always suffices. This is the form to use when … |
| `supporters_subset_authorsAt` | Supporters are a subset of the round's authors. |

### `Nemo/Rules.lean` (3)

| Lemma | Role |
|:---|:---|
| `certifiedIn_of_mem_refs` | One hop suffices: a direct reference that votes for `L` certifies. |
| `certifiedIn_of_reaches` | Cone monotonicity: whatever an anchor certifies, everything above the anchor certifies too. |
| `exists_vote_ref_of_directCommit` | The base case. A directly committed leader has a vote among the references of every round-`(r+2)` block: … |

### `Nemo/Decision.lean` (6)

| Lemma | Role |
|:---|:---|
| `anchor_round_le` | The anchor's round clears the slot's decision round by one — exactly the `r + 2` clearance that link … |
| `certifiedIn_of_directCommitIn_at_anchor` | The visibility lemma. A view-level direct commit is certified at any committed anchor of any eligible slot … |
| `directCommit_of_directCommitIn` | A view can only under-report: its direct commit is genuine. |
| `isLeaderBlock_of_decided` | Whatever route it took, a committed verdict names a genuine candidate for that slot. |
| `slot_eq_of_decided_commit` | A committed block belongs to one slot. The ledger reads verdicts off in slot order, so without this a … |
| `slot_eq_of_isLeaderBlock` | A block is the candidate of at most one slot — what `Slots.keyed` yields: two slots sharing a round are … |

### `Nemo/Liveness.lean` (9)

| Lemma | Role |
|:---|:---|
| `PopulatedOn.mono` | Population is antitone: a smaller set is easier to populate. |
| `SynchronisedOn.mono` | Coverage is antitone too. |
| `all_decided_below_of_fairRun_live` | Liveness at `T := Live` — the whole live class, which the tight committee `n = 2f + 1` requires exactly. |
| `decided_of_leader_of_populated` | The commit half against a horizon: two rounds read off it. `T ⊆ Live` is consumed here and only here, … |
| `directCommitIn_full` | — |
| `directCommitIn_mono` | A larger view can only see more supporters. |
| `majority_le_card_live` | The bridge — the arc's only consumer of the fault bound: the live class carries the majority quorum, since … |
| `mem_live` | — |
| `supportersIn_full` | The full view sees every supporter. |

### `MahiMahi/Helpers/Rules.lean` (9)

| Lemma | Role |
|:---|:---|
| `Votes.mem_history` | — |
| `Votes.mem_ids` | — |
| `decisionRoundAt_three` | — |
| `eq_of_votes` | A block votes for at most one candidate of a given author and round: both are least in the same candidate set. |
| `mem_blamers` | — |
| `not_blames_of_votes` | A vote for `L` is not a blame of `L`'s slot. |
| `votesIn_eq_of_three` | The votes a round-`(r+2)` block counts for a round-`r` block are the core's. |
| `votesIn_spec` | A vote counted by a decision-round certificate is a voting-round block of the universe. |
| `votes_iff_mem_refs` | At the round below a block, a vote is a direct reference: the cone at that round is the reference set, and … |

### `MahiMahi/Helpers/Decision.lean` (15)

| Lemma | Role |
|:---|:---|
| `anchor_round` | An eligible anchor's block sits above the slot's decision round. |
| `certificates_nonempty_of_certifiedIn` | — |
| `certifiedIn_of_directCommitIn_at_anchor` | A direct commit is seen from any eligible anchor. |
| `certifiedIn_three_iff` | — |
| `core_directSkipIn_of_directSkipIn` | A blame of the slot in view is a blame of each candidate in view. |
| `decisionRound_eq` | — |
| `directCommitIn_three_iff` | — |
| `directCommit_of_directCommitIn` | — |
| `directSkip_of_directSkipIn` | — |
| `eligible_three_iff` | — |
| `eq_of_directCommitIn` | — |
| `eq_of_hasCertificate` | Two candidates of one slot with certificates coincide. |
| `isLeaderBlock_of_decided` | — |
| `not_certifiedIn_of_directSkip` | The skip half of M4: a skipped slot's candidates are certified nowhere. |
| `not_directSkipIn_of_directCommitIn` | A committed candidate's slot is not skipped, across views. |

### `MahiMahi/Helpers/Counting.lean` (3)

| Lemma | Role |
|:---|:---|
| `certifies_of_refs_reach` | A decision-round block all of whose references reach a correct candidate certifies it: every reference … |
| `nonempty_of_quorum` | A reliable quorum is nonempty. |
| `votes_of_reaches` | Reaching a correct block is voting for it: it is in the cone, and no other block of that author and round … |

### `MahiMahi/Helpers/Liveness.lean` (16)

| Lemma | Role |
|:---|:---|
| `AgreeUpto.blocksAt_eq` | — |
| `AgreeUpto.candidatesAt_eq` | — |
| `AgreeUpto.certificates_eq` | — |
| `AgreeUpto.certifies_iff` | — |
| `AgreeUpto.creatorsOf_eq` | — |
| `AgreeUpto.directCommit_iff` | — |
| `AgreeUpto.goodAt_subset` | — |
| `AgreeUpto.history` | — |
| `AgreeUpto.reaches` | Reachability from a block below the round is the same in both universes: every step stays below the round, … |
| `AgreeUpto.symm` | — |
| `AgreeUpto.votesIn_eq` | — |
| `AgreeUpto.votes_iff` | — |
| `certificatesIn_full` | — |
| `directCommitIn_full` | — |
| `holds_roundBlocks_eventually` | Every reliable round-`n` block is held by every reliable validator by `max (latest n) gst + delay`: its … |
| `lt_of_eligible` | An eligible anchor lies strictly above the slot; the one property of eligibility the descent uses. Needs a … |

### `MahiMahi/Helpers/Synchrony.lean` (1)

| Lemma | Role |
|:---|:---|
| `reaches_of_synchronisedOn` | Under coverage at round `r`, every block at round `≥ r + 2` reaches a reliable round-`r` block: its … |

### `Network/Quorum.lean` (2)

| Lemma | Role |
|:---|:---|
| `populated_and_card_viewUpto_le` | The capstone, unconditional. `EventuallyDelivers` is gone: production plus the enforceable budget plus the … |
| `populated_and_card_viewUpto_le'` | The composed statement — DoS resistance in one theorem. One set of hypotheses — production, post-`R` … |

### `Integration/Sound.lean` (4)

| Lemma | Role |
|:---|:---|
| `hybrid_agree_of_soundOn` | The capstone, from the bundle. A validator that has recovered from a crash and pruned its history still … |
| `soundOn_chop` | Truncation preserves it, shifting the synchrony round by the cut. |
| `soundOn_skipFill` | The fill preserves it, above the gap. The synchrony round must clear the filled round: inside the gap the … |
| `soundOn_stack` | The stack preserves it, the offsets composing exactly as the two statements above suggest: the fill … |

### `WaveRobin.lean` (3)

| Lemma | Role |
|:---|:---|
| `correct_nonempty` | The correct pool is nonempty — at least `2 F.f + 1 ≥ 1` members. All the fault model contributes to … |
| `waveRobin_leader_val` | The leader holds for a wave: slots `3v, 3v+1, 3v+2` of each rotation cycle are led by validator `v`. |
| `waveRobin_slotRound` | The schedule is pipelined: slot `k` is proposed at round `k`. |

<!-- END GENERATED REFERENCE -->
