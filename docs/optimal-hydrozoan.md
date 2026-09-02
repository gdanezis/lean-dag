# lean-dag — Optimal-Hydrozoan: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Optimal-Hydrozoan** arc:
the theory-only variant of Hydrozoan (`\optsysname` in the manuscript)
that closes the gap between Hydrozoan's fast-path fault allowance
`p = ⌊(c + k)/2⌋` and Hydrangea's lower bound `⌊(c + k)/2⌋ + 1` on
two-round commits, by the device FinWhale uses at `n = 3f + 2p − 1`: a
validity rule on the DAG-building layer under which a block that has
seen a leader equivocate must not reference that leader's block, and a
per-block notion of *fast evidence* in place of Hydrozoan's aggregated
weak quorum. The arc keeps Hydrozoan's committee `n ≥ 3f + 2c + k + 1`,
its slow path, its certificates and its schedule, and changes the fast
quorum, the direct skip and the second rung of the indirect rule. It
is a **peer arc** of `hydrozoan.md`'s: `LeanDag/OptimalHydrozoan/`
imports `LeanDag/Hydrozoan/` read-only — the frozen core is never
edited — and every Hydrozoan lemma applies to the underlying universe.
The protocol is not implemented; the arc exists to settle whether an
optimal protocol exists in the spectrum `n ≥ 3f + 2c + k − 1`, and the
answer is that this one reaches Hydrangea's bound at the same
committee. Results carry **OH**-labels, under the statement/proof
partition (§9), with `decide` witnesses in
`LeanDagTest/OptimalHydrozoan/`.

## 0. Overview

Hydrozoan's fast path commits on `qFast = n − p` votes and defends the
commit through the weak rung: an anchor sees at least `qWeak = f + p + 1`
of the fast quorum's votes, and no rival can reach that many. The
counting has slack of one because a Byzantine author's block in the
anchor's history may be a non-voting equivocation. Optimal-Hydrozoan
takes the fault allowance up by one, `pOpt = p + 1`, and recovers the
slack where it is lost: at the decision round, block by block. A
decision-round block is *fast evidence* for a candidate when it
references enough votes for it — `tPlain = n − 2f − c − pOpt` votes if
the block has not witnessed the leader equivocate, and `tEquiv = f + pOpt`
votes, with every rival below `tEquiv`, if it has. The leader-exclusion
rule is what makes the second case count: a block that witnesses the
equivocation references no block by that leader, so the leader is a
*detected* Byzantine replica and at most `f − 1` undetected ones sit
among the block's parents. Quorums of `qCert` such blocks replace
Hydrozoan's quorum of `qWeak` votes: the evidence rung of the indirect
rule asks for `qCert` anchor-linked evidence blocks, and the direct skip
asks for `qCert` blames **and** `qCert` decision-round blocks that are
evidence for no candidate, settled one round later than Hydrozoan's.

The arc's structural observation is that **the seam consumes the
validity rule exactly once**. A fast commit at `qFastOpt` makes every
decision-round block fast evidence for the committed block — by the
plain row if the block witnessed nothing, by the equivocation row and
the exclusion rule if it did — so every eligible anchor reaches an
evidence quorum, a block is evidence for at most one candidate, and two
evidence quorums share a non-Byzantine author. The evidence rung is
therefore unique without a tie-break (decision D3), and the arc's safety
statements need no `LinearOrder` on ids.

Three consequences shape the arc.

- **The direct skip becomes a liveness claim.** Its blame quorum is
  `qCert ≤ q`, which a quorum of correct replicas always supplies, and
  every decision-round block is vacuously no-evidence for a
  candidate-less slot; so a slot whose leader produced no candidate is
  *guaranteed* skipped, where Hydrozoan's skip at `qFast` blames is
  opportunistic (decision D5). With a candidate present the skip is
  not guaranteed — FinWhale's attack, `f` Byzantine votes making every
  honest decision block evidence — and the slot resolves indirectly.
- **Realizability must exhibit an `OptUniverse`.** The liveness
  hypotheses are grounded by a universe satisfying the validity rule;
  in the good case no one equivocates and the rule is implied by the
  package, so the conjunct fixes the witness's type rather than adding
  an obligation.
- **The always-fast parametrisation.** At `k = 2f + c − 2` the allowance
  is `pOpt = f + c`, every fault fits the fast path, and the committee
  is `n ≥ 5f + 3c − 1` — Kuznetsov's `5f − 1` at `c = 0`; Hydrozoan
  needs `k = 2f + c` and `n ≥ 5f + 3c + 1`, Orcaella's bound. The
  four- and seven-replica witness configurations sit at these points.

### 0.1 Correspondence with the paper

| Paper (`hydrozoan-paper/sections/`) | Lean |
|:---|:---|
| Thresholds (`optimal-protocol.tex`) | `Model/Faults.lean` — `OptimalFaults`, `pOpt`, `qFastOpt`, `tPlain`, `tEquiv` |
| DAG-building layer, the validity rule (`optimal-protocol.tex`) | `Model/Universe.lean` — `WitnessesEquivocation`, `OptUniverse` |
| *IsFastEvidence*, *IsNoFastEvidence*, *SkippedLeader* (`optimal-algorithms.tex`, Algorithm 3) | `Model/DirectRules.lean` — `FastCommitOpt`, `votesFor`, `IsFastEvidence`, `IsNoFastEvidence`, `NoEvidenceQuorum`, `SkippedLeaderOpt` |
| *DecideFromAnchor*, the evidence rung | `Model/IndirectRules.lean` — `EvidenceLinked`; `Model/Decided.lean` — `DecidedOpt` |
| `lem:opt-thresholds` (`optimal-proof.tex`) | `ThresholdArithmetic/` (OH1) |
| `lem:opt-direct-decision`, `lem:opt-indirect-decision`, `lem:opt-commit-excludes-direct-skip` | `DirectSafety/` (OH2), `SlotAgreement/` (OH3) |
| prefix consistency | `PrefixAgreement/` (OH4) |
| the Liveness paragraph | `DirectLiveness/` (OH5), `IndirectLiveness/` (OH6), `EventualDecision/` (OH7), `Grounding/` (OH8) |

Every Hydrozoan name the arc reuses — `q`, `qCert`, `qSlow`, `Correct`,
`NonByzantine`, `BlockUniverse`, `View`, `Reaches`, `Slots`,
`IsLeaderBlock`, `IsVote`, `IsCertificate`, `supporters`, `SlowCommit`,
`blames`, `CertifiedIn`, `EligibleAsAnchor`, the liveness package — is
`LeanDag.Hydrozoan`'s, applied to `U.toBlockUniverse`.

## 1. The fault model and the thresholds

`OptimalFaults` extends `Faults` with one field, the paper's standing
assumption `1 ≤ f + c` (decision D2): under `f = c = 0` the model
tolerates no fault and the threshold table is not guaranteed, so the
configuration is excluded by construction rather than assumed away in
every statement. The allowance and the thresholds:

```lean
def pOpt : ℕ := p Replica + 1
def qFastOpt : ℕ := Fintype.card Replica - pOpt Replica
def tPlain : ℕ := Fintype.card Replica - (2 * O.f + O.c + pOpt Replica)
def tEquiv : ℕ := O.f + pOpt Replica
```

`pOpt` is defined through Hydrozoan's `p`, so the "+1" is definitional.
`tPlain` is a truncated subtraction on purpose: the table states the
paper's identity `qFastOpt + q = n + f + tPlain` as an equality, which
fails under truncation, so the row the seam consumes also certifies
that no truncation occurred. `qWeak` is not used.

## 2. The universe with leader exclusion

```lean
def WitnessesEquivocation (U : BlockUniverse Replica BlockId) (k : ℕ)
    (b : BlockId) : Prop :=
  ∃ L₁ L₂, IsLeaderBlock U k L₁ ∧ IsLeaderBlock U k L₂ ∧ L₁ ≠ L₂ ∧
    (∃ j ∈ (U.block b).parents, IsVote U j L₁) ∧
    (∃ j ∈ (U.block b).parents, IsVote U j L₂)
```

A block witnesses an equivocation in a slot when two distinct candidates
of the slot are each voted for by one of its parents — the paper's
*WitnessesEquivocation*, whose quantification over the leader blocks of
the local DAG coincides with the universe-level form here, since the two
candidates a witnessing block sees are parents of its parents and so
held by any view holding the block (decision D6). `OptUniverse` extends
`BlockUniverse` with the rule: a block at the decision round of a slot
that witnesses an equivocation in it references no block by the slot's
leader. The round guard is stated although it is derivable from the
predecessor condition (decision D4), so the rule reads as the paper
states it; with several slots per round the rule applies to each
separately, which the quantifier over slots gives. Views are Hydrozoan's
over the projection. The witness file exhibits a block universe over
which no `OptUniverse` exists: the rule bites, at one block.

## 3. The rules

```lean
def FastCommitOpt (U : BlockUniverse Replica BlockId) (L : BlockId) (r : ℕ) :
    Prop :=
  qFastOpt Replica ≤ (supporters U L (r + 1)).card
```

Fast evidence is stated as two implications rather than an `if`, so
that the core needs no decidability, and is not restricted to
candidates or to decision-round blocks — every consumer guards:

```lean
def IsFastEvidence (U : BlockUniverse Replica BlockId) (k : ℕ) (C L : BlockId) :
    Prop :=
  (¬ WitnessesEquivocation U k C →
    tPlain Replica ≤ (votesFor U C L).card) ∧
  (WitnessesEquivocation U k C →
    tEquiv Replica ≤ (votesFor U C L).card ∧
    ∀ L', IsLeaderBlock U k L' → L' ≠ L →
      (votesFor U C L').card < tEquiv Replica)
```

`IsNoFastEvidence` is evidence for no candidate of the slot, vacuously
true of a candidate-less slot. Quorums of decision-round blocks are
existential over a witness set, as Hydrozoan's `WeakLinked` is: the
block property quantifies over ids, and a filter in the core would need
decidability the core does not carry. The direct skip is `qCert` blames
and a `NoEvidenceQuorum`; the evidence rung is `EvidenceLinked`, `qCert`
anchor-reachable decision-round blocks each fast evidence for the
candidate. `DecidedOpt` is Hydrozoan's `Decided` with the Optimal skip
and evidence rung, over an `OptUniverse` — only the decision relation
and the safety statements see the exclusion rule — and with no tie-break
on rung 2.

## 4. Safety

**OH1 — the threshold table** (`ThresholdArithmetic/`): Hydrozoan's
`CertUniqueness`, `AnchorSeesSlow` and `SlowCollectible` inherited, and
four Optimal rows over every `OptimalFaults` instance — no cap on `k`:

```lean
def CertFastExclusion : Prop :=
  Fintype.card Replica + O.f < qCert Replica + qFastOpt Replica
def EvidencePlain : Prop :=
  qFastOpt Replica + q Replica = Fintype.card Replica + O.f + tPlain Replica ∧
    1 ≤ tPlain Replica
def EvidenceEquiv : Prop :=
  Fintype.card Replica + O.f + tEquiv Replica ≤ qFastOpt Replica + q Replica + 1
def FastUniqueness : Prop :=
  1 ≤ O.f → Fintype.card Replica + O.f < 2 * qFastOpt Replica
```

`CertFastExclusion` replaces Hydrozoan's `FastStarvation`; the two
evidence rows replace `AnchorSeesFast`, and `EvidenceEquiv`'s `+ 1` is
the leader-exclusion dividend — the row that pins
`n ≥ 3f + c + 2·pOpt − 1`. `FastUniqueness` carries the paper's `f ≥ 1`
guard, necessary (at `f = 0` the row fails on a crash-only
configuration with slack, pinned in the witnesses) and sufficient (with
`f = 0` no replica equivocates, so a slot holds one candidate). A
silently stronger guard would keep every witness green; the docstring
says so.

**OH2 — direct-rule safety** (`DirectSafety/`): the five pairings, two
of them Hydrozoan's own claims on the underlying universe (certificates
and the slow path are unchanged), the other three reading the Optimal
rules. Commit/skip is `lem:opt-commit-excludes-direct-skip` restricted
to direct commits; the skip's no-evidence half is never needed against
them.

**OH3 — slot agreement** (`SlotAgreement/`): `DecidedUnique` over
`DecidedOpt`, `lem:opt-direct-decision` together with the
indirect/indirect case, and slightly more — the paper's indirect lemma
covers two decisions from the same anchor, the claim covers two views
whose nearest eligible committed anchors differ. The seam lemmas are the
arc's heaviest proof work: a fast commit makes every decision-round
block evidence for the committed block, evidence for two candidates is
impossible, and two evidence quorums at one anchor share a
non-Byzantine author.

**OH4 — prefix agreement** (`PrefixAgreement/`): Hydrozoan's claims over
`DecidedOpt`, `commitSeq` and `ledger` reused. The docstring states the
linearizer abstraction's limit honestly: the paper's *LinearizeSubDags*
is stateful, the claim covers memoryless per-leader linearizers.

## 5. Liveness

**OH5 — direct liveness** (`DirectLiveness/`). `CommitLiveness` is
Hydrozoan's, harvested as `DecidedOpt`: the slow path is unchanged, and
so is the guaranteed commit. `SkipLiveness` is what the arc adds:

```lean
def SkipLiveness (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (k : ℕ),
    T ⊆ (Correct : Finset Replica) →
    q Replica ≤ T.card →
    PopulatedOn U.toBlockUniverse T (S.slotRound k + 1) →
    PopulatedOn U.toBlockUniverse T (S.slotRound k + 2) →
    (∀ L, ¬ IsLeaderBlock U.toBlockUniverse k L) →
    ∀ V : View U.toBlockUniverse,
      V.CoversUpto (S.slotRound k + 2) →
    SkippedLeaderOpt U.toBlockUniverse k ∧
      DecidedOpt U V k none
```

No synchrony and no fault-count hypothesis: blames and no-evidence
reference nothing. Both claims conclude on any view caught up to the
decision round (`View.CoversUpto`, Hydrozoan's, over the projected
universe) — the blames, the no-evidence quorum and the certificates all
sit at or below it, and the eventual view is the special case.
`FastLatency` at `pOpt` stays outside `Statement`, one more actual
fault than Hydrozoan's admits.

**OH6 — indirect liveness** (`IndirectLiveness/`): totality without the
tie-break — the evidence rung fires on any candidate clearing it, and
that this is at most one is slot agreement's business — and the
descent, `SpansEligible` reused. **OH7 — eventual decision**
(`EventualDecision/`): `RunDecidesBelow` over `DecidedOpt`, Hydrozoan's
`FairRunOn` and `RunsRecur` reused verbatim. **OH8 — grounding**
(`Grounding/`): `WaveRobinFair` reused; `HypothesesRealizable`
quantifies over the schedule and exhibits an `OptUniverse` — the
horizon universe lifted through non-equivocation, the rule inert in
every universe meeting the package; and `GroundedProgress` over
`DecidedOpt` by a universe **authored by correct replicas alone**, the
clause Hydrozoan's statement lacks (`hydrozoan.md` §11).

## 6. Witnesses (`LeanDagTest/OptimalHydrozoan/`)

Every definition is exercised by `decide` before anything is proved
from it, on configurations chosen for what they separate.

- **Configurations.** `Fin 4` with `f = 1`, `c = k = 0` — FinWhale's
  minimal instance, the first at which Hydrozoan has no usable fast
  path (`p = 0`, unanimity) and Optimal-Hydrozoan commits on three of
  four votes; `Fin 3` crash-only, the `f = 0` branch and the one place
  `tEquiv = 1`; `Fin 7` lifted from Hydrozoan's model; `Fin 6` with
  `c + k` odd; `Fin 5` one above the tight size; `Fin 20`, the reference
  implementation's mixed configuration, where every quorum is distinct;
  and local models pinning the `f ≥ 1` guard's necessity and the
  always-fast parametrisation.
- **The rule.** A sixteen-block universe in which the Byzantine leader
  equivocates and a decision-round block witnesses it: the block
  excludes the leader's vote and keeps the honest one, under one slot
  per round and under two, where one block witnesses one slot and not
  the other; and the same table with one more block admitted, a valid
  Hydrozoan universe over which no `OptUniverse` exists.
- **The six routes**, on a thirty-block universe, in particular the
  evidence rung with no certificate anywhere; the headline universe of
  the seam, with witnessing decision blocks; the crash-only universe.
- **FinWhale's attack on the skip**: a candidate withheld from the
  correct replicas while the Byzantine one votes for it, every correct
  decision block evidence — the candidate-less restriction of
  `SkipLiveness` shown necessary.
- **Liveness end to end**: the slow path where the fast one cannot
  fire, the fast commit at exactly `pOpt` actual faults where
  Hydrozoan's premise `card ≤ p` is false, the guaranteed skip at two
  slots, the ladder verdicts the descent derives cross-checked against
  the direct ones through slot agreement, a steady-state universe and
  its variant synchronised from round 1 but not from 0, and the
  sub-quorum negative — a `T`-only universe with `|T| = 2 < q` cannot
  populate round 1.
- **Grounding** at `Fin 3`, `Fin 4`, `Fin 7` and `Fin 20`, realizability
  under the two-slots-per-round schedule, and the axioms tripwire
  (`Axioms.lean`).

The witness headers record what a four-replica committee cannot
exercise — its quorums coincide — and defer to a committee of five or
more: a proper-subset `T`, a run whose slots commit only through the
slow path, a rival at exactly `tEquiv`, a Byzantine replica that both
votes and blames.

## 7. Findings for the paper

- **The evidence rung needs no tie-break.** Two candidates cannot both
  clear it, so `argmin digest` in *DecideFromAnchor* is vacuous; the
  arc drops it and proves uniqueness (D3).
- **The skip is a liveness claim for candidate-less slots and not
  otherwise.** The paper's remark on FinWhale's attack is exhibited on
  data (`OA`), and the guaranteed skip lands one round later than
  Hydrozoan's.
- **`f ≥ 1` on fast/fast agreement is exact.** The guard is necessary
  at `f = 0` with slack and sufficient by non-equivocation; the arc
  states the row with the guard and discharges the `f = 0` case
  separately (D2).
- **Realizability is implied by the package.** Leader exclusion holds
  in every `T`-only synchronised universe, so the paper's "the
  DAG-building layer never blocks after GST" is, in the good case, a
  consequence of synchrony and validity, not a further assumption.
- **The always-fast point** `k = 2f + c − 2`, `n ≥ 5f + 3c − 1`, sits on
  the arc's own witnesses.

## 8. Out of scope

- Implementation: the arc is theory-only by design; the reference
  implementation is Hydrozoan's.
- The `n ≥ 5` witness material listed in §6.
- Everything Hydrozoan leaves out (`hydrozoan.md` §12): delivery, GST,
  weak links, the DFS reading of a vote, round-jumping recovery.

## 9. Layout and discipline

The arc mirrors `LeanDag/Hydrozoan/` one directory over, under the same
partition; `OptimalHydrozoan` is in `ARCS` of
`scripts/check-arc-holes.py`.

```
LeanDag/OptimalHydrozoan/
  Model/         definitions only: Faults (§1), Universe (§2),
                 DirectRules, IndirectRules, Decided (§3)
  Helpers/       lemma and construction infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ and the Hydrozoan Statement.lean it mirrors;
                            `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
LeanDagTest/OptimalHydrozoan/  witness models; audited
```

Results: `ThresholdArithmetic` (OH1), `DirectSafety` (OH2),
`SlotAgreement` (OH3), `PrefixAgreement` (OH4), `DirectLiveness` (OH5),
`IndirectLiveness` (OH6), `EventualDecision` (OH7), `Grounding` (OH8).

**Relation to the Hydrozoan arc.** Read-only, by construction (D1):
`OptUniverse` extends `BlockUniverse`, every rule predicate is applied
to `U.toBlockUniverse`, and a `Statement.lean` may import the Hydrozoan
`Statement.lean` it mirrors to reuse claim shapes (`CertUniqueness`,
`commitSeq`, `SpansEligible`, `FairRunOn`) — a reviewed file importing a
reviewed file, the one sanctioned exception to "imports `Model/` only".
Where a Hydrozoan statement says less than its docstring, the Optimal
mirror is corrected and the Hydrozoan one is recorded, never edited.

**Instance diamonds.** `OptimalFaults` instances project to `Faults`
instances; a file importing a Hydrozoan liveness witness and an Optimal
one would carry two `Faults (Fin n)` for one `n`. No Optimal witness
file imports a Hydrozoan liveness witness file, and where two instances
are in scope a table names its instance explicitly.

**The freeze protocol** is Hydrozoan's (`hydrozoan.md` §10). Six
decisions were settled before the first file was written: D1 the
parallel arc; D2 non-triviality as a field; D3 no tie-break on rung 2;
D4 the explicit round guard; D5 the skip promoted to a liveness claim;
D6 the fidelity of `WitnessesEquivocation` and `IsFastEvidence` to the
paper's *Votes* read at wave length 3.

## 10. Phases

Developed in `asonnino/mysticeti` (`lean/`, PR #230) as the parallel arc
`Hydrozoan/Optimal/`, and ported here as a peer arc with its namespace
re-homed under `LeanDag.OptimalHydrozoan` and no other change.

| phase | deliverable |
| :-- | :-- |
| O1 | `Model/Faults.lean`; the threshold tables at `Fin 3`, `4`, `5`, `6`, `7`, `20` |
| O2 | `ThresholdArithmetic/` (OH1) |
| O3 | `Model/Universe.lean`; the equivocation universe and the one no `OptUniverse` extends |
| O4 | `Model/{DirectRules,IndirectRules,Decided}.lean`; the six-route universe |
| O5 | `DirectSafety/` (OH2) |
| O6 | `SlotAgreement/` (OH3); the headline universe with witnessing decision blocks |
| O7 | `PrefixAgreement/` (OH4); the axioms tripwire |
| OL1 | `DirectLiveness/` (OH5); FinWhale's attack on the skip |
| OL2 | `IndirectLiveness/` (OH6) |
| OL3 | `EventualDecision/` (OH7); the steady-state universes |
| OL4 | `Grounding/` (OH8); the quorum-separating and sub-quorum witnesses |
| OL5 | this record; report §23; the reference pipeline |

Each phase ran as statements → review → freeze → proofs → witnesses →
a reviewing agent over the frozen files and the witnesses → commit; the
phases introducing definitions (O1, O3, O4, OL1, OL4) were planned
before their statements were written.
