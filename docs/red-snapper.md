# lean-dag — RedSnapper: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **RedSnapper** arc: the
owned-object fast path of the RedSnapper paper (`~/GitHub/redsnapper-paper`,
"Snapper" in the manuscript) layered over an uncertified DAG whose
consensus is treated as a black box. Validators publish a *stance* per
object version in the blocks they already produce; transaction
certificates, skip certificates and unlock certificates are read from
the DAG; a conflict between two transactions spending one owned object
is resolved in the epoch rather than at its boundary. At `n ≥ 3f + 1`
the univalent cases are decided from the DAG and the bivalent case at a
committed anchor; at `n ≥ 5f + 1` a validator may safely revoke an
earlier vote on `2f + 1` opposing votes, a coin coordinates the moves,
and a freeze-and-count fallback at an anchor bounds the resolution. A
protocol-independent section characterises when revocation is safe and
when a quorum of votes is guaranteed to expose it. The arc proves the
certificates exclusive, the verdicts unique across views and routes,
the conflict resolved under a structural rendering of synchrony, and
the `5f + 1` revocation rules safe with the recovery fallback; it
states the revocation arithmetic first, as the seam both protocols
consume. Results carry **RS**-labels; everything lives in
`LeanDag/RedSnapper/` under the statement/proof partition (§5), with
`decide` witnesses in `LeanDagTest/RedSnapper/`, consuming nothing from
the core.

This record was written at Phase 0 as the plan; this is the final
position. Everything planned is proved: RS1–RS9, ten `holds` theorems
each pinned by the axiom tripwire to `[propext, Classical.choice,
Quot.sound]`, over a trusted core the reader can audit without reading
a proof. The headline the mechanisation adds to the paper: **the
`5f + 1` rules' safety needs only `n ≥ 3f + 1`** — every certificate
exclusion closes at the small committee (finding 19), and the wide one
is consumed exactly three times: the frozen set's overlap with a
hidden commit (finding 20 — a safety count, serving RS8 through the
reflection claim), the fragmented coin round's universal movability,
and RS1's exposure itself, the seam §10 of the paper draws.

## 0. Overview

The arc's one structural observation is that **the two protocols differ
in one inequality**. Both count the same two thresholds: a quorum
`n − f` (the paper's `2f + 1` at `n = 3f + 1`, its `4f + 1` at
`n = 5f + 1`) and a half `2f + 1`. At `n ≥ 3f + 1` the half is the
revocation threshold of the paper's Theorem "vote revocation": `2f + 1`
opposing votes prove that a validator's earlier vote can no longer
complete a quorum. What the larger committee adds is *exposure*: among
any `n − f` votes one side reaches `2f + 1` exactly when
`n ≥ 5f + 1`. Below that bound the protocol may collect a quorum of
votes and still be unable to move, which is the bivalent case that
`n = 3f + 1` sends to consensus; at or above it every quorum licenses a
move, which is what the coin-driven protocol relies on. RS1 states this
arithmetic once, in the paper's protocol-independent form and at the
two thresholds, and both protocols consume it.

Three consequences shape the arc.

- **Safety has no behavioural content beyond monotonicity.** Every
  safety lemma at `3f + 1` uses of a correct validator only that it does
  not equivocate, that its blocks form a chain, and that its stance on
  an object moves along `none → {tx, ⊥}`, `tx → {tx, ⊥}`, `⊥ → ⊥`. The
  full voting rule — when a correct validator adopts, keeps or retracts
  — enters only the liveness claims (D5).
- **Consensus is one global object.** The paper's interface properties
  (C1)–(C3) say the committed anchor sequence and every anchor's causal
  history are the same at every correct validator. The arc takes the
  anchor sequence as a component of the universe; the anchor-route
  verdicts are then functions of global data, and agreement across
  validators reduces to agreement across views for the consensusless
  routes (D4, D6).
- **The `5f + 1` results generalise to `n ≥ 5f + 1`.** With the
  thresholds written as `n − f` and `2f + 1`, every counting step of
  the paper's `5f + 1` section closes (`|S| ≥ n − 2f`,
  `n − |S| ≤ 2f < 2f + 1`; `|F ∩ S| ≥ n − 3f ≥ 2f + 1`), as Odontoceti's
  did (D1).

### 0.1 Correspondence with the paper

| Paper (`redsnapper-paper/`) | Lean |
|:---|:---|
| System model, `f`, correct validators (`2.Prelim.tex`) | `Model/Faults.lean` — `Faults`, `quorum`, `half`, `Five`, `Correct` |
| §10 Fundamental limits of vote revocation | `Model/Revocation.lean` — `Profile`, `supporters`, `opposers`, `voters`; `Revocation/` (RS1) |
| Blocks, `Link`, `RoundParents` (`Alg:FastPathPredicates`) | `Model/{Block, Universe, View, CausalHistory}.lean` — `Block`, `ValidWrt`, `Universe`, `View`, `Reaches` |
| Transactions, `OwnedInputs`, `Includes`, `Candidates`, `ConflictedObjs` | `Model/{Block, Transaction}.lean` — `Transactions`, `Conflict`, `Owned`, `Includes`, `IsCandidate`, `Conflicted` |
| `Stance`, `AckedBefore`; the `held` automaton of §7 | `Model/Stance.lean` — `StanceIs`, `AckedBefore`, `StanceDiscipline` |
| `IsFastVoteTX`, `IsSkipVoteObj`, `IsUnlockVoteObj` | `Model/Votes.lean` — `IsFastVote`, `IsBotVote`, `IsSkipVote`, `IsUnlockVote` |
| `IsFastCertTX`, `HasCertTX`, `CertVisible`, `IsSkipCertObj`, `IsUnlockCertObj`; `DAG[r]` | `Model/Certificates.lean` — `AtLeast`, `blocksAt`, `IsFastCert`, `HasCert`, `CertVisible`, `IsSkipCert`, `IsUnlockCert`, `FastQuorumAt` |
| Lemmas single-ack, cert-unique, univalent, fast-unlock-exclusion, cert-propagation | `CertificateExclusion/` (RS2) — `HonestSingleAck`, `CertUniqueness`, `AckSkipExclusion`, `AckUnlockExclusionBelow`, `CertPropagation` |
| Consensus interface (C1)–(C4), `Dead`, `Resolves` | `Model/{Anchors, Dead}.lean` — `Anchors`, `DeadGiven`, `ResolveReadyGiven`, `ReleasedBelow`, `ResolvesAt`, `DeadAt` |
| `TryFastDecideTX`, `TrySkipDecideObj`, `FinalizeOnCommitTX` (both loops), `ResolveOnCommitObj` | `Model/Verdict.lean` — `Fate`, `FastQuorumAtInView`, `SkipQuorumAtInView`, `TxVerdict` (`releasedDrop` is the first loop's late candidate) |
| Theorem commit-safety, Lemma mixed-object safety | `TxAgreement/` (RS3) — `VerdictAgreement`, `NoConflictingFinal`, `MixedViaAnchor` |
| Lemmas fp-liveness, equiv-live; `CastVotes` | `Model/{Liveness, HonestVoting}.lean` — `PopulatedOn`, `SynchronisedOn`, `VotingRule`; `Uncontested/` (RS4) — `FastLiveness`, `FastVerdict`, `AnchorVerdict`; `ConflictResolution/` (RS5) — `Trichotomy`, `AnchorDecides` |
| Lemma termination-3f; Termination of the Conditional State-Machine Replication definition | `Termination/` (RS11) — `DecidedAgainst`, `Decided`, `DecidedOrdered` |
| §8 certificates, refutations, moves (`Alg:FastPathPredicates5f+1`) | `Model/Five/{Certificates, Moves}.lean` — `IsAntiVote`, `IsFullCert`, `IsHalfCert`, `IsRefutation`, `IsFullUnlockCert`, `MoveDiscipline` |
| §8 freeze, `Triggers`, `TriggerAnchor`, `Frozen`, `Resolves`; `ResolveOnCommitObj`'s `F`, `W` | `Model/Five/Freeze.lean` — `AtLeastV`, `Triggers`, `TriggerAt`, `Frozen`, `FreezeQuorum`, `ResolvesFiveAt`, `EligibleFive`, `FreezeDiscipline`; `Block.freezes` |
| `TryFullDecideTX`, `TryFullUnlockObj`, `FinalizeOnCommitTX` (both loops), `ResolveOnCommitObj` | `Model/Five/Verdict.lean` — `VerdictFive` (owned and mixed candidates; `mixedFinal` is the anchor route; `observedRivalDrop`, `certifiedRivalDrop` and `resolvedDrop` the first loop's aborts) over a linear-order parameter `prio` (the min-hash tie-break, D8-style) |
| Lemmas single-stance-5f … full-cert-unique | `Five/FullCertSafety/` (RS6) — `SingleStance`, `CommitExcludesRefutation`, `UnlockExcludesRefutation`, `CommitExcludesUnlock`, `FullCertUniqueness` |
| Lemmas recovery-determinism, recovery-reflects, recovery-safety | `Five/RecoverySafety/` (RS7) — `ResolutionUnique`, `RecoveryReflects`, `UnlockEmptiesElection`, `RecoverySafetyBot`, `RecoverySafetyWin` |
| Theorem safety-5f | `Five/Agreement/` (RS8) — `VerdictAgreement`, `NoConflictingFinal`, `MixedViaAnchor` |
| Phase 3 of `CastVotes` (`Alg:Voting5f+1`), the coin | `Model/Five/Coin.lean` — `CoinRule` (the coin as its output `w`, D8), `StancedAt`, `AgreeUpto` (measurability, Mahi-Mahi's MM2′ pattern) |
| Lemma coin-success | `Five/CoinSuccess/` (RS9a) — `CoinConcentrated`, `CoinFragmented`, `CoinSuccessCount` (the probability bound as its numerator: a good-target set of at least `half`), `CoinMeasurable` |
| Lemma recovery-termination | `Five/RecoveryTermination/` (RS9b) — `TriggerExists`, `ResolutionExists`, `RecoveryDecides`, `ConflictDecides` |
| Lemma termination-5f | `Five/Termination/` (RS12) — `Decided` |
| Lemma uncontended-liveness; phases 2–4 of `CastVotes` (`Alg:Voting5f+1`) | `Model/Five/HonestVoting.lean` — `VotingRuleFive`; `Five/Uncontested/` (RS10) — `FullLiveness`, `FullVerdict`, `MixedVerdict` |

Names follow the paper's where it has them (`Candidates`, `Stance`,
`HasCert`); faulty validators are Byzantine, the rest correct.

## 1. Decisions

Each decision is stated with its reason and what it changes downstream.

**D1 — Thresholds `n − f` and `2f + 1`, committees `n ≥ 3f + 1` and
`n ≥ 5f + 1`.** The paper fixes `n = 3f + 1` with every threshold
`2f + 1`, and `n = 5f + 1` with `4f + 1` and `2f + 1`. The arc's
`Faults` class assumes `3f + 1 ≤ n`; `quorum = n − f` and
`half = 2f + 1` are the two thresholds; the `Five` mixin adds
`5f + 1 ≤ n`. At the tight committees the definitions evaluate to the
paper's numbers. Reason: two quorums of `2f + 1` do not intersect in a
correct validator above `n = 3f + 1`, so the paper's constants do not
generalise and `n − f` is what every argument counts; this is the
core's convention. Consequence: the `5f + 1` section is proved for
every `n ≥ 5f + 1`, and RS1's corollaries are stated at `quorum` and
`half` so that the exposure bound *is* the `Five` premise. The two
consensusless finality quorums — the fast route's certificates and the
skip route's skip certificates, both `2f + 1` blocks in the paper — are
read at `quorum`: what certificate propagation counts, and, above
`n = 3f + 1`, a deliberate strengthening of the skip route's premise
that any skip-route liveness claim must meet.

**D2 — One owned input per transaction.** §8 defines `IsOwned` as
exactly one input; §7's `Dead` and the transaction-closed fixpoint
`RecoveryObjs` exist only to keep a validator's stance coherent across
several owned inputs. With one input the fixpoint collapses —
`RecoveryObjs(b) = ConflictedObjs(b)`, since each disjunct of `Dead`
already implies a visible conflict — and `Dead` survives only as the
filter that stops a certified transaction from being committed after
its object was released at an earlier anchor. Consequence: no closure
operator in the trusted core; multi-input transactions are a candidate
follow-up arc, not a fidelity gap of this one.

**D3 — Object versions atomic; `Spendable` dropped from
`Candidates`.** The paper's `Spendable` is a recursion on the version
index through certificates and anchors, and no safety lemma consumes
it. The arc treats an object version as an opaque element of `Obj`;
`Candidates(b, o)` is every valid transaction in `b`'s causal history
spending `o`. Consequence: the object-reuse lemma (`o^{j+1}` becomes
spendable once `o^j` is decided) is out of scope, and the gap is
recorded on the definition. The direction of the gap flips with the
side of a claim: enlarging `Candidates` is conservative inside the
safety statements, but inside the hypothesis-predicate `VotingRule` it
narrows applicability — an execution whose sole included candidate is
unspendable satisfies the paper's rule and not the arc's.

**D4 — Consensus as a chained anchor sequence.** The universe carries
the committed anchors as a sequence of block ids in the universe,
committed order being sequence order, with every earlier anchor in the
causal history of every later one. (C1)–(C3) are then the fact that the
sequence is one object; (C4) is a liveness hypothesis, anchors above
every round. The chaining is what the paper's `Dead` and `Spendable`
assume when they test an earlier anchor by `Link(A, b)` (§3, finding 3);
it is true of Mysticeti and could later be derived from the core's
`commitSeq` in a grounding phase.

**D5 — Honest behaviour in two predicates.** On correct-authored blocks
of the universe: a *safety-side* predicate — non-equivocation, the
self-parent chain, and stance monotonicity along `none → {tx, ⊥}`,
`tx → {tx, ⊥}`, `⊥ → ⊥` at `3f + 1`; at `5f + 1`, a stance changes only
on a refutation of the old stance among the round parents, a frozen
stance never changes, and a stance `tx` implies `tx` is a candidate at
that block — and a *liveness-side* predicate, the full `CastVotes` rule.
Reason: every safety lemma was traced and uses nothing beyond the
former; stating the minimum on the safety side is what makes the safety
results say what they claim about the protocol's freedom.

**D6 — Verdicts as an order-free inductive relation.** `Verdict U V tx v`
with one constructor per route — fast finality, skip, finalize at an
anchor, resolve at an anchor (commit or drop) — the paper's stateful
guards (`fastCommittedTX`, `skippedTX`, `decidedObj`, "the first
anchor") encoded as explicit least-anchor clauses, as Hydrozoan's
`Decided` encodes the nearest anchor. Consensusless routes are read
through views and under-report; anchor routes are functions of the
global data of D4. Agreement is uniqueness of `v` across views and
constructors, the shape of `SlotAgreement.DecidedUnique`.

**D7 — Equivocation voids a stance at the latest declaring round.** The
`3f + 1` predicate file voids the stance on equivocation at *any*
common round; §8 and the §7 prose void it only when the latest declaring
round holds two blocks. The arc takes the latter, the weaker premise;
the proofs need only that a correct validator's stance is unique.

**D8 — The coin is a parameter.** `coin : Obj → ℕ → Validator` is a
function of the model. The arc proves the deterministic core of the
coin lemma — if the coin selects a holder of a stance held by `2f + 1`
correct validators, or any correct validator when no stance has that
many, every correct validator holds one stance a round later — and the
cardinality of the favourable set; the probability and the expectation
bound of the latency theorem are left as arithmetic outside the arc.

**D9 — Mixed transactions as a tag.** A transaction is owned or mixed;
the consensusless routes are gated by owned. The paper's mixed-object
safety lemma is then a corollary inside RS3; its liveness lemma reduces
to (C4) and is not stated.

**D10 — One arc, results namespaced by committee.** `LeanDag/RedSnapper/`
holds a shared `Model/` — faults, blocks, transactions, stances,
anchors — and results under `RedSnapper.*` for the `3f + 1` protocol and
`RedSnapper.Five.*` for the `5f + 1` one, since the two share everything
except thresholds and the honest-move rule.

## 2. Phases

| phase | audit surface | result |
| :-- | :-- | :-- |
| 0 | this record; branch `red-snapper` | D1–D10 |
| 1 | `Model/Faults.lean`, `Model/Revocation.lean`; the committee and profile witnesses | |
| 2 | `Revocation/Statement.lean` | RS1: the support bound and the revocation threshold, its tightness, the exposure characterisation, the three corollaries at `quorum` and `half` |
| 3 | `Model/{Block, Universe, View, CausalHistory, Transaction, Stance}.lean`; witnesses for equivocation, a chain, a stance read through twins | |
| 4 | `Model/{Votes, Certificates}.lean`; `CertificateExclusion/Statement.lean` | RS2: honest single ACK, certificate uniqueness, ack/skip exclusivity, a fast commit excludes an unlock certificate, certificate propagation |
| 5 | `Model/{Anchors, Dead, Verdict}.lean`; `TxAgreement/Statement.lean` | RS3: verdict uniqueness across views and routes; no two conflicting transactions finalised; one finalised transaction per object; the mixed corollary |
| 6 | `Model/{Liveness, HonestVoting}.lean`; `Uncontested/`, `ConflictResolution/` | RS4: a sole candidate reaches fast finality in two synchronised rounds; RS5: by `r + 2` every synchronised block holds an ack certificate or an unlock certificate in its history, so every synchronised anchor above `r + 2` resolves the object |
| 7 | `Model/Five/{Certificates, Moves}.lean`; `Five/FullCertSafety/` | RS6: single stance; a full certificate excludes refutations of its ACK, a full unlock certificate excludes refutations of `⊥`, the two certificates exclude each other, and conflicting full certificates never coexist — all at `n ≥ 3f + 1` (finding 19) |
| 8 | `Model/{Block (the defaulted `freezes` field), Five/Freeze, Five/Verdict}.lean`; `Five/RecoverySafety/`, `Five/Agreement/` | RS7: resolution uniqueness; a hidden commit is reflected (`W = {tx}`, candidacy derived — finding 21); an empty election forbids any full certificate; no rival certificate above a resolution. RS8: verdict agreement and no conflicting finalisation across views and routes |
| 9 | `Model/Five/Coin.lean`; `Five/CoinSuccess/`, `Five/RecoveryTermination/` | RS9: the coin round unifies the committee — the concentrated case at any committee, the fragmented case (all movable at once) under `Five`, at least `half` good targets, and the good set fixed before a post-round draw (`AgreeUpto`); the trigger, the resolution, and a verdict for every candidate exist under the structural C4/C5 |
| 10 | this record's final position; the paper appendix (`appendix-mechanisation.tex` in the paper repo); README; the tripwire completeness check; the pull request | |

Phases 1 and 2 are reviewed together: the statement fixes what the
model must carry. Each phase runs as statements → review → freeze →
proofs and witnesses, with a cold-context vacuity auditor over the
frozen files in parallel → commit.

### 2.1 The results

Each result names the behavioural hypotheses it consumes and the
committee bound it actually uses; nothing else about validators is
assumed anywhere.

- **RS1 `Revocation/`** — the paper's §10, protocol-independent: the
  support bound, the revocation threshold `n + f − C + 1` and its
  tightness for `f ≤ C ≤ n` (finding 16), and the exposure
  characterisation — among any `C ≥ n − f` votes one side reaches the
  threshold exactly when `n ≥ 5f + 1`. Pure arithmetic over vote
  profiles; no DAG, no behaviour.
- **RS2 `CertificateExclusion/`** — honest single ACK, certificate
  uniqueness, ack/skip exclusivity, the round-conditioned
  ack/unlock exclusion, and certificate propagation, at `n ≥ 3f + 1`
  under `StanceDiscipline` alone — the `held` automaton's monotonicity,
  nothing about when a validator votes.
- **RS3 `TxAgreement/`** — verdict agreement across views and routes
  and no two conflicting finalisations under `StanceDiscipline`; the
  mixed corollary with no hypothesis at all (arc audit); the anchors are one global value (D4), so
  cross-validator agreement about the anchor route is definitional and
  the theorem's content is route-pair exclusion.
- **RS4 `Uncontested/` and RS5 `ConflictResolution/`** — the `3f + 1`
  liveness pair under `VotingRule` alone (the safety automaton is not
  consumed — arc audit; `AnchorDecides` still takes it, through RS2)
  and the structural synchrony of
  `PopulatedOn`/`SynchronisedOn`: a sole valid candidate reaches fast
  finality two synchronised rounds after its carrier (the no-rival
  premise gated by validity, finding 18) — or, owned or mixed, at a
  committed anchor above a correct certificate-round block, the C5
  branch of fp-liveness (`AnchorVerdict`) — and a conflict resolves at
  every synchronised anchor above `r + 2` through the corrected
  trichotomy (finding 5).
- **RS11 `Termination/`** — Lemma termination-3f, in its two halves.
  *Decided against*: a candidate of a committed anchor is dropped when
  its object resolved at or below the anchor, or when the anchor holds
  the certificate of a finalized rival — under `StanceDiscipline`
  alone, with no voting rule and no synchrony, which is what lets it
  speak of runs where the correct validators decided the object and
  fell silent (there `VotingRule` is false, and the second half says
  nothing). *Decided*: a valid transaction included by a correct block
  receives a verdict, under both `3f + 1` hypotheses and the structural
  synchrony, given a correct-authored committed anchor four rounds above
  (C4) — and no (C5): the anchor's own chain carries the evidence
  (finding 34). No premise says whether the transaction is contested:
  the proof splits on whether the anchor's own block two rounds above
  the carrier includes a valid rival, reading RS4's no-rival premise at
  that block only (finding 18). A third claim restates it from the
  paper's "placed in the global order". It needed one more route in the
  verdict relation, `releasedDrop` — a candidate first included above
  its object's release, `FinalizeOnCommitTX`'s first loop; RS3 covers
  the new route by the argument it already had, since a finalized
  transaction's object is release-ready at no anchor.
- **RS6 `Five/FullCertSafety/`** — single stance unconditionally; under
  `MoveDiscipline` (a declared change carries a refutation of the old
  value), a full certificate excludes refutations of its ACK, a full
  unlock certificate excludes refutations of `⊥` (the algorithm's
  split-refutation form, finding 8), the two certificates exclude each
  other at any round pair, and conflicting full certificates never
  coexist — **all at `n ≥ 3f + 1`** (finding 19).
- **RS7 `Five/RecoverySafety/`** — resolution uniqueness for any linear
  order; the election claims stated, after the arc audit, at a bare
  marker quorum with no resolution in sight: under `MoveDiscipline` and
  `FreezeDiscipline` a full certificate anywhere makes its transaction
  the unique eligible one (candidacy derived, round-unconditional —
  finding 21; needs `Five`), a full unlock certificate anywhere leaves
  nothing eligible (the lemma's second clause; no `Five` — finding 29),
  an empty election forbids any full certificate ever (needs `Five`),
  and — under `FreezeDiscipline`
  alone, at any block — no rival of an eligible transaction certifies
  above it (no `Five`, no `MoveDiscipline`, no anchors).
- **RS8 `Five/Agreement/`** — Theorem safety-5f: verdict agreement and
  no conflicting finalisation across views for the order-free
  `VerdictFive`, under `Five`, both disciplines, and the shared
  tie-break order; the algorithm's `decidedObj`/`skippedTX` guards and
  route precedence are discharged as theorems, and finding 9's miscited
  step closes through RS7's round-unconditional reflection. Owned and
  mixed candidates compete alike; the two certificate routes —
  `fullFinal` on an observation, `mixedFinal` at a committed anchor —
  rest on the same evidence, and a finalised mixed transaction is tied
  to the anchor that finalised it, with no hypothesis.
- **RS9 `Five/CoinSuccess/`, `Five/RecoveryTermination/`** — the coin
  round unifies the committee: the concentrated case at any committee,
  the fragmented case under `Five` (universal movability is exactly
  `n ≥ 5f + 1`), at least `half` good targets — the numerator of the
  paper's probability bound — and the good set fixed before a
  post-round draw (`AgreeUpto`, Mahi-Mahi's measurability pattern);
  the trigger, the first-quorum resolution, and a verdict for every
  candidate exist under the structural C4/C5 hypotheses, with no `Five`
  anywhere in termination; `ConflictDecides` composes them into the
  lemma's three cases, asking for the markers only where no certificate
  exists — a validator that decided on a certificate never freezes.
- **RS12 `Five/Termination/`** — Lemma termination-5f, contested half
  (the uncontested half is RS10): every candidate of a committed anchor
  receives a verdict — the per-transaction form of RS9b's
  `ConflictDecides`, under its two consensus-liveness inputs and, where
  no certificate exists, a rival under a committed anchor too. The
  algorithm has it only since `FinalizeOnCommitTX`'s first loop aborts
  owned candidates too (finding 33); the relation renders that loop by
  what decided the object: an owned rival's full certificate in the view
  (`observedRivalDrop`, read as `fullFinal` reads it), a rival's full
  certificate under the anchor (`certifiedRivalDrop`), or a resolution
  below the anchor that the transaction did not win (`resolvedDrop`).
  RS8 covers the three routes with the lemmas it already used —
  certificate uniqueness, and the reflection claim, which makes a
  certified transaction the only eligible one. Between RS10 and RS12
  lies a run with no certificate where a valid rival is included
  somewhere and never ordered.
- **RS10 `Five/Uncontested/`** — Lemma uncontended-liveness in RS4's
  shape, under `VotingRuleFive`: a sole valid candidate is fully
  certified by every correct block two synchronised rounds after its
  carrier, final on one observation if owned and at a committed anchor
  above the certificate if mixed — at any `n ≥ 3f + 1`. The `5f + 1`
  rule traces a `⊥` to a visible conflict or to an own freeze marker,
  and a marker to an anchor that triggers; the `3f + 1` rule's
  `bot_conflicted` has no justification in phase 2.

### 2.2 The witnesses (`LeanDagTest/RedSnapper/`)

Every definition is exercised by `decide` on concrete committees before
anything is proved from it — `Fin 4` and `Fin 7` for the `3f + 1`
protocol and the thresholds' coincidence at the tight committee,
`Fin 6` (`quorum = 5 ≠ half = 3`, one Byzantine) for everything at
`5f + 1`, `Fin 11` for the tight `Five` committee. The base files build
the happy paths: `UCert`/`USkip` (certificates form, propagate, and are
retracted), `ULive`/`UTri` (the liveness pair end to end),
`U6Full`/`U6Ref`/`U6Unlock` (the four `5f + 1` certificate shapes, the
two legal move shapes — including the `⊥ → ack` coin move that
`StanceDiscipline` forbids), `U6Rec`/`U6RecBot` (the recovery pipeline
with a committed winner and with an empty election), `U6Coin`/`U6Frag`
(both coin cases through to their certificates). The hardening files
carry the audit-adopted mutants: threshold boundaries at exactly
`half`/`quorum` and one below, equivocation-voided stances and
anti-votes, stale refutations at the wrong block, Byzantine marker
shapes, the one-shot and least-index clauses, the `prio` winner flip on
a two-member election, the `Five` gates refuted at the `3f + 1`
committee, and per-clause refutations of every behavioural hypothesis.
The mixed route has its own files: `MixedRecovery` (a second
transaction table, `threeTxs`, where a mixed and an owned transaction
conflict — a mixed winner, and a mixed certificate agreeing with the
recovery across routes), `UnlockElection` (a full unlock certificate
beside frozen validators, with the move rule and the freeze rule each
shown needed), `FiveLiveness` (the `5f + 1` voting rule, including a
freeze-written `⊥` with no conflict in sight), `FiveRoutes` (the anchor
route reads the universe and is class-gated) and `LiteralThreshold`
(finding 19's constant, at `n = 7`). `Termination` carries the late
candidate — in the global order, its object released below, and
`releasedDrop` the only route to a verdict — and RS11's hypotheses on
an uncontested run, on a contested one, and on one where the rival is
seen only at the anchor: the run that separates RS11's local no-rival
premise from RS4's global one.

## 3. Findings for the paper

Recorded at Phase 0 from the reading and updated as the mechanisation
confirmed, refined, or added to them; findings 16, 18–21, 29 and 34 are the
mechanisation's own.

1. **Stale schema in the proofs.** Lemma univalent-exclusive and the
   Preliminaries refer to `noacks`/`nacks`/`unlocks` fields; the
   algorithms use `b.Stance`. Lemma finalize-safety uses
   `committedTX`/`droppedTX`; the algorithm has
   `fastCommittedTX`/`skippedTX`. Theorem commit-safety names
   `TryDirectDecide`, `TryIndirectDecide`, `ResolveOnCommitTX`.
   *Mostly fixed by the 2026-09-01 revision* (the offending lemmas were
   rewritten or commented out); one new instance appeared — the
   Preliminaries' consensus-projection sentence lists the opaque fields
   as `txs`, `nacks`, `unlocks`, where the schema is `Stance`.
2. **Routes count blocks, not authors.** `TryFastDecideTX` and
   `TrySkipDecideObj` test `|{b ∈ B : …}| ≥ 2f + 1`; the prose says
   "from distinct validators". Byzantine twins inflate a block count.
   The arc counts authors. The 2026-09-01 revision adds sites: the
   rewritten `Spendable` counts blocks, and Theorem three-safety says a
   "certificate-carrying block is correct" — authors are correct,
   blocks are not.
3. **"Earlier anchor" by `Link`.** `Dead` and `Spendable` test an
   earlier anchor by `Link(A, b)`; the proofs reason by commit order and
   local state. The two agree only if earlier anchors lie in later
   anchors' histories — true of Mysticeti, stated nowhere (D4). The
   2026-09-01 revision formalised (C1)–(C4) with Mysticeti citations
   and still omits chaining — the natural place for it.
4. **Fast commit and the unlock certificate.** The lemma's title says
   "while an unlock certificate exists"; its proof covers rounds `≤ r`,
   and the round-counting is not the reason: a correct validator at `⊥`
   never returns to `tx`. The `> r` half holds by a different argument
   (the certificate is visible from `r + 1` on, so ACKers keep their
   ACK and at most `2f` validators can retract). *Addressed by the
   2026-09-01 revision*: the new Lemma fast-excludes-unlock covers both
   halves with exactly this argument — but its second half thereby
   consumes the voting rule, not the stance automaton; see finding 22.
5. **Case 3 of conflict resolution.** The lemma claims an unlock
   certificate forms at `r + 2`. With `f + 1` correct ACKers and
   Byzantine ACKs shown to one of them, that validator certifies and
   keeps, the others retract, and no `2f + 1` retractions exist. What
   holds, and what RS5 states, is the disjunction: an ack certificate
   in every synchronised `r + 2` block's history, or an unlock
   certificate at `r + 2`. *Resolved by the 2026-09-01 revision*: the
   rewritten Lemma equiv-live drops the claim and its two cases match
   RS5's trichotomy (the keep case resolves through the certificate at
   the anchor, the no-keep case through the unlock certificate, with
   the all-skip fast special case); two nits remain under finding 23.
6. **Certificate propagation.** The proof's "a correct validator's block
   fails to link its own block" is not the argument; the induction on
   rounds with quorum intersection over authors and non-equivocation of
   correct validators is.
7. **(C5) is undefined.** Lemma recovery-termination and Theorem
   latency-5f assume it; only (C1)–(C4) exist — now formalised with
   Mysticeti citations by the 2026-09-01 revision, which also makes
   (C5) central to the `3f + 1` analysis: the rewritten Lemma
   equiv-live invokes it twice with an implicit "a committed anchor
   contains a given block within `κ` rounds" meaning. See finding 23.
8. **Half certificate versus refutation of `⊥`.** Lemmas
   unlock-excludes-half and full-excludes-unlock say a correct validator
   leaves `⊥` only on a half certificate; the algorithm's `Movable` uses
   a refutation of `⊥` — `2f + 1` non-`⊥` stances, possibly split across
   transactions. The counting closes either way; the text describes an
   older algorithm. RS6 takes the algorithm's form (confirmed by the
   mechanisation: `U6Ref`'s refutation of `⊥` is split two rival ACKs
   against two, and neither rival reaches a half certificate).
9. **Theorem safety-5f cites the wrong lemma.** "A full unlock
   certificate before `A` would have made `W` empty by Lemma
   full-excludes-unlock" needs unlock-excludes-half: permanent `⊥`
   holders leave at most `2f` frozen stances at any transaction.
10. **Skip certificates are per object.** Lemma univalent-exclusive and
    Lemma cross-route are stated "for the same `tx`".
11. **Shared-only transactions.** §7 says a valid inclusion of a
    shared-only transaction is a vote; the `Candidates` comment says
    `Valid` rejects a transaction with no owned input.
12. **Equivocation clause.** Any common round in the `3f + 1` predicate
    file; the latest declaring round in §8 and the §7 prose (D7).
13. **`Adopt` no longer links the transaction** at `5f + 1`; the
    recovery-safety step "a frozen stance `tx` places `tx` in `A`'s
    history" rests on the phase-3 guard `tx ∈ Candidates(b, o)`.
14. **`n = 5f + 1` exactly.** With thresholds `n − f` and `2f + 1` the
    section generalises to `n ≥ 5f + 1` (D1); the subsection titles'
    `n > 5f + 1` and `n > 3f + 1` are then literal.
15. **Hygiene.** §5 cites `sec:fastunlock`, `sec:fastfinality`,
    `lem:ackuniqueness`, `lem:fullcertuniqueness`, none defined;
    `3.RelatedWork.tex` and `9.parallelCertification .tex` are empty.
    The 2026-09-01 revision adds: a `\ref{def:AtomicBroadcast}` whose
    label is now `def:cab`; `IsFullUnlockCertTX` in Lemma
    full-excludes-unlock where the algorithm defines `…Obj`; a
    redundant `decidedObj` guard in `ResolveOnCommitObj`; "inlcudes"
    and a leftover `\fatima` note in the proofs.
16. **Tightness has a side condition.** "Moreover, this threshold is
    tight" holds for `f ≤ C ≤ n` only: for `C > n` no certificate can
    form and `R = 0` suffices; for `C < f` the threshold `n + f − C + 1`
    exceeds `n` and cannot be met. RS1's `Tight` carries the condition
    (confirmed by the mechanisation: both sides are refuted by witnesses).
17. **The self-parent chain is an assumption the model never states.**
    The proofs use that a correct validator's blocks form a chain ("as it
    links its own block in every round"); the Preliminaries do not say
    so. It is indispensable, not convenient: without it a correct
    validator's earlier ACK can lie outside its later block's history,
    and the ack-versus-skip argument ("a skip voter never ACKed") does
    not close. The arc states it as `Universe.self_parent`, from which
    every correct validator has a block at every round below its own.
18. **The uncontested-liveness premise counts invalid rivals, and
    globally.** Lemma fp-liveness assumes "no conflicting transaction";
    RS4 transcribes it as no conflicting transaction *included anywhere
    in the universe*, which an included invalid rival voids (witnessed)
    although the algorithm and the conclusion are untouched, and which a
    rival first included far above the decision round voids too. The
    premise should read: no *valid* conflicting transaction included
    before certification.
19. **The `5f + 1` certificate-safety lemmas need only `3f + 1`.**
    Lemmas single-stance-5f through full-cert-unique close at any
    committee `n ≥ 3f + 1`: the persisting core of a full certificate
    has `n − 2f` correct members, the rest of the committee cannot fill
    a refutation (`2f < 2f + 1`) nor a rival quorum (`2f < n − f`), and
    no step uses `n ≥ 5f + 1`. RS6 is stated and proved without the
    `Five` mixin. The wide committee provides *exposure* — a quorum of
    votes always leaves the refutation reachable (§10's corollary,
    RS1's `ExposureAtQuorum`) — that is, the liveness of revocation,
    not its safety; the paper could say so. The parameterisation
    matters: with the literal `4f + 1` threshold the lemmas fail
    for `n ≥ 5f + 2` — the correct core is `3f + 1` and the remaining
    `n − 3f − 1 ≥ 2f + 1` validators fill a refutation — so the paper's
    fixed threshold carries a hidden *upper* bound on `n` that D1's
    `quorum = n − f` removes (compare finding 14). Witnessed at
    `n = 7`, `f = 1` (`ULit`): five ACKs certify at the literal
    threshold, and one round above, three anti-votes — two correct
    `⊥` holders and the Byzantine ACKer turned — refute the ACK, with no
    correct validator having moved.
20. **The recovery layer is where `5f + 1` is indispensable.**
    Complementing finding 19: Lemma recovery-reflects and claim 1 of
    recovery-safety consume the bound — the frozen set omits at most
    `f` validators, so `|F ∩ S| ≥ 2f + 1` needs `|F| ≥ 4f + 1`, hence
    `n ≥ 5f + 1`. Claim 2 does not: an eligible transaction's `2f + 1`
    frozen supporters contain `f + 1` permanently correct ones at any
    committee. RS7 takes `Five` as a hypothesis exactly where it is
    consumed; RS8 inherits it through the reflection claim alone.
21. **Lemma recovery-reflects holds without its candidacy premise, at
    any round.** The paper assumes `tx ∈ Candidates(A, o^j)`;
    mechanised, candidacy is *derived*: a frozen correct supporter's
    marker block declares the ACK, the `Adopt` guard makes the
    transaction a candidate of the marker block, and inclusion travels
    into the resolving anchor's history. The strengthened form also
    relates the certificate's round to the resolution not at all, which
    closes Theorem safety-5f's cross-route cases — including the step
    finding 9 flags — with no case analysis on rounds.
22. **The revised fast-commit/unlock exclusion is not a pure-safety
    lemma** (2026-09-01 revision). Lemma fast-excludes-unlock's
    "after round `r`" half argues `CertVisible` → "will not vote `⊥`" —
    the keep branch of `CastVotes`, i.e. the honest *voting rule*.
    Under the stance automaton alone the unconditional claim is false,
    and the arc's committed witness refutes it: `UCert` carries a fast
    quorum of certificates at round 2, an unlock certificate at round
    5, and satisfies `StanceDiscipline`. Since Lemma
    three-anchor-safety cites the unconditional form, the revised
    `3f + 1` safety theorem silently consumes honest voting behaviour.
    The dependence is avoidable: RS3 proves the same agreement from the
    automaton alone, resolving the bivalent case at the anchor with the
    round-conditioned exclusion (RS2). Either state the voting-rule
    hypothesis on the lemma, or revert to the round-conditioned form
    plus the anchor argument.
23. **(C5) once names a synchrony fact** (2026-09-01 revision). In the
    rewritten Lemma equiv-live, "by (C5), every correct round-`(r+2)`
    block sees all `2f + 1` of these votes" is Lemma round-sync's
    synchrony, not a consensus property; the lemma's other (C5) use and
    those of recovery-termination and latency-5f need the definition
    finding 7 asks for.
24. **Small revision nits.** "restract" in Lemma equiv-live; the new
    Conditional Atomic Broadcast definition is a top-level
    specification with no stated reduction from the protocol's results
    (the arc's RS3/RS8 give Conflict safety and RS4 Honest Liveness;
    no reduction is mechanised either — recorded out of scope).
25. **Theorem three-safety's totality clause is a liveness claim**
    (2026-09-01 revision). "All correct validators *eventually agree on
    one of the following outcomes*" rests on eventual observation and
    (C4)/(C5); the theorem's second sentence is RS3 exactly, but no
    mechanised result — and no pure-safety argument — yields the
    eventual-outcome half, which RS4/RS5 deliver only under the voting
    rule and synchrony. Flag the clause as liveness or drop it from the
    safety statement.
26. **Mixed transactions at `5f + 1`** (retired by the 2026-09-10
    revision). The earlier predicates carried `IsOwned` down to the fast
    vote while nothing consumed a fully certified mixed transaction;
    the paper now lets owned and mixed transactions compete on their
    owned input and finalises a certified mixed one at a committed
    anchor (`FinalizeOnCommitTX`). The arc follows — `mixedFinal`, and
    every recovery definition over `Candidates` as the paper has it —
    and `UMixSix` now witnesses the route firing at an anchor above the
    certificate and at no anchor below it.
27. **Several hypotheses in the paper's lemmas are dead, mechanically.**
    The arc-wide audit re-proved and restated: the `3f + 1` liveness
    pair consumes the voting rule only — the stance automaton is not
    used by fp-liveness or the trichotomy; the mixed-object corollary
    consumes no behavioural hypothesis at all; and the `5f + 1`
    election claims hold at a bare marker quorum — recovery-reflects
    and recovery-safety need no trigger, no one-shot, and (for the
    winner claim) no move rule and no resolution whatsoever. The
    paper's proofs could say so; the arc's statements now do.
28. **Two protocol-independent readings of §10, both favourable.** The
    arc's `Exposes` lets a both-ways Byzantine voter count on both
    sides (the paper partitions votes), making the mechanised
    sufficiency direction weaker and necessity stronger — a consumer
    counting one vote per validator recovers the paper's form; and the
    arc's revocation threshold aggregates opposing votes across all
    rivals where Theorem vote-revocation names a single `x′` — strictly
    stronger, and the form the `5f + 1` split refutation needs. Also:
    RS5's anchor resolution is stated at a *correct-authored* committed
    anchor (its proof walks the anchor's own chain); the paper's lemma
    does not say so, though the formalised (C4) makes such anchors the
    ones consensus guarantees.
29. **The second clause of recovery-reflects needs no `5f + 1`**
    (2026-09-10 revision). "A full unlock certificate makes `W` empty"
    closes at any committee `n ≥ 3f + 1` under the move and freeze
    rules: the certificate's correct `⊥` core and an eligible
    transaction's correct frozen supporters must share a validator, whose
    marker would declare both. Each rule is needed — a witness per rule
    has the certificate and an eligible transaction side by side. Only
    the first clause consumes the wide committee (finding 20).
30. **Theorem safety-5f's recovery case argues from one validator's
    state** (2026-09-10 revision). "Suppose `ResolveOnCommitObj`
    finalizes `tx` at `A`" excludes an earlier drop by the local guard
    `win ∉ skippedTX`; that another validator released the object
    through `TryFullUnlockObj` is excluded nowhere. The new second
    clause of recovery-reflects is the missing citation (RS8 closes the
    pair with it).
31. **The short algorithms are not the full ones.** The body's
    simplified listings define the `3f + 1` certificate without the
    block's own ACK, cast `⊥` without the conflict gate, commit at an
    anchor with no `Dead` or recovery guard, and still call the `5f + 1`
    candidates "owned". The arc mechanises the full algorithms of the
    appendix; the body should say the listings are sketches.
32. **Status against the 2026-09-21 paper.** Resolved: 5 (the corrected
    trichotomy is what the rewritten lemma argues), 9 (the citation now
    names recovery-reflects, but see 30), 25 ("eventually" removed).
    Half resolved: 7 and 23 — (C5) is defined, and Lemma equiv-live
    still uses it once for a synchrony fact, with an undefined `κ`; 8 —
    the proofs speak of refutations, §8's prose and the short §4 still
    of half certificates, and Lemma full-excludes-unlock's proof mixes
    the two; 2, 3, 17 — now stated before the proofs, not in the
    Preliminaries. Open: 1 (the consensus-projection sentence still
    lists `nacks`, `unlocks`), 12, 16, 18, 22 (the lemma is now
    explicitly unconditional, the voting rule named only in its proof).
33. **Per-transaction termination failed for the `5f + 1` algorithm**
    (fixed in the paper, 2026-09-21, and mechanised as RS12). The only
    abort sites were `TryFullUnlockObj` and
    `ResolveOnCommitObj`, each over the candidates it sees at that one
    call and never again for the object, and `FinalizeOnCommitTX`'s
    first loop, which was gated by `IsMixed`. `TryFullDecideTX` only
    `continue`s on a decided object, where the `3f + 1` procedure
    records an abort. So when an owned transaction was finalized on a
    full certificate, its owned rivals — present from the start or
    included later, by a Byzantine block or by a correct validator not
    yet aware of the decision — are valid, lie under committed anchors,
    and are never decided: the Termination property of the paper's
    specification does not hold of them, and neither does the
    "eventually" half of Agreement, since a validator that instead
    reached the same winner through recovery does abort them. The paper
    claims termination per object only (Lemma recovery-termination,
    RS9b). The fix is one line: the first loop ranges over every
    candidate of the anchor, owned or mixed, as at `3f + 1`; the abort
    in `TryFullDecideTX` is not needed, since that branch is unreachable
    for a certified transaction. Witnessed on `U6RecFull`: the
    finalized transaction's owned rival is dropped once the certificate
    is observed or lies under the anchor, and has no verdict of either
    fate where neither holds (before the fix it had none at all).
34. **Termination at `3f + 1` needs (C4), not (C5).** The lemma's proof
    sends a certificate under a committed anchor by (C5); mechanised,
    the correct-authored anchor four rounds above the carrier suffices,
    because its own chain passes through a certificate, or through a
    block from which RS5 applies. The Lean (C5) would also have been
    stronger than the paper's, which speaks of honest blocks only.

## 4. Out of scope

- **Delivery, GST, timeouts.** Synchrony is rendered structurally as in
  Hydrozoan (`PopulatedOn`, `SynchronisedOn`); the arc grounds
  satisfiability, not operational realisability.
- **Object versioning and reuse** (D3); **multi-input transactions**
  (D2); **probabilities and the expected latency** (D8).
- **The consensus protocol itself.** Anchors are given (D4); deriving
  them from the core's Mysticeti is a possible grounding phase.
- **The probabilistic and timing remainder of §4's liveness.** Lemma
  coin-success is mechanised as its deterministic core plus the
  cardinality of the good-target set (RS9a): under a uniform draw the
  bound `half / n` is the stated numerator over the committee, and
  `CoinMeasurable` fixes the good set before a post-round draw; the
  division, independence across attempts, the geometric expectation,
  and Theorem latency-5f's round bookkeeping stay on paper. Lemma
  reuse-5f lives on `Spendable`, dropped by D3, and so does the new
  mixed disjunct of `Spendable`.
- **Timing of the first loop's aborts.** The relation renders the loop
  up to one anchor, in both directions: the validator's loop runs before
  the routes of the same anchor, so it aborts at the next anchor what
  the relation drops at this one; and at `3f + 1` the relation drops a
  late candidate at an anchor that holds the deciding evidence, possibly
  later than a validator that observed it consensuslessly. And the lemmas of the 2026-09-10 revision that read
  local state or execution: decision integrity (the verdict relations
  are functional by RS3 and RS8) and consistent execution.
- **Execution, reverts, epoch change**, and the paper's §5 liveness
  claim for shared objects.

## 5. Layout and discipline

The arc adopts the statement/proof partition of the Hydrozoan arc
(`hydrozoan.md` §10) and is in `ARCS` of `scripts/check-arc-holes.py`.

```
LeanDag/RedSnapper/
  Model/         definitions only — no theorem and no proof term:
                 Faults, Revocation (§10), Block, Universe, View,
                 CausalHistory, Transaction, Stance, Votes, Certificates,
                 Anchors, Dead, Verdict, Liveness, HonestVoting, Five/…
  Helpers/       lemma and construction infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ only; `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
LeanDagTest/RedSnapper/  witness models; audited
```

Results: `Revocation` (RS1), `CertificateExclusion` (RS2),
`TxAgreement` (RS3), `Uncontested` (RS4), `ConflictResolution` (RS5),
`Five/FullCertSafety` (RS6), `Five/RecoverySafety` (RS7),
`Five/Agreement` (RS8), `Five/CoinSuccess` and
`Five/RecoveryTermination` (RS9).

**The freeze protocol.** For each phase, the audit surface — `Model/`
definitions, `Statement.lean`, witness instantiations — is written
first, in its own files, reviewed, and frozen on the author's go; proofs
are then written until they verify, with a cold-context reviewing agent
over the frozen files and the witnesses in parallel, hunting vacuous
claims and missing witnesses; its findings are relayed, fixes to frozen
files need the go again, and the phase is committed green.
Human-readable and machine-checked content never share a file.

Three frozen statements were amended after their freeze, each proposed
with its reason and applied on the author's explicit go, and each now
pinned by a hardening witness: RS4's no-rival premise gained the
validity gate (finding 18); `ResolvesFiveAt`'s one-shot clause was
widened from strictly-between to every earlier committed anchor, the
paper's exact form; and `CoinRule`'s adopt clauses moved the target's
read from the constrained block — circular, hence vacuous, on the
target's own block — to the target's referenced round-parent, the
algorithm's pre-write read (the Phase 9 audit compiled a universe where
the original form holds and the concentrated coin lemma is false).
The arc-wide audit then amended five frozen statements once more, on
the author's go, dropping hypotheses their proofs never used: the
liveness pair and the trichotomy lost `StanceDiscipline`, the mixed
corollary moved outside the discipline arrow, the three RS7 election
claims lost the resolution apparatus (and the winner claim the move
rule), and `ResolutionExists` lost a derivable index bound — each drop
a strictly stronger theorem, recorded as finding 27.

**Checker scope.** `check-arc-holes.py` bars `theorem`/`lemma`/
`example` from `Model/` and additionally `instance` from
`Statement.lean`; Model-file instances are permitted repo-wide (other
arcs carry `inferInstanceAs` decidability instances), so a
tactic-proved instance in a Model file would pass the checker — the arc
keeps its Model files instance-free, and the axioms tripwire backstops
every headline.

**Relation to the core.** None consumed: the arc carries its own fault
model, blocks, universe and reachability, so that its trusted core is
exactly the paper's model. The modelling style is the core's (a
structural block universe, `Finset` counting discharged by `omega`).
