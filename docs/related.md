# Related work: consensus on uncertified DAGs

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.
> In particular, the paper summaries in this survey may contain errors
> of reading; verify claims against the cited sources before relying on
> them.

**Scope.** This document surveys the protocols that share Mysticeti's central
structural commitment — an *uncertified* DAG, in which no certificate is ever
constructed or transmitted, and certification is instead a property of the graph
recovered by the reader. It is organised around a single question: for each
protocol, what does it re-use from the uncertified-DAG structure, and where does
it depart from Mysticeti?

Certified protocols (Narwhal/Bullshark, Sailfish, Shoal++) appear only in §5, as
contrast points that fix what "uncertified" is defined against, and the
mechanised-verification literature appears in §6, since it bears directly on the
present development.

*Survey compiled 2026-08-05 from published abstracts and papers. Claims below are
attributed to the cited work; where a detail could not be confirmed against the
paper text it is marked* (unconfirmed).

*Sections 8 and 9 compare the two most closely related works against the Lean
development directly. The changes they called for have been made to
`report.md`; what remains here is the comparison itself, and the open
questions §8.3 and §9.5 record.*

---

## 1. The distinction

In a **certified** DAG, a block is disseminated by reliable broadcast and enters
the DAG only once it carries a quorum of signatures. Every block therefore costs
three message steps — propose, acknowledge, certify — and the reader may assume
that any block it sees is non-equivocated and available, because the certificate
proves it.

In an **uncertified** DAG, a block is disseminated by a single broadcast and
enters the DAG immediately. There is no certificate message and no certificate
round. A block two rounds above a leader constitutes a certificate for that
leader precisely when its own references happen to contain a quorum of blocks
that reference the leader. Certification becomes a *pattern in the graph*,
discovered by each reader independently, rather than an artefact produced by a
writer.

Three consequences organise the entire literature below:

1. **Latency falls** by at least one round-trip, since the certification steps
   disappear from the critical path (Mysticeti, §3; Bluestreak, §4.4).
2. **Equivocation becomes the reader's problem.** Nothing structurally prevents a
   Byzantine validator from broadcasting two blocks for one slot, so the commit
   rule must be safe in the presence of equivocation rather than being protected
   from it.
3. **Liveness becomes delicate.** With no certificate to prove availability, a
   validator may reference a block it cannot supply, and correct validators may
   fail to converge on a common view. This is the sore point of the family, and
   the subject of §4.3.

The third consequence is the one this repository's development speaks to
directly; see §7.

---

## 2. Ancestors

### 2.1 Hashgraph

> L. Baird. *The Swirlds Hashgraph Consensus Algorithm: Fair, Fast, Byzantine
> Fault Tolerance.* Swirlds Tech Report SWIRLDS-TR-2016-01, 2016.
> L. Baird and A. Luykx. *The Hashgraph Protocol: Efficient Asynchronous BFT for
> High-Throughput Distributed Ledgers.* IEEE COINS, 2020.

The original uncertified construction. Validators gossip *about gossip*: each
event records the hashes of the two events it descends from, and the resulting
graph is interpreted locally by "virtual voting" — every validator computes what
every other validator *would have voted*, from graph structure alone, with no
vote messages exchanged.

**Re-uses:** the defining idea that consensus can be read off an unauthenticated
graph without any explicit voting or certification round. Mysticeti's own
framing acknowledges this lineage.

**Differs from Mysticeti:**
- *Randomised and fully asynchronous*, rather than partially synchronous with a
  deterministic commit rule. Hashgraph terminates with probability 1 using a coin
  round; Mysticeti's commit rule is deterministic and its liveness rests on
  partial synchrony.
- *Unstructured gossip graph* rather than a round-indexed DAG with a quorum
  reference rule. There are no rounds, so there is no notion of "a block at round
  r references 2f+1 blocks at round r-1" — which is precisely the invariant the
  present development builds on.
- *Latency is not the design objective*; virtual voting over famous witnesses
  costs many more effective rounds than Mysticeti's three.

### 2.2 Blockmania

> G. Danezis and D. Hrycyszyn. *Blockmania: from Block DAGs to Consensus.*
> arXiv:1809.01620, 2018.

Nodes emit blocks referencing prior blocks, forming a block DAG that each node
interprets separately to derive consensus. Blockmania shows that the message
pattern of PBFT can be *emulated* by interpreting a DAG, reducing communication
from O(N⁴) to O(N²) with small constants.

**Re-uses:** the "interpret the graph locally" discipline, and the insight that
the DAG can carry the consensus messages implicitly rather than as distinct
protocol messages.

**Differs from Mysticeti:**
- *Emulates a specific PBFT-style state machine* over the DAG, whereas Mysticeti
  defines a commit rule natively in terms of reference counting.
- *Leaderless* in its published form; Mysticeti assigns leader slots per round
  and commits leaders.
- Predates the round/wave discipline and the 3-round latency lower-bound framing.

### 2.3 Cordial Miners — the direct predecessor

> I. Keidar, O. Naor, O. Poupko, E. Shapiro. *Cordial Miners: Fast and Efficient
> Consensus for Every Eventuality.* DISC 2023, LIPIcs vol. 281.
> arXiv:2205.09174.

The most important ancestor. Cordial Miners forgoes reliable broadcast as a
building block and uses the **blocklace** — a partially-ordered counterpart of
the blockchain — to implement all three components of consensus: dissemination,
equivocation-exclusion, and ordering. It achieves optimal good-case message
complexity O(n) and roughly halves the latency of certified DAG protocols. It
comes in two instances, one for asynchrony and one for eventual synchrony.

**Re-uses:** essentially everything Mysticeti later builds on — no reliable
broadcast, no certificates, equivocation handled by graph inspection rather than
prevented by construction.

**Differs from Mysticeti:**
- *Disjoint 3-round waves with one leader in the first round of each wave.*
  Mysticeti's contribution over this is precisely to remove the wave structure:
  it assigns leader slots in *every* round and pipelines the commit rule, so that
  every block can be committed without waiting for a wave boundary. This is the
  source of Mysticeti's 3-message-round optimum.
- *Explicit equivocation-exclusion machinery* over the blocklace; Mysticeti
  instead makes the commit rule itself safe under equivocation.
- Cordial Miners' asynchronous instance uses randomisation; Mysticeti-C is
  deterministic under partial synchrony.

---

## 3. The reference point

### 3.1 Mysticeti

> K. Babel, A. Chursin, G. Danezis, A. Kichidis, L. Kokoris-Kogias, A. Koshy,
> A. Sonnino, M. Tian. *Mysticeti: Reaching the Limits of Latency with
> Uncertified DAGs.* NDSS 2025. arXiv:2310.14821.

Mysticeti-C is the first DAG-based Byzantine consensus protocol to reach the
latency lower bound of three message rounds. It achieves this by (i) forgoing
explicit certification, so a block costs one broadcast, and (ii) a commit rule
under which every block carries a leader slot and can be committed without
delay — no wave boundaries. Mysticeti-FPC weaves a fast path for owned-object
transactions into the same DAG rather than running it as a separate protocol.
Reported: 0.5s WAN commit latency at >200k TPS; deployed on Sui with a >4×
latency reduction.

This is the design the present formalisation targets. The commit rule — direct
commit, direct skip, and the indirect rule that resolves undecided slots from
later certificates — is the object of `LeanDag/Mysticeti.lean`.

---

## 4. Protocols that re-use the uncertified DAG

### 4.1 Mahi-Mahi

> P. Jovanovic, L. Kokoris-Kogias, B. Kumara, A. Sonnino, P. Tennage,
> I. Zablotchi. *Mahi-Mahi: Low-Latency Asynchronous BFT DAG-Based Consensus.*
> arXiv:2410.08670, 2024. (IEEE, 2025.)

The asynchronous sibling, from substantially the same group. It keeps the
uncertified structured DAG — explicitly to forgo certification, cutting both
message count and the CPU cost of certificate verification — and pairs it with a
commit rule that commits **multiple leader blocks in each DAG round**.

**Differs from Mysticeti:**
- *Asynchronous rather than partially synchronous.* Mahi-Mahi is designed to make
  progress against a continuously active asynchronous adversary; Mysticeti-C's
  liveness argument requires partial synchrony. This is the single largest
  difference and the reason the commit rule must change.
- *Longer waves, votes through the cone.* The rule is Mysticeti's with the wave
  stretched to four or five rounds and a vote counted through the voting block's
  causal history (the first block of the slot met in a depth-first walk) rather
  than among its direct references; the thresholds are unchanged. Mysticeti
  commits on a fixed 3-round pattern.
- *Leaders revealed after the wave.* A common coin, reconstructed from the
  decision round's blocks, names the slots of a round only once the wave is
  built, so the adversary cannot aim its delivery schedule at the leader's block.

**Bearing on this development:** formalised as the `LeanDag/MahiMahi/` arc
(report §17; `mahi-mahi.md`). The rule is the core's generalised over the wave
length `w`, safe at every `w ≥ 3` and collapsing onto the core at `w = 3`. Its
liveness is stated with no synchrony hypothesis, under a single clause on the
pair (schedule, DAG) — the schedule keeps naming a validator whose block the
DAG directly committed — which is what the late-revealed leader amounts to on
a DAG; the coin is one mechanism that makes the clause true, and under
synchrony the clause is derived from the core's fairness. The counting behind
it is the core's own common-core lemma (T3c). Two points where the
mechanisation sharpens the paper: the paper's Lemma C.13 counts every
reference of the common core as committable, where an equivocating author's
block can be denied by splitting the voters, so the guaranteed count at five
rounds is `n − f − |byzantine|` (a `1/3` probability per wave, not `2/3`) and
the deterministic multi-leader threshold is `2f + 1` slots, not `f + 1`; and the
core's own skip rule, which blames per candidate, is weaker than the
implementation's, which blames the slot.

### 4.2 Odontoceti

> P. Vander Vos (supervised by P. Jovanovic and A. Sonnino). *Odontoceti:
> Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis,
> arXiv:2510.01216, 2025.

Builds an uncertified DAG with a novel decision rule, and is the first DAG
protocol to commit in **two** communication rounds rather than three.

**Differs from Mysticeti:**
- *Weakens the fault threshold to remove a round.* Odontoceti runs with n = 5f+1
  (≈20% fault tolerance) instead of n = 3f+1 (≈33%). The extra validators make a
  quorum intersection large enough that the vote and certificate rounds can be
  collapsed into one. This is a deliberate trade of security margin for latency,
  not a strictly better commit rule.
- *Includes a slow-participant optimisation* that advances progress under crash
  faults, argued to be the common case in practice.
- Reported 300ms median latency at 10k TPS.

**Bearing on this development: formalized.** A closer look corrected an
earlier note here: at `n = 5f+1`, Odontoceti's quorums — the DAG quorum
`4f+1` and both direct thresholds — **are** `n − f`, exactly the shape
`LeanDag` is parameterised at, so the entire DAG layer applies verbatim
and only the two-round rule layer is new. `LeanDag/Odontoceti/` proves
its safety and liveness (`odontoceti.md`), generalized to `n ≥ 5f+1`
with indirect threshold `n − 3f`, and surfaces four findings
(`odontoceti.md` §6). Chief among them: the thesis's agreement proof
(Lemma 5) silently relies on the implementation's candidate-iteration
order — two equivocating leader blocks can both pass the `2f+1`
indirect test at one anchor (`utwin6_both_pass`, realised on data) — so
the formalized rule commits the canonical least passing candidate,
which is what makes agreement a theorem. Also: a missing
commit-versus-indirect-rival lemma the safety proof needs, the
blocks-versus-authors ambiguity in the indirect test's count, and a
counting step in its Lemma 2 that holds only via the exact complement
identity.

### 4.3 Starfish — and the liveness critique of uncertified DAGs

> N. Polyanskii, S. Mueller, I. Vorobyev. *Making Uncertified DAG BFT Provably
> Live with Linear Payload and Quadratic Metadata Communication.*
> IACR ePrint 2025/567, 2025 (rev. 2026). Also circulated as *Starfish: A high
> throughput BFT protocol on uncertified DAG with linear amortized communication
> complexity.*

The most consequential paper for this repository. Starfish is a partially
synchronous uncertified DAG protocol that aims for "the security properties of
certified DAGs, the efficiency of uncertified approaches, and linear amortized
communication complexity."

The paper's diagnosis, in its own words: *"existing protocols lack rigorous
liveness proofs … The underlying vulnerability—validators advancing rounds
without creating blocks—is inherent to uncertified DAG protocols; Cordial
Miners, which originates the same round advancement mechanism, assumes
synchronization after GST without proof."* It states specifically that
Mysticeti's Lemma 8 and Cordial Miners' Proposition 38 both claim post-GST
validator synchronisation but leave gaps, and cites Qiu et al. (§6.1) for an
explicit counterexample.

#### The pacemaker conditions

Starfish's Table 3 governs three events; its own additions are A2, C3 and B2.

**Round advancement** (r−1 → r) requires *both*:
- **A1** — received 2f+1 blocks of round r−1;
- **A2** *(new)* — **created its own block in round r−1.** This is the fix. In
  the paper's words, it *"prevents validators from 'jumping' ahead without
  contributing blocks that serve as votes and certificates needed for leader
  commitment."*

**Block creation** at round r, on any one of:
- **C1** — received the round-(r−1) leader block (L1) *and* saw the round-(r−2)
  leader either collect 2f+1 votes or match a skip pattern (L2);
- **C2** — a timeout δ_TO = **2Δ** expired;
- **C3** *(new, "safe jump")* — received 2f+1 blocks of round **r** itself,
  enabling a lagging validator to catch up without waiting out the timeout.

**Broadcast** of the unknown causal history to each peer, on:
- **B1** — creating a block; or
- **B2** *(new)* — **advancing a round.** Called *"essential: it ensures that
  after GST, all honest validators advance rounds and create blocks within time
  Δ of each other."*

The argument for the fix: if a validator receives 2f+1 round-r blocks but C1 is
unsatisfied, then at least f+1 honest validators have already advanced past
round r, so C3 permits catching up immediately.

#### What they prove

- **Lemma 4 (Synchronicity after GST).** All honest validators enter any round
  r > r_max within time Δ of each other, and create their round-r blocks within
  Δ of each other. Sharpens to the actual delay δ when δ < Δ.
- **Lemma 5.** Any leader block created by an honest validator in round r ≥ r_max
  is marked TO-COMMIT by the direct decision rule.
- **Lemma 6.** After GST, any undecided leader block is eventually decided.

**Differs from Mysticeti:** adds A2/C3/B2 to the pacemaker, plus an encoded
dissemination layer (Reed–Solomon coding with data-availability guarantees
folded into DAG construction, giving O(Mn) payload at one extra round) and
**Starfish-C**, using threshold signatures and delayed dissemination for O(κn³)
worst-case and O(κn²) happy-case metadata. Retains the uncertified commit
structure throughout.

See §8 for the detailed comparison against this development.

### 4.3.1 Qiu, Xiao and Shao — the counterexample, mechanised

> L. Qiu, J. Xiao, Z. Shao. *Mechanized Safety and Liveness Proofs for the
> Mysticeti Consensus Protocol under the LiDO-DAG Framework.* IEEE S&P 2026,
> pp. 149–168. [PDF](https://flint.cs.yale.edu/flint/publications/sp26.pdf) ·
> [artifact](https://zenodo.org/records/17267594)

The source of Starfish's counterexample, and the closest prior art to this
repository by a wide margin. Rocq (Coq) proofs under the LiDO-DAG framework.

Their finding: *"liveness of Mysticeti is highly sensitive to the round-jumping
behavior of honest participants. If honest processes are allowed to jump over
rounds arbitrarily, then we present an explicit counterexample to the liveness
of Mysticeti: an infinite trace where no data blocks are ever committed."*
Safety, by contrast, is *"mostly insensitive to the details of round-jumping."*

**Their fix** is weaker — and therefore sharper — than Starfish's A2. They
introduce a *global catchup time* (GCT), analogous to GST and known to honest
parties, before which round-jumping is implementation-defined. After GCT:

> if an honest party jumps to round r, it must create a vertex in every round
> r′ < r, **unless it has already made a decision for the round r′ − 2**.

Full liveness guarantees hold after max{GST, GCT}. Leader vertices created
before GCT still cannot be skipped: at least f+1 honest processes create
certificates for them (`every_vert_certificate` in the artifact).

**They audited deployed code.** *"We found that current versions of Sui indeed
implemented round-jumping incorrectly, making them susceptible to liveness
attacks."* Mysten Labs acknowledged the issue. This makes the clause an
empirical fact about implementations, not only a modelling nicety.

**Differs from this development:** an operational model (traces, a transition
system, an explicit time model) in Rocq, versus the structural, execution-free
account here. See §8.

### 4.4 Bluestreak

> N. Polyanskii, I. Vorobyev, S. Mueller. *Bluestreak: Scaling DAG BFT by
> Sparsifying Metadata.* IACR ePrint 2026/898, May 2026.

A **sparse** uncertified DAG. The observation: dense round-based DAGs require
every block to reference ≥2f+1 blocks of the previous round, giving O(n) metadata
per block, O(n²) per round, and O(n³) metadata bytes transmitted per round under
all-to-all dissemination — so at large committee sizes *metadata*, not payload,
becomes the latency bottleneck.

**Differs from Mysticeti:**
- *Non-leader blocks are kept constant-size in n.* Committee-scale ancestry is
  concentrated into a single leader block per round, so average metadata per
  block stays constant as committees grow.
- This directly changes the reference structure that Mysticeti's commit rule
  counts over. The rule "a block references a quorum of the round below" — P1 and
  the quorum reference invariant in this development — no longer holds uniformly
  across all blocks.

**Bearing on this development:** the model here assumes every block references a
quorum below (report §2, P1). Bluestreak is the case where that assumption is
deliberately dropped for non-leader blocks, and is therefore the natural boundary
marker for the model's scope.

### 4.5 Lifefin

> J. Zhang et al. *Lifefin: Escaping Mempool Explosions in DAG-based BFT.*
> arXiv:2511.15936, 2025.

Not a new DAG protocol but a *generic overlay*, and it targets Mysticeti by name.
It identifies a liveness vulnerability in which an adversary triggers a **mempool
explosion**: during asynchrony, nodes maintain an ever-growing set of uncommitted
vertices, exhaust their resources, and can then no longer generate vertices
supporting the latest leader — so the protocol stalls. Lifefin uses Agreement on
Common Subset to commit transactions under bounded resource usage, and is
instantiated as **Sailfish-Lifefin** and **Mysticeti-Lifefin**.

**Differs from Mysticeti:** an add-on layer rather than a redesign; applies to
certified and uncertified DAGs alike.

**Bearing on this development:** the attack is resource-exhaustion driven and
therefore lies outside the model here, which has no notion of node resources and
no executions (report §1.4). Worth citing as an explicitly out-of-scope liveness
threat, so that the liveness claims are not read as stronger than they are.

---

## 5. Certified DAGs — what the family is defined against

Included only to fix the contrast; none of these re-use the uncertified
structure.

- **Narwhal & Tusk / Bullshark.** > G. Danezis, L. Kokoris-Kogias,
  A. Sonnino, A. Spiegelman. *Narwhal and Tusk.* EuroSys 2022. /
  A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias. *Bullshark: DAG
  BFT Protocols Made Practical.* CCS 2022, arXiv:2201.05677.
  The certified baseline: reliable broadcast per block, certificates in the DAG,
  leaders every other round. Mysticeti's latency claim is stated against these.

- **Sailfish.** > N. Shrestha, R. Shrothrium, A. Kate, K. Nayak. *Sailfish: Towards
  Improving the Latency of DAG-based BFT.* IEEE S&P 2025, ePrint 2024/472.
  Keeps certification (RBC) but supports **a leader vertex in every round**,
  committing a leader in one RBC round plus 1δ — roughly 25% below Bullshark.
  Instructive because Sailfish and Mysticeti reach for the same goal (a leader
  every round) from opposite sides: Sailfish keeps certificates and restructures
  leaders; Mysticeti drops certificates.

- **Shoal++.** > B. Arun, Z. Li, F. Suri-Payer, S. Das, A. Spiegelman
  (Aptos Labs / Cornell / UIUC). *Shoal++: High Throughput DAG BFT Can Be Fast
  and Robust!* NSDI 2025, arXiv:2405.20488.
  The explicit counter-argument to the uncertified thesis: it contends that
  *certification is not the root cause of high latency*, reaching 4.5 message
  delays on a certified DAG. It argues uncertified designs are less robust —
  under message drops Shoal++ latency rises at most 1.3×, whereas uncertified
  DAGs "experience sharp latency spikes as replicas perform critical-path
  synchronization on missing data," which is the availability problem of §1.
  Notably **hybrid**: it also commits anchors on observing 2f+1 *uncertified*
  proposals, so it re-uses the uncertified commit pattern as a fast path over a
  certified DAG.

---

## 6. Mechanised verification of DAG consensus

Directly relevant, since this repository is a Lean 4 development.

- **LiDO-DAG.** > *LiDO-DAG: A Framework for Verifying Safety and Liveness of
  DAG-Based Consensus Protocols.* Proc. ACM Program. Lang., 2025.
  doi:10.1145/3729306 (Yale FLINT).
  Coq. Applied to Narwhal, Bullshark and Sailfish, giving mechanised safety *and
  liveness* proofs — claimed as the first mechanised liveness proofs of any
  DAG-based protocol. All three targets are certified DAGs — but see the next
  entry, which extends the same framework to Mysticeti.

- **Qiu, Xiao and Shao (S&P 2026)** — mechanised safety *and* liveness for
  Mysticeti itself, in Rocq under LiDO-DAG. **This is the closest prior art to
  the present development and is treated in full at §4.3.1 and §8.**

- **Reusable Formal Verification of DAG-based Consensus Protocols.**
  > N. Bertrand, P. Ghorpade, S. Rubin, B. Scholz, P. Subotic. arXiv:2407.02167,
  2024; Springer, doi:10.1007/978-3-031-93706-4_9.
  TLA+ with TLAPS, over DAG-Rider, **Cordial Miners**, **Hashgraph**, eventually
  synchronous Bullshark, and an Aleph variant, with modular specifications
  separating DAG construction from ordering to enable proof reuse (≈half the
  effort). **Safety only — liveness is not covered.** The two uncertified targets
  make this the closest prior art; the modular construction/ordering split is
  also the same decomposition used here.

- **Formal Verification of Blockchain Nonforking in DAG-Based BFT Consensus with
  Dynamic Stake.** > arXiv:2504.16853, 2025.
  Nonforking under dynamic stake — orthogonal to the static-committee model here,
  but relevant if committee reconfiguration is ever added. (Proof assistant and
  authorship not confirmed in this pass.)

---

## 6.5 Chain quality and fairness

The chain-quality property originates with the Bitcoin backbone analysis
(Garay, Kiayias, Leonardos, EUROCRYPT 2015); order-fairness (Kelkar,
Zhang, Goldfeder, Juels, CRYPTO 2020) concerns transaction ordering and
is orthogonal. For DAG protocols, fairness claims go back to Hashgraph
(§2.1) and remain informal across the family. The present development's
chain-quality arc (`chain-quality.md`, `LeanDag/Quality/`) proves the
inclusion side mechanically: per-flush author coverage with no synchrony
assumption, individual inclusion within a schedule window once the DAG
is synchronous, and a counterexample separating the two.

## 7. Summary: where this development sits

| Protocol | Uncertified | Synchrony | Leader cadence | Commit depth | Fault bound |
|---|---|---|---|---|---|
| Hashgraph | yes | asynchronous | none (virtual voting) | — | 3f+1 |
| Blockmania | yes | partial | leaderless | PBFT-emulating | 3f+1 |
| Cordial Miners | yes | both instances | 1 per 3-round wave | 3 rounds | 3f+1 |
| **Mysticeti** | **yes** | **partial** | **every round** | **3 rounds** | **3f+1** |
| Mahi-Mahi | yes | asynchronous | multiple per round | 4 or 5 hops | 3f+1 |
| Odontoceti | yes | partial | every round | **2 rounds** | **5f+1** |
| Starfish | yes | partial | every round | 3 rounds | 3f+1 |
| Bluestreak | yes (sparse) | partial | every round | 3 rounds | 3f+1 |
| Sailfish | no | partial | every round | 1 RBC + 1δ | 3f+1 |
| Shoal++ | no (hybrid) | partial | every round | 4.5 delays | 3f+1 |

Three observations for the report.

1. **The uncertified family is converging on Mysticeti's shape** — leader every
   round, commit by reference counting — and varying one parameter at a time:
   the synchrony assumption (Mahi-Mahi), the fault threshold (Odontoceti), the
   reference density (Bluestreak), the dissemination layer (Starfish). This
   supports the claim that the commit rule formalised here is the family's
   common core, and suggests parameterising the Lean development over quorum
   threshold and certificate distance rather than fixing them.

2. **Liveness is the family's acknowledged weak point**, and it is contested
   ground: Starfish claims uncertified DAGs including Mysticeti lacked a rigorous
   liveness proof and admit post-GST desynchronisation; Shoal++ argues from the
   certified side that uncertified DAGs are less robust because availability is
   not guaranteed. The report's structural condition and its GST derivation land
   squarely in this dispute; report §7.5 engages with both by name.

3. **A mechanised liveness proof of Mysticeti already exists** — Qiu, Xiao and
   Shao (§4.3.1), in Rocq, at S&P 2026. Priority of mechanisation is therefore
   *not* available as a claim, and report §1.3 does not make it. What remains
   distinctive is the *form* of the account: theirs is an operational model with
   traces and an explicit time model; this development states liveness
   structurally, with no theorem mentioning time, and derives the structural
   condition from GST separately. That is a real and defensible difference, but
   it is a difference of method, not of first occupancy. See §8.

---

## 8. The pacemaker against the liveness assumptions here

This section compares Starfish's pacemaker (§4.3) and Qiu et al.'s round-jumping
rule (§4.3.1) against `LeanDag/Timing.lean`, `LeanDag/Liveness.lean` and the
trust boundary of report §4.

### 8.1 The correspondence

| Starfish | Qiu et al. | This development | Status here |
|---|---|---|---|
| A1: 2f+1 blocks of round r−1 | — | `Live.builds` + `DeliversQuorum` (P8) | assumed (protocol) |
| **A2: created own block of round r−1** | **after GCT, no jumping over r′ unless r′−2 decided** | `Live.builds`, giving L1 `Populated`; `Timing.blk` total for n ≤ N | **assumed (P8) — the clause the argument rests on** |
| C1: wait for leader + votes | — | not modelled — `waits` is a pure timeout | absent |
| C2: timeout δ_TO = **2Δ** | — | `Timing.waits` + backoff past `D + delay`; **= 2Δ** when D = Δ | derived |
| C3: safe jump on 2f+1 blocks of round r | the "unless decided" clause | `Timing.prompt`: `built v (n+1) ≤ max (built v n + timeout n) (latest n + delay)` | assumed (P9) |
| B1/B2: broadcast unknown history on create **and on advance** | — | `Timing.covers` + P7 (references everything held) | assumed (network + protocol) |
| **Lemma 4**: honest validators enter round r within Δ | — | `Timing.DriftFrom`, via `driftFrom_of_prompt` | **derived — but from an assumed base case** |
| Lemma 5: honest leader committed | their liveness theorem | `directCommit_of_correct_leader`, `decided_of_correct_leader` | derived |

### 8.2 The counterexample does not apply here — and that is the point

The Qiu et al. counterexample is an infinite trace in which honest processes jump
rounds and no leader is ever committed. It cannot be instantiated in this model,
because **P8 (`Live.builds` — a validator builds on holding a quorum) excludes
round-jumping outright**, and L1 ("no stall") turns that into the statement that
every correct validator has a block at *every* round up to the horizon. `Timing`
then takes this for granted: `blk : Validator → ℕ → BlockId` is total over
`n ≤ N`.

So the theorems here are not threatened by the counterexample. But the reason
they are not is exactly the clause the literature has now identified as the crux.
Report §4.1 originally listed P8 as

> | P8 | a validator has a genesis block, and builds on holding a quorum |

alongside nine other clauses, in the same register as "no block cites one author
twice". On the evidence of §4.3 and §4.3.1 it is not that kind of clause. It is
*the* clause on which liveness of the whole uncertified family turns; omitting it
makes liveness **false**, not merely unproven; and the deployed Sui implementation
did not satisfy it. Report §4.1 now promotes it accordingly, with both citations.

### 8.3 The condition here is stronger than either published fix

Worth stating precisely, because it bounds what can be claimed:

- **Qiu et al.** permit jumping over round r′ when a decision for r′−2 already
  exists — jumping is restricted, not forbidden, and only after GCT.
- **Starfish A2** requires a block only in the immediately preceding round.
- **Here**, `blk` is total: a correct validator has a block at every round ≤ N,
  with no exception clause and no analogue of GCT.

This is sound but strictly stronger, so it describes a protocol doing more work
than the minimal fix. Two consequences. First, no claim of *minimality* for the
condition is available. Second, there is a clear route to a sharper result:
weakening `Live.builds` to Qiu et al.'s "unless already decided" form, and
checking L1 and `Timing` survive, would put this development at the same strength
as the S&P 2026 result rather than above it.

### 8.4 Where the accounts genuinely differ

**The base case is assumed here and derived there.** `driftFrom_of_prompt` proves
drift is *preserved*, not established: `exists_synchronisedOn_of_backoff` takes

```lean
(hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D)
```

as a hypothesis, recorded honestly in the trust boundary as R4 ("round-`0` spread
at most `D₀`", deployment). Starfish's **Lemma 4** instead *derives* the
corresponding Δ-synchronisation for every round past r_max, and its condition
**B2** — broadcast on round advancement, not merely on block creation — is precisely
what supplies it. Note that B2 is vacuous in this model: advancement and
block creation coincide when `blk` is total, so B1 alone suffices, which is why
its absence here is not an error. But it does mean **R4 is avoidable**: adopting
a B2-style clause would let the round-0 spread assumption be discharged rather
than assumed, tightening §4.4's "derived, not assumed" claim at its one soft
point. Report §4.5 records this.

**The 2Δ agreement is a genuine corroboration.** Starfish independently fixes its
block-creation timeout at δ_TO = **2Δ**. Report §6.10/§7.1 derives a required wait
of `D₀ + Δ`, which is **2Δ** under a common broadcast start (D₀ ≤ Δ). Two
different routes — a protocol designer's choice there, a derived threshold here —
landing on the same constant. It is the kind of external check a formalisation
rarely gets, and report §6.10 now records it.

**Method.** Qiu et al. work operationally (traces, transition system, explicit
time) in Rocq; the account here is structural and execution-free, with time
confined to `Timing.lean` and no theorem above it mentioning a clock. The
comparison to draw is not who proved it first — they did — but that the
structural formulation isolates the time-dependence into a single file, which is
what makes the P8/A2 dependency visible as a *hypothesis of one theorem* rather
than as a clause buried in a transition relation.

---

## 9. Detailed review: Qiu, Xiao and Shao (S&P 2026)

> L. Qiu, J. Xiao, Z. Shao. *Mechanized Safety and Liveness Proofs for the
> Mysticeti Consensus Protocol under the LiDO-DAG Framework.* IEEE S&P 2026,
> pp. 149–168. Rocq (Coq); artifact evaluated Available / Functional /
> Reproduced.

Read in full. This is the paper closest to the present development, and the
comparison is worth making at the level of individual hypotheses.

### 9.1 What they did

Four contributions, in their own ordering: (1) an explicit counterexample to
Mysticeti's liveness; (2) a modification restoring it, compatible with existing
deployments; (3) a Rocq model of modified Mysticeti with machine-checked safety
and liveness, by refinement to LiDO-DAG; (4) an audit finding deployed Sui
susceptible.

The background is a dispute. Sailfish [16 in their numbering] had pointed out
flaws in Mysticeti's liveness proof but gave no counterexample, leaving three
possibilities open — proof gap, latency-only failure, or genuine liveness bug.
This paper settles it as the third.

### 9.2 The protocol they model versus the one modelled here

| | Qiu et al. | This development |
|---|---|---|
| Validators | 3f+1, 2f+1 honest | `Faults`: `n ≥ 3f+1`, ≤ f Byzantine — **generalises** (equal at `n = 3f+1`) |
| Reference rule | 2f+1 vertices of round r−1, distinct builders | P3 `ValidWrt.quorum` — **same** |
| Supporter | *first* leader-slot vertex in `preds` | plain `refs`-membership (`votesIn`) — **differs; see below** |
| Certificate | round r+2 vertex referencing 2f+1 distinct supporters | `Certifies` — **same** |
| **Direct commit** | **2f+1 certificates, distinct builders** | `DirectCommitIn`: `n−f ≤ (creatorsOf … certificatesIn).card` — **same** at `n = 3f+1` |
| Direct skip | 2f+1 round-(r+1) vertices, none supporting | `DirectSkipIn` — **same** |
| Indirect rule | earliest non-Skipped anchor at r′ ≥ r+3 | M4, anchor at ≥ r+3 — **same** |
| **Leader slots** | **every round**; view v = round r, 1-to-1 | **`Slots.spacing`: `slotRound k + 3 ≤ slotRound (k+1)`** — **differs** |
| Equivocation | Byzantine may equivocate; hash IDs distinguish vertices | P5 non-equivocation for correct only; `BlockId` distinct — same in effect |
| Availability | staging area; local DAG ⊆ global DAG (their Prop. 1, *assumed*) | P4 `BlockUniverse.complete` — same discipline, both assumed |
| Model shape | transition system, traces, segmented traces for pre/post-GST timers | structural; no executions (report §1.4) |

**Two divergences, both worth owning.**

*Supporter uniqueness is obtained differently.* Their Definition 1 makes `v′` a
supporter of `v` only when `v` is the **first** leader-slot vertex in `v′.preds`;
their Fig. 2(b) exists precisely to show this keeps support unique when the
leader equivocates. Our `votesIn` has no such tie-break — a vote for `L` is just
`L ∈ (U.block q).refs`, so on the face of it one block could vote for two
equivocating leader blocks. Uniqueness is recovered instead from **P2**
(`ValidWrt.distinct_creators`: no block cites one author twice), which is exactly
how M5′ is proved — the intersecting correct voter's single block would otherwise
reference two round-`r` blocks by one author. Report §5.4 already notes this is
P2's only use in the development.

The two mechanisms agree in effect, but they are not the same assumption. Their
Alg. 1 validity check requires 2f+1 *distinct builders* among the strong edges
and does **not** forbid additional references to an equivocating author's second
block; that permissiveness is why they need the tie-break. **P2 is therefore
strictly stronger than Mysticeti's validity rule**, and it is doing work that the
deployed protocol does with the supporter definition instead. This is defensible
— it is simpler, and the report is explicit that P2 is a protocol clause — but it
needs stating, because a reader checking this model against the real one will
find a validity condition that Mysticeti does not impose. Report §4.1 states it.

*The leader schedule.* Mysticeti's headline
optimisation — and the direct source of what this paper calls "significantly more
complex security proofs than previous protocols" — is a leader vertex in *every*
round, so that DAG rounds and logical views correspond one-to-one. Here,
`Slots.spacing` requires consecutive leader slots to be **at least three rounds
apart**.

Report §3.4 justifies this internally, and correctly: three rounds is what places
every later anchor at `≥ r+3`, which is the hypothesis of M4. But note what the
two uses of "r+3" are. In Mysticeti the r+3 bound constrains *which round may
serve as an anchor* while leaders continue to exist at every round; here it
constrains *where leader slots may be at all*. The formalised object is therefore
a **de-pipelined Mysticeti**: it has Mysticeti's uncertified DAG and Mysticeti's
commit rule, but Cordial-Miners-like leader spacing. Everything proved is true of
that object, and the safety development is unaffected — but the pipelining that
motivates Mysticeti is outside the model, and a reader coming from this paper
will notice at once. Report §1.4 now states this among the scope restrictions.

### 9.3 The counterexample, and exactly which hypothesis it falsifies

Their trace (§3.2, needing f ≥ 3, so n ≥ 10) maintains for every round r ≥ 3:

- between f+2 and f+3 honest processes create a vertex, which is both a supporter
  of the round-(r−1) leader and a certificate for the round-(r−2) leader;
- the remaining honest processes **jump over round r**, creating nothing;
- each Byzantine process creates two vertices — one supporter that is not a
  certificate, one that is neither.

Sets S(r) of size ≥ f+2 with |S(r) ∪ S(r+1)| ≤ f+3 rotate the participating
honest processes, so nobody is starved and partial synchrony is never violated.
The certificate count per round is at most f+3 ≤ 2f, so the 2f+1 threshold is
never reached, no round is ever directly committed, and since indirect commit
depends on direct commit, nothing commits at all.

**Where this meets the development here.** `certifies_of_synchronisedOn`
(`Liveness.lean:447`) is precisely Mysticeti's Lemma 10 — the lemma Sailfish
attacked and this paper refutes. It is a theorem here, and the reason is visible
in its statement: it takes

```lean
(hpop1 : PopulatedOn U T (r + 1))   (hpop2 : PopulatedOn U T (r + 2))
```

as hypotheses — *every* validator in `T` has a block at rounds r+1 and r+2. The
counterexample is exactly a countermodel to that: in their trace only f+2…f+3 of
the 2f+1 honest processes have a vertex in any given round.

So the counterexample **does not refute L4, and does not refute any theorem in
this repository.** It refutes the *availability* of L4's hypothesis under
Mysticeti as published. Formally it is a countermodel to `Populated`, hence to
L1, hence to **P8 `Live.builds`** — the clause stating that a correct validator
holding a quorum at round r *has* a block at round r+1. That clause is what
forbids round-jumping, and it is imported, not derived.

This is the cleanest statement of the relationship, and report §6.6 makes it:
*the liveness results here are conditional on a protocol clause that the S&P 2026
paper proves is necessary and shows deployed Mysticeti lacked.*

### 9.4 Their fix versus the clause here

Their Algorithm 4, replacing lines 15–18 of the original:

> After GCT, if an honest party jumps to round r, it must create a vertex in
> every round r′ < r, **unless it has already made a decision for round r′ − 2**.

Two engineering features worth noting, both absent from the all-or-nothing
version here. First, **GCT** — a global catchup time analogous to GST, before which
the rule need not hold — makes the fix a drop-in upgrade for running deployments;
full liveness holds after max{GST+Δ, GCT}. Second, the **"unless decided"**
escape means a validator that has already decided round r′−2 need not backfill
r′, so a lagging validator does not have to manufacture an unbounded burst of
vertices. Their Theorem 5 closes that concern: with all processes honest, after
GST+6Δ every new vertex is a certificate, so a jumping validator has already seen
2f+1 certificates for every round ≤ r−2 and creates just one vertex.

`Live.builds` has neither refinement: it demands a block at every round
unconditionally and from the start. Sound, and simpler, but strictly stronger,
and it forecloses any minimality claim (§8.3).

### 9.5 "Weak liveness" — a result absent here

Their **Theorem 3** holds *without* the round-jumping fix: after GST+Δ, every
leader vertex created by an honest process gets at least f+1 certificates from
honest processes. Consequently every vertex at round ≥ r+3 indirectly references
a certificate of `Lr`, so `Lr` can never be indirectly *skipped* — the adversary
can withhold commitment but cannot force a skip.

**How they get it, since the reference rule does not give it.** A round-(r+1)
block must cite 2f+1 of 3f+1 distinct round-`r` authors, so it may legally omit
the leader; nothing structural forces `Lr` into anyone's references. The
guarantee comes from two other places.

*Their Lemma 4.* If no honest process has ever timed out in round R, then every
round-R vertex built by an honest process supports a leader vertex of round R−1
and certifies a leader vertex of round R−2. This rests on the **Predecessor
Rule** (Alg. 3 line 19) — when creating a vertex, a process must "try its best"
to make it a supporter and a certificate — and is proved by induction over the
trace: a process creating its vertex via the jump condition sees 2f+1 round-R
vertices, of which ≥ f+1 are honest and, by the induction hypothesis, already
support and certify; the predecessor rule then carries the property to the new
vertex.

*The dilemma.* After GST, `Lr` reaches every honest process within Δ, and the
2Δ timer guarantees none has timed out in round r+1 yet. So within another Δ,
each honest process either

- **creates a supporter for `Lr`** — obliged by the predecessor rule; or
- **jumps over round r+1** — but jumping is not silent. To jump, it must observe
  2f+1 vertices in round r+2, and by Lemma 4 at least f+1 of those are honest and
  are *already certificates for `Lr`*.

Either horn yields ≥ f+1 honest certificates. Note the same argument first rules
out the leader jumping over its own round r: that would require 2f+1 vertices at
r+1, of which f+1 honest ones support some round-`r` leader vertex — contradicting
that `leader_at(r)` created none.

**How much of this is reachable here.** Not their Theorem 3: weakening
`PopulatedOn` does not suffice, and the obstruction is precisely the step above.
In the vocabulary of this development:

- **L0 (density)** gives, with no assumptions at all, ≥ 2f+1 distinct authors at
  round r+1 whenever the DAG reaches above it — hence ≥ f+1 *correct* authors.
- **`SynchronisedOn` at round r** makes each of those correct blocks reference
  `Lr`. So **f+1 correct supporters is reachable**, from L0 + coverage, with no
  `Populated` and no P8.
- But a **certificate** needs a round-(r+2) block citing **2f+1** distinct
  supporters, and density only supplies f+1 correct ones. `SynchronisedOn` is
  honest-to-honest — as `liveness.md` puts it in the L4/L5 gap discussion, it
  "says nothing about whether correct validators reference a Byzantine-authored
  block" — so it cannot recruit the remaining f. Reaching 2f+1 supporters needs 2f+1 correct
  authors at round r+1 — which is `Populated`, i.e. P8 again.

So the decomposition is: **f+1 correct supporters comes free (L0 + coverage);
f+1 certificates does not.** Qiu et al. bridge the gap with the Predecessor Rule,
which has no counterpart here — the nearest clause, P7 (`Delivery.includes`,
references ⊇ held), constrains what a validator cites given what it holds, but
says nothing that forces a *quorum* of supporters to exist for an early-building
or jumping validator.

The realistic prize is therefore the supporter-level statement, not their
certificate-level one, unless a Predecessor-Rule analogue is added to the model.
That is still worth having — it is a liveness result independent of P8, and it marks
exactly where the argument starts to depend on the protocol
clause — but it should
not be advertised as their Theorem 3. M3
(`certificates_eq_empty_of_directSkip`) remains the only nearby existing result,
and it runs the other direction.

### 9.6 Method

They work by refinement into LiDO-DAG: a transition system over (global DAG,
LiDO cache tree, abstract pacemaker), where committing a leader vertex decomposes
into Pull / Invoke / Push, each adding an ECache / MCache / CCache node. The
selling point is that liveness reduces to safety properties of the abstract
pacemaker, which are provable by refinement — an engineering answer to the
difficulty of liveness proofs. Pre-GST timer unreliability is handled with
segmented traces.

The contrast with this development is real and worth stating plainly rather than
competitively. Theirs is operational and quantified over traces and instants;
liveness is a property of executions. The account here is structural:
`SynchronisedOn` is a condition on a DAG, no theorem above `Timing.lean` mentions
time, and the time-dependence is confined to one file. The payoff of the
structural style is visible in §9.3 — the dependency on the round-jumping clause
shows up as a named hypothesis (`PopulatedOn`) of a single lemma, rather than as a
line in a transition relation. The cost is that their theorems cannot be stated
here at all: "within bounded time" is not expressible in this vocabulary
(report §9).

Both models have acknowledged gaps at the same place, incidentally: their
Proposition 1 (local DAG ⊆ global DAG) is "implicitly assumed … as it does not
yet capture the staging area", which is the same status P4 has here.

---

## Sources

- [Mysticeti — arXiv:2310.14821](https://arxiv.org/abs/2310.14821) · [NDSS 2025](https://www.ndss-symposium.org/ndss-paper/mysticeti-reaching-the-latency-limits-with-uncertified-dags/)
- [Cordial Miners — arXiv:2205.09174](https://arxiv.org/abs/2205.09174) · [DISC 2023](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.DISC.2023.26)
- [Blockmania — arXiv:1809.01620](https://arxiv.org/abs/1809.01620)
- [Hashgraph — COINS 2020](https://hedera.com/wp-content/uploads/2025/11/hh-ieee_coins_paper-200516.pdf)
- [Mahi-Mahi — arXiv:2410.08670](https://arxiv.org/abs/2410.08670)
- [Odontoceti — arXiv:2510.01216](https://arxiv.org/abs/2510.01216)
- [Starfish — ePrint 2025/567](https://eprint.iacr.org/2025/567) · [preprint](https://nikitapolyanskii.com/writings/2025-44-starfish/preprint.pdf)
- [Bluestreak — ePrint 2026/898](https://eprint.iacr.org/2026/898)
- [Lifefin — arXiv:2511.15936](https://arxiv.org/abs/2511.15936)
- [Sailfish — ePrint 2024/472](https://eprint.iacr.org/2024/472)
- [Shoal++ — arXiv:2405.20488](https://arxiv.org/abs/2405.20488) · [NSDI 2025](https://www.usenix.org/conference/nsdi25/presentation/arun)
- [Qiu, Xiao, Shao — Mechanized Safety and Liveness Proofs for Mysticeti, S&P 2026](https://flint.cs.yale.edu/flint/publications/sp26.pdf) · [artifact](https://zenodo.org/records/17267594) · [FLINT page](https://flint.cs.yale.edu/flint/publications/sp26.html)
- [LiDO-DAG — doi:10.1145/3729306](https://dl.acm.org/doi/10.1145/3729306) · [PDF](https://flint.cs.yale.edu/flint/publications/lido-dag.pdf)
- [Reusable Formal Verification of DAG-based Consensus — arXiv:2407.02167](https://arxiv.org/abs/2407.02167)
- [Nonforking with Dynamic Stake — arXiv:2504.16853](https://arxiv.org/abs/2504.16853)
