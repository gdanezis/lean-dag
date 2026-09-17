# lean-dag — Steelhead: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their _intended_ meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Steelhead** arc: two commit
rules over one DAG, the synchronous rule of Mysticeti at wavelength `ws`
and the asynchronous rule of Mahi-Mahi at wavelength `wa`, composed by
giving every round a wavelength. The paper (Sonnino et al., *Steelhead*,
2026 draft) argues that the composition is safe for any two rules
satisfying an interface, that it is live under partial synchrony and,
through a second verdict on the asynchronous slots, under asynchrony, and
that a validator can change the period without any drain. The arc
settles those claims for the `3f + 1` pair, on the unmodified DAG layer,
and proves as a theorem the argument that makes the second verdict
necessary (§4).
Results carry **SH**-labels. Everything lives in `LeanDag/Steelhead/`
with witnesses in `LeanDagTest/Steelhead/`, consuming the core and the
Mahi-Mahi arc read-only, under the statement/proof partition of
`mahi-mahi.md` §9, and importing nothing of Barnacle.

## 0. Overview

**The protocol.** Mysticeti decides a slot proposed at round `r` from
rounds `r + 1` (votes) and `r + 2` (certificates); Mahi-Mahi from rounds
`r + wa − 2` and `r + wa − 1`, with the leader named by a coin read at
the decision round. Steelhead runs both on one DAG: a wavelength function
`w : ℕ → ℕ` gives every round the number of rounds its slot reads, and
the protocol's `w` is periodic, `wa` at every `k`-th round and `ws`
elsewhere. Which rounds are asynchronous is a function of the round
number alone, so the mode is an interpretation of the DAG and touches no
block. The one rule change is the anchor floor: an undecided slot at
round `r` searches for its anchor from round `r + w r`, at its own
wavelength (§3). The period `k` is adapted by a deterministic update rule
run on the causal history of an agreed event, the interval's chain anchor
(§5).

**What is reused.** The DAG core; the anchored decision relation
(`Common/Anchored.lean`), whose `waveAt` field became a function of the
slot's round for this arc; Mahi-Mahi's direct rules, certificate, link
and laws at every wave; the counting lemma MM2; the timed model's bridge
from coverage into certification; the unpredictable-leader clause.

**The results.**

- **SH1–SH5, safety at a wavelength function** (§3): the certificate
  lemmas at the slot's own wave, agreement across views and routes
  whatever the waves of the slot and of its anchor, the handover
  corollary, conservativity at a constant wavelength, chain agreement,
  and the coincidence of the direct verdicts of the output and the chain
  at an asynchronous slot (SH5b). The paper's Lemmas 1 and 2, Theorem 1,
  Corollary 1, Theorem 5, the agreement half of Theorem 4, and the
  protocol section's remark on direct verdicts.
- **SH6, liveness under synchrony** (§6): a reliably led slot commits
  under coverage, by the direct rule, everything below a fair run is
  decided, a slot whose leader has no block is skipped once a quorum
  blames it (SH6c), a candidate one reliable block references one round
  up commits under synchrony whether or not its leader is reliable
  (SH6e), and a slot is decided once every slot from its floor up to
  some reliably led slot is decided (SH6f), or once the chain of floors
  above it reaches a reliably led landing (SH6g); and the round-robin
  schedule the implementation runs offers a reliable run past every
  round, and a reliable leader within `n − |T|` rounds of every round,
  which is what SH6b asks for (SH6h). The paper's Theorem 2, for
  the decision relation.
- **SH7, chain liveness** (§4): under Mahi-Mahi's run clause at the
  chain schedule every chain verdict below a run is settled, under
  synchrony without the clause, and below any one run of `wa` good coins
  (SH7c). The chain half of Theorem 3 (i).
- **SH8, the stall** (§4): under the paper's own asynchronous adversary,
  at every period `k ≥ ws` the output never decides a slot of the
  residue class `k − 1`, whatever the asynchronous slots do. The
  argument the chain verdict answers, as a theorem.
- **SH9, the drain** (§4): `wa` consecutive commits decide every slot
  below them at any wavelength function bounded by `wa`; at period `1`,
  under the run clause at the output schedule, past every round some
  slot has everything below it decided (SH9b); and an asynchronous slot
  costs `wa − ws` rounds, its successor waits at most `wa − ws − 1`
  (SH9c). Theorem 3 (ii), and the protocol section's latency arithmetic.
- **SH10, the scan's state** (§5): the period, the agreed output's cursor
  and its last commit are agreed across views under any update rule, so
  is the output under the adaptive wavelength
  over the intervals the record's rounds fall in; the scan of an
  interval ends once its chain verdicts are in, and under the clause it
  ends for every interval; an anchor below which the agreed output
  committed nothing for `I` rounds hands the next interval period `1`
  (SH10e); every
  interval holds two asynchronous rounds and the period stays in its
  range (SH10f, SH10g); the agreed output is a prefix of the view's own
  and stalls below a slot the view leaves undecided (SH10i, SH10j); and
  a window of `I + 1` rounds resolves an asynchronous slot of every
  candidate once `I ≥ K + wa − 2` (SH10k). Theorem 4, the period half of
  Theorem 3 (i), and the adaptive section's structural claims.
- **SH11, the coin** (§4): with a uniform coin the chain slot of a
  round commits with probability `|good| / n`, at least `(n − f − b) / n`
  by MM2 at `wa ≥ 5` and so at least `1/3`, and at least `1/n` at
  `wa ≥ 4` (SH11e); over `m` rounds the probability that no round's coin
  names a directly committed leader is at most `((f + b) / n)^m`, which
  tends to zero. The probability half of Theorem 3 (i), in Mathlib's
  `PMF`. And Theorem 3's "with probability `1`" in the form a finite
  record admits (SH15): over the coins of `M` blocks of `K` rounds, one
  opening each interval from the second after a slot's, a view's scan
  stalls below the slot's interval or leaves the slot undecided under
  the failover with probability at most
  `2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)`, which tends to zero; and
  over a sequence of records, with the coin drawn as a process, the
  infinite product of the uniform distribution, for almost every coin
  some record decides the slot in every view holding its horizon
  (SH15c), Theorem 3's "with probability `1`" itself. Both hold against
  an adversary that builds its record from the draws already made
  (SH11f, SH15d, SH15e): what it may not read is a block's own coins
  before fixing what that block's rounds commit.
- **SH12, on data** (§8): the anchor-floor counterexample, the stall DAG
  with its asynchronous commit beside it, the period sequence at a
  concrete update rule, the coin streak that outputs nothing through any
  horizon, the Byzantine floor, Algorithm 2's replay on a healthy
  window, on a startup window and on a complete window too short for a
  wave, and the rotating stall whose period Algorithm 2 answers `4` at
  every anchor.
- **SH13, the ledger** (§3): the committed-leader sequence and the
  ledger of a settled prefix are agreed across views, the ledger is
  monotone, and a block enters at one slot, which both views name. The
  paper's Corollary 2, order and integrity.
- **SH14, output liveness under the failover** (§5): a slot
  two intervals below an anchored one is decided once a run of `wa`
  coin-led commits above that interval is in view: while the slot waits
  the agreed output's last commit lies below it, so every anchor two
  intervals up sits more than `I` rounds above that commit, the failover
  fires at each anchored one and the period is `1`
  from the first, where the run decides everything below it. Theorem 3
  (ii) and the asynchronous half
  of Definition 1's validity, deterministic given the anchor and the run,
  the two events the coin supplies almost surely; SH14b reads both off
  Mahi-Mahi's run clause at the chain schedule with runs of `K` good
  coins, `K` the bound on the period, and concludes that every slot far
  enough below the horizon is decided; SH14c names them as two runs of
  the coin alone, `K` good coins opening an interval past the slot's and
  `wa` above it, the form SH15 draws.
- **SH16, the interface composes** (§3): any family of rules whose laws
  hold, one per round, agreeing on rung count and tie-break, composes
  into a rule whose laws hold, so its verdicts agree across views; and
  Steelhead's rule is the composite of Mahi-Mahi's read at each round's
  wave, by definition. The paper's Theorem 1 at the interface level, SH2
  its instance.
- **SH17, atomic broadcast** (§3): Definition 1 clause by clause over
  settled prefixes: a delivered block is delivered by every view whose
  settled prefix is as long, a delivered block is a block of the record
  entering at one slot, a reliable block is delivered with the first
  committed reliable leader two rounds up after GST, and two blocks
  enter at the same slots in every view, so in the same order. Under
  asynchrony the delivery rests on the reference rule instead: a block
  every reliable validator has referenced by round `ρ` lies in the cone
  of every block above `ρ`, so the first committed slot there delivers
  it whoever led it (SH17e). The
  liveness half is SH6b, SH14b and SH15.
- **SH18, the replay** (§5): Algorithm 2 as data, the window's evidence
  read from the anchor's causal history, the three passes and the
  hysteretic selection; the selection stays among the candidates and
  never worsens the score, the window's evidence is consistent, Lemma
  3's count holds on the window once a quorum has populated the boost
  and decision rounds within it, every timing lies between its round and
  the window's top, the asynchronous term is at most the rule's own
  value on the same data, and a window commit is a commit on the DAG;
  Algorithm 2 keeps the period in range (SH18h), the
  share of the candidates the window marks committed is the rule's
  commit probability on the window read as a record (SH18i), and a
  canary spacing coprime to a candidate period gives a probe in any
  window holding two canary rounds (SH18j).

### 0.1 Correspondence with the paper

| paper | here | remark |
| :--- | :--- | :--- |
| Definition 1 (atomic broadcast) | SH17, with SH6b, SH14b, SH15c | agreement, integrity and total order over settled prefixes, validity after GST with the first committed reliable leader two rounds up (SH17c) or, under asynchrony, with the first committed slot above the round by which the reliable validators have referenced the block, whoever led it (SH17e, the reference rule of A1); the "eventually" is SH6b under synchrony, SH14b under the clause and SH15c almost surely under asynchrony. The order of the blocks one commit releases is not modelled |
| Lemma 1 (certificate uniqueness; a skipped block is never certified) | SH1a, SH1b | Mahi-Mahi's lemmas at the slot's wave |
| Lemma 2 (quorum intersection across the wave) | SH1c | at `r + w r`, whatever the block's own wave |
| Corollary 1 (handover) | SH3 | stated against the relation's anchor search |
| Theorem 1 (agreement) | SH2, SH16 | `AnchoredRule.decided_unique` at Steelhead's laws; at the interface level, any family of rules whose laws hold composes into one whose laws hold, and Steelhead is the composite of Mahi-Mahi's rule at each round's wave |
| Corollary 2 (total order and integrity) | SH13 | in part: the relation's own ledger theorems at Steelhead's laws, over a settled prefix. Ordering the blocks a single commit releases is declined development-wide (report §1.4, §5.6) |
| Theorem 2 (liveness under partial synchrony) | SH6a, SH6b, SH6c, SH6e, SH6f, SH6g, SH6h | in part: the honest-leader commit by the direct rule, everything below a fair run, the crashed-leader skip from `n − f` blames, the remark that partial dissemination does not defer, for a leader that did not equivocate, and the anchor clause as the rule has it, a slot decided once every slot from its floor up to some reliably led slot is decided (SH6f) or once the chain of floors reaches a reliably led landing (SH6g). The bound on that clause, "once the first honest-led slot above its floor commits, at most `b` slots higher", is refuted on data, an equivocating leader at the floor being the anchor (§7, finding 7); what holds at the implementation's round-robin schedule is a round count, one reliable leader within `n − |T|` rounds and a reliable run of three past every round at `n = 3f + 1` (SH6h), which also discharges SH6b's fairness hypothesis there. The `O(wa + b)` ordering bound fails for some coin sequences at period `1` (§7, finding 5) and holds only as SH15's tail; timeouts and pacing are not modelled, `SynchronisedOn` standing for the paper's A4 and its pacing |
| Theorem 3 (i) (the chain resolves, the period reaches `1`) | SH7a, SH7c, SH10c, SH10d, SH10e, SH11 | the chain settles under Mahi-Mahi's run clause and below any one run of `wa` good coins, a period is derived for each interval, an anchor below which the agreed output committed nothing for `I` rounds hands the next interval period `1`, the failover the implementation applies before the rule is consulted (`apply_period_update`) and the paper's premise on the update rule is not (§7), and the coin is modelled by its effect and as a `PMF`, at `wa ≥ 5` and at `wa ≥ 4`. The "with probability `1`" is SH15c over a sequence of records, SH15a's tail on one |
| Theorem 3 (ii) (at period `1` the ledger grows) | SH9, SH9b, SH14, SH14b, SH14c, SH15 | SH9b at period `1` under the run clause at the output schedule and below its horizon; SH14 for the adaptive output under the failover, given one anchored interval at least two past the slot's and one run of `wa` good coins above it; SH14b reads both off the run clause at the chain schedule, SH14c off two runs of the coin; SH15a bounds the probability that some view has not derived the slot's period or leaves it undecided, over `M` blocks of coins, by `2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)`, which tends to zero (SH15b); and SH15c states the "with probability `1`" itself, over a sequence of records with the coin drawn as a process: for almost every coin some record decides the slot in every view holding its horizon. SH15d and SH15e are the same two against an adversary that answers the draws already made, by the adaptive block bound SH11f. The growth of the ledger from the settled prefix is SH13 |
| Theorem 4 (agreement of the period) | SH10a, SH10b | for any deterministic update rule |
| Adaptive section, `I ≥ 2 · maxPeriod` and `1 ≤ k ≤ maxPeriod` | SH10f, SH10g, SH10k, SH18h | two asynchronous rounds per interval at any `k ≥ 1` with `2k ≤ I`; the period stays in range when the initial period does and the update rule keeps it there, the failover's `1` included, which Algorithm 2's replay does whenever the candidates lie in `[1, K]` (SH18h). The bound admits `I < maxPeriod + wa − 2`, where a window of `I + 1` rounds holds the decision round of none of its asynchronous slots at some anchors and of one at others (SH10k; §7, finding 8) |
| Adaptive section, "the replay is exact in expectation" | SH18i | in the part that is a theorem: at a round the window retains, the share of the `n` candidates the window marks committed is the probability that a uniform coin names a directly committed leader on the anchor's history read as a record, the paper's `c_r / n`, at `1 ≤ wa`. The anchor's term is the approximation the paper admits |
| Protocol section, "setting the canary odd ensures it is coprime to candidate periods, guaranteeing periodic probes" | SH18j | at a canary spacing coprime to a candidate period of at least two, a window holding two canary rounds whose decision round it retains holds a probe for the candidate, since two consecutive multiples of the spacing cannot both be multiples of the period |
| Protocol section, "whenever either verdict of an asynchronous slot is direct, the two coincide" | SH5b | predicate for predicate, at a slot proposed at its own round and led by the coin |
| Protocol section, "the successor waits at most `max(0, wa − ws − 1)` rounds", "delays never compound" | SH9c | arithmetic on the decision rounds; output timing itself is not modelled |
| Theorem 5 (conservativity) | SH4 | at a constant wavelength by `rfl`, period `1` by `Nat.mod_one`, and at wave three the derivations are exactly the core's, both directions |
| Lemma 3 (the replay cannot be starved) | SH11a, SH18d, SH18f, SH18g | `c_r ≥ n − f − b` on the DAG under any scheduling (SH11a), and on the window once a quorum has populated the boost and decision rounds within it (SH18d), which is what "populated" must mean for the replay, whose evidence is the window's (§7, finding 6); the replay's asynchronous term is at most the mean of the decision round over the `c_r` committed candidates and the window's top over the rest, the rule's own value on the same data (SH18f); a probe's success is a certificate quorum the DAG holds, so the adversary lowers the synchronous term's estimate but never raises it (SH18g). Both at `2 ≤ ws < wa` |
| Theorem 3 (i), "a committed asynchronous slot does not by itself decide the synchronous slots below it" | SH8 | the argument of "Why the chain, and not the output" as a theorem, for every `2 ≤ ws ≤ k` rather than the one period it walks through (§4) |

## 1. The wavelength function

`periodic ws wa k` is the paper's `w(r) = wa if r mod k = 0 else ws`
(`Model/Wavelength.lean`), and `IsAsync k r` names the asynchronous
rounds. At `k = 1` the function is the constant `wa` (`Nat.mod_one`), at
`k = ∞` the constant `ws`, so both ends of the dial are one rule at one
wave. Lean's `r % 0 = r` makes only round `0` asynchronous at `k = 0`; no
result excludes that period and none needs to, since SH8 reads `2 ≤ k`
off its own `2 ≤ ws ≤ k` and SH10 holds at every period.

Every result is stated at an arbitrary `w : ℕ → ℕ`, not at `periodic`:
the rule consumes a wavelength function, and the period is one way of
producing one. What the results assume of `w` is a lower bound at every
round, `2 ≤ w r` for safety and `3 ≤ w r` for liveness, and for the
drain an upper bound `wa`.

## 2. The rule at a wavelength function

`steelheadAnchored w` (`Model/Decision.lean`) is one anchored rule whose
data at a slot proposed at round `r` are Mahi-Mahi's at wave `w r`: the
certificate-quorum direct commit, the slot blame as direct skip, one rung
of link (a certificate in the anchor's cone), no tie, and the wave offset
`waveAt r = w r − 1`, so that an anchor sits at round `r + w r` or above.
`Decided w U V k v` is the anchored relation at that data. At a constant
`w` the rule *is* `mahiMahiAnchored w` by `rfl` (SH4); at the constant
`3` the derivations are exactly the core's (MM1d transported, and its
mirror).

The one change to the shared relation was to make `AnchoredRule.waveAt`
a function of the slot's round. Every other rule sets a constant, and
`Banded` (the offset band) requires one: the band rebases every round by
a constant, and a wave that alternates with the round reads an absolute
round. Steelhead has no band, no `LocalTruncate` and no `Safe` headline
(`target-properties.md` §3.4c); what the band derives that needs no
offset, persistence and view monotonicity, is proved through the
extension laws (§6).

## 3. Safety, and the anchor floor

`Safety/Statement.lean`, each claim at the weakest bound its proof
consumes on the rounds read, `1 ≤ w r` for SH1c and `2 ≤ w r` for the
rest:

- **SH1a, SH1b, SH1c** are Mahi-Mahi's certificate lemmas at the slot's
  own wave: a directly skipped slot has no certificate for any
  candidate, two certified candidates of one author and round coincide,
  and a directly committed candidate at `r` is certified in the cone of
  every block at round `r + w r` or above, whatever wave that block's
  own slot carries.
- **SH2, agreement**: two views deciding one slot reach the same verdict
  by any routes, whether the slot's wave is `ws` or `wa` and whether the
  anchor's is. The relation's agreement at `steelheadLaws`: every law of
  `AnchoredRule.Laws` speaks of one slot and its anchors, and at that
  slot the rule is Mahi-Mahi's at the slot's wave, eligibility included.
- **SH3, handover**: a direct commit in one view is committed by every
  view that finds the slot an anchor, whichever rule decides that anchor,
  and no view skips it. This is the one cross-rule law: the anchor lies
  at `r + w r` or above, where SH1c places a certificate in its cone.
- **SH4, conservativity**: `steelheadAnchored (fun _ => w) =
  mahiMahiAnchored w` and `periodic ws wa 1 = fun _ => wa`, by `rfl` and
  `Nat.mod_one`; at the constant `3` the derivations are exactly the
  core's, MM1d one way and its mirror the other, since the core's skip
  is the slot-level blame Mahi-Mahi's is (`decided_of_core_decided`).
- **SH5, chain agreement**: the chain verdicts (§4) agree across views,
  an instance of MM1c at the chain schedule.
- **SH5b, the direct verdicts coincide**: at an asynchronous round whose
  slot is proposed there and led by the coin, the output's direct commit
  and direct skip are the chain's predicates, so a direct derivation in
  either relation is one in the other. The protocol section's "whenever either verdict of an
  asynchronous slot is direct, the two coincide"; only the indirect
  verdicts may differ, and §4 says why.

**The interface.** Theorem 1 is stated for any two rules of the
interface. `compose rules` (`Model/Compose.lean`) is the composite of a
family of anchored rules, one per round: the slot proposed at round `r`
takes its wave offset, direct predicates and rungs of link from
`rules r`, and the rung count and tie-break, which the relation reads
without a slot, from the rule of round `0`. **SH16**
(`Interface/Statement.lean`): if every rule of the family satisfies
`AnchoredRule.Laws` and the family agrees on rungs and ties, the
composite does (SH16a), each law at a slot being the slot's rule's, the
anchor's rule never entering; the composite's verdicts then agree across
views (SH16b); and `steelheadAnchored w` is the composite of Mahi-Mahi's
rule read at `w r`, by definition (SH16c), so SH2 is an instance. The
laws are clauses A2 and A3 in the relation's terms; a pair the paper's
discharge table leaves open is outside the theorem until they are
discharged.

**The ledger.** Agreement is about one slot; the output layer reads
verdicts off in slot order, and what it owes is the paper's Corollary 2.
**SH13** (`Ledger/Statement.lean`) states it: over a prefix each view has
settled, the committed-leader sequences coincide, so do the ledgers they
deliver, the ledger only grows as further slots settle, a block enters at
one slot and both views name the same one, and a committed block is the
candidate of one slot. Every conjunct is the anchored relation's own
ledger theorem at `steelheadLaws`, or a fact of `Common/Ledger.lean` that
reads no rule at all, so the arc adds no argument here. The claims are
order and integrity, not progress: they are conditional on a settled
prefix, which under the stall (§4) is short.

**Atomic broadcast.** Definition 1's clauses, as **SH17**
(`Broadcast/Statement.lean`) reads them off settled prefixes: agreement,
a block one view delivers over a settled prefix every view delivers over
any settled prefix at least as long (SH13b and SH13c); integrity, a
delivered block is a block of the record, so one its author proposed,
and enters the ledger at one slot (SH13d); validity, a reliable block at
round `r` lies in the cone of every reliable block from round `r + 2`
under synchrony from `r`, so it is delivered with the first committed
reliable leader there once the prefix below is settled
(`reaches_of_synchronisedOn`); and total order, two blocks enter at the
same slots in every view that settled them, so in the same order
(SH13d). Validity under asynchrony reads the reference rule instead of
synchrony (**SH17e**): with the clause `Core::try_new_block` implements,
where a block references every block its author holds that its own
parent does not already cover, a block every reliable validator has
referenced by round `ρ` lies in the cone of every block above `ρ`, its
author reliable or not, since a quorum of references meets the reliable
set; so the first committed slot above `ρ` delivers it, whichever leader
the coin named. Without that clause a block delayed past its own round is
never referenced and validity fails under asynchrony, which is why the
paper's A1 states it (§7). The "eventually" of agreement and validity is
the liveness half: SH6a and SH6b under synchrony, SH14b under the clause
and SH15c almost surely under asynchrony. The order of the blocks one
commit releases is a tie-break the development does not assume
(report §1.4).

**Why the floor is the slot's own wave.** An asynchronous slot at round
`r` with `wa = 5` has its certificates at `r + 4`. A block at `r + 1`
references only round-`r` blocks and sees none of them; a synchronous
anchor at `r + 3` sees none either. Reading the floor from the
synchronous wave would let one validator skip through such an anchor
what another directly committed. `LeanDagTest/Steelhead/Model.lean`
exhibits it: on an eight-round DAG at period four, the rule with every
floor read from the synchronous wave derives both a commit and a skip of
slot `0` from the one full view (`lowFloor_commit`, `lowFloor_skip`),
and at the slot's own floor the same anchor is not eligible.

## 4. The chain verdict, the stall, and the drain

**The stall.** A direct commit reaches a slot below it only through a
decided stretch: from the lower slot's floor up to the commit every slot
must be decided, because the anchor search stops at an undecided one. At
every period `k ≥ ws` that stretch holds a synchronous slot, which the
adversary keeps undecided at no cost, and the output stalls while the
asynchronous slots commit on schedule. This is the paper's "Why the
chain, and not the output"; SH8 is it as a theorem, for every period
rather than the one the paragraph walks through. A synchronous slot at
round `r` anchors at the earliest
commit-or-undecided slot at round `≥ r + ws`, passing over skips; an
undecided anchor leaves it undecided. Under the paper's own adversary,
the leader block delivered to exactly `f + 1` validators before the
vote, a synchronous slot has `f + 1` votes and `n − f − 1` blames,
neither quorum: it is never directly decided and never certified, so no
anchor commits it and no anchor skips it. A slot of the residue class
`k − 1` then waits on the class-`(k − 1)` slot one period up, which waits
on the next, and the chain never closes: the asynchronous slots at
`0, k, 2k, …` all commit and nothing above the first such slot is ever
output.

**SH8** (`Liveness/Statement.lean`, `Stall`) states it for every
`2 ≤ ws ≤ k` and every `wa`: at one slot per round, if no synchronous
candidate is ever certified and no synchronous slot is directly skipped
in a view, no slot at a round `≡ k − 1 (mod k)` is ever decided in that
view. The proof is an induction on the derivation: a class-`(k − 1)`
slot's direct verdicts are excluded by hypothesis; a synchronous anchor
never commits without a certificate; an asynchronous anchor sits a full
period above, and the class-`(k − 1)` slot between must be skipped,
which is the claim one period up. `LeanDagTest/Steelhead/Stall.lean`
shows the adversary's shape on valid data at `n = 4`: every synchronous
slot's candidate has exactly two votes, the asynchronous slot commits
directly, and slot `3` is undecided by SH8. For `ws = 3` only `k = 1`
and `k = 2` are live; every larger candidate the paper's update rule can
select, `4` up to its maximum of `64`, stalls.

**The chain verdict.** The paper keeps the output relation and
adds, for the asynchronous slots, a second verdict that drives the
period update alone: the asynchronous rule with anchors restricted to
asynchronous slots, so that no known-leader slot lies on the chain and
nothing the adversary holds undecided blocks it. The arc reads the chain
at *every* round, with that round's coin leader, as the reference
implementation does (`committer.rs`, `compute_chain`): `chainSlots coin
= Slots.identity coin` and `ChainDecided wa coin = MahiMahi.Decided wa`
at that schedule (`Model/Chain.lean`). Reading only the asynchronous
rounds would make the chain depend on the period, which its own
verdicts are meant to fix (§7). The chain is therefore an instance of
the Mahi-Mahi arc at a new schedule, and every result about it is
Mahi-Mahi's: agreement (SH5), liveness under the run clause (**SH7a**,
MM3c with the spanning hypothesis discharged by the identity rounds, so
a run of `wa` chain commits suffices), liveness under synchrony
without any clause (**SH7b**, the core's L10 at Mahi-Mahi's support),
and the step SH7a takes once per round on its own (**SH7c**): one run of
`wa` good coins settles every chain verdict below it, in any view holding
its decision rounds. SH7c is the form the coin's tail (SH15) consumes,
which asks for one run rather than one in every window.

**The coin** (`Model/Coin.lean`, `Coin/Statement.lean`). The clause
states the coin's effect; the probability that the effect obtains is
the counting lemma read through a uniform draw. With the coin
`PMF.uniformOfFintype Validator`, the chain slot of round `r` commits
directly exactly when the coin lands in `goodAt U wa r`, so with
probability `|goodAt U wa r| / n`, which MM2 bounds below by
`(n − f − b) / n` at `wa ≥ 5` on any populated wave, under any
scheduling, at least `1/3` at `n ≥ 3f + 1` (`ratio_le_commitProb`,
`third_le_commitProb`). At `wa ≥ 4` MM2 promises only one committed
correct candidate, so the bound is `1/n` (`inv_card_le_commitProb`,
SH11e): the paper's wavelength-four trade-off. Over `m` rounds with
independent coins, modelled as the uniform distribution over the leader
maps `Fin m → Validator`, the probability that no round's coin names a
directly committed leader is at most `((f + b) / n)^m`, and that tends to
zero (`noCommitProb_le`, `tail_tendsto_zero`); `Coin/Statement.lean`
states the five as SH11a to SH11e over `commitProb` and `noCommitProb`,
two of the quantities `Model/Coin.lean` defines.

**The tail of the output** (`undecidedProb`, SH15). Theorem 3's "with
probability `1`" cannot be stated on a fixed record, which is finite and
so populates finitely many rounds; what a finite record admits is a
probability that tends to zero with the horizon, uniformly over records
populated through it, the form SH11c/d already take. `undecidedProb`
draws the coins of `M` blocks of `K` rounds, block `j` opening interval
`j₀ + 2 + j` past the slot's interval `j₀` (`blockRound`, `coinOfBlocks`,
which reads the blocks back and draws a fixed value elsewhere), uniformly
and independently, and measures the maps under which some view holding
the horizon (`blocksHorizon`), at a period sequence matching every
state it derives, has not
derived the state of the slot's interval or leaves the slot undecided
at the adaptive wavelength and schedule. A sequence matching what the
view derives is arbitrary where the scan has stalled, so a slot counts
as decided only under every completion of the derived periods, and a
scan that never reaches the slot's interval counts as a failure.
**SH15a** (`undecidedProb_le`) bounds it by
`2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)` at `2 ≤ ws ≤ wa`, `5 ≤ wa ≤ K
≤ I`, a slot at round one or above, under any update rule, and the
blocks' waves populated where MM2
reads them: a good block in each half of the `M` settles every chain
verdict up to the later block, so the periods are derived that far
(SH7c, SH10c), and decides the slot by SH14c, the earlier one anchoring
its interval and the later one the run above it, so the failure set lies
in the union of the two halves' no-good-block sets, and each of those is
a product whose every block of the half misses its all-good maps, of
which MM2 counts at least `(n − f − b)^K` out of `n^K`
(`no_good_block_prob_le`). **SH15b**
(`undecided_tail_tendsto_zero`) is that the bound vanishes as `M` grows,
since `n − f − b ≥ 1`. The blocks' coins are drawn after the record is
fixed, as SH11c's are: the adversary that shapes the DAG does not see
them, which is the coin's unpredictability; what the network must supply
is that the blocks' waves be populated.

**The adaptive adversary** (`NonAnticipating`, SH11f, SH15d). A record
fixed before the draw is more than the argument needs. A **strategy**
`σ` answers the coins of the `M` blocks with a record, and is
*non-anticipating* when the committed set of a block's rounds is fixed
by the blocks below that one: the adversary shapes the whole DAG from
the draws already revealed, and only a block's own coins are hidden from
the blocks it decides. **SH11f** (`no_good_block_prob_le_adaptive`) is
the block bound for such a family: peel the last block, whose good set
the earlier ones fix, so the count over the maps whose every block of a
set is bad is at most the product of the per-block counts
(`card_all_bad_le`), exactly the bound the fixed family gets. The box
argument cannot reach this, since the failure event is no longer a
product once the good sets read the draw. **SH15d**
(`undecidedProb_le_adaptive`) is SH15a against a strategy, at the same
bound and by the same inclusion, and **SH15e**
(`decidedAlmostSurely_adaptive`) is SH15c over a sequence of strategies,
the `m`-th answering the coins of its own `m` blocks. What the adversary
may not do is read a block's coins before fixing what that block's
rounds commit, which is what an unpredictable coin means on a DAG.

**The coin as a process** (`coinMeasure`, SH15c). What one finite record
cannot say, a sequence of them can. `coinMeasure` is
`Measure.infinitePi` of the uniform distribution over the validators, on
whatever discrete measurable structure they carry, so the coin of every
round is drawn at once and independently; on the rounds of finitely many
blocks it is the uniform block map (`coinMeasure_blockCoins_mem`: one
block map is a box on the blocks' rounds, of measure `n^(−MK)`, and a
set of maps the disjoint union of its members' boxes). **SH15c**
(`decidedAlmostSurely`) takes a sequence of records, the `m`-th holding
the waves of `m` blocks populated where MM2 reads them, each with its
own update rule kept in `[1, K]`, and concludes that for almost every
coin some record decides the slot in every view holding its horizon, in
SH15a's sense. The coins under which no record decides it lie, for every
`m`, among those under which the `m`-th leaves it undecided, a set of
measure at most SH15a's bound read through the process
(`undecided_coin_le`), which vanishes (SH15b); so they are null, by
monotonicity alone. The records are any sequence, the prefixes of one
execution among them, since the argument reads each on its own; they are
fixed before the coin is drawn, as SH15a's one record is. This is
Theorem 3's "with probability `1`" as the paper states it.

**The drain.** Once the period is `1` every slot is asynchronous, and a
run of `wa` consecutive commits decides every slot below it, including
the slots an earlier period left undecided: **SH9**
(`AllDecidedBelowOfRun`) states this at any wavelength function with
`1 ≤ w r ≤ wa` and one slot per round, by the relation's descent below a
committed run, the spanning hypothesis discharged by the identity rounds
at the largest wave. **SH9b** (`AllDecidedBelowAtPeriodOne`) is Theorem
3 (ii) as one statement: at `periodic ws wa 1`, under the run clause at
the output schedule, past every round whose window decides below the
horizon there is a slot below which every slot is decided, in any view
caught up to the horizon, so the settled prefix and with it the ledger
(SH13) extend as far as the horizon and the clause reach. The proof is
SH7a's at the output schedule,
since at period `1` the rule is Mahi-Mahi's at `wa` (SH4). The clause is
stated at the output schedule, whose asynchronous leaders are the coin's;
deriving it from the coin is the almost-sure half (§0.1).

**The cost of an asynchronous slot.** The protocol section's arithmetic
for a healthy network is **SH9c** (`AsyncSlotCost`): at one slot per
round and `1 ≤ ws ≤ wa`, an asynchronous slot at round `r` decides at
`r + wa − 1`, which is `wa − ws` rounds later than a synchronous slot
there would, and the synchronous slot `i` rounds above it, for
`1 ≤ i < k`, is decided at most `max(0, wa − ws − i)` rounds before it:
the successor waits at most `wa − ws − 1` rounds for causal ordering and
the wait is nonincreasing in `i`, so delays never compound. Decision
rounds only; output timing is not modelled.

## 5. The period

`Model/Period.lean` states the configuration-sequence model afresh,
importing nothing of Barnacle. Rounds `j·I + 1` to `(j + 1)·I` form
interval `j` (`intervalOf I r = (r − 1) / I`, round `0` in interval `0`),
each decided under one period. The **anchor** of interval `j` is the
interval's earliest round whose chain verdict is a commit, every round of
the interval below it chain-skipped (`IntervalAnchor`); **no anchor** is
every round of the interval chain-skipped (`NoAnchor`). The chain is read
at every round, so the anchor does not depend on the period in force, as
`complete_scans` reads it. The state a scan carries is the period, the
agreed output's next slot and the round of its last committed leader
(`ScanState`, the implementation's `period_schedule`, `agreed_next` and
`agreed_last_commit_round`). The sequence is a relation,
`PeriodAt I wa coin upd k₀ U V w j st`: interval `0` runs at
`⟨k₀, 1, 0⟩`; an anchored interval advances the agreed output over the
anchor's causal history (`AgreedAdvance`, the implementation's
`advance_agreed_output`: the cursor moves to the least slot that history
leaves undecided, the last commit to the round of the highest leader
committed on the way) and hands interval `j + 1` period `1` when that
commit lies more than `I` rounds below the anchor's round
(`apply_period_update`) and the update rule's answer otherwise; an
interval with no anchor keeps the state. A validator whose scan meets a
chain-undecided round waits, which is the absence of a derivation. The
update rule `upd : BlockId → ℕ → ℕ` is any function of
the anchor block and the current period; the paper's replay reads
the anchor's causal history, which the block id determines within one
universe. The wavelength the agreed output is read at is a parameter, so
that the agreement claims hold for any reading.
`adaptiveWave ws wa I per` is the wavelength function a
validator that derived `per` runs the output relation at, and
`adaptiveSlots coin known I per` the schedule it runs it on: one slot per
round, the coin at the rounds `per` makes asynchronous and the known
schedule `known` elsewhere. The claims that relate a schedule to the coin
one clause at a time (SH14) take this schedule as their instance (SH15).

`Period/Statement.lean`:

- **SH10a, agreement of the state**: two views deriving a state for
  interval `j` derive the same one, period, cursor and last commit
  alike, at `3 ≤ wa`, under any update rule.
  Induction on the derivation: the anchor is unique across views, since
  a lower anchor in one view is a chain-skipped round in the other and
  SH5 forbids it, and an anchor in one view against none in the other
  is the same contradiction; and the advance over an anchor's history is
  unique, since no verdict of that history lies above the anchor's round,
  so the new cursor is the least undecided slot at or past the old one
  and the new last commit the highest commit consumed.
- **SH10b, agreement of the output under the adaptive wavelength**: two
  validators that derived the state of every interval the record's
  rounds fall in, and decided a slot proposed among them at their own
  adaptive wavelengths, agree on the verdict. The sequences coincide
  there by strong induction on the interval: the anchors of the
  intervals below lie in the record, their histories are read at rounds
  below their own, where the sequences already agree, so the two views
  advance the agreed output alike (`AgreedAdvance.congr`)
  and SH10a gives the same state; a verdict reads the wavelength only
  at the rounds of the slots its derivation names, all of them at or
  below the round of the anchor block it rests on (`decided_congr`);
  and SH2 applies to the one function. The bound is not a convenience: a record holds finitely
  many blocks, so above its top round no chain verdict is derivable and
  no period beyond it either, and a claim asking for the *whole*
  sequence would hold only where the period reaches `0`, which is
  Mysticeti at every round but the first.
- **SH10c, the scan ends**: once every round of the
  interval has a chain verdict in a view, the view derives the next
  state: the least chain-committed round is the anchor, or every round
  is chain-skipped.
- **SH10d, the period advances under the clause**: under Mahi-Mahi's
  run clause at the chain schedule, a view caught up to the horizon
  derives a state for every interval whose rounds lie far enough below
  it, by SH7a at each interval and SH10c.
- **SH10e, the period reaches `1`**: the failover, as
  `apply_period_update` applies it. An interval that finds an anchor
  at round `r` below which the agreed output, advanced over the anchor's
  history, has its last commit at a round `last'` with `last' + I < r`
  hands the next interval period `1`, whatever the update rule would
  answer. The test is the scan's own, on the state it already carries,
  so no clause is placed on the rule and the recovery claims need
  nothing of Algorithm 2 but its range; where the paper's premise on the
  update rule, read literally, forbids every recovery from period `1`
  (§7). The anchor is a hypothesis: nothing deterministic forces one,
  and its existence is the almost-sure half (§0.1).
- **SH10f, SH10g, the shape of the adaptive run**: at any period `k ≥ 1`
  with `2k ≤ I`, every interval holds two asynchronous rounds, the
  paper's reason for `I ≥ 2 · maxPeriod`; and if the initial period lies
  in `[1, K]` and the update rule keeps a period there, so does every
  derived period, the failover's `1` included.
- **SH10i, SH10j, the agreed output**: every slot the agreed output
  consumed is decided in the view that derived it, since the anchors'
  histories lie inside that view and the laws carry a verdict out of a
  history (`2 ≤ w r`), which is what `assert_agreed_prefix` checks in the
  implementation's tests; and a slot the view leaves undecided is never
  consumed, so the cursor and the last commit stay at or below it in
  every state the view derives. The second is what puts the failover's
  test below a stuck slot, and both speak of slots at round one or above,
  the agreed output starting at slot `1` as the implementation's does.
- **SH10k, a window resolves an asynchronous slot of every candidate**:
  the window holds `I + 1` rounds, `round A − I` to `round A`, so an
  asynchronous round of period `k` has its decision round inside it when
  `I ≥ k + wa − 2`; at `I ≥ 2K` alone the window resolves a slot at some
  anchors and none at others (§7, finding 8).
- **SH14, output liveness under the failover**: in a view that derived
  every state up to a run's last round, if some interval at least two
  past a slot's finds an anchor, and above that interval the coin names
  a committed candidate at `wa` consecutive rounds that lead the output's
  slots there, then the slot is decided once the view holds the run's
  decision rounds. An anchor two intervals up lies more than `I` rounds
  above the slot, so while the slot waits the agreed output's last
  commit lies below it (SH10j),
  SH10e fires at the anchored interval and,
  by induction on the derivations, every interval up to the run runs at
  period `1`; the run's rounds then carry wave `wa`, its coins commit
  their candidates directly (SH11b's argument at the output schedule),
  and the drain SH9 decides every slot below the run. At `2 ≤ ws ≤ wa`,
  `3 ≤ wa` as SH10a, one slot per round and a positive interval. This is
  Theorem 3 (ii) and the asynchronous half of Definition 1's validity,
  deterministic given the anchor and the run; that the coin supplies both
  almost surely is the remaining half of Theorem 3.
- **SH14b, every slot is decided under the clauses**: SH14 with its two
  events read off Mahi-Mahi's run clause at the chain schedule, with runs
  of `K` good coins, `K` the bound the periods stay within (SH10g's
  premise), `wa ≤ K` and a window plus a run fitting in an interval
  (`c + K ≤ I`). A run of `K` consecutive rounds inside the second
  interval after the slot's holds a multiple of whatever period is in
  force, so an asynchronous round with a good coin, which the view
  chain-commits directly; SH7a settles every chain verdict of the
  interval, so that round or a lower chain-committed one is the anchor.
  The run in the next interval is the one SH14 needs. Every slot whose
  interval lies three intervals and a window below the horizon is then
  decided, in a view
  caught up to the horizon that derived every state below it. The clause
  with runs of `K` in every window is the deterministic stand-in for what
  the coin gives almost surely, as SH7a's is.
- **SH14c, output liveness from two good runs**: SH14 with its two
  events named as runs of the coin alone. `K` good coins opening an
  interval at least two past the slot's hit an asynchronous round under whatever
  period is in force, which the view chain-commits directly; `wa` good
  coins above that interval settle every chain verdict below them
  (SH7c), so the interval has its anchor, and they are the run SH14
  needs. At `K ≤ I`, so that a block of `K` rounds fits in an interval.
  Two runs at named places, each of a fixed positive probability: the
  form SH15 draws from the coin. No liveness claim here asks the period
  to stay in range: every round carries a chain verdict, so an
  interval's anchor exists whatever period is in force.

**The replay** (`Model/Replay.lean`, `Replay/Statement.lean`). Algorithm
2 as data: `ofAnchor U A I` reads the window's evidence off the anchor's
causal history at the rounds `round A − I` and above, as
`collect_window` takes it, per proposal round, wave and
candidate author, counting distinct validators (a candidate is committed
when a quorum certify it within the window, skipped when a quorum of the
window's vote-round blocks blame the author's slot, certified when the
window holds one certificate); `score` is `REPLAY(W, k')`'s three passes
over that evidence, in exact rationals, the probes of the canary rounds
(`probeRate`) standing in for the unprobed synchronous slots; `select`
is the hysteretic selection among the powers of two up to the largest
candidate (`candidatesUpto`), ties favouring the larger candidate and
the hysteresis keeping the current period unless a candidate improves on
it; `anchorUpdate` is the whole as an `UpdateRule`. **SH18a, b** (`select_mem`, `select_score_le`): the
selection stays among the candidates and never worsens the score.
**SH18c** (`certified_of_commits`, `not_certified_of_skips`): in the
window's evidence a committed candidate is certified and a skipped one
is not, at `2 ≤ w`. **SH18d** (`window_count`): Lemma 3's count on the
window: at a round the window retains whose boost round and decision
round a quorum has populated *within the anchor's history*, at least
`n − f − b` authors are marked committed at wave `wa`, MM2 read on the
history as a record of its own, whose votes and certificates are the
universe's restricted to it (`candidatesAt_toRecord`,
`certificates_toRecord`). The hypothesis that the quorum's blocks lie in
the window is §7's finding 6. The passes are recursions on the round
index, as Algorithm 2 walks them: `timingAt` from the top of the window
down, `firstCommitAt` the earliest expected commit at or above a round,
`gateAt` the latest expected decision below it. **SH18e**
(`bounded_timingAt`): every round's expected decision lies at or above
the round, its expected commit at or above its decision, and both at or
below the window's top, so the top is the penalty an unresolved outcome
pays and no more. **SH18f** (`async_term_bound`), Lemma 3's second
sentence: at an asynchronous round of the window whose committed
candidates are not skipped (SH18c), the replay's commit term is at most
the mean over the `n` candidates of the decision round for the `c_r`
committed ones and the window's top for the rest, which is what the
asynchronous rule attains on the same data under a uniform coin, and
which SH18d bounds below `c_r ≥ n − f − b` under any scheduling.
**SH18g** (`commits_sound`): a candidate the window marks committed is
directly committed on the DAG, so a probe's success is a certificate
quorum the DAG holds: the adversary can suppress the probes' evidence of
the synchronous rule, never manufacture it, the paper's "lower but never
raise". SH18e and SH18f ask `2 ≤ ws < wa`, so that a decision round lies
at or above its slot and an asynchronous round is not read as an
unprobed synchronous one, which the algorithm does when the waves
coincide. **SH18h** (`anchorUpdate_range`): with candidates in
`[1, K]` and a current period there, `anchorUpdate` answers a period in
`[1, K]` at every anchor, the current period or a candidate
(`select_eq_or_mem`), and the failover's `1` is the scan's own (SH10e)
and lies in the range too; the range hypothesis SH10g, SH14b, SH14c and
SH15 place on the update rule, discharged for the paper's rule. **SH18i**
(`commitWeight_eq_commitProb`), the adaptive section's "exact in
expectation" in the part that is a theorem: at a round the window
retains, `committedCount / n` is `commitProb` on the anchor's history
read as a record, since the window marks committed exactly the authors
whose block that record directly commits (`committedCount_eq_card_goodAt`),
at `1 ≤ wa`; the anchor's term is the approximation the paper admits.
**SH18j** (`probe_exists`), the protocol section's canary claim: at a
canary spacing coprime to a candidate period of at least two, which odd
spacings and powers of two are, a window holding two canary rounds whose
decision round it retains holds a probe for the candidate, since two
consecutive multiples of the spacing cannot both be multiples of the
period, at `1 ≤ ws`. What the selection can see of a window whatever
its evidence (`score_le_sum_top`, `sum_floor_le_score`): every score
lies between the sum of a commit floor's excess over the round and the
sum of the delays to the window's top, so at waves `3` and `5` with a
probe at every round, where periods `1` and `2` commit no round below
two or three rounds up (`halfFloor`), they score at least half of what
period `4` can on a window of at most nine rounds, and hysteresis `1/2`
answers period `4` at every anchor of an eight-round interval
(`anchorUpdate_half_retains`), which is finding 3 on the selector
(§8, `RotatingStall.lean`). What leaves such a period is the scan's
failover, not the replay.

What is not modelled: the gating rule that a validator evaluates the
slots of an interval only once the preceding scan has ended, which the
relational form covers, since a validator with no derivation for
interval `j + 1` has no wavelength for its rounds and decides nothing
there; and the replay's expected rounds as expectations of a stochastic
execution, which the paper itself calls an approximation. The
implementation computes those expectations in units of `1/n` with
truncating division, where the model keeps exact rationals, a difference
no result here reads. The failover is the scan's own step, taken on the
state before the rule is consulted, so the update rule is a function of
the anchor block and the period alone, where Barnacle's is handed its
range's verdicts (§21).

## 6. Properties, and the carrier

`Properties.lean` gives the rule a carrier per wavelength function,
`steelheadRule w`, and shows `Agree`, `CommitsCandidate`,
`CommitsDirect`, `Indirect`, `Quorate`, `SelfParent`, `NoEquiv` and
`Persist` at every `w` of at least two rounds, each Mahi-Mahi's fact at
the wave of the slot it concerns, and `Descends` from `Indirect` under
`SpansEligible` at each slot's own wave. `shSupport w` is Mahi-Mahi's
certificate with the certifiers `w r − 1` rounds above a candidate
proposed at `r`; its `Local` and `Commits` laws hold at two rounds and
above, its `OfCoverage` law at three, the wave-three case by the core's
argument and the higher waves by Mahi-Mahi's. The liveness headline
`Support.Lives` follows. `Banded`, `LocalTruncate` and `Safe` are not
claimed (§2).

**SH6** (`Liveness/Statement.lean`) is the timed model at this support:
**SH6a**, a reliably led slot commits in every view caught up to its
decision round on a DAG a reliable quorum has synchronised and populated
through it, by the direct rule, at whichever wave the slot's round
carries; **SH6b**, past
any slot the schedule offers a run of `c` reliably led slots spanning
eligibility, and everything below the run is decided once the DAG is
covered through its decision rounds. At one slot per round `c = wa`
spans. Two clauses of Theorem 2 need no timed model: **SH6c**, a slot
whose leader has no block at its round is directly skipped in every view
holding its vote round, once a quorum populates that round, since no
cone holds a candidate and every block of the round blames; and
**SH6e**, the paper's "partial dissemination alone does not defer": a
candidate that one reliable block references one round up, its leader's
only block at that round, is directly committed in every view holding
its decision round, once the quorum is synchronised from that round and
populates the wave, at `4 ≤ w r`. Synchrony carries the candidate into
every reliable cone from two rounds up, the reliable voters vote for it,
every reliable block at the decision round references all of them and
so certifies. The leader may be Byzantine, so long as it did not
equivocate; neither clause asks the quorum to be correct. **SH6f**,
Theorem 2's Byzantine-led clause as the anchor rule has it: at one slot
per round, a slot is decided once every slot from its floor up to some
reliably led slot is decided, whatever led them. The reliably led slot
commits directly (SH6a), so the least commit at or above the floor is
the anchor, and every slot between, decided but not committed, is a
skip the search passes over (`indirect`). What the hypothesis excludes
is an undecided slot at the floor, one led by an equivocating Byzantine
validator (§7, finding 7). **SH6g** takes the chain of floors itself:
hop from a slot to the first slot at or above its floor the view does
not skip (`FloorHop`), and again from there; if the chain reaches a
reliably led landing in `h` hops, the slot it started from is decided.
Downward induction: the last landing commits (SH6a), and a landing whose
successor commits is decided by SH6f's argument and not skipped, so it
commits in turn and anchors the landing below it. **SH6h** is what
bounds the chain at the implementation's known schedule, `r mod n`: a
validator outside the reliable set `T` leads one residue, which spoils
the `c` windows of `c` consecutive rounds ending at it and no others, so
at `c · (n − |T|) < n` one of the `n` windows a cycle holds is wholly
`T`-led and the schedule repeats it past every round (`FairRunOn T c`);
and one reliable leader sits within `n − |T|` rounds of every round,
since a window of `n − |T| + 1` rounds leads that many distinct
validators. At `c = 3` and `n = 3f + 1` every correct quorum qualifies,
which discharges SH6b's fairness hypothesis for the schedule the
implementation runs; at `c = wa` it does not, so the asynchronous rounds
rest on the coin (SH7, SH14) and not on the schedule. Together with SH6f
this is Theorem 2's Byzantine-led clause as a round count, `w + b + c`
rounds above the floor, where the paper counts `b` hops of the schedule
(§7, finding 7).

## 7. Findings for the paper

1. **The chain must be read at every round.** Reading the chain at the
   asynchronous rounds alone, as the protocol section says, makes the
   chain relation depend on the period at rounds above the interval
   under scan, whose period the scan is to fix; the reference
   implementation reads every round, and the arc follows it. The chain's
   own liveness is then Mahi-Mahi's at the identity schedule, with a run
   of `wa` commits; read at the asynchronous rounds alone the run would
   have to span `⌈wa / k⌉ + 1` of them, a length the paper does not
   state.
2. **The simulator's adversary does not exhibit the stall.** Delaying
   the leader's messages to everyone yields a direct skip, which the
   anchor search passes over. The adversary that delivers the leader
   block to exactly `f + 1` validators produces neither quorum, and it
   is the one the stall needs.
3. **Algorithm 2's selector can retain a stalled period.** At four
   validators, `f = 1`, waves `3` and `5`, `I = 8`, initial and maximum
   period `4`, canary `1` and hysteresis `50%`, all of which the
   implementation accepts, a DAG in which round `r`'s known leader and
   one fixed validator reference all of round `r` while the other two
   omit the leader holds every synchronous slot at two votes and two
   blames while the asynchronous slots commit directly. The replay then
   scores period `4` at most `28` and each alternative at least `15`,
   short of the strict improvement hysteresis demands, so the selector
   answers period `4` at every anchor and the output never passes round
   `2`; a smaller hysteresis escapes this DAG but
   tied windows retain the period even at zero. What leaves such a period
   is the scan's failover (§5), which the implementation applies before
   the rule is consulted and Algorithm 2 itself has no clause for.
   `RotatingStall.lean` (§8) proves the retention at every anchor: on
   that family Algorithm 2 at hysteresis
   `1/2` answers `4` whatever the anchor block, since the window of an
   anchor spans at most nine rounds,
   on which periods `1` and `2` score at least half of what period `4`
   can, and at period `4` slot `3` is never decided, so no block above
   round `2` is ever output. `ReplayStartup.lean` and
   `ReplayShortWindow.lean` show the retention on tied windows; a Rust
   reproduction through 256 rounds is held outside this PR.
4. **Theorem 3's premise on the update rule is neither Algorithm 2's
   rule nor enough.** The theorem assumes that a window in which no
   synchronous slot commits maps to `k = 1`. Algorithm 2 keeps the period
   on a window without a chain commit and otherwise takes the replay's
   argmin under hysteresis and ties toward the larger candidate, of
   which finding 3 is one consequence. Granted anyway, the premise does
   not give liveness: an adversary that lets one synchronous slot above
   the stuck one commit in every window keeps the period while the
   output stays stuck. Read literally it also forces `upd j A 1 = 1`,
   since at period `1` no synchronous slot exists to commit, so it
   forbids every recovery from period `1`. The implementation asks
   nothing of the rule: its scan tests the agreed output's own last
   commit against the anchor's round (§5), which no commit above a stuck
   slot can satisfy, since the agreed output stops at the stuck slot
   (SH10j); a count of commits over the window, which never sees the
   stuck slot below it, cannot read that.
5. **Theorem 2's `O(wa + b)` bound does not hold for every coin
   sequence.** The theorem orders every honest block within `O(wa + b)`
   rounds of its creation after GST. At period `1` every slot is the
   coin's, and a uniform coin names the one absent validator at `N + 1`
   rounds in a row with probability `n^-(N + 1) > 0`, for every horizon
   `N`; on a DAG whose three reliable validators reference one another
   at every round while validator `0` never proposes, no slot below the
   horizon then commits and no settled prefix outputs a block, although
   every reliable round is populated and synchronised from round `0`
   and the reliable round-`1` block exists (`LeanDagTest/Steelhead/
   CoinDelay.lean`, `positive_no_output`). The bound holds in expectation
   or with probability tending to one (SH15), and the ordering itself
   almost surely (SH15c), as the sentence before it in the theorem
   already says of the asynchronous slots, not deterministically; the
   deterministic part of Theorem 2 is the synchronous slots' (SH6a) and
   the crashed leaders' (SH6c).
6. **Lemma 3 counts on the DAG, the replay reads the window.** The
   lemma's proof applies the counting lemma to every candidate at once;
   the counting lemma counts the certificates the DAG holds, and the
   replay counts those the window holds, the anchor's causal history at
   the rounds `round A − I` and above. The history holds a quorum's worth of blocks
   at every round, by quorum references, but not necessarily one quorum's
   blocks at both the boost round and the decision round, which the
   counting lemma reads; under asynchrony an anchor's references may omit
   any `f` validators' blocks at each round. SH18d states the lemma for
   the window under the hypothesis that a quorum has populated both
   rounds within the anchor's history, which synchrony from below the
   window gives and which the paper's "whose wave rounds are populated"
   should be read to mean.
7. **An equivocating Byzantine leader at the floor is the anchor.**
   Theorem 2 says an asynchronous slot whose Byzantine leader equivocates
   "is decided by its anchor once the first honest-led slot above its
   floor commits, at most `b` slots higher". The anchor search stops at
   the first commit-or-undecided slot at or above the floor, and a slot
   whose leader equivocates is undecided, two votes each way forming
   neither quorum; so when the slot at the floor is led by an
   equivocating Byzantine validator, the search waits on it, whatever
   commits above. `LeanDagTest/Steelhead/ByzantineFloor.lean` shows it at
   wave `3` on thirty blocks: validator `0` leads slots `0` and `3` and
   equivocates at both, the honest-led slot `4` commits directly, and
   slot `0` is undecided in the full view. The chain of floors advances
   one wave a hop and the same Byzantine validator may lead every hop,
   with probability `b / n` each under the coin, so what decides such a
   slot is a run of reliably led slots above its floor (SH6b, SH9), or
   one reliably led slot above the floor with every slot between
   decided (SH6f), or a chain of floors reaching a reliably led landing
   (SH6g), and no bound in `b` alone holds. At the implementation's
   round-robin schedule what does hold is a round count: a reliable
   leader sits within `n − |T|` rounds of every round and a reliable run
   of three past every round, at `n = 3f + 1` (SH6h).
8. **`I ≥ 2 · maxPeriod` does not make a window hold a wave.** The
   adaptive section bounds the interval so that every window holds two
   asynchronous slots, and asks nothing else of it. A window holds
   `I + 1` rounds, `round A − I` to `round A`, so an asynchronous round
   of period `k` has its decision round inside it only when
   `I ≥ k + wa − 2`. At `I = 4`,
   `maxPeriod = 2` and `wa = 5` the bound holds and that one does not:
   on `rw44` (§8) the window of the anchor at round `7` holds two
   asynchronous rounds of period `2` and the decision round of neither,
   so the replay resolves no asynchronous slot at any candidate and pays
   the window's top for each, both candidates tie and the period never
   moves at any hysteresis, while the window of the anchor one round
   lower does hold the decision round of its asynchronous slot at round
   `2`: what the replay sees turns on where the anchor fell. The bound
   the replay needs is `I ≥ max(2 · maxPeriod, maxPeriod + wa − 2)`
   (SH10k); the campaigns' `I = 128` satisfies it,
   the paper's constraint does not state it.

## 8. Witnesses (`LeanDagTest/Steelhead/`), SH12

`Model.lean`: the wavelength arithmetic, the per-slot floors, the direct
rules at each slot's own wave, the anchor route for the asynchronous slot
through a synchronous one, the chain on data, and the anchor-floor
counterexample (§3). `Period.lean`: the state derived over two
intervals at a concrete doubling update rule, which pins `intervalOf`'s
boundary convention, the window's first round at three anchors, the
history of a round-`7` block deciding slots `0` and `1`, so that an
advance from slot `1` over that anchor passes it and carries its
leader's round, the adaptive schedule naming the known leader at a
synchronous round and the coin at the asynchronous ones, and a block map
read back at the rounds of its blocks (§5). `Stall.lean`: the adversary's shape on valid
data, the asynchronous commit beside it, and the stalled slot by SH8
(§4). `CoinDelay.lean`: the reliable-only DAG at every horizon, populated
and synchronised from round `0`, on which the coins naming the absent
validator through the horizon, a set of positive probability, leave
every settled prefix of every view empty (§7, finding 5).
`ByzantineFloor.lean`: seven rounds at wave `3` on which validator `0`
leads slots `0` and `3` and equivocates at both, so that each has two
votes each way and neither quorum; the honest-led slot `4` commits
directly and slot `0` stays undecided, its anchor search waiting on the
undecided floor (§7, finding 7). `Replay.lean`: Algorithm 2 on the
window of `sh8`'s round-`7` block, where period `1` scores `18` and
period `8` scores `11`, so the replay recovers from period `1` at
hysteresis `1/10` and stays there at `1/2`, and the selection's ties on
data (§5). `ReplayStartup.lean`: nine rounds with every synchronous slot
at two votes and two blames, whose first anchor's window holds one
asynchronous round and no synchronous commit, certificate or skip; every
candidate scores `6` and Algorithm 2 keeps period `4` at hysteresis `0`
and `1/10` (§7, findings 3 and 4). `ReplayShortWindow.lean`: eleven such
rounds at `I = 4`, `maxPeriod = 2`, where the window of the anchor at
round `7` holds two asynchronous rounds of period `2` and the decision
round of neither, while the window one anchor lower holds its own; both
candidates score `10` and
Algorithm 2 keeps period `2` at every hysteresis (§7, finding 8).
`RotatingStall.lean`: the family `rtDag N` at every horizon `N`, the
known leader rotating and every synchronous slot at two votes and two
blames, on which Algorithm 2 at interval `8`,
candidates `[1, 2, 4]`, a probe at every round and hysteresis `1/2`
answers period `4` at every anchor (`rt_update_four`, from
`anchorUpdate_half_retains`: periods `1`
and `2` score at least half of what period `4` can on a window of at
most nine rounds), at period `4` slot `3` is never decided in any view
for any coin (`rt_stall`, SH8), at any period sequence that is `4` on
the intervals the record reaches the adaptive output never decides it
either (`rt_adaptive_stall`, by `decided_congr`), no settled prefix has
more than three slots and no block above round `2` is ever in the ledger
(`rt_no_output_above_two`), while validator `1`'s honest round-`3` block
exists (§7, finding 3). `Axioms.lean`: the eight headline theorems, the
carrier's persistence and its liveness headline depend on the standard
axioms only.

## 9. Layout

```
LeanDag/Steelhead/
  Model/Wavelength.lean     periodic, IsAsync
  Model/Decision.lean       steelheadAnchored, Decided, FloorHop
  Model/Chain.lean          chainSlots, ChainDecided
  Model/Period.lean         intervalOf, UpdateRule, windowBottom, IntervalAnchor, NoAnchor,
                            ScanState, AgreedAdvance, PeriodAt, adaptiveWave, adaptiveSlots
  Model/Coin.lean           commitProb, noCommitProb, blockRound, coinOfBlocks, blockCoins,
                            blocksHorizon, Matches, Settles, undecidedProb, NonAnticipating,
                            undecidedProbAgainst, coinMeasure
  Model/Compose.lean        compose
  Model/Replay.lean         Evidence, Config, Timing, windowIds, ofAnchor, committedCount,
                            probeRate, timingAt, firstCommitAt, gateAt, score, prefer, best,
                            select, candidatesUpto, update, anchorUpdate
  Safety/Statement.lean     SH1–SH5        Safety/Proof.lean
  Liveness/Statement.lean   SH6–SH9        Liveness/Proof.lean
  Period/Statement.lean     SH10, SH14     Period/Proof.lean
  Coin/Statement.lean       SH11, SH15     Coin/Proof.lean
  Ledger/Statement.lean     SH13           Ledger/Proof.lean
  Interface/Statement.lean  SH16           Interface/Proof.lean
  Broadcast/Statement.lean  SH17           Broadcast/Proof.lean
  Replay/Statement.lean     SH18           Replay/Proof.lean
  Helpers/*.lean            the lemma layers
  Properties.lean           the carrier, its properties and support
LeanDagTest/Steelhead/
  Model.lean  Period.lean  Stall.lean  CoinDelay.lean  ByzantineFloor.lean  Replay.lean
  ReplayStartup.lean  ReplayShortWindow.lean  RotatingStall.lean  Axioms.lean
```

`scripts/check-arc-holes.py` enforces the partition: `Statement.lean`
files are proof-free, `Model/` files theorem-free (instances excepted),
and no synchrony name appears under `Properties/`.
