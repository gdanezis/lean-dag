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
  under coverage, everything below a fair run is decided, a slot whose
  leader has no block is skipped once a quorum blames it (SH6c), and a
  candidate one reliable block references one round up commits under
  synchrony whether or not its leader is reliable (SH6e). The paper's
  Theorem 2, for the decision relation.
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
- **SH10, the period** (§5): the period sequence is agreed across views
  under any update rule, so is the output under the adaptive wavelength
  over the intervals the record's rounds fall in; the scan of an
  interval ends once its chain verdicts are in, and under the clause it
  ends for every interval; under the failover an anchored interval the
  view did not output hands the next one period `1` (SH10e); every
  interval holds two asynchronous rounds and the period stays in its
  range (SH10f, SH10g); and the failover wrapped around any update rule
  satisfies its clause (SH10h). Theorem 4, the period half of
  Theorem 3 (i), and the adaptive section's structural claims.
- **SH11, the coin** (§4): with a uniform coin the chain slot of a
  round commits with probability `|good| / n`, at least `(n − f − b) / n`
  by MM2 at `wa ≥ 5` and so at least `1/3`, and at least `1/n` at
  `wa ≥ 4` (SH11e); over `m` rounds the probability that no round's coin
  names a directly committed leader is at most `((f + b) / n)^m`, which
  tends to zero. The probability half of Theorem 3 (i), in Mathlib's
  `PMF`. And Theorem 3's "with probability `1`" in the form a finite
  record admits (SH15): over the coins of `M` blocks of `K` rounds, one
  opening each interval after a slot's, the slot stays undecided under
  the failover with probability at most
  `2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)`, which tends to zero.
- **SH12, on data** (§8): the anchor-floor counterexample, the stall DAG
  with its asynchronous commit beside it, and the period sequence at a
  concrete update rule.
- **SH13, the ledger** (§3): the committed-leader sequence and the
  ledger of a settled prefix are agreed across views, the ledger is
  monotone, and a block enters at one slot, which both views name. The
  paper's Corollary 2, order and integrity.
- **SH14, output liveness under the failover** (§5): under the failover
  that stands in for Theorem 3's premise on the update rule (§7), a slot
  below an anchored interval is decided once a run of `wa` coin-led
  commits above that interval is in view: an undecided slot sits below
  every commit of every later interval, so the failover fires at each
  anchored one and the period is `1` from the first, where the run
  decides everything below it. Theorem 3 (ii) and the asynchronous half
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
  enter at the same slots in every view, so in the same order. The
  liveness half is SH6b, SH14b and SH15.
- **SH18, the replay** (§5): Algorithm 2 as data, the window's evidence
  read from the anchor's causal history, the three passes and the
  hysteretic selection; the selection stays among the candidates and
  never worsens the score, the window's evidence is consistent, and
  Lemma 3's count holds on the window once a quorum has populated the
  boost and decision rounds within it.

### 0.1 Correspondence with the paper

| paper | here | remark |
| :--- | :--- | :--- |
| Definition 1 (atomic broadcast) | SH17, with SH6b, SH14b, SH15 | agreement, integrity and total order over settled prefixes, validity after GST with the first committed reliable leader two rounds up; the "eventually" is SH6b under synchrony and SH14b/SH15 under asynchrony, where the delivery of a reliable block to the coin's leaders is the substrate's and is stated as `SynchronisedOn` only. The order of the blocks one commit releases is not modelled |
| Lemma 1 (certificate uniqueness; a skipped block is never certified) | SH1a, SH1b | Mahi-Mahi's lemmas at the slot's wave |
| Lemma 2 (quorum intersection across the wave) | SH1c | at `r + w r`, whatever the block's own wave |
| Corollary 1 (handover) | SH3 | stated against the relation's anchor search |
| Theorem 1 (agreement) | SH2, SH16 | `AnchoredRule.decided_unique` at Steelhead's laws; at the interface level, any family of rules whose laws hold composes into one whose laws hold, and Steelhead is the composite of Mahi-Mahi's rule at each round's wave |
| Corollary 2 (total order and integrity) | SH13 | in part: the relation's own ledger theorems at Steelhead's laws, over a settled prefix. Ordering the blocks a single commit releases is declined development-wide (report §1.4, §5.6) |
| Theorem 2 (liveness under partial synchrony) | SH6a, SH6b, SH6c, SH6e | in part: the honest-leader direct commit, everything below a fair run, the crashed-leader skip from `n − f` blames, and the remark that partial dissemination does not defer, for a leader that did not equivocate. The Byzantine-equivocation anchor bound is not formalised; the `O(wa + b)` ordering bound fails for some coin sequences at period `1` (§7, finding 6) and is stated only as SH15's tail; timeouts and pacing are not modelled |
| Theorem 3 (i) (the chain resolves, the period reaches `1`) | SH7a, SH7c, SH10c, SH10d, SH10e, SH11 | the chain settles under Mahi-Mahi's run clause and below any one run of `wa` good coins, a period is derived for each interval, an anchored interval the view did not output hands the next one period `1` under the failover, which the arc models in place of the paper's premise on the update rule (§7), and the coin is modelled by its effect and as a `PMF`, at `wa ≥ 5` and at `wa ≥ 4`. The "with probability `1`" is SH15's tail |
| Theorem 3 (ii) (at period `1` the ledger grows) | SH9, SH9b, SH14, SH14b, SH14c, SH15 | SH9b at period `1` under the run clause at the output schedule and below its horizon; SH14 for the adaptive output under the failover, given one anchored interval past the slot and one run of `wa` good coins above it; SH14b reads both off the run clause at the chain schedule, SH14c off two runs of the coin; SH15 bounds the probability that the two runs fail among `M` blocks of coins by `2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)`, which tends to zero. The "with probability `1`" is that tail, as a finite record admits it; the growth of the ledger from the settled prefix is SH13 |
| Theorem 4 (agreement of the period) | SH10a, SH10b | for any deterministic update rule |
| Adaptive section, `I ≥ 2 · maxPeriod` and `1 ≤ k ≤ maxPeriod` | SH10f, SH10g | two asynchronous rounds per interval at any `k ≥ 1` with `2k ≤ I`; the period stays in range when the initial period does and the update rule keeps it there |
| Protocol section, "whenever either verdict of an asynchronous slot is direct, the two coincide" | SH5b | predicate for predicate, at a slot proposed at its own round and led by the coin |
| Protocol section, "the successor waits at most `max(0, wa − ws − 1)` rounds", "delays never compound" | SH9c | arithmetic on the decision rounds; output timing itself is not modelled |
| Theorem 5 (conservativity) | SH4 | at a constant wavelength by `rfl`, period `1` by `Nat.mod_one`, and at wave three the derivations are exactly the core's, both directions |
| Lemma 3 (the replay cannot be starved) | SH11a, SH18d | `c_r ≥ n − f − b` on the DAG under any scheduling (SH11a), and on the window once a quorum has populated the boost and decision rounds within it (SH18d), which is what "populated" must mean for the replay, whose evidence is the window's (§7, finding 7). The replay's asynchronous term averages over the `n` candidates, so at least that fraction of them decide at the decision round; the arithmetic of the score's passes is not proved |
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

**Atomic broadcast.** Definition 1's four clauses, as **SH17**
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
(SH13d). The "eventually" of agreement and validity is the liveness
half: SH6a and SH6b under synchrony, SH14b and SH15 under asynchrony,
where a reliable block reaches the coin's committed leaders by the
substrate's delivery, which the model states as `SynchronisedOn` and
not otherwise. The order of the blocks one commit releases is a
tie-break the development does not assume (report §1.4).

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
`j₀ + 1 + j` past the slot's interval `j₀` (`blockRound`, `coinOfBlocks`,
which reads the blocks back and draws a fixed value elsewhere), uniformly
and independently, and measures the maps under which some view holding
the horizon (`blocksHorizon`), having derived its periods under the
failover, leaves the slot undecided at the adaptive wavelength and
schedule. **SH15a** (`undecidedProb_le`) bounds it by
`2 · ((n^K − (n − f − b)^K) / n^K)^(M/2)` at `2 ≤ ws ≤ wa`, `5 ≤ wa ≤ K
≤ I`, periods kept in `[1, K]`, and the blocks' waves populated where MM2
reads them: a good block in each half of the `M` decides the slot by
SH14c, the earlier one anchoring its interval and the later one the run
above it, so the failure set lies in the union of the two halves'
no-good-block sets, and each of those is a product whose every block of
the half misses its all-good maps, of which MM2 counts at least
`(n − f − b)^K` out of `n^K` (`no_good_block_prob_le`). **SH15b**
(`undecided_tail_tendsto_zero`) is that the bound vanishes as `M` grows,
since `n − f − b ≥ 1`. The blocks' coins are drawn after the record is
fixed, as SH11c's are: the adversary that shapes the DAG does not see
them, which is the coin's unpredictability; what the network must supply
is that the blocks' waves be populated.

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
each decided under one period. The **anchor** of interval `j` under
period `k` is a round of the interval, asynchronous under `k`, whose
chain verdict is a commit, every asynchronous round of the interval
below it chain-skipped (`IntervalAnchor`); **no anchor** is every such
round chain-skipped (`NoAnchor`). The period sequence is a relation,
`PeriodAt I wa coin upd k₀ U V j k`: interval `0` runs at `k₀`; interval
`j + 1` runs at `upd j A k` when `A` anchors interval `j` under `k`, and
at `k` when `j` has no anchor. A validator whose scan meets a
chain-undecided round waits, which is the absence of a derivation. The
update rule `upd : ℕ → BlockId → ℕ → ℕ` is any function of the interval
index, the anchor block and the current period; the paper's replay reads
the anchor's causal history, which the block id determines within one
universe. `adaptiveWave ws wa I per` is the wavelength function a
validator that derived `per` runs the output relation at, and
`adaptiveSlots coin known I per` the schedule it runs it on: one slot per
round, the coin at the rounds `per` makes asynchronous and the known
schedule `known` elsewhere. The claims that relate a schedule to the coin
one clause at a time (SH14) take this schedule as their instance (SH15).

`Period/Statement.lean`:

- **SH10a, agreement of the period**: two views deriving a period for
  interval `j` derive the same one, at `3 ≤ wa`, under any update rule.
  Induction on the derivation: the anchor is unique across views, since
  a lower anchor in one view is a chain-skipped round in the other and
  SH5 forbids it, and an anchor in one view against none in the other
  is the same contradiction.
- **SH10b, agreement of the output under the adaptive wavelength**: two
  validators that derived the period of every interval the record's
  rounds fall in, and decided a slot proposed among them at their own
  adaptive wavelengths, agree on the verdict. The sequences coincide
  there by SH10a; a verdict reads the wavelength only at the rounds of
  the slots its derivation names, all of them at or below the round of
  the anchor block it rests on (`decided_congr`); and SH2 applies to the
  one function. The bound is not a convenience: a record holds finitely
  many blocks, so above its top round no chain verdict is derivable and
  no period beyond it either, and a claim asking for the *whole*
  sequence would hold only where the period reaches `0`, which is
  Mysticeti at every round but the first.
- **SH10c, the scan ends**: once every asynchronous round of the
  interval has a chain verdict in a view, the view derives the next
  period: the least chain-committed round is the anchor, or every round
  is chain-skipped.
- **SH10d, the period advances under the clause**: under Mahi-Mahi's
  run clause at the chain schedule, a view caught up to the horizon
  derives a period for every interval whose rounds lie far enough below
  it, by SH7a at each interval and SH10c.
- **SH10e, the period reaches `1`**: under the failover, which the arc
  models in place of Theorem 3's premise on the update rule (§7).
  `ResetsOnNoOutput` (`Model/Period.lean`) asks the update to answer `1`
  at an anchor whose causal history, read at the wavelength the validator
  runs, shows no output of the interval: every slot of the interval
  committed there sits above a slot the history leaves undecided. Under
  it, an interval that finds an anchor, and of which the view output
  nothing, hands the next interval period `1`; the view's verdicts carry
  into the anchor's history and back through the laws, which is why the
  claim asks `2 ≤ ws` and `2 ≤ wa`. The anchor is a hypothesis: nothing
  deterministic forces one when `k > wa`, and its existence is the
  almost-sure half (§0.1). At period `1` the clause fires only when
  nothing was output, so period `1` is not absorbing, where the paper's
  premise read literally forces `upd j A 1 = 1` (§7).
- **SH10f, SH10g, the shape of the adaptive run**: at any period `k ≥ 1`
  with `2k ≤ I`, every interval holds two asynchronous rounds, the
  paper's reason for `I ≥ 2 · maxPeriod`; and if the initial period lies
  in `[1, K]` and the update rule keeps a period there, so does every
  derived period.
- **SH10h, the failover satisfies its clause**: `failover U w I upd`
  (`Model/Period.lean`) answers `1` at an anchor whose causal history,
  read at `w`, shows no output of the interval, and `upd`'s own answer
  elsewhere; it satisfies `ResetsOnNoOutput` by construction, whatever
  `upd` is, so the paper's replay with the agreed failover is a rule the
  liveness claims apply to. The wrapper is classical, its test being a
  proposition on verdicts.
- **SH14, output liveness under the failover**: in a view that derived
  every period up to a run's last round, if some interval past a slot's
  finds an anchor, and above that interval the coin names a committed
  candidate at `wa` consecutive rounds that lead the output's slots
  there, then the slot is decided once the view holds the run's decision
  rounds. If the slot were undecided it would sit below every commit of
  every later interval, so SH10e fires at the anchored one and, by
  induction on the derivations, every interval up to the run runs at
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
  (`c + K ≤ I`). A run of `K` consecutive rounds inside the interval
  after the slot's holds a multiple of whatever period is in force, so an
  asynchronous round with a good coin, which the view chain-commits
  directly; SH7a settles every chain verdict of the interval, so that
  round or a lower chain-committed one is the anchor. The run in the next
  interval is the one SH14 needs. Every slot whose interval lies two
  intervals and a window below the horizon is then decided, in a view
  caught up to the horizon that derived every period below it. The clause
  with runs of `K` in every window is the deterministic stand-in for what
  the coin gives almost surely, as SH7a's is.
- **SH14c, output liveness from two good runs**: SH14 with its two
  events named as runs of the coin alone. `K` good coins opening an
  interval past the slot's hit an asynchronous round under whatever
  period is in force, which the view chain-commits directly; `wa` good
  coins above that interval settle every chain verdict below them
  (SH7c), so the interval has its anchor, and they are the run SH14
  needs. At `K ≤ I`, so that a block of `K` rounds fits in an interval.
  Two runs at named places, each of a fixed positive probability: the
  form SH15 draws from the coin.

**The replay** (`Model/Replay.lean`, `Replay/Statement.lean`). Algorithm
2 as data: `ofAnchor U A I` reads the window's evidence off the anchor's
causal history over the last `I` rounds, per proposal round, wave and
candidate author, counting distinct validators (a candidate is committed
when a quorum certify it within the window, skipped when a quorum of the
window's vote-round blocks blame the author's slot, certified when the
window holds one certificate); `score` is `REPLAY(W, k')`'s three passes
over that evidence, in exact rationals, the probes of the canary rounds
(`probeRate`) standing in for the unprobed synchronous slots; `select`
is the hysteretic selection, ties keeping the current period and then
favouring the larger candidate; `anchorUpdate` is the whole as an
`UpdateRule`. **SH18a, b** (`select_mem`, `select_score_le`): the
selection stays among the candidates and never worsens the score.
**SH18c** (`certified_of_commits`, `not_certified_of_skips`): in the
window's evidence a committed candidate is certified and a skipped one
is not, at `2 ≤ w`. **SH18d** (`window_count`): Lemma 3's count on the
window: at a round the window retains whose boost round and decision
round a quorum has populated *within the anchor's history*, at least
`n − f − b` authors are marked committed at wave `wa`, MM2 read on the
history as a record of its own, whose votes and certificates are the
universe's restricted to it (`candidatesAt_toRecord`,
`certificates_toRecord`). The replay's asynchronous term averages over
the `n` candidates, so at least that fraction decide at the decision
round; the arithmetic of the passes is not proved. The hypothesis that
the quorum's blocks lie in the window is §7's finding 7.

What is not modelled: the gating rule that a validator evaluates the
slots of an interval only once the preceding scan has ended, which the
relational form covers, since a validator with no derivation for
interval `j + 1` has no wavelength for its rounds and decides nothing
there; and the replay's expected rounds as expectations of a stochastic
execution, which the paper itself calls an approximation. The failover
is a clause on the update rule (`ResetsOnNoOutput`) and the wrapper
`failover` that satisfies it; wrapped around `anchorUpdate` it is the
rule the authors agreed to.

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
through it, at whichever wave the slot's round carries; **SH6b**, past
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
equivocate; neither clause asks the quorum to be correct.

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
3. **The stall's threshold is `k ≥ ws`, not `k ≥ 2`.** The proofs
   section states the stall at every period of at least two. At `ws = 3`
   and `k = 2` the synchronous slots sit at odd rounds, whose floor
   `r + 3` is even and so asynchronous; that slot commits directly under
   the adversary's own construction, so the stretch below a commit is
   that one asynchronous slot, holds no synchronous slot, and the slot
   decides indirectly. The claim does hold at `ws = 2`, where `r + 2`
   preserves parity, so the sentence is true for one pair and false for
   the other. SH8 states the condition the argument needs, `2 ≤ ws ≤ k`.
   Unlike the two above, this is an error in the paper's sentence rather
   than a place where the arc departs from it.
4. **Algorithm 2's selector can retain a stalled period.** At four
   validators, `f = 1`, waves `3` and `5`, `I = 8`, initial and maximum
   period `4`, canary `1` and hysteresis `50%`, all of which the
   implementation accepts, a DAG in which round `r`'s known leader and
   one fixed validator reference all of round `r` while the other two
   omit the leader holds every synchronous slot at two votes and two
   blames while the asynchronous slots commit directly. The replay then
   scores period `4` at most `28` and each alternative at least `15`,
   short of the strict improvement hysteresis demands, so the period
   never drops and the output never passes round `2`, at every horizon
   and for every coin schedule; a smaller hysteresis escapes this DAG but
   tied windows retain the period even at zero. The arc therefore models
   the failover of §5 in place of the selector's own reset: an interval
   that was not output hands the next one period `1`, whatever the
   scores. Algorithm 2 has no such clause; the paper's authors have
   agreed to add one. The Lean witness of the stall and a Rust
   reproduction through 256 rounds are held outside this PR.
5. **Theorem 3's premise on the update rule is neither Algorithm 2's
   rule nor enough.** The theorem assumes that a window in which no
   synchronous slot commits maps to `k = 1`. Algorithm 2 keeps the period
   on a window without a chain commit and otherwise takes the replay's
   argmin under hysteresis and ties toward the larger candidate, of
   which finding 4 is one consequence. Granted anyway, the premise does
   not give liveness: an adversary that lets one synchronous slot above
   the stuck one commit in every window keeps the period while the
   output stays stuck. Read literally it also forces `upd j A 1 = 1`,
   since at period `1` no synchronous slot exists to commit, so it
   forbids every recovery from period `1`. The failover reads the
   sequenced output in the anchor's history instead (§5), which no
   commit above a stuck slot can satisfy; the same holds of a count of
   commits over a replay window, which never sees the stuck slot below
   the window.
6. **Theorem 2's `O(wa + b)` bound does not hold for every coin
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
   or with probability tending to one (SH15), as the sentence before it
   in the theorem already says of the asynchronous slots, not
   deterministically; the deterministic part of Theorem 2 is the
   synchronous slots' (SH6a) and the crashed leaders' (SH6c).
7. **Lemma 3 counts on the DAG, the replay reads the window.** The
   lemma's proof applies the counting lemma to every candidate at once;
   the counting lemma counts the certificates the DAG holds, and the
   replay counts those the window holds, the anchor's causal history
   over the last `I` rounds. The history holds a quorum's worth of blocks
   at every round, by quorum references, but not necessarily one quorum's
   blocks at both the boost round and the decision round, which the
   counting lemma reads; under asynchrony an anchor's references may omit
   any `f` validators' blocks at each round. SH18d states the lemma for
   the window under the hypothesis that a quorum has populated both
   rounds within the anchor's history, which synchrony from below the
   window gives and which the paper's "whose wave rounds are populated"
   should be read to mean.

## 8. Witnesses (`LeanDagTest/Steelhead/`), SH12

`Model.lean`: the wavelength arithmetic, the per-slot floors, the direct
rules at each slot's own wave, the anchor route for the asynchronous slot
through a synchronous one, the chain on data, and the anchor-floor
counterexample (§3). `Period.lean`: the period sequence derived over two
intervals at a concrete doubling update rule, which pins `intervalOf`'s
boundary convention, the failover's premise on data, satisfied by
the constant rule `1` and refuted at an anchor whose history has output
the interval, the adaptive schedule naming the known leader at a
synchronous round and the coin at the asynchronous ones, and a block map
read back at the rounds of its blocks (§5). `Stall.lean`: the adversary's shape on valid
data, the asynchronous commit beside it, and the stalled slot by SH8
(§4). `CoinDelay.lean`: the reliable-only DAG at every horizon, populated
and synchronised from round `0`, on which the coins naming the absent
validator through the horizon, a set of positive probability, leave
every settled prefix of every view empty (§7, finding 6). `Axioms.lean`: the five headline theorems, the carrier's
persistence and its liveness headline depend on the standard axioms
only.

## 9. Layout

```
LeanDag/Steelhead/
  Model/Wavelength.lean     periodic, IsAsync
  Model/Decision.lean       steelheadAnchored, Decided
  Model/Chain.lean          chainSlots, ChainDecided
  Model/Period.lean         intervalOf, ResetsOnNoOutput, failover, IntervalAnchor, NoAnchor,
                            PeriodAt, adaptiveWave, adaptiveSlots
  Model/Coin.lean           commitProb, noCommitProb, blockRound, coinOfBlocks, blocksHorizon,
                            undecidedProb
  Model/Compose.lean        compose
  Model/Replay.lean         Evidence, Config, Timing, windowIds, ofAnchor, probeRate, timings,
                            firstCommits, score, prefer, best, select, update, anchorUpdate
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
  Model.lean  Period.lean  Stall.lean  Axioms.lean
```

`scripts/check-arc-holes.py` enforces the partition: `Statement.lean`
files are proof-free, `Model/` files theorem-free (instances excepted),
and no synchrony name appears under `Properties/`.
