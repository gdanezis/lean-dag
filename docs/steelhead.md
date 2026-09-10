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
  under coverage, and everything below a fair run is decided. The
  paper's Theorem 2, for the decision relation.
- **SH7, chain liveness** (§4): under Mahi-Mahi's run clause at the
  chain schedule every chain verdict below a run is settled, and under
  synchrony without the clause. The chain half of Theorem 3 (i).
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
  ends for every interval; under the paper's premise on the update rule
  an anchored interval hands the next one period `1` (SH10e); every
  interval holds two asynchronous rounds and the period stays in its
  range (SH10f, SH10g). Theorem 4, the period half of Theorem 3 (i), and
  the adaptive section's structural claims.
- **SH11, the coin** (§4): with a uniform coin the chain slot of a
  round commits with probability `|good| / n`, at least `(n − f − b) / n`
  by MM2 at `wa ≥ 5` and so at least `1/3`, and at least `1/n` at
  `wa ≥ 4` (SH11e); over `m` rounds the probability that no round's coin
  names a directly committed leader is at most `((f + b) / n)^m`, which
  tends to zero. The probability half of Theorem 3 (i), in Mathlib's
  `PMF`.
- **SH12, on data** (§8): the anchor-floor counterexample, the stall DAG
  with its asynchronous commit beside it, and the period sequence at a
  concrete update rule.
- **SH13, the ledger** (§3): the committed-leader sequence and the
  ledger of a settled prefix are agreed across views, the ledger is
  monotone, and a block enters at one slot, which both views name. The
  paper's Corollary 2, order and integrity.

### 0.1 Correspondence with the paper

| paper | here | remark |
| :--- | :--- | :--- |
| Lemma 1 (certificate uniqueness; a skipped block is never certified) | SH1a, SH1b | Mahi-Mahi's lemmas at the slot's wave |
| Lemma 2 (quorum intersection across the wave) | SH1c | at `r + w r`, whatever the block's own wave |
| Corollary 1 (handover) | SH3 | stated against the relation's anchor search |
| Theorem 1 (agreement) | SH2 | `AnchoredRule.decided_unique` at Steelhead's laws |
| Corollary 2 (total order and integrity) | SH13 | in part: the relation's own ledger theorems at Steelhead's laws, over a settled prefix. Ordering the blocks a single commit releases is declined development-wide (report §1.4, §5.6) |
| Theorem 2 (liveness under partial synchrony) | SH6a, SH6b | in part: the honest-leader direct commit, and everything below a fair run. The crashed-leader skip from `n − f` blames, the Byzantine-equivocation anchor bound and the `O(wa + b)` ordering bound are not formalised; timeouts and pacing are not modelled |
| Theorem 3 (i) (the chain resolves, the period reaches `1`) | SH7a, SH10c, SH10d, SH10e, SH11 | in part: the chain settles under Mahi-Mahi's run clause, a period is derived for each interval, an anchored interval whose synchronous slots hold no certified candidate hands the next one period `1` under the paper's premise on the update rule, and the coin is modelled by its effect and as a `PMF`, at `wa ≥ 5` and at `wa ≥ 4`. Nothing yet derives the run clause or the anchor's existence from the coin: the "with probability `1`" is stated only as the vanishing tail SH11c/d |
| Theorem 3 (ii) (at period `1` the ledger grows) | SH9, SH9b | under the run clause at the output schedule and below its horizon; the clause itself is what the coin is to supply |
| Theorem 4 (agreement of the period) | SH10a, SH10b | for any deterministic update rule |
| Adaptive section, `I ≥ 2 · maxPeriod` and `1 ≤ k ≤ maxPeriod` | SH10f, SH10g | two asynchronous rounds per interval at any `k ≥ 1` with `2k ≤ I`; the period stays in range when the initial period does and the update rule keeps it there |
| Protocol section, "whenever either verdict of an asynchronous slot is direct, the two coincide" | SH5b | predicate for predicate, at a slot proposed at its own round and led by the coin |
| Protocol section, "the successor waits at most `max(0, wa − ws − 1)` rounds", "delays never compound" | SH9c | arithmetic on the decision rounds; output timing itself is not modelled |
| Theorem 5 (conservativity) | SH4 | in part: at a constant wavelength by `rfl`, period `1` by `Nat.mod_one`; the wave-three end is one inclusion, where the paper says "exactly" |
| Lemma 3 (the replay cannot be starved) | its counting half, `card_goodAt_of_populated` and SH11a | `c_r ≥ n − f − b` under any scheduling; the bridge to the replay's score is not modelled, since the replay is not |
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
`3` every derivation is the core's (MM1d transported).

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
  `Nat.mod_one`; at the constant `3` every derivation is the core's.
- **SH5, chain agreement**: the chain verdicts (§4) agree across views,
  an instance of MM1c at the chain schedule.
- **SH5b, the direct verdicts coincide**: at an asynchronous round whose
  slot is proposed there and led by the coin, the output's direct commit
  and direct skip are the chain's predicates, so a direct derivation in
  either relation is one in the other. The protocol section's "whenever either verdict of an
  asynchronous slot is direct, the two coincide"; only the indirect
  verdicts may differ, and §4 says why.

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
a run of `wa` chain commits suffices), and liveness under synchrony
without any clause (**SH7b**, the core's L10 at Mahi-Mahi's support).

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
the two quantities `Model/Coin.lean` defines.

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
validator that derived `per` runs the output relation at.

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
- **SH10e, the period reaches `1`**: Theorem 3's premise on the update
  rule, "a window in which no synchronous slot commits maps to `k = 1`",
  is the clause `ResetsOnStall` (`Model/Period.lean`): when no
  synchronous slot of interval `j` under period `k` has a certified
  candidate, the update at any anchor of `j` is `1`. Under it, and with
  no synchronous slot of the interval holding a certified candidate
  (SH8's adversary within the interval), an interval that finds an anchor
  hands the next interval period `1`. The anchor is a hypothesis: nothing
  deterministic forces one when `k > wa`, and its existence is the
  almost-sure half (§0.1).
- **SH10f, SH10g, the shape of the adaptive run**: at any period `k ≥ 1`
  with `2k ≤ I`, every interval holds two asynchronous rounds, the
  paper's reason for `I ≥ 2 · maxPeriod`; and if the initial period lies
  in `[1, K]` and the update rule keeps a period there, so does every
  derived period.

What is not modelled: the replay itself, the canary rounds and the
probes, hysteresis, and the gating rule that a validator evaluates the
slots of an interval only once the preceding scan has ended. The
relational form covers the last: a validator with no derivation for
interval `j + 1` has no wavelength for its rounds and decides nothing
there.

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
spans.

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

## 8. Witnesses (`LeanDagTest/Steelhead/`), SH12

`Model.lean`: the wavelength arithmetic, the per-slot floors, the direct
rules at each slot's own wave, the anchor route for the asynchronous slot
through a synchronous one, the chain on data, and the anchor-floor
counterexample (§3). `Period.lean`: the period sequence derived over two
intervals at a concrete doubling update rule, which pins `intervalOf`'s
boundary convention (§5). `Stall.lean`: the adversary's shape on valid
data, the asynchronous commit beside it, and the stalled slot by SH8
(§4). `Axioms.lean`: the five headline theorems, the carrier's
persistence and its liveness headline depend on the standard axioms
only.

## 9. Layout

```
LeanDag/Steelhead/
  Model/Wavelength.lean     periodic, IsAsync
  Model/Decision.lean       steelheadAnchored, Decided
  Model/Chain.lean          chainSlots, ChainDecided
  Model/Period.lean         intervalOf, ResetsOnStall, IntervalAnchor, NoAnchor, PeriodAt,
                            adaptiveWave
  Model/Coin.lean           commitProb, noCommitProb
  Safety/Statement.lean     SH1–SH5        Safety/Proof.lean
  Liveness/Statement.lean   SH6–SH9        Liveness/Proof.lean
  Period/Statement.lean     SH10           Period/Proof.lean
  Coin/Statement.lean       SH11           Coin/Proof.lean
  Ledger/Statement.lean     SH13           Ledger/Proof.lean
  Helpers/*.lean            the lemma layers
  Properties.lean           the carrier, its properties and support
LeanDagTest/Steelhead/
  Model.lean  Period.lean  Stall.lean  Axioms.lean
```

`scripts/check-arc-holes.py` enforces the partition: `Statement.lean`
files are proof-free, `Model/` files theorem-free (instances excepted),
and no synchrony name appears under `Properties/`.
