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
necessary (§4). It also states the claims for any rules meeting the
interface and instantiates them at BlueBottle's `5f + 1` pair (§11).
A generic result carries an **SH**-label, and its instance at a pair the
same number in that pair's series, **SH-MM** at the Mysticeti and
Mahi-Mahi pair and **SH-BB** at the `5f + 1` pair; a result about one
pair alone keeps its number in its pair's series. §1 to §9 follow the
`3f + 1` pair. Everything lives in `LeanDag/Steelhead/`
with witnesses in `LeanDagTest/Steelhead/`, consuming the core and the
Mahi-Mahi arc read-only, under the statement/proof partition of
`mahi-mahi.md` §9, and importing nothing of Barnacle.

## 0. Overview

**The protocol.** Mysticeti decides a slot proposed at round `r` from
rounds `r + 1` (votes) and `r + 2` (certificates); Mahi-Mahi from rounds
`r + wa − 2` and `r + wa − 1`, with the leader named by a coin read at
the decision round. Steelhead runs both on one DAG: every slot has a
**kind**, `0` synchronous and `1` asynchronous, assigned by the schedule
(`Slots.kind`, `docs/kinds.md`), and a wavelength function `w : ℕ → ℕ`
gives every kind the number of rounds its slots read; the pair's is
`wavelength ws wa`, and the protocol's schedule assigns the kinds
`periodicKind k`, asynchronous at every `k`-th round, so that the paper's
`w(r)` is the two read together (SH-MM4). Which slots are asynchronous is a
fact about the schedule, so the mode is an interpretation of the DAG and
touches no block. The one rule change is the anchor floor: an undecided
slot of kind `κ` at round `r` searches for its anchor from round
`r + w κ`, at its own wavelength (§3). The period `k` is adapted by a
deterministic update rule run on the causal history of an agreed event,
the interval's chain anchor (§5).

**What is reused.** The DAG core; the anchored decision relation
(`Common/Anchored.lean`), whose `waveAt` field is a function of the
slot's kind; Mahi-Mahi's direct rules, certificate, link
and laws at every wave; the counting lemma MM2; the timed model's bridge
from coverage into certification; the unpredictable-leader clause.

**The results.**

- **SH-MM1–SH-MM5a, safety at a wavelength function** (§3): the certificate
  lemmas at the slot's own wave, agreement across views and routes
  whatever the waves of the slot and of its anchor, the handover
  corollary, conservativity at a constant wavelength, chain agreement,
  and the coincidence of the direct verdicts of the output and the chain
  at an asynchronous slot (SH-MM5b). The paper's Lemmas 1 and 2, Theorem 1,
  Corollary 1, Theorem 5, the agreement half of Theorem 4, and the
  protocol section's remark on direct verdicts.
- **SH-MM6, liveness under synchrony** (§6): a reliably led slot commits
  under coverage, by the direct rule, everything below a fair run is
  decided, a slot whose leader has no block is skipped once a quorum
  blames it (SH-MM6c), a candidate one reliable block references one round
  up commits under synchrony whether or not its leader is reliable
  (SH-MM6d), and a slot is decided once every slot from its floor up to
  some reliably led slot is decided (SH-MM6e), or once the chain of floors
  above it reaches a reliably led landing (SH-MM6f); and the round-robin
  schedule the implementation runs offers a reliable run past every
  round, and a reliable leader within `n − |T|` rounds of every round,
  which is what SH-MM6b asks for (SH-MM6g), and at `ws · (n − |T|) < n` the
  chain reaches such a landing within `n − |T|` hops, the paper's hop
  count (SH-MM6h), within `b` hops once every other validator outside
  `T` has crashed (SH-MM6i), and so within `(b + 1) · (ws + (n − |T|))`
  rounds, the paper's `(b + 1)(ws + f)` (SH-MM6j). All three read the wave
  at the constant `ws`; at the paper's dial the descent takes a commit
  in place of a reliable leader (SH-MM6m), the count deducts the coin's
  rounds and becomes `ws · (n − |T|) + ws · ⌈n / p⌉ < n` (SH-MM6o), a
  reliably led synchronous round lies within `n − 1` rounds rather than
  `n − |T|` (SH-MM6n), and the round count is `(b + 1) · (ws + W)` at that
  wait (SH-MM6p). The deducted term is never zero, so at the tight
  committee with a bare reliable quorum the count is empty and the chain
  rests on the coin instead (§6.1, §7 finding 12). Both execution
  disciplines reach SH-MM6a's hypothesis: the
  reactive one, where a builder never waits past its timeout and
  `SynchronisedOn` is false by design (SH-MM6k), and the timed one, from a
  `ViewPace` whose timeout clears the delay (SH-MM6l). The paper's Theorem
  2, for the decision relation.
- **SH-MM7, chain liveness** (§4): at any schedule whose rounds strictly
  increase, the coin schedule and every control schedule among them,
  every verdict below a run of `wa` consecutive commits is settled under
  Mahi-Mahi's run clause, under synchrony without the clause, and, at the
  coin schedule, below any one run of `wa` good coins (SH-MM7c). The control
  half of Theorem 3 (i).
- **SH-MM8, the stall** (§4): under the paper's own asynchronous adversary,
  at every period `k ≥ ws` the output never decides a slot of the
  residue class `k − 1`, whatever the asynchronous slots do. The
  argument the chain verdict answers, as a theorem.
- **SH-MM9a, the drain** (§4): `wa` consecutive commits decide every slot
  below them at any wavelength function bounded by `wa`; at period `1`,
  under the run clause at the output schedule, past every round some
  slot has everything below it decided (SH-MM9b); and an asynchronous slot
  costs `wa − ws` rounds, its successor waits at most `wa − ws − 1`
  (SH-MM9c). Theorem 3 (ii), and the protocol section's latency arithmetic.
- **SH-MM10, the scan's state** (§5): the period, the agreed output's cursor
  and its last commit are agreed across views under any update rule, so
  is the output under the adaptive wavelength
  over the intervals the record's rounds fall in (SH-MM10a, SH-MM10b); the
  control slots of a scan are a function of the interval's period, the
  period bound and the boundary, and their verdicts agree per scan
  (SH-MM10k, SH-MM10l); the scan of an interval ends once its control verdicts
  are in, and under the clause at every control schedule in range it
  ends for every interval (SH-MM10c, SH-MM10d); an anchor below which the
  agreed output committed nothing for `I` rounds hands the next interval
  period `1` (SH-MM10e), and the first interval's anchor keeps its period
  (SH-MM10m); every interval and every window holds two asynchronous
  rounds, and the period stays in its range and a divisor of the bound
  (SH-MM10f, SH-MM10n, SH-MM10g, SH-MM10o); the control slots of every scan carry a
  coin under the adaptive schedule (SH-MM10p); an interval is evaluated only
  once the scan below it has closed (SH-MM10q); the agreed output is a prefix of
  the view's own and stalls below a slot the view leaves undecided
  (SH-MM10h, SH-MM10i); and a window of `I + 1` rounds resolves an asynchronous
  slot of every candidate once `I ≥ K + wa − 2` (SH-MM10j). Theorem 4, the
  period half of Theorem 3 (i), and the adaptive section's structural
  claims.
- **SH-MM11, the coin** (§4): with a uniform coin the chain slot of a
  round commits with probability `|good| / n`, at least `(n − f − b) / n`
  by MM2 at `wa ≥ 5` and so at least `1/3`, and at least `1/n` at
  `wa ≥ 4` (SH-MM11b); the coin names a Byzantine leader with probability
  `b / n` (SH-MM11c); over `m` rounds the probability that no round's coin
  names a directly committed leader is at most `((f + b) / n)^m`, which
  tends to zero, and the probability that every one of them does is at
  least `((n − f − b) / n)^m`, the paper's `p^{wa}` per attempt at
  `m = wa` (SH-MM11d). The probability half of Theorem 3 (i), in Mathlib's
  `PMF`. Theorem 2's asynchronous-floor clause is here too: at period
  one a slot below `M` consecutive blocks of `wa` coins stays undecided
  with probability at most `((n^wa − (n − f − b)^wa) / n^wa)^M`, the
  drain below a block of good coins (SH-MM11i), and the search waits for
  the first good block, `1 / p^wa` blocks of `wa` rounds in expectation,
  the paper's `wa / p^wa` (SH-MM11j), at most `n^wa` blocks at `wa ≥ 4`
  (SH-MM11k); no bound per hop of the
  search holds (§7, finding 9). A scan's `c` control slots all miss with
  probability at most `((f + b) / n)^c` (SH-MM11l), so a scan anchors
  within `1 / (1 − ((f + b) / n)^c)` intervals in expectation, the
  asynchronous section's `1 / (1 − (1 − p)^c)` (SH-MM11m). And Theorem 3's "with probability `1`" in the form a finite
  record admits (SH-MM15): over the coins of `M` blocks of `wa · K` rounds,
  one opening every `q`-th interval from the second after a slot's, with
  `wa · K ≤ q · I` so that a block ends before the next opens, a view's
  scan stalls below the slot's interval or leaves the slot undecided
  under the failover with probability at most
  `2 · ((n^(wa·K) − (n − f − b)^(wa·K)) / n^(wa·K))^(M/2)`, which tends
  to zero, and at `wa ≥ 4`, where the counting lemma promises one
  committed candidate per round, with `1` in place of `n − f − b`
  (SH-MM15d); and
  over a sequence of records, with the coin drawn as a process, the
  infinite product of the uniform distribution, for almost every coin
  some record decides the slot in every view holding its horizon
  (SH-MM15e), Theorem 3's "with probability `1`" itself, some interval above
  the slot's is anchored (SH-MM15f), and every slot at
  once, each with its own sequence of records (SH-MM15h). Both hold against
  an adversary that builds its record from the draws already made
  (SH-MM11h, SH-MM15b, SH-MM15g), keeping at every round a floor of committed
  candidates, fixed by the coins drawn before that round, that the
  round's own coin cannot shrink; and a period sequence matching what a
  view derives, which those claims quantify over, always exists (SH-MM15i).
- **SH12, on data** (§8): the anchor-floor counterexample, the stall DAG
  with its asynchronous commit beside it, the period sequence at a
  concrete update rule, the coin streak that outputs nothing through any
  horizon, the Byzantine floor with the two hops of its floor chain and
  the round-robin schedule that bounds such a chain, the good sets an
  adaptive adversary answers with, the Byzantine validator's block
  delivered by a commit that no reliable leader carried, Algorithm 3's
  replay on a healthy window, on a startup window and on a complete
  window too short for a wave, and the rotating stall whose period
  Algorithm 3 answers `4` at every anchor.
- **SH-MM13, the ledger** (§3): the committed-leader sequence and the
  ledger of a settled prefix are agreed across views, the ledger is
  monotone, and a block enters at one slot, which both views name. The
  paper's Corollary 2, order and integrity.
- **SH-MM14a, output liveness under the failover** (§5): a slot
  two intervals below an anchored one is decided once a run of `wa`
  coin-led commits above that interval is in view: while the slot waits
  the agreed output's last commit lies below it, so every anchor two
  intervals up sits more than `I` rounds above that commit, the failover
  fires at each anchored one and the period is `1`
  from the first, where the run decides everything below it. Theorem 3
  (ii) and the asynchronous half
  of Definition 1's validity, deterministic given the anchor and the run,
  the two events the coin supplies almost surely; SH-MM14b reads both off
  Mahi-Mahi's run clause at every control schedule the period can name
  and concludes that every slot far enough below the horizon is decided;
  SH-MM14c names them as two events of the coin alone, a good coin at the
  first control round of an interval past the slot's and `wa` good coins
  above it, the form SH-MM15 draws.
- **SH16, the interface composes** (§3): any family of rules whose laws
  hold, one per round, agreeing on rung count and tie-break, composes
  into a rule whose laws hold, so its verdicts agree across views; and
  Steelhead's rule is the composite of Mahi-Mahi's read at each round's
  wave, by definition. The paper's Theorem 1 at the interface level, SH-MM2
  its instance.
- **SH-MM17, atomic broadcast** (§3): Definition 1 clause by clause over
  settled prefixes: a delivered block is delivered by every view whose
  settled prefix is as long, a delivered block is a block of the record
  entering at one slot, a reliable block is delivered with the first
  committed reliable leader two rounds up after GST, and two blocks
  enter at the same slots in every view, so in the same order. Under
  asynchrony the delivery rests on the reference rule's consequence
  instead: a block every reliable validator has referenced by round `ρ`
  lies in the cone of every block above `ρ`, so the first committed slot
  there delivers it whoever led it (SH-MM17d); that such a round exists is
  the reference rule's doing, which the substrate, its references one
  round back, does not model. The liveness half is SH-MM6b, SH-MM14b and SH-MM15.
- **SH18, the replay** (§5): Algorithm 3 as data, the window's evidence
  read from the anchor's causal history, the three passes and the
  hysteretic selection; the selection stays among the candidates and
  never worsens the score, the window's evidence is consistent, Lemma
  3's count holds on the window once a quorum has populated the boost
  and decision rounds within it, every timing lies between its round and
  the window's top, the asynchronous term is bounded by the committed
  count, and a window commit is a commit on the DAG;
  Algorithm 3 keeps the period in range (SH18h), the
  share of the candidates the window marks committed is the rule's
  commit probability on the window read as a record (SH-MM18i), a
  canary spacing coprime to a candidate period gives a probe in any
  window holding two canary rounds (SH18j), an odd spacing for every
  candidate (SH18m); the hysteresis keeps the current period unless the
  best candidate improves on it by the factor `1 − ε` (SH18k), ties keep
  the current period and otherwise favour the larger candidate (SH18l),
  and at a power-of-two bound every candidate divides it, as does
  Algorithm 3's answer (SH18n).
- **SH-MM19, the periodic class** (§3): the paper's dial, `wa` at every
  `k`-th round and `ws` elsewhere, read as the pair's wavelength at the
  kinds a period assigns, is a wavelength function the results above
  take, every kind's wave between two and the larger wave, so that an
  identity-round schedule spans at that wave and agreement, the
  extension laws and the support's laws hold at it; and at two distinct
  waves the two kinds read two waves, which a period of two or more
  both assigns, so a wave that varies is on record.
- **SH-MM20, the mistimed leader timeout** (§9): the arithmetic of the
  paper's appendix on a timeout below the link delay, where every block
  carries minimum-quorum references. A certificate forms with
  probability `1` on a unanimous vote round and `f / n` when one block
  abstained, and the layer cake of the tail probabilities gives the
  appendix's `1 / P₂` rounds. No DAG and no consensus: the arrival model
  is the appendix's assumption, and only the arithmetic is checked.
- **SH-BB16, the `5f + 1` pair** (§3): the second pair the paper
  instantiates, BlueBottle's two variants on one committee at
  `n ≥ 5f + 1`, Odontoceti at wave two and Async BlueBottle at wave
  three. Both halves satisfy the laws at their own wave, which is the
  paper's clauses A2 and A3 for them (SH-BB16a), and they agree on the rung
  count and the tie-break, which is all a pair owes beyond the laws
  (SH-BB16d); so SH16a and SH16b apply and the composite's verdicts agree
  across views (SH-BB16b) and hand a direct commit over to an anchor decided
  by the other rule (SH-BB3). Unlike the `3f + 1` pair the two halves are
  two predicate families, and their floors differ, `r + 2` against
  `r + 3` (SH-BB16e).

### 0.1 Correspondence with the paper

The generic column is the statement at any rules meeting the interface
(§11), the `3f + 1` column its instance at the Mysticeti and Mahi-Mahi
pair, and the `5f + 1` column at BlueBottle's pair; "via" names the
hypothesis bundle or the generic statement that gives the claim there
without a restatement. The remarks describe the `3f + 1` pair.

| paper | generic | `3f + 1` pair | `5f + 1` pair | remark |
| :--- | :--- | :--- | :--- | :--- |
| Definition 1 (atomic broadcast) | SH17, SH6b, SH14b, SH15e | SH-MM17, SH-MM6b, SH-MM14b, SH-MM15e | SH-BB17, SH-BB14b, SH-BB15e | agreement, integrity and total order over settled prefixes, validity after GST with the first committed reliable leader two rounds up (SH-MM17c) or, under asynchrony, with the first committed slot above the round by which the reliable validators have referenced the block, whoever led it (SH-MM17d); that A1's reference rule yields such a round is taken as a hypothesis, the substrate's references sitting one round back (§7, finding 11); the "eventually" is SH-MM6b under synchrony, SH-MM14b under the clause and SH-MM15e almost surely under asynchrony. The order of the blocks one commit releases is not modelled |
| Lemma 1 (certificate uniqueness; a skipped block is never certified) | — | SH-MM1a, SH-MM1b | — | Mahi-Mahi's lemmas at the slot's wave |
| Lemma 2 (quorum intersection across the wave) | — | SH-MM1c | — | at `r + w κ` for a slot of kind `κ`, whatever the block's own wave |
| Corollary 1 (handover) | SH3 | SH-MM3 | SH-BB3 | stated against the relation's anchor search |
| Theorem 1 (agreement) | SH2, SH16a, SH16b | SH-MM2, SH-MM16c | SH-BB16a, SH-BB16b, SH-BB16d | `AnchoredRule.decided_unique` at Steelhead's laws; at the interface level, any family of rules whose laws hold composes into one whose laws hold, and Steelhead is the composite of Mahi-Mahi's rule at each kind's wave. Both pairs the paper instantiates are on record: the `3f + 1` one as SH-MM16c and the `5f + 1` one, Odontoceti at wave two with Async BlueBottle at wave three, as SH-BB16, whose laws are the paper's Lemmas 1 and 2 at this pair, as its discharge table cites them |
| Corollary 2 (total order and integrity) | SH13 | SH-MM13 | SH-BB13 | in part: the relation's own ledger theorems at Steelhead's laws, over a settled prefix. Ordering the blocks a single commit releases is declined development-wide (report §1.4, §5.6) |
| Theorem 2 (liveness under partial synchrony) | SH6a, SH6b, SH6c, SH6e, SH6f, SH6g, SH6h, SH6i, SH6j, SH6m, SH6n, SH6o, SH6p, SH11j, SH6l | SH-MM6a, SH-MM6b, SH-MM6c, SH-MM6d, SH-MM6e, SH-MM6f, SH-MM6g, SH-MM6h, SH-MM6i, SH-MM6j, SH-MM6m, SH-MM6n, SH-MM6o, SH-MM6p, SH-MM11j, SH-MM11k, SH-MM6k, SH-MM6l | SH-BB6, SH-BB6a, SH-BB6c, SH-BB6d, SH-BB6k, SH-BB11j | in part: the honest-leader commit by the direct rule, everything below a fair run, the crashed-leader skip from `n − f` blames, the remark that partial dissemination does not defer, for a leader that did not equivocate, and the anchor clause as the rule has it, a slot decided once every slot from its floor up to some reliably led slot is decided (SH-MM6e) or once the chain of floors reaches a reliably led landing (SH-MM6f), which is how the theorem now states its anchor clause; its earlier form, "once the first honest-led slot above its floor commits, at most `b` slots higher", was refuted on data, an equivocating leader at the floor being the anchor (§7, finding 7). What holds at the implementation's round-robin schedule is the hop count, a reliably led landing within `n − |T|` hops once `ws · (n − |T|) < n` (SH-MM6h), within the paper's `b` hops once every other validator outside `T` has crashed (SH-MM6i), and a round count, one reliable leader within `n − |T|` rounds and a reliable run of three past every round at `n = 3f + 1` (SH-MM6g), which also discharges SH-MM6b's fairness hypothesis there; and the theorem's `(b + 1)(ws + f)` rounds above a synchronous floor, as `(b + 1) · (ws + (n − |T|))` rounds above an unskipped slot at the schedule of SH-MM6i (SH-MM6j). Those three fix the wave at `ws`; at the paper's dial the descent takes a commit in place of a reliable leader (SH-MM6m), the count deducts the coin's rounds and reads `ws · (n − |T|) + ws · ⌈n / p⌉ < n` (SH-MM6o), the wait for a reliably led synchronous round is `n − 1` rather than `n − |T|` (SH-MM6n), and the round count is `(b + 1) · (ws + W)` at that wait (SH-MM6p); the deducted term is never zero, so at `n = 3f + 1` with a bare reliable quorum the count is empty and the chain rests on the coin (§7, finding 12). No per-hop probability holds for the coin's slots, a landing of the search reading coins above it (`HopBound.lean`; §7, finding 9); what holds is SH-MM11i, the tail below runs of `wa` good coins at period one, and its mean, the search waiting for at most `1 / p^wa` blocks of `wa` rounds in expectation, the `wa / p^wa` the theorem states (SH-MM11j), at both waves, `n^wa` blocks at `wa ≥ 4` (SH-MM11k). The ordering of the coin's slots holds in expectation and almost surely (SH-MM15e), not for every coin sequence (§7, finding 5). SH-MM6a's hypothesis is reached from either execution discipline, the reactive one (SH-MM6k) and the timed one (SH-MM6l); what neither bounds is a wall-clock latency, since a round is the only unit the model carries |
| Theorem 3 (i) (the control verdicts resolve, the period reaches `1`) | SH7a, SH7c, SH10c, SH10d, SH10e, SH11 | SH-MM7a, SH-MM7c, SH-MM10c, SH-MM10d, SH-MM10e, SH-MM11 | SH-BB7a, SH-BB7c, SH-BB10d, SH-BB11a | the control verdicts of a scan settle under Mahi-Mahi's run clause at that scan's schedule and, at the coin schedule, below any one run of `wa` good coins, a period is derived for each interval, and an anchor below which the agreed output committed nothing for `I` rounds hands the next interval period `1`, the failover the theorem's premise states and the implementation applies before the rule is consulted (`apply_period_update`; §7, finding 4). The coin is modelled by its effect and as a `PMF`: the commit probability `(n − f − b) / n` at `wa ≥ 5` (SH-MM11a) and `1 / n` at `wa ≥ 4` (SH-MM11b), and the tail at both waves (SH-MM15a, SH-MM15d). The "with probability `1`" is SH-MM15e over a sequence of records, SH-MM15a's tail on one, and "some scan finds its anchor" is SH-MM15f, the same over the anchored interval |
| Theorem 3 (ii) (at period `1` the ledger grows) | SH9a, SH9b, SH14a, SH14b, SH14c, SH15 | SH-MM9a, SH-MM9b, SH-MM14a, SH-MM14b, SH-MM14c, SH-MM15 | SH-BB9b, SH-BB14b, SH-BB15a, SH-BB15e | SH-MM9b at period `1` under the run clause at the output schedule and below its horizon; SH-MM14a for the adaptive output under the failover, given one anchored interval at least two past the slot's and one run of `wa` good coins above it; SH-MM14b reads both off the run clause at every control schedule the period can name, SH-MM14c off a good coin at an interval's first control round and a run above it; SH-MM15a bounds the probability that some view has not derived the slot's period or leaves it undecided, over `M` blocks of `wa · K` coins opening every `q`-th interval above the slot's at `wa · K ≤ q · I`, by `2 · ((n^(wa·K) − (n − f − b)^(wa·K)) / n^(wa·K))^(M/2)`, which tends to zero (SH-MM15c); and SH-MM15e states the "with probability `1`" itself, over a sequence of records with the coin drawn as a process: for almost every coin some record decides the slot in every view holding its horizon, and SH-MM15h every slot at once, each with its own sequence of records. SH-MM15b and SH-MM15g are the same two against an adversary that answers the draws already made and keeps a floor of committed candidates per round, by the adaptive block bound SH-MM11h; SH-MM15i gives the period sequence those claims quantify over. The growth of the ledger from the settled prefix is SH-MM13 |
| Asynchronous liveness, "a scan finds its anchor within an expected `1 / (1 − (1 − p)^c)` intervals" at `c = I / period` control slots | SH11l, SH11m | SH-MM11l, SH-MM11m | via SH-BB11 | a scan's `c` slots all miss with probability at most `((f + b) / n)^c` at any strictly increasing schedule of rounds (SH-MM11l), and the wait is the geometric series in that bound, summing to its inverse (SH-MM11m). The paper reads `c` off the interval and the period; the statement takes the slot count as given, and the independence across intervals is the uniform draw's, as everywhere else in §4 |
| Appendix on a mistimed leader timeout, `π(v) = 1` at `v = n` and `f / n` at `v = n − 1`, and the `1 / P₂` rounds an undecided slot waits | — | SH-MM20a, SH-MM20b | — | the two ratios exactly, `C(n − 1, q) / C(n, q) = (n − q) / n` at the threshold `q = n − f`; and the layer cake of the appendix's tail probabilities `(1 − p)^m`, which sums to `1 / p`. The arrival model, the minimum-quorum reference pattern and the independence between validators' orders are the appendix's assumptions, not results, and `P₁`, `Pr[V = n] = p^(n−1)` and the measured rates are outside the model (§9) |
| Adaptive section, the gating rule, "a slot is evaluated once its interval's period is known" | SH10q | SH-MM10q | via SH-BB10 | a state for interval `j + 1` carries a state for interval `j` and a closed scan of `j` at that state's period, with an anchor or with none, so the derivation itself gates: waiting is the absence of a state, and no round of an interval is read at any period until the scan below it closes |
| Clause A5, the candidates fixed "before the round's coin can be learned" and the leader uniform "conditional on that history ... whatever the adversary learned from earlier coins" | SH15b, SH15g, SH11h | SH-MM15b, SH-MM15g, SH-MM11h | via SH-BB11 | the arc's floor of committed candidates is a subset of `good` at each round and is a function of the draws already made (`NonAnticipating`), so the per-round bound multiplies against an adversary free to rebuild the DAG at every draw; the model does not derive the floor, which is what the clause supplies. The paper restated A5 this way on 2026-09-22; Mahi-Mahi's own arc needs no such condition, taking a DAG-shape hypothesis in place of the product |
| Theorem 4 (agreement of the period) | SH10a, SH10b, SH10k, SH10l | SH-MM10a, SH-MM10b, SH-MM10k, SH-MM10l | SH-BB10a, via SH-BB10 | for any deterministic update rule, per scan: the control slots of a scan are a function of the interval's period, the period bound and the boundary (SH-MM10k) and their verdicts agree across views (SH-MM10l); SH-MM10a at one wavelength and schedule on both sides, SH-MM10b at each validator's own derived wavelength and on the schedule its own sequence names, where the sequences agree below the record's top interval and the verdicts with them |
| Appendix, the bounds `I ≥ 2 · maxPeriod` and `I ≥ maxPeriod + wa − 2`, and `1 ≤ k ≤ maxPeriod` | SH10f, SH10n, SH10g, SH10j, SH18h | SH-MM10f, SH-MM10n, SH-MM10g, SH-MM10j | via SH-BB10 | two asynchronous rounds per interval, and per window of an anchor at round `I` or above, at any `k ≥ 1` with `2k ≤ I`; the period stays in range when the initial period does and the update rule keeps it there, the failover's `1` included, which Algorithm 3's replay does whenever the candidates lie in `[1, K]` (SH18h). The bound admits `I < maxPeriod + wa − 2`, where a window of `I + 1` rounds holds the decision round of none of its asynchronous slots at some anchors and of one at others (SH-MM10j; §7, finding 8) |
| Adaptive section, "the replay is exact when the window holds no probe" | — | SH-MM18i | SH-BB18i | in the part that is a theorem: at a round the window retains, the share of the `n` candidates the window marks committed is the probability that a uniform coin names a directly committed leader on the anchor's history read as a record, the paper's `c_r / n`, at `1 ≤ wa`. The anchor's term is the approximation the paper admits |
| Adaptive section, "with the canary odd and hence coprime to every candidate period, so that every candidate is probed" | SH18j, SH18m | — | — | at a canary spacing coprime to a candidate period of at least two, a window holding two canary rounds whose decision round it retains holds a probe for the candidate, since two consecutive multiples of the spacing cannot both be multiples of the period; an odd spacing is coprime to every candidate, the candidates being powers of two (SH18m) |
| Adaptive section, "the multiples of maxPeriod are asynchronous slots under every candidate period, hence defined and coin-carrying whatever the scan decides", with "every candidate divides maxPeriod" | SH18n, SH10o, SH10p | SH-MM10o, SH-MM10p | via SH-BB10 | at a power-of-two bound every candidate divides it and Algorithm 3 answers a divisor of the bound from one (SH18n), so every derived period divides the bound (SH-MM10o), and every control slot of a scan that lies in its interval or above it is an asynchronous round of the adaptive schedule, led by the coin (SH-MM10p); with SH-MM5b the two readings agree on every such slot whenever either verdict is direct |
| Algorithm 3, "hysteresis against noisy windows" and "ties keep the period, then favor the larger candidate" (the body defers both to the appendix) | SH18k, SH18l | — | — | the selection leaves the current period only for a candidate scoring below `1 − ε` times the current period's, and takes the best candidate whenever that one does; the best candidate scores no worse than the current period and than every candidate, is the current period at a tie with it, and is otherwise the largest candidate at its score, in whatever order the candidates are listed |
| (no current paper claim) | SH11c | SH-MM11c | via SH-BB11 | the uniform coin lands among the `b` Byzantine validators with probability `b / n` exactly, and so at most `f / n`. The protocol section's "an asynchronous slot whose Byzantine leader equivocates (probability at most `b/n`)" is gone from the paper, so the statement stands without a claim to answer |
| Adaptive section, "where either reading decides directly, both decide alike" | — | SH-MM5b | — | predicate for predicate, at a slot proposed at its own round and led by the coin |
| Protocol section, "the successor waits at most `max(0, wa − ws − 1)` rounds", "delays never compound" | SH9c | SH-MM9c | via SH9c | arithmetic on the decision rounds; output timing itself is not modelled |
| Theorem 5 (conservativity) | SH4 | SH-MM4 | SH-BB4 | at a constant wavelength by `rfl`, period `1` by `Nat.mod_one`, and at wave three the derivations are exactly the core's, both directions |
| Protocol section, the dial `w(r) = wa` at every `k`-th round and `ws` elsewhere | — | SH-MM19 | SH-BB16e | the pair's wavelength satisfies every hypothesis the results place on a wavelength function, `2 ≤ w κ ≤ max ws wa`, so the laws hold at every period, and at `ws ≠ wa` the two kinds read two waves, both of which a period `k ≥ 2` assigns: the wave the core's `waveAt` admits as a function of the kind is not a constant in disguise |
| Lemma 3 (the replay cannot be starved) | SH11a, SH18f | SH-MM11a, SH-MM18d, SH-MM18g | SH-BB11a, SH-BB18d, SH-BB18g | `c_r ≥ n − f − b` on the DAG under any scheduling (SH-MM11a), and on the window once a quorum has populated the boost and decision rounds within it (SH-MM18d), which is what "populated" must mean for the replay, whose evidence is the window's (§7, finding 6), and `c_r ≥ n − 3f` at the `5f + 1` pair on the window once a correct quorum has populated the two rounds above within it (SH-BB18d); the replay's asynchronous term is at most the mean of the decision round over the `c_r` committed candidates and the window's top over the rest (SH18f), a bound and not a comparison with the rule's own latency, which is not modelled; a probe's success is a certificate quorum the DAG holds, so the adversary cannot forge one (SH-MM18g), while the probes' rate is extended to the unprobed synchronous slots and a scheduler serving the canary rounds alone raises that estimate (§7, finding 10). Both at `2 ≤ ws < wa` |
| Appendix, "Period updates while output is stalled", and the Lean appendix's "the stall, a committed asynchronous slot deciding nothing below it" | SH8 | SH-MM8 | via SH8 | the argument of that paragraph as a theorem, for every `2 ≤ ws ≤ k` rather than the one period it walks through (§4) |

## 1. The wavelength function

The paper's `w(r) = wa if r mod k = 0 else ws` splits in two
(`Model/Wavelength.lean`): `wavelength ws wa : ℕ → ℕ` is the wave of a
kind, `ws` at the synchronous kind `0` and `wa` at the asynchronous kind
`1`, and `periodicKind k : ℕ → ℕ` is the kind of a round, `1` at every
`k`-th round and `0` elsewhere. A schedule sets `kind s = periodicKind k
(slotRound s)`, and `IsAsync k r` names the asynchronous rounds. The
formula itself is kept as `periodic ws wa k`, and SH-MM4 carries the
identity `wavelength ws wa (periodicKind k r) = periodic ws wa k r`. At
`k = 1` every slot is asynchronous and the pair reads the constant `wa`
(`periodicKind_one`); a schedule that assigns no kinds leaves every slot
at `Slots.kind`'s default `0`, so the pair reads the constant `ws`, and
both ends of the dial are one rule at one wave. Lean's `r % 0 = r` makes
only round `0` asynchronous at `k = 0`; no result excludes that period
and none needs to, since SH-MM8 reads `2 ≤ k` off its own `2 ≤ ws ≤ k` and
SH-MM10 holds at every period.

Every result is stated at an arbitrary `w : ℕ → ℕ`, not at the pair's:
the rule consumes a wavelength function, and the pair is one way of
producing one. What the results assume of `w` is a lower bound at every
kind, `2 ≤ w κ` for safety and `3 ≤ w κ` for liveness, and for the drain
an upper bound `wa`. A claim about the period takes the schedule's kinds
as a hypothesis, `∀ s, S.kind s = periodicKind k s`, or names the
adaptive schedule that carries them (§5).

## 2. The rule at a wavelength function

`steelheadAnchored w` (`Model/Decision.lean`) is one anchored rule whose
data at a slot of kind `κ` proposed at round `r` are Mahi-Mahi's at wave
`w κ`: the certificate-quorum direct commit, the slot blame as direct
skip, one rung of link (a certificate in the anchor's cone), no tie, and
the wave offset `waveAt κ = w κ − 1`, so that an anchor sits at round
`r + w κ` or above. `Decided w U V k v` is the anchored relation at that
data. At a constant `w` the rule *is* `mahiMahiAnchored w` by `rfl`
(SH-MM4); at the constant `3` the derivations are exactly the core's (MM1d
transported, and its mirror).

The shared relation reads `AnchoredRule.waveAt` at the slot's kind, which
the schedule assigns beside the slot's round and leader and which a
rebase carries with them (`docs/kinds.md`). That is what gives the rule a
band: `Banded` rebases every round by a constant, under which a wave read
from the round number would move, while a wave read from the kind does
not. Steelhead is therefore banded, truncation-local and safe under the
`2 ≤ w κ` its laws already ask (`target-properties.md` §3.4c, §6), and
persistence follows from the band at offset zero.

## 3. Safety, and the anchor floor

`Safety/Statement.lean`, each claim at the weakest bound its proof
consumes on the kinds read, `1 ≤ w κ` for SH-MM1c and `2 ≤ w κ` for the
rest:

- **SH-MM1a, SH-MM1b, SH-MM1c** are Mahi-Mahi's certificate lemmas at the slot's
  own wave: a directly skipped slot has no certificate for any
  candidate, two certified candidates of one author and round coincide,
  and a directly committed candidate of kind `κ` at `r` is certified in
  the cone of every block at round `r + w κ` or above, whatever wave that
  block's own slot carries.
- **SH-MM2, agreement**: two views deciding one slot reach the same verdict
  by any routes, whether the slot's wave is `ws` or `wa` and whether the
  anchor's is. The relation's agreement at `steelheadLaws`: every law of
  `AnchoredRule.Laws` speaks of one slot and its anchors, and at that
  slot the rule is Mahi-Mahi's at the slot's wave, eligibility included.
- **SH-MM3, handover**: a direct commit in one view is committed by every
  view that finds the slot an anchor, whichever rule decides that anchor,
  and no view skips it. This is the one cross-rule law: the anchor lies
  at `r + w κ` or above, where SH-MM1c places a certificate in its cone.
- **SH-MM4, conservativity**: `steelheadAnchored (fun _ => w) =
  mahiMahiAnchored w` by `rfl`, `wavelength ws wa (periodicKind k r) =
  periodic ws wa k r` at every round, and `periodicKind 1 = fun _ => 1`
  by `Nat.mod_one`, so at period one the pair reads `wa` everywhere; at
  the constant `3` the derivations are exactly the core's, MM1d one way
  and its mirror the other, since the core's skip is the slot-level
  blame Mahi-Mahi's is (`decided_of_core_decided`).
- **SH-MM5a, chain agreement**: the chain verdicts (§4) agree across views,
  an instance of MM1c at the chain schedule.
- **SH-MM5b, the direct verdicts coincide**: at an asynchronous round whose
  slot is proposed there and led by the coin, the output's direct commit
  and direct skip are the chain's predicates, so a direct derivation in
  either relation is one in the other. The protocol section's "whenever either verdict of an
  asynchronous slot is direct, the two coincide"; only the indirect
  verdicts may differ, and §4 says why.

**The interface.** Theorem 1 is stated for any two rules of the
interface. `compose rules` (`Model/Compose.lean`) is the composite of a
family of anchored rules, one per kind: a slot of kind `κ`
takes its wave offset, direct predicates and rungs of link from
`rules κ`, and the rung count and tie-break, which the relation reads
without a slot, from the rule of kind `0`. **SH16a** and **SH16b**
(`Interface/Statement.lean`): if every rule of the family satisfies
`AnchoredRule.Laws` and the family agrees on rungs and ties, the
composite does (SH16a), each law at a slot being the slot's rule's, the
anchor's rule never entering; the composite's verdicts then agree across
views (SH16b). The laws are clauses A2 and A3 in the relation's terms.

The two pairs the paper instantiates are stated in sibling directories,
at the two families `Model/Pair.lean` names, so that neither is the
interface's default. **SH-MM16c** (`MahiMahiPair/Statement.lean`):
`steelheadAnchored w` is the composite of `mahiMahiPair w`, Mahi-Mahi's
rule read at `w κ`, by definition, so SH-MM2 is an instance of SH16b.
**SH-BB16** (`BlueBottlePair/Statement.lean`) does the same for
`blueBottlePair`, Odontoceti at wave two and Async BlueBottle at wave
three on a `5f + 1` committee. Both halves already carry
`AnchoredRule.Laws` in their own arcs, `odontocetiLaws` and
`asyncBlueBottleLaws`, and both run one rung and break ties by the least
candidate, so the family's two side conditions hold by `rfl` (SH-BB16a,
SH-BB16d) and the composite's laws and agreement follow (SH-BB16b). The
handover (SH-BB3) is the one place the pair costs more than the `3f + 1`
one: there the rung's link is a certificate, unique per slot, so the tie
is empty and `indirectCommit_single` applies, while here each half lets
several candidates pass and the commit has to be identified with the
tie-break's choice, which each arc supplies as the strong form of its
fourth law. The floors differ, `r + 2` against `r + 3` (SH-BB16e), and
`LeanDagTest/Steelhead/BlueBottlePair.lean` runs both halves on one
universe under one schedule. The paper's Lemmas 1 and 2, which its
discharge table cites for this pair's clauses A2 and A3, are
`commit_link` and `skip_link` of SH-BB16a. **SH-MM19**
(`MahiMahiPair/Statement.lean`) states the periodic
class: `wavelength ws wa`, the paper's dial read at the kinds a period
assigns, is a wavelength function the results of this arc take, every
kind's wave at least two and at most `max ws wa`, so an identity-round
schedule spans at that wave (`spansEligible_of_le`), and agreement, the
extension laws persistence rests on, the support's locality and commit
laws, and its coverage law at waves of three hold at it
(`Properties.lean`'s theorems at that function); and at `ws ≠ wa` the two
kinds read different offsets, both of which a period of two or more
assigns, rounds `0` and `1` carrying one each, so what `waveAt` being a
function of the kind admits is a wave that varies, on record beside the
constant-wave rules of the tree.

**The ledger.** Agreement is about one slot; the output layer reads
verdicts off in slot order, and what it owes is the paper's Corollary 2.
**SH-MM13** (`Ledger/Statement.lean`) states it: over a prefix each view has
settled, the committed-leader sequences coincide (SH-MM13a), so do the
ledgers they deliver (SH-MM13b), the ledger only grows as further slots
settle (SH-MM13c), a block enters at one slot and both views name the same
one (SH-MM13d), and a committed block is the candidate of one slot
(SH-MM13e). Every conjunct is the anchored relation's own
ledger theorem at `steelheadLaws`, or a fact of `Common/Ledger.lean` that
reads no rule at all, so the arc adds no argument here. The claims are
order and integrity, not progress: they are conditional on a settled
prefix, which under the stall (§4) is short.

**Atomic broadcast.** Definition 1's clauses, as **SH-MM17**
(`Broadcast/Statement.lean`) reads them off settled prefixes: agreement
(SH-MM17a), a block one view delivers over a settled prefix every view
delivers over any settled prefix at least as long (from SH-MM13b and
SH-MM13c); integrity (SH-MM17b), a delivered block is a block of the record, so
one its author proposed, and enters the ledger at one slot (from SH-MM13d);
validity (SH-MM17c), a reliable block at round `r` lies in the cone of every
reliable block from round `r + 2` under synchrony from `r`, so it is
delivered with the first committed reliable leader there once the prefix
below is settled (`reaches_of_synchronisedOn`); and total order (SH-MM17e),
two blocks enter at the same slots in every view that settled them, so
in the same order (from SH-MM13d). Validity under asynchrony reads the reference rule's consequence
instead of synchrony (**SH-MM17d**): a block every reliable validator has
referenced by round `ρ` lies in the cone of every block above `ρ`, its
author reliable or not, since a quorum of references meets the reliable
set; so the first committed slot above `ρ` delivers it, whichever leader
the coin named. That such a round exists for every block the reliable
validators receive is what the clause `Core::try_new_block` implements
gives, a block referencing every block its author holds that its own
parent does not already cover; the substrate's references sit one round
back (`ValidWrt.predecessor`), so the rule and the round it yields lie
outside the model and the claim takes the round as its hypothesis (§7,
finding 11). Without the rule a block delayed past its own round is never
referenced and validity fails under asynchrony, which is why the paper's
A1 states it. The "eventually" of agreement and validity is
the liveness half: SH-MM6a and SH-MM6b under synchrony, SH-MM14b under the clause
and SH-MM15e almost surely under asynchrony. The order of the blocks one
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

## 4. The control verdict, the stall, and the drain

**The stall.** A direct commit reaches a slot below it only through a
decided stretch: from the lower slot's floor up to the commit every slot
must be decided, because the anchor search stops at an undecided one. At
every period `k ≥ ws` that stretch holds a synchronous slot, which the
adversary keeps undecided at no cost, and the output stalls while the
asynchronous slots commit on schedule. This is the paper's "Why the
chain, and not the output"; SH-MM8 is it as a theorem, for every period
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

**SH-MM8** (`Liveness/Statement.lean`, `Stall`) states it for every
`2 ≤ ws ≤ k` and every `wa`: at one slot per round, if no synchronous
candidate is ever certified and no synchronous slot is directly skipped
in a view, no slot at a round `≡ k − 1 (mod k)` is ever decided in that
view. The proof is an induction on the derivation: a class-`(k − 1)`
slot's direct verdicts are excluded by hypothesis; a synchronous anchor
never commits without a certificate; an asynchronous anchor sits a full
period above, and the class-`(k − 1)` slot between must be skipped,
which is the claim one period up. `LeanDagTest/Steelhead/Counterexamples/Stall.lean`
shows the adversary's shape on valid data at `n = 4`: every synchronous
slot's candidate has exactly two votes, the asynchronous slot commits
directly, and slot `3` is undecided by SH-MM8. For `ws = 3` only `k = 1`
and `k = 2` are live; every larger candidate the paper's update rule can
select, `4` up to its maximum of `64`, stalls.

**The control verdict.** The paper keeps the output relation and
adds, on the **control slots**, a second verdict that drives the period
update alone: the asynchronous rule with anchors restricted to control
slots, so that no known-leader slot lies on the chain and nothing the
adversary holds undecided blocks it. A control slot is a round that
carries a coin, fixed by rule and per scan, as the reference
implementation reads it (`committer.rs`, `is_control_round`,
`compute_chain`): for the scan of interval `j` at period `k`, the
multiples of `k` up to the boundary `(j + 1) · I` and the multiples of
the period bound `K` above it, where the next period is not yet known
(the implementation's candidate periods all divide `K`, so those rounds
are asynchronous whatever the scan fixes; the arc's update rule is any
function and the coin a map on every round, so no claim needs that).
`controlSlots coin I K j k` enumerates those rounds in order, each led by
its coin, every slot asynchronous (`controlRound I K j k i` is slot `i`'s
round), and `ControlDecided I K wa coin j k = MahiMahi.Decided wa` at
that schedule (`Model/Chain.lean`). A round without a coin reads in the
implementation as a skip, which the anchor search and the scan pass over
exactly as they pass over a round that is no slot, so the control
reading is the Mahi-Mahi arc at a sub-schedule and every result about it
is Mahi-Mahi's: agreement per scan (SH-MM10l), liveness under the run
clause (**SH-MM7a**, MM3c at any schedule whose rounds strictly increase,
the spanning hypothesis discharged because consecutive slots lie at least
one round apart, so a run of `wa` consecutive control slots suffices),
liveness under synchrony without any clause (**SH-MM7b**, the core's L10 at
Mahi-Mahi's support, at any such schedule), and the step SH-MM7a takes once
per slot on its own (**SH-MM7c**, at the coin schedule `chainSlots coin`,
one slot per round led by the coin, which is also the output schedule at
period `1`): one run of `wa` good coins settles every verdict below it,
in any view holding its decision rounds. Each scan has its own control
set, so a round above the boundary may read differently in the next
scan; no claim compares verdicts across scans.

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
SH-MM11b): the paper's wavelength-four trade-off. The coin lands among the
Byzantine validators with probability `b / n`, at most `f / n`
(`byzantine_prob_eq`, `byzantine_prob_le`, SH-MM11c), the protocol
section's bound on the chance that an asynchronous slot's leader
equivocates. Over `m` rounds with
independent coins, modelled as the uniform distribution over the leader
maps `Fin m → Validator`, the probability that no round's coin names a
directly committed leader is at most `((f + b) / n)^m`, and that tends to
zero (`noCommitProb_le`, `tail_tendsto_zero`). The positive form is the
one the paper's Theorem 3 (ii) states: every one of those rounds names a
committed leader with probability at least `((n − f − b) / n)^m`, which
at `m = wa` is the `p^{wa}` a window is asked for (`runProb_ge`, SH-MM11d).
It is not the complement of the tail, which bounds the chance that no
round commits, and it is proved the same way, by counting the maps that
land in every round's good set. `Coin/Statement.lean` states the seven as
SH-MM11a, SH-MM11b, SH-MM11c, SH-MM11d, SH-MM11e, SH-MM11f and SH-MM11g over `commitProb`,
`runProb` and `noCommitProb`, three of the quantities `Model/Coin.lean`
defines.

**The search under the coin** (`coinOfBlocksFrom`, SH-MM11i). Theorem 2
bounds the anchor search above an asynchronous floor. What holds is the
run form: at period one every slot below a block of `wa` coin rounds
naming committed candidates is decided, by the drain (SH-MM9a), so over `M`
consecutive blocks of `wa` coins above a slot it stays undecided with
probability at most `((n^wa − (n − f − b)^wa) / n^wa)^M`, the chance
that every block holds a bad coin, which the fixed-record block count
gives (`undecidedAtPeriodOne_le`, `no_good_block_prob_le`), the paper's
`(1 − p^{wa})^M` after `M` attempts. No bound per hop of the search
holds: a landing of the search is not a function of the coins below it,
since the coin that commits an anchor above a pending slot both skips
that slot and shifts the landing, and `HopBound.lean` (§8) exhibits two
landings led by the one Byzantine validator with probability `19/256`,
above `(b/n)^2 = 1/16` (§7, finding 9). The claim is stated at period
one, where every slot is the coin's; at a mixed schedule a hop may land
on a known leader, which no coin governs. **SH-MM11j**
(`expected_firstGoodBlock_le`, `decided_of_firstGoodBlock`) is the
theorem's expectation in that form: `firstGoodBlock` is the least of the
`M` blocks whose every coin is good, or `M` when there is none, and the
search waits for `firstGoodBlock + 1` blocks, whose expected value over
the uniform block map is at most `(n / (n − f − b))^wa`, the paper's
`1 / p^wa`, whatever the horizon `M`, since it is the sum over `m` of
the chance that the first `m` blocks are all bad, each at most
`(1 − p^wa)^m` (`firstGoodBlock_ge_prob_le`), a geometric series
summing to `1 / p^wa` (`one_sub_badBlockBound`); and a view holding the
first good block's decision rounds decides the slot by the drain. In
rounds, `wa` a block, that is the theorem's `wa / p^wa`, the decision
falling within a wave of the good block. **SH-MM11k**
(`expected_firstGoodBlock_le_four`) is the same at `4 ≤ wa`, where MM2's
weaker form promises one committed candidate per populated round
(SH-MM11b): the first `m` blocks are all bad with probability at most
`((n^wa − 1) / n^wa)^m` (`firstGoodBlock_ge_prob_le_four`), and the
series sums to `n^wa` (`one_sub_badBlockBoundOne`), the paper's
`1 / p^wa` at its `p = 1/n`.

**The wait for an anchor, in intervals** (`noCommitProbOn`,
`firstGoodInterval`, SH-MM11l, SH-MM11m). The asynchronous section counts the
sparsity of the control slots: an interval holds `c = I / period` of
them, an interval retains its period when all of them are skipped, and a
scan therefore finds its anchor within an expected
`1 / (1 − (1 − p)^c)` intervals. **SH-MM11l** (`noCommitProbOn_le`) is the
inner bound, SH-MM11f read at a schedule rather than a stretch, since
control slots sit at multiples of the period: at any strictly increasing
`ρ` whose slots' waves are populated, every slot misses with probability
at most `((f + b) / n)^c`. **SH-MM11m** (`expected_firstGoodInterval_le`)
is the wait: the first `m` scans all miss with probability at most that
bound to the `m` (`all_miss_prob_le`, the box of `no_good_block_prob_le`
with the complement taken slot by slot rather than interval by
interval), and the layer cake (`expected_wait_eq`, now shared with
SH-MM11j) sums the geometric series to its inverse. What the statement does
not do is derive `c` from the interval and the period; it takes the slot
count as given, and the independence across intervals is the uniform
draw's, as everywhere else here.

**The tail of the output** (`undecidedProb`, SH-MM15). Theorem 3's "with
probability `1`" cannot be stated on a fixed record, which is finite and
so populates finitely many rounds; what a finite record admits is a
probability that tends to zero with the horizon, uniformly over records
populated through it, the form SH-MM11f/d already take. `undecidedProb`
draws the coins of `M` blocks of `wa · K` rounds, block `j` opening
interval `j₀ + 2 + q · j`, every `q`-th interval from the second past
the slot's interval `j₀` (`blockRound`, `coinOfBlocks`, which reads the
blocks back and draws a fixed value elsewhere), uniformly
and independently, and measures the maps under which some view holding
the horizon (`blocksHorizon`), at a period sequence matching every
state it derives, has not
derived the state of the slot's interval or leaves the slot undecided
at the adaptive wavelength and schedule. A sequence matching what the
view derives is arbitrary where the scan has stalled, so a slot counts
as decided only under every completion of the derived periods, and a
scan that never reaches the slot's interval counts as a failure.
**SH-MM15a** (`undecidedProb_le`) bounds it by
`2 · ((n^(wa·K) − (n − f − b)^(wa·K)) / n^(wa·K))^(M/2)` at
`2 ≤ ws ≤ wa`, `5 ≤ wa`, `K ≤ I`, `wa ≤ I`, a stride `q` at which a
block of `wa · K` rounds ends before the next opens (`wa · K ≤ q · I`,
so that the block maps read back), a slot at round one or above, under
any update rule keeping the period in `[1, K]`, and the blocks' waves populated
where MM2 reads them: the later good block of a pair holds `wa`
consecutive multiples of `K`, the control slots every scan below its
interval reads above its boundary, so it settles those scans (SH-MM7a at
each scan's schedule) and the periods are derived that far (SH-MM10c); the
earlier good block's first `K` rounds hold the first control round of
its interval at whatever period the view derived, so its coin anchors
that interval; and the later block's first `wa` rounds are the run
above it; so a good block in each half of the `M` decides the slot by
SH-MM14c, and the failure set lies in the union of the two halves'
no-good-block sets, each a product whose every block of the half misses
its all-good maps, of which MM2 counts at least `(n − f − b)^(wa·K)` out
of `n^(wa·K)` (`no_good_block_prob_le`). **SH-MM15c**
(`undecided_tail_tendsto_zero`) is that the bound vanishes as `M` grows,
since `n − f − b ≥ 1`. **SH-MM15d** (`undecidedProb_le_four`,
`undecided_tail_four_tendsto_zero`) is the same at `4 ≤ wa`, the other
wave the implementation accepts for the pair: MM2's weaker form promises
one committed correct candidate per populated round (SH-MM11b), so the
halves are counted at a floor of one and the bound is
`2 · ((n^(wa·K) − 1) / n^(wa·K))^(M/2)`, which vanishes as well, more
slowly. The blocks' coins are drawn after the record is
fixed, as SH-MM11f's are: the adversary that shapes the DAG does not see
them, which is the coin's unpredictability; what the network must supply
is that the blocks' waves be populated. The stride is what the block
length asks of the interval, and nothing else is: at `q = 1` a block
fits in one interval, and at the implementation's headline parameters,
`I = 128`, `K = 64` and `wa = 5`, the blocks open every third interval,
so no bound on `I` beyond the paper's `I ≥ 2 · maxPeriod` enters the
claim; the tail then runs over `q · M` intervals for its `M` blocks.

**The adaptive adversary** (`NonAnticipating`, SH-MM11h, SH-MM15b). A record
fixed before the draw is more than the argument needs. A **strategy**
`σ` answers the coins of the `M` blocks with a record, and is
*non-anticipating with the floor `G`* when at every round of the blocks
`G` names a set of candidates the record commits directly, fixed by the
coins drawn before that round, those of the blocks below and of the
block's own earlier rounds: the adversary shapes the whole DAG from the
draws already revealed, may commit more candidates once a round's coin
is out, as Byzantine certifiers that learn it from the honest shares can,
and may not take a candidate out of the floor after the draw. The
claims read the floor's size, at least `n − f − b`, and nothing else of
the record; that the counting lemma's share survives the round's own
draw is what A5's reveal timing supplies, which the model does not
derive and which the paper now states outright: the candidates are fixed
before the coin can be learned, and the leader is uniform conditional on
the revealed history, earlier coins included. **SH-MM11h** (`no_good_block_prob_le_adaptive`) is the block bound
for such a family: peel the last block, whose bad set the earlier ones
fix once its own rounds are written into the draw, so the count over the
maps whose every block of a set is bad is at most the product of the
per-block counts (`card_all_bad_le`), and inside a block peel the last
round, so at least `c^K` of a block's maps are good throughout
(`card_all_good_ge`), exactly the bound the fixed family gets. The box
argument cannot reach this, since the failure event is no longer a
product once the good sets read the draw. **SH-MM15b**
(`undecidedProb_le_adaptive`) is SH-MM15a against a strategy, at the same
bound and by the same inclusion read at the floor, and **SH-MM15g**
(`decidedAlmostSurely_adaptive`) is SH-MM15e over a sequence of strategies,
the `m`-th answering the coins of its own `m` blocks with its own floor.
What the adversary may not do is shrink the floor of a round with that
round's coin, which is what an unpredictable coin means on a DAG.

**The coin as a process** (`coinMeasure`, SH-MM15e). What one finite record
cannot say, a sequence of them can. `coinMeasure` is
`Measure.infinitePi` of the uniform distribution over the validators, on
whatever discrete measurable structure they carry, so the coin of every
round is drawn at once and independently; on the rounds of finitely many
blocks it is the uniform block map (`coinMeasure_blockCoins_mem`: one
block map is a box on the blocks' rounds, of measure `n^(−MK)`, and a
set of maps the disjoint union of its members' boxes). **SH-MM15e**
(`decidedAlmostSurely`) takes a sequence of records, the `m`-th holding
the waves of `m` blocks populated where MM2 reads them, each with its
own update rule kept in `[1, K]`, and concludes that for almost every
coin some record decides the slot in every view holding its horizon, in
SH-MM15a's sense. The coins under which no record decides it lie, for every
`m`, among those under which the `m`-th leaves it undecided, a set of
measure at most SH-MM15a's bound read through the process
(`undecided_coin_le`), which vanishes (SH-MM15c); so they are null, by
monotonicity alone. The records are any sequence, the prefixes of one
execution among them, since the argument reads each on its own; they are
fixed before the coin is drawn, as SH-MM15a's one record is. This is
Theorem 3's "with probability `1`" as the paper states it, for one slot;
**SH-MM15h** (`allDecidedAlmostSurely`) is every slot at once, each with
its own sequence of records, since the slots are countably many and the
null sets add up. **SH-MM15f** (`anchoredAlmostSurely`) is the same
argument read at the anchor: Theorem 3 (i)'s "some scan finds its
anchor", as an anchored interval above the slot's (`Anchored`) in every
view holding the record's horizon at every matching sequence, for almost
every coin. The two good blocks a failure lacks are the same, since the
earlier one anchors its own interval at its first control slot
(`anchored_of_good_blocks`, `unanchored_coin_le`). **SH-MM15i** (`matchingPer_matches`) supplies the period
sequence these claims quantify over: `matchingPer` is built interval by
interval from the states the view derives at the sequence built so far,
which the state of an interval reading the sequence below it alone
(`periodAt_congr_per`, SH-MM10b's congruence) makes the one every
derivation at it agrees with.

**The drain.** Once the period is `1` every slot is asynchronous, and a
run of `wa` consecutive commits decides every slot below it, including
the slots an earlier period left undecided: **SH-MM9a**
(`AllDecidedBelowOfRun`) states this at any wavelength function with
`1 ≤ w κ ≤ wa` and one slot per round, by the relation's descent below a
committed run, the spanning hypothesis discharged by the identity rounds
at the largest wave. **SH-MM9b** (`AllDecidedBelowAtPeriodOne`) is Theorem
3 (ii) as one statement: with every slot of the asynchronous kind, as
period one has it, under the run clause at
the output schedule, past every round whose window decides below the
horizon there is a slot below which every slot is decided, in any view
caught up to the horizon, so the settled prefix and with it the ledger
(SH-MM13) extend as far as the horizon and the clause reach. The proof is
SH-MM7a's at the output schedule,
since at period `1` the rule is Mahi-Mahi's at `wa` (SH-MM4). The clause is
stated at the output schedule, whose asynchronous leaders are the coin's;
deriving it from the coin is the almost-sure half (§0.1).

**The cost of an asynchronous slot.** The protocol section's arithmetic
for a healthy network is **SH-MM9c** (`AsyncSlotCost`): at one slot per
round and `1 ≤ ws ≤ wa`, an asynchronous slot at round `r` decides at
`r + wa − 1`, which is `wa − ws` rounds later than a synchronous slot
there would, and the synchronous slot `i` rounds above it, for
`1 ≤ i < k`, is decided at most `max(0, wa − ws − i)` rounds before it:
the successor waits at most `wa − ws − 1` rounds for causal ordering and
the wait is nonincreasing in `i`, so delays never compound. Decision
rounds only; output timing is not modelled.

## 5. The period

`Model/Period.lean` states the configuration-sequence model on its own,
importing nothing of Barnacle. Rounds `j·I + 1` to `(j + 1)·I` form
interval `j` (`intervalOf I r = (r − 1) / I`; the arithmetic leaves round
`0` in interval `0`, which no scan reads), each decided under one period.
The **anchor** of interval `j` under period `k` is the interval's earliest
control slot at round `1` or above whose control verdict is a commit,
every control slot of the interval below it skipped
(`IntervalAnchor I K wa coin U V j k i A`, slot `i` of
`controlSlots coin I K j k`); **no anchor** is every scanned control slot
of the interval skipped (`NoAnchor`), an interval without a control slot
among them. The control slots depend on `k`, the period in force at the
interval, which the scan carries and reads them at, as `complete_scans`
does, starting at the interval's first round. The state a scan carries
is the period, the agreed output's next slot and the round of its last
committed leader (`ScanState`, the implementation's `period_schedule`,
`agreed_next` and `agreed_last_commit_round`). The sequence is a
relation, `PeriodAt I K wa coin upd k₀ U V w j st`: interval `0` runs at
`⟨k₀, 1, 0⟩`; an anchored interval advances the agreed output over the
anchor's causal history (`AgreedAdvance`, the implementation's
`advance_agreed_output`: the cursor moves to the least slot that history
leaves undecided, the last commit to the round of the highest leader
committed on the way) and hands interval `j + 1` period `1` when that
commit lies more than `I` rounds below the anchor's round
(`apply_period_update`), its own period when it is interval `0`, the
warm-up, whose window holds the start-up rounds, and the update rule's
answer otherwise; an interval with no anchor keeps the state. A
validator whose scan meets an undecided control slot waits, which is the
absence of a derivation. The
update rule `upd : BlockId → ℕ → ℕ` is any function of
the anchor block and the current period; the paper's replay reads
the anchor's causal history, which the block id determines within one
universe. The wavelength the agreed output is read at is a parameter, so
that the agreement claims hold for any reading.
`adaptiveKind I per` is the kind of each round at the period of its
interval, and `adaptiveSlots coin known I per` the schedule a validator
that derived `per` runs the output relation on: one slot per round, of
that kind, the coin at the rounds `per` makes asynchronous and the known
schedule `known` elsewhere, the wave read at `wavelength ws wa`. The
claims that relate a schedule to the coin one clause at a time (SH-MM14a)
take this schedule as their instance (SH-MM15), and a sequence matching what
a view derives on it always exists (`matchingPer`, SH-MM15i).

`Period/Statement.lean`:

- **SH-MM10a, agreement of the state**: two views deriving a state for
  interval `j` derive the same one, period, cursor and last commit
  alike, at `3 ≤ wa`, under any update rule.
  Induction on the derivation: the periods agree, so the scans read one
  control schedule; the anchor is unique across views, since a lower
  anchor in one view is a skipped control slot of that schedule in the
  other and SH-MM10l forbids it, and an anchor in one view against none in
  the other is the same contradiction; and the advance over an anchor's history is
  unique, since no verdict of that history lies above the anchor's round,
  so the new cursor is the least undecided slot at or past the old one
  and the new last commit the highest commit consumed.
- **SH-MM10b, agreement of the output under the adaptive kinds**: two
  validators that derived the state of every interval the record's
  rounds fall in, each on the schedule its own sequence names
  (`adaptiveSlots`), and decided a slot proposed among them on their own
  schedules, derived the same periods there and agree on the verdict.
  The sequences coincide by strong induction on the interval, the state
  of an interval reading the sequence below that interval only
  (`periodAt_congr_per`, which transports a derivation across the
  schedule): the anchors of the intervals below lie in the record, their
  histories are read at rounds below their own, where the sequences
  already agree and so the schedules' kinds and leaders, so the two
  views advance the agreed output alike (`AgreedAdvance.congr_slots`) and
  SH-MM10a gives the same state; a verdict reads the schedule only at the
  slots its derivation names, all of them proposed at or below the round
  of the anchor block it rests on (`decided_congr_slots`); and SH-MM2
  applies on the one schedule. The bound is not a convenience: a record holds finitely
  many blocks, so above its top round no chain verdict is derivable and
  no period beyond it either, and a claim asking for the *whole*
  sequence would hold only where the period reaches `0`, which is
  Mysticeti at every round but the first.
- **SH-MM10c, the scan ends**: once every control slot of the interval,
  at the interval's period, has a verdict in a view, the view derives
  the next state: the least committed control slot is the anchor, or
  every one is skipped.
- **SH-MM10d, the period advances under the clause**: under Mahi-Mahi's
  run clause at every control schedule a period in range names, with
  the period kept in range (SH-MM10g's hypotheses, since the control set
  is a function of the period), a view caught up to the horizon derives
  a state for every interval whose control slots, and `c + wa` control
  slots above its boundary, decide below it, by SH-MM7a at the interval's
  own schedule and SH-MM10c.
- **SH-MM10e, the period reaches `1`**: the failover, as
  `apply_period_update` applies it. An interval that finds an anchor
  at round `r` below which the agreed output, advanced over the anchor's
  history, has its last commit at a round `last'` with `last' + I < r`
  hands the next interval period `1`, whatever the update rule would
  answer. The test is the scan's own, on the state it already carries,
  so no clause is placed on the rule and the recovery claims need
  nothing of Algorithm 3 but its range; where the paper's premise on the
  update rule, read literally, forbids every recovery from period `1`
  (§7). The anchor is a hypothesis: nothing deterministic forces one,
  and its existence is the almost-sure half (§0.1).
- **SH-MM10f, SH-MM10n, SH-MM10g, SH-MM10o, the shape of the adaptive run**: at any
  period `k ≥ 1` with `2k ≤ I`, every interval holds two asynchronous
  rounds, the paper's reason for `I ≥ 2 · maxPeriod`, and so does every
  window of an anchor at round `I` or above, the adaptive section's
  "every interval and every window" (SH-MM10n); if the initial period lies
  in `[1, K]` and the update rule keeps a period there, so does every
  derived period, the failover's `1` and the warm-up's included; and if
  the initial period divides `K` and the update rule keeps a period a
  divisor of `K`, so does every derived period (SH-MM10o), the paper's
  "every candidate divides maxPeriod" carried through the scan, which
  Algorithm 3 supplies at a power-of-two bound (SH18n).
- **SH-MM10h, SH-MM10i, the agreed output**: every slot the agreed output
  consumed is decided in the view that derived it, since the anchors'
  histories lie inside that view and the laws carry a verdict out of a
  history (`2 ≤ w κ`), which is what `assert_agreed_prefix` checks in the
  implementation's tests; and a slot the view leaves undecided is never
  consumed, so the cursor and the last commit stay at or below it in
  every state the view derives. The second is what puts the failover's
  test below a stuck slot, and both speak of slots at round one or above,
  the agreed output starting at slot `1` as the implementation's does.
- **SH-MM10j, a window resolves an asynchronous slot of every candidate**:
  above round `I` the window holds `I + 1` rounds, `round A − I` to
  `round A` (`windowBottom`), so an asynchronous round of period `k` has
  its decision round inside it when `I ≥ k + wa − 2`; at `I ≥ 2K` alone
  the window resolves a slot at some anchors and none at others (§7,
  finding 8), and an anchor at round `I` itself, whose window starts at
  round `1` and is one round short, resolves none at `I = K + wa − 2`.
- **SH-MM10k, SH-MM10p, the control schedule enumerates the control rounds,
  which carry a coin**: the rounds of `controlSlots coin I K j k` are
  exactly the multiples of `k` up to the boundary and the multiples of
  `K` above it, the implementation's `is_control_round` for the scan of
  interval `j`; and under a period sequence whose every period divides
  `K`, every control slot of the scan of interval `j` that lies in the
  interval or above it is an asynchronous round of the adaptive
  schedule, led by the coin (SH-MM10p, `controlRound_adaptive_async`): up
  to the boundary a multiple of the interval's own period, above it a
  multiple of `K` and so of the period of the interval it falls in,
  which is the protocol section's reason the multiples of the bound
  carry a coin whatever period the scan fixes. With SH-MM5b, the two
  readings agree on every such slot whenever either verdict is direct.
- **SH-MM10l, control verdicts agree per scan**: two views agree on the
  control verdict of every slot of one scan's schedule, under any coin,
  MM1c at that schedule; verdicts of different scans are never compared.
- **SH-MM10q, the gating rule**: a state for interval `j + 1` carries a
  state for interval `j` and a closed scan of `j` at that state's
  period, with an anchor or with none (`periodAt_gated`). The adaptive
  section's "a slot is evaluated once its interval's period is known" is
  therefore a property of the derivation rather than a side condition:
  waiting is the absence of a derivation, so no round of interval
  `j + 1` is read at any period until the scan below it closes. The
  statement is case analysis on `PeriodAt`, which is the point, since it
  is what "modelled by construction" has to mean to be checkable.
- **SH-MM10m, the first interval keeps its period**: the warm-up of
  `apply_period_update`, at a positive interval: at an anchor of
  interval `0` the next interval runs at the initial period, the agreed
  output advanced all the same. The failover cannot fire there, the
  anchor lying at round `I` or below and the output's last commit at
  `0` or above.
- **SH-MM14a, output liveness under the failover**: in a view that derived
  every state up to a run's last round, if some interval at least two
  past a slot's finds an anchor under the period the view derived for
  it, and above that interval the coin names
  a committed candidate at `wa` consecutive rounds that lead the output's
  slots there, then the slot is decided once the view holds the run's
  decision rounds. An anchor two intervals up lies more than `I` rounds
  above the slot, so while the slot waits the agreed output's last
  commit lies below it (SH-MM10i),
  SH-MM10e fires at the anchored interval and,
  by induction on the derivations, every interval up to the run runs at
  period `1`; the run's rounds then carry wave `wa`, its coins commit
  their candidates directly (SH-MM11e's argument at the output schedule),
  and the drain SH-MM9a decides every slot below the run. At `2 ≤ ws ≤ wa`,
  `3 ≤ wa` as SH-MM10a, one slot per round and a positive interval. This is
  Theorem 3 (ii) and the asynchronous half of Definition 1's validity,
  deterministic given the anchor and the run; that the coin supplies both
  almost surely is the remaining half of Theorem 3.
- **SH-MM14b, every slot is decided under the clause**: SH-MM14a with its two
  events read off Mahi-Mahi's run clause at every control schedule a
  period in range names, the period kept in range (SH-MM10g's premise) and
  `c + wa` control slots fitting in an interval at every period up to
  `K` (`(c + wa) · K ≤ I`). At the second interval after the slot's, the
  clause at the interval's own schedule places a run of `wa` good
  control slots inside it: the run's first slot commits directly and the
  run settles every control slot below it (SH-MM7a), so the interval has an
  anchor at or below that slot. At period `1` the control schedule of
  the next interval is every round up to its boundary, so the clause at
  that schedule places the run of rounds SH-MM14a needs. Every slot whose
  interval lies three intervals and a window below the horizon is then
  decided, in a view caught up to the horizon that derived every state
  below it. The clause family, one schedule per candidate period, is the
  deterministic stand-in for what the coin gives almost surely, as
  SH-MM7a's is.
- **SH-MM14c, output liveness from a good coin and a good run**: SH-MM14a with
  its two events named by the coin alone. The first control round of an
  interval at least two past the slot's, at the period the view derived
  for it (`firstControlRound I j k`, in the interval once `1 ≤ k ≤ I`),
  has no control slot of the interval below it, so a good coin there
  commits the first control slot and the interval has its anchor with
  nothing to settle; `wa` good coins above that interval are the run
  SH-MM14a needs. Two events at named places, each of a fixed positive
  probability: the form SH-MM15 draws from the coin, a block of `K` good
  coins from the interval's first round covering its first control round
  at every period up to `K`.

**The replay** (`Model/Replay.lean`, `Replay/Statement.lean`). Algorithm
2 as data: `ofAnchor U A I` reads the window's evidence off the anchor's
causal history at the rounds `round A − I` and above, as
`collect_window` takes it, per proposal round, wave and
candidate author, counting distinct validators (a candidate is committed
when a quorum certify it within the window, skipped when a quorum of the
window's vote-round blocks blame the author's slot, certified when the
window holds one certificate), the `3f + 1` pair's reading of the paper's
support; `BlueBottlePair.Replay.ofAnchor` is the `5f + 1` pair's, the
decision-round votes themselves, Odontoceti's references one round up at
wave two and Async BlueBottle's cone votes two rounds up otherwise, with
`n − 3f` of them the indirect threshold, the implementation's
`merged_certificates`; where the blame round lies, the vote round or the
decision round, is `Config.merged`; `score` is `REPLAY(W, k')`'s three passes
over that evidence, in exact rationals, the probes of the canary rounds
(`probeRate`) standing in for the unprobed synchronous slots; `select`
is the hysteretic selection among the powers of two up to the largest
candidate (`candidatesUpto`), ties favouring the larger candidate and
the hysteresis keeping the current period unless a candidate improves on
it; `anchorUpdate` is the whole as an `UpdateRule`. **SH18a**
(`select_mem`) and **SH18b** (`select_score_le`): the selection stays
among the candidates and never worsens the score.
**SH-MM18c** (`certified_of_commits`, `not_certified_of_skips`): in the
window's evidence a committed candidate is certified and a skipped one
is not, at `2 ≤ w`. **SH-MM18d** (`window_count`): Lemma 3's count on the
window: at a round the window retains whose boost round and decision
round a quorum has populated *within the anchor's history*, at least
`n − f − b` authors are marked committed at wave `wa`, MM2 read on the
history as a record of its own, whose votes and certificates are the
universe's restricted to it (`candidatesAt_toRecord`,
`certificates_toRecord`). The hypothesis that the quorum's blocks lie in
the window is §7's finding 6. The passes are recursions on the round
index, as Algorithm 3 walks them: `timingAt` from the top of the window
down, `firstCommitAt` the earliest expected commit at or above a round,
`gateAt` the latest expected decision below it. **SH18e**
(`bounded_timingAt`): every round's expected decision lies at or above
the round, its expected commit at or above its decision, and both at or
below the window's top, so the top is the penalty an unresolved outcome
pays and no more. **SH18f** (`async_term_bound`), Lemma 3's second
sentence in the form that is a theorem: at an asynchronous round of the
window whose committed candidates are not skipped (SH-MM18c), the replay's
commit term is at most the mean over the `n` candidates of the decision
round for the `c_r` committed ones and the window's top for the rest,
which SH-MM18d bounds below `c_r ≥ n − f − b` under any scheduling. The
bound charges every candidate without a direct commit the window's top;
the asynchronous rule's own latency on the same data is not modelled,
and the lemma's "at most the value the asynchronous rule attains" and
its selector corollary are not claimed (§7, finding 10). **SH-MM18g**
(`commits_sound`): a candidate the window marks committed is directly
committed on the DAG, so a probe's success is a certificate quorum the
DAG holds: the adversary can suppress the probes' evidence of the
synchronous rule, never manufacture it. What this does not give is a
one-sided bound on the synchronous term: the replay
extends the probes' rate to the unprobed synchronous slots, and a
scheduler that serves the canary rounds' leaders alone raises that
estimate above what those slots hold (§7, finding 10). SH18e and SH18f
ask `2 ≤ ws < wa`, so that a decision round lies
at or above its slot and an asynchronous round is not read as an
unprobed synchronous one, which the algorithm does when the waves
coincide. **SH18h** (`anchorUpdate_range`): with candidates in
`[1, K]` and a current period there, `anchorUpdate` answers a period in
`[1, K]` at every anchor, the current period or a candidate
(`select_eq_or_mem`), and the failover's `1` is the scan's own (SH-MM10e)
and lies in the range too; the range hypothesis SH-MM10g, SH-MM10d, SH-MM14b and
SH-MM15 place on the update rule, discharged for the paper's rule. **SH-MM18i**
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
period, at `1 ≤ ws`. **SH18m** (`probe_exists_of_odd`) is the sentence
itself: an odd spacing is coprime to every power of two, so every
candidate of at least two has a probe. **SH18k** (`select_hysteresis`)
and **SH18l** (`best_tie_rule`) are the adaptive section's selection
rule: the selection leaves the current period, a candidate itself, only
for a candidate whose score is below `1 − ε` times the current period's,
and takes the best candidate whenever that one's is; and the best
candidate scores no worse than the current period and than every
candidate, is the current period whenever that scores as well, and is
otherwise the largest of the candidates at its score, whatever order the
candidates are listed in, by an invariant of the selection fold
(`TieInv`, `tieInv_step`). **SH18n** (`candidatesUpto_dvd`,
`anchorUpdate_dvd`): at a power-of-two bound every candidate divides it,
and Algorithm 3 answers a divisor of the bound from one, the current
period or a candidate, which is what SH-MM10o asks of an update rule. What
the selection can see of a window whatever
its evidence (`score_le_sum_top`, `sum_floor_le_score`): every score
lies between the sum of a commit floor's excess over the round and the
sum of the delays to the window's top, so at waves `3` and `5` with a
probe at every round, where periods `1` and `2` commit no round below
two or three rounds up (`halfFloor`), they score at least half of what
period `4` can on a window of at most nine rounds, and hysteresis `1/2`
answers period `4` at every anchor of an eight-round interval
(`anchorUpdate_half_retains`), which is finding 3 on the selector
(§8, `RotatingStall.lean`). What leaves such a period is the scan's
failover, not the replay, and on that family it fires at the second
interval's anchor (§8, `Failover.lean`).

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
certificate with the certifiers `w κ − 1` rounds above a candidate of
kind `κ`; its `Local` and `Commits` laws hold at two rounds and above,
its `OfCoverage` law at three, the wave-three case by the core's
argument and the higher waves by Mahi-Mahi's. The liveness headline
`Support.Lives` follows. `Banded`, `LocalTruncate` and the `Safe`
headline hold at every `w` of at least two rounds, since the wave is
read at the kind (§2).

**SH-MM6** (`Liveness/Statement.lean`) is the timed model at this support:
**SH-MM6a**, a reliably led slot commits in every view caught up to its
decision round on a DAG a reliable quorum has synchronised and populated
through it, by the direct rule, at whichever wave the slot's kind
carries; **SH-MM6b**, past
any slot the schedule offers a run of `c` reliably led slots spanning
eligibility, and everything below the run is decided once the DAG is
covered through its decision rounds. At one slot per round `c = wa`
spans. Two clauses of Theorem 2 need no timed model: **SH-MM6c**, a slot
whose leader has no block at its round is directly skipped in every view
holding its vote round, once a quorum populates that round, since no
cone holds a candidate and every block of the round blames; and
**SH-MM6d**, the paper's "partial dissemination alone does not defer": a
candidate that one reliable block references one round up, its leader's
only block at that round, is directly committed in every view holding
its decision round, once the quorum is synchronised from that round and
populates the wave, at `4 ≤ w κ`. Synchrony carries the candidate into
every reliable cone from two rounds up, the reliable voters vote for it,
every reliable block at the decision round references all of them and
so certifies. The leader may be Byzantine, so long as it did not
equivocate; neither clause asks the quorum to be correct. **SH-MM6e**,
Theorem 2's Byzantine-led clause as the anchor rule has it: at one slot
per round, a slot is decided once every slot from its floor up to some
reliably led slot is decided, whatever led them. The reliably led slot
commits directly (SH-MM6a), so the least commit at or above the floor is
the anchor, and every slot between, decided but not committed, is a
skip the search passes over (`indirect`). What the hypothesis excludes
is an undecided slot at the floor, one led by an equivocating Byzantine
validator (§7, finding 7). **SH-MM6f** takes the chain of floors itself:
hop from a slot to the first slot at or above its floor the view does
not skip (`FloorHop`), and again from there; if the chain reaches a
reliably led landing in `h` hops, the slot it started from is decided.
Downward induction: the last landing commits (SH-MM6a), and a landing whose
successor commits is decided by SH-MM6e's argument and not skipped, so it
commits in turn and anchors the landing below it. **SH-MM6g** is what
bounds the chain at the implementation's known schedule, `r mod n`: a
validator outside the reliable set `T` leads one residue, which spoils
the `c` windows of `c` consecutive rounds ending at it and no others, so
at `c · (n − |T|) < n` one of the `n` windows a cycle holds is wholly
`T`-led and the schedule repeats it past every round (`FairRunOn T c`);
and one reliable leader sits within `n − |T|` rounds of every round,
since a window of `n − |T| + 1` rounds leads that many distinct
validators. At `c = 3` and `n = 3f + 1` every correct quorum qualifies,
which discharges SH-MM6b's fairness hypothesis for the schedule the
implementation runs; at `c = wa` it does not, so the asynchronous rounds
rest on the coin (SH-MM7, SH-MM14a) and not on the schedule. Together with SH-MM6e
this is Theorem 2's Byzantine-led clause as a round count, `w + b + c`
rounds above the floor.

**SH-MM6k and SH-MM6l** say where SH-MM6a's hypothesis comes from, and they are
the two execution disciplines the repository already carries. The
reactive one (`ReactiveS`, `Model/Reactive.lean`) is the core's
reactive pace with its leader wait asked at the rounds that carry it
(`waits`, the synchronous slots and the canary rounds, since nobody
waits for the hidden leader of an asynchronous slot, which the core's
`ReactivePace` would ask at every reliably led slot), plus one clause:
time advances with rounds, a builder never waits past its timeout, and
at the round above a reliable leader of a waiting round a block either
votes or its builder waited the timeout out and votes for any leader
block it holds. At a wave of four rounds or more that is enough, since
the vote round then sits two rounds or more below the certifiers and the
votes reach them through the DAG; at the wave of three the certify round
is the vote round's successor, so a certifier must reference the votes
itself, and `cert_or_wait` is that wait, stated at wave three alone and
at the waiting rounds; the paper's pacing states it too, as Mysticeti's
vote wait, and it is what the wave of three needs of an execution. SH-MM6k is
stated for a slot at a waiting round. `SynchronisedOn` is false by
design in such an execution, and appears in neither clause. The timed
one (SH-MM6l) instead
discharges `SynchronisedOn` from a `ViewPace` whose timeout grows at a
rate that clears the delay, which the core proves as
`synchronisedOn_of_rate` at `max (2Δ + proc, gst)`; it says nothing new
about the rule, only where the hypothesis comes from, and it is worth
what the core's `ViewPace` is worth. Neither bounds a wall-clock
latency: the model's only unit is the round.

**SH-MM6h** counts the hops themselves, which is how the paper states the
clause. A reliably led round commits (SH-MM6a) and a view decides a slot one
way, so a reliably led round is never one of the skips a hop passes over:
if no landing were reliably led, neither would be any round from a
landing's floor up to the next landing, and the only rounds left free
would be the `ws − 1` between a landing and its own floor. Two landings
at one residue would then bound a whole number of cycles, each holding
`|T|` reliably led rounds, all of which would have to fall in those free
rounds; counting the two against each other gives `n ≤ ws · (n − |T|)`.
So at `ws · (n − |T|) < n` the landings' residues are distinct, only
`n − |T|` residues are led from outside `T`, and the chain reaches a
reliably led landing within that many hops, which with SH-MM6f decides the
slot it started from. The bound is the synchronous wave's: at `ws = 3`
and `n = 3f + 1` it holds for every correct quorum, and at the
asynchronous wave it does not (§7, finding 7).

**SH-MM6i** is the same count with the paper's `b`, the Byzantine
validators, in place of `n − |T|`. It asks one thing more of the
validators outside `T`: those that are not Byzantine have crashed, with
no block from the synchronised round on. A crashed leader's slot is
directly skipped once the reliable set populates its vote round (SH-MM6c),
and a landing is a slot the view does not skip, so every landing led
from outside `T` is Byzantine-led; the residues are distinct as in SH-MM6h,
the Byzantine validators hold `b` of them, and one of the first `b + 1`
landings is reliably led. The chain's start is asked not to be skipped
either, which Theorem 2's undecided slot is not.

**SH-MM6j** (`floorChainDecidesWithinRounds`) turns the hop count into
Theorem 2's round count, `(b + 1)(ws + f)` above a synchronous floor,
with `f` read as `n − |T|`. A reliably led round lies within `n − |T|`
rounds above any floor (SH-MM6g), it commits under synchrony (SH-MM6a) and so
is not skipped, and the landing of a hop is the least unskipped slot at
or above the floor (`floorHopOf_floorLandingOf`), so the chain of floors
climbs by at most `ws + (n − |T|)` rounds a hop. One of its first `b + 1`
landings is reliably led (SH-MM6i), and that landing's commit decides the
chain's start (SH-MM6f); every decision round the argument reads lies within
`(b + 1) · (ws + (n − |T|))` rounds of the slot, which is what the view
is asked to hold.

### 6.1 The anchor search at a mixed period, SH-MM6m to SH-MM6p

SH-MM6h, SH-MM6i and SH-MM6j read the wave at the constant `ws`. The paper states
Theorem 2's anchor clause at the dial itself, where a hop of the chain
may land on a known-leader slot that no coin governs and on a coin slot
no schedule names. Restating them there changes two things and leaves
the rest of the argument alone.

**The descent takes a commit.** SH-MM6f gets the top of the chain committed
from a reliable leader under synchrony. **SH-MM6m**
(`floorChainDecidesFromCommit`) asks for the commit itself instead, and
then needs no quorum, no synchrony and no horizon: a landing whose
successor commits is decided and left unskipped by its own hop, so it
commits in turn and anchors the landing below it. That is what lets the
chain stop wherever the coin decided something.

**The count loses the coin's rounds.** SH-MM6h counts, over a span of whole
round-robin cycles, the rounds the schedule leads from `T`: at least
`|T|` a cycle, each of which must fit in the `ws − 1` rounds a hop leaves
free, which forces `ws · (n − |T|) < n`. At a period a coin round is led
by nobody the schedule names, so those rounds drop out of the count. At
most `⌈n / p⌉` of every `n` rounds carry a coin (`card_multiples_le`), so
the bound becomes `ws · (n − |T|) + ws · ⌈n / p⌉ < n`
(`roundRobin_residues_distinct_exempt`, which the constant-wave case is
now an instance of, at the empty exemption).

**SH-MM6o** (`floorChainReachesAtPeriod`) is SH-MM6h at the dial. It asks in
addition that every asynchronous slot at or above the chain's start be
decided, which is the coin's business (SH-MM7a) and not the schedule's; such
a landing is then committed, a landing being unskipped by definition, and
the chain stops there. Otherwise every landing is synchronous and led by
the round robin, and the count above applies. **SH-MM6n**
(`periodicRoundRobinReliableSync`) is SH-MM6g's second half at the dial:
every window of `n` rounds holds one round of each residue, so `|T|` of
them are reliably led where the leader is known and at most `⌈n / p⌉`
carry a coin, so a reliably led synchronous round lies within `n − 1`
rounds of every round once `⌈n / p⌉ < |T|`. The bound is `n − 1` and not
SH-MM6g's `n − |T|`: a reliable residue may fall on a coin round, and the
schedule cannot say which. **SH-MM6p**
(`floorChainDecidesWithinRoundsAtPeriod`) is the round count, in the
paper's shape `(b + 1) · (ws + W)` with `W` the wait SH-MM6n supplies, plus
the one asynchronous wave a decision round in that range may carry.

⚠ **The count is empty at the tight committee.** `⌈n / p⌉ ≥ 1` for every
committee and every period, and at `ws = 3`, `n = 3f + 1` with a bare
reliable quorum `|T| = n − f` the constant-wave bound `3f < 3f + 1` holds
with exactly one round to spare, which the coin's rounds take. So SH-MM6o
and SH-MM6p say nothing there, and the chain is bounded by the coin rather
than by the schedule. The bound holds as soon as fewer than `f`
validators lie outside `T`, or the committee is larger;
`LeanDagTest/Steelhead/Counterexamples/PeriodicFairness.lean` has both
the failure and two instances where it holds. The paper states the
round count without a condition on the period, which is finding 12.

## 7. Findings for the paper

1. **The control slots are fixed by rule, and the claims are per
   scan.** A control set read from the view, or from the period above
   the interval under scan, which the scan is to fix, would let two views
   enumerate different control slots and break Theorem 4;
   `Counterexamples/ControlSlotsFromView.lean` (§8) shows it on data,
   with the shares as the block payload: two views of one DAG, neither
   inside the other, that count different rounds as control slots and
   anchor interval `0` on rounds `1` and `2`, where the rule anchors both
   on round `1`. The paper's
   adaptive section now defines the control slots of a scan by rule, the
   interval's asynchronous slots and the multiples of `maxPeriod` above
   its boundary, and the arc states the period, its agreement and
   the run clause per scan (SH-MM10k, SH-MM10l, SH-MM10d), so that a round above
   the boundary may carry one verdict in the scan of interval `j` and
   another in that of `j + 1`. Theorem 3 (i)'s sketch now carries the
   run as a note: an undecided control verdict resolves
   once `wa` consecutive control slots of the same scan commit, above
   the boundary `wa` consecutive multiples of `maxPeriod`, whatever
   their spacing (SH-MM7a at any schedule whose rounds strictly increase),
   and not through any one later commit while a control slot between
   stays undecided. The probabilistic tail (SH-MM15) accordingly reads
   blocks of `wa · maxPeriod` rounds, which hold such a run, one block
   every `⌈wa · maxPeriod / I⌉` intervals above the slot's; no bound on
   the interval beyond the paper's `I ≥ 2 · maxPeriod` enters, and at the
   implementation's headline `I = 128`, `maxPeriod = 64`, `wa = 5` the
   blocks open every third interval.
2. **The simulator's adversary does not exhibit the stall.** Delaying
   the leader's messages to everyone yields a direct skip, which the
   anchor search passes over. The adversary that delivers the leader
   block to exactly `f + 1` validators produces neither quorum, and it
   is the one the stall needs.
3. **Algorithm 3's selector can retain a stalled period.** At four
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
   the rule is consulted and which the paper's Algorithms 2 and 3 now
   carry as a branch of their own, ahead of the replay;
   `Failover.lean` (§8) shows it firing on that family and the stalled
   slot decided once the coin runs.
   `RotatingStall.lean` (§8) proves the retention at every anchor: on
   that family Algorithm 3 at hysteresis
   `1/2` answers `4` whatever the anchor block, since the window of an
   anchor spans at most nine rounds,
   on which periods `1` and `2` score at least half of what period `4`
   can, and at period `4` slot `3` is never decided, so no block above
   round `2` is ever output. `ReplayStartup.lean` and
   `ReplayShortWindow.lean` show the retention on tied windows.
4. **Theorem 3's premise is the failover, which the replay's selector
   alone does not supply.** The theorem's premise is now the failover as
   implemented: period `1` at an anchor whose window holds no commit of
   the agreed output, before the update rule is consulted. Its earlier
   premise, that a window in which no synchronous slot commits maps to
   `k = 1`, was neither Algorithm 3's rule nor enough. Algorithm 3 keeps
   the period on a window without a control commit and otherwise takes
   the replay's argmin under hysteresis and ties toward the larger
   candidate, of which finding 3 is one consequence. Granted anyway, that
   premise does not give liveness: an adversary that lets one
   synchronous slot above the stuck one commit in every window keeps the
   period while the output stays stuck. Read literally it also forces
   `upd j A 1 = 1`, since at period `1` no synchronous slot exists to
   commit, so it forbids every recovery from period `1`. The
   implementation asks nothing of the rule: its scan tests the agreed
   output's own last commit against the anchor's round (§5), which no
   commit above a stuck slot can satisfy, since the agreed output stops
   at the stuck slot (SH-MM10i); a count of commits over the window, which
   never sees the stuck slot below it, cannot read that. SH-MM10e and SH-MM14a
   state the failover in that form.
5. **Theorem 2's ordering bound holds in expectation, not for every
   coin sequence.** The theorem now orders every honest block with
   probability `1`, in expectation within `wa / p^wa` rounds above an
   asynchronous floor; its earlier form promised `O(wa + b)` rounds
   outright. At period `1` every slot is the coin's, and a uniform coin
   names the one absent validator at `N + 1` rounds in a row with
   probability `n^-(N + 1) > 0`, for every horizon `N`; on a DAG whose
   three reliable validators reference one another at every round while
   validator `0` never proposes, no slot below the horizon then commits
   and no settled prefix outputs a block, although every reliable round
   is populated and synchronised from round `0` and the reliable
   round-`1` block exists (`LeanDagTest/Steelhead/Counterexamples/CoinDelay.lean`,
   `positive_no_output`). What the arc checks is the tail, with
   probability tending to one (SH-MM11i, SH-MM15), its mean, the wait for the
   first good block, at most `1 / p^wa` blocks in expectation (SH-MM11j),
   and the ordering itself almost surely (SH-MM15e). The deterministic part
   of Theorem 2 is the synchronous slots'
   (SH-MM6a) and the crashed leaders' (SH-MM6c).
6. **Lemma 3 counts on the DAG, the replay reads the window.** The
   lemma's proof applies the counting lemma to every candidate at once;
   the counting lemma counts the certificates the DAG holds, and the
   replay counts those the window holds, the anchor's causal history at
   the rounds `round A − I` and above. The history holds a quorum's worth of blocks
   at every round, by quorum references, but not necessarily one quorum's
   blocks at both the boost round and the decision round, which the
   counting lemma reads; under asynchrony an anchor's references may omit
   any `f` validators' blocks at each round. SH-MM18d states the lemma for
   the window under the hypothesis that a quorum has populated both
   rounds within the anchor's history, which synchrony from below the
   window gives. The paper adopted it: Lemma 3 now reads "for every round
   `r` of a window that holds the blocks of one quorum at every round of
   `r`'s wave", which is SH-MM18d's hypothesis.
7. **An equivocating Byzantine leader at the floor is the anchor.**
   Theorem 2 said an asynchronous slot whose Byzantine leader equivocates
   "is decided by its anchor once the first honest-led slot above its
   floor commits, at most `b` slots higher"; it now says "once every slot
   from its floor up to the first commit above it is decided", SH-MM6e's
   shape, and counts `b` hops of at most `ws + f` rounds each at a
   round-robin schedule with `ws f < n`, so `(b + 1)(ws + f)` rounds. The anchor search stops at
   the first commit-or-undecided slot at or above the floor, and a slot
   whose leader equivocates is undecided, two votes each way forming
   neither quorum; so when the slot at the floor is led by an
   equivocating Byzantine validator, the search waits on it, whatever
   commits above. `LeanDagTest/Steelhead/Counterexamples/ByzantineFloor.lean` shows it at
   wave `3` on thirty blocks: validator `0` leads slots `0` and `3` and
   equivocates at both, the honest-led slot `4` commits directly, and
   slot `0` is undecided in the full view. The chain of floors advances
   one wave a hop and the same Byzantine validator may lead every hop,
   with probability `b / n` each under the coin, so what decides such a
   slot is a run of reliably led slots above its floor (SH-MM6b, SH-MM9a), or
   one reliably led slot above the floor with every slot between
   decided (SH-MM6e), or a chain of floors reaching a reliably led landing
   (SH-MM6f), and no bound in `b` alone holds on an arbitrary schedule. At
   the implementation's round-robin schedule the paper's bound does hold,
   in hops: at `ws · (n − |T|) < n`, which the synchronous wave clears at
   `n = 3f + 1`, the chain reaches a reliably led landing within
   `n − |T|` hops (SH-MM6h), within `b` once every other validator outside
   `T` has crashed (SH-MM6i), and a reliable leader sits within `n − |T|`
   rounds of every round with a reliable run of three past every round
   (SH-MM6g). The bound is the schedule's, not the decision rule's, which
   is how the paper now argues it; the round count `(b + 1)(ws + f)`
   itself is SH-MM6j, as `(b + 1) · (ws + (n − |T|))` above an unskipped
   slot at SH-MM6i's schedule.
   The paper counts `b` hops, which its fault model supports: a leader
   that never proposes draws `n − f` blames and is skipped, so the chain
   lands only on leaders that proposed and only the equivocators among
   them block it, and two landings of one leader would need a full cycle
   of the schedule between them, which `ws · f < n` leaves too few faulty
   leaders to fill. The arc proves `n − |T|` because its model carries a
   reliable set and no crash class, so a validator outside `T` that
   proposes nothing is not distinguished from one that equivocates; SH-MM6i
   supplies the `b` count under the hypothesis that the others have
   crashed. The distance between the two is a model change, not a missing
   argument.
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
   (SH-MM10j). The paper states both bounds, in the appendix's outline
   rather than in the adaptive section, which defers them there; the
   implementation validates only the first (`protocol.rs`), and 2 of the
   9 configurations of its control-slot fuzz, `(I, maxPeriod, wa) =
   (4, 2, 5)` and `(2, 1, 5)`, violate the second, the first of them
   being `rw44`'s.
9. **No per-hop bound holds for the anchor search under the coin.**
   Theorem 2 bounded each hop of the search onto a Byzantine-led slot by
   `b/n`; the clause is gone, and the Lean appendix's trust-partition
   item records the witness below. A landing of the search is not a function of the coins below
   it: whether a pending slot is skipped turns on a commit above it, and
   the coin that commits that anchor both skips the slot, shifting the
   landing up by one, and leads the next landing. On thirty-six blocks
   at wave `3` with validator `0` Byzantine (`HopBound.lean`, §8), the
   coins `(3, 6) = (0, 0)` land the search on slots `3` and `6`, and the
   coins `3 = 0`, `6 ≠ 0`, `(4, 7) = (0, 0)` on slots `4` and `7`; the two
   patterns are disjoint, both Byzantine-led twice, and together have
   probability `19/256`, above `(b/n)^2 = 1/16`. What holds is the run
   form (SH-MM11i): at period one a slot below a block of `wa` good coins is
   decided, so the search outlasts `M` blocks with probability at most
   `((n^wa − (n − f − b)^wa) / n^wa)^M`, which is the expectation the
   paper states in place of the per-hop clause.
10. **Lemma 3's comparison and its selector corollary are not what the
    replay's bound gives.** SH18f bounds the replay's asynchronous term
    by the mean of the decision round over the committed candidates and
    the window's top over the rest; the asynchronous rule's own latency
    on the same data has no definition in the model, so "at most the
    value the asynchronous rule attains" and "an adversary cannot make
    the replay prefer the synchronous rule" are not theorems, and the
    second is false as stated for the synchronous term: SH-MM18g says a
    probe's success is a certificate quorum the DAG holds, and the replay
    extends the probes' rate to every unprobed synchronous slot, so a
    scheduler that serves the canary rounds' known leaders and starves
    the others makes every probe succeed while no unprobed slot holds a
    certificate, and the estimate of the synchronous rule rises above
    what those slots would achieve. The failover bounds what that costs,
    the period alone, not liveness. The paper adopted this too: the
    comparison with the asynchronous rule's own latency is gone, and the
    adaptive section now sends the starved-canary case to the failover.
11. **A1's reference rule lies outside the substrate.** The rule
    `Core::try_new_block` implements references every held block the
    author's parent does not cover, which puts a block delayed past its
    own round into later blocks; the substrate's references sit one
    round back (`ValidWrt.predecessor`), so that rule cannot be stated
    on it and SH-MM17d takes its consequence, a round by which every
    reliable validator has referenced the block, as a hypothesis. The
    rule also feeds the rule's own verdicts, a late reference carrying a
    certificate into an anchor's history, so a faithful substrate is a
    core change, not an arc's.

12. **Theorem 2's round count needs a condition on the period that the
    body does not state.** The count rests on the round robin leading
    `|T|` rounds of every cycle from the reliable set, and at a period a
    coin round is led by nobody the schedule names. Deducting those
    turns `ws · (n − |T|) < n` into
    `ws · (n − |T|) + ws · ⌈n / p⌉ < n` (SH-MM6o, SH-MM6p), and since
    `⌈n / p⌉ ≥ 1` always, the count says nothing at `ws = 3`,
    `n = 3f + 1` with a bare reliable quorum, where the constant-wave
    bound holds by exactly one round. There the chain is bounded by the
    coin and not by the schedule. The second factor changes too: SH-MM6g's
    `n − |T|` becomes SH-MM6n's `n − 1`, a reliable residue being able to
    fall on a coin round. Both are on data in
    `LeanDagTest/Steelhead/Counterexamples/PeriodicFairness.lean`.

Findings 1, 4, 5, 6, 7, 8, 9 and 10 went to the authors and the paper's
text is their result, so each is kept as the reason the paper now says
what it says; 2, 3, 11 and 12 describe divergences that stand.

**Three behaviours of the implementation the arc does not reach**,
recorded so that they are not taken for defects of either. The tail is
stated at `wa ≥ 5` with the counting lemma's `n − f − b` (SH-MM15a) and at
`wa ≥ 4` with its floor of one (SH-MM15d), the two waves the implementation
accepts for the Mysticeti/Mahi-Mahi pair; the `wa = 3` it forces for the
BlueBottle pair is outside the arc altogether (§3), and not by a choice
of bound: Mahi-Mahi's `GoodNonempty` needs the vote round at or above
`r + 2` and `GoodCard` at or above `r + 3`, which is where `4 ≤ w` and
`5 ≤ w` come from at `3f + 1` quorums, so a floor at `wa = 3` would have
to come from the `5f + 1` counting argument, which the tree does not
carry. Everything downstream is already generic over the floor, SH-MM15d
running the same tail at a floor of one, so that one lemma would reach
the whole family. The arc runs one slot per round
(`∀ t, S.slotRound t = t` in SH-MM10i and SH-MM14a); the paper's introduction
keeps one leader slot per round while its model section now reads the
count as free, and the implementation's
`leader_count` admits two, with the agreed cursor a `(round, offset)`
pair, and 2 of its 9 fuzz configurations use it. And the
implementation's fuzz asserts that two views fire the failover the same
number of times (`stall_fallbacks`); `ScanState` does not record how a
period was reached, so SH-MM10a's `st₁ = st₂` says nothing about the count.

## 8. Witnesses (`LeanDagTest/Steelhead/`), SH12

The satisfiability witnesses sit in the directory itself; the DAGs on
which a claim fails sit in `Counterexamples/`, one file per claim:

| The claim that fails | File (`Counterexamples/`) | Declaration |
| :--- | :--- | :--- |
| the output progresses at a period `k ≥ ws` under the paper's own adversary (§4) | `Stall.lean` | `st20_stall` |
| Algorithm 3's selector leaves a stalled period (§7, finding 3) | `RotatingStall.lean`, `ReplayStartup.lean` | `rt_update_four`, `rs36_keeps_four` |
| every honest block is ordered within a fixed number of rounds at period `1` (§7, finding 5) | `CoinDelay.lean` | `positive_no_output` |
| a slot is decided once the first honest-led slot above its floor commits (§7, finding 7) | `ByzantineFloor.lean` | `bf30_slot0_undecided` |
| `I ≥ 2 · maxPeriod` makes a window hold a wave (§7, finding 8) | `ReplayShortWindow.lean` | `rw44_keeps_two` |
| each hop of the anchor search costs `b/n` under the coin (§7, finding 9) | `HopBound.lean` | `hb36_hop_bound_fails` |
| control slots read from the view give every validator the same anchor (issue #35, step 6; §7, finding 1) | `ControlSlotsFromView.lean` | `cv_anchors_differ` |
| the fairness count that bounds the anchor search survives a mixed period at `n = 3f + 1` (§6.1; §7, finding 12) | `PeriodicFairness.lean` | `tight_committee_periodic_fails` |

`Model.lean`: the wavelength arithmetic, the per-slot floors, the direct
rules at each slot's own wave, the anchor route for the asynchronous slot
through a synchronous one, the chain on data, the anchor-floor
counterexample (§3), and SH-MM17d's conclusion on data: the Byzantine
validator's round-`0` block, which leads no settled slot, is in the
ledger of the prefix slot `2` closes, since every round-`1` block
references it. `Period.lean`: the state derived over two
intervals at a concrete doubling update rule, which pins `intervalOf`'s
boundary convention, the window's first round at three anchors, the
history of a round-`7` block deciding slots `0` and `1`, so that an
advance from slot `1` over that anchor passes it and carries its
leader's round, the adaptive schedule naming the known leader at a
synchronous round and the coin at the asynchronous ones, and a block map
read back at the rounds of its blocks (§5). `Stall.lean`: the adversary's shape on valid
data, the asynchronous commit beside it, and the stalled slot by SH-MM8
(§4). `CoinDelay.lean`: the reliable-only DAG at every horizon, populated
and synchronised from round `0`, on which the coins naming the absent
validator through the horizon, a set of positive probability, leave
every settled prefix of every view empty (§7, finding 5).
`AdaptiveCoin.lean`: two one-round blocks whose second good set is the
adversary's answer to the first block's draw, satisfying SH-MM11h's
non-anticipation and size hypotheses on data and carrying its bound,
so that the adaptive claim is not the fixed family's in disguise.
`ByzantineFloor.lean`: seven rounds at wave `3` on which validator `0`
leads slots `0` and `3` and equivocates at both, so that each has two
votes each way and neither quorum; the honest-led slot `4` commits
directly and slot `0` stays undecided, its anchor search waiting on the
undecided floor (§7, finding 7); the two hops of the floor chain SH-MM6f
reads (`0` to `3` to `6`), every landing of which the Byzantine
validator leads, so that SH-MM6f's reliably led landing is the one thing
missing; and the round-robin schedule of SH-MM6g at `n = 4`, which leads
three consecutive rounds from a correct quorum past every round and
never four, so that the side condition `c · (n − |T|) < n` is tight at
the committee the implementation runs. `HopBound.lean`: nine rounds at
wave `3` on which validator `0`'s blocks of rounds `3`, `4` and `6` carry
two votes and two blames each, so that under the chain schedule of an
arbitrary coin the first two landings of the search from slot `0` are
both led by validator `0` under two disjoint coin patterns, rounds `3`
and `6` drawing `0`, or round `3` drawing `0`, round `6` an honest
validator whose commit skips slot `3`, and rounds `4` and `7` drawing
`0`; their union has probability `19/256` under the uniform coin of nine
rounds, above the `(b/n)^2 = 1/16` of two hops at `b/n` each
(`hb36_hop_bound_fails`; §7, finding 9). `Replay.lean`: Algorithm 3 on the
window of `sh8`'s round-`7` block, where period `1` scores `18` and
period `8` scores `11`, so the replay recovers from period `1` at
hysteresis `1/10` and stays there at `1/2`, and the selection's ties on
data (§5). `ReplayStartup.lean`: nine rounds with every synchronous slot
at two votes and two blames, whose first anchor's window holds one
asynchronous round and no synchronous commit, certificate or skip; every
candidate scores `6` and Algorithm 3 keeps period `4` at hysteresis `0`
and `1/10` (§7, findings 3 and 4). `ReplayShortWindow.lean`: eleven such
rounds at `I = 4`, `maxPeriod = 2`, where the window of the anchor at
round `7` holds two asynchronous rounds of period `2` and the decision
round of neither, while the window one anchor lower holds its own; both
candidates score `10` and
Algorithm 3 keeps period `2` at every hysteresis (§7, finding 8).
`RotatingStall.lean`: the family `rtDag N` at every horizon `N`, the
known leader rotating and every synchronous slot at two votes and two
blames, on which Algorithm 3 at interval `8`,
candidates `[1, 2, 4]`, a probe at every round and hysteresis `1/2`
answers period `4` at every anchor (`rt_update_four`, from
`anchorUpdate_half_retains`: periods `1`
and `2` score at least half of what period `4` can on a window of at
most nine rounds), at period `4` slot `3` is never decided in any view
for any coin, on the adaptive schedule of any period sequence that is
`4` on the intervals the record reaches (`rt_stall`, SH-MM8 with its
hypotheses asked below the horizon, which is where every slot a view
decides lies, `slotRound_le_of_decided`), no settled prefix has
more than three slots and no block above round `2` is ever in the ledger
(`rt_no_output_above_two`), while validator `1`'s honest round-`3` block
exists (§7, finding 3). `Failover.lean`: the same family with the coin
naming validator `2` at every round and the period bound `4`, on which
every control slot commits (`rt_control_decided`, from the DAG's
structure: everyone reaches that validator's block by two rounds up, so
the whole of round `r + 3` votes for it and the whole of round `r + 4`
certifies it), interval `0`'s anchor is its first control round at
period `4`, round `4`, and the warm-up keeps period `4` (SH-MM10m on data);
interval `1`'s anchor is round `12`, whose history commits nothing at
round `1` or above since slot `3` is undecided in the history of every
anchor up to round `17` (SH-MM8 asked at the slots such a history can
decide, `stall_of_pred`) and the synchronous slots below it never
commit, so the agreed output's last commit stays at `0` and the failover
hands interval `2` period `1` while the replay answers `4`
(`rt_failover`, SH-MM10e on data); and once interval `2` finds its anchor at
round `17`, its first control round at period `1`, and the coin names
committed candidates at rounds `25` to `29`, a view holding round `33`
decides slot `3` at the adaptive wavelength of the sequence `4, 4, 1, 1`
it derives (`rt_recovers`, SH-MM14a on data). `ControlSlotsFromView.lean`:
the model has no shares, so this file carries one as the block payload,
`true` where the author put a share for the coin two rounds below into
the block; five fully connected rounds on which the round-`4` blocks of
validators `1`, `2`, `3` omit validator `0`'s round-`3` block, and two
views of them, neither inside the other, the causal histories of the
round-`3` blocks of validators `0`, `1`, `2` and of the round-`4` blocks
of validators `1`, `2`, `3`. Read from the view, with a round a control
slot once the view holds a quorum of its shares, the first view counts
round `1` and the second round `2`, each commits the candidate of the
round it counts, and the scans anchor on rounds `1` and `2`
(`cv_control_differ`, `cv_anchors_differ`); under the rule at period
`1` both anchor interval `0` on round `1` (`cv_rule_anchor₁`,
`cv_rule_anchor₂`), issue #35's step 6 on data (§7, finding 1).
`Axioms.lean`: every `holds` of the arc, both pairs' included, the
carrier's persistence and its liveness headline depend on the standard
axioms only.

## 9. The mistimed leader timeout, SH-MM20

The paper carries an appendix on what the two partially synchronous
rules do when the leader timeout `T` is smaller than the link delay `D`.
With every link delayed past the timeout, the timer fires before any
block of the round arrives, so a validator proposes the instant its
threshold clock reaches `n − f` blocks, and every block then carries
**minimum-quorum references**: exactly `n − f` blocks of the previous
round, the earliest to arrive, never more. A certifier therefore holds
exactly `n − f` references, so a certificate forms only if all of them
are votes, which reading the arrival order as uniform makes
hypergeometric in the round's vote count. That is `certProb`.

This carries no DAG and no consensus. The reference pattern, the uniform
arrival order and the independence between validators' orders are the
appendix's assumptions about the network, not properties of the model;
the appendix states the last of them as its one optimistic step. Only
the arithmetic is here, which is why the claims sit apart from the rest
of the arc.

- **SH-MM20a, the certificate probability at the top of the vote round**
  (`certProb_self`, `certProb_pred`): a certificate forms with
  probability `1` when every block of the vote round voted, and `f / n`
  when exactly one did not. The second is the one that decides the
  appendix. `C(n − 1, q) / C(n, q) = (n − q) / n`, so at the threshold
  `q = n − f` the complement is the fault bound, `f / n`, and not
  `(n − f) / n`: at `n = 10`, `f = 3` it is `36 / 120 = 0.3`, not `0.7`.
  The appendix's own numbers depend on which: the `0.001` that the
  `v = n − 1` term contributes and the approximation `P₂ ≈ Pr[V = n]`
  that follows from it hold at `f / n` and fail at `(n − f) / n`.
- **SH-MM20b, the wait for the next direct commit** (`tsum_tail_eq_inv`):
  the appendix's `1 / P₂`. At a per-round direct-commit probability `p`,
  with the rounds independent, no commit falls in the first `m` rounds
  with probability `(1 − p)^m`, and the layer cake `∑ₘ P(T > m)` of
  those chances is `1 / p`. This is the series and not an expectation
  over a process the model carries: nothing here builds the rounds as
  random variables, so what is checked is that the layer cake of the
  appendix's own tail probabilities sums to its `1 / P₂`.

## 10. Layout

```
LeanDag/Steelhead/
  Model/Wavelength.lean     wavelength, periodicKind, periodic, IsAsync
  Model/Decision.lean       steelheadAnchored, Decided, FloorHop, floorLanding, floorChain
  Model/Chain.lean          chainSlots, ChainDecided, controlRound, firstControlRound,
                            controlSlots, ControlDecided
  Model/Period.lean         intervalOf, UpdateRule, windowBottom, IntervalAnchor, NoAnchor,
                            ScanState, AgreedAdvance, PeriodAt, adaptiveKind, adaptiveSlots
  Model/Coin.lean           commitProb, runProb, noCommitProb, noCommitProbOn, goodIntervals,
                            firstGoodInterval, goodBlocks, firstGoodBlock, blockRound,
                            coinOfBlocks, blockCoins, blocksHorizon, Matches, Settles,
                            Anchored, undecidedProb, NonAnticipating, undecidedProbAgainst,
                            coinOfRounds, coinOfBlocksFrom, coinMeasure
  Model/Reactive.lean       ReactiveS
  Model/Compose.lean        compose
  Model/Clauses.lean        CommitsUnderSync, SkipsSilent, LeastLinked, FloorHopOf, CommitLaws,
                            ViewLaws, GoodCommits, RunWithin, GoodFloor, RulePair.Lawful
  Model/RulePair.lean       RulePair, RulePair.rules, steelheadAt
  Model/Pair.lean           mahiMahiPair, blueBottlePair, blueBottlePairAnchored, mmPair, bbPair
  Model/Replay.lean         Evidence, Config, Config.blame, Timing, windowIds, ofAnchor,
                            committedCount, probeRate, timingAt, firstCommitAt, gateAt, score,
                            prefer, best, select, candidatesUpto, update, anchorUpdate;
                            BlueBottlePair.Replay.{omitters, supportBlocks, blameBlocks,
                            ofAnchor, anchorUpdate}
  Model/Timeout.lean        certProb
  Safety/Statement.lean     SH2–SH5a        Safety/Proof.lean
  Liveness/Statement.lean   SH6–SH9c        Liveness/Proof.lean
  Period/Statement.lean     SH10, SH14      Period/Proof.lean
  Coin/Statement.lean       SH11, SH15      Coin/Proof.lean
  Ledger/Statement.lean     SH13            Ledger/Proof.lean
  Interface/Statement.lean  SH16a, SH16b    Interface/Proof.lean
  Broadcast/Statement.lean  SH17            Broadcast/Proof.lean
  Replay/Statement.lean     SH18            Replay/Proof.lean
  MahiMahiPair/Statement.lean     SH-MM16c, SH-MM19
  MahiMahiPair/<Result>/Statement.lean
                            SH-MM1–SH-MM20, for Safety, Liveness, Period, Coin, Ledger,
                            Broadcast, Replay, Timeout; each with its Proof.lean
  BlueBottlePair/Statement.lean   SH-BB3, SH-BB16
  BlueBottlePair/<Result>/Statement.lean
                            SH-BB4–SH-BB18, for Safety, Liveness, Period, Coin, Ledger,
                            Broadcast, Replay; each with its Proof.lean
  Helpers/*.lean            the generic lemma layers
  Helpers/MahiMahiPair/*.lean, Helpers/BlueBottlePair/*.lean
                            each pair's lemma layers
  Properties.lean           the carrier, its properties and support
LeanDagTest/Steelhead/
  Model.lean  Period.lean  AdaptiveCoin.lean  Replay.lean  Failover.lean  Axioms.lean
  BlueBottlePair.lean
  Counterexamples/
    Stall.lean  CoinDelay.lean  ByzantineFloor.lean  HopBound.lean  ReplayStartup.lean
    ReplayShortWindow.lean  RotatingStall.lean  ControlSlotsFromView.lean
    PeriodicFairness.lean  SyncDissemination.lean
```

`scripts/check-arc-holes.py` enforces the partition: `Statement.lean`
files are proof-free, `Model/` files theorem-free (instances excepted),
and no synchrony name appears under `Properties/`.

## 11. The interface over a rule pair, and the `5f + 1` pair

The paper states Theorems 1 to 4 for any two rules meeting its
interface. The arc states them so as well: the generic statements sit
in the result directories under **SH**-labels, each pair's instances in
`MahiMahiPair/<Result>/` and `BlueBottlePair/<Result>/` under **SH-MM**
and **SH-BB**, numbered like the generic statement they instantiate
(`SH-MM6h` is SH6h at the `3f + 1` pair), and a result about one pair
alone keeps its number in its pair's series (`SH-MM6d`, `SH-BB10`). The
`3f + 1` pair's statements are the ones §1 to §9 describe, moved
verbatim, and each that has a generic counterpart is proved from it.

**The clauses** (`Model/Clauses.lean`, definitions only). A generic
statement reads a rule `R` only through `R.Laws` and these:

- `CommitsUnderSync R U`, clause A4 on the DAG: under synchrony from
  `R₀` and a reliable quorum populating every round up to
  `R.decisionRound k`, a reliably led slot at or above `R₀` is directly
  committed there. A single decision round rather than one per lower
  slot, so the clause passes from each rule of a family to the composite
  exactly, the composite's decision round being the slot's rule's;
- `SkipsSilent R U`: a slot whose leader has no block at its round is
  directly skipped once a quorum populates the rounds up to its decision
  round; Mahi-Mahi reads the blames at the vote round, Odontoceti one
  round up, Async BlueBottle two;
- `LeastLinked R`: the tie-break has a choice at every nonempty rung,
  which the handover and the descent need;
- `FloorHopOf R`: one hop of the chain of floors at the rule's own wave,
  which is `FloorHop` at `steelheadAnchored w`;
- `CommitLaws R` and `ViewLaws R`: a commit puts its candidate in the
  view and a link in the anchor's history, and a direct skip rests on a
  block at or above the slot's round; the control rule needs only the
  first, so SH-MM10h and SH-MM10i hold at every `wa`;
- `GoodCommits R good`: every validator in `good U r` has a round-`r`
  block the rule directly commits in every view holding its decision
  round;
- `RunWithin R good U c d N`: clause A5 in its run form, a run of `d`
  good leaders in every window of `c` slots below the horizon;
- `GoodFloor good Pop floor`: the counting lemma as the coin reads it,
  at least `floor` validators in `good U r` whenever the population
  hypothesis `Pop U T r` holds.

**A pair** (`Model/RulePair.lean`) is a synchronous and an asynchronous
rule that agree on the rung count and the tie-break;
`RulePair.rules p` reads the first at kind `0` and the second elsewhere,
and `steelheadAt p` is their composite. `RulePair.Lawful` bundles both
rules' laws, view laws and tie-break choices. Theorems 1 and 2, the
ledger and atomic broadcast take one lawful rule (SH2 to SH5a, SH6, SH13,
SH17); the chain and the stall read the asynchronous rule of a pair (SH7
to SH9); the period sequence takes its control verdicts from any rule
`Ra` and its agreed output from any rule `R` (SH10, SH14); the coin reads
a pair, a good set and a floor, its bounds §4's with `n − f − b`
replaced by the floor and the block bound `badBlockBoundAt floor K`
(SH11, SH15); the replay's selection, timings and probes read only a
window's evidence (SH18).

**The `3f + 1` pair** is `mmPair ws wa`, whose composite is the arc's
rule, `steelheadAt (mmPair ws wa) = steelheadAnchored (wavelength ws wa)`.
MM2 is its floor, `n − f − b` at `wa ≥ 5` on a quorum populating
`r + 3` and the decision round, and one at `wa ≥ 4` on `r + 2` and the
decision round; the pair is lawful at waves of two rounds or more.
SH-MM11b, SH-MM11k and SH-MM15d are the generic claims at a floor of
one, and SH-MM11e keeps its direct proof, the generic route needing
`1 ≤ wa` where the statement allows `wa = 0`. Two instances ask more
than the generic proof uses and keep their text: SH-MM7b asks `4 ≤ wa`
where three suffices, SH-MM10a `3 ≤ wa` where two does. The pair's own
results, with no generic counterpart:

- SH-MM1a to SH-MM1c and SH-MM5b, Mahi-Mahi's certificate lemmas and the
  direct verdicts' agreement with the chain: the laws consume their
  BlueBottle counterparts, O1 to O4 and ABB1 to ABB4, inside those arcs;
- SH-MM6d and SH-MM6k, partial dissemination and the reactive
  discipline, which read the rule's vote round (the `5f + 1` pair has its
  own, SH-BB6d and SH-BB6k);
- SH-MM16c and SH-MM19, the family and the periodic class;
- SH-MM18c, d, g, i, and the anchor forms SH-MM18h and SH-MM18n: the
  window's evidence, which reads Mahi-Mahi's certificates and blames (the
  `5f + 1` pair has its own reading, SH-BB18);
- SH-MM20, the timeout appendix, whose filter is the certificate layer.

**The `5f + 1` pair** is `bbPair`, Odontoceti at the synchronous kind and
Async BlueBottle elsewhere on one `n ≥ 5f + 1` committee; its composite
is `blueBottlePairAnchored` by definition. SH-BB16 is the pair itself:
both halves' laws (SH-BB16a), the family's rung and tie agreement
(SH-BB16d), agreement (SH-BB16b), and the two waves (SH-BB16e); SH-BB3
is the handover and SH-BB4 conservativity at `p = ∞` and `p = 1`.
Theorem 2 at the pair (SH-BB6) takes clause A4 from Odontoceti's O7 at
the synchronous kind and Async BlueBottle's ABB10a elsewhere (SH-BB6a),
the skip of a silent leader from blames one and two rounds up (SH-BB6c),
and the reactive discipline without a certificate wait (SH-BB6k); SH6
then gives the descent from a committed landing, the round count
`(b + 1) · (2 + (n − |T|))` when every slot is synchronous, where
`2 · (n − |T|) < n` holds for a bare reliable quorum, and
`(b + 1) · (2 + W) + 3` at a period. Partial dissemination does not
defer at the asynchronous kind (SH-BB6d); at the synchronous kind it
does, Odontoceti's vote round being the round above the candidate, and
`Counterexamples/SyncDissemination.lean` exhibits a DAG meeting every
hypothesis whose slot stays uncommitted. The chain at Async BlueBottle
(SH-BB7a to SH-BB7c, SH-BB9b) runs on ABB9c's run clause with runs of
three slots and on ABB10a under synchrony. SH-BB10 bundles the rule
hypotheses of the period statements, which both rules and their
composite meet: a commit reaches its candidate through blocks the view
holds and a link through `n − 3f` supporters or voters in the anchor's
cone, and a skip rests on blames one or two rounds up; the period is
then agreed (SH-BB10a), advances under ABB9c's clause (SH-BB10d), and
every slot far enough below the horizon is decided (SH-BB14b). SH-BB11
bundles the coin's hypotheses with ABB7 as the floor: on a reliable
quorum populating the two rounds above a round, at least `n − 3f`
validators' blocks of the round are directly committed, so the coin
names a committed leader with probability at least `(n − 3f) / n`
(SH-BB11a, one half on `full6`), the search at period one waits at most
`(n / (n − 3f))^3` blocks in expectation (SH-BB11j), and the output's
tail and almost sure decision are SH15's at that floor and blocks of
`3 · K` rounds (SH-BB15a, SH-BB15e). The ledger and atomic broadcast are
SH-BB13 and SH-BB17.

**The replay at the `5f + 1` pair, SH-BB18.** The paper reads Algorithm 3
and Lemma 3 through the support of its Lemmas 1 and 2: `n − f` supporters
at the decision round commit, `n − f` blames at the rule's blame round
skip, and the indirect threshold of supporters within the window stands
in for the anchor's certificate. `BlueBottlePair.Replay.ofAnchor` is that
reading at this pair, the decision-round votes themselves, Odontoceti's
references one round up at wave two and Async BlueBottle's cone votes two
rounds up at any other wave, with `n − 3f` of them the indirect
threshold; it is the implementation's `merged_certificates`, and where
the blame round lies, the decision round here and the vote round at the
`3f + 1` pair, is the replay's one parameter, `Config.merged`, read by
the skip's timing. What the window's reading gives is SH-MM18's at this
pair: a committed candidate is certified and a skipped one is not, a
skipped slot's candidate keeping at most `2f` supporters (SH-BB18c); Lemma
3's count on the window, `n − 3f` authors marked committed at wave three
once a correct quorum has populated the two rounds above within the
anchor's history, ABB7 read on the history as a record (SH-BB18d); a
window commit is a direct commit on the DAG under the wave's rule
(SH-BB18g); the selection keeps the range and answers a divisor of the
period bound (SH-BB18h, SH-BB18n); and the commit weight at wave three is
the coin's commit probability on the history as a record (SH-BB18i).
`LeanDagTest/Steelhead/BlueBottlePair.lean` runs the replay on a
five-round universe: the window commits every round-`1` and round-`2`
candidate at wave two and every round-`1` candidate at wave three, and
climbs from period `1` to period `4`. No timeout appendix is stated at
the pair: its filter is the certificate layer, which this pair lacks.
