# Synchroniser simulator for the sparse K-partial DAG

A discrete-event simulator of the honest case: every validator is correct and
none equivocates. It compares ways of repairing lost or late fragments.

```
python3 run.py [n]     # all sweeps, about 16 minutes at n = 100 on 14 cores
```

`run.py` writes `results.md` (tables) and `results.csv`. `sim.py` holds the
model; `simulate(**kw)` runs one setting, with the fields of `Config` as
keyword arguments. Pure Python, no dependencies. For profiling and debugging,
use small settings (n = 20–30, a few rounds) that run in seconds.

## Model

**Network.**

- Validators sit at random points of a unit square. The one-way base latency
  of a link is 5–120 ms, by distance.
- Each packet adds an exponential jitter (mean 5 ms), which reorders packets.
- Each packet waits on its sender's 1 Gb/s uplink.
- Each packet is dropped with probability `loss`; a fraction `bad_links` of
  directed links drop with `bad_loss` instead.
- `loss_steps = ((t, p), ...)` sets the loss of every link that is not bad
  to p at time t.
- `lossy_in = (x, p)` / `lossy_out = (x, p)`: every link into / out of a
  fraction x of the validators drops with p.
- `jitter_steps = ((t, j), ...)` sets the mean jitter to j at time t.
- `outage = (v, t, d)` drops every packet sent to v during [t, t + d).
- `crash = (vs, t)`: the validators vs build and send nothing from time t.
- Every packet pays 80 B of IPv6, UDP and encryption framing.

**Blocks.**

- A block has a 150 B header and 44 B per reference (digest and length).
  - A sparse block has 2 references (about 240 B without payload, 350 B with
    the window bitmap).
  - A dense block references a block of every author it holds one round below
    (about 4.5 KB at n = 100).
- Every block carries a lognormal payload, mean `payload` (10 KB by default).
- A block is cut into fragments of F = 1380 B. Each fragment is one packet
  with a 19 B header.
- The fragments of one block sent to one peer leave back to back on the
  sender's uplink. Those not lost arrive together, at the last arrival.

**Consensus.** Rules R2–R4 of the paper, in the honest case, with one leader
per round in rotation.

- **Admission (R2).** A block is admitted once:
  - all its fragments are held;
  - its references are admitted;
  - a quorum of the round below is admitted;
  - for each leader block it claims, that block and votes for it from a
    quorum are admitted.
- **Building (R3).** A validator at highest quorum round r builds at r + 1
  when it holds the leader block of r and, if its own block at r references
  the leader block of r − 1, votes from a quorum for that block. A validator
  whose block at r does not reference the leader of r − 1 builds on the
  quorum at r and the leader of r (`vote_wait = "always"` restores the wait).
  It also builds once 1 s has passed since it reached quorum round r, while
  still at r, or at once when f + 1 others hold blocks of r + 1. The rule is
  checked after each admission, so a validator skips only rounds it could
  not have built. The grace period is γ = 0.
- **Shape (R4).** A leader's block, or a validator's first block after a gap,
  or a block built without the leader block, is dense. Every other block is
  sparse.
- **Commit.** A leader block commits directly once a quorum of round r + 2
  blocks claim it. A leader that does not commit directly is counted as
  decided at the next direct commit after it.

**Strategies.** All push every block, as fragments, to every peer.

- **pull τ.**
  - **When:** a validator holds a block B whose references it lacks, or holds
    part of a block B.
  - **Whom:** it asks B's author, who held B's window when building B.
  - **What** (`pull_mode`). The window of B is the blocks reached from B at
    most K + 1 = 7 rounds below. With no equivocation, a slot (author,
    round) names at most one block.
    - `bitmap` (default): every block carries a bitmap of the slots of its
      window, n(K + 2) bits (112 B at n = 100). Once B is held, the
      requester asks for every block of the window it lacks, in one request.
    - `refs`: the requester asks for the references of B that it lacks.
      Deeper gaps appear only as those blocks arrive, and are pulled at once,
      one round trip per level.
    - `oracle`: as `bitmap`, but the window is read from the global DAG and
      blocks carry no bitmap; a bound, not a protocol.

    A request names each block by its slot (4 B, or a slot bitmap if
    shorter) and, for each block held in part, carries a bitmap of the
    fragments held. The responder sends what the request reports missing;
    blocks that arrived meanwhile come twice, and count as duplicates.
    While a request is outstanding, its blocks are not asked for again.
  - **Timing:** the request goes out after τ, and is retried every τ; after
    three requests in a row with no packet from the author, the interval
    doubles each time, up to 2 s (the author may be down). A pull stops once
    every leader whose output can hold its block is decided (the block is
    more than D = 8 rounds below the lowest undecided leader), and a crashed
    validator stops pulling. The quorum round is no bound: a leader's output
    is its available sub-DAG to depth D, which reaches below the window of
    any block the validator builds on (`Avail`, `Out` and `Fetches` in the
    Lean model). There
    is no wait when the validator is behind: it holds blocks from f + 1
    authors two rounds above its quorum round, so nothing it lacks is in
    flight. Requests waiting for τ go out at once when the validator finds
    it is behind.
- **coded** (the default configuration).
  - A pull with τ = 500 ms stays as the fallback.
  - When a validator first holds complete blocks of round r from f + 1 other
    authors, it sends coded symbols over rounds r − 1 and r. Each symbol is
    the XOR of a random half of the fragments it holds of those rounds.
    Receivers are chosen so that each gets s symbols per round on average,
    from distinct senders when s < n.
  - Receivers decode by Gaussian elimination over GF(2), after removing the
    fragments they hold. One linear system holds the symbols of every sender
    over every block.
  - The symbols also cover the blocks of older rounds that the sender
    completed in the last 100 ms (`recent`): a late block of an old round,
    from a validator that fell behind, is covered while it is new.
  - A validator that has sent no symbols for 150 ms sends a batch over its
    quorum round and the round above, and its recent arrivals (`idle`); the
    interval doubles after each idle batch. This covers a late leader block
    when fewer than f + 1 validators can build the next round, so no round
    reaches the trigger.
  - s is d at its 99.9th percentile plus 3, where d is Poisson with mean p
    times the fragments the sender holds over the span.
  - A pull response carries repair symbols: d at its 99.9th percentile plus
    3, over the fragments of the response, d Poisson with mean p times their
    number.
  - Options, off by default:
    - `trigger = "quorum"` sends on a quorum of admitted blocks of round r;
      `trigger = "build"` sends on building, over the rounds below.
    - `tail = (k, t)` also sends t symbols per receiver per round over the
      older rounds r − k + 1 … r − 2.
    - `size_class = 256` codes each 256 B class of fragment sizes separately,
      each class with its own budget.
    - `cuts = (L,)` nests the classes: a symbol of class L is L bytes long
      and covers every held fragment of at most L bytes; a full-length symbol
      covers every fragment.
- **relay.** As coded, with the same number of symbols, but each symbol is one
  random fragment, uncoded.
- **Adaptive control** (`adapt = True`, off by default). The budgets above
  use the true loss rate p, which a validator cannot know. With `adapt`, each
  validator measures what it needs instead:
  - **Loss.** It counts the fragments missing from each delivery of a block
    (every fragment header carries the block's fragment count). A push lost
    whole shows no fragment; each block references its author's previous
    block, so when no fragment of that block has arrived one round time
    later, all its fragments count as lost. It keeps two decayed estimates,
    with time constants 0.1 s and 2 s, each with a Beta prior of weight 20 at
    1%. It uses the slow one, unless the fast one exceeds it by more than two
    standard errors of the fast one (`est_gate`): taking the larger of the
    two would bias the estimate upwards, as the fast one is noisy.
  - **Report.** It puts its estimate p̂ and its margin m in each block,
    symbol and pull request it sends (2 B), and keeps the newest report of
    each peer.
  - **Budget per receiver.** A sender sizes the symbols for receiver w from
    w's newest report, with its own estimate as a floor on p̂ (`own_floor`): w needs (d + m) / (1 − p̂) symbols in all, where d is
    the 99.9th percentile of a Poisson variable with mean p̂ times the
    fragments covered. Each of the n − 1 senders sends its share, rounded so
    that w receives the total. Repair symbols on pull responses use the
    requester's p̂ the same way. Budgets plan for at most 25% loss
    (`loss_cap`): a validator in an outage counts every push as lost, but
    more symbols do not repair an outage.
  - **Margin.** A partial block that symbols have not repaired by its repair
    deadline is a miss. When symbols covering its missing fragments did
    arrive, too few to decode, the margin doubles at the next quorum round;
    otherwise it falls by 0.05 per round, between 1 and 30. A miss with no
    covering symbol is a matter of timing, which more symbols do not fix.
  - **Timers.** The repair deadline, after which a partial block is pulled,
    is twice the measured round time, between 50 ms and 500 ms. A pull is
    retried after twice the measured delay of the author's blocks plus four
    deviations, at most 500 ms. The `recent` window is one round time, and
    the idle interval is between 30 ms and 250 ms, so that late arrivals
    are covered before the longest repair deadline when rounds are slow.

**What is simplified.**

- No Byzantine behaviour, no equivocation; crashed validators stop and stay
  down.
- Receivers know each block's fragment count; in the protocol it comes from
  the length in the reference.
- Computation (coding, elimination, signatures) takes no time.
- Without `adapt`, every validator knows the true loss rate, and uses it
  for every link.
- A leader counts as decided when its decision rule is met; the simulator
  does not model output, so a decision does not wait for the validator to
  fetch the leader's available sub-DAG.

## Findings (n = 100; `results.md`)

Three seeds, six for the ablation, the pull modes and the outages. Without
loss, a block is admitted at another validator in 64 ms at the median, a
leader block is decided in 241 ms (p99 285 ms), every block is built on its
leader and votes, and every leader commits directly.

1. **A pull with a long timer collapses under rare loss.** A dense leader
   block references about n blocks. Admitting it needs every fragment of
   all of them, so in most rounds some validator lacks one fragment and
   waits for the timer.

   Median decision:

   | Loss | pull 500 ms | pull 100 ms | coded | extra bandwidth for coding |
   |---|---|---|---|---|
   | 0.1% | 682 ms | 326 ms | 247 ms | 1.1% |
   | 1% | 1.14 s | 505 ms | 258 ms | 3.4% |
   | 5% | 1.99 s | 697 ms | 322 ms | 12.0% |
   | 5% of links at 20%, 0.1% elsewhere | 1.66 s | 542 ms | 262 ms | 3.6% |

   With coding, the decision p99 stays within 80 ms of the loss-free run up
   to 5% loss, with no pulls and no timeouts.

2. **Ablation.** Each row changes one component of the default.

   | Variant | p = 1%: decide p50 / p99 | p = 1%: extra | p = 5%: decide p50 / p99 | p = 5%: extra | catch-up after 500 ms outage |
   |---|---|---|---|---|---|
   | default | 263 / 326 ms | 3.4% | 327 / 372 ms | 12.0% | 329 ms |
   | no recent arrivals | 421 / 992 ms | 4.4% | 327 / 374 ms | 11.9% | 372 ms |
   | no recent arrivals, tail (6, 3) | 263 / 327 ms | 3.7% | 329 / 373 ms | 12.3% | 298 ms |
   | no idle batches | 264 / 331 ms | 3.4% | 327 / 464 ms | 11.8% | 327 ms |
   | no pull repair | 263 / 326 ms | 3.4% | 329 / 467 ms | 11.8% | 708 ms |
   | trigger on quorum | 267 / 323 ms | 3.9% | 512 / 652 ms | 16.1% | 326 ms |
   | trigger on build | 269 / 321 ms | 4.1% | 779 / 1327 ms | 17.9% | 377 ms |
   | span 1 | 271 / 367 ms | 3.0% | 363 / 552 ms | 9.2% | 310 ms |
   | span 6 | 254 / 740 ms | 8.3% | 281 / 1114 ms | 33.8% | 296 ms |
   | density ¼ | 279 / 411 ms | 3.5% | 329 / 456 ms | 12.1% | 390 ms |
   | relay, uncoded | 1103 / 1568 ms | 5.0% | 1937 / 2491 ms | 18.9% | 917 ms |
   | quorum trigger, span 2 only | 273 / 915 ms | 3.9% | 516 / 741 ms | 14.5% | 678 ms |
   | pull 500 ms only | 1133 / 1556 ms | 1.1% | 1992 / 2614 ms | 5.8% | 757 ms |

   - **Recent arrivals.** A validator that falls behind builds late blocks
     of old rounds. A dense leader block that references one stalls every
     validator that lost a fragment of it, and through the leader every
     validator, until the 500 ms pull. Symbols over rounds r − 1 and r do
     not cover such a block; symbols over the blocks received in the last
     100 ms do. Symbols over older rounds (tail) also work, at a little
     more bandwidth.
   - **Idle batches.** A late leader block that misses the symbols of its
     round, and that fewer than f + 1 validators receive whole, is never
     covered: only those validators build the next round, so no round
     reaches the trigger. An idle batch covers it.
   - **Trigger.** A sender should send once it holds f + 1 complete blocks
     of the round. At p = 5% a 10 KB block of 8 fragments loses one with
     probability 1 − 0.95⁸ ≈ 34%, so reaching a quorum of complete blocks
     itself waits on repair: a quorum trigger waits for the repairs it would
     send. Building waits on the leader block, so the repair of a lost
     leader block waits with it.
   - **Pull repair.** After an outage a validator pulls its missing window.
     Without repair symbols, a lost fragment of the response waits for the
     500 ms retry. Pull repair costs nothing when no validator pulls.
   - **Span.** Two rounds beat one at p = 5%: a sender sends before it holds
     the late blocks of round r, and covers them one round later. Six
     rounds widen the delivery tail, since every symbol mixes the unknowns
     of six rounds, and cost two to three times the bandwidth.
   - **Coding.** An uncoded relay with the same number of symbols is no
     better than pull alone. A random fragment is the missing one with
     probability about d over the number of fragments.
3. **Pull modes.** In steady state with coding, almost nothing is pulled,
   and the three modes decide alike (263 ms at p = 1%). They differ when a
   validator must fetch history:

   | | oracle | refs | bitmap |
   |---|---|---|---|
   | Catch-up after 200 ms outage, coded | 311 ms | 649 ms | 463 ms |
   | Catch-up after 500 ms outage, coded | 300 ms | 912 ms | 329 ms |
   | Catch-up after 500 ms outage, pull only | 716 ms | 1019 ms | 757 ms |
   | Push per validator per round, no payload | 36 KB | 36 KB | 46 KB |

   With `refs`, a sparse block names only its author's previous block and
   the leader, so each author's missing blocks form a chain that the
   requester discovers one round trip per round; after a 500 ms outage
   that is about a dozen round trips. The bitmap gives the whole window
   from one block, and comes within 30 ms of the oracle after a 500 ms
   outage. It costs 112 B per block: 1% of a 10 KB block, and 28% of push
   bytes with no payload.
4. **Budget.** At p = 1%, s = 20 is enough (270 / 343 ms), and at s = 10 the
   pulls return (558 / 1157 ms). The automatic budget (28) is enough.
5. **A short pull timer (100 ms) recovers about half the gap.** It doubles
   the decision latency of coding, and duplicates fragments (4.2 per
   validator per round at p = 1%, 20 at p = 5%).
6. **The extra bandwidth falls as n grows** at p = 1%: 6.9% of push bytes at
   n = 25, 2.9% at n = 150. The symbol count grows about as 2p·n·T plus a
   tail, and the push bytes as n·T.
7. **Large payloads.** At 100 KB, coding decides in 652 ms at the median
   (rounds of 230 ms) for 2.2% extra bandwidth; pull alone takes 2.1 s. A
   block of about 73 fragments loses one at p = 1% with probability about
   one half, so almost every round needs repair.
8. **Crashes.** With a crashed validator, its leader slot costs the 1 s
   timeout. Waiting for votes on the leader of r − 1 only when one's own
   block references it removes the second timeout, a round later, for votes
   that cannot come:

   | | rounds, votes always awaited | rounds, awaited if referenced | blocks built on timeout |
   |---|---|---|---|
   | 1 crashed | 172 ms | 126 ms | 7.7% → 3.8% |
   | f crashed | 800 ms | 507 ms | 46% → 24% |

   With f crashed, the median decision falls from 1.59 s to 1.23 s; every
   correct validator is needed for a quorum, so each lost fragment stalls
   it until repaired.

**Adaptive control** (`python3 adapt_eval.py`, about 12 minutes on 14 cores;
`adapt_results.md`). Each scenario runs with three budgets: fixed at the
scenario's loss averaged over links and time (a well-informed operator),
fixed at 1%, and adaptive. Decision p99 in ms with a 95% bootstrap interval,
and repair bytes as a share of push bytes; n = 100 unless stated, 8 seeds.
The interval resamples leader rounds, not single decisions: the decisions of
one leader at every validator move together, so a run of 30 rounds gives
about 26 independent samples, and each seed's p99 rests on its worst one or
two leaders. With 3 seeds, p99 differences under about 50 ms were noise.

| scenario | fixed, mean loss | fixed, 1% | adaptive |
|---|---|---|---|
| p = 0.1% | 293 [287–301] (1.1%) | 282 [278–286] (3.3%) | 294 [286–304] (1.2%) |
| p = 1% | 321 [303–335] (3.4%) | 321 [303–335] (3.4%) | 353 [330–368] (3.6%) |
| p = 2% | 362 [333–371] (5.5%) | 471 [426–796] (3.8%) | 334 [316–353] (5.8%) |
| p = 5% | 370 [366–375] (12.0%) | 1760 [1563–1816] (14.0%) | 363 [357–369] (13.3%) |
| step up: 0.1% → 5% (1.5–3 s) → 0.1% | 836 [799–862] (4.9%) | 1026 [959–1098] (4.1%) | 421 [402–432] (5.9%) |
| step down: 5% → 0.1% at 1.5 s | 609 [563–645] (5.1%) | 672 [305–763] (4.2%) | 347 [339–359] (7.2%) |
| ramp: 0.1% → 5% over 1–2.5 s | 680 [601–754] (8.1%) | 1486 [1446–1551] (8.4%) | 367 [361–374] (7.3%) |
| bursts: 5% for 0.2 s each second, else 0.1% | 583 [572–590] (3.8%) | 523 [508–534] (4.0%) | 400 [390–424] (5.1%) |
| 5% of links at 20%, p = 0.1% | 329 [310–339] (3.6%) | 354 [313–364] (3.5%) | 309 [297–348] (4.2%) |
| 10% of validators receive at 10%, p = 0.1% | 497 [473–523] (6.6%) | 496 [472–522] (6.4%) | 302 [298–307] (5.6%) |
| 10% of validators send at 10%, p = 0.1% | 363 [329–372] (3.6%) | 376 [350–385] (3.4%) | 359 [325–369] (3.8%) |
| jitter 30 ms, p = 0.1% | 616 [593–761] (1.1%) | 577 [544–640] (3.4%) | 586 [572–595] (1.5%) |
| jitter 5 → 30 ms (1.5–3 s) → 5 ms, p = 0.1% | 573 [538–598] (1.2%) | 540 [519–555] (3.5%) | 541 [530–548] (1.4%) |
| routing stretch σ = 0.4, p = 1% | 497 [467–517] (3.5%) | 497 [467–517] (3.5%) | 460 [446–468] (4.3%) |
| outage 500 ms, p = 0.1% | 306 [296–313] (1.2%) | 290 [285–301] (3.5%) | 316 [299–385] (1.4%) |
| f crashed at 0.5 s, p = 1% | 3962 [3830–3999] (5.5%) | 3962 [3833–3994] (5.5%) | 2158 [2124–2171] (8.9%) |
| n = 50, p = 1% | 313 [302–329] (4.6%) | 313 [301–327] (4.6%) | 320 [304–331] (4.8%) |
| n = 150, p = 1% | 347 [321–360] (2.9%) | 347 [321–360] (2.9%) | 349 [324–359] (3.1%) |
| no payload, p = 1% | 269 [255–297] (29.3%) | 269 [255–297] (29.3%) | 273 [256–450] (27.6%) |
| payload 100 KB, p = 1% | 912 [797–958] (2.2%) | 912 [797–958] (2.2%) | 722 [714–728] (2.3%) |
| p = 1%, jitter 20 ms, stretch 0.3, 5% of links at 20% | 648 [612–675] (5.5%) | 1319 [1166–1550] (4.4%) | 633 [601–647] (7.4%) |

- **Steady loss: a tie.** The intervals of the adaptive and the mean-loss
  budget overlap at every rate (at 1% only just: 353 [330–368] against
  321 [303–335]; an earlier 3-seed run had the order reversed). The adaptive
  validator spends 0.1–1.3 points more bytes, and its estimates are exact
  (0.0010, 0.0100, 0.0200, 0.0500). A budget that assumes too little loss
  collapses: at 5%, the 1% budget stretches rounds from 111 ms to 427 ms.
- **Changing loss: a clear win.** No fixed budget fits a schedule. The
  adaptive validator cuts the p99 by a third (bursts) to about a half
  (steps, ramp), with intervals far apart, for at most 2.1 more points of bytes.
- **Uneven loss.** When a tenth of the validators receive at 10%, their
  reports raise only their own budgets: p99 302 ms against 497 ms, for fewer
  bytes. When a tenth send at 10%, all three budgets tie: every symbol mixes
  the fragments of all blocks of its rounds, so a receiver needs as many
  symbols as it lost fragments, whichever authors they came from.
- **Timing.** The margin rises after late blocks miss their repair deadline
  (to about 3 under 30 ms jitter, 6 under routing stretch); the adaptive
  validator matches a fixed 1% budget under jitter at less than half its
  bytes, and is slightly ahead under routing stretch (460 [446–468] against
  497 [467–517] ms, intervals just touching).
- **Crashes.** With f crashed, rounds wait for the 1 s timeout, and blocks
  that arrive after their round's symbols waited about 1.5 s for the next
  batch. The cap on the idle interval covers them within 250 ms: p99 2.2 s
  against 4.0 s, median 1.4 s against 2.8 s, for 3.4 more points of bytes.
- **Large payloads.** At 100 KB the p99 falls from 912 ms to 722 ms.
- **Reports alone are not enough.** Without the floor of the sender's own
  estimate, a step up in loss stalls rounds, few blocks or symbols carry the
  new reports, and senders keep sizing for the old loss (p99 623 ms against
  400 ms with the floor, 3 seeds).

**Limits.**

- **Small blocks are costly to protect.** With no payload, coding costs
  29% of push bytes (46 KB per validator per round, with bitmaps): a symbol
  is a full fragment (1.4 KB), while sparse blocks are about 350 B. Coding
  each 256 B size class separately costs 25%, but more once blocks carry a
  payload (25% against 10% at 1 KB), since every class needs its own
  margin of symbols.
- **Catch-up times vary** by up to a factor of two between seeds.
