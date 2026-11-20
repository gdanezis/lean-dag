# Synchroniser simulator for the sparse K-partial DAG

A discrete-event simulator of the honest case: every validator is correct and
none equivocates. It compares ways of repairing lost or late fragments.

```
python3 run.py [n]     # all sweeps, about 20 minutes at n = 100 on 12 cores
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
- `outage = (v, t, d)` drops every packet sent to v during [t, t + d).
- `crash = (vs, t)`: the validators vs build and send nothing from time t.
- Every packet pays 80 B of IPv6, UDP and encryption framing.

**Blocks.**

- A block has a 150 B header and 44 B per reference (digest and length).
  - A sparse block has 2 references (about 240 B without payload).
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
  - **What:** every block of B's window that it lacks, in one request. The
    window is the blocks reached from B at most K + 1 = 7 rounds below. The
    request carries a bitmap of the slots the requester holds or has already
    asked for, so the author sends every block missing in the window at
    once.
  - **Timing:** the request goes out after τ, and is retried every τ. There
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

**What is simplified.**

- No Byzantine behaviour, no equivocation; crashed validators stop and stay
  down.
- Receivers know each block's fragment count; in the protocol it comes from
  the length in the reference.
- The responder of a pull sees the requester's holdings exactly, as the
  request's bitmap would report them.
- Computation (coding, elimination, signatures) takes no time.

## Findings (n = 100; `results.md`)

Three seeds, six for the ablation and the outages. Without loss, a block is
admitted at another validator in 64 ms at the median, a leader block is
decided in 241 ms (p99 282 ms), every block is built on its leader and votes,
and every leader commits directly.

1. **A pull with a long timer collapses under rare loss.** A dense leader
   block references about n blocks. Admitting it needs every fragment of
   all of them, so in most rounds some validator lacks one fragment and
   waits for the timer.

   Median decision:

   | Loss | pull 500 ms | pull 100 ms | coded | extra bandwidth for coding |
   |---|---|---|---|---|
   | 0.1% | 687 ms | 330 ms | 246 ms | 1.1% |
   | 1% | 1.12 s | 482 ms | 259 ms | 3.4% |
   | 5% | 1.99 s | 711 ms | 322 ms | 11.9% |
   | 5% of links at 20%, 0.1% elsewhere | 1.60 s | 533 ms | 262 ms | 3.7% |

   With coding, the decision p99 stays within 120 ms of the loss-free run
   up to 5% loss, with no pulls and no timeouts.

2. **Ablation.** Each row changes one component of the default.

   | Variant | p = 1%: decide p50 / p99 | p = 1%: extra | p = 5%: decide p50 / p99 | p = 5%: extra | catch-up after 500 ms outage |
   |---|---|---|---|---|---|
   | default | 263 / 309 ms | 3.4% | 327 / 368 ms | 11.9% | 300 ms |
   | no recent arrivals | 484 / 1165 ms | 4.2% | 335 / 1198 ms | 13.1% | 309 ms |
   | no recent arrivals, tail (6, 3) | 266 / 348 ms | 3.8% | 327 / 430 ms | 12.3% | 302 ms |
   | no idle batches | 263 / 309 ms | 3.4% | 327 / 850 ms | 11.8% | 329 ms |
   | no pull repair | 263 / 309 ms | 3.4% | 326 / 374 ms | 11.7% | 704 ms |
   | trigger on quorum | 268 / 324 ms | 3.9% | 496 / 632 ms | 16.0% | 316 ms |
   | trigger on build | 269 / 321 ms | 4.1% | 699 / 1241 ms | 16.2% | 337 ms |
   | span 1 | 268 / 338 ms | 3.1% | 362 / 622 ms | 9.2% | 332 ms |
   | span 6 | 255 / 752 ms | 8.3% | 281 / 883 ms | 33.8% | 319 ms |
   | density ¼ | 279 / 375 ms | 3.5% | 327 / 441 ms | 12.0% | 329 ms |
   | relay, uncoded | 1116 / 1566 ms | 5.1% | 1940 / 2480 ms | 19.1% | 806 ms |
   | quorum trigger, span 2 only | 281 / 872 ms | 3.9% | 516 / 862 ms | 14.5% | 686 ms |
   | pull 500 ms only | 1120 / 1556 ms | 1.2% | 1987 / 2644 ms | 6.1% | 716 ms |

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
3. **Budget.** At p = 1%, s = 20 is enough (269 / 324 ms), and at s = 10 the
   pulls return (532 / 1109 ms). The automatic budget (28) is enough.
4. **A short pull timer (100 ms) recovers about half the gap.** It doubles
   the decision latency of coding, and under reordering it duplicates
   fragments.
5. **The extra bandwidth falls as n grows** at p = 1%: 6.9% of push bytes at
   n = 25, 3.0% at n = 150. The symbol count grows about as 2p·n·T plus a
   tail, and the push bytes as n·T.
6. **Large payloads.** At 100 KB, coding decides in 642 ms at the median
   (rounds of 217 ms) for 2.1% extra bandwidth; pull alone takes 2.1 s. A
   block of about 73 fragments loses one at p = 1% with probability about
   one half, so almost every round needs repair.
7. **Crashes.** With a crashed validator, its leader slot costs the 1 s
   timeout. Waiting for votes on the leader of r − 1 only when one's own
   block references it removes the second timeout, a round later, for votes
   that cannot come:

   | | rounds, votes always awaited | rounds, awaited if referenced | blocks built on timeout |
   |---|---|---|---|
   | 1 crashed | 167 ms | 126 ms | 7.7% → 3.8% |
   | f crashed | 824 ms | 519 ms | 49% → 26% |

   With f crashed, the median decision falls from 1.59 s to 1.30 s; every
   correct validator is needed for a quorum, so each lost fragment stalls
   it until repaired.

**Limits.**

- **Small blocks are costly to protect.** With no payload, coding costs
  37% of push bytes (36 KB per validator per round): a symbol is a full
  fragment (1.4 KB), while sparse blocks are about 240 B. Coding each 256 B
  size class separately (27.5%) or nesting classes with a 320 B cut (28%)
  costs less here, but more once blocks carry a payload (26% and 12%
  against 11% at 1 KB), since every class needs its own margin of symbols.
- **Catch-up times vary** by up to a factor of two between seeds.
