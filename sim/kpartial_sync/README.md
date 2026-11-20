# Synchroniser simulator for the sparse K-partial DAG

A discrete-event simulator of the honest case: every validator is correct and
none equivocates. It compares ways of repairing lost or late fragments.

```
python3 run.py [n]     # all sweeps, about 12 minutes at n = 100 on 12 cores
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
  when it holds the leader block of r and votes from a quorum for the leader
  block of r − 1. It also builds after 1 s from the quorum, or at once when
  f + 1 others hold blocks of r + 1. The grace period is γ = 0.
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
    flight.
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

- No crashes, no Byzantine behaviour, no equivocation.
- Receivers know each block's fragment count; in the protocol it comes from
  the length in the reference.
- The responder of a pull sees the requester's holdings exactly, as the
  request's bitmap would report them.
- Computation (coding, elimination, signatures) takes no time.

## Findings (n = 100; `results.md`)

Three seeds, six for the ablation and the outages. Without loss, a block is
admitted at another validator in 64 ms at the median, and a leader block is
decided in 248 ms.

1. **A pull with a long timer collapses under rare loss.** A dense leader
   block references about n blocks. Admitting it needs every fragment of
   all of them, so in most rounds some validator lacks one fragment and
   waits for the timer.

   Median decision:

   | Loss | pull 500 ms | pull 100 ms | coded | extra bandwidth for coding |
   |---|---|---|---|---|
   | 0.1% | 815 ms | 352 ms | 252 ms | 1.1% |
   | 1% | 1.45 s | 604 ms | 272 ms | 3.3% |
   | 5% | 2.22 s | 854 ms | 324 ms | 11.7% |
   | 5% of links at 20%, 0.1% elsewhere | 1.98 s | 630 ms | 275 ms | 3.5% |

   Coded symbols keep the median within 80 ms of the loss-free run up to 5%
   loss, with almost no pulls.

2. **Ablation.** Each row changes one component of the default.

   | Variant | p = 1%: decide p50 / deliver p99 | p = 1%: extra | p = 5%: decide p50 / deliver p99 | p = 5%: extra | catch-up after 500 ms outage |
   |---|---|---|---|---|---|
   | default | 274 / 159 ms | 3.3% | 329 / 146 ms | 11.6% | 338 ms |
   | trigger on quorum | 275 / 147 ms | 3.8% | 545 / 409 ms | 15.0% | 305 ms |
   | trigger on build | 281 / 165 ms | 4.1% | 1489 / 685 ms | 17.6% | 376 ms |
   | no pull repair | 269 / 152 ms | 3.3% | 328 / 146 ms | 11.5% | 639 ms |
   | + tail (6, 3) | 275 / 152 ms | 3.7% | 331 / 148 ms | 12.0% | 330 ms |
   | span 1 | 1141 / 796 ms | 3.1% | 1754 / 1127 ms | 11.2% | 454 ms |
   | span 6 | 256 / 275 ms | 8.2% | 281 / 625 ms | 33.7% | 310 ms |
   | density ¼ | 304 / 328 ms | 3.4% | 333 / 213 ms | 11.6% | 331 ms |
   | relay, uncoded | 1416 / 946 ms | 4.5% | 2194 / 1314 ms | 17.1% | 932 ms |
   | previous default (quorum, no pull repair) | 274 / 147 ms | 3.8% | 539 / 292 ms | 14.5% | 740 ms |
   | pull 500 ms only | 1446 / 961 ms | 1.2% | 2270 / 1360 ms | 6.1% | 823 ms |

   - **Trigger.** A sender should send once it holds f + 1 complete blocks
     of the round. At p = 5% a 10 KB block of 8 fragments loses one with
     probability 1 − 0.95⁸ ≈ 34%, so reaching a quorum of complete blocks
     itself waits on repair: a quorum trigger waits for the repairs it would
     send. Fewer held blocks (1, or f/2) cover too little of the round, and
     pulls return. Building waits on the leader block, so the repair of a
     lost leader block waits with it.
   - **Pull repair.** After an outage a validator pulls its missing window.
     Without repair symbols, a lost fragment of the response waits for the
     500 ms retry. Pull repair costs nothing when no validator pulls.
   - **Tail.** Symbols over older rounds also repair the pull, but with pull
     repair they add nothing and cost 0.4 points of bandwidth.
   - **Span.** Two rounds beat one: a sender sends before it holds the late
     blocks of round r, and covers them one round later. Six rounds widen
     the delivery tail, since every symbol mixes the unknowns of six rounds,
     and cost two to three times the bandwidth.
   - **Coding.** An uncoded relay with the same number of symbols is no
     better than pull alone. A random fragment is the missing one with
     probability about d over the number of fragments.
3. **Budget.** At p = 1% the knee is about s = 20, and below about 10 the
   pulls return. The automatic budget (25) is enough.
4. **A short pull timer (100 ms) recovers about half the gap.** It doubles
   or triples the decision latency of coding, and under reordering it
   duplicates fragments.
5. **The extra bandwidth falls as n grows** at p = 1%: 6.7% of push bytes at
   n = 25, 2.8% at n = 150. The symbol count grows about as 2p·n·T plus a
   tail, and the push bytes as n·T.
6. **Large payloads.** At 100 KB, coding decides in 642 ms at the median
   (rounds of 217 ms) for 2.1% extra bandwidth; pull alone takes 2.1 s. A
   block of about 73 fragments loses one at p = 1% with probability about
   one half, so almost every round needs repair.
7. **Losses erode the sparse savings without coding.** A validator that
   lacks the leader block builds a dense block. With no payload, pull-only
   runs push 132 KB per validator per round, against 65 KB with coding.

**Limits.**

- **Small blocks are costly to protect.** With no payload, coding costs
  21.2% of push bytes: a symbol is a full fragment (1.4 KB), while sparse
  blocks are about 240 B. Coding each size class separately costs more, not
  less (22.8%), because every class needs its own margin of symbols. Nested
  classes with a 320 B cut send fewer symbol bytes (16.2%), but they protect
  the dense leader block less: more validators miss it and build dense
  blocks, push bytes rise from 65 KB to 79 KB per round, and the decision
  p99 rises from 394 ms to 619 ms.
- **The decision tails are noisy.** With γ = 0, the catch-up rule lets fast
  validators move on without a slow leader's block. The fraction of leaders
  committed directly therefore varies between runs, and decision
  percentiles above the median vary by several hundred ms between settings
  that behave alike in steady state; the ablation reports the delivery p99
  instead. Catch-up times vary by a factor of two between seeds.
