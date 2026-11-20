# Synchroniser simulator for the sparse K-partial DAG

A discrete-event simulator of the honest case: every validator is correct and
none equivocates. It compares ways of repairing lost or late fragments.

```
python3 run.py [n]     # all sweeps, about 7 minutes at n = 100 on 12 cores
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
- **coded.**
  - A pull with τ = 500 ms stays as the fallback.
  - When a validator first holds a quorum of round r, it sends coded symbols
    over rounds r − 1 and r. Each symbol is the XOR of a random half of the
    fragments it holds of those rounds. Receivers are chosen so that each
    gets s symbols per round on average, from distinct senders when s < n.
  - Receivers decode by Gaussian elimination over GF(2), after removing the
    fragments they hold. One linear system holds the symbols of every sender
    over every block.
  - By default s is d at its 99.9th percentile plus 3, where d is Poisson
    with mean p times the fragments the sender holds over the span.
  - `size_class = 256` instead codes each 256 B class of fragment sizes
    separately, each class with its own budget.
  - `cuts = (L,)` nests the classes: a symbol of class L is L bytes long and
    covers every held fragment of at most L bytes; a full-length symbol
    covers every fragment.
  - `tail = (k, t)` also sends t symbols per receiver per round over the
    older rounds r − k + 1 … r − 2.
  - `pull_fec = m` adds, to each pull response, d at its 99.9th percentile
    plus m symbols over the fragments of the response, d Poisson with mean
    p times their number.
- **relay.** As coded, with the same number of symbols, but each symbol is one
  random fragment, uncoded.

**What is simplified.**

- No crashes, no Byzantine behaviour, no equivocation.
- Receivers know each block's fragment count; in the protocol it comes from
  the length in the reference.
- The responder of a pull sees the requester's holdings exactly, as the
  request's bitmap would report them.
- Computation (coding, elimination, signatures) takes no time.

## Findings (n = 100, three seeds; `results.md`)

Without loss, a block is admitted at another validator in 64 ms at the
median, and a leader block is decided in 248 ms.

1. **A pull with a long timer collapses under rare loss.** A dense leader
   block references about n blocks. Admitting it needs every fragment of
   all of them, so in most rounds some validator lacks one fragment and
   waits for the timer.

   Median decision:

   | Loss | pull 500 ms | pull 100 ms | coded | extra bandwidth for coding |
   |---|---|---|---|---|
   | 0.1% | 815 ms | 352 ms | 248 ms | 1.2% |
   | 1% | 1.45 s | 604 ms | 274 ms | 3.8% |
   | 5% | 2.22 s | 854 ms | 536 ms | 14.5% |
   | 5% of links at 20%, 0.1% elsewhere | 1.98 s | 630 ms | 266 ms | 4.1% |

   Coded symbols keep latency close to the loss-free run up to 1% loss, and
   with a few bad links, with no pulls.

2. **Coding is what helps.** An uncoded relay with the same number of
   symbols is no better than pull alone. A random fragment is the missing
   one with probability about d over the number of fragments.
3. **A short pull timer (100 ms) recovers about half the gap.** It doubles
   or triples the decision latency of coding, and under reordering it
   duplicates fragments.
4. **The coding choices hold up:**
   - **Span.** Covering two rounds beats covering one: when a sender first
     holds a quorum, it does not yet hold the late blocks of the round.
   - **Trigger.** Sending on a quorum beats sending on build at 5% loss
     (536 ms against 1.25 s). Building waits on the leader block, so the
     repair of a lost leader block waits with it.
   - **Density.** ½ is best; ¼ is close; ⅛ needs more symbols.
   - **Budget.** At p = 1% the knee is about s = 20, and below about 10 the
     pulls return. The automatic budget (29) is enough.
5. **The extra bandwidth falls as n grows** at p = 1%: 7.4% of push bytes at
   n = 25, 3.3% at n = 150. The symbol count grows about as 2p·n·T plus a
   tail, and the push bytes as n·T.
6. **Catch-up needs repair of the pull, not symbols over many rounds.**
   After an outage a validator pulls its missing window. A lost fragment of
   the response then waits for the 500 ms retry. Symbols over six rounds
   repair it, and so do two cheaper additions to span 2: three symbols per
   receiver per round over rounds r − 5 … r − 2 (tail), or repair symbols
   attached to the pull response.

   | | span 2 | span 6 | span 2 + tail | span 2 + pull repair | pull only |
   |---|---|---|---|---|---|
   | Catch-up after a 200 ms outage (mean) | 571 ms | 282 ms | 387 ms | 298 ms | 439 ms |
   | Catch-up after a 500 ms outage (mean) | 758 ms | 315 ms | 369 ms | 342 ms | 895 ms |
   | Extra bandwidth at p = 1% | 3.8% | 8.4% | 4.2% | 3.8% | — |
   | Decision p50 / p99 at p = 1% | 274 / 506 ms | 266 / 1369 ms | 271 / 460 ms | 273 / 506 ms | — |
   | Decision p50 / p99 at p = 5% | 536 / 887 ms | 422 / 1820 ms | 518 / 711 ms | 537 / 943 ms | — |

   Span 6 widens the steady-state tail, since every symbol mixes the
   unknowns of six rounds. The tail keeps span 2's steady state, and at
   p = 5% improves its tail. Pull repair costs nothing when no validator
   pulls. The catch-up times vary by a factor of two between seeds.
7. **Losses erode the sparse savings without coding.** A validator that
   lacks the leader block builds a dense block. With no payload, pull-only
   runs push 132 KB per validator per round, against 68 KB with coding.

**Limits.**

- **Small blocks are costly to protect.** With no payload, coding costs
  22.5% of push bytes: a symbol is a full fragment (1.4 KB), while sparse
  blocks are about 240 B. Coding each size class separately costs more, not
  less (26.8%), because every class needs its own margin of symbols. Nested
  classes with a 320 B cut send fewer symbol bytes (16.0%), but they protect
  the dense leader block less: more validators miss it and build dense
  blocks, push bytes rise from 68 KB to 88 KB per round, and the decision
  p99 rises from 368 ms to 680 ms.
- **Large payloads are limited by bandwidth.** At 100 KB, a validator pushes
  about 10 MB per round on a 1 Gb/s uplink. Both strategies decide in about
  2.1 s; the uplink, not the synchroniser, sets the pace.
- **The decision tails are noisy.** With γ = 0, the catch-up rule lets fast
  validators move on without a slow leader's block. The fraction of leaders
  committed directly therefore varies between runs, and decision percentiles
  above the median vary between settings even without loss.
