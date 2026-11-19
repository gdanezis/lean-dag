# Synchroniser simulator for the sparse K-partial DAG

A discrete-event simulator of the honest case: every validator is correct and
none equivocates. It compares ways of repairing lost or late fragments.

```
python3 run.py [n]     # all sweeps, about 3 minutes at n = 100 on 10 cores
```

`run.py` writes `results.md` (tables) and `results.csv`. `sim.py` holds the
model; `simulate(**kw)` runs one setting, with the fields of `Config` as
keyword arguments. Pure Python, no dependencies.

## Model

**Network.**

- Validators sit at random points of a unit square. The one-way base latency
  of a link is 5–120 ms, by distance.
- Each packet adds an exponential jitter (mean 5 ms), which reorders packets.
- Each packet waits on its sender's 1 Gb/s uplink.
- Each packet is dropped with probability `loss`; a fraction `bad_links` of
  directed links drop with `bad_loss` instead.
- Every packet pays 80 B of IPv6, UDP and encryption framing.

**Blocks.**

- A block has a 150 B header, 44 B per reference and a lognormal payload with
  mean 10 KB.
- It is cut into fragments of F = 1380 B, each sent as one packet with a 19 B
  header.

**Consensus.** Rules R2–R4 of the paper, in the honest case, with one leader
per round in rotation:

- **Admission (R2):** a block is admitted once all its fragments are held, its
  references are admitted and a quorum of the round below is admitted.
- **Building (R3):** a validator at highest quorum round r builds at r + 1
  when it holds the leader block of r and votes from a quorum for the leader
  block of r − 1. It also builds after 1 s from the quorum, or at once when
  f + 1 others hold blocks of r + 1.
- **Shape (R4):** leader blocks are dense; the other blocks are sparse.
- **Commit:** a leader block commits directly once a quorum of round r + 2
  blocks claim it. A leader that does not commit directly is counted as
  decided at the next direct commit after it.

**Strategies.** All push every block, as fragments, to every peer.

- **pull τ.** When a validator notices a missing fragment (a fragment of the
  block arrived, or a reference names the block), it starts a timer τ. When
  the timer fires it asks the author of a block that references the missing
  block (or its own author) for the missing fragments, and retries every τ.
- **coded.**
  - A pull with a 500 ms timer stays as the fallback.
  - When a validator first holds a quorum of round r, it sends coded symbols.
    Each symbol is the XOR of a random half of the fragments it holds of
    rounds r − 1 and r. The validators to send to are chosen so that each
    receives `s` symbols per round from distinct senders.
  - Receivers decode by Gaussian elimination over GF(2), after removing the
    fragments they hold.
  - By default `s` is d_f at its 99.9th percentile plus 3, where d_f is the
    number of fragments lost over the two rounds, a Poisson variable.
- **relay.** As coded, with the same number of symbols, but each symbol is
  one random fragment, uncoded.

**What is simplified.**

- No crashes, no Byzantine behaviour, no equivocation.
- The receiver knows each block's fragment count (in the protocol it comes
  from the length in the reference).
- The fragments of one pushed block are delivered to a receiver together, at
  the arrival of the last fragment that is not lost.
- Admission reads references one round down, which in the honest case gives
  the windows.
- Computation (coding, elimination, signatures) takes no time.

## Findings (n = 100, three seeds; `results.md`)

Without loss, a block is admitted at another validator in 64 ms at the
median and 132 ms at the 99.9th percentile. A leader block is decided in
245 ms at the median.

1. **A pull with a long timer collapses under rare loss.** At p = 0.1% the
   median decision triples (245 → 821 ms) and so does the round time
   (85 → 273 ms). At p = 1% the median decision is 1.46 s. Admitting a
   dense leader block needs every block it references, about n·T fragments
   of the round below, so most rounds some validator lacks one fragment and
   waits for the timer.
2. **Coded symbols remove that cost.**

   | Loss | Median decision | Pulls | Extra bandwidth (of push bytes) |
   |---|---|---|---|
   | 0.1% | 248 ms | none | 1.3% |
   | 1% | 267 ms | none | 4.3% |
   | 5% | 574 ms (pull: 2.15 s) | few | 13% |

   At 0.1% and 1% loss, latency stays within a few percent of the loss-free
   run. With 5% of links at 20% loss, the median decision is 262 ms against
   1.35 s with pull.
3. **Coding is what helps.** An uncoded relay with the same number of
   symbols changes nothing: a random fragment is the missing one with
   probability about d/(n·T).
4. **A short pull timer (100 ms) recovers only part of the latency.** At
   p = 1% the median decision is 494 ms. Under reordering it duplicates
   fragments. At p = 5% it duplicates about 18 fragments per validator per
   round.
5. **The coding choices hold up:**
   - **Span:** covering two rounds beats covering one. At build time a
     sender does not yet hold the late blocks of the round below.
   - **Trigger:** sending on a quorum beats sending on build. Building waits
     on the leader block, so when the leader block is lost the repair waits
     with it. At 5% loss: 574 ms against 1.64 s.
   - **Density:** ½ is best.
   - **Budget:** s needs about d_f at its tail. Below about 20 symbols at
     p = 1%, the pulls return.
6. **The extra bandwidth falls as n grows** at p = 1%: 7.7% of push bytes at
   n = 25, 3.7% at n = 150. The symbol count s is about λ + 3√λ + 3, with
   λ = 2p·n·T. The push grows with n·T, so the share tends to 2p, which is
   2% at p = 1%.

**Limits.**

- Decision percentiles above the median vary between settings even without
  loss. Grace γ = 0 and the catch-up rule let fast validators move on
  without a slow leader's block, so the fraction of leaders committed
  directly changes from run to run.
- At p = 5%, a lost fragment of the leader block itself still costs about a
  round. With symbols sent on build, a second batch over the current round,
  sent 50 ms after building (`early = 0.05`), brings the median decision to 270 ms, at about
  twice the symbol bytes.
