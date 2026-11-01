# Certified joins of twins

This note records a simulation of one rule, `scripts/sync-auth.py`. Under
the rule, a block that brings twins together in its history carries a
certificate signed by a quorum. The question is whether the rule stops
Byzantine nodes from building large structures of twins without the honest
nodes knowing. The network, the honest rules `react` and `min`, and the
attacks are those of `docs/sync.md` §8. There `n = 10`, `f = 3`, the system
is synchronous from the start (`Δ = 3`), and there is no horizon.

## 1. The rule

A block `b` *joins* a twin pair `{x, x′}` when both are in its history and
in the history of no single reference of `b`. A block that joins pairs is
valid only with a certificate. The certificate holds the round of `b` and a
set `E` of pairs that contains every pair `b` joins. It is signed by at
least `q = n − f` nodes, and it is evidence against the authors of `E`.

An honest node prefers references that join nothing. When it must join, it
sends `(r, E)` to every node, and it builds once `q` nodes have signed.

A node that receives `(r, E)` learns `E` and convicts its authors. It
refuses to sign, and sends the block back, when it holds a block of round
`r` whose history contains no pair of `E`. This is the rule `clean`.
Byzantine nodes refuse every honest request. They request only when they
would succeed, and their request reaches every node.

## 2. Results

Each cell gives the rounds reached, the blocks of Byzantine authors in
honest histories (all / largest in one round), the least share, the most
failed requests of one node, and the largest `E`. The checks are evidence
only, twins as well, or certificates under `clean`. The rule is `react`.

| Attack | Evidence | Twins | Certificates |
|---|---|---|---|
| No attack | 54, 3 / 3 | 54, 3 / 3 | 54, 3 / 3, 0, 0 |
| `edge` | 53, 46 / 3 | 55, 32 / 3 | 55, 32 / 3, 0, 78 |
| `split` | 55, 18 / 14 | 54, 18 / 14 | 53, 18 / 14, 0, 42 |
| `isolate` | 55, 24 / 21 | 55, 24 / 21 | 53, 24 / 21, 0, 63 |
| `inject`, `d = 8` | 147, 686 / 257 | 79, 44 / 3 | 78, 44 / 3, 0, 1 |
| `nest`, `depth = 13` | 52, 619 / 49 | 52, 619 / 49 | 52, 224 / 17, 0, 512 |
| `nest`, `depth = 39` | 43, 1893 / 49 | 43, 1893 / 49 | 50, 744 / 19, 0, 1842 |
| `bulk`, `depth = 39` | 54, 156 / 4 | 54, 156 / 4 | 54, 156 / 4, 0, 38 |
| `force` | 53, 70 / 4 | 53, 70 / 4 | 53, 70 / 4, 0, 1 |

Under `min` with certificates, `nest` admits 26 / 2 at `depth = 13` and
78 / 2 at `depth = 39`, against 303 / 24 and 387 / 10 with twin checks.
The other rows are as under twin checks. Every share is at least 0.79, and
no request fails, under any attack.

## 3. Findings

* **No join is silent.** Every pair of twins in a valid history is in
  the set `E` of a certificate of the round of the block that joins it.
  Every node received `E` before that block existed.
* **Joins are not back-dated.** Signers hold their own blocks of past
  rounds, and those blocks contain no pair of the request. So no
  certificate is granted for a join below the rounds the honest nodes
  have built. `inject` fails as under twin checks, and so does every
  level of the doubling family of `nest` that joins twins inside the
  family.
* **The mass is not bounded.** What remains of `nest` is twin-free
  chains, dated back, which each honest node adopts on its own.
  The honest nodes then join them in public, at the current round, under
  certificates that name up to 1842 pairs. `bulk` is one Byzantine
  certificate for a join at the current round, of 38 pairs. The rule
  makes the mass known; it does not price it.
* **A cap on `E` breaks liveness.** When signers refuse an `E` of more
  than `2n` pairs, `split`, `filler` and `isolate` stall the system at
  round 2 or 3. The adversary shows each honest node different twins, and
  the honest requests that follow exceed the cap.
* **The signing rule matters.** Under `built`, a node refuses when it has
  built round `r`. That rule needs no history, but it stalls `nest` at
  round 40: a node that comes late to round 41 needs a join that the
  others have already made, and every signer refuses it. Citing the
  certificates of round 41 that the node holds (`reuse`) does not cover
  its join. Under `clean`, the signers' round-41 blocks contain pairs of
  the request, so they sign.
* **Honest nodes must avoid joins.** A `react` node that takes a block of
  every author joins both carriers of `bulk`, is refused, and stalls the
  system at round 39. Taking blocks that join nothing first, and joining
  blocks only to reach a quorum, removes the stall.
* **A horizon defeats the test of `clean`.** A signer cannot test rounds
  it has deleted, so under `oldjoin` it signs a join 25 rounds back. The
  blocks below the horizon are not fetched, so the fullest honest disk
  holds 6 blocks of Byzantine authors.

## 4. Open

* A bound on what one certificate may name, without the stall a cap
  causes. The mass comes from blocks created late at old rounds; the rule
  constrains only where they are joined.
* Whether a Byzantine node can build the doubling family at the current
  round, with each level certified in public. The simulation does not try.
* Liveness of `clean` in general. The refusal sends a block of round `r`
  whose references join no pair of `E`; the requester then takes them,
  but may join other pairs, and the loop has no proved end.
