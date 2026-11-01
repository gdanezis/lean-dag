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
* **The test of `clean` needs the signer's past rounds.** The node keeps
  every block it has stored (garbage collection is out of scope), so a
  signer can always test the round of a request. Under `oldjoin`, a join
  25 rounds back is refused and no Byzantine block enters. Only with a
  simulated horizon of 20 rounds, which the node does not have, is that
  join signed; the blocks below the horizon are then not fetched, and the
  fullest honest disk holds 6 blocks of Byzantine authors.

## 4. The mass

The blocks of Byzantine authors that certificates do not keep out of
honest histories share three properties.

* **They are twins, beyond one chain per author.** Under `nest` every
  one of them is a twin. Under `bulk`, 76 of 153 are; the others are the
  chains of Z and Y that carry the twins, one block of each author a
  round, which no rule on twins can tell from an honest node's chain.
* **They are late.** A block of round `j` is *late* when it is created
  after every honest node has built round `j + 1`. No honest block can
  then reference it, so its honest support is zero. Under `nest` with
  certificates, 197 of 221 such blocks are late at `depth = 13`, and 715
  of 741 at `depth = 39`. The others are the tops, which honest nodes
  adopt at the frontier. Honest blocks have support 6, all the other
  honest nodes, in all but a few cases. The twins of `split` are not
  late, and each has honest support 1.
* **They hang below a top.** A block that references a late block of
  round `j` is of round `j + 1`, and is not honest. The mass is therefore
  a structure of Byzantine blocks whose only link to an honest block is
  its top, adopted at the frontier. The structure joins nothing below the
  frontier, so its history holds at most one block of each Byzantine
  author in each round. Its twins arise only between structures that
  different honest nodes adopt, or that one honest node adopts at
  successive rounds. Honest nodes then join them in public, under
  certificates whose `E` consists of late blocks.

The size of the mass is argued, not proved. Let an honest node adopt
structures one at a time. A structure's top author must not be exposed
in the node's history, so it can have no chain in an earlier structure
it adopted. A Byzantine block at the frontier must reference honest
blocks of the round below, and these carry the evidence of every join
made public more than `Δ` before. So nesting at the frontier stops once
evidence spreads, and under `rtnest` a round holds 7 blocks of Byzantine
authors at most. The best order then has the `i`-th top author carry
chains of the `i` authors before it. An honest node gathers
`f(f + 1)/2` chains, against the `2^f − 1` of the doubling family, and a
round of the union of honest histories holds at most
`n + (n − f)·f(f + 1)/2` blocks. That is 52 at `n = 10, f = 3`, and 103
at `n = 13, f = 4`.

The attack `flat` builds these structures, back-dated `depth = 13`
rounds. In blocks of Byzantine authors in honest histories, all /
largest in a round:

| `n, f` | Rule | `flat` | `flat`, certificates | `nest`, certificates |
|---|---|---|---|---|
| 10, 3 | `react` | 542 / 42 | 497 / 38 | 224 / 17 |
| 10, 3 | `min` | 232 / 18 | 254 / 20 | 26 / 2 |
| 13, 4 | `react` | 1138 / 90 | 744 / 59 | 303 / 23 |
| 13, 4 | `min` | 429 / 34 | 605 / 48 | 39 / 3 |

Certificates leave `flat` nearly whole, and under `min` they let more of
it in. The joins are made by honest nodes, with certificates whose `E`
names up to 1764 pairs. Each structure is as long as the attacker dates
it back, so without garbage collection the mass of one attack grows with
the current round. Each Byzantine author can serve as a top only until it
is convicted, which every honest node does within `Δ` of the first
request naming its twins. The attack therefore works once per author.

## 5. Open

* **A rule on late blocks.** The mass is identified by lateness. A signer
  could refuse an `E` that contains a block it received only after it had
  built the round above. An honest node that has already adopted a late
  structure would then be refused the joins it needs. At a bare quorum
  that stalls the system, as the cap on `E` does. The test would have to
  be made when a block is adopted, and a late chain of an honest node
  catching up looks the same.

* A bound on what one certificate may name, without the stall a cap
  causes.
* The size of §4, which is argued, not proved.
* Liveness of `clean` in general. The refusal sends a block of round `r`
  whose references join no pair of `E`; the requester then takes them,
  but may join other pairs, and the loop has no proved end.
