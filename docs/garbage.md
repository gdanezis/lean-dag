# lean-dag — Garbage collection: bounding the DAG

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document records the garbage-collection mechanism and its
theorems: a **horizon** below which stores need not retain blocks, with
machine-checked proofs that commit safety, commit liveness, bounded
storage, and bootstrap all survive above it — and that no consensus on
the horizon is ever needed. Results carry **G**-labels (G1, G2, …),
continuing the house scheme. Everything lives in `LeanDag/GC/`, with
`decide` witnesses in `LeanDagTest/GC/`; the mechanism is strictly
additive — no definition or theorem of the base development was
modified. The DoS/novelty-budget layer this builds on is
`dos-equivocation-and-growth.md`.

## 0. Overview

**Notation** (shared with the DoS doc). `n` validators with at most `f`
Byzantine, `n ≥ 3f+1`; quorums have size `n−f`; `Correct` is the set of
non-Byzantine validators, `|Correct| ≥ n−f ≥ 2f+1`. `U` is the block
universe (every block any correct validator ever held — an analysis
object, not a store); `H(b)` is block `b`'s causal history (cone);
`viewUpto D v t` is validator `v`'s **store** at round `t` — the cones
of everything it accepted. `R` is the synchrony round
(`Synchronised`/`EventuallyDelivers` hold from `R` on); `κ` is the
per-acceptance novelty budget (`ByzBudget`); `RefsAccepted` is the
protocol rule *reference only what you accepted*. New objects here:

- `G` — the **horizon**, a round (per validator: `G_v`) below which
  nothing is retained, requested, or served;
- `chop U G` — the **truncation**: blocks of rounds `≥ G`, rounds
  rebased by `−G`, the new round-0 layer's reference sets emptied;
- `Λ` — the **lag**: how far `G` trails the current round;
- `Slots.chop S G d` — the induced slot schedule, re-indexed from a
  base slot `d` with `G ≤ slotRound d`;
- `Base U t G` — the **attested base**: the round-`G` blocks lying in
  the cones of round-`t` blocks by `≥ f+1` distinct authors;
- `joinIds` — what a joiner fetches: the base plus a correct peer's
  window strictly above the cut.

**The headline results.**

- **Safety crosses the cut unconditionally** (`decided_chop_iff`,
  `decided_agree_chop`). A validator re-running Mysticeti on the
  truncation decides every slot exactly as on the full universe, and a
  joiner holding *any* view of the truncation agrees with *any*
  full-history validator, slot for slot. The only hypothesis anywhere
  is `G ≤ slotRound d` — no synchrony, no liveness, no lag bound, no
  DoS condition.
- **Storage is constant at lag `Λ`** (`card_retained_le`). The retained
  store obeys
  `|retained| ≤ |Correct|·(Λ+1) + |Correct|·f + Λ·|Correct|·f·κ` —
  independent of how long the system has run. The DoS layer ended at
  "linear forever"; the horizon ends at "constant".
- **Join and relay cost the same constant** (`card_joinIds_le`,
  `card_serve_le`). A joiner's entire fetch is a subset of one correct
  peer's retained store; a correct author serves at most its own
  retained store plus its block. GC bounds sync cost, not just storage.
- **Bootstrap needs sampling, not consensus** (`Base` sandwiched by
  `exists_correct_attester_of_mem_base` / `correct_mem_base` /
  `accepted_mem_base`; `joinView`; `bootstrap_agree`). A joiner adopts
  a genesis layer filtered per block by `f+1` distinct attesters —
  attestations *are* blocks, no signatures — and its decisions equal
  every full-history validator's. Bases sampled from different peers
  need not match; verdicts still do.
- **Horizons are local** (`chop_chop`, `decided_agree_horizons_chop`,
  `viewUpto_subset_viewUpto_succ`). Different validators cut at
  different rounds; a deeper cut is just another cut, verdicts are
  horizon-independent, and post-`R` possession universalises in one
  round, so nothing a peer still lacks is ever discarded. The
  admissible lag envelope is `2 ≤ Λ ≤` storage appetite (§6) —
  everything below 2 loses a completeness property, never safety.
- **Truncation forgives, at a bounded and priced rate** (§3, §8). An
  equivocation whose witnessing pair falls strictly below the cut is
  forgiven — the statute of limitations — but re-entry runs under the
  windowed budget: one reveal per author per epoch, `Λ·f·κ` of freight
  per correct store per epoch, a term the storage constant already
  carries. Commit safety never depended on any of it.

## 1. The problem

The DoS results end at *linear* storage: under the novelty budget a correct
validator's view obeys `|V_v(t)| ≤ |Correct|·(t+1) + |Correct|·f·(1+t·T)`
(B4) — linear in the round `t`, and that is optimal for what it claims,
since correct production alone is `|Correct|` blocks per round. But linear
still diverges. A validator that runs for years retains years of history,
and a joining validator must fetch it. Eventually storage — and sync time —
is exhausted not by an adversary but by the protocol's own health.

What we want is **bounded storage**: retain a *window* of the DAG and
discard the prefix. This collides with two properties the model relies on:

- **Completeness / downward closure.** `BlockUniverse.complete` says every
  referenced block is present; `View.complete` closes views downward; a
  block's cone `H(b)` reaches round 0 (D20 — self-parent chains reach the
  ground). Pruning any prefix falsifies all three as stated.
- **Cone-validity.** `ValidWrt`, `DoSValid` and `ExposedIn` are properties
  of cones. A validator that discarded the prefix cannot recompute them for
  the discarded rounds — and, more subtly, cannot recompute *exposure*
  whose witnessing pair sits below the cut (§3).

One scoping fact to keep straight throughout: **GC bounds *stores*, not
`U`.** The universe — every block some correct validator ever held — keeps
growing as an analysis object; the theorems live at the level of what a
validator retains (`viewUpto`) and what a joiner must fetch.

So garbage collection is a genuine model change, the third one after S10
(self-parent) and the novelty budget: a **horizon** `G`, a round below
which stores need not retain blocks and sync need not deliver them,
together with theorems that commit safety and commit liveness survive
above it.

## 2. The horizon, and truncation

The design variable: a round `G` (per validator: `G_v`), the **horizon**.
Below it, nothing is retained, requested, or served. The model-side
counterpart is the **truncation operator**:

> `chop U G` — the universe whose blocks are those of `U` at rounds `≥ G`,
> with rounds rebased by `−G` and the (rebased) round-0 blocks' reference
> sets emptied.

The rebasing is the key move: **the round-`G` layer becomes the new
genesis layer.** All four validity clauses then hold of `chop U G` exactly
as they hold of `U` — `predecessor`, `distinct_creators`, `quorum` and
`self_parent` constrain only rounds `> 0`, and the old round-0 special
case (`refs_empty_of_round_zero`) applies verbatim to the new base. This
is why truncation is an *operator producing a bona-fide `BlockUniverse`*
(G1) rather than a weakening of `complete` threaded through every proof:
every existing theorem — safety, liveness, counting, the budget — applies
to `chop U G` **unchanged**, because `chop U G` is just another universe.
The work was never re-proving the theory above the cut; it was relating
verdicts across the cut, and choosing the cut.

**Rebasing does not touch the slot schedule.** Verdicts are indexed by
`Slots` (leader per slot, `slotRound`). A node that recomputed leaders
from *rebased* rounds would assign different leaders than the network,
and every cross-node verdict comparison would be garbage. Nor can `chop`
simply keep absolute rounds: the base layer's emptied references would
then violate `quorum` (genesis-emptiness is *derived* from `predecessor`
at round 0 and does not generalize to round `G` without further argument). The
resolution: rebase the universe, **carry the offset**. The induced
schedule is `Slots.chop S G d hd` (`ChopDecided.lean`), re-indexed from
a base slot `d` whose round clears the horizon
(`hd : G ≤ slotRound d`), with `slotRound' k = slotRound (d + k) − G`;
every cross-node claim is stated in absolute terms through the
correspondence `k ↦ d + k`. Two structural facts make this light. The
rule layer
(`supporters`/`certificates`/`DirectCommit`/`DirectSkip`/`CertifiedIn`)
is round-indexed and **never consults the schedule**, so all of G2 and
per-slot G3 close with no correspondence at all; the schedule enters
only at the `Decided` level, where the correspondence (`decided_chop_iff`)
goes through by structural induction with the base-slot condition as the
*only* premise. And the base-slot condition is what makes the induced
schedule's keying survive: `G ≤ slotRound d` pins the rebased rounds
above zero, where subtraction is faithful.

**Model versus implementation.** `chop` *edits* the base-layer blocks
(empties their reference sets). In a real system a block's identity is a
hash over its references, so this is not a re-hash of history: it is the
checkpoint *reinterpreting* those ids as opaque geneses. The model's block
map makes this a definition; an implementation makes it a rule about what
the sync layer serves.

Two invariants make a horizon *admissible* for a validator:

- **(A1) Decided below.** Every leader slot with proposer round `< G` is
  decided (committed or skipped) in the validator's view. What A1 is
  *for*: not verdict invariance — verdicts for slots `≥ G` are
  window-local and invariant regardless (§4) — but **ledger totality**:
  a slot's verdict reads rounds `slotRound k` through `+2`, so pruning
  above an undecided slot discards its certificates and the slot can
  never be decided — the ledger stalls below the validator's own cut. A
  liveness-of-output failure, never a safety one. A1 is a policy-layer
  invariant (§6), not a hypothesis of the safety transfer — none of
  `decided_chop_iff`/`decided_agree_chop`/`bootstrap_agree` assumes it. It
  is also *dischargeable*: a committed run decides everything below it
  (`all_decided_below_of_fairRun`), so post-`R` the frontier below a
  commit is total.
- **(A2) Lag bound.** `G` trails the validator's current round by a
  margin `Λ`. Note what `Λ` is *not* for: the indirect-anchor reach —
  the anchor sits *above* its slot, so anchor reach never looks below
  the cut. What `Λ` provides is two **completeness** properties, not
  safety: the one-round possession bound of the depth rule (G9,
  `Λ ≥ 1`) and the attestation lag of the certified base (G11, `Λ ≥ 2`,
  tight on data). The full accounting of what constrains `Λ` — and what
  does not — is §6's *lag envelope*.

## 3. What breaks, what bends, what holds

An inventory against the base development.

**Holds without change (after rebasing).**
- The commit rules are **round-local**: votes at `r+1`, certificates at
  `r+2`, `DirectCommit`/`DirectSkip` read a three-round window, and the
  indirect rule consults an anchor *above* its slot. Nothing in a verdict
  for slot `r` looks below `r`.
- L1/production is one-round-local (references point one round down);
  L4/L6 operate in the slot window. Liveness never reaches below the cut.
- `DoSValid` transfers to `chop U G` **one-way**: cones shrink under
  truncation, so exposure shrinks, so the per-block condition weakens —
  `DoSValid U → DoSValid (chop U G)` (`dosValid_chop`). The failure of
  the converse direction *is* the statute of limitations, below, and
  the witness file makes it visible on data.

**Bends #1: the budget must be windowed.** The novelty budget is not
horizon-friendly as stated — it is *anti*-friendly: novelty is antitone
in the store, so pruning `V` below `G` makes every arriving block's
`H(b) \ V` **explode** with the entire discarded prefix, and the budget
would defer every correct block forever. The repair is to measure
novelty **on the truncated universe**:

> windowed novelty := `novelty (chop U G) V b` = `(H(b) ∩ [G, ∞)) \ V`

— the fetch never descends below the horizon, which is the entire point
of GC. This is a definition with its own law (**G13**): windowed novelty
is *antitone under cut-advance* — for `G' ≥ G`,
`novelty_{G'} ⊆ novelty_G` — so as the window slides, **pruning only
cheapens blocks**: a block within budget never leaves it, and deferral
decisions never flip
the wrong way. Without G13 the
bounded-storage headline (G6) would be unprovable over a *sequence* of
cuts.

**Bends #2: exposure below the horizon — the statute of limitations.**
`ExposedIn` needs the witnessing pair — two same-author blocks at one
round. If the equivocation round falls **strictly below** `G`, the pair
is gone: in `chop U G` the author is not exposed, and `DoSValid` no
longer forbids referencing it. Exclusion permanence (D12, D17) is a
statement about `U`; truncation **forgives**. A precision the witnesses
carry: the statute applies strictly below the cut — a pair *at* round
`G` survives into the base layer (base blocks keep round and creator),
and later cones containing both halves are still exposed. The design accepts
forgiveness, for the reasons below, set against the
alternatives:

1. **Accepted: the budget is the backstop.** C2's "one reveal per
   author, ever" weakens to **one reveal per author per GC epoch** — the
   author must first rebuild a self-parent chain from the *new* genesis
   layer (D20 rebased), in public, under the windowed budget, which prices
   every block of the comeback. Forgiveness is a bounded-rate phenomenon,
   not a cliff (§8). And its blast radius is confined by an existing
   theorem: **commit safety never depended on `DoSValid` at all** (D14),
   so the statute of limitations touches only the DoS-storage layer —
   never safety.
2. **Rejected: tombstones** — carrying the exposed set across the cut as
   explicit state. Same grounds as the evidence channel (S3): it is
   state *beside* the DAG, needs its own agreement and its own GC, and
   the backstop makes it unnecessary for storage purposes. Revisit only
   if accountability becomes a goal.
3. **Rejected: holding `G` below live exposures.** It hands the
   adversary veto power over GC — equivocate once and your evidence must
   be retained forever, which is the unbounded growth GC set out to
   remove.

**Breaks, by design, and is replaced.** Global downward closure and
"full history available to all". The replacement, proved: for everything
the protocol still *does* — validate new blocks (G1), decide slots
(`decided_chop_iff`), stay live (`sustains_chop`), bound storage
(`card_retained_le`) — the truncated universe is as good as the full
one.

## 4. Safety above the horizon

**The right level for invariance is views, not `U`.** `U` contains
held-but-never-accepted blocks (S5 keeps `held` undeduplicated), which no
correct validator retains or serves — a certificate held once and
accepted by nobody counts in a `U`-level verdict but is unobtainable by
any syncing node, GC or no GC. The existing machinery already has the
right idiom for this: decisions are **view-relative and monotone** (L2),
**never conflicting** across views (M6), and **propagating** (L3). The
results, in that idiom:

- **G1 (truncation is a universe)** — `Chop.lean`. `chop U G` satisfies
  `complete`, `valid`, `no_equivocation`;
  `DoSValid U → DoSValid (chop U G)` (`dosValid_chop`). Immediate
  consequence: every existing theorem holds of `chop U G`.
- **G2 (verdict invariance)** — one witness now, not a lemma per
  relation. `truncates_chop` (`Properties/Arcs/GC.lean`) exhibits the
  cut in the generic `Truncates` relation: the rebased round's blocks
  keep their membership, authorship and references above the settling
  round. `Properties.LocalTruncate.of_banded` turns that witness into
  G3 below for any rule with a band, which is what replaced the nine
  separate per-relation lemmas the old `Chop.lean`/`ChopDecided.lean`
  proved by hand (`supporters_chop`, `blames_chop`, `certificates_chop`,
  `directCommit_chop`, `directSkip_chop`, `certifiedIn_chop`,
  `certificatesIn_chop`, `directCommitIn_chop`, `directSkipIn_chop`).
- **G3 (decision invariance)** — per slot, and for the **full decision
  relation**: `decided_chop_iff` (`Properties/Arcs/GC.lean`). A validator
  re-running Mysticeti on the truncation from its truncated view
  decides slot `k` exactly as it decided slot `d + k` on the full
  universe. It was a structural induction through anchors and
  intermediate skips, both directions, in `ChopDecided.lean`; it is now
  `LocalTruncate` applied to the witness that the cut is a `Truncates`,
  and so holds for every rule with a band rather than for the core
  alone. The only premise is `G ≤ slotRound d` — no synchrony, no
  liveness, and A1 is *not* a hypothesis (§2).
- **G4 (cross-cut agreement)** — `decided_agree_chop`
  (`Properties/Arcs/GC.lean`), and it is
  deliberately asymmetric: outright **equality of verdicts** between a
  full-history validator and a joiner holding an **arbitrary** view of
  the truncation. The asymmetry matters: a joiner's view is never
  `V.chop` for any full-history `V` (lifted to `U` it would not be
  downward closed), so `decided_unique` is played *inside* the
  truncation against a truncated view, and `LocalTruncate` carries the
  verdict across the cut. Agreement across *different* horizons
  `G_v ≠ G_w` is `decided_agree_horizons_chop` (§6).

Safety needs no new quorum argument anywhere: it inherits T0/T3/M-series
through G1, and G2–G4 are locality and correspondence bookkeeping — the
counting was never redone.

## 5. Liveness, storage, and the cost of joining

- **G5 (liveness transfer)** — `sustains_chop` (`Properties/Arcs/GC.lean`)
  is the one witness that the cut `Sustains` the protocol from its
  horizon: every predicate a mechanism computes from a block's
  membership, authorship and references — a protocol's own certificate
  layer among them — transports across the cut with it, which is what
  used to need a `DeliversQuorum`/`Live` transfer lemma apiece. `Window.lean`
  still gives the store-level facts (`populated_chop`), so L1 holds in
  the truncated universe, and the post-`R` commit chain with it.
- **G13 (windowed novelty)** — `Window.lean`. The definition of §3 with
  its cut-advance law (`history_chop_anti`, `novelty_chop_anti`): as
  the window slides, pruning only cheapens blocks. Prerequisite to G6
  over a sliding cut.
- **G14 (store correspondence)** — `viewUpto_chopD`. Pruning a store
  below `G` yields exactly the `viewUpto` of the induced delivery on
  `chop U G`:
  `viewUpto (chopD D G) v m = (viewUpto D v (G+m)).filter (G ≤ round ·)`.
  The bridge between "what a validator retains" and "B4 on the truncated
  universe".
- **G6 (bounded storage — the headline)** — `card_retained_le`. Stated
  **per time**, because a validator's life is a sequence of cuts, not
  one: at each `t` with `G ≤ t ≤ G + Λ`, the retained store
  `(viewUpto D v t).filter (G ≤ round ·)` obeys
  > `|retained| ≤ |Correct|·(Λ+1) + (|Correct|·f + Λ·|Correct|·f·κ)`
  — **constant in `t`**, under `ByzBudget κ` and `RefsAccepted`
  (mechanism-side, instantiate `κ` through the budget sandwich of the
  DoS doc), with G13 guaranteeing the sequence of prunings never
  un-prices anything. The DoS story ended at "linear forever"; the GC
  story ends at "constant, at lag `Λ`".
- **G6b (bounded join)** — `base_subset_retained`, `card_joinIds_le`.
  The joiner's *entire* fetch — attested base plus window (`joinIds`) —
  is a **subset of one correct peer's retained store**, so the same G6
  constant bounds sync cost, not just storage.
- **G7 (relay obligation, windowed)** — `history_chop_subset_retained`,
  `card_serve_le`. What a correct author can be asked to serve for its
  block — the block's truncated cone — is its **own retained store
  above its own horizon, plus the block itself** (`RefsAccepted` one
  step down, S10 the rest of the way): the G6 constant plus one. Floods
  are still dampened at acceptance; now the *honest* obligation is
  bounded too, and everything below the cut is the base's job.

## 6. Setting the horizon without consensus

The traditional design runs consensus on `G` itself: after a commit, all
correct validators agree on a GC round. That works, but it is not
needed: **horizons need not be equal — each needs to be admissible.**
G4 already makes heterogeneous horizons safe. Two local rules, not
exclusive:

- **The commit-frontier rule.** `G_v :=` (the largest round such that
  every slot below it is decided in `v`'s view) `− Λ`. A1 holds by
  construction — and is *supplied* post-`R` by the pipelining theorem
  that a committed run decides everything below it
  (`all_decided_below_of_fairRun`); A2 by the margin. Note the frontier
  is the *decided* frontier, not the commit frontier: direct skips
  advance it too. On skew between two validators' frontiers, the model
  is round-synchronous with static views, so a clock-lag constant has
  no carrier here; what it proves instead is that skew **does not need
  bounding for correctness** — verdicts at different horizons are equal
  outright (`decided_agree_horizons_chop`), and different horizons compose
  (`chop_chop`: `chop (chop U G₁) (G₂−G₁) = chop U G₂` — a deeper cut
  is just another cut, so validators at different `G` sit on one tower
  of truncations, never in incomparable worlds). No agreement protocol;
  the DAG's own commits are the synchronizer, and timing constants live
  with `R` in `liveness.md`.
- **The common-core rule** (depth-based). Possession universalises in
  **one** round: `viewUpto_subset_viewUpto_succ` — post-`R`, everything
  *any* correct validator retains by round `m` is in *every* correct
  store by `m+1`. So a validator may set `G_v := t − Λ` for any
  `Λ ≥ 1` knowing no correct peer in the L1 envelope still lacks what
  it discards (`pruned_subset_peer_store`). **The rule's guarantee is
  exactly coextensive with that envelope**: any validator outside it —
  partitioned, crashed, joining — is by definition on the bootstrap
  path (§7).

The two rules bound different things (frontier: decidedness; depth:
universality of possession) and the admissible horizon is their minimum.

**The lag envelope — what actually constrains `Λ`.** Collected in one
place, because the answer is easy to misremember: *safety constrains `Λ`
not at all*; every restriction is a completeness or cost statement, each
pinned to its theorem.

| bound | source | what breaks below it |
|---|---|---|
| — (any `G` is safe) | `decided_chop_iff`, `decided_agree_chop`, `bootstrap_agree` | nothing — commit safety carries no lag hypothesis at all; its only premise is `G ≤ slotRound d` |
| `Λ ≥ 0` vs the *decided* frontier | A1 / `all_decided_below_of_fairRun` | ledger totality: a slot reads rounds `slotRound k … +2`, so cutting above an undecided slot discards its certificates and the slot is undecidable forever — output stalls, safety unharmed |
| `Λ ≥ 1` | G9, `viewUpto_subset_viewUpto_succ` | no-desync among correct peers: possession universalises in exactly one round, so at `Λ = 0` a peer may still lack what you discard |
| `Λ ≥ 2` | G11, `accepted_mem_base` (`t ≥ m + 2`, tight on data) | base completeness for joiners: below it, an accepted round-`G` block can be missing from the attested base and a window block dangles — the `Dexcl` witness realises this at `t = m + 1` |
| upper bound: none | G6/G6b/G7 constants | nothing breaks; storage, join cost and relay obligation grow **linearly in `Λ`** (`|Correct|·(Λ+1) + |Correct|·f + Λ·|Correct|·f·κ`), so the ceiling is appetite, not correctness |

One further consideration that is a trade-off, not a restriction: `Λ` is
the epoch length of the statute of limitations (§8). Smaller `Λ`
forgives exposed equivocators sooner; the budget prices every re-entry
either way. The practical envelope is therefore
**`2 ≤ Λ ≤` storage appetite** — everything below 2 loses a
completeness property, never a safety one.

The policy results:

- **G8 (heterogeneous horizons)** — `Horizon.lean`. The composition law
  `chop_chop` — every pair of horizons is related by the one operator —
  and `decided_agree_horizons`: validators truncated at *different*
  horizons, holding arbitrary views of their truncations, decide every
  shared slot (matched through the absolute index `d₁+k₁ = d₂+k₂`)
  identically. The full-history verdict both are compared against is
  supplied under liveness by L8/L10.
- **G9 (no desync)** — `viewUpto_subset_viewUpto_succ`,
  `pruned_subset_peer_store`. Post-`R`, possession universalises in one
  round, so a correct validator never *needs* a block below any correct
  peer's admissible horizon (`Λ ≥ 1`), except at bootstrap — where the
  attested base suffices. This is the formal content of "slightly
  different horizons are fine".

## 7. Bootstrap: the attested base

Where a residue of agreement genuinely lives is bootstrap — and the
inexact certificate dissolves most of it. A validator so far behind that
its needs predate every peer's horizon cannot fetch the prefix — it must
adopt the new genesis layer from others. Demanding `f+1` *identical*
checkpoints would be wrong: correct validators' layers share the correct
core exactly (backbone) but differ in the Byzantine fringe, so honest
presenters need never match block-for-block. The right primitive is the
**inexact certificate**, filtered per block:

> attest the layer, keep what `≥ f+1` distinct authors attest.

Post-`R` each correct attestation is `C ∪ B_v` — the **shared correct
layer** `C` (identical across correct validators, `|C| ≥ n−f`, by the
backbone; one block per correct author by T1) plus a varying Byzantine
fringe. Among any `n−f` attestations, `≥ n−2f ≥ f+1` are correct and each
contains all of `C`, so nothing of `C` is filtered out; conversely
anything surviving the filter has a correct attester, hence lies in a
correct cone. The certified base is therefore **sandwiched** —
`C ⊆ Base ⊆` (the layer of the union of correct cones) — and the
sandwich is all rebasing needs: window completeness holds two rounds
above the window frontier (`t ≥ m + 2`, one round for the carrier, one
for the backbone — tight on data), verdicts above the cut are view-local
(G2), and extra fringe is inert and bounded. Bases need not agree,
exactly as horizons need not. Two precisions the witnesses carry: the
fringe may contain **several same-author blocks** — harmless, since
`no_equivocation` constrains correct authors only, and the witnesses
carry Byzantine multi-geneses (`Udouble`); and when both halves of a
round-`G` equivocation circulated, **both clear the filter**, so the
certificate *preserves* boundary exposure — the statute of limitations
is mitigated at the cut itself.

**No signatures are needed**: in this model a validator's attestation
*is its block* — its cone is its objective, checkable (D13), unforgeable
statement of what the layer contains. The certificate is DAG-internal
and decidable:
`Base U t G := { y at round G : y lies in the cones of round-t blocks by
≥ f+1 distinct authors }`, with the guarantee side supplied by `n−f`
authors *having* round-`t` blocks (Populated) rather than by collecting
messages. Equivocating attesters gain nothing — the filter counts distinct
authors, and `f+1` authors always include a correct one
(`exists_correct_of_card`). A joiner adopts a specific pair `(t, G)`;
which pair (presenters may offer different cuts) is a protocol detail
that G8 makes inert.

The bootstrap results:

- **G10 (the sandwich)** — `AttestedBase.lean`. Post-`R`,
  `C ⊆ Base U t G ⊆` the round-`G` layer of the union of correct
  cones — completeness from the backbone (`correct_mem_base`),
  soundness from `f+1`-implies-a-correct-attester
  (`exists_correct_attester_of_mem_base`). Witness:
  `Base Utwin 1 0 = {1,2,3}`, the shared correct layer exactly, both
  equivocation halves filtered.
- **G11 (window completeness)** — `accepted_mem_base`
  (`Bootstrap.lean`). *Every* round-`G` block a correct validator
  accepted into its window by `m` — Byzantine-authored included, not
  merely blocks referenced by surviving window blocks — is in the base
  attested at any `t ≥ m + 2`, and the bound is tight on data. Three
  existing theorems composed: acceptance puts the block in a correct
  store, the store rides into its keeper's next block
  (`viewUpto_subset_history`), and the backbone
  (`mem_history_of_correct`) carries that block into every correct
  round-`t` cone — a cone *is* an attestation. The scope — blocks in
  *accepted* cones — is exactly the obtainable window of §4.
- **G12 (bootstrap safety)** — `joinView`, `bootstrap_agree`. The
  joiner's assembly — base as genesis layer plus a correct peer's
  window strictly above the cut — is a bona-fide `View` of `chop U G`
  (downward closure is the content: window references above the cut
  stay in the window; references *at* the cut are exactly the G11
  blocks), and any decision reached from it **equals** any full-history
  validator's. Inexact certificates, exact decisions.

## 8. The forgiveness ledger

What survives of the exclusion economy across epochs, and why nothing
new needed proving.

**Within an epoch, everything survives.** `chop U G` is a bona-fide
`BlockUniverse` and `DoSValid` crosses the cut (`dosValid_chop`), so the
entire D-series applies to the truncation *verbatim*: exposure anywhere
in the window debars for the rest of the window (D12), at most `f`
authors are ever exposed (C2), exclusion lands only on the guilty (D15).
No theorem is re-proved; the truncation is just another universe.

**Across a cut, forgiveness is one-way and priced.** The statute of
limitations (`LeanDagTest/GC/Chop.lean`) forgives exactly the
equivocations whose witnessing pair falls strictly below the cut — a
pair *at* the cut survives, and the attested base *preserves* boundary
exposure (both halves of a circulated round-`G` equivocation clear the
`f+1` filter). To be debarred again, a forgiven author must equivocate
**again, inside the new window**: one reveal per author per epoch is the
maximum forgiveness rate. And the re-entry is not free — the windowed
budget backstop (`byzBudget_chopD`, `refsAccepted_chopD`, feeding
`card_retained_le`) prices a forgiven author's freight exactly as it
prices a fresh author's: `Λ·f·κ` per correct store per epoch. "Adversary
work per epoch" is not a new quantity to bound — it is the third term of
the G6 constant.

**And safety never depended on any of it** (the D14 note, restated for
GC): commit safety is quorum arithmetic; exclusion and forgiveness are a
DoS-layer economy. The cross-cut safety results (`decided_chop_iff`,
`decided_agree_chop`, `bootstrap_agree`) carry **no** exclusion, budget,
or exposure hypothesis — their only premise is the base-slot condition
`G ≤ slotRound d`. A world that forgives every equivocation still
commits the same blocks; it just stores more junk.

## 9. What remains

- **Cutting under asynchrony.** The commit-frontier rule stalls when
  decisions stall, and A1 cannot be weakened: skipping an undecided slot
  by fiat when some correct validator may have committed it is an
  output-safety change, and making the fiat safe means agreeing on it —
  consensus again. The honest behaviour during sustained asynchrony is
  therefore: the cut stalls at the decided frontier and storage degrades
  from "constant at lag `Λ`" to the linear, budget-bounded B4 guarantee,
  which needs no synchrony; when synchrony returns, L10 closes the
  frontier and the horizon catches up. The *possession* half of the rule
  admits a commit-free, asynchrony-safe replacement that is identified
  but **not formalized**: an observed-coverage criterion — cut at `G`
  once the retained round-`G` layer lies in the cones of round-`t`
  blocks by `n−f` distinct authors (the existing `attesters` read at
  quorum threshold). References are unforgeable possession receipts, so
  coverage proves `≥ n−2f ≥ f+1` correct validators hold what is
  discarded, with the evidence surviving above the cut; post-`R` the
  backbone makes coverage automatic, so the criterion degenerates to
  the depth rule exactly when the depth rule was valid. Its failure
  mode under asynchrony is firing late — retention, not wrongful
  pruning.
- **Application state.** For the DAG machinery the attested base *is*
  the checkpoint, with no signatures. What stays out of scope is
  application state — the ledger prefix a joining node also wants — a
  different object with different trust requirements; "bootstrap" for a
  full node means both.
- **Timing constants.** The model is round-synchronous with static
  views: how far apart two correct validators' decided frontiers can
  drift in *time* is a statement about clocks and lives with `R` in
  `liveness.md`, not here. What the model proves is that the answer
  does not matter for correctness (G8).

## 10. Where everything lives

| module | contents |
|---|---|
| `LeanDag/GC/Chop.lean` | the operator; reachability and history across the cut; `dosValid_chop` (G1) |
| `LeanDag/GC/ChopDecided.lean` | `Slots.chop`, the induced schedule (G3, G4); `View.chop` moved to `Common/Record/Chop.lean`, and `decided_chop_iff`/`decided_agree_chop` to `Properties/Arcs/GC.lean` (§4) |
| `LeanDag/GC/Window.lean` | `chopD`, windowed novelty and store correspondence, liveness transfer, `card_retained_le` (G5, G6, G13, G14) |
| `LeanDag/GC/AttestedBase.lean` | `attesters`, `Base`, the sandwich (G10) |
| `LeanDag/GC/Bootstrap.lean` | `accepted_mem_base`, `joinIds`/`joinView`, `card_joinIds_le`, `card_serve_le`, `bootstrap_agree` (G11, G6b, G7, G12) |
| `LeanDag/GC/Horizon.lean` | `chop_chop`, `decided_agree_horizons`, `viewUpto_subset_viewUpto_succ` (G8, G9) |
| `LeanDagTest/GC/Chop.lean` | the cut computed on `Uexcl`; the statute of limitations on data; G6 on `Dtwin`; the base on `Utwin`/`Uexcl`; G3/G4 with the induced schedule |
| `LeanDagTest/GC/Bootstrap.lean` | `Dexcl` (the honest delivery schedule for `Uexcl`); G11 tight at `t = m+2`; the joiner's assembly and G12 on data |
| `LeanDagTest/GC/Horizon.lean` | the composition law recomputed blockwise; one-round possession on data; heterogeneous horizons deciding `some 11` |

All witnesses are by `decide`; all proofs use the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) only.
