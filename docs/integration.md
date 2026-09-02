# lean-dag — Integration: composing the arcs

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Every arc of this development was built additively: each consumes the
core read-only, and none modifies another. That discipline kept the
arcs independent, and it left a question unanswered — **do the arcs
compose
with each other?** A validator that garbage-collects below a horizon,
recovers from a crash by Safe Skip, runs an adaptive leader schedule
and tolerates hybrid faults is running all four mechanisms at once, and
nothing proved so far says the four are jointly consistent.

This document is the design record for the **integration** arc. Its
thesis is that the composition matrix must *not* be proved cell by
cell. Nine arcs pair into thirty-six combinations, and triples into far
more; the development would double in size to say something most
readers would assume anyway. Instead: give each arc a small,
explicitly named **interface** — the invariants it consumes and the
invariants it preserves — and prove interface-to-interface facts. Then
composition is a corollary, and the cost is linear rather than
quadratic. §2 collects that interface and reports an audit confirming
it is closed; §3 turns it into a work plan of roughly twenty small
lemmas in place of thirty-six real proofs.

Results will carry **I**-labels. Everything will live in
`LeanDag/Integration/`, with `decide` witnesses in
`LeanDagTest/Integration.lean`.

## 1. What the arcs actually are

The arcs are not all the same kind of object, and the composition
strategy differs by kind. Four kinds:

**Universe transformers.** Take a `BlockUniverse` and produce another:
`chop U G` (§9, truncation at a horizon) and `SkipMsg.skipFill` (§12,
extension by a fill). These are the arcs that can *break* another arc's
hypotheses, because they change the object every other arc quantifies
over.

**Fault-layer variants.** Replace the `Faults` instance: `Faults5`
(§10, `n ≥ 5f+1`) and `HybridFaults` (§14, with its *derived* base
instance). These change the quorum arithmetic under everything.

**Schedule- and timing-layer variants.** Replace or refine the `Slots`
instance or the timed structure: `slotsOf` (§13, adaptive assignment),
`Slots.chop` (report §9's induced schedule), `ReactiveCore`/`ReactiveM`
(report §11), `CatchupSync` (report §6.12).

**Property provers.** Consume a universe plus conditions and conclude:
chain quality (§7), the storage bounds (§8), the liveness capstones
(§6), agreement (§5).

The asymmetry is the point. A property prover cannot break anything —
it only reads. A transformer can break everything. So the interface
discipline needs to bear almost entirely on the transformers, and the
property provers need only be *stated* against named invariants rather
than against incidental facts about a particular universe.

## 2. The named invariants

The development already has the right vocabulary; it has simply never
been collected. Collecting it is the substantive part of
the plan, because the invariants do **not** all live at the same level,
and the level is what determines which transformer can break them.

There are three layers, and they are not independent: a `Delivery` is
*indexed by* a universe, so a universe transformer forces a delivery
transformer, while a `Slots` instance is independent of the universe
entirely.

### 2.1 Layer U — the block universe

The object: `BlockUniverse Validator BlockId Payload`. Broken by:
`chop`, `skipFill`.

**U1. The DAG laws (P1–P5).** Carried by the `BlockUniverse` structure
itself — predecessor rounds, distinct creators, the reference quorum,
the self-parent clause, completeness, non-equivocation.
*Provides:* everything; no theorem in the development is stated without
them. *Preservation is free*, in the strict sense that a transformer
cannot typecheck without proving it — which is why `chop` and
`skipFill` both discharge it in their definitions rather than as
lemmas.

**U2. Production.**
```lean
def PopulatedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r
```
*Provides:* every liveness result in the development. L4 (a reliable
leader is committed) consumes it three times — at the leader's round
and the two above — and every capstone above L4 inherits it. If a
transformer preserves nothing else, it must preserve this or nothing
downstream of §6 applies.

**U3. Coverage.**
```lean
def SynchronisedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```
*Provides:* the other half of L4, and with it the whole liveness line.
Note the shape: it is a statement about **every** block of `T` at
**every** round above `R`, which is precisely why adding blocks to a
universe is dangerous for it and removing blocks is not (§3.1, I4/I5).

**U4. The exposure condition.**
```lean
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```
*Provides:* C2 (at most `f` authors exposed per cone) and through it
C1′, the general per-cone storage bound of §8. Consumed by nothing
outside §8 and §9 — safety and liveness are provably independent of it,
which is one of §8's headline claims.

**U5. Honest non-equivocation.**
```lean
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator ∉ H.byzantine →
    (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j
```
*Provides:* every safety theorem of §14 — H2 through H6. It is P5 at
the wider honest class, and it is the *only* invariant in this list
introduced by an arc rather than by the core, which makes it the
canonical example of the audit question of §2.4.

**U6. Verdict facts** — `Decided U V k v`, and its bounded variant
`DecidedWithin`. Not an invariant of a universe so much as a family of
derivable facts about one, but it behaves like one for composition
purposes: a transformer must say what happens to verdicts.
*Provides:* the ledger (M7, M8), chain quality (§7), and — through
`DecidedWithin` — the entire adaptive fixpoint (§13).

### 2.2 Layer D — the delivery structure

The object: `Delivery U`, **indexed by the universe**. This dependency
is the structural fact this document's plan missed as first written: a
universe transformer `F : U ↦ F U` does not merely need to preserve
delivery-level invariants, it needs a *transformer of its own* at this
layer, `F_D : Delivery U → Delivery (F U)`, before those invariants can
even be stated in the transformed setting.

GC has one — `chopD D G : Delivery (chop U G)`, shifting every index by
`G`. **Safe Skip has none**, which is why I6 as first drafted was not a
well-formed obligation (§3.1).

**D1. Production, operationally** — `Live U D N`: every correct
validator has a genesis block, and one holding a quorum at `r` builds
at `r+1` (P8). *Provides:* the untimed production derivation, hence U2.

**D2. Delivery conditions** — `DeliversQuorum D`, `EventuallyDelivers
D R`.
*Provides:* the legacy quorum route (§15) and the delivery derivation
of coverage (L7a). Both already have `chopD` counterparts.

**D3. The storage budgets** — `UniformBudget D T`, `ByzBudget D κ`,
`RefsAccepted D`. *Provides:* B4 and B, the linear-storage capstone of
§8. All three have `chopD` counterparts (`byzBudget_chopD`,
`refsAccepted_chopD`).

### 2.3 Layer S — the schedule

The object: `Slots Validator`, independent of the universe. Broken not
by universe transformers but by *schedule* variants — `Slots.chop`
(§9's re-indexing) and `slotsOf` (§13's adaptive assignment).

**S1. Fairness** — `FairScheduleOn T` (a reliable leader arbitrarily
far out) and `FairRunOn T c` (`c` consecutive reliable-led slots
arbitrarily far out). *Provides:* recurrence (L6), chain-quality
inclusion (CQ6, CQ7), and the liveness capstone L10.

**S2. Shape** — `SpansEligible c` (a run of `c` reaches past everything
below it) and `BoundedSpacing s`. *Provides:* the committed-run
descent, hence L10 and its Odontoceti and hybrid mirrors.

**S3. Adaptive fairness** — `PlacesRuns P T c`: every assignment the
policy can emit still places a reliable run in each epoch.
*Provides:* the existence half of the adaptive fixpoint (AL5). Note it
is a condition on a *policy*, not on a schedule — the only invariant in
the list at that level, and a sign that §13 sits one abstraction step
above the rest.

### 2.4 What the audit found

The claim that these are *all* the hypotheses is now checked rather
than asserted, by querying the extracted statements of the principal
capstones (`dos_resistance`, `chain_quality`, `decided_agree_chop`,
`card_retained_le`, `bootstrap_agree`, `all_decided_below_of_fairRun`,
`commits_recur_on`, `decided_fill`, `adaptiveRun_exists`,
`adaptiveRun_agree`, `committed_of_correct_block`, `card_history_le'`,
`card_viewUpto_le`) for hypothesis-position identifiers outside the
list. Three findings, all of which changed this plan:

1. **The schedule layer was missing entirely.** `FairScheduleOn`,
   `FairRunOn`, `SpansEligible` and `PlacesRuns` appear as hypotheses
   of five capstones and were absent from §2's list as first written.
   That list would therefore have produced a preservation table that
   silently omitted every combination involving a schedule variant —
   including GC × Adaptive, the most interesting one (I5).
2. **The delivery layer is dependent, not parallel.** `UniformBudget`
   and `RefsAccepted` range over `Delivery U`, not `U`, so they cannot
   be stated for a transformed universe without a transformed delivery.
3. **Nothing else turned up.** Modulo the two structural corrections,
   the surface really is closed: every hypothesis of every capstone
   audited is `U1`–`U6`, `D1`–`D3`, `S1`–`S3`, or arithmetic side
   conditions on `ℕ`. That is the fact the linear strategy rests on,
   and it is now evidence rather than hope.

The list is also the thing to *audit when a new arc is added*: an arc
that introduces a hypothesis outside it has, by that act, created a new
row in every future preservation table. §14 did exactly this with
`HonestNoEquiv`, which is why it is the one entry above with a single
consumer. The integration arc should treat "does this need a new named
invariant?" as a design question, not bookkeeping.

## 3. The strategy: preservation, not combination

### 3.1 Transformers × invariants

The core move. For each transformer `F` and each named invariant `I`,
prove one lemma:

    I U  →  I (F U)

Then any property `P` whose statement depends only on named invariants
transfers to `F U` **with no new proof**, and with no mention of `P`
anywhere. The pattern is already established — GC carries most of
its column, and this is why §9 reads as cleanly as it does.

**Layer U — universe transformers.**

| Invariant | `chop U G` | `skipFill` |
|:---|:---|:---|
| U1 DAG laws | ✅ (definitional) | ✅ SS1 (definitional) |
| U2 `Populated` | ✅ `populated_chop` | ✅ SS2 `skipFill_populatedOn` |
| U3 `SynchronisedOn` | ✅ **I4** `synchronisedOn_chop` | ⛔ **I5 — refuted**; ✅ above the fill |
| U4 `DoSValid` | ✅ `dosValid_chop` | **I1 — open** |
| U5 `HonestNoEquiv` | ✅ **I2** `honestNoEquiv_chop` | ✅ **I3** `honestNoEquiv_skipFill` |
| U6 verdicts | ✅ G3 `decided_chop` | ✅ SS5 `decided_fill` |

**Layer D — delivery transformers.** `chopD` supplies the whole
column; Safe Skip has no delivery transformer at all, so the entire
column is blocked behind constructing one:

| Invariant | `chopD D G` | Safe Skip |
|:---|:---|:---|
| — the transformer itself | ✅ `chopD` | **I6a — open, blocking** |
| D1 `Live` | ✅ `live_chopD` | I6b |
| D2 `DeliversQuorum` | ✅ `deliversQuorum_chopD` | I6c |
| D3 budgets | ✅ `byzBudget_chopD`, `refsAccepted_chopD` | I6d |

**Layer S — schedule variants.** Universe transformers do not touch
this layer, but both schedule variants do, and the table is nearly
empty:

| Invariant | `Slots.chop S G d` | `slotsOf hinj a` |
|:---|:---|:---|
| — the correspondences | ✅ `chop_slotRound`, `chop_leader` | ✅ `slotsOf_slotRound`, `slotsOf_leader` |
| S1 `FairScheduleOn`, `FairRunOn` | ✅ **I13** `fairScheduleOn_chop`, `fairRunOn_chop` | ✳︎ not a preservation fact |
| S2 `SpansEligible` | ✅ **I15** `spansEligible_chop` | ✅ `spansEligible_slotsOf` |

✳︎ The empty cell is the informative one. `slotsOf` sets
`leader := a`, so fairness of the induced instance is a statement about
the *assignment* and is not derivable from the base schedule's
fairness — an adaptive policy changes who leads, which is the entire
point of §13. There is no lemma to prove here; `PlacesRuns` (S3) *is*
the replacement, and seeing it arise this way explains its otherwise
peculiar shape: it quantifies over every verdict function the policy
might see, because no fact about the base schedule survives
reassignment. The contrast with `spansEligible_slotsOf` directly below
is the whole distinction — eligibility reads only `slotRound`, which
reassignment fixes, so *shape* transfers verbatim while *fairness*
cannot transfer at all.

### 3.2 The results

Nineteen results, all on Lean's three standard axioms. The index first,
the accounts after.

| | Result | Where |
|:---|:---|:---|
| I1 | honest non-equivocation survives truncation and the fill | `Preservation` |
| I2 | coverage survives truncation, at a horizon offset | `Preservation` |
| I3 | fairness and shape survive truncation | `ScheduleShape` |
| I4 | coverage is **refuted** under the fill; returns strictly above it | `Coverage` |
| I5 | horizon-stability, and epoch alignment | `Joiner` |
| I6 | anchor retention; the lag bounds the outage | `Retention` |
| I7 | the composition capstone | `Stack` |
| I8 | a severed chain cannot restart | `Retention` |
| I9 | the crash-prone lifecycle, and the hypothesis it forced | `Lifecycle` |
| I10 | re-genesis at the cut, needing no P3′ exemption | `ReGenesis` |
| I11 | local derivation converges; no agreement on the cut | `ReGenesis` |
| I12 | bootstrap, re-genesis and Safe Skip compose | `ReGenesis` |
| I13 | the exposure condition survives re-genesis; the fill enlarges cones | `ReGenesis`, `Exposure` |
| I14 | the fill disturbs exposure only at its own blocks | `Exposure` |
| I15 | a covered donor line reduces the check to reachability | `Exposure` |
| I16 | the delivery layer; the budget transfers, the discipline does not | `DeliveryFill` |
| I17 | the budget needs a donor, not the author | `Margin` |
| I18 | severance costs liveness margin: at most `f` at once | `Margin` |
| I19 | a common-core target makes the fill transmission-free | `CommonTarget` |

Two entries are **non-tasks** and are findings in their own right: the
adaptive layer needs no lemma relating it to the hybrid fault model,
because the crash class is invisible in verdicts; and `slotsOf` cannot
preserve fairness, because reassignment is what an adaptive policy is
for — `PlacesRuns` is the replacement, and seeing it arise that way
explains its shape.


Six cells are closed, all on the standard three axioms
(`LeanDag/Integration/`, witnessed in `LeanDagTest/Integration.lean`).

**I1 — honest non-equivocation survives both transformers**
(`honestNoEquiv_chop`, `honestNoEquiv_skipFill`). Together these are
what let §14's hybrid model be used inside §9's truncation and across
§12's fill: a hybrid universe stays a hybrid universe on both sides.
The fill's half is the same argument `skipFill`'s own
`no_equivocation` field makes for the derived correct class, run at the
wider honest class, and turns on the same clause — `hgap`, the crash
itself.

**I2 — coverage survives truncation** (`synchronisedOn_chop`), needing
only the horizon offset `R ≤ G + R'` and no base-layer exception. The
reason is structural and generalises (§3.3): coverage constrains a
block at chopped round `n + 1`, which lies above the cut by
construction, so `chop` retains its references and the original clause
applies unchanged.

**I4 — coverage under the fill, in three cases.** The division is the
result, and the middle case was found late.

*It fails* (`not_synchronisedOn_skipFill`) for a reliable set
containing the recovering validator, at that validator's gap rounds —
refuted in general rather than on data, because at every gap round of
every fill an old block at the round above fails to reference the
filled block below it. The `Ucrash` witness
(`ucrash_not_synchronisedOn`) exhibits the hypotheses satisfiable, so
the refutation is not vacuous.

*It is preserved* (`synchronisedOn_skipFill_of_notMem`) for any
reliable set excluding the recovering validator. The filled blocks are
that validator's alone, so a clause quantified over the others never
encounters them.

*It returns strictly above the fill*
(`synchronisedOn_skipFill_above`, requiring `sk.r < R'`), for any set.
The strictness is not slack: at the target round the lower block may
still be the last filled one, and the refutation reaches there too.

The refutation is the same fact that makes Safe Skip **safe**. SS3
concludes a filled candidate is always directly skipped *because no old
block references a fresh identifier*; coverage asks the opposite of
that reference. One fact, two consequences: the fill can manufacture
neither a commit nor coverage.

So the fill composes with §6's liveness account. What it cannot support
is the claim that a validator was covered at rounds during which it was
absent — which §12 does not make: §12 claims the fill restores
*production*, which is the hypothesis liveness consumes and which SS2
supplies. A recovering validator is outside the covered set for the
duration of its gap, and an ordinary participant from the round above
the fill onward.

**I3 — the schedule layer survives truncation**
(`fairScheduleOn_chop`, `fairRunOn_chop`, `spansEligible_chop`). A
joiner reasoning inside a truncation has a schedule that is fair and
spanning in its own right, which is what I5 needs.

**I6 — the lag bounds the recoverable outage.** Both directions.
`anchor_pruned` (I6a) states the constraint: a horizon past the crash
round prunes the anchor, so every `SkipMsg` over the truncation must
name a different one. `chopMsg` (I6b) shows it is the *only* constraint
— with the anchor retained the whole message rebases, every field
shifted by `−G`, and a validator that has already pruned can still
rejoin with one message.

One hypothesis appeared that the plan had not predicted: the horizon
must also lie below the *target* round (`G ≤ sk.r`), not only below the
anchor. It is needed where `k ≤ r − G` must give `G + k ≤ r`, which
truncated subtraction does not supply. In any non-degenerate
fill it is implied, but it is a real side condition and is stated
rather than assumed.

Composing with report §9's lag envelope makes it operational.
`outage_bounded_by_lag`: with the horizon trailing the recovery round
by `Λ`, the anchor survives *exactly* when the outage did not exceed
`Λ` —

> Garbage collection at lag `Λ` supports Safe Skip recovery from
> outages of up to `Λ` rounds, and no more.

Beyond it the validator's last block is gone — and the consequence is
sharper than "the fill fails".

**I8 — filling only the retained rounds is not a repair, and the
obstruction is P3′.** A filled block at the round above the cut needs a
`v1`-authored block *at* the cut to chain from, and a validator that
crashed below the horizon has none: a fill cannot start in mid-air.
Pushing on that yields a general fact
(`no_blocks_of_no_genesis`): a validator with no block in a universe's
genesis layer can produce nothing in it **at all**, because P3′ walks
every block down to genesis one round at a time. Truncation makes the
retained layer genesis, so `severed_of_pruned_anchor` concludes that a
validator whose whole history fell below the horizon has no block in
the truncation whatsoever.

So the failure is not Safe Skip's. **Any** attempt to resume is blocked,
because the validator's self-parent chain has been severed, and
rejoining would need a protocol provision the model does not have — a
re-genesis block. This also locates a cost of P3′ that report §2.2 does
not record: the clause is credited there for the DoS and
garbage-collection arcs and noted as unused by safety and liveness, but
it is what makes a pruned validator unrecoverable.

**I18 — and severance is a liveness cost, not only a storage one.**
A severed validator can still *read* after bootstrap, but it cannot
*produce*, and the reliable sets liveness quantifies over are defined
by production. So a severed validator belongs to none of them
(`notMem_of_no_blocks`), and since liveness needs a reliable set of
quorum size, at most `f` validators can be severed at once
(`card_severed_le`).

That reprices the horizon lag. It is set as a storage parameter — how
much history to retain — but it also fixes the window during which a
returning validator counts against the fault budget rather than towards
the quorum. A shorter lag saves disk and lengthens that window. The
trade-off is not visible from §9 alone, because §9 has no notion of a
validator that is present but unable to produce.

**I10 — and the provision needed is a single block**
(`Integration/ReGenesis.lean`).
The obvious repair is to let the stranded validator start a fresh chain
*at the cut*, with a block carrying no references. It needs no exemption
from P3′ at all: truncation rebases the retained layer to round `0`,
where P1, P3 and P3′ are guarded by `0 < round` and P2 is vacuous for an
empty reference set — which is exactly how `chop`'s own validity proof
discharges that layer ("no references, nothing to prove"). A re-genesis
block is indistinguishable, to the rules, from a block the cut
flattened.

`addGenesis` builds it and proves the extension a lawful universe, and
the non-equivocation obligation needs **no separate argument**: adding
a genesis
block would normally risk a twin at round `0`, but the very fact that
stranded the validator — its total absence from the truncation,
`severed_of_pruned_anchor` — is what makes the new block unambiguous.
`populatedOn_addGenesis` then puts the validator back in the genesis
layer, which is P8's hypothesis at round `0`, and an ordinary Safe Skip
anchored on the new block fills the rounds above.

**I11 — and the condition dissolves if the block is derived, not sent.**
§5.7's objection was that a re-genesis block is valid only to
validators who have pruned at least as far, which report §9's
per-validator horizons cannot guarantee. It applies to a *transmitted*
block. Let each validator instead **synthesise** a genesis for any
validator absent from its own retained layer, as a deterministic
function of its own horizon: nothing is sent, so nothing can be
rejected.

What that needs is that the local derivations converge, and they do,
cleanly. A validator's own derived genesis sits at round `0` and is
pruned by any further cut (`chop_addGenesis`), leaving exactly the
base a more-truncated validator already holds — `regenesis_converges`,
composing that with `chop_chop`. Both then derive the same genesis from
the same base. So a validator holding more history, on truncating
further, arrives at precisely what the later-cutoff validator had, and
heterogeneous horizons stay compatible with **no agreement on the
cut** — which is §9's design constraint, preserved rather than
traded away.

The statements are observational: identifier sets equal, and blocks
equal at those identifiers. The two universes differ only on junk
outside their identifier sets, which nothing reads.

**I12 — and the three mechanisms compose into one recovery.**
`recoveryMsg` puts them in sequence for a validator that crashed below
the horizon: bootstrap supplies the retained layer, re-genesis supplies
a block at the cut, and an ordinary `SkipMsg` anchored on that block
fills the rounds above. The result is a lawful universe in which the
validator produces again.

This is the answer to a question §12 could not pose. Safe Skip alone
covers outages up to the lag (I6); beyond it the anchor is gone and the
mechanism has nothing to attach to. The composite covers the rest, so
the two are **complementary rather than alternatives**: Safe Skip is
the cheap path when the anchor survives, and bootstrap with re-genesis
is the path when it does not. Neither subsumes the other, and the lag
is what divides them.

**I13 — re-genesis preserves the exposure condition, and the fill's
mechanism is its exact opposite.** The two recovery mechanisms come
apart here, for one structural reason.

`dosValid_addGenesis`: re-genesis adds a block with **no references**.
It therefore cannot cite an exposed author — the clause is vacuous for
it — and it enters no other block's cone, since nothing reaches what
nothing references. `DoSValid` is untouched in both directions, so §8's
per-cone bound applies to a re-genesised universe unchanged. Report
§2.2's worry that re-genesis severs the self-parent chain does not
apply at the condition level: what §8 forbids is *citing* an exposed
author, and a block citing nothing is safe by inspection.

The fill does the opposite, and `history_B1_subset_fill` is what §5.6
predicted: P3′ obliges `fillBlock` to insert a self
reference, so the first filled block **reaches the anchor**, and with
it the whole of `v1`'s pre-crash history. Its citations are inherited
unchanged from the donor, but its cone is strictly larger — and
`DoSValid` forbids citing an author exposed *in one's own cone*. A
citation innocuous in the donor's smaller cone can therefore be a
violation in the filled block's larger one.

So the same clause has opposite effects in the two arcs: P3′ is what
makes a cone a complete record of its author's acceptances, which is
what §8 relies on, and the self reference it obliges the fill to add is
exactly what enlarges the cone past what the donor vouched for, which
is what §12 must then handle. The
disturbance is nonetheless **local**, which is what I14 establishes.

A fill copies a donor block's references, which `DoSValid U` already
vouches for in the donor's cone; and it disturbs no *other* block,
because an old block's cone contains no filled block. Exposure at an
old block is unchanged in both directions (`exposedIn_skipFill_old`),
so `dosValid_skipFill` gives the extension the condition as soon as its
own blocks satisfy it.

The residual obligation is therefore local to the fill and
**checkable**: a recipient computes the fill and inspects it,
consulting no identity oracle and nothing beyond the message and its
own DAG. In report §8's vocabulary the condition is enforceable, so it
is admissible as a clause of the mechanism rather than an assumption
about the network — a fill whose enlarged cone exposes one of the
donor's citations fails the check and is refused, rather than accepted
and unsound.

**I15 — and the check reduces to reachability**
(`dosValid_skipFill_of_covered`). If each donor block already reaches
the anchor — which a donor line satisfies whenever it referenced `v1`'s
last block, the ordinary case since `v1` was producing at `r0` — then
the fill's cone adds nothing but `v1`'s own new blocks
(`fill_cone_subset`), and those cannot form an equivocating pair: they
sit at distinct rounds, `hgap` excludes an old `v1` block at any of
them, and `hB1uniq` pins the anchor's round. What is left is the
donor's own cone, for which `DoSValid U` already vouches. A recipient
therefore runs one reachability query per gap round and needs no
exposure computation over the extension.

One hypothesis is forced rather than chosen, and is worth stating for
what it reveals: `SkipMsg` records only that the anchor is `v1`'s
unique block *at its own round*, which leaves open that `v1`
equivocated before crashing — and the fill's self reference would then
cite an exposed author. Non-equivocation of `v1` throughout is what the
base model's correctness and report §14's honesty each supply, and it
is the second place (after I9) where weakening `hv1` to `hB1uniq`
required the missing strength to be named explicitly.

**I16 closes the delivery layer, with a modelling choice recorded
rather than settled.** `skipFillD` is the transformer, and it changes
nothing: a `Delivery` records what validators held when they built,
and nobody received the fill at the time. Its one obligation with
content is `includes` over the filled blocks, discharged by the
hypothesis that `v1` accepted nothing while down — the acceptance-side
counterpart of `hgap`.

The author-blind budget then transfers at the same constant
(`uniformBudget_skipFillD`), since every accepted block is old and
views and novelty are literally the same finite sets. The *reference
discipline* does not (`not_refsAccepted_skipFillD`), and the failure
describes Safe Skip rather than the transformer: `RefsAccepted` says a
validator cites only what reached it, and a fill cites the donor's
blocks, which the recovering validator did not receive. A retroactive
reconstruction cannot satisfy both under a delivery structure that
records what actually arrived.

Modelling recovery as acceptance *at recovery time* satisfies both by
construction, and concedes the budget instead — the novelty of the
newly accepted blocks becomes a property of the fill, checkable as in
I14/I15 rather than inherited. Which model is right is a question
about
what a `Delivery` is meant to record, and the arc records it rather
than settling it. Either way B4's storage bound transfers by the route
that model supports.

**I9 — a crash-prone validator can Safe Skip, once a hypothesis is
stated as the fact it stands for.** This is the composition that did
*not* fit, and the misfit is the finding. `SkipMsg` carried
`hv1 : v1 ∈ Correct`; the hybrid model splits `Correct` into honest and
available, and a crash-prone validator — precisely the one Safe Skip
serves — is honest but not correct. The structure could not describe
its own motivating case.

The hypothesis was stronger than its use. It appeared **once**, pinning
`v1`'s round-`r0` block to the anchor at the fill's boundary. §12 now
carries that fact directly (`hB1uniq`), with `hB1uniq_of_correct`
recovering the base model's route and `hB1uniq_of_crash` supplying the
hybrid one from `HonestNoEquiv`. Neither arc was wrong; one of them
stated a hypothesis in terms of a class the other splits, and finding
that is what an integration arc is for.

This is the arc's one modification to existing code, and it is a strict
weakening: every model that satisfied the old field satisfies the new
one, and the report's §12.1 now explains why the fact is stated rather
than the membership.

**A non-task, and that is the result.** The expectation was
a lemma relating `AdaptivePolicy` to `HybridFaults`. There is none, and
there cannot usefully be one: a policy reads verdicts, and the crash
class is invisible in verdicts. A halted validator's slot is skipped by
L5, whose hypothesis is that no block at the round carries the leader
as creator — which says nothing about *why* the leader is absent. A
crash-prone leader, a withholding Byzantine leader and a correct leader
that has not yet built are indistinguishable there, and a demoting
policy demotes all three alike. This joins `slotsOf`'s failure to
preserve fairness as the arc's second non-task, and
`lifecycle` composes L5, SS2 and I1 into one statement in which three
arcs meet without any of them mentioning another.

**I7 — the thesis holds: composition needs no new arguments.** The capstone
(`LeanDag/Integration/Stack.lean`) puts a validator on all four
mechanisms at once — recovered by Safe Skip, then truncated below a
horizon, read in the hybrid fault model, under an adaptive schedule —
and every proof is a chain of existing lemmas. Honest non-equivocation
survives the stack by I1 applied at each transformer in turn
(`honestNoEquiv_stack`, one line); coverage by I4's positive case then
I2, the two offsets composing exactly as their statements suggest;
production by SS2 then the truncation's
rebasing. The payoff is `hybrid_agree_stack`: **a validator that
recovered from a crash and then pruned still cannot disagree with
anyone about a verdict**, its proof being §14's agreement theorem
applied to a different universe with the one hypothesis discharged by
`honestNoEquiv_stack`. Nothing about the fill or the cut is re-proved.

Two things the capstone settled that the ingredients did not.

**Order matters, asymmetrically — and the deployment order is the free
one.** Fill-then-truncate is unconditional: `chop (skipFill U) G` is
well formed at every horizon, because the fill has already happened
when the cut is made. The reverse needs the anchor retained, since a
`SkipMsg` for `chop U G` requires `B1 ∈ (chop U G).ids`. So I6's
condition is real but appears here as an *asymmetry between orders*
rather than as an obstacle, and the unconditional order is the one
deployments actually take: fill the gap on recovery, prune later. §5.4
anticipated that the capstone might need I6 first; it does not, and
this is why.

**The schedule layer stacks with no compatibility lemma at all**
(`schedule_stack`).
`Slots.chop` and `slotsOf` are functions of a `Slots` instance and
nothing else, so the layer-S results hold for a validator running *any*
stack of universe transformers, with no compatibility lemma. That is
the clearest evidence for §2's layering: the composition matrix is
smaller than the arc count suggests because one of its three layers
does not interact with the others at all.

**I5 — a joiner can run the network's schedule, under two obligations**
(`LeanDag/Integration/Joiner.lean`). The question decomposed further
than expected, and the decomposition is the result.

The schedule half is *definitional*: truncating an adaptive schedule
and adapting a truncated one produce the same rounds and the same
leaders, `slotsChop_slotsOf` closing by `⟨rfl, rfl⟩`, provided the
assignment used inside the truncation is the original one shifted past
the base slot. No policy hypothesis is involved — all of I5's content
sits in whether a joiner can *produce* that shifted assignment.

That is `HorizonStable`, and it is the deployment obligation the arc
was looking for: the joiner's rule, run on the truncation with the
joiner's own slot numbering, must return what the network's policy
returns at the corresponding slot. Under it a joiner computes exactly
the leaders the network is using (`joiner_assign_agree`), so the two
run one schedule seen from two origins (`joiner_leader_agree`). The
obligation is stated on the *rule* rather than on a whole
`AdaptivePolicy`, because a policy is indexed by its `Slots` instance
and a joiner's policy therefore inhabits a different type from the
network's; the rule is the part that survives re-indexing, and the
leaders are what must agree.

A **second, independent obligation** surfaced from the run structure.
Horizon-stability aligns leaders; it does not align *epochs*. A
joiner's slot `k` is the network's `d + k`, so the epoch numberings
correspond only when the base slot is a whole number of epochs
(`epochOf_add_of_dvd`), and the example beneath it shows the
correspondence genuinely failing otherwise. So: **a garbage-collection
base slot must be a multiple of the adaptive epoch width.** Without
it two validators can agree on who leads every slot and still disagree
about which verdicts the policy was entitled to read.

The constant policy is horizon-stable only at `d = 0`
(`horizonStable_const_zero`), which is the informative degenerate
case: even a rule that ignores verdicts entirely must be *stated
relative to the reader's own slot numbering* to survive truncation.
Horizon-stability is not only about how far back a policy reads.

### 3.3 The constructions, witnessed

The house rule of report §16 applies with particular force to the
structures introduced here: `recoveryMsg` and `skipFillD` carry many
hypotheses, and clauses that cannot be met jointly make every theorem
above them vacuous. `LeanDagTest/Integration.lean` exhibits the
scenario they all describe — validator `3` of `Ucrash`, crashed after
its genesis block, severed by a horizon at round `1` — and builds the
re-genesis universe and the catch-up message over it by `decide`.

### 3.4 Transport heuristics

Three patterns emerged that should be applied to the remaining cells
before attempting them, because each predicts the shape of the answer:

**Quantify upward, transport cheaply.** A clause constraining a block
at round `n + 1` in terms of round `n` transports through truncation
without a base-layer exception, because the constrained block is above
the cut by construction (I2). A clause pinned at a fixed round needs
one (`supporters_chop`'s `1 ≤ m`). When a new invariant is added to
§2, its quantifier shape predicts its transport cost.

**Truncated subtraction is faithful only above the cut.** Paid three
times now — in I2, in `Slots.chop`'s `keyed` clause, and in I6 — and
discharged the same way each time: some hypothesis already in scope
pins the rounds above `G` (the `chop` filter; the base-slot condition
`G ≤ S.slotRound d`, carried upward by monotonicity in
`le_slotRound_add`). Expect every round-sensitive `chop` lemma to pay
it, and look for the pinning hypothesis rather than strengthening the
statement.

**Adding blocks is dangerous; removing them is not.** Truncation
restricts universally quantified invariants downward without further
hypotheses (I1, I2). Extension does not (I4), because an invariant of
the form "every block
here relates to every block there" acquires new obligations when new
blocks arrive — and `skipFill`'s new blocks are, by SS3's own argument,
exactly the ones nothing old can reference. **The heuristic predicted
the shape of I14 correctly**, and the prediction is recorded because
it held: the fill's cone is strictly larger than the donor's — it adds
`v1`'s chain below the anchor — and `DoSValid` forbids referencing an
author exposed *in one's own cone*, so a larger cone can only expose
more. Unconditional preservation is indeed false, and I14 supplies
exactly the hypothesis the heuristic named: a condition confining
equivocations in `v1`'s pre-crash history, which `hB1uniq` and `hgap`
together provide.

### 3.5 Transformers × transformers, and how the order question closed

The plan proposed proving a **commutation or normalization** result
once rather than checking every *order* of applying transformers. §9
already had `chop_chop`: two horizons compose, and the composite is the
coarser one. The mixed pair was the gap:

**`chop` and `skipFill` on their common domain.** If the anchor `B1` is
retained (`G ≤ round B1`), then truncating a filled universe and
filling a truncated one agree:

    chop (skipFill sk) G  ≃  skipFill (sk.chop G) G

with the fill's data re-indexed.

The side condition was correctly identified as the interesting content,
and it became I6: **Safe Skip requires its anchor to be above the
horizon.** A validator that crashes for longer than the
garbage-collection lag cannot Safe Skip back in — its last block has
been pruned — and must bootstrap and re-genesise instead (I8, I10).
`outage_bounded_by_lag` states it in both directions.

What the arc did *not* need was the commutation theorem itself. I7's
capstone showed the two orders are not symmetric and do not have to be:
fill-then-truncate is unconditional, truncate-then-fill needs the
anchor retained, and the unconditional order is the one deployments
take. A commutation result would have proved something true and
unnecessary. The heuristic that a normalization result saves work is
sound in general; here the asymmetry was cheaper to state and more
useful to know.

### 3.6 Layer variants: parametrize once, instantiate thrice

The schedule and fault layers should not be handled by preservation
lemmas but by **abstraction over the interface actually consumed**.

The evidence that this works is already in the development. §14
(hybrid) composes with the entire DAG layer at no cost in proof — not
through any composition theorem, but because `HybridFaults.toFaults`
places the
hybrid parameters into the *base* `Faults` interface, so every theorem
stated over an arbitrary `Faults` instance applies verbatim. Nothing
was proved to make that happen; the theorems were simply stated at the
right level of generality.

The same move is available, and not yet taken, for the adaptive layer.
§13.5 already observes the adaptive layer is rule-agnostic — but it
demonstrates this by *mirroring* the whole development onto Odontoceti,
a second copy of every definition and theorem. A third copy for Hybrid
is the obvious next step and the wrong one. Instead:

**The decision-relation interface.** Extract the three properties
the adaptive fixpoint actually consumes from its underlying rule:

1. a bounded decision relation with an agreement theorem
   (`DecidedWithin.agree`);
2. a congruence lemma — the relation reads `leader` only below its
   bound;
3. a committed-run descent producing bounded derivations.

Anything satisfying these three admits the adaptive construction. The
existing Mysticeti and Odontoceti mirrors become instances, the Hybrid
case follows without a third copy, and the report's §26.5 remark about
the one refactor the development declined ("a rule-parameterised
decision relation shared between §3.5 and §10.3") is finally
discharged — with three instances to justify it where two did not.

It is the most invasive item considered here — it touches existing
code rather than adding to it, which every other arc has avoided — and
it should be done as a *generalization with the old statements retained
as corollaries*, so nothing downstream breaks and the diff is
auditable. That is a refactor, and §4.2 moves it out of this arc
accordingly: I5 settled adaptive × GC without it, so no integration
result now depends on it. The analysis above is kept because it is the
specification that arc will need.

### 3.7 The four genuinely pairwise cells, as posed and as closed

Four combinations were not preservation facts and had to be proved
directly. All four are now closed, and the accounts below state each
question as it was originally posed, with the closing result named.
They are kept because in three of the four the answer differed in shape
from the question.

**GC × Adaptive: can a joiner recompute the schedule?** *(Closed by I5.
The question as posed:)* The
adaptive schedule at epoch `e` is a function of verdicts at epochs
`≤ e−2`. Garbage collection prunes history below a horizon. A
validator that joins from the truncation therefore may not hold the
verdicts the policy needs to compute the current schedule — and if it
computes a *different* schedule, §13's uniqueness theorem does not
apply to it, because uniqueness quantifies over runs of *one* policy
over *one* universe. This is the sharpest integration question in the
development, it has a deployment analogue (Hammerhead's schedule is
recomputed from committed sub-DAGs, which a pruned node lacks), and it
has a clean statement: the policy must be **horizon-stable** — its
output depends only on verdicts within the retained window —

        pick U v k = pick (chop U G) (v restricted above G) k

    and then a joiner's run agrees with a full-history run. A policy that
reads arbitrarily far back is a policy incompatible with garbage
collection, and saying so precisely is worth more than proving one
compatible instance.

*How it closed.* The schedule half proved to be definitional
(`slotsChop_slotsOf`, by `⟨rfl, rfl⟩`), and all the content moved into
whether a joiner can produce the shifted assignment. That is
horizon-stability, and a **second** obligation the question had not
anticipated came with it: the garbage-collection base slot must be a
multiple of the adaptive epoch width, or two validators can agree on
every leader and still disagree about which verdicts the policy was
entitled to read.

**Hybrid × Safe Skip: the natural pairing.** *(Closed by I9.)* The
hybrid model names a *crash-prone* class; Safe Skip is the recovery
mechanism for a crashed validator. That these two were built separately
is an accident of order. The composite statement — a crash-prone
validator's fill, verified at hybrid thresholds, restoring it to the
correct class — was expected to follow from honest non-equivocation
plus restating §12's theorems over `HybridFaults`.

*How it closed.* It did not follow, and that is the finding. §12's
`hv1 : v1 ∈ Correct` excluded the crash-prone validator the pairing is
about, so the composite was unstatable before the hypothesis was
weakened to the fact it stood for (`hB1uniq`). The expectation that
this cell would be routine was the arc's largest single misjudgement.

**Hybrid × Adaptive: demotion of the crash class.** *(Closed as a
non-task; see §3.2.)* The demote-on-skip policy of §13.6 removes a
crashed validator from the leader rotation, and the hybrid model is
where "crashed" is a named class. The full lifecycle — demoted while
down, safe-skipped back in, re-promoted after recovery — was expected
to need a lemma relating the two.

*How it closed.* There is no such lemma and there cannot usefully be
one: a policy reads verdicts, and the crash class is invisible in
verdicts. The lifecycle theorem exists (`lifecycle`) and is exactly as
strong as hoped, but it composes three arcs none of which mentions
another.

**DoS × Safe Skip.** *(Closed by I14, I15, I16, I17 and I19 — the cell
that expanded most.)* Two questions, separated by the analysis of §5.6.
At the universe layer, whether the fill preserves `DoSValid` — expected
conditional rather than preserved, since the fill's cone is strictly
larger than the donor's. At the delivery layer, whether a bulk fill
respects the novelty budget.

*How it closed.* The universe-layer expectation was right, and the
condition proved **enforceable** rather than assumed: a
recipient computes the fill and inspects it (I14), and against a donor
line that already reaches the anchor the check reduces to one
reachability query per gap round (I15). The delivery layer needed a
transformer built first (I16), after which the budget transferred with
no arithmetic; the reference discipline did not, and that failure
describes Safe Skip rather than the transformer. The residual worries —
which discipline the specification should state, and whether the
recovering validator can serve what it cites — were then removed
together by I17 and I19 rather than resolved. This cell was recorded as
the most likely to stay open, and it produced five results.

## 4. Status, and what is left

| Module | Contents | Status |
|:---|:---|:---|
| `Integration/Preservation.lean` | honest non-equivocation under both transformers; coverage under truncation | **done** |
| `Integration/Coverage.lean` | coverage refuted under the fill, recovered strictly above it | **done** |
| `Integration/ScheduleShape.lean` | fairness and shape under `Slots.chop` | **done** |
| `Integration/Joiner.lean` | the transformers commute; horizon-stability; epoch alignment | **done** |
| `Integration/Retention.lean` | anchor retention; the outage bound; the severed chain | **done** |
| `Integration/ReGenesis.lean` | re-genesis; convergence; the exposure condition; the composite recovery | **done** |
| `Integration/Stack.lean` | the composition capstone | **done** |
| `Integration/Lifecycle.lean` | the crash-prone lifecycle | **done** |
| `Integration/Exposure.lean` | cone growth; the enforceable check; its reachability form | **done** |
| `Integration/DeliveryFill.lean` | the delivery transformer; the budgets over it | **done** |
| `LeanDagTest/Integration.lean` | the refutation witnessed; the constructions exhibited | **done** |
| — | the decision-relation interface (§3.6) | **moved out**, §4.2 |

### 4.1 The three kinds of result the arc produced

Three kinds of result appeared, and only the first was planned:

1. **Preservation lemmas** — the planned kind, and the cheapest. Each
   closes a column of the composition matrix.
2. **Refutations with exact boundaries** — coverage under the fill, the
   severed chain, the reference discipline under the fill's delivery.
   Each is worth more than the corresponding positive would have been,
   because each names a constraint no single arc can see.
3. **Placement and enforceability conditions** — where a horizon may
   fall (epoch alignment, horizon-stability, anchor retention), and
   what a recipient must check to accept a fill. These were not in the
   plan at all, and they are the arc's most directly usable output,
   being engineering guidance rather than proof plumbing.

The composition capstone is not a fourth kind but the payoff of the
first: it is the proof that the preservation lemmas *compose*, which is
what makes collecting them worthwhile rather than merely tidy.

### 4.2 What the arc is not

**The decision-relation interface (§3.6) is out of scope.** It was
included on the reasoning that Hybrid should become a third instance of
the adaptive layer rather than a third copy. That is still worth doing,
but the joiner result settled adaptive × GC without it, so nothing here
depends on it — and it is a *refactor*, restructuring working code for
elegance. It belongs in its own arc, with the old statements retained
as corollaries.

The rule this arc followed is not "adds versus modifies". One
composition required modifying report §12 — weakening `hv1` to
`hB1uniq` — because the composition was **unstatable** otherwise. That
is a different act from a refactor: a hypothesis weakening forced by a
theorem one wants to state, strictly conservative, one field and one
proof line. *Modify existing code only when a result cannot otherwise
be stated, never for elegance.*

### 4.3 Loose ends

Four, none of which blocks the arc's claims.

**A modelling choice, now known to matter for neither the bound nor,
against a common-core target, for availability (§3.2's I19).**
Whether a `Delivery` records what arrived over the network or what a
recovering validator accepts at recovery time decides which of report
§8.4's two clauses the fill satisfies (§3.2). The conjecture that this
does not affect the *bound* is now proved: `card_novelty_le_of_donor`
shows the novelty budget holds for a block whose references lie inside
**any** correct validator's acceptances — its author's or not —
provided that validator has a block at the round, which a donor line
does at every gap round. Both component lemmas were already stated at
the right generality; composing them at a `w` other than the author is
what had not been done.

So the discipline is stated more tightly than the storage bound
requires, and the fill is the case that exhibits the difference.

**And the residual question dissolves once the target is drawn from the
common core.** What the storage argument leaves untouched is
availability: a validator citing blocks it does not hold cannot serve
them. Report §5.2's T3c produces at every round — under no assumption
whatever — a correct-authored block that every block two rounds later
reaches, so its references lie in the causal past of every validator
holding a block two rounds up (`fill_refs_available`). A fill built
against such a line therefore cites only material its recipients
already have: nothing needs transmitting, the recovering validator
holds what it cites once bootstrapped, and both candidate clauses are
satisfied. What was a specification choice becomes a choice the
mechanism can make for itself, by picking its target well.

**One deliberate omission.** The arc proves nothing about *executions*:
the order in which mechanisms fire, or whether a validator's local
sequence of bootstrap, re-genesis and fill is realisable in time. That
is outside the model by report §1.4, as it is for every other arc.

## 5. Risks and predictions

**5.1 The negative results were the valuable ones, as expected.** The
prediction held throughout, and in more places than were listed.
Settled negative: coverage under the fill, the two non-tasks, the
severed chain, and the reference discipline under the fill's
delivery — each naming a constraint no single arc could see. Settled
*conditional* rather than negative: anchor retention, horizon-stability
and the exposure condition, where in each case the condition was the
deliverable.

I4 set the template the rest followed: refute in general where
possible, keep a witness so the refutation is seen to be non-vacuous,
and state
the positive form that survives — the boundary is the result, not the
failure. The one methodological correction is that "negative" was too
narrow a category. Three of this arc's most useful outputs (the lag
bound, horizon-stability, epoch alignment) are neither positive nor
negative but *conditions*, and §4.1 names that as the third kind of
result the plan had not anticipated.

**5.2 The interface audit is done, and it moved the plan.** This risk
was live while §2's list was still a survey rather than a
verified fact. It has now been checked mechanically against the
extracted statements of thirteen capstones (§2.4), and it was
*wrong in two structural ways* — the schedule layer was missing
entirely, and the delivery layer is universe-indexed rather than
parallel. Both corrections are folded in above; the residual risk is
that the audit covered capstones rather than every theorem, so an
intermediate lemma could still consume something unlisted. That is
cheap to re-check as the arc proceeds and should be re-run whenever a
new preservation lemma needs a hypothesis not in §2.

**5.3 The DoS accounting survives a bulk fill, and the risk was
correctly located.** The concern was that §8's novelty budget limits
the rate at which an author can inject material while Safe Skip injects
one block per gap round in a single message, and that the *acceptance*
side (`RefsAccepted`) might see a burst.

Both halves were right. The budget itself transfers with no arithmetic
once the delivery transformer exists (I16), because the fill produces
exactly one block per round and every accepted block is old. The
acceptance side is where it fails, exactly as predicted — and the
failure is `RefsAccepted`, exactly the clause named. What the risk
register did not anticipate is that the failure would be a *description
of Safe Skip* rather than a defect: a retroactive reconstruction cannot
satisfy a clause saying a validator cites only what reached it. Nor
that the residual question would then be removed by I17 and I19 rather
than answered.

The prediction that this cell needed a genuinely new argument rather
than a preservation lemma held, and it was the correct place to expect
one.

**5.4 The composition capstone chained cleanly, in one order.** This
risk is discharged (§3.2). The second half of it was right: the
invariants compose in one order and not obviously the other. But the
order that works — fill, then truncate — is the deployment
order, so the capstone (I7) needed no hypothesis `chop`'s statement
does not already carry, and the commutation result of §3.5 was not a
prerequisite after all. Truncate-then-fill has since been proved
outright (I6b) under the retention condition the asymmetry predicted,
so both composition orders are now settled.

**5.5 Scope discipline.** The temptation in an integration arc is to
prove the full cross product because each individual proof is easy once
the interface exists. That would defeat the purpose. The rule for this
arc: **a combination gets its own theorem only if it has content that
the preservation lemmas do not already imply.** Everything else is a
one-line corollary at most, and more often simply an observation in the
report that the composition is immediate.

**5.6 `DoSValid` under the fill was conditional, as predicted.** The
mechanism was stated before the attempt and held: a filled block's cone
is the donor's *plus* `v1`'s chain below the anchor, since `fillBlock`
inserts the self reference, and `DoSValid` forbids citing an author
exposed in one's own cone — so a larger cone can only expose more,
while the citations are inherited unchanged.

What was not anticipated is how *well* it resolves. The disturbance is
local to the fill's own blocks, so the residual obligation is checkable
by a recipient (§3.2), and under the ordinary condition that the donor
line already covers the anchor it reduces to a reachability test. The
prediction was right about the failure and wrong about its cost.

**5.7 Re-genesis looked like it needed agreement on the cut, and does
not.** The objection recorded here was that a re-genesis block is valid
only to validators who have pruned at least as far, which report §9's
per-validator horizons cannot guarantee — so the provision appeared to
require the one thing §9 is designed to avoid.

It dissolved rather than being answered, and I11 is the resolution:
the objection applies to a *transmitted* block, and the block need not
be transmitted. Each validator synthesises a genesis for any validator
absent from its own retained layer, and the local derivations converge
under further truncation. Nothing is sent, so nothing can be rejected,
and heterogeneous horizons stay compatible.

The methodological point is the one §5.1 makes: the useful move was to
find the *weakest form of the mechanism* that avoids the obstacle, not
to prove the obstacle surmountable.

## 6. Out of scope

- **Executions.** Composition here is composition of structural
  conditions, not of protocol executions; nothing about the *order* in
  which mechanisms fire is modelled, and nothing can be, in a model
  with no traces (§1.4).
- **Reactive × everything.** The reactive schedule (§11) is a timing
  refinement below the `SynchronisedOn`/`Populated` interface, so it
  composes with the structural arcs trivially — it produces the same
  interface by a different route. Nothing to prove; worth one sentence
  in the report.
- **The certified variant, and cryptography** — outside the model, as
  in every other arc.
