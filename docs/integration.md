# lean-dag — Integration: the mechanisms at every rule, and what the properties do not say

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

`LeanDag/Integration/` is where the mechanisms of this development —
garbage collection, crash recovery, re-genesis, adaptive leaders — meet
each commit rule and one another. Two kinds of file live there, and the
distinction is the point of this document.

The first kind is a **mechanism cell**: a rule's own cut or fill, built
on the shared data, with the witness that puts it in the relation the
properties read, and the generic theorem applied. Nothing about verdicts
is proved in these files; that is done once, in `LeanDag/Properties/`,
and `docs/target-properties.md` (its opening part) is the current
statement of what a rule shows and what it gets. The composition of
mechanisms with one another is the same story: `Stack.safe_and_live`
reads any sequence of them as one, and the headlines `Properties.Safe`
and `Support.Lives` are what a rule instantiates.

The second kind is a **standing fact about a mechanism** that no
property states, because it is not about verdicts: whether coverage
survives a fill, where a horizon may be put, what a severed validator
can do, what a fill does to the exposure condition and the storage
budgets. Those are the I-labelled results, and they are collected in
§3 with the deployment conditions they yield.

## 1. The composition method, in one paragraph

A mechanism that transforms the DAG delivers one relation between the
universe it reads and the one it writes — `Properties.RebasedAbove`: the
same blocks at and above a settling round, at rounds `G` apart, with the
same authors and, strictly above, the same references. A cut is that
relation at settling round `G` with a rebase of the schedule
(`Truncates`); a fill or a re-genesis is it at no offset, settling at the
top of the gap (`Sustains`); an extension proper is the stronger
`Extends`. Verdicts cross a `Truncates` by `LocalTruncate.of_banded` and
an `Extends` by `Persist.of_banded`, both derived from the rule's
`Banded`; the liveness precondition `Support.live` crosses either from
the support's `Local` law. A `Stack` is a finite sequence of such steps
and is itself one step (`Stack.rebased`), which is the composition
theorem. A mechanism therefore owes a *witness* and nothing else, and
what the files below contain is witnesses.

## 2. The mechanism cells

Every universe is the block record (`BlockRecord.lean`) at the rule's
validity predicate, and the cut, the fill and re-genesis are built once
at the record (`Record/`). A rule's predicate has the four facts its
predicate owes (`Validity.Mechanised`) and, if it does not read the
author, the copy fill's validity (`CopyStable`), both inherited along
its equivalence with the validity family `ValidAt` at the rule's
threshold and clause (`Mechanised.of_iff`); a carrier read as records
(`DagRule.OnRecord`, `Properties/Record.lean`) then has every witness
the properties read. The core, Nemo, FinWhale and Hydrozoan are records
by definition, Hydrozoan's block being the shared block with no payload. Rules on the
core's `BlockUniverse` (the core, Odontoceti, Mahi-Mahi) take the core's
`chop` and `skipFill` directly.

**Each witness sits with its protocol.** A `<Protocol>/Record.lean`
holds the one instance saying that protocol's universe is a block
record, in the same namespace as its carrier and under the same name,
`onRecord`. `Integration/` keeps what needs two arcs at once: a schedule
over a rule, or mechanisms composed with one another.

| file | rule | instance | constructions |
|---|---|---|---|
| `Mysticeti/Record.lean` | core | `MysticetiProperties.onRecord`, identity maps | the core's `chop`, `skipFill`, `addGenesis`, and the cut's `Truncates` witness |
| `Odontoceti/Record.lean` | Odontoceti | `OdontocetiProperties.onRecord`, identity maps | the core's, through it |
| `MahiMahi/Record.lean` | Mahi-Mahi | `MahiMahiProperties.onRecord`, identity maps | the core's, through it |
| `Nemo/Record.lean` | Nemo | `NemoProperties.onRecord`, identity maps | the record's, through `NemoProperties.onRecord` |
| `FinWhale/Record.lean` | FinWhale | `FinWhaleProperties.onRecord`, identity maps | the record's, through `FinWhaleProperties.onRecord` |
| `Hybrid/Record.lean` | Orcaella | `HybridProperties.onRecord`, under `HonestNoEquiv` | `HybridProperties.fill` (the self-referencing fill with `honestNoEquiv_fill`); the prompt skip `HybridProperties.decided_none_fresh` |
| `HydrozoanMechanisms.lean` | Hydrozoan | `Hydrozoan.onRecord`, identity maps | the record's own; `decided_none_fresh_hz`; the coverage refutation |
| `OptimalHydrozoan/Record.lean` | Optimal-Hydrozoan | `OptimalHydrozoanProperties.onRecord`, under `BlockRecord.Any` (leader exclusion is a validity clause, preserved automatically) | the record's, through `OptimalHydrozoanProperties.onRecord` |
| `ReactiveMechanisms.lean` | reactive Mysticeti | — | `live_chop_reactive`, `live_skipFill_reactive`, `live_addGenesis_reactive`, `decidedBelow_of_run_chop_reactive`: the reactive precondition across each mechanism, through `coreSupport` |
| `StackRules.lean` | core, Nemo, FinWhale | — | `stack_core`, `stack_nemo`, `stack_finwhale`: fill then cut as a `Stack`; the headline `Properties.Safe` reads any of them |
| `AdaptiveHydrozoan.lean`, `AdaptiveReactive.lean` | Hydrozoan; reactive Mysticeti | — | the adaptive leader mechanism (`Adaptive.run_agree`, `run_exists`) at those rules' properties |

Every witness (`truncates_chop`, `sustains_chop`, `extends_fill`,
`sustains_fill`, `extends_addGenesis`, `sustains_addGenesis`) and every
verdict cell (`decided_chop_iff`, `decided_agree_chop`, `decided_fill`,
`decided_agree_fill`, `decided_addGenesis`, `decided_agree_addGenesis`)
is a theorem of `DagRule.OnRecord` (`Properties/Record.lean`,
`Properties/Arcs/Record.lean`), so a row's instance is the whole of its
cell; `audit-mechanisms.py` reads an instance as the cut, fill and
re-genesis cells collected.

The Hydrozoan and Optimal cells are described in more detail in
`docs/hydrozoan-integration.md`. What every row has in common: the
instance is a dozen `rfl`s, the constructions are one line each, and
the file proves nothing about the rule's decision relation.

Orcaella carries one invariant that is not a property, and shows it
survives the cut, the copy fill and re-genesis once
(`Invariant.Mechanised`). Honest non-equivocation survives because the
cut removes blocks, any fill adds blocks only at gap rounds the crash
left empty, and re-genesis adds a block by an author with none.
Optimal-Hydrozoan carries no such invariant: leader exclusion is a
clause of its validity (`ValidOpt`) rather than a separate predicate,
so `OptimalHydrozoanProperties.onRecord` reads it under the trivial invariant `BlockRecord.Any`
and every mechanism preserves it clause by clause, with nothing
proved per mechanism.

## 3. What the properties do not state

Everything below is a fact about a mechanism, not about a rule, and no
property reaches it. The labels are the report's (§16.3–§16.7).

### 3.1 Coverage under the fill (`Coverage.lean`, `Timed/Extension.lean`)

Coverage behaves in three ways under a fill, and each is a theorem at
the relation the fill delivers. It **fails** for any reliable set that
holds the author of a novel block, at that block's round: an old
reliable block one round up references no novel identifier
(`Timed.not_synchronisedOn_of_extends`, at any rule's `Extends`). This
needs nothing beyond what makes a fill worth doing, and it is the same
fact that makes the fill safe: no old block references a new id, so
the fill can manufacture neither a commit nor coverage. It is
**preserved** for any reliable set holding no novel author
(`Timed.synchronisedOn_of_extends`), and it **returns** strictly above
the settling round for any set (`Timed.synchronisedOn_of_rebased`, at
the `Sustains` witness). The core reads all three at Safe Skip
(`not_synchronisedOn_skipFill`, I4, `synchronisedOn_skipFill_of_notMem`,
`synchronisedOn_skipFill_above`) and the cut at a horizon offset
(`synchronisedOn_chop`, I2); Hydrozoan reads the refutation at its copy
fill (`not_synchronisedOn_copyFill_hz`).

What the fill restores is *production*, which is what liveness reads,
and a recovering validator is outside every covered set for the
duration of its gap.

### 3.2 Where a horizon may be put (`Joiner.lean`, `Adaptive/Joiner.lean`, `Retention.lean`)

**The joiner** (I5, `Adaptive/Joiner.lean`). A validator joining from a
cut under an adaptive schedule computes the same leaders as the network
exactly when the policy's rule is horizon-stable
(`Adaptive.HorizonStable`, `Adaptive.joiner_assign_agree`), and its verdicts
agree with the network's by cross-rebase agreement at the adaptive
schedule (`Adaptive.joiner_run_decided_agree`, from `Agree` and
`Banded`). Rebasing a schedule commutes with installing a shifted
assignment (`Rebases.slotsOf`), so any rule's cut is a cut at the
adaptive schedule (`Truncates.slotsOf`); the core's `Joiner.lean` is
these at `truncates_chop`, where the two constructions are equal by
`rfl` (`slotsChop_slotsOf_eq`). Epochs align only when the base slot is
a multiple of the epoch width (`epochOf_add_of_dvd`): **a
garbage-collection base slot must be a multiple of the adaptive epoch
width.**

**The anchor** (I6, I8). A recovery message needs its anchor retained,
and `chop` retains it exactly when the horizon has not passed the crash
round (`anchor_pruned`); with the anchor retained the whole message
rebases (`chopMsg`). Composed with the lag: **garbage collection at lag
`Λ` supports recovery from outages of up to `Λ` rounds and no more**
(`outage_bounded_by_lag`). Past that, a validator with no block in the
retained layer can produce nothing at all (`no_blocks_of_no_genesis`,
`severed_of_pruned_anchor`): P3′ walks every block down to genesis.

### 3.3 Re-genesis (`ReGenesis.lean`)

A severed validator restarts with a fresh chain at the cut. `addGenesis`
adds a reference-free block at round `0`; the truncation's base layer is
already such a layer, so the block needs no exemption from P3′ and is
unambiguous because the absence that stranded the validator is total
(I10). Verdicts survive it by `Persist` (`decided_addGenesis`), and the
validator is back in the genesis layer (`populatedOn_addGenesis`).
Heterogeneous horizons need no agreement: a validator's derived genesis
is pruned by any further cut, leaving exactly the base a more-truncated
validator holds (`regenesis_converges`, I11), and re-genesis is forced
rather than chosen — any block returning an absent validator to
production is such a block (`genesis_forced`). Bootstrap, re-genesis and
Safe Skip then compose into a full recovery (`recoveryMsg`,
`hB1uniq_of_addGenesis`, I12), the absence that licensed re-genesis
discharging both of the recovery message's crash clauses. Re-genesis
preserves the exposure condition (`dosValid_addGenesis`, I13), since a
block with no references cites nobody.

### 3.4 The exposure condition under the fill (`Exposure.lean`)

The fill's self reference makes a filled block's cone strictly larger
than the donor's (`history_B1_subset_fill`), so a citation innocuous in
the donor's cone can be a violation in the filled block's. The
disturbance is local: exposure at an old block is unchanged
(`exposedIn_skipFill_old`), and the condition decomposes into the old
universe's plus a clause on the fill's own blocks (`dosValid_skipFill`,
I14), which a recipient checks by computing the fill. When each donor
block already reaches the anchor the check reduces to reachability
(`dosValid_skipFill_of_covered`, I15), because the fill's cone then adds
only the recovering validator's own blocks (`fill_cone_subset`).

### 3.5 Storage under the fill (`DeliveryFill.lean`, `Margin.lean`, `CommonTarget.lean`)

The fill's delivery layer changes nothing, since nobody received the
fill at the time (`skipFillD`, `viewUpto_skipFillD`), so the author-blind
budget transfers at the same constant (`uniformBudget_skipFillD`, I16);
the reference discipline does not (`not_refsAccepted_skipFillD`),
because a filled block cites what the recovering validator never
accepted. The budget needs a donor, not the author
(`card_novelty_le_of_donor`, I17), so the storage bound holds whichever
clause a deployment states. A severed validator is a reader and not a
producer, so it belongs to no reliable set (`notMem_of_no_blocks`) and
at most `f` may be severed at once (`card_severed_le`, I18): **the
horizon lag is a liveness-margin parameter.** A donor line drawn from
the common core cites only what every recipient holds
(`exists_commonAt`, `fill_refs_available`, I19), so the message carries
nothing but the target's name.

`Preservation.lean` holds the one invariant of a carrier that is not a
property: Orcaella's `HonestNoEquiv` survives the cut and the fill
(`honestNoEquiv_chop`, `honestNoEquiv_skipFill`, I1), which is what lets
`Hybrid/Record.lean` build its universes.

## 4. Conditions for a deployment

Read off §3, these are the constraints a deployment of several
mechanisms must respect; none is visible from a single mechanism.

- Garbage collection at lag `Λ` bounds the outage a one-message
  recovery can span to `Λ` rounds; beyond it the validator re-genesises
  and catches up from the cut.
- A garbage-collection base slot under an adaptive schedule must fall
  on an epoch boundary, and the policy's rule must be horizon-stable.
- A fill is checked before it is accepted: its own blocks must satisfy
  the exposure condition, which reduces to one reachability query per
  gap round when the donor line reaches the anchor.
- Draw the donor line from the common core, so the message names its
  target and every recipient reconstructs the fill.
- A validator pruned past its own history counts against the fault
  budget until it re-genesises; at most `f` may be in that state.

## 5. Witnesses and audits

The standing facts are exercised on data in `LeanDagTest/Integration/Model.lean`:
the coverage refutation on the crash
family, retention and the outage bound, re-genesis and its convergence,
the exposure check. The mechanism cells are checked by the build and by
`scripts/audit-mechanisms.py`, which reads the dependency graph and
prints, for every rule, which cells exist; `scripts/audit-bespoke.py`
checks that no cell reaches a rule's verdicts except through its
properties. Both run in CI and exit nonzero on a gap.
