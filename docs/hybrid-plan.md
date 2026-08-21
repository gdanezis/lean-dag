# lean-dag — Hybrid fault tolerance: plan

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **hybrid** arc, written
before the development. The subject is the hybrid fault model for
two-round DAG consensus (arXiv:2607.04789; the working notes are
`hybrid.md`), an extension of the two-round rule: a fault model distinguishing `f` Byzantine validators
(may equivocate) from `c` crash-prone validators (honest, may halt,
never equivocate), with the claimed tight bound

    n = 5f + 3c + 1,   q = 4f + 2c + 1,   k = 2f + c + 1

for committee size, direct threshold and indirect threshold. The goal
is machine-checked safety and liveness of the two-round commit rule
under this model, at the generalized bound `n ≥ 5f + 3c + 1`, collapsing
onto the existing Odontoceti development at `c = 0`. Results will carry
**H**-labels; everything will live in `LeanDag/Hybrid/` with `decide`
witnesses in `LeanDagTest/Hybrid.lean`, consuming the core read-only.

The DAG theorems below do not depend on checkpoint signatures. The
additive `Hybrid/Checkpoint/` subarc is a separate assume-guarantee
model: it takes possibly forked per-validator histories and messages as
execution input, then proves resilient finality safety and
highest-checkpoint recovery. It neither derives AbC-induced forks from
the DAG nor composes these checkpoint results with the DAG proofs.

## 1. What the hybrid model splits

In the base development one set does two jobs. `Correct` — the
complement of the Byzantine set — is simultaneously the population that
does not equivocate (P5 binds its creators) and the population liveness
may rely on (the reliable set `T` is drawn from it). The hybrid model
splits the two roles:

- **Honest** (`n − f` validators): do not equivocate. Crash-prone
  validators are honest — a block they produce is one block, identical
  to all recipients. This is the population the *safety* counting
  discounts against.
- **Correct** (`≥ n − f − c`): honest *and* available. This is the
  population *liveness* may rely on — a crash-prone validator's blocks
  may simply stop.

Two observations make the arc smaller than it first appears.

**Crashing is invisible to a structural model.** The object of study is
a DAG with invariants, not a transition system: "halts at time `t`"
cannot even be expressed. A crash manifests entirely as *absence* —
the validator's blocks stop appearing, so production (`PopulatedOn`)
cannot be promised for it. Consequently the crash class needs **no new
behavioural clause at all**: it enters only through (a) the extension
of non-equivocation to crash-prone creators and (b) the cardinality
arithmetic. The `T`-relativised liveness interface — coverage and
production over an arbitrary reliable `T ⊆ Correct` with a card
hypothesis — was built for exactly this shape of exclusion, and is
consumed unchanged.

**The derived-instance trick.** Instantiating the *base* fault
structure with the union class —

    F' : Faults Validator,   F'.byzantine := byzantine ∪ crash,   F'.f := f + c

— makes the base quorum `n − F'.f` equal to `q = n − f − c` on the
nose. Every quorum-shaped clause of the DAG layer — reference validity
P3, views, `blocksAt`/`creatorsOf`, the whole counting vocabulary —
then instantiates verbatim at the hybrid quorum, and `n ≥ 5f + 3c + 1`
implies `n ≥ 3F'.f + 1`, so the instance is lawful. What the derived
instance gets *wrong* is exactly one clause: its `no_equivocation`
binds only `Correct = univ \ (byzantine ∪ crash)`, and the hybrid
safety counting needs it over the larger `Honest`. That one clause is
the genuinely new assumption of the arc.

## 2. The model

```lean
class HybridFaults (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] where
  fb : ℕ                        -- Byzantine bound
  fc : ℕ                        -- crash bound
  byzantine : Finset Validator
  crash : Finset Validator
  disjoint : Disjoint byzantine crash
  card_byzantine : byzantine.card ≤ fb
  card_crash : crash.card ≤ fc
  card_validators : 5 * fb + 3 * fc + 1 ≤ Fintype.card Validator
```

with `Honest := univ \ byzantine` and the derived base instance
`toFaults : Faults Validator` at `byzantine ∪ crash` (so the derived
`Correct` is the fully-correct class, which is what both the views and
the liveness interface should mean by it). The derived instance will be
a `def` promoted locally, not a global `instance` — the arc must not
change which `Faults` other developments resolve.

The strengthened equivocation clause is a universe-level condition,
threaded as a hypothesis the way `DoSValid` is, rather than baked into
a new universe structure:

```lean
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator ∉ HybridFaults.byzantine →
    (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → U.block i = U.block j
```

(P5 for the derived instance follows from it, `Correct ⊆ Honest`, so a
universe carrying `HonestNoEquiv` is not doubly constrained.) Its
enforceability reading belongs in the eventual report section: that
crash-prone validators do not equivocate is a clause of the *fault
model* — the honesty of a class, like the Byzantine bound itself — not
conduct the protocol enforces.

**Thresholds, `n`-relative.** The development will not fix
`k := 2f + c + 1`; it will mirror the house treatment of Odontoceti,
which generalized the thesis's `2f + 1` to `n − 3f`. Set

    q := n − fb − fc        (the derived instance's quorum, with no new proof)
    k := n − 3·fb − 2·fc

Then both constraints of `hybrid.md` §4 collapse into the class bound:

- *indirect safety* `q + k > n + fb` ⟺ `n ≥ 5fb + 3fc + 1`;
- *link integrity* `2q − n − fb ≥ k` holds with **equality** — the
  choice of `k` is exactly the support count a valid anchor is forced
  to carry, as `n − 3f` was in the pure-Byzantine case.

At the tight committee `n = 5fb + 3fc + 1` this `k` is `2fb + fc + 1`,
recovering `hybrid.md`'s constant; at `c = 0` both thresholds are
Odontoceti's, which is what makes conservativity (§4, H8) definitional
rather than a theorem with content.

At general `n` the two candidate thresholds diverge, and *any* `k` in

    2fb + fc + 1  ≤  k  ≤  n − 3fb − 2fc

is admissible: the lower end is what the skip-side conflicts need
(`q + k > n + fb`), the upper end is what link integrity supplies
(`2q − n − fb ≥ k`), and the interval is nonempty exactly when
`n ≥ 5fb + 3fc + 1` — the class bound *is* the existence of a working
threshold. The development will therefore prove the rule theorems over
an abstract `k` carrying the two interval inequalities as hypotheses,
with `hybrid.md`'s constant and the `n`-relative choice as the two
named instantiations. The bound itself is consumed at exactly two
places — H3 and the O4′ mirror, the skip-side counting — with slack
everywhere else, mirroring where `n ≥ 5f + 1` is consumed in the
existing Odontoceti development.

## 3. Mirror, not parameterise

The hybrid rules are Odontoceti's shape at new constants: direct
commit/skip at `q` distinct authors, the indirect test (`ThickLink`) at
`k` distinct in-cone authors, the decision relation with the canonicity
clause. The arc will *mirror* the `Odontoceti/` modules rather than
retrofit them — arcs are additive, and the existing development stays
untouched — and rather than build the rule-parameterised decision
relation the discussion section has twice declined. The reason to
decline a third time is that the constants do not enter uniformly: the
safety counting discounts against the *honest* population `n − fb`
while every quorum is taken against the *derived* population
`n − fb − fc`, so a shared abstraction would need a four-parameter core
(population, discount, quorum, threshold) whose only instances would be
these two. What *will* be shared is the arithmetic seam: the
intersection lemmas of H1 below are stated over abstract cardinals, so
the mirrored rule proofs consume inequalities, not fault classes.

## 4. The theorems

**H1 (the counting core).** Two author sets whose sizes sum past
`n + fb` share an honest member:

    a.card + b.card > n + fb  →  ∃ v ∈ a ∩ b, v ∈ Honest

— T0′ with the discount at `fb` rather than the derived `F'.f`. Stated
over abstract cardinals; every conflict argument below is one
application plus the observation that an honest validator's single
decision block cannot both reference and omit `L` (`HonestNoEquiv`).

**H2 (commit versus skip).** `DirectCommit` and `DirectSkip` for one
candidate conflict: `q + q > n + fb` ⟸ `n > 3fb + 2fc`. Mirror of O1.

**H3 (a skipped leader fails the indirect test everywhere).** A direct
skip caps any cone's support authors below `k`: `q + k > n + fb` is
exactly the class bound. Mirror of O2, and the constraint `hybrid.md`
§3.3 derives is consumed here and nowhere else.

**H4 (link integrity / support propagation).** Every valid block at the
round above the decision round carries at least `k = 2q − n − fb`
support authors for a directly-committed candidate in its references,
so every anchor's cone passes the indirect test. Mirror of O3; the
counting is `hybrid.md` §3.4: honest blamers number at most `n − q`,
Byzantine blames at most `fb`, and a valid block references `q`
distinct authors, leaving `q − (n − q + fb) = k` supports. This is
where the derived instance's P3-at-`q` does the structural work.

**H5 (twin uniqueness; the canonical candidate).** Only Byzantine
validators can produce candidate twins now — crash-prone leaders never
equivocate — so twin uniqueness for direct commits (O1′'s mirror)
discounts at `fb`. The canonicity clause and the exact-complement
argument of O4′ carry over at the new constants; nothing suggests the
canonicity *gap* closes under the hybrid model (a Byzantine leader can
still plant two passing candidates in one anchor's cone), so the
canonical-candidate rule is retained, and a hybrid re-run of the
`utwin6_both_pass` exhibit is part of the witness plan.

**H6 (agreement and safety).** `Hybrid.decided_unique` and
`Hybrid.safety`, mirroring O5/O6 from H2–H5 exactly as the Odontoceti
proofs compose — per the extraction, O5 rests on O1, O1′, O2, O3, O4′
and nothing else, so the mirror's dependency budget is known in
advance.

**H7 (liveness).** Over the derived instance the existing interface
applies verbatim: `T ⊆ Correct`, `q ≤ T.card`, coverage from
`SynchronisedOn U T R`, production from `PopulatedOn U T`. The mirrors
of O7–O10 (direct commit of a reliable leader in one delivery; the
committed-run descent; `all_decided_below_of_fairRun`) go through at
quorum `q` with two populated rounds per commit, and view convergence
supplies the interface unchanged — `converges` binds exactly the
fully-correct class, which is the right set: nothing is promised about
what a crash-prone validator holds. Note the tight case has **no
slack**: at `n = 5fb + 3fc + 1` the correct class is exactly `q`, so
`T` must be all of it — the hybrid analogue of the report's remark that
at `f = 1` every correct validator is needed for a quorum.

**H8 (conservativity).** At `fc = 0` (`crash = ∅`) the hybrid
definitions coincide with Odontoceti's — same quorum, same `k`, same
relation — stated as definitional equalities or one-line `iff`s, the
anchor demanded by the house rule.

**H9 (witnesses).** Two models, both `decide`-sized:

- **Pure crash, `fb = 0, fc = 1, n = 4`**: `q = 3`, `k = 2`. Four
  validators, two-round commits, one line that stops — the smallest
  model in which the hybrid bound beats `5f + 1` (pure-Byzantine
  two-round would need `n = 6` to tolerate one fault). The crashed
  validator's absence is a truncated line, `Ucrash`-style; commits
  proceed on three supporters. This model is the arc's headline: *the classical
  committee of `3f + 1` = 4, with two-round finality, when the single
  tolerated fault is a crash* — where tolerating it as Byzantine would
  cost six validators.
- **Genuinely hybrid, `fb = 1, fc = 1, n = 9`**: `q = 7`, `k = 4`. One
  equivocator and one halted line in the same universe, four rounds
  (`Fin 36` ids, the size the Odontoceti witnesses already handle):
  every rule exercised, the indirect commit and skip both anchored, and
  the canonicity exhibit re-run.

**H10 (tightness — stretch).** `hybrid.md` claims the bound tight. The
refutation half is a data question in the house style of
`bound_is_necessary`: at `n = 5fb + 3fc` (one validator short),
construct a universe and two views deriving conflicting verdicts —
the H3 counting fails by exactly one honest validator, so the
counterexample is an equivocation pattern at the smallest short
committee, plausibly `fb = 1, fc = 0, n = 5` (where it is the known
tightness of `5f + 1`) and more interestingly `fb = 0, fc = 1, n = 3`.
Recorded as a target, not a promise; the safety theorems do not depend
on it.

## 5. Module plan

| Module | Contents |
|:---|:---|
| `Hybrid/Faults.lean` | `HybridFaults`, `Honest`, the derived `Faults` instance, `HonestNoEquiv`; H1 |
| `Hybrid/Rules.lean` | direct rules at `q`, `coneSupports`, `ThickLink` at `k`; H2–H4 |
| `Hybrid/Decision.lean` | the decision relation with canonicity; H5, H6 |
| `Hybrid/Liveness.lean` | H7 over the `T`-relativised interface |
| `Hybrid/Conservativity.lean` | H8, the `fc = 0` collapse |
| `Hybrid/Checkpoint/BaseSpec.lean` | **human review:** AbC classes, execution assumptions, proposal and certificate objects |
| `Hybrid/Checkpoint/RecoverySpec.lean` | **human review:** broadcast, validation, selection, and epoch-transition contracts |
| `Hybrid/Checkpoint/SafetyProofs.lean` | **Lean-checked:** quorum, uniqueness, prefix consistency, and recorder derivations |
| `Hybrid/Checkpoint/RecoveryProofs.lean` | **Lean-checked:** concrete selection, agreement, and preservation derivations |
| `LeanDagTest/Hybrid.lean` | H9: the `n = 4` crash model and the `n = 9` hybrid model |
| `LeanDagTest/HybridCheckpoint.lean` | concrete checkpoint certificate, finality certificate and recovery output |

## 6. Out of scope

- **Authenticated-broadcast implementation.** Recovery consumes only
  authentication/integrity, agreement, and delivery of actual inputs
  from recovery-correct senders. Protocol handlers are separately
  proved to submit recorded concrete certificate payloads. Local
  validation checks the closing epoch, quorum, and each signer-indexed
  authenticated proposal, and its soundness constructs a
  `CheckpointQC`; malformed inputs may be broadcast but are rejected.
  Dolev--Strong's rounds and cryptographic argument are not formalized.
- **Multi-epoch checkpoint safety.** Prefix consistency and
  same-height uniqueness are intentionally scoped to a single epoch.
  Recovery connects a selected closing-epoch checkpoint to the next
  genesis, but does not model arbitrary multi-epoch protocol machinery.
- **Post-checkpoint VoteQC extension.** The formal recovery output is
  the highest validated checkpoint history. The paper's deterministic
  extension with delivered VoteQCs up to the first gap is not modeled,
  so theorem names claim checkpoint preservation only.
- **DAG rejoin after recovery.** Safe Skip addresses a crash-prone
  validator that returns (report §12). The checkpoint subarc proves the
  recovered prefix safe; composing it with the subsequent DAG fill is
  outside this model.
- **Adaptive leaders over hybrid faults.** The adaptive layer is
  rule-agnostic (report §13.5) and should mirror onto the hybrid
  relation as it did onto Odontoceti's; also a sequel.
- **Detecting crashes.** Nothing distinguishes a crashed validator from
  a slow one, here or in any partially-synchronous model; the class is
  a modelling device, not an observable.
- **Chain quality and storage under the hybrid model** — the §7–§9
  accounts are pure-Byzantine and stay so.
