# lean-dag — Specification

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Formalize, in Lean 4 + Mathlib, the core combinatorial structures and safety
arguments underlying DAG-based BFT consensus, starting with the fragment of
**Mysticeti** needed to state and prove its key persistence/safety lemma,
then extending outward.

Sections marked **(assumption)** are modeling choices made where the
original notes were open-ended — flag any you want changed.

## 1. Scope

Phases 1, 1b and 2 are **built**; §7 indexes every theorem to its Lean name.

- **Phase 1 (main target):** static block DAG structure, quorum-intersection
  combinatorics, and the causal-persistence theorem from the notes (T0–T3).
  This is the mathematical core of why Mysticeti-style protocols are safe.
- **Phase 1b:** the counting argument giving a common correct ancestor
  across any three consecutive rounds (T3a–T3c). Still pure DAG
  combinatorics, and independent of Phase 2.
- **Phase 2 — uncertified DAGs (Mysticeti) — complete:** the two-level
  certification rule, direct commit and skip, and the indirect rule (T6a,
  M1–M6). What one must do once blocks are no longer certificates.
- **Phase 3 (stretch) — partly done:** total-order safety across the commit
  sequence; liveness under partial synchrony. The committed-*leader* sequence
  and all of **no retraction** are already proved, since neither needs an
  order on ids; what remains of T6 is the arrangement of blocks *within* a
  single flush. Liveness needs network timing axioms
  (GST, message delay bounds) rather than pure DAG combinatorics — scope it
  separately once Phases 1–2 land.

Appendix A holds the **certified-DAG** commit rule (T4–T5), deliberately off
the roadmap.

## 2. System model

**(assumption)** The fault model is **bundled as a class**, not threaded as
section variables. This fixes the signature of `ValidWrt`, `BlockUniverse`,
and every theorem below, so it is worth settling first.

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  byzantine : Finset Validator
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  card_byzantine : byzantine.card ≤ f

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*}
variable {Payload : Type*}

def Correct : Finset Validator := (F.byzantine)ᶜ
```

Bundling wins on two counts, both verified against the built file rather
than assumed:

- **The cardinality hypotheses ride on the instance**, so they never appear
  as explicit arguments and no `include` is ever needed. With section
  variables every theorem carried `(f) (Byzantine) (hcard) (hbyz)` before
  its real arguments, and every declaration needed `include hcard hbyz in`,
  since `Prop`-valued variables are not auto-included.
- **`Correct` takes no argument** — the instance is inferred from
  `Validator`. As a section-variable `def` it necessarily absorbed
  `Byzantine` as a parameter, forcing `Correct Byzantine` at every use.

**Refer to the fault bound as `F.f`, never as a bare `f`.** With `f` as a
class field, `Faults.f` takes `Validator` explicitly, and a bare `f` in a
position expecting only an `ℕ` gives Lean nothing to determine the type
from — it elaborates to a metavariable and fails confusingly later. Naming
the instance `F` and writing `F.f`, `F.byzantine`, `F.card_validators`,
`F.card_byzantine` keeps every reference unambiguous.

The fields are not uniform in this respect, which is what makes it a trap:
`Faults.byzantine` returns a `Finset Validator`, so `Validator` *is*
recoverable from its result type and a bare `byzantine` elaborates fine,
while `Faults.f` returns a bare `ℕ` and does not. Going through `F.` for
everything avoids having to remember which is which.

Remaining notes:

- `DecidableEq Validator` is needed for `creatorsOf` (§3.2), a
  `Finset.image` into `Validator`. **`DecidableEq BlockId` is not needed
  globally**: `Finset α` itself imposes no decidable equality — only
  operations like `image`, `∪`, and `∩` do, and here those all land in
  `Validator`.

  Introduce it locally where a `Finset.filter` tests a predicate of the form
  `i ∈ (U.block q).refs`: `Support.lean` for `supporters`, `CommonCore.lean`
  for `correctBlocksAt`, and `Mysticeti.lean` for the vote and certificate
  sets.

  Note the split *within* `Support.lean`. The coverage and hitting lemmas
  take their support set as a plain `Finset Validator` with a witness per
  member, so they need no instance; it is declared only lower down, for the
  concrete `supporters` sets callers build. Keeping the lemmas instance-free
  is what lets T3 and M2 apply without any decidability on ids.
- **(assumption)** `3 * f + 1 ≤ Fintype.card Validator` — the literature's
  general form. Throughout, `n` abbreviates `Fintype.card Validator`;
  quorums are `n − f`, which at the boundary `n = 3f+1` (where every
  concrete witness sits) is the familiar `2f+1`.
- Rounds are plain `ℕ` throughout. No `Round` abbreviation — it would add
  nothing, and two spellings for one type reliably drift apart.

Five consequences worth naming once rather than re-deriving at each use:

- `exists_correct_of_card`: any `S : Finset Validator` with
  `F.f + 1 ≤ S.card` contains a correct validator, since
  `F.byzantine.card ≤ F.f` means `S` cannot be wholly Byzantine. Feeds T0,
  and through T0' reaches M5′ — the whole chain is live.
- `card_correct_add_byzantine : Correct.card + F.byzantine.card = 3 * F.f + 1`
  — from `Finset.card_compl` and `F.card_validators`. Stated **additively**
  so it gives both bounds without ℕ subtraction. Phase 1b needs the *upper*
  bound on `Correct.card`: T3a divides an incidence count by the number of
  correct validators, and a lower bound is useless as a denominator bound.
- `card_le_card_inter_correct_add_byzantine : S.card ≤ (S ∩ Correct).card + F.byzantine.card`
  for any `S : Finset Validator` — "Byzantine validators absorb at most `b`
  of any set". The workhorse behind *a quorum still contains many correct
  validators*; T3a's per-block bound is one line given it.
- `card_inter_correct_of_quorum : n−f ≤ S.card → F.f + 1 ≤ (S ∩ Correct).card`
  — the *cardinality* strengthening of `exists_correct_of_card`, which only
  produces one witness. Reach for this whenever a count of correct members is
  wanted rather than their existence.
- `card_correct : 2 * F.f + 1 ≤ Correct.card`. Used by **nothing** — T0, T3,
  and the commit-agreement arguments route through `F.card_byzantine`, and
  T3a needs the additive form above rather than this one. Kept because
  liveness (T7) would want it, but it is on no currently-built path; do not
  reach for it in the counting argument.

## 3. Blocks and the DAG

### 3.1 Block and BlockId

Blocks are referenced by **id**, not by value. `BlockId` is an opaque type
carrying no instances at all (§2); `Block` itself is then non-recursive:

- `round : ℕ`
- `creator : Validator`
- `refs : Finset BlockId` — pointers to blocks at the preceding round
- `payload : Payload` — opaque, per the notes; inert throughout Phase 1.

**(assumption)** `Block` is declared with its three type parameters
**explicit** — `structure Block (Validator BlockId Payload : Type*)`, used as
`Block Validator BlockId Payload` — rather than letting them auto-bind from
the section variables. Auto-binding would also drag in whichever instance
variables mention `Validator`, so `Block` would silently acquire a
`Fintype`/`Faults` dependency it has no use for. Explicit parameters are
verbose at use sites but predictable.

This is not merely stylistic. The value-recursive alternative (`refs :
Finset Block`) almost certainly does not elaborate in Lean 4: nested
inductive types may recurse through `List`, but `Finset` is built on
`Multiset`, itself a quotient of `List`, and the nested-inductive
construction does not support recursion through a quotient. Indirection via
ids sidesteps that, and matches real implementations where a `BlockId` is a
hash of the block.

The cost is that a `BlockId` means nothing on its own — it must be resolved
through a lookup function to yield a `Block`, so validity (§3.2) and causal
history (§3.4) both take that lookup as a parameter. The benefit is that
"same block" becomes **same id**, which is what every uniqueness claim below
(non-equivocation, T1, M5) actually wants; content equality is strictly
weaker and never needed.

**(assumption)** Ids are *not* assumed collision-free — `U.block` need not
be injective on `U.ids`. Real ids are content hashes so injectivity would be
realistic, but nothing below needs it and omitting it keeps the theorems
strictly stronger. See §5 Q4.

**(assumption)** Only "strong" edges to the immediately preceding round are
modeled — no weak edges to older rounds. Real Mysticeti has weak edges (to
avoid dropping blocks that missed the quorum cutoff); omitting them keeps
Phase 1 simpler and does not affect persistence.

**(assumption)** Round-0 blocks are genesis blocks with no refs. Nothing
constrains how many a validator has beyond ordinary non-equivocation (§3.3),
which already gives correct validators at most one; a Byzantine validator
may have several, and no theorem cares.

### 3.2 Block validity

Validity dereferences refs, so it takes a **lookup function**
`blk : BlockId → Block`, not a universe. This is forced: §3.3 makes "every
member is valid" a field of `BlockUniverse`, and a structure field cannot
mention the structure being defined. With `blk` as the parameter that field
reads `∀ i ∈ ids, ValidWrt block (block i)`, referring only to siblings.

Two notations for "the validators behind a set of ids", split so that one
set of lemmas serves both blocks and bare id-sets:

```lean
creatorsOf blk (s : Finset BlockId) : Finset Validator :=
  s.image (fun i => (blk i).creator)

creators blk b : Finset Validator := creatorsOf blk b.refs
```

The generalized form is not cosmetic. T3's hypothesis, `authorsAt` (§4
*Coverage*), and Phase 2's vote and certificate sets all quantify over
id-sets that are *not* any block's refs; a block-only `creators` would force
each of them to inline the image by hand.

Then `ValidWrt blk b` holds iff:

- **Predecessor:** `∀ i ∈ b.refs, (blk i).round + 1 = b.round`
- **Distinct creators:**
  `∀ i j ∈ b.refs, (blk i).creator = (blk j).creator → i = j`
- **Quorum:** `b.round > 0 → 2 * F.f + 1 ≤ (creators blk b).card`

Three notes on the shape.

**Predecessor is stated additively**, not as `(blk i).round = b.round - 1`.
That avoids ℕ-subtraction entirely, and makes the genesis case *derivable*
rather than a separate branch: if `b.round = 0` then `(blk i).round + 1 = 0`
is impossible, so `b.refs = ∅` falls out. Only the quorum condition needs a
round guard.

**Quorum is stated on the creator set**, not on `b.refs.card`. This is the
form every downstream proof wants, and it is the more faithful reading of
"a quorum of blocks from the previous round" — the protocol means `n−f`
*validators*. Stating it directly makes the quorum fact the field projection
`ValidWrt.quorum` itself, rather than a derived `creators_quorum` lemma, and
removes any `card_creators` bridge from the critical path. With distinctness
also present `b.refs.card ≥ n−f` still follows, so nothing is lost.

**Distinct creators is needed only at commit agreement.** It is a
genuine protocol rule — a block must not cite the same author twice — but it
is worth being precise about where it is needed, because the guess is
wrong. T3
does *not* use it: coverage requires its supporters to be **correct**, and
universe-level non-equivocation (§3.3) already makes a correct validator's
block unique. Distinctness is needed only where an *equivocating* author
must be ruled out — M5, and T5 in Appendix A — precisely the case
non-equivocation says nothing about.

This is **enforced, not merely asserted**, and it is easy to lose by
accident. `ValidWrt.refs_nonempty` — which T3's inductive step needs — is
proved from the quorum condition alone rather than via `card_refs`, because
`card_refs` goes through `card_creators`, which *does* use distinctness.
Routing it that way would silently put distinctness on T3's dependency path.

`distinct_creators` has exactly **two** consumers, and the split is the whole
point: M5′, which is the genuine use, and `card_creators` (which
feeds only `card_refs`, which nothing calls). Grepping for it is therefore a
live check that Phase 1 and 1b have not started leaning on it.

### 3.3 Block universe

Non-equivocation constrains *what correct validators ever author*, not what
a particular DAG happens to contain. Stating it per-DAG would be too weak:
two DAGs could each satisfy "at most one block per correct validator per
round" while containing *different* such blocks — a correct validator
equivocating, with both DAGs looking well-formed. That would silently break
every cross-view result — M6, and T5 in Appendix A. So the constraint lives
one level up.

A **`BlockUniverse` `U`** is every block that exists, authored by anyone:

- `ids : Finset BlockId` — which blocks exist;
- `block : BlockId → Block` — what each one is;

subject to:

- **Complete:** `∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids`.
- **Valid:** `∀ i ∈ ids, ValidWrt block (block i)` (§3.2) — mentions only
  sibling fields, which is why §3.2 takes a lookup function.
- **Correct validators do not equivocate:** for `v ∈ Correct` and any round
  `r`, at most one `i ∈ ids` has `(block i).creator = v` and
  `(block i).round = r`. Byzantine validators are unconstrained.

**(assumption)** `block` is *total*, with junk outside `ids`, rather than
`BlockId → Option Block`. Every theorem quantifies over `i ∈ ids`, so the
junk is never observed, and this avoids `Option`-unwrapping throughout.

**(assumption)** Non-equivocation is a universe field rather than (a) an
ambient hypothesis over all inhabitants of `BlockId`, or (b) a structural
`authored : Validator → ℕ → Option BlockId` map. Option (b) makes
Byzantine equivocation awkward to express, which we need; (a) detaches the
constraint from any carrier set.

### 3.4 Causal history

`Reaches U c b` — "`b` is in the causal history of `c`" — the
reflexive-transitive closure of `refs` resolved through `U`, and the target
relation for T3.

Since refs are ids this is a relation on `BlockId × BlockId` indexed by `U`,
definable via `Relation.ReflTransGen` on
`fun i j => j ∈ (U.block i).refs`. The predecessor condition (§3.2) makes
`round` strictly decrease along `refs`, supplying the induction T3 needs.

### 3.5 Views (Phase 2)

Phases 1 and 1b need no views, and neither do M1–M3 or M5 — all are
universe-level. Views first matter at M4/M6, where committing is a decision
an individual validator makes from its own local DAG.

A **view** is a `V : Finset BlockId` with `V ⊆ U.ids`, itself complete:
`∀ i ∈ V, ∀ j ∈ (U.block i).refs, j ∈ V`. Views share `U.block` — they
disagree about *which* blocks they hold, never about what an id means — and
inherit validity and non-equivocation from `U`. Different correct validators
may hold different views; that asymmetry is the entire point of M6 (and of
T5 in Appendix A).

## 4. Theorem roadmap

### Coverage — the shared principle

Both T3 and T3c rest on one statement, in `Support.lean`:

> If a block is referenced by the round-`(r+1)` blocks of enough **correct**
> validators, then every round-`(r+2)` block reaches it.

Correctness of the *supporters* is what makes it work: a correct validator
has exactly one round-`(r+1)` block, so naming it suffices to reach what it
references. A Byzantine supporter could hold two, only one of which
references the target — which is why Byzantine support is worthless here
even though it exists.

"Enough" admits two thresholds, and the gap between them is the only thing
separating the two theorems:

- **`p + f + 1 - n`** (`reaches_of_correct_support`), where
  `p = |authorsAt U (r+1)|`. A round-`(r+2)` block draws its `n−f`
  referenced creators from those same `p`, so it misses at most
  `p - (n−f)` and cannot dodge `p + f + 1 - n` (the old `p - 2f` at
  `n = 3f+1`).
- **`f+1`** (`reaches_of_correct_support_of_card`), uniform. Since `p ≤ n`
  always, this is the corollary: `n−f` named out of at most `n` means at
  most `f` missed.

**Why `p + f + 1 - n` rather than just `f+1`.** It looks like a
participation-sensitive fudge and is not. Imagine handing every absent
correct validator a valid round-`(r+1)` block — always possible, since a
round-`(r+2)` block exists and so enough round-`r` blocks are available to
reference. Now participation is full and the count yields `f+1` supporters.
But the observed round-`(r+2)` block still references only the *originally
present* validators, so of those `f+1` supporters it can see at least

> `(f + 1) − (n − p)  =  p + f + 1 − n`

`p + f + 1 - n` is exactly `f+1` net of absentees. Absentees shrink the requirement
precisely as fast as they shrink what counting can deliver, which is why no
progress assumption appears anywhere. (We do not formalise the extension
argument — it would need fresh `BlockId`s, hence an `Infinite BlockId`
hypothesis and a universe-extension construction, for a theorem statement
that comes out identical.)

**The hitting lemma is the actual primitive.** Coverage reaches a *fixed*
block; M2 must reach *some certificate*, a target set. So the primitive is
`exists_mem_refs_of_correct_support`: if `f+1`-or-so correct validators
published round-`n` blocks satisfying a predicate `P`, no round-`(n+1)` block
can avoid referencing one. It is stated with `P` a bare predicate rather than
a `Finset BlockId`, since only the *validator* set is ever counted — so the
hitting and coverage lemmas need no `DecidableEq BlockId` at all.

Both coverage lemmas are then the instance where every `P`-block references
the same `b`, and `reaches_pred_of_round_le` (**propagation**) carries the
result upward from one round to all higher ones. T3 and M2 are each a base
case plus propagation, and neither carries its own induction. This makes
precise that both commit rules are instances of *a quorum of correct support
cannot be dodged* — differing only in how many layers deep it runs.

Which form to use is determined by how supporters are obtained:

- **assumed** → `f+1`. T3's quorum of `n−f` distinct creators contains
  `f+1` correct ones by `card_inter_correct_of_quorum`, regardless of `p`.
- **counted** → `p + f + 1 - n`. T3a can only guarantee that much; at
  `n = 10, f = 3`, `p = n−f = 7`, `b = f = 3` the count yields 3 supporters
  where `f+1 = 4`, and the theorem survives only because
  `p + f + 1 - n = 1` there.

### Phase 1

- **T0 — Quorum intersection.** Any two `Q₁ Q₂ : Finset Validator` with
  `card ≥ n−f` (out of `n` total) satisfy `(Q₁ ∩ Q₂).card ≥ n−2f ≥ f + 1`,
  hence contain a correct validator by `exists_correct_of_card` (§2). Pure
  `Finset`/`Fintype` cardinality — likely close to a one-liner from
  `Finset.card_inter_add_card_union` or similar.

  Corollary **T0'**, stated on **id-sets** rather than blocks: for
  `s t : Finset BlockId` with `2 * F.f + 1 ≤ (creatorsOf blk s).card` and
  likewise for `t`, some correct validator lies in
  `creatorsOf blk s ∩ creatorsOf blk t`.

  For a block, apply it with `s := b.refs` and discharge the quorum
  hypothesis from validity (§3.2, definitional).

  **Unused by Phase 1 and 1b, required from Phase 2 on.** T3's base case
  went through T0' until the coverage refactor (§4 *Coverage*) and now calls
  `reaches_of_correct_support_of_card`, whose intersection has a different
  shape: one quorum against one *correct* set of size `f+1`, rather than two
  quorums. Phases 1 and 1b therefore reach a correct validator via
  `card_inter_correct_of_quorum` instead.

  M5′ uses T0' — the two vote quorums of two certificates — which is exactly
  T0's two-quorum shape, as does T5 in Appendix A. Note it uses it **once**:
  M5's original proof intersected the certificate quorums as well, and M5′
  showed that outer step was unnecessary.

- **T1 — Non-equivocation as id equality.** For `v ∈ Correct`, any two ids
  `i j ∈ U.ids` with creator `v` at the same round satisfy `i = j`.
  Immediate from §3.3, but it is what lets a quorum-intersection argument
  land on a *single concrete id* instead of an existential.

- **T2 — Causal history composes and runs downward.** `Reaches U` is
  reflexive, closed under single reference steps, and transitive — all three
  inherited from `Relation.ReflTransGen`. The content is
  `round_le_of_reaches`: following a reference strictly decreases the round
  (§3.2's predecessor condition), so causal history never climbs.

  Calling this "well-founded" overstates it. T3 inducts
  on the round *number*, an ordinary `ℕ`, not on `Reaches`; no
  `WellFoundedRelation` instance is needed, only the fact that a block's
  references sit at a strictly smaller round. Supporting lemmas:
  `mem_ids_of_reaches` (completeness propagates along a walk) and
  `eq_of_reaches_of_refs_empty` (genesis blocks are causal-history leaves).

- **T3 — Persistence (the theorem from the notes).** Precise statement:

  > Let `Q ⊆ U.ids` be a set of ids at round `r+1`, all of which reference
  > `b` (`∀ q ∈ Q, b ∈ (U.block q).refs`), and whose creator set is a
  > quorum: `2 * F.f + 1 ≤ (creatorsOf U.block Q).card`. Then for every
  > `c ∈ U.ids` with `(U.block c).round ≥ r + 2`, `Reaches U c b`.

  Note `b ∈ U.ids` and `(U.block b).round = r` are **not** hypotheses. Both
  are consequences of the quorum condition: a quorum has `≥ n−f ≥ 2f+1 ≥ 1`
  authors so `Q` is nonempty, and any member is in the universe, references
  `b`, and sits at round `r+1` — which pins `b` by completeness and the
  predecessor condition. Assuming them would only weaken the theorem
  (`mem_ids_and_round_of_quorum_support` records the derivation).

  **The bound is `r + 2`, and it is tight.** A round-`(r+1)` block outside
  `Q` need not reach `b` at all, so the naive "every block after round `r`"
  reading is false. Counterexample: `f = 1`, validators `{A,B,C,D}`, quorum
  3. Let `b` be A's round-`r` block and `Q` the round-`(r+1)` blocks of
  `A,B,C`, all referencing `b`. D's round-`(r+1)` block must reference 3
  round-`r` blocks and may pick `{B,C,D}`, omitting `b`; all its refs sit at
  round `r`, so `b` is not in its causal history. Quorum intersection needs
  *two* ref-quorums to compare, and `r+2` is the first round that has them.

  The hypothesis is on `Q`'s *creator set*, not `Q.card`: `Q` is an
  arbitrary id set here, not one block's refs, so it carries no distinctness
  invariant of its own and `Q.card` would be the wrong measure. In every
  application `Q` does come from distinct validators, so this loses nothing
  at call sites.

  Proof sketch — induction on `(U.block c).round`. All the real work is in
  the base case, and since the coverage refactor that case is a single
  appeal to §4 *Coverage*:

  - **Base, `round c = r + 2`.** `Q`'s creator set is a quorum, so at least
    `f+1` of its members are correct (`card_inter_correct_of_quorum`, §2).
    Each such creator authored a round-`(r+1)` block referencing `b`, i.e.
    is a correct supporter — so the uniform (`f+1`) coverage lemma applies
    directly.
  - **Step, `round c = n + 1` with `n ≥ r + 2`.** No coverage needed: `c`'s
    refs are nonempty (the quorum is `≥ n−f ≥ 2f+1 ≥ 1`, and the image of `∅` is
    `∅`) and sit at round `n ≥ r + 2`, so the IH applies to any one of them;
    compose by T2.

  So **T3 is coverage plus induction**. Its quorum hypothesis is used for
  exactly one thing: manufacturing `f+1` correct supporters. Above the base
  layer, height is carried by transitivity alone.

  **Distinctness (§3.2) is not used in this proof.** Coverage requires its
  supporters to be correct, and non-equivocation (T1) alone pins their
  blocks. What the induction relies on across rounds is completeness (so refs
  land in `U.ids` and the IH applies) plus the quorum and predecessor
  conditions at every intervening round — all supplied by §3.3's validity
  field.

### Phase 1b — a common correct ancestor

Persistence (T3) says a block *already backed by a quorum* survives forever.
This group says something is **always** backed, whether or not anyone
arranged it: across any three consecutive rounds, some correct validator's
round-`r` block ends up in the causal history of every round-`(r+2)` block.
The argument is a counting one, in the spirit of the Gather protocol's
common-core lemma.

Coverage (§4 *Coverage*) supplies the second half of the argument; this
section supplies the first — **producing** the correct supporters coverage
consumes. `blocksAt`, `authorsAt`, `p` and the `p − 2f` threshold are all as
defined there, and live in `Support.lean`. Write `b := F.byzantine.card` for
the actual Byzantine count, which appears only inside the proof.

**(assumption)** Every `p − 2f` below is written subtractively for
readability only. In Lean state the support threshold **additively** — `k`
supporters with `p ≤ k + 2 * F.f` — exactly as §3.2 does for the predecessor
condition. Truncated ℕ subtraction would otherwise make the threshold
silently collapse to `0` whenever `p ≤ 2f`, which is precisely the
degenerate range where no round-`(r+2)` block exists, turning a vacuous case
into an apparently provable one.

- **T3a — Correct-support counting.** Some correct validator's round-`r`
  block is referenced by the round-`(r+1)` blocks of at least
  `p + f + 1 − n` distinct **correct** validators.

  At least `p − b` of the `p` are correct, and each has a *unique*
  round-`(r+1)` block (T1) referencing `n−f` distinct validators — straight
  from the creator-set quorum, no distinctness needed — of which at least
  `n−f−b` are correct. Counting incidences between those blocks and the
  correct round-`r` authors they name gives at least `(p−b)(n−f−b)`, spread
  over `Correct.card = n − b` validators (`card_correct_add_byzantine`,
  §2 — the *upper* bound is the one that matters here). Pigeonhole yields a
  validator `w` receiving at least `(p−b)(n−f−b) / (n−b)`, and `w`'s
  round-`r` block is unique by T1. The arithmetic obligation reduces to
  `c² ≤ f(l+c)` for `c = n − b` and `l` the number of correct
  round-`(r+1)` blocks; `l ≤ c` turns it into `c ≤ 2f` — impossible, since
  `b ≤ f` and `n ≥ 3f+1` force `c ≥ 2f+1`. Tight exactly at
  `b = f, p = n`; slack everywhere else.

- **T3c — Common correct ancestor.** If any block exists at round `r+2`,
  then some correct validator's round-`r` block lies in the causal history of
  **every** round-`(r+2)` block. Immediate from T3a and the
  participation-sensitive form of coverage (§4 *Coverage*).

  The sole premise is that a round-`(r+2)` block exists — a fact about the
  DAG in hand, not an assumption that anyone makes progress. This stays a
  safety result. The degenerate cases are consistent with it: if `p < n−f`
  no round-`(r+2)` block can be formed and the claim is vacuous; if
  `p = n−f` every round-`(r+2)` block names all of them and the conclusion
  is immediate.

### Phase 2 — uncertified DAGs (Mysticeti)

Mysticeti drops the per-block certification round for latency, so a block
carries no independent authority. That authority has to be rebuilt inside
the DAG, as a **second certification layer** one round further on. This
section is that rule and its safety.

Fix a slot with leader block `L` by `leader k` at round `r`:

- a round-`(r+1)` block **votes** for `L` if `L ∈ refs`, and **blames**
  otherwise;
- a round-`(r+2)` block **certifies** `L` if its refs include votes for `L`
  from **`n−f` distinct validators**;
- **direct commit**: certificates for `L` come from `n−f` distinct validators;
- **direct skip**: blames come from `n−f` distinct validators;
- otherwise **undecided**. A later direct commit triggers a backward sweep
  over the undecided slots in the causal history of *that* leader block,
  **earliest first**: each is committed if a certificate for it lies in that
  causal history, and skipped otherwise.

**(assumption) Leader slots are not every round.** Write `slotRound k` for
the round of slot `k`, with

> `slotRound (k+1) ≥ slotRound k + 3`

**This spacing is required for safety, not merely for scheduling.** A
certificate for `L` sits at round `r+2`, and by T2 a block's causal history
reaches only strictly lower rounds. An anchor whose leader block sat at
round `≤ r+2` could therefore never see a certificate for `L`, and would
skip it unconditionally — even where another validator directly committed
it. The `+3` spacing is exactly what puts every anchor at round `≥ r+3`,
which is what M2 needs. Any schedule change that narrows it breaks M4.

The work splits cleanly, and the split is worth respecting because the
stages need very different machinery:

- **Stage A — M1, M2, M3, M5.** Universe-level, and needing neither views
  nor a leader function: M5 is stated as *same round, same creator* rather
  than *same slot*. Pure combinatorics on top of `Support.lean`, the same
  character as Phase 1b. Nothing below blocks it.
- **Stage B — T6a.** Makes the per-view certificate check well-defined.
  `View` sits with the universe in `BlockDag.lean` and T6a with `Reaches` in
  `CausalHistory.lean`, rather than inside `Mysticeti.lean`: both are general
  notions, and Appendix A's T4/T5 would want them too.
- **Stage C — M4, M6.** The decision procedure, the slot schedule, and
  agreement.

- **T6a — Causal history is view-closed.** For a complete view `V` and
  `i ∈ V`, `Reaches U i j` implies `j ∈ V`, and reachability computed inside
  `V` coincides with reachability in `U`.

  Not needed by M1–M3 or M5, which are universe-level. **Required for M4
  and M6**: the indirect rule asks whether a certificate lies in an anchor's
  causal history, and each validator evaluates that against its own view.
  Two validators with the same anchor agree only because views are
  downward-closed. Cheap — an induction along `Reaches` — and it is the
  whole of Stage B.

- **M1 — Commit and skip are exclusive.** No slot admits both a direct
  commit and a direct skip. Immediate from M3.

- **M2 — Direct commit ⟹ the certificate is unavoidable.** If `L` is
  directly committed, every block at round `≥ r+3` reaches some certificate
  for `L`.

  The certificates sit at round `r+2` with `n−f` distinct creators, so `f+1`
  of them are correct (`card_inter_correct_of_quorum`). A round-`(r+3)`
  block names `n−f` of at most `n` validators and so misses at most `f`, hence
  names one of those correct certifiers, whose round-`(r+2)` block is unique
  (T1) and therefore *is* that certificate. Later rounds follow by
  induction. This is the **hitting lemma** — coverage generalised from a
  fixed block to a set — and it is the same argument as T3's base case.

- **M3 — Direct skip ⟹ no certificate exists anywhere.** If `n−f` validators
  blame, no certificate for `L` exists in the entire universe.

  A *correct* validator's single round-`(r+1)` block either votes or blames,
  never both, so `blames ∩ votes ⊆ Byzantine` and

  > `|votes| ≤ n − (n−f) + f = 2f  <  n−f`

  and a certificate requires `n−f` distinct vote-creators. Note the
  conclusion is universe-wide, not view-relative: this is why a skip needs
  no anchor to justify it.

- **M4 — Direct and indirect never disagree.** If `L` is directly committed
  by anyone, every anchor's causal history contains a certificate for `L`
  (M2, using the `≥ r+3` spacing), so the indirect rule commits it too. If
  `L` is directly skipped, no certificate exists at all (M3), so no anchor's
  history contains one and the indirect rule skips it too.

  The two halves are **not symmetric**, which is worth noticing. The commit
  half needs the anchor far enough along, since the certificate has to be
  *reachable*; the skip half needs no round hypothesis at all, because M3
  rules the certificate out universe-wide rather than merely out of reach.
  Only the commit half is why leader spacing matters.

  `certifiedIn_iff_of_view` records the companion fact that the test is
  view-independent (T6a): confining the search to the validator's own view
  loses nothing, since the certificate could never have lain outside it.

- **M5′ — Certificate uniqueness.** If certificates exist for two round-`r`
  blocks by the same author, those blocks coincide.

  Two certificates each name `n−f` distinct voters; the two voter sets
  intersect in a correct `w` (T0'); `w`'s single round-`(r+1)` block votes
  for both (T1); and **distinctness** (§3.2) forbids one block referencing
  two round-`r` blocks by one author. That last step is the sole
  essential use of distinctness in the development.

  This is the form M6 needs, because the indirect rule commits on a *single*
  certificate in reach rather than a quorum of them. The proof needs no
  relationship between the two certificates, and no round hypothesis — a
  voter sits at round `r+1` and references its candidate, which pins the
  candidate to round `r`.

- **M5 — One block per slot.** Two blocks directly committed for the same
  slot are equal. A corollary of M5′: a direct commit implies a certificate
  exists. An outer certificate-quorum intersection here is
  unnecessary.

- **M6 — Agreement.** No two correct validators reach conflicting decisions
  for a slot. As with T5 this is *no-conflicting-decision*, not "both
  decide": a validator that has not yet decided is not in disagreement.

  **The anchor is the nearest committed slot after `k`** — not the slot whose
  direct commit happened to trigger the sweep. That distinction is not
  cosmetic; the other reading is unsound. Slots at rounds 0, 3, 6, with
  exactly one certificate `C` for slot 0 — too few to commit it directly, so
  slot 0 is undecided. Validator 1 directly commits slot 1, whose leader
  block references a quorum of round-2 blocks but misses `C`, and skips slot 0.
  Validator 2 instead directly commits slot 2, whose leader block does reach
  `C`, and commits slot 0. Two validators, opposite verdicts.

  Anchoring on the *nearest* committed slot closes it. Validator 2 must
  resolve slot 1 first, and M2 forces its hand: slot 1 was directly
  committed by someone, so a quorum of certificates for it exists and validator 2's
  anchor reaches one, so validator 2 commits slot 1 indirectly. Slot 1 is
  then the nearest committed slot after 0 for **both** validators, so both
  evaluate slot 0 against the same subgraph.

  So the engine of M6 is *any direct commit is recoverable indirectly* — M2
  — and the sweep resolves slots downward from the trigger precisely so the
  nearest anchor is known when each slot is reached.

  **(assumption)** Decisions are modelled as an **inductive relation**,
  `Decided V k v`, not a function. A `decide` function recurses upward in
  slot index with no a-priori bound, so it would need fuel or a partiality
  wrapper, and nothing here needs to compute.

  The "nearest" side-condition looks like it needs a *negative* premise —
  no slot strictly between `k` and `j` is committed — which an inductive
  definition cannot carry. It is stated positively instead: **every slot
  strictly between is `Decided` *skip***. That is equivalent, since the sweep
  decides every slot it passes, and it keeps every recursive occurrence
  positive.

  **(assumption)** The direct rules become **view-relative** here
  (`DirectCommitIn V`), since a validator applies them to the certificates it
  can actually see. They are monotone into the universe-level versions of
  Stage A — `V ⊆ U.ids` — so M4 and M5 lift to views directly, and no
  counting is redone.

  Which leader block is "the" slot-`k` candidate is left open: for a correct
  leader T1 gives uniqueness, but a Byzantine one may have several. The
  definitions quantify over round-`slotRound k` blocks by `leader k` rather
  than selecting one, and M5 supplies the uniqueness where it is needed.

  ### C3 in detail

  **A missing lemma, found while designing this: M5 is too weak.** M5 says
  two *directly committed* blocks for a slot coincide, i.e. two blocks each
  backed by a quorum of certificates. But the indirect rule commits on the strength
  of **one** certificate lying in the anchor's history. Comparing an indirect
  commit against anything therefore needs:

  > **M5′ (certificate uniqueness).** If a certificate exists for `L₁` and a
  > certificate exists for `L₂`, and `L₁`, `L₂` are round-`r` blocks with the
  > same author, then `L₁ = L₂`.

  It holds, and by M5's *inner* argument alone. Each certificate names `n−f`
  distinct voters, the two voter sets intersect in a correct `w` (T0), `w`'s
  single round-`(r+1)` block votes for both (T1), and distinctness forbids it
  referencing two round-`r` blocks by one author. Note this never needs the
  two certificates to be the same block, so the outer certificate-quorum
  intersection M5 performs is not required. **M5 becomes a corollary of M5′**
  — a direct commit implies a certificate exists.

  With M5′ in hand, define `HasCertificate L r` as `(certificates U L r)`
  being nonempty. Both a direct commit and a `CertifiedIn` witness imply it,
  so *every* commit-versus-commit case collapses to one appeal to M5′.

  **The induction is structural on the first derivation**, generalised over
  the second view and verdict:

  > `Decided U V₁ k v₁ → ∀ V₂ v₂, Decided U V₂ k v₂ → v₁ = v₂`

  Not induction on rounds, and not on slot index — on the derivation tree.
  The IH then applies to exactly the two kinds of sub-derivation the indirect
  constructors carry: the anchor `Decided U V₁ j (some A)`, and each
  intermediate `Decided U V₁ i none`.

  Case analysis on the second derivation. Of the sixteen pairings, all but
  one are immediate:

  | pairing | closes by |
  |---|---|
  | commit / commit, any mix of direct and indirect | M5′ |
  | direct commit / direct skip | cross-view M1 (C2) |
  | direct commit / indirect skip | the engine — `certifiedIn_of_directCommitIn` puts the certificate in the other anchor's reach, contradicting its skip |
  | direct skip / indirect commit | M3 — a skip leaves no certificate anywhere, so nothing is in reach |
  | skip / skip | both `none` |

  **The one real case is indirect commit against indirect skip**, with
  anchors at slots `j₁` and `j₂`. Compare them three ways:

  - `j₁ = j₂` — the IH at that slot forces `A₁ = A₂`, and then one derivation
    claims a certificate in reach of that anchor while the other denies it.
  - `j₁ < j₂` — the *skip* derivation's intermediate premise covers `j₁`, so
    it decides `j₁` as `none`; the IH against the commit derivation's anchor
    sub-derivation gives `some A₁ = none`.
  - `j₁ > j₂` — symmetric, using the commit derivation's intermediate premise
    at `j₂`.

  So "anchor agreement" is never proved as a standalone statement. It falls
  out of the induction: the intermediate-skip premises are exactly what let
  the IH reach across to the other validator's anchor. That is the payoff of
  stating "nearest" positively in C1 — the negative reading would carry no
  sub-derivation to induct on.

  Staging, in dependency order:

  | | | risk |
  |---|---|---|
  | C1 | slot schedule, leader blocks, `DirectCommitIn`, the `Decided` relation | ✓ |
  | C2 | view-relative M4 and M5, by monotonicity | ✓ |
  | C3 | M5′, then `decided_unique` by structural induction | ✓ |
  | C4 | M6 from C2 and C3 | ✓ |

  *Built.* The one surprise in C3 was that the IHs in Lean's generated
  recursor come **after** all constructor arguments rather than beside their
  own recursive premise; the case patterns must be ordered accordingly.

  C3 is the only part that is not static combinatorics. Its induction runs
  over *slots between `k` and its anchor* rather than over rounds, so the
  measure is not the round number, and the well-foundedness needs care.

### Phase 3 (stretch)

- **T6 — Total order safety.** Two correct validators emit the same *blocks*
  in the same order.

  The **leader half is already done**: slots are indexed by `ℕ`, so reading
  M6's verdicts off in slot order and dropping the skips gives a list, and
  pointwise agreement makes the lists equal. That is `commitSeq_agree`, a
  corollary rather than a theorem.

  The **block half** is what remains. A ledger contains every block, not just
  leaders: committing the leader at slot `k` flushes all blocks in its causal
  history not already output. Two of the three ingredients are in hand — the
  agreed leader sequence (M6), and the fact that a validator holding a leader
  necessarily holds its whole causal history (T6a, which is where view
  closure is needed beyond the certificate check).

  The missing ingredient is a **deterministic order within each flush**, and
  it needs a new assumption: `BlockId` currently carries no order at all —
  not even `DecidableEq` outside the few files that need it. Any fixed rule
  serves (a `LinearOrder` on ids, or round-then-tie-break), so this is
  protocol configuration rather than mathematics, but the theorem cannot be
  stated without choosing one.

  **No retraction is already done**, and it needed no ordering assumption —
  which is the point. Retraction is about *whether* and *when* a block is
  output, not about its position within a flush, so none of it touches an
  order on ids:

  - `ledgerSet_mono` — nothing already output is ever dropped;
  - `ledgerSet_agree` — two validators output the same blocks;
  - `outputAt_unique` and `outputAt_agree` — each block enters at exactly one
    slot, and validators concur on which.

  Together: a block, once written, stays written, in the same place. That is
  closer to what a ledger's users rely on than abstract sequence equality,
  and it means the outstanding ordering assumption affects only the arrangement
  *inside* each flush.

- **T7 — Liveness.** Under partial synchrony, leaders eventually get
  committed. Needs timing/network axioms, not just DAG structure — an
  explicit decision to include or drop, not an oversight.

## 5. Open questions

1. Weak edges (§3.1) — include now or defer?
2. Leader selection — round-robin, stake-weighted, or left abstract as an
   arbitrary function? Note M1–M3 and M5 need no leader function at all
   (M5 is stated as "same round, same creator"), so this only bites at
   M4/M6, together with the slot schedule and its `≥ 3` spacing.
3. Is Phase 3 (total order, liveness) in scope, or is M6 the practical
   finish line?
4. Should ids be assumed collision-free (`U.block` injective on `U.ids`),
   modeling a content hash? Currently *not* assumed, so the theorems stay
   maximally general. Revisit only if a proof demands it.

## 6. Layout

- `LeanDag/Validators.lean` — §2 (all five fault-counting consequences), T0
- `LeanDag/Block.lean` — §3.1 (`Block`), §3.2 (`creatorsOf`, `creators`,
  `ValidWrt`), T0', and `nonempty_of_creatorsOf_card_pos` (a quorum of
  authors needs a nonempty id set — used in three files)
- `LeanDag/BlockDag.lean` — §3.3 (universe), §3.5 (`View`), T1, and
  `BlockUniverse.exists_common_mem_of_quorums` (two quorum-backed sets of
  round-`n` blocks share a block — the "peel off one certification layer"
  step)
- `LeanDag/CausalHistory.lean` — §3.4, T2, T6a
- `LeanDag/Support.lean` — `blocksAt`, `authorsAt`, `supporters`,
  `correctSupporters`, `blames`, the hitting/propagation/coverage lemmas
  (§4 *Coverage*), and the counting fact that a quorum of blamers caps
  supporters below a quorum. The whole "who backs what" layer: Mysticeti's
  *voters* are exactly `supporters` at the following round, and its *blames*
  are the complement.
- `LeanDag/Persistence.lean` — T3
- `LeanDag/CommonCore.lean` — `correctBlocksAt`, T3a and T3c (Phase 1b)
- `LeanDag/Mysticeti.lean` — the whole of Phase 2: the vote/certificate
  machinery and M1–M3, M5′, M5 (Stage A); the slot schedule, `DirectCommitIn`
  and the `Decided` relation (C1); the view-relative lifts (C2); M4 and M6
  (C3–C4). Plus the Phase 3 fragments that need no ordering assumption:
  `commitSeq` and the `ledgerSet` / `OutputAt` no-retraction results.
- `LeanDag/Commit.lean` — T4–T5 (Appendix A, unscheduled)
- `LeanDagTest/` — concrete models confirming the definitions are
  satisfiable. Built by default, so a change that empties `ValidWrt` or
  `BlockUniverse` fails the build rather than silently making every theorem
  vacuously true. Worth extending with a model at each new layer.

Imports form a chain down to `Support.lean`, which then branches:

```
Validators → Block → BlockDag → CausalHistory → Support
                                                   │
                                    ┌──────────────┼──────────────┐
                                Persistence   CommonCore     Mysticeti
```

The three leaves are **siblings**; none imports another. T3, T3c and the
Mysticeti rules are all consequences of the same coverage principle,
differing only in how their supporters are obtained — assumed (T3), counted
(T3a), or accumulated a layer at a time (M2).

Parameterizing validity by a lookup function (§3.2) is what keeps this
acyclic: `ValidWrt`, `creatorsOf` and T0' never mention `BlockUniverse` — T0'
quantifies over bare `Finset BlockId`s — so all three sit beside `Block`
instead of being pushed downstream to dodge a circular import.
`BlockDag.lean` is left holding only what genuinely needs the universe: the
structure itself and T1.

**Where the weight is.** Everything through `CausalHistory.lean` is
definitional or near-definitional. `Support.lean` holds the coverage
argument both headline theorems rest on. T3a's double count is the only
proof with substantial machinery, and the only reason `CommonCore.lean`
needs a wholesale `Mathlib` import.

**What Phases 1 and 1b actually require.** Completeness, the predecessor
condition, the creator-set quorum, and non-equivocation — four conditions.
Not distinctness, not views, not view-closure. This holds for Phase 1b too:
T3a takes its `n−f` distinct validators straight from the creator-set quorum,
and coverage runs on correctness plus non-equivocation. So distinctness is
required only at commit agreement (M5′, and T5 in Appendix A), exactly
as §3.2 claims — and that is checkable rather than aspirational.
`distinct_creators` has exactly two consumers: M5′, and `card_creators`
(which feeds only `card_refs`, which nothing calls). Grep for it when in
doubt. If a Phase 1 or 1b proof reaches for distinctness, views, or
view-closure, something has gone sideways.

## 7. Theorem index

Spec label to Lean identifier, for the parts that are built.

| Label | Lean | File |
|---|---|---|
| T0 | `exists_correct_mem_inter` | `Validators.lean` |
| T0' | `exists_correct_mem_creators_inter` | `Block.lean` |
| — | `nonempty_of_creatorsOf_card_pos` | `Block.lean` |
| T1 | `BlockUniverse.eq_of_creator_eq` | `BlockDag.lean` |
| — | `View` | `BlockDag.lean` |
| — | `BlockUniverse.exists_common_mem_of_quorums` | `BlockDag.lean` |
| T2 | `round_le_of_reaches` | `CausalHistory.lean` |
| T6a | `View.mem_of_reaches` | `CausalHistory.lean` |
| T6a (usable form) | `View.exists_reaches_iff` | `CausalHistory.lean` |
| Hitting, `p − 2f` | `exists_mem_refs_of_correct_support` | `Support.lean` |
| Hitting, `f+1` | `exists_mem_refs_of_correct_support_of_card` | `Support.lean` |
| Propagation | `reaches_pred_of_round_le` | `Support.lean` |
| Coverage, `p − 2f` | `reaches_of_correct_support` | `Support.lean` |
| Coverage, `f+1` | `reaches_of_correct_support_of_card` | `Support.lean` |
| — | `blames`, `blames_inter_supporters_subset_byzantine` | `Support.lean` |
| — | `card_supporters_le_of_card_blames` | `Support.lean` |
| T3 | `reaches_of_quorum_support` | `Persistence.lean` |
| T3a | `exists_correct_common_support` | `CommonCore.lean` |
| T3c | `exists_common_correct_ancestor` | `CommonCore.lean` |
| M1 | `not_directCommit_of_directSkip` | `Mysticeti.lean` |
| M2 | `exists_certificate_reaches_of_directCommit` | `Mysticeti.lean` |
| M3 | `certificates_eq_empty_of_directSkip` | `Mysticeti.lean` |
| M5′ | `eq_of_certificates_nonempty` | `Mysticeti.lean` |
| M5 | `eq_of_directCommit_of_creator_eq` | `Mysticeti.lean` |
| M4 | `indirect_agrees_with_direct` | `Mysticeti.lean` |
| M4 (view form) | `certifiedIn_iff_of_view` | `Mysticeti.lean` |
| C1 | `Slots`, `IsLeaderBlock`, `DirectCommitIn`, `Decided` | `Mysticeti.lean` |
| C2 | `directCommit_of_directCommitIn`, `certifiedIn_of_directCommitIn` | `Mysticeti.lean` |
| M6 | `decided_unique`, `decided_agree` | `Mysticeti.lean` |
| M6 (corollaries) | `eq_of_decided_commit`, `not_decided_skip_of_decided_commit` | `Mysticeti.lean` |
| M6 (sequence) | `commitSeq`, `commitSeq_agree` | `Mysticeti.lean` |
| No retraction | `ledgerSet_mono`, `ledgerSet_agree` | `Mysticeti.lean` |
| No retraction | `OutputAt`, `outputAt_unique`, `outputAt_agree` | `Mysticeti.lean` |
| T4–T5 | *(unscheduled, Appendix A)* | `Commit.lean` |

`CommonCore.lean` is the one file importing `Mathlib` wholesale rather than
targeted modules: the counting argument draws on big operators, ordered
sums, pigeonhole and `nlinarith`, and chasing individual module paths cost
more than the build time it saved. Everything else keeps narrow imports.

## Appendix A. Certified DAGs (deferred)

**Not on the roadmap.** Retained because it is of independent interest and
the contrast with Phase 2 is instructive, but nothing below is scheduled.

In DAG-Rider, Bullshark and Narwhal-style protocols a block enters the DAG
only once 2f+1 validators have signed it: **the block is itself a
certificate**. There, "referenced by 2f+1 validators at the next round" is
the entire commit rule, and T5 is its safety proof — the single-level
counterpart of Mysticeti's two-layer rule.

Reading the two together is the point: Phase 2 is what one must do after
giving up the certified-block discipline. T5 and M5 have the same proof
shape, M5 simply running it once per certification layer.

These need views (§3.5) and T6a, which Phase 2 introduces anyway.

- **T4 — Round leaders and the commit rule.** A deterministic
  `leader : ℕ → Validator` (mechanism TBD — round-robin is simplest to
  formalize first). Define **directly committed in a view**:
  `DirectlyCommittedIn U V r i` — note it takes the universe *and* the view,
  since the predicate dereferences ids through `U.block` while quantifying
  over `V` — holds when `i ∈ V` is a round-`r` block by `leader r`, and the
  *support set* `Q := {q ∈ V | (U.block q).round = r+1 ∧ i ∈ (U.block q).refs}`
  satisfies `2 * F.f + 1 ≤ (creatorsOf U.block Q).card`. That is T3's
  hypothesis instantiated at the leader block and evaluated inside `V`.

  The predicate must be **view-relative**: committing is a decision an
  individual validator makes from its own local DAG. Were it universe-level,
  T5 would have nothing to compare.

- **T5 — Commit agreement.** If `DirectlyCommittedIn U V₁ r i₁` and
  `DirectlyCommittedIn U V₂ r i₂` for two complete views of the *same*
  universe `U`, then `i₁ = i₂`. This is *no-conflicting-commit*, not "both
  decide" — a validator whose view lacks the quorum simply has not decided
  yet, which is not disagreement.

  **One uniform proof — no case split on whether the leader is honest.**
  Let `Q₁, Q₂` be the two support sets. Their creator sets are quorums, so
  T0' gives a correct `v` in both. Unfolding, `v` authored some `q₁ ∈ Q₁`
  and some `q₂ ∈ Q₂`, both at round `r+1` and both in `U.ids`; since `v` is
  correct, T1 forces `q₁ = q₂ =: q`. Then `(U.block q).refs` contains both
  `i₁` and `i₂`, which are round-`r` ids with the **same creator**
  (`leader r`, by definition of `DirectlyCommittedIn`). Distinctness (§3.2)
  gives `i₁ = i₂`.

  Note where the leader's honesty would have entered and does not: the
  argument never asks whether `leader r` equivocates, only that `i₁` and
  `i₂` share a creator — which the commit rule guarantees outright. A
  correct leader *also* yields `i₁ = i₂` directly from non-equivocation, but
  that is a shortcut, not a required branch.

    So commit agreement holds even against an equivocating leader, and it is
  **distinctness** rather than non-equivocation that supplies it — the
  one place in the development where that invariant is required.
