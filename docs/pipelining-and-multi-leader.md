# lean-dag — Pipelining and multiple leaders

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

A record of extending the safety and liveness results from the single-leader,
three-round-spaced commit rule of `spec.md` and `liveness.md` to the
**pipelined, multi-leader** Mysticeti-C rule actually deployed.

> **Status. Complete for safety and liveness.** Every result of `spec.md` §4 and
> `liveness.md` now holds for a schedule that places a leader in every round, or
> several leaders in one round, or both. The full build reports no errors and no
> warnings, and every principal result depends on exactly `propext`,
> `Classical.choice` and `Quot.sound`.
>
> One assumption was added — `FairRunOn T c`, that the schedule places `c`
> consecutive `T`-led slots arbitrarily far out — and round-robin over the `n`
> satisfies it with `c = 3` for every `f ≥ 1`. Nothing else about the model
> changed: no new synchrony assumption, no change to the vote rule.
>
> Latency is **out of scope**; §10 says what the bounds do and do not deliver so
> that their insensitivity to the number of leaders is not later mistaken for a
> defect. §12 lists what remains, all of it generality rather than goal.
> Statements and file locations are indexed in §11.

**The thesis in one paragraph.** The development was already parametric in the
leader schedule: `Slots` is a class and every theorem takes it as an instance.
Pipelining and multiple leaders per round are, between them, exactly one
weakening of one field of that class — `spacing : ∀ k, slotRound k + 3 ≤
slotRound (k+1)` became `Monotone slotRound`. Five places consumed that field,
only two of them directly. The repair was to stop *deriving* the three-round
separation between a slot and its anchor and start *requiring* it, as a premise
on the indirect constructors — which is what the deployed protocol does anyway.
Safety then went through with no counting redone. Liveness needed one genuinely
new theorem, and getting it right took two false starts (§14).

---

## 1. What the existing development already gave

Most of what follows is assembled from these rather than built. None of them
mentions `Slots`, and none of them changed:

| | |
|---|---|
| **T1** `eq_of_creator_eq` | a correct author has one block per round |
| **T0′** `exists_common_mem_of_quorums` | two reference quorums share a block by a correct author |
| `ValidWrt.distinct_creators` | one block never references two blocks by one author |
| **T2, T3, T3c** | causal history; quorum-backed blocks are unavoidable |
| **M1** `not_directCommit_of_directSkip` | commit and skip are exclusive |
| **M2** `exists_certificate_reaches_of_directCommit` | from round `r+3` on, a certificate is in reach |
| **M3** `certificates_eq_empty_of_directSkip` | a skipped block has no certificate anywhere |
| **M4** `indirect_agrees_with_direct` | where the direct rule decides, the indirect rule agrees |
| **M5′** `eq_of_certificates_nonempty` | at most one certifiable block per (round, author) |
| **L0** `card_authorsAt_of_lt` | the DAG is dense below its frontier |

The three-round structure of the *commit pattern* — proposal at `r`, votes at
`r+1`, certificates at `r+2`, unavoidability from `r+3` — is baked into
`certificates`, `Certifies` and M2, and **none of it changed**. Pipelining does
not shorten the pattern; it overlaps successive copies of it. Worth saying
plainly, because the confusion is common: pipelining gives recurrence, not depth.
A slot is still decided three rounds after its proposal.

The overlap is harmless because *every role is assigned by the reader of
the DAG, not by its writer*. A round-`(r+2)` block was already permitted to be a
certificate for the slot at `r`, a vote for the slot at `r+1`, and a proposal for
the slot at `r+2`, because nothing in `Block` or `ValidWrt` records which of
these it is. Uncertified-DAG modelling is what makes this so: the most conspicuous
feature of pipelining required no change to the model at all.

## 2. The protocol, as specified

From Mysticeti-C (Babel, Chursin, Danezis, Kokoris-Kogias, Sonnino,
arXiv:2310.14821), Algorithms 1–3. Parameters: `waveLength` (3), `roundOffset`,
`numOfProposers` (the paper's §VII sets it to 2).

- `ProposerRound(w) = w·waveLength + roundOffset`, `DecisionRound(w) =
  w·waveLength + waveLength − 1 + roundOffset`. With `waveLength = 3` a slot
  proposed at round `r` has voting round `r+1` and decision round `r+2`.
- `SkippedProposer`: `≥ 2f+1` blocks at `r+1` with no parent by the leader
  (the paper's `2f+1` is our `n−f` at the boundary `n = 3f+1`) —
  this is `DirectSkip` with `blames` at `r+1`.
- `SupportedProposer`: `≥ 2f+1` blocks at `r+2` each of which is a certificate,
  where `IsCert(b, L)` counts `≥ 2f+1` of `b`'s parents voting for `L` — this is
  `DirectCommit` over `certificates U L r`.
- `CertifiedLink(A, L)`: some `b` at the decision round is a certificate for `L`
  with a path from `b` up to `A` — this is exactly `CertifiedIn U A L r`.
- `TryDecide` walks slots downward from the highest round to the last committed
  round, and within a round over proposer offsets, prepending — so the
  `sequence` it builds is in increasing (round, proposer) order.

The clause that mattered is the anchor filter in `TryIndirectDecide`:

```
r_decision ← c.DecisionRound(w)                  -- = r + 2
anchors    ← [s ∈ sequence  s.t.  r_decision < s.round]
for a in anchors:
    if a = ⊥            then return ⊥
    if a = Commit(A)    then return CertifiedLink(A, L) ? Commit(L) : Skip
return ⊥
```

`r_decision < s.round` is `slotRound k + 3 ≤ slotRound s`. **The deployed
protocol does not anchor on the nearest later slot; it anchors on the nearest
later slot at least three rounds ahead**, walking past nearer ones whatever they
decided and stalling only on an undecided *eligible* slot. Under `+3` spacing
every later slot is eligible and the two readings coincide, which is why the
original development could get away with `k < j`. Under pipelining they come
apart, and not cosmetically: slots `k+1` and `k+2` sit at rounds `r+1` and
`r+2`, and a block at those rounds cannot reach a round-`(r+2)` certificate, so
anchoring on them would turn one validator's direct commit into another's
indirect skip. Agreement would fail on the first pipelined commit.

## 3. The two generalisations are one weakening

### 3.1 The class

Slots stay indexed by `ℕ`, as the linearisation of (round, proposer offset) that
`TryDecide` already builds. Then **pipelining** is `slotRound (k+1) = slotRound k
+ 1` and **multiple leaders** is `slotRound (k+1) = slotRound k` for the slots
sharing a round. Both are instances of `Monotone slotRound`:

```lean
class Slots (Validator : Type*) where
  slotRound : ℕ → ℕ
  leader    : ℕ → Validator
  mono      : Monotone slotRound
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  keyed     : Function.Injective (fun k => (slotRound k, leader k))
```

`mono` replaces `spacing`.

`unbounded` was previously the theorem `3 * k ≤ slotRound k`, derived from
`spacing`. Under `mono` alone it is underivable — a schedule parking every slot
at one round is monotone — and liveness needs it, so it is assumed. Pipelining
and every bounded-spacing schedule imply it.

`keyed` says distinct slots differ in round or in leader. It too held
automatically under the
single-leader spacing, which made `slotRound` injective outright. Under multiple
leaders it is a real condition: the proposers of a round must be distinct
validators. Without it one block would be the candidate for two slots and the
ledger would deliver it twice (§8). §3.2 moves it somewhere checkable.

### 3.2 `Slots.uniform` — what a reader writes

`Slots` is the right *interface*, since every theorem downstream indexes slots by
`ℕ`, but nobody wants to write a pair of functions out of `ℕ` with three side
conditions. Every deployed schedule is **uniform** — `m` leaders in every `p`-th
round — and that case has a closed form:

```lean
@[reducible]
def Slots.uniform (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (elect : ℕ → Validator)
    (hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂) :
    Slots Validator                       -- slotRound k = p * (k / m)

@[reducible]
def Slots.uniformSingle (p : ℕ) (hp : 0 < p) (elect : ℕ → Validator) : Slots Validator
```

`mono` is monotonicity of division, `unbounded` holds since `slotRound (m·n) =
p·n ≥ n`, and `keyed` is `hblock` — equal slot rounds force `k₁ / m = k₂ / m`
because `p > 0`, and then equal leaders force equality. `hblock` says only that
the `m` proposers of a round are distinct, and round-robin `elect k = k % n`
satisfies it whenever `m ≤ n`. With one leader per round it is vacuous, which is
what `uniformSingle` exploits via `Slots.one_hblock`.

| | `p` | `m` | `slotRound k` | |
|---|---|---|---|---|
| the original schedule | 3 | 1 | `3k` | `uniformSingle_spacing` recovers the old field |
| pipelined, one leader | 1 | 1 | `k` | |
| pipelined, `m` leaders | 1 | `m` | `k / m` | the deployed rule |

Proving the three class fields once inside `uniform` is what keeps them out of
every instance, and that ordering is not cosmetic: the old `spacing` field was a
`∀ k` statement `by omega` discharged instance-locally, whereas `unbounded` and
`keyed` are an existential and an injectivity statement that `omega` will not
touch.

### 3.3 Conservativity

`uniformSingle 3` is the schedule the development had before pipelining, and two
results say the generalisation lost nothing:

- `Slots.uniformSingle_spacing` — its consecutive slots really are three rounds
  apart, so the single-leader schedule is an instance of the weakened class;
- `eligible_of_lt_of_spacing` (§5) — under that condition every later slot is an
  eligible anchor, so the revised `Decided` offers exactly the constructors the
  old one did. No derivation available before the change is unavailable after it.

### 3.4 Irregular schedules — not built

A schedule given as an arbitrary assignment of validators to rounds is **not**
covered. It would need a per-round primitive with `Slots` derived from it:

```lean
structure Schedule (Validator : Type*) where
  leaders : ℕ → List Validator
  nodup   : ∀ n, (leaders n).Nodup
  cofinal : ∀ n, ∃ m, n ≤ m ∧ leaders m ≠ []
```

A `List`, not a `Finset`: when a round has several leaders their slots commit in
a definite order and that order reaches the ledger, so a `Finset` would have to
recover the order with a `LinearOrder` on `Validator`. Empty lists are how "a
leader every third round" is said. `nodup` would give `keyed` and `cofinal` would
give `unbounded`, both becoming theorems rather than assumptions. Slot `k` is the
`k`-th entry of `leaders 0 ++ leaders 1 ++ ⋯`, so the derivation needs partial
sums and `Nat.find` plus a characterisation lemma.

This is generality, not goal: `uniform` covers every deployed schedule and every
witness here. See §12.

## 4. Where the three rounds were required

Every occurrence, from a sweep of the source, with what became of it:

| Site | Consumed | Outcome |
|---|---|---|
| `Mysticeti.slotRound_add_three_le` | `spacing` | **deleted** — it is exactly the fact that stopped being true |
| `Mysticeti.certifiedIn_of_directCommitIn` | the above | **premise change**: takes `Eligible` instead of deriving it |
| `Liveness.le_slotRound` | `spacing` | **replaced** by `Slots.unbounded`, surfaced as `exists_slotRound_ge` |
| `Liveness.commits_recur_on` | both | **reproved** against `unbounded` and `mono` |
| `Quantitative.commits_recur_within` | both | **restated** — see below |

Only two sites consumed `spacing` directly; the other three routed through those.

`commits_recur_within` needed its *statement* changed, not merely its proof. It
quantified over `max k R`, mixing a slot index and a round index in one `max`,
which is meaningful only when `slotRound R ≥ R` — precisely the coincidence
`spacing` supplied. Under a monotone schedule the first slot at or after a round
has to be named, so `Liveness.slotAt` was added (`Nat.find` on `unbounded`, with
`le_slotRound_slotAt` and `slotAt_zero`), and both quantitative theorems now read
`max k (slotAt Validator R)`. Under the single-leader schedule
`slotAt R ≤ R`, so no bound weakened.

`BoundedSpacing`, which bounds slot rounds from *above*, still compiles and is
untouched. Nothing in `Block`, `BlockDag`, `CausalHistory`, `Support`,
`Persistence`, `CommonCore` or `Timing` mentions `Slots` at all.

## 5. The repair: eligible anchors

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

instance decidableEligible (k j : ℕ) : Decidable (Eligible Validator k j)
theorem eligible_iff : Eligible Validator k j ↔ S.slotRound k + 3 ≤ S.slotRound j
theorem lt_of_eligible (h : Eligible Validator k j) : k < j
theorem eligible_of_lt_of_spacing (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k+1))
    (h : k < j) : Eligible Validator k j
```

Stated through `decisionRound` rather than as a bare `+ 3` so that a later
wavelength parameter is a change to one definition. `Validator` is explicit
because the result is a bare `ℕ`, so nothing else would fix it. The `Decidable`
instance is declared explicitly, as `IsLeaderBlock`, `DirectCommitIn` and
`DirectSkipIn` all are, so that `decide`-checked witnesses elaborate.

`lt_of_eligible` makes the `k < j` premises of `Decided` redundant — under `mono`
an eligible anchor is a later slot. They are kept anyway: `decided_unique`
recurses on them and hands them to `lt_trichotomy`.

The revised relation, with the two changes marked:

```lean
inductive Decided (U) (V : View …) : ℕ → Option BlockId → Prop
  | directCommit  … unchanged …
  | directSkip    … unchanged …
  | indirectCommit {k j A L} :
      k < j → Eligible Validator k j →                                    -- NEW
      Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) → -- RESTRICTED
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  | indirectSkip {k j A} : … the same two changes …
```

Both edits are forced, for opposite reasons.

Adding `Eligible k j` is forced **by safety**: without it the engine lemma has no
round hypothesis and agreement fails, as §2 describes.

Restricting the intermediate quantifier to eligible `i` is forced **by
liveness**: `Decided V i none` for the ineligible `i ∈ {k+1, k+2}` is not
something a validator can wait for, those slots being routinely *committed*, so
under the unrestricted premise slot `k` would never be decidable at all.

Recursive occurrences stay **strictly positive**: `Eligible` is a predicate on
two naturals and does not mention `Decided`, which was the reason the
intermediate premise was stated positively in the first place.

## 6. Safety

### 6.1 Unchanged

M1, M2, M3, M5′ and M5 are stated at the round level over `certificates U L r`
and never mention `Slots`. So is **M4 in both halves**:
`certifiedIn_of_directCommit` already took `r + 3 ≤ (U.block A).round` as an
explicit hypothesis rather than deriving it from the schedule, and
`not_certifiedIn_of_directSkip` needs no round hypothesis at all. *That* is why
the repair was a premise change and not a reproof: the safety core was already
written against the round separation, and only the slot layer above it assumed
the schedule would supply it.

`directCommit_of_directCommitIn`, `directSkip_of_directSkipIn`,
`certifiedIn_iff_of_view`, `not_directSkipIn_of_directCommitIn`,
`eq_of_directCommitIn`, `not_certifiedIn_of_directSkipIn`,
`certificates_nonempty_of_*` and `eq_of_hasCertificate` compiled untouched.

### 6.2 The engine, re-premised

```lean
theorem certifiedIn_of_directCommitIn
    (h : DirectCommitIn U V L (S.slotRound k))
    (hA : A ∈ U.ids) (hAr : (U.block A).round = S.slotRound j)
    (helig : Eligible Validator k j) :        -- was (hkj : k < j)
    CertifiedIn U A L (S.slotRound k)
```

The body lost its appeal to `slotRound_add_three_le` and feeds `helig` to
`certifiedIn_of_directCommit` directly — strictly a simplification. Every call
site is inside `decided_unique`, and each has an `Eligible` premise in hand from
the constructor it just destructured.

### 6.3 Agreement (M6), and why the induction survives

The central claim, and it held exactly as predicted. `decided_unique` is a
structural induction over sixteen constructor pairings; fifteen close on Stage A
and were unaffected. The real case is *indirect commit at `k` with anchor `j`*
against *indirect skip at `k` with anchor `j₂`*, settled by
`lt_trichotomy j j₂`:

- `j < j₂` — the other validator's intermediate premise at `j` now demands a
  third argument, `Eligible k j`, **which is precisely the new premise carried by
  the first validator's own derivation**. Available verbatim, no transport.
- `j = j₂` — unchanged: the IH identifies the anchor blocks.
- `j > j₂` — symmetric, using the other side's eligibility.

The design constraint this imposes: **`Eligible` is a predicate on the pair
`(k, j)` alone**, not on any view. Both derivations concern the same slot `k`, so
the two validators agree on which slots may anchor it, and each one's eligibility
premise is exactly the side condition the other's intermediate premise requires.
Had eligibility been view-relative — "an anchor I can see far enough ahead" — the
premises would not meet and the induction would have nothing to stand on. This is
the same discipline that forced `CertifiedIn` to be universe-level, arriving from
a different direction.

`decided_agree`, `eq_of_decided_commit` and `not_decided_skip_of_decided_commit`
follow as corollaries.

Exactly three proofs touch the indirect constructors, and two match positionally:
`decided_mono` builds them, `isLeaderBlock_of_decided` destructures them, and
`decided_unique` does both. Everything else that mentions `Decided` uses only
`directCommit` and `directSkip`.

### 6.4 Schedule faithfulness

```lean
theorem slot_eq_of_isLeaderBlock (h₁ : IsLeaderBlock U k₁ L) (h₂ : IsLeaderBlock U k₂ L) :
    k₁ = k₂
theorem slot_eq_of_decided_commit (h₁ : Decided U V₁ k₁ (some L))
    (h₂ : Decided U V₂ k₂ (some L)) : k₁ = k₂
```

Under the single-leader spacing these held automatically, `slotRound` being
injective, so a block's round named its slot. Under multiple leaders they
are what `keyed` supplies. The
second is the shape the ledger wants: a committed block belongs to one slot.

## 7. Multiple leaders, specifically

Three things could have gone wrong and, on inspection, did not.

**Certificate uniqueness across co-round slots.** M5′ concludes `L₁ = L₂` from
equal creators, and its proof runs through `ValidWrt.distinct_creators`: a common
correct voter's single round-`(r+1)` block references both candidates, which
distinctness forbids unless they coincide. Two slots in the *same round with
different leaders* have different creators, so M5′ does not apply to them and
does not need to — they are different slots and may both commit. Two candidates
for the *same* slot have the same creator by `IsLeaderBlock`, which is the
hypothesis M5′ wants. The proof is indifferent to how many slots share a round.

This is also where the model's `L ∈ (U.block q).refs` vote rule is what the
argument needs.
The paper implements votes through `SupportedBlock`, a depth-first traversal
returning the first block for the slot encountered, precisely so that its Lemma 4
holds. `ValidWrt.distinct_creators` discharges the same obligation structurally,
one layer down, and per-author rather than per-slot — which is what makes it
insensitive to the number of leaders in a round.

**Skip counting.** `DirectSkip U L r` counts round-`(r+1)` blocks omitting `L`,
per candidate block. Candidates for different co-round slots are counted
independently: a voter that references leader 0's block but not leader 1's blames
the latter and not the former.

**Self-anchoring.** A slot cannot anchor itself, nor can a co-round slot anchor
it: `Eligible` needs a strict three-round gap, which co-round slots fail by
construction. Under the old `k < j` premise a co-round slot *would* have
qualified — another way to see that `k < j` was never the right condition, only
an adequate proxy under `+3` spacing.

## 8. The ledger and total order

`commitSeq`, `ledgerSet`, `OutputAt` and their four theorems are stated over
`g : ℕ → Option BlockId` and the slot order on `ℕ`, so they are agnostic to how
slots map onto rounds and carried over unchanged. What they rely on is that the
linearisation of (round, proposer) into `ℕ` is fixed and identical for all
validators, which it is, being a function of the public schedule.

`keyed` — via `slot_eq_of_decided_commit` — is what stops a block appearing twice
in `commitSeq` at two slots. Without it `outputAt_unique` still holds, `OutputAt`
taking the *first* slot, but the delivered sequence would repeat a block: a
total-order defect the existing statements do not see.

The within-commit ordering problem is unchanged in character: committing a leader
releases its whole causal history, and the blocks inside one flush remain
unordered for want of a `LinearOrder` on ids. Multiple leaders make the flushes
more frequent and smaller; they neither help nor hinder here.

## 9. Liveness

### 9.1 Carried over unchanged

L0 (density), L1 (`no_stall`), L2 (`decided_mono`), L3 (`decided_full`), L7
(`synchronised_of_delivery`), the `Delivery` layer and all of `Timing` are
round-level and slot-free. L4 (`directCommit_of_leader_mem`,
`decided_of_leader_mem`) and L5 (`decided_none_of_leader_absent`) are stated at a
single slot and consume its three rounds being populated and synchronised; they
never consumed `spacing`. All compiled untouched.

L6 (`commits_recur_on`, `commits_recur_within`) was reproved against `unbounded`
and `mono` as described in §4. `FairScheduleOn` and `FairWithin` are conditions
on `leader` and needed no change.

`exists_eligible` — every slot has an eligible anchor somewhere — is immediate
from `unbounded` at `slotRound k + 3`. Small, but it is what stops the
restriction of §5 from being vacuously unsatisfiable: under a schedule that
stalled at some round, a slot the direct rules left undecided could never be
settled at all.

### 9.2 What liveness actually required

**Commits recurring is not the ledger advancing.** L6 gives infinitely many
commits while saying nothing about the gaps between them, and `commitSeq` reads
verdicts in slot order and halts at the first undecided slot. So one permanently
undecided slot withholds delivery of everything above it. The paper keeps this
backpressure deliberately (§III-C). Closing it is what §9.3–§9.5 do.

Two facts frame the problem, and separating them is essential.

**A Byzantine-led slot can be permanently undecided by the direct rules, and no
synchrony assumption repairs that.** At `f = 1`, `n = 4`: the leader hands its
candidate to exactly one correct validator, moments before that validator builds
its round-`(r+1)` block. The candidate then collects two votes — one short of the
three a certificate needs — and two blames, one short of a skip. Rounds `r+1` and
`r+2` are fixed sets of blocks, so neither count ever grows again.

No stronger delivery assumption helps. A *correct* validator's round-`n` block is
built at round pace and sent at once, so with bounded drift and a timeout
exceeding `Δ` every correct validator holds it before building round `n+1` —
which is what `EventuallyDelivers` states and what makes it derivable. A
Byzantine leader chooses its send times, so it can always place a block inside
the window where one correct validator has it and the others have already built.
The authorship clause in `EventuallyDelivers` is therefore **faithful**, and an
assumption covering Byzantine-authored blocks would be one a real adversary
violates.

**But an undecided slot does not stall the ledger.** The indirect rule is *total
given a committed anchor*: a certificate either lies in the anchor's causal
history or it does not, so the outcome is a commit or a skip, never a third
thing. Undecidedness is never the rule failing to answer; it is the canonical
anchor not being available. Two reasons it may not be:

- *A skipped slot cannot anchor.* The test searches the causal history of the
  anchor **block**, and a skip carries no block. So "resolved at round `r+3`" is
  not enough — the anchor must be *committed*.
- *The anchor must be canonical, because anchors genuinely disagree.* A
  certificate sits at round `r+2`, and a round-`(r+3)` block's references are all
  at `r+2`, so it reaches that certificate only by referencing it — and it
    references a quorum (`n−f`) of them, not all. One committed anchor may see it
  and another
  may not. Hence the *first* committed eligible slot is fixed as the anchor, and
  to know a slot is first, every eligible slot below it must be known **skipped**
  — not merely "not yet decided", since a slot undecidable now may commit later
  as a view grows. That gap between *undecided* and *skipped* is the
  backpressure, and it is why Algorithm 3 returns `⊥` on an undecided eligible
  anchor.

### 9.3 The escape

Under pipelining slot `k`'s eligible anchors are exactly the slots at round
`slotRound k + 3` and beyond, and **nothing strictly between `k` and there is
eligible at all**. So take the case that looks fatal: slot `j − 1` immediately
below a committed `j`. It cannot anchor on `j`, which sits one round on, inside
its decision round. But if `j + 2` is committed then `j + 2` is eligible for
`j − 1`, and the eligible intermediates in `(j − 1, j + 2)` are the `i` with
`j − 1 < i < j + 2` *and* `i ≥ j + 2` — **empty**.

```lean
theorem decided_of_first_eligible_commit
    (helig : Eligible Validator k j)
    (hfirst : ∀ i, k < i → i < j → ¬ Eligible Validator k i)
    (hj : Decided U V j (some A)) : ∃ v, Decided U V k v
```

The intermediate premise is vacuous and the slot resolves at once, with no
induction. This is the fact that keeps pipelining live.

### 9.4 A committed run decides everything below it

```lean
theorem decided_below_of_committed_run {b n : ℕ}
    (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided U V i v
```

No synchrony, no timing, no fairness, no hypothesis on the schedule. Two changes
from the special case `decided_of_committed_above` make it go through. The anchor
is the nearest **eligible** committed slot rather than the nearest committed one.
And an eligible intermediate is shown to lie *below `b`*: were it in `b … n` it
would be committed by `hrun`, contradicting minimality — which is what lets the
induction hypothesis reach it.

That second step explains why three consecutive commits suffice where one does
not. The slots just below `b` have no eligible intermediates at all, their
eligible range beginning inside the run, so they resolve outright by §9.3;
everything lower descends onto them.

**`hspan` is the whole difference between the two schedules**, and it is one line
each in `LeanDagTest/Pipelined.lean`:

| schedule | `hspan` holds with | commits needed |
|---|---|---|
| `uniformSingle 3` (`slotRound k = 3k`) | `n = b` | **one** |
| `uniformSingle 1` (`slotRound k = k`) | `n = b + 2` | **three consecutive** |

Three is exactly right and two will not do: `Eligible (b−1) (b+1)` is false, slot
`b−1`'s certificates sitting at round `b+1`. That is checked too.

### 9.5 L10 — the ledger does not stall

```lean
def FairRunOn (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T

def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)

theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ Correct) (hcard : 2 * F.f + 1 ≤ T.card)
    (hspan : SpansEligible c) (fair : FairRunOn T c) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ U D N, Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v
```

`FairRunOn` is the one genuinely new assumption: `FairScheduleOn` promises a
single `T`-led slot and this needs a *run*. It refines `FairScheduleOn`
(`FairRunOn.fairScheduleOn`), so nothing proved from the older condition is
disturbed. Every slot of the run is `T`-led, hence directly committed by L4,
which discharges `hrun`.

**Round-robin satisfies it with `c = 3` for every `f ≥ 1`**, whatever the `f`
Byzantine validators are and wherever they sit in the rotation: they cut the
cycle into at most `f` arcs holding at least `n−f ≥ 2f+1` correct slots
between them, so some arc has at least `⌈(2f+1)/f⌉` slots, and
`(2f+1)/f = 2 + 1/f` makes that ceiling `3` for all `f ≥ 1`. Three is exactly what
pipelining asks for — a coincidence
rather than a design. The concrete case, four validators with one Byzantine and a
run at `4k+1, 4k+2, 4k+3`, is `pipe_fairRun`, and `Pipelined.lean` instantiates
L10 at that schedule: both schedule hypotheses discharged, leaving only the
DAG-and-network hypotheses L4 and L6 already require.

The quantifier order is L6's, for L6's reason: the run is named by the schedule
before any DAG is mentioned, and any DAG grown past it decides everything below.
Reversing the order would let the horizon cap how far fairness may reach.

**This is what "the ledger does not stall" means operationally.** A prefix of
decided slots growing without bound *is* the ledger advancing.

### 9.6 The obstruction, for completeness

A stall is possible only under an adversarial *leader schedule*, and that is a
theorem rather than an observation:

```lean
theorem notMem_stuck_of_decided {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, Eligible Validator i j → (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ Eligible Validator i i')
    (h : Decided U V i v) : i ∉ X
```

`X` is *stuck*. Induction on the derivation: direct commit and indirect commit
both produce a certificate and die on `hcert`; direct skip dies on `hskip`; and
indirect skip hands back a strictly smaller sub-derivation at a slot `hregress`
places back inside `X`. Derivations are finite trees, so the descent cannot
continue.

`hcert` is the half-published candidate. `hskip` requires a candidate to *exist*
and not be skippable — a slot whose leader published nothing is skipped
vacuously, so a stall genuinely needs a leader that speaks to some correct
validators and not enough of them. `hregress` requires commits to be *isolated*,
with no three consecutive: with three available, §9.3 gives a vacuous
intermediate range and the clause fails. Fair round-robin therefore excludes it,
by §9.5.

`stuck_empty_below_commit_of_spacing` composes this with `decided_of_committed_above`
to show neither is vacuous: under the single-leader spacing a stuck set has no
member at or
below a committed slot, however the DAG is arranged.

Not supplied: a concrete universe satisfying `hcert` and `hskip`, which would be
a `U7`-sized model in which a candidate collects exactly `2f` votes and `2f`
blames. See §12.

## 10. Latency — out of scope

**The goal is that pipelined and multi-leader Mysticeti be safe and live.**
Latency is not part of it. This section records what the existing bounds say only
so that their insensitivity to the number of leaders is not later mistaken for an
unnoticed defect.

The per-slot commit depth is unchanged: proposal at `r`, votes at `r+1`,
certificates at `r+2`, unavoidable from `r+3`. Pipelining does not touch this and
cannot; it is the width of the commit pattern.

`commits_recur_by_round` bounds the committing slot's round by
`slotRound (max k (slotAt R)) + s·w + 2` for `BoundedSpacing s` and
`FairWithin T w`. Pipelining takes `s` from 3 to 1. **Multiple leaders do not
improve this bound**: `BoundedSpacing s` says `slotRound (k+1) ≤ slotRound k + s`,
and under `m` leaders per round consecutive slots either stay in the round or
advance it by one, so `s` is still `1`, not `0`, and `s·w` still reads `w` rounds
for `w` slots. The bound is loose by exactly the factor of interest, and
`BoundedSpacing` cannot see it. A bound that improved with `m` would come from
`Slots.uniform`'s closed form as `slotRound (k+w) ≤ slotRound k + p·⌈w/m⌉` — a
computation, needing no new hypothesis. It is not done, and is not needed.

Two things worth stating rather than proving. The improvement pipelining does yield
is in *recurrence*, not *latency*: a transaction still waits three rounds from
the block carrying it to the commit of a leader referencing it. And it is not
free under attack — more slots means more slots left undecided by the direct
rules when leaders are slow, which is the backpressure of §9.2, mitigated in the
paper by keeping `numOfProposers` small.

## 11. What is in the code

**Schedule layer** — `LeanDag/Mysticeti.lean`, `LeanDag/Schedule.lean`:

| | |
|---|---|
| `Slots` | `slotRound`, `leader`, `mono`, `unbounded`, `keyed` |
| `decisionRound`, `Eligible`, `decidableEligible` | the anchor filter |
| `eligible_iff`, `lt_of_eligible` | its two basic facts |
| `eligible_of_lt_of_spacing` | conservativity: old spacing ⇒ every later slot eligible |
| `Slots.uniform`, `Slots.uniformSingle`, `Slots.one_hblock` | `m` leaders every `p` rounds |
| `uniform_slotRound`, `uniform_leader`, `uniformSingle_slotRound` | closed forms |
| `Slots.uniformSingle_spacing` | `uniformSingle 3` satisfies the old field |

**Safety** — `LeanDag/Mysticeti.lean`:

| | |
|---|---|
| `certifiedIn_of_directCommitIn` | M6's engine, re-premised on `Eligible` |
| `Decided` | eligible anchors; intermediate premise restricted |
| `decided_unique`, `decided_agree` | **M6**, reproved |
| `eq_of_decided_commit`, `not_decided_skip_of_decided_commit` | its usable shapes |
| `slot_eq_of_isLeaderBlock`, `slot_eq_of_decided_commit` | a block belongs to one slot |

**Liveness** — `LeanDag/Liveness.lean`:

| | |
|---|---|
| `exists_slotRound_ge`, `slotAt`, `le_slotRound_slotAt`, `slotAt_zero` | the first slot at or after a round |
| `exists_eligible` | every slot has an eligible anchor |
| `commits_recur_on`, `commits_recur` | **L6**, reproved |
| `decided_of_first_eligible_commit` | the escape (§9.3) |
| `decided_of_committed_above`, `all_decided_below_of_spacing` | the `helig` special case |
| `decided_below_of_committed_run` | a committed run decides everything below (§9.4) |
| `FairRunOn`, `FairRunOn.fairScheduleOn`, `SpansEligible` | the run conditions |
| `all_decided_below_of_fairRun`, `…_correct` | **L10** (§9.5) |
| `notMem_stuck_of_decided`, `stuck_empty_below_commit_of_spacing` | the obstruction (§9.6) |

`LeanDag/Quantitative.lean` carries the restated `commits_recur_within` and
`commits_recur_by_round`.

**Witnesses** — `LeanDagTest/Pipelined.lean`, three `local instance` schedules so
they never meet:

- *pipelined* (`uniformSingle 1`): `¬ Eligible 0 1`, `¬ Eligible 0 2`,
  `Eligible 0 3`; `pipe_not_eligible_between`, `pipe_eligible_add_three`;
  `pipe_hspan`, `pipe_spansEligible` (`c = 3`); `pipe_fairRun`; and L10
  instantiated at the schedule;
- *multi-leader* (`uniform 1 2`): co-round slots `0` and `1` at round `0` with
  distinct leaders, `¬ Eligible 0 1` for a co-round slot, slot `6` the first that
  qualifies;
- *spaced* (`uniformSingle 3`): `a < b ↔ Eligible a b`; `spaced_hspan`,
  `spaced_spansEligible` (`c = 1`).

Plus two facts about `keyed`: that `Slots.uniform`'s `hblock` argument is
*unprovable* for a schedule giving one validator two slots in a round, so such a
schedule cannot be built at all; and that at one leader per round the condition
is free, which is what `Slots.one_hblock` records. A concrete `commitSeq` with a
repeated element is *not* exhibited — the construction is excluded upstream
rather than caught downstream.

An axiom audit covers eighteen results, new and reproved.

`LeanDag/WaveRobin.lean` frees the pipelined pair of the committee: the
wave-aligned rotation `waveRobin` — pipelined, the leader holding for a
three-slot wave before the rotation advances — satisfies `FairRunOn Correct 3`
and `SpansEligible 3` at *every* `n` and every fault configuration, with no
premise beyond the fault model. One correct leader's wave is a full correct
3-run by itself, so fairness needs only `Correct.Nonempty`, where per-slot
rotation would need the pigeonhole argument recorded on `FairRunOn`.
`LeanDagTest/WaveRobin.lean` pins the wave shape at `Fin 4` and instantiates
L10 with no schedule hypothesis left.

The existing instances in `LeanDagTest/{Model,Growth,Quantitative}.lean` were
rebuilt through `uniformSingle 3`. One practical note: `uniform` puts `k / m`
where a literal round used to be, so `rfl` proofs of `slotRound k = 3 * k` stop
working — `k / 1` is not definitionally `k` — and three test lemmas moved from
`rfl` to `simp`. Anyone adding a schedule should reach for a `@[simp]` closed
form immediately.

## 12. What remains

None of it is required by the goal.

**Irregular schedules (§3.4).** `Schedule` and `Schedule.toSlots`, so that "an
arbitrary assignment of validators to rounds works" becomes a theorem rather than
a family of examples. Separable — nothing above needs it. Budget for index
arithmetic (partial sums, `Nat.find`, a characterisation lemma) rather than for
anything conceptual, and expect an irregular witness with `decide`-checked
`slotRound` and `leader` values.

**A concrete stuck universe (§9.6).** A `U7`-sized model in which a Byzantine
leader's candidate collects exactly `2f` votes and `2f` blames, which would turn
`notMem_stuck_of_decided`'s hypotheses from assumptions into an exhibited
configuration. Note no *fair* schedule can satisfy `hregress`, so this witnesses
the obstruction's reachability under an adversarial schedule only.

**The `m`-sensitive bound (§10).** Optional, and explicitly not a goal.

**Documentation.** `spec.md` needs `Eligible`, `keyed`, and what the schedule
layer assumes; `report.md` needs §3.4 (the slot schedule), §3.5
(`Decided`), §6 (the liveness chain), §9 (requalify the limitations) and §10
(the module table and axiom audit). Both are deliberately untouched here.

**A wavelength parameter.** The paper parameterises `waveLength`, defaulting to
3, and the whole development hard-codes it through `certificates` (round `r+2`)
and M2 (round `r+3`). `Eligible` is stated through `decisionRound` so that a
later generalisation is a definition change rather than a search for the numeral
`3`, but M2's `r+3` would be the hard part.

## 13. Settled

**The commit pattern does not change.** Three rounds, `certificates` at `r+2`,
M2 tight at `r+3`. Pipelining overlaps waves; it does not shorten them (§1).

**Roles need no modelling work.** A block being a proposal, a vote and a
certificate at once was already expressible, roles being reader-assigned (§1).

**The deployed rule anchors on eligible slots, not on the next slot.** Confirmed
against Algorithm 3: `anchors ← [s ∈ sequence s.t. r_decision < s.round]` (§2).

**Pipelining and multi-leader are one weakening.** `spacing` becomes `mono`; five
sites consumed it, only two directly (§3.1, §4).

**M4 already took its round hypothesis explicitly**, which is why the repair was
a premise change rather than a reproof (§6.1).

**`Eligible` must depend on `(k, j)` only.** A view-relative eligibility would
break M6 (§6.3).

**Restricting the intermediate quantifier is required, and safe.** Required
because slots `k+1`, `k+2` are routinely committed; safe because the trichotomy
argument only ever compares eligible anchors (§5, §6.3).

**M5′ is indifferent to co-round slots**, running through
`ValidWrt.distinct_creators`, which is per-author and does the work the paper's
`SupportedBlock` traversal does (§7).

**The ledger layer is slot-order-generic** and needs `keyed` — and only `keyed` —
to stay faithful under multiple leaders (§8).

**One constructor covers every deployed schedule.** `Slots.uniform p m` gives
`slotRound k = p * (k / m)` (§3.2).

**A Byzantine-led slot can be permanently undecided by the direct rules, and no
synchrony assumption repairs it.** Byzantine blocks have no send time pinned to
the round structure, so `EventuallyDelivers`' authorship clause is faithful
rather than weak (§9.2).

**That does not stall the ledger.** Nothing between a slot and three rounds on is
eligible to anchor it, so the slot below a commit reaches past it with a vacuous
intermediate premise. A stall needs isolated commits, which fair round-robin
excludes (§9.3, §9.6).

**Pipelining's cost to ledger-advance is one number**: `SpansEligible` holds at
`c = 1` under three-round spacing and `c = 3` under pipelining, and round-robin
supplies three for every `f ≥ 1` (§9.4, §9.5).

**Liveness needs one new schedule assumption**, `FairRunOn T c`, which refines
`FairScheduleOn` (§9.5).

## 14. Two wrong turns, recorded

Both concerned the liveness property of §9.2, and each was a distinct kind of
error. They are kept because the residue was live in this document for a while.

**Treating it as arithmetic.** The property was first proposed as "after `R`
every slot is decided", with the difficulty assumed to be how much eligibility
slack to add to a `w`-slot walk. Slack is not the issue: the anchor must be
*committed*, which is a property of the DAG and not of the schedule. Correct
response, and it produced `decided_of_committed_above` and
`notMem_stuck_of_decided`.

**Concluding that pipelining loses the property.** This inference took "slot
`j − 1` cannot anchor on `j`" and jumped to "so it must reach the next commit",
overlooking that `j + 1` and `j + 2` are ordinarily committed too and that
nothing between `j − 1` and `j + 2` is *eligible*. The error was reasoning about
the anchor while forgetting that eligibility also prunes the intermediates. What
it produced — §9.3 — became the core of the real theorem.

A third correction belongs with them. It was proposed that `SynchronisedOn`'s
authorship clause was a modelling weakness, to be repaired by a `CoversOn`
covering Byzantine-authored blocks. That is withdrawn: no such assumption is
derivable, for the reason in §9.2, and the argument it carried for adopting the
paper's `SupportedBlock` traversal goes with it. What survives is unrelated to
liveness — `L ∈ refs` is a coarser vote rule than the DFS traversal, and if
equivocation handling is ever wanted for its own sake, that is where to look.
