# The transformer interface, and what generalising it would take

A design record for work deliberately **not** done in the Hydrozoan
integration arc. `LeanDag/Integration/Hydrozoan/Simulation.lean` states
a transformer interface for one protocol; this document records what a
protocol-generic one would be, and what the second open question —
abstracting the property that skip and fill actually need — would
require. Neither is needed by any theorem now in the repository. Both
are worth doing in their own arc, and the reason to write them down now
is that the material that shows what the abstractions must say is
freshest at the moment the concrete instances are finished.

Nothing here is proved. Section 1 is a record of committed code;
sections 2 and 3 are proposals, and every claim in them is a
conjecture until instantiated.

---

## 1. What exists

`Simulates U V S U' V' S' R Novel` is a structure of thirteen fields
over Hydrozoan's decision relation. Each field names one of the
predicates `Decided` inspects — candidacy, anchor eligibility, the
three direct rules in view, the two rung tests — and the claim the
structure makes is that there are no others. `Simulates.decided` is the
six-constructor induction, done once.

Two parameters carry the variation.

**`R : ℕ → ℕ → Prop`** relates a slot of the source to a slot of the
target. It is a relation rather than a function because the three
directions the arc needs do not share a functional map: the cut
forwards relates `d + k` to `k`, and the cut backwards relates `n` to
`d + n`, which is the same correspondence read the other way. Three
fields govern it — `ord` (order-respecting in both directions), `lift`
(an anchor above a corresponding slot has a corresponding slot above
it), and `drop` (a target slot above a corresponding one has a source
slot). Nothing else about the numbering is used, and in particular no
arithmetic appears.

**`Novel : BlockId → Prop`** names the identifiers the target has and
the source lacks. Two fields say what the graded rungs need of it —
that neither rung reaches a novel candidate. For a cut `Novel` is
empty and both are vacuous; for a fill it is "fresh".

All three of the arc's transport directions are instances, and none
carries an induction of its own:

| Instance | `R n k` | `Novel` | Recovers |
|---|---|---|---|
| `simulates_fill` | `n = k` | `L ∉ U.ids` | `decided_fillHZ` |
| `simulates_chop` | `n = d + k` | `False` | `decided_chopHZ_of_decided` |
| `simulates_chop_bwd` | `k = d + n` | `False` | `decided_of_decided_chopHZ` |

The bespoke proofs in `ChopDecided.lean` and `FillDecided.lean` are
retained: `Stack.lean` and `Liveness.lean` consume them, and
`integration.md` §4.2 prescribes generalising with the old statements
kept as corollaries rather than rewriting working code.

**The limit of this interface is that its field types name Hydrozoan's
predicates.** It abstracts over transformers, not over protocols. That
is what sections 2 and 3 address, from two different directions.

---

## 2. Generalising over protocols

### 2.1 The population

A survey of the repository gives the size of the question. There are
**nine** inductive decision relations:

| Relation | File | Ctors | Direct | Indirect |
|---|---|---|---|---|
| `Decided` (Mysticeti, core) | `Mysticeti.lean:508` | 4 | commit, skip | `CertifiedIn`, skip |
| `Decided` (Odontoceti) | `Odontoceti/Decision.lean:188` | 4 | commit, skip | `ThickLink` + canonicity, skip |
| `Decided` (Nemo) | `Nemo/Decision.lean:158` | 3 | commit | commit, skip |
| `Decided` (MahiMahi) | `MahiMahi/Model/Decision.lean:120` | 4 | commit, slot-level skip | `CertifiedIn`, skip |
| `Decided` (Hybrid) | `Hybrid/Decision.lean:170` | 4 | commit, skip | `ThickLink k` + canonicity, skip |
| `Decided` (Hydrozoan) | `Hydrozoan/Model/Decided.lean:45` | 6 | fast, slow, skip | cert, weak + tie-break, skip |
| `DecidedOpt` (Optimal) | `OptimalHydrozoan/Model/Decided.lean:41` | 6 | fast, slow, skip | cert, evidence, skip |
| `DecidedWithin` (Adaptive/Mysticeti) | `Adaptive/Basic.lean:103` | 4 | as core, bounded by `B` | as core, bounded |
| `DecidedWithin` (Adaptive/Odontoceti) | `Adaptive/Odontoceti.lean:33` | 4 | as Odontoceti, bounded | as Odontoceti, bounded |

Exactly **one**, the core's, has transformer invariance. Hydrozoan is
the second, added by this arc.

Four of the remaining protocols — Odontoceti, Hybrid, MahiMahi and
Adaptive — are stated over the **core** `BlockUniverse Validator
BlockId Payload`, so `chop` and `skipFill` already apply to them
unchanged. For those the transformer exists and only the theorem is
missing. Nemo is the exception: it has its own `Universe` (crash
model, no direct-skip rule), and would need its own transformer, as
Hydrozoan did.

Two further transformers have no verdict-transport theorem for any
protocol: `Integration/ReGenesis.lean` (a validator whose history fell
below the horizon restarts with a reference-free block) and
`SafeSkip/Jump.lean`'s `denote`.

### 2.2 The schema

Every relation in the table has the same skeleton:

- a set of **direct** paths at slot `k`, each a predicate of
  `(U, V, L, slotRound k)` gated by `IsLeaderBlock k L`;
- a **skip** path, likewise, either per-candidate (the core) or
  slot-level (MahiMahi, Hydrozoan);
- an ordered list of **indirect rungs**, each a predicate of
  `(U, A, L, slotRound k)` at an anchor `A` decided at an eligible
  `j > k`, where rung *i* fires only if no candidate satisfies any
  rung below it, some rungs carrying a least-candidate tie-break;
- a **fallthrough** to skip when no rung fires;
- optionally a **slot domain**, a predicate the decided slot and its
  anchor must satisfy.

Each column of the table is a setting of those parameters. Nemo is one
direct path and no direct skip. Odontoceti and Hybrid are one rung
with a tie-break. Hydrozoan is two direct paths and two rungs, the
second with a tie-break. Adaptive is the core's or Odontoceti's
settings with the slot domain `· < B`.

The proposal is to define a `RuleSpec` carrying those parameters, a
generic `Decided` over it, and the simulation theorem against the
generic relation. Each protocol then proves **one** equivalence —
`its Decided ↔ Generic itsSpec` — and inherits transport for every
transformer, present and future.

### 2.3 What it would give, and what it would cost

Give: verdict survival under garbage collection for eight protocols
that have no such theorem; the same under recovery; a route for
`ReGenesis` and `denote`; and the collapse of `integration.md` §3.6's
duplication, where `Adaptive/Odontoceti.lean` repeats 285 of its 362
non-blank lines from `Basic.lean`, `Run.lean` and `Liveness.lean`.
Item B of the Hydrozoan arc — Hydrozoan under Adaptive and Hammerhead
— needs this interface and has no other route that is not a third
hand-written mirror.

Cost, stated honestly: by obligation count the interface loses. Nine
protocols owing thirteen fields each is more than nine bespoke
inductions of four to six cases. What it saves is not the obligations
but the transformer arithmetic threaded through each of them, which is
where the direct route's length actually goes — and the saving is
realised only when a protocol meets its *second* transformer.

### 2.4 Risks

- **The schema is read off the nine relations, not proved of them.**
  The most likely thing to break it is a negative premise not of the
  "no lower rung fired" form. Adaptive's bound was the candidate and
  it fits, as a slot domain; that is one check passed, not a proof.
- **The generic relation must be equivalent, not merely sufficient.**
  Each protocol's equivalence proof is a two-way induction, and it is
  new work, not a re-use of anything existing.
- **Nemo's missing constructor** means the spec must allow an empty
  direct-skip path without that emptiness leaking into the other
  protocols' proofs.
- **`integration.md` §4.2 calls this the most invasive item
  considered**, because it touches existing code rather than adding to
  it. Its own prescription applies: do it as a generalisation with the
  old statements retained as corollaries.
- The interface should be designed against **two** worked instances at
  minimum. Hydrozoan supplied the second for the transformer question.
  For the protocol question there is currently one candidate shape
  with nine settings and no worked generic instance at all.

---

## 3. Abstracting what skip and fill need

Section 2 abstracts over the *rule*. This section abstracts over the
*transformer*, and asks the sharper question: what property of a
transformation makes old decisions stay decided?

The interface of section 1 answers it by listing predicates. That is
an accurate answer and a shallow one — it says "the rule reads these
things, so preserve these things". A semantic answer would say what a
cut and a fill have in common that makes them safe, without naming any
predicate.

Two conditions look sufficient, and `hydrozoan-integration.md` §9
names them:

**Upward locality.** A verdict at slot `k` depends only on the DAG at
rounds `≥ slotRound k`. This is what makes a cut invisible: everything
the truncation removed is below the verdicts it must preserve, and the
indirect rule's recursion runs upward, away from the cut. Note the
recursion is *unbounded* above — the anchor chain has no ceiling — so a
window formulation will not serve; the condition has to be a genuine
lower bound, not an interval.

**Additive inertness.** Blocks that nothing references cannot change a
verdict. This is what SS3 and SS5 already turn on, and what
`not_certifiedInHZ_fresh` proves in the small for Hydrozoan's fill.

Stated together, the target theorem is roughly: *if a transformation
adds only blocks nothing references and removes only blocks below a
round, then every verdict at a slot above that round is unchanged.*
That is the sentence a reader wants, and neither the concrete lemmas
nor the interface of section 1 currently states it.

### 3.1 Why this is harder than it looks

- **Upward locality is a property of the rule, not the transformer**,
  so proving it still requires an induction per protocol — unless
  section 2 lands first, in which case it is one induction over the
  generic relation. The two proposals are therefore ordered: section 2
  is the prerequisite, and doing section 3 alone would give a nicer
  statement over the same nine proofs.
- **The fill is not purely additive in the core arc.** The core's
  `decided_fill` carries a real hypothesis, `QuorateOverGap`, which
  Hydrozoan's `decided_fillHZ` does not need — because Hydrozoan
  counts blame at the *slot* rather than per candidate. So "additive
  inertness" as stated is too strong for one protocol and too weak for
  another, and the interface must carry the difference. `Novel` is the
  crude version of that; the semantic version has to explain why a
  per-candidate skip rule needs a quorum and a slot-level one does
  not.
- **Round-based cuts and slot-based verdicts are different
  orderings.** Everything in the arc's `chop` work threads
  `G ≤ S.slotRound d`, relating the two. A statement of upward
  locality has to fix which ordering it is local in, and the honest
  answer is both, connected by the schedule's monotonicity.

### 3.2 What would count as done

A theorem of the form "`Local` and `Inert` imply verdicts are
preserved", with `chop` and `skipFill` discharged as instances for at
least two protocols, and the concrete lemmas of `ChopDecided.lean` and
`FillDecided.lean` retained as corollaries. Anything less general than
two protocols is the interface of section 1 with more indirection.

---

## 4. Ordering

1. Section 2, the protocol-generic schema, since section 3 depends on
   it to avoid a per-protocol induction.
2. Section 3, the semantic conditions, as the statement layer over it.
3. Item B of the Hydrozoan arc, which section 2 unblocks.

None of this is required by any result in the repository today. It is
recorded so that the next arc starts from the shape rather than
rediscovering it.
