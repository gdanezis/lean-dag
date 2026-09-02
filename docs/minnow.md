# Minnow — the minimal commit rule, and two defects

The design record for `LeanDag/Minnow/`. The report chapter is §19; this
is where the reasoning behind the model lives.

## 1. What the protocol is, and what is modelled

Minnow separates a DAG protocol into a communication component, which
builds a round-based DAG, and a **commit rule**, which reads it and
returns a sequence of committed vertices. `crs*`, the rule for the
eventually synchronous model, commits a leader vertex when a **quorum**
of `2f + 1` distinct processes point to it from the round above, and
every earlier leader slot is **resolved** — some vertex of it lies in the
candidate's causal past, or is concurrent and either committed or
**skipped**, where skipped means `2f + 1` vertices of the round above
carry no edge to it.

The arc models the rule and nothing downstream of it. Every negative
finding is of the form "this leader is not committed", and Definition 4
of the paper says a leader is committed **if and only if** the pattern is
enabled, so the sort, the delivery of non-leader vertices and the
round-advance loop cannot affect any of them.

**Why the DAG type is new.** The rest of this development uses a
`ValidWrt` that requires a non-genesis block to reference a block by its
own author. Minnow does not: section 2 of the paper asks only that
"vertices are valid only if they reference at least `2f + 1` valid
vertices issued in the previous round by distinct processes". Imposing a
self-parent would not be a harmless strengthening — it would force the
faulty process of §5 to point at its own previous vertex, which is one of
the pointers that construction counts. So `Minnow.ValidHere` has exactly
three clauses. `Minnow.Dag` does keep a `correct_single` field — the
core's `no_equivocation` with its correctness guard intact — because
section 2 admits equivocating vertices of *faulty* processes only, and a
correct process issues one vertex a round. Dropping it would admit DAGs
the communication component cannot build.

**Where the paper is ambiguous, the reading is argued rather than
assumed.** Two clauses are written in a way their own sentences do not
support, and §3 settles both. The leader sequence is genuine round robin
rather than one chosen to suit the construction; that choice is recorded
because it could have been made the other way to make a finding look
stronger than it is, and because the value of `l` is what
§5 is about.

## 2. What the counterexamples rest on

Two theorems, read off Definition 9 and proved rather than assumed.
`quorum_of_committedAt`: a commit needs a quorum, at every position in
`leaders`, since the quorum clause is a conjunct at each.
`not_committedAt_of_dead`: if every vertex of an earlier leader slot lies
outside the candidate's causal past, carries no quorum and cannot be
skipped, the second clause is unsatisfiable.

The second is deliberately weak. It concludes nothing about what *is*
committed — only that a particular leader is not — so it cannot be
accused of resolving the recursion in a way the paper would not.

## 3. Two readings, settled

**An empty slot, at the letter, resolves nothing.** Definition 9's second
clause opens "there is a vertex `v′` in slot `s′` in `D` such that …",
and all three ways of resolving a slot sit inside that existential, so a
slot holding no vertex satisfies none of them. That is not the reading to
take: the skip disjunct needs no `v′` at all — it asks that `2f + 1`
vertices of the round above carry no edge into the slot, which an empty
slot satisfies trivially. The model implements the letter because a
formalisation must choose, and `LeanDagTest/Minnow/Deadlock` records what
the letter would cost.

**The skip clause, at the letter, counts vertices where the quorum
clause counts processes.** Two lines apart, Definition 9 asks for "a set
`Q` of `2f + 1` vertices issued by distinct processes" and for "`2f + 1`
vertices that do not have an edge to `v′`". A faulty process issuing
three vertices in one round contributes to the second without giving up
its place in the first, and both clauses then hold of one vertex — so two
processes with different views may commit and skip the same slot, which
is Safe-Commit, and §3.2 of the paper obtains Total-order and Agreement
from Safe-Commit. A reading on which the rule is unsafe is not the
reading meant, so the clause is over processes. `SkippedByVertex` is kept
only to state what the letter costs.

**Neither defect depends on either choice.** The liveness construction
carries no equivocation, so the two counts are the same count throughout
it, and every slot whose resolution matters there holds one vertex. The
safety construction turns on a slot holding two, and both counts leave
the twin undecided — `¬ Skipped Dpart 0` and `¬ SkippedByVertex Dpart 0`,
both checked — while the slot is resolved through the causal-past
disjunct rather than the skip clause.

## 4. The safety defect: one twin resolves a slot the other commits

The first disjunct of the second condition asks only that some vertex of
an earlier slot lie in the candidate's causal past — resolving a slot,
not deciding it. Where the slot's process equivocates it holds two
vertices, and the disjunct is satisfied by whichever is in the way, which
need not be the one later committed. A validator whose view is one short
of a twin's quorum sees that twin undecided, resolves the slot through
the other, and commits a later leader; the missing vertex then arrives
and the twin acquires its quorum, demanding a place before what is
already output. That is Safe-Commit in the form the paper spells out, and
with it Total-order and Agreement.

**Where Lemma 10 fails.** The paper's safety proof ends in a case split,
and this execution is in its second case: `vk` and `vz` concurrent, `vk`
before `vz` in `leaders`, and `Ps*(vk, D)` false — from which the proof
concludes that `vz` is not committed. It is. The inference treats the
second condition as a condition on `vk`, where the rule states an
existential over `vk`'s slot, and the slot holds two vertices. The
proof's opening observation — at most one vertex of a slot satisfies
`Ps*` — is true and is checked on the witness, but it is uniqueness of
the *committable* vertex where the step needs uniqueness of the
*resolving* one. Two further steps of the same proof are unsupported: the
first case commits a leader vertex "by indirect commit", which Definition
9's clause restricts to non-leader vertices, and the step carrying `vk`
into `D` "by the causality of the correct process in common" assumes a
self-parent condition Minnow does not impose.

The equivocation is what does it, and the witness checks the converse: a
slot with one vertex is either resolved by the vertex the rule will
decide, or not resolved at all. Two vertices break the tie between
resolving and deciding. This is the same defect `report.md` §18 finds in
Black Marlin — a slot with two vertices resolved by a test that does not
read support.

## 5. The liveness defect: the dead zone, and the schedule it needs

**The dead zone.** Commit needs `a ≥ 2f + 1` pointing processes; skip
needs `2f + 1` non-pointers, so `a ≤ f`. The window `f + 1 ≤ a ≤ 2f` is
neither, and is non-empty for every `f ≥ 1`.

It cannot be repaired by lowering the threshold. Read the skip clause
over distinct processes with threshold `s`. A view that skips holds at
least `s − f` correct processes with no pointing vertex, and a correct
process issues one vertex a round, so they have none in any view. A view
that commits holds at least `f + 1` correct processes that point. Those
sets are disjoint among the `2f + 1` correct processes, so a disagreement
needs `(s − f) + (f + 1) ≤ 2f + 1`, that is `s ≤ 2f`. So `2f + 1` is the
least safe threshold and the window is forced. A slot in the window is
decided in no view, and no schedule changes that.

**How far a dead slot reaches.** Resolved is not decided, read the other
way round: the first disjunct asks only that some vertex of the slot lie
in the candidate's causal past. A dead vertex has at least `f + 1`
pointers, and a vertex two rounds up references `2f + 1` of the `3f + 1`
below it, so it misses at most `f` and cannot miss them all. From two
rounds up the slot is resolved for everyone. A dead slot therefore blocks
two rounds of leaders and no more.

**Which makes the finding one about the pair.** `Deadlock` sustains the
habit every cycle at `l = 2`, where round robin over four processes puts
the faulty process in a leader slot every other round — the cadence that
keeps a fresh dead slot within reach of every leader — and `crs*` then
commits nothing at all. `Fair` holds that DAG fixed and moves to `l = 1`,
where the same dead slot blocks the round above it and the round after
that commits: `¬ CommittedAt Dm mFair 1 6` against
`CommittedAt Dm mFair 2 11` and `CommittedAt Dm mFair 3 13`, all checked.

So what fails is Live-Commit for `crs*` paired with a multi-leader round
robin. At `l = 1` an adversary cannot deny two consecutive correct leader
rounds: `f` faulty cut the cycle into at most `f` runs of the `2f + 1`
correct, so some run has three. At `l ≥ 2` it always can, for every `f`,
since meeting every window of `2l` positions needs `⌈n / 2l⌉ ≤ f` faulty
at `n = 3f + 1`.

**What that does not rescue.** The paper's Lemma 11 claims each leader
slot is eventually decided, and the dead slot is decided in no view under
any schedule. And the escape runs through the disjunct §4 breaks: what
resolves a dead slot two rounds up is a vertex that will never be
committed. `crs*` is live under a fair schedule by the mechanism that
costs it safety under an equivocating one.

## 6. What is not covered

No attempt is made to prove anything positive about `crs*` in general —
the commit argument of §5 is stated in `report.md` §19.5 and checked only
at `n = 4`, `f = 1` — nor to model `cra*`, the asynchronous rule, nor to
assess the minimality claim of Definition 7 and Theorem 8. Nor is it
settled whether the blocking construction generalises past `n = 4`,
`f = 1`, `l = 2`: denying the fairness window is not the same as blocking
every leader. The sub-rule relation compares patterns, and two of the
four findings above are matters of the pattern's wording rather than of
its strength, so what they bear on is whether `crs*` is a commit rule at
all rather than whether it is a minimal one.
