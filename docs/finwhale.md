# FinWhale — the fast path, and what its safety proof consumes

The design record for `LeanDag/FinWhale/`. The report chapter is §20;
this is where the reasoning behind the model lives.

The protocol is Ladelsky and Friedman, *FinWhale: An Optimally Resilient
Two-Round Terminating DAG Protocol*, arXiv:2606.26292v2 (18 August 2026).
Lemma and theorem numbers below are that version's.

## 1. What the protocol is, and what is modelled

FinWhale is Mysticeti with a fast path. The DAG and the slow-path commit
rule are Mysticeti's, in the form Starfish corrects; the addition is a
**fast path** that commits a leader block two message delays after it is
proposed, and the structures that let a validator combine the two paths
without a validator on the slow path disagreeing with one on the fast
path.

The arc models the decision layer: block validity, votes, FP-evidence,
SP-certificates, the direct commit and skip rules, the anchor, and the
reverse pass that turns them into a verdict per leader slot. It models
neither the timers nor the delivery of non-leader blocks; the network and
the round-advance loop enter only as §10's schedule, over which the
protocol's own block-creation conditions are read. Every result is about
which leader slots are committed and which blocks are delivered in what
order.

**References sit one round below, which the paper does not require.** Its
block structure gives a block "`n` edges to the latest blocks created by
distinct validators in rounds up to `r − 1`", of which at least `n − f`
are in round `r − 1`; `ValidHere.predecessor` asks that *every* reference
be at `r − 1`. That is the core's convention throughout this development
rather than a choice made here, and it strengthens validity: the results
below hold of fewer DAGs than the paper's rule admits. Every count the
commit rules take is over round-`(r+1)` or round-`(r+2)` blocks, so the
dropped edges carry no votes and no certificates, but a faithful model
would admit them.

**Why the DAG type is new.** FinWhale strengthens Mysticeti's validity
rule with a clause about the leader two rounds down (§2), and the fast
path's counting rests on it. `FinWhale.ValidHere` and the core's
`ValidWrt` each have four clauses and share three: where the core's
fourth is the self-parent edge, FinWhale's is the leader clause.
`FinWhale.Dag` keeps a
`correct_single` field — one block per correct validator per round — as
the core does, because equivocating blocks are admitted of faulty
validators only.

The two rules are not ordered: FinWhale adds the leader clause and drops
the self-parent edge, which the core requires and the paper's block
structure has. Both differences vanish under the denial-of-service
condition of `dos-equivocation-and-growth.md`. `DoSValid` — a block may
not cite an author its own causal history convicts of equivocating — is
the leader clause with three of its narrowings removed: every author, at
unbounded depth, permanently. `DoSBridge.lean` proves the implication
(`leaderClause_of_dosValid`) and builds the DAG (`Dag.ofDoSValid`), so a
DoS-valid `BlockUniverse` is a FinWhale DAG at any leader schedule, with
the self-parent edge included. It is strictly stronger than what FinWhale
specifies — the protocol admits a DAG citing an equivocating non-leader —
so this says what a deployment over a DoS-protected DAG gets, not what
the paper's model gives.

**And on the reactive schedule it is live.** `Run.ofDoSValidReactive`
takes such a universe together with a `ReactiveM` over it, at one slot
per round under a round-robin schedule, and returns a `Run` — so
`commits_of_reactive` supplies the liveness input and the four guarantees
of §12 hold of it. Nothing in the statement is bounded above: it is
universal in the horizon, so every correct-led slot between the
stabilisation round and `N` commits, at every `N`, and §10's rotation
result makes correct-led slots recur.

**The two disciplines do not collide, and the reason is specific to this
route.** A reactive builder's citation obligations are confined to
reliable authors — `ReactivePace.vote_or_wait` is guarded by the leader
being reliable, `ReactiveM.cert_or_wait`'s fallback by the author being
in `T` — and a correct validator is never exposed (`citable_of_correct`,
which is the DoS arc's `ExposedIn.not_correct` read for this purpose). So
nothing the schedule requires is anything the condition forbids. The
block-creation discipline of §10 has no such guard: `selects_votes`
obliges a builder to reference a block by the author of *any* held vote,
reliable or not, and that clause and `DoSValid` are not jointly
satisfiable where a convicted equivocator votes for a reliable leader.
Composing through `commits_of_creation` would need the selection clause
guarded and the certificate confined to its witnesses first; through
`commits_of_reactive` it needs neither.

**And the composite cannot become vacuous.** It is inhabited where
equivocation is live — §9's equivocating execution satisfies both
conditions at once — and `quorumCard_le_citable` is why no height can
exhaust it: an exposed author has equivocated, hence is Byzantine, hence
one of at most `f`, while the correct validators are never exposed and
number at least `n − f`. So the authors a block may cite always include a
validity quorum. The margin is nil rather than small: at exactly `f`
Byzantine validators the citable authors are the `n − f` correct ones and
no others, so every one of them must be cited — which turns the question
from what may be cited into what has arrived, and that is what the pacing
structure supplies past GST.

## 2. The committee, and where the numbers come from

`Params` fixes `p` with `1 ≤ p ≤ f` and `n + 1 = 3f + 2p`, stated
additively so that `omega` never meets a truncated subtraction. Three
quantities follow, and the arc keeps them apart:

`p` is a threshold parameter, not a second class of fault. There is one
fault set here, `Faults.byzantine`, bounded by `f`; `p` never partitions
it. Safety assumes nothing about `p` — `lemma4` takes a fast commit and
the standing bound `|byzantine| ≤ f` and holds however many validators
actually failed. Only fast-path liveness assumes `|byzantine| ≤ p`
(`fastCommit_of_reactive`), as a counting step: the correct validators
all vote past GST, there are `n − |byzantine|` of them, and that clears
`n − p` exactly when `|byzantine| ≤ p`. Above `p` failures the fast path
stays sound and does not fire. So `p` counts missing round-`(r+1)` votes
whatever their cause — a crash, a withheld vote, a vote for a conflicting
block — since the threshold counts distinct authors that did vote and
does not ask why the rest did not.

| Quantity | Value | Where it is used |
|:---|:---|:---|
| `quorumCard` | `n − f` | block validity: how many parents a block carries |
| `spQuorum` | `2f + p` | the slow path: certificates, votes, the skip rule |
| `fastCard` | `n − p` | the fast path: votes for a fast commit |

`spQuorum_eq_ceil` checks that `2f + p` is the paper's
`⌈(n + f + 1)/2⌉`. The three are ordered `spQuorum ≤ quorumCard ≤
fastCard` (`spQuorum_le_quorumCard`, `quorumCard_le_fastCard`), and
neither inequality is strict in general: at `p = 1` the
slow-path quorum and the validity quorum coincide, and at `p = f` the
validity quorum and the fast-path threshold do. The witnesses of §7 use
`p = 2` with `f = 2`, where the first inequality is strict.

## 3. Where the paper is read one way rather than another

Three readings are argued rather than assumed.

**Validity's leader clause is about what parents reference.** The paper
asks that a block's parent set be *leader-consistent* with respect to the
leader two rounds down, or exclude that leader's block. Leader-consistency
is a condition on the round-`r` blocks the parents vote for, not on who
authored the parents. Writing it over the parents' authors would make the
clause say something the fast path's counting does not support:
`leader_not_parent_of_exposes` needs the *exclusion* half to be about
authorship and the *consistency* half to be about references, and both
are stated that way in `ValidHere.leader_clause`.

**"Exposes equivocation" has two glosses, and they agree here.** The
paper writes that a round-`(r+2)` block exposes equivocation if "its
parent set is not leader-consistent, i.e., its causal history contains
multiple conflicting versions of the leader's block". At this depth the
two coincide: the block's parents sit at round `r + 1` and their
references at round `r`, so the round-`r` blocks in its causal history are
exactly what its parents vote for, and validity gives each parent at most
one edge per validator, so no single parent votes for two versions.
`ExposesEquivocation` is the parent-set form, which is the one validity
constrains.

**Lemma 4's proof names the wrong round.** Its equivocating case says the
block "does not reference the `r − 1` block of the Byzantine leader". The
parents of a round-`(r+2)` block are round-`(r+1)` blocks, and the block
excluded is the leader's block of round `r + 1`. The count the argument
uses — at most `f − 1` Byzantine parents — is what `parents_byzantine_lt`
states, and is unaffected.

## 4. Lemma 4, and why the committee is tight

Lemma 4 is the fast path's safety statement: if `n − p` distinct
validators vote for a leader block `b` of round `r`, then *every*
round-`(r+2)` block is FP-evidence for `b`. Both branches of the
FP-evidence definition are reached, and `Counting.lean` is the arithmetic
of each.

- A block that has not seen the equivocation carries `n − f` parents and
  meets the correct voters — at least `2f + p − 1` of them, by
  `honest_voters` — in `f + p − 1` validators (`nonequivocating_voters`).
- A block that has seen it may not reference the equivocating leader, so
  at most `f − 1` of its parents are Byzantine. Its correct parents number
  `n − 2f + 1`, of which at most `p` fail to vote (`honest_nonvoters`),
  leaving `f + p` voting for `b`, and at most `f + p − 1` voting for any
  conflicting block (`equivocating_voters`, `conflicting_voters_le`).

`equivocating_margin` is the tightness: at `n = 3f + 2p − 1` the
equivocating branch reaches exactly `f + p`, the threshold the definition
asks for, and at one validator fewer it reaches `f + p − 1`, one short,
for every `f` and `p` in range. The committee is the least at which
Lemma 4 holds.

`honest_voters` is stated as `2f + p ≤ |voters ∩ Correct| + 1` rather
than as a subtraction, for the same reason as `Params`.

## 5. The skip rule, and where correctness is genuinely consumed

The direct skip rule has two halves: a quorum of round-`(r+1)` validators
declining to vote for every block of the slot (`SPSkip`), and a quorum of
round-`(r+2)` blocks that are FP-evidence for nothing in the slot
(`NonFPEvidence`). Lemma 6 says a commit and a skip cannot both happen,
and the two halves need different arguments.

The slow-path half (`no_skip_of_quorum`) meets a quorum of voters and a
quorum of non-voters in `f + 1` validators and needs one of them to be
correct, since a correct validator's round-`(r+1)` block either references
the leader block or does not.

The fast-path half (`no_skip_of_fpEvidence`) meets a quorum of
FP-evidence blocks and a quorum of Non-FP-evidence blocks. Here the
counts are by *author*, and a distinct author is not enough: a Byzantine
author may write one block of each kind and satisfy both counts with no
contradiction. The argument needs a *correct* author, whose single
round-`(r+2)` block cannot be FP-evidence for `b` and for nothing at
once. That is the one place in the skip argument where correctness rather
than distinctness is consumed.

Lemma 7's fast-path premise is `no_nonFPEvidence_of_fastCommit`: under a
fast commit every round-`(r+2)` block is evidence for the committed
block, so none is evidence for nothing, and the skip rule's second
condition is unsatisfiable whatever the first says.

Lemma 9's third case — no round-`(r+2)` block is FP-evidence for a block
conflicting with a fast-committed one — is proved from the two branches
of the FP-evidence definition (`not_fpEvidence_conflicting`), not from
Lemma 4. The slow-path twin (`not_fpEvidence_of_spCertificate`) reads an
SP-certificate as a count of parents voting and runs the same case split.

## 6. The anchor, and why a deterministic tie-break is safe here

The indirect rule decides a slot from a committed **anchor** above it:
the anchor either reaches an SP-certificate for a block of the slot or
reaches a quorum of FP-evidence blocks for one. The paper notes that both
may hold at once for conflicting blocks and resolves the choice
"according to a deterministic rule".

That is the shape of the defect the Black Marlin arc reports (report
§18): a support-blind deterministic choice among an equivocator's blocks.
FinWhale escapes it, for two reasons that are separate.

**The rule is decidable, on a block of the DAG.** `ReachesFrom` is a
reflexive transitive closure and settles nothing by computation, so
`IndirectCommitOn` states the same condition over `historyFrom` — the
same relation as a `Finset`, computed from the references with the round
as its fuel. `indirectCommitOn_iff` is the equivalence, for an anchor of
the DAG, and it is what lets a model check the indirect rule rather than
exhibit a path through it.

**The tie-break's input is the anchor's causal history and nothing else.**
`IndirectCommit` is a predicate of the anchor, the slot and the candidate;
no view occurs in it. A validator holding the anchor holds everything the
anchor reaches, since views are closed under references
(`indirect_view_independent`), so two validators that commit the same
anchor feed the same data to the same rule. Black Marlin's descent failed
because its two validators descended from *different* anchors.

**The pattern arises only where nobody could decide directly.** A direct
commit of `b` rules out an indirect commit of a conflicting `b′` by either
path (`no_indirectCommit_of_directCommit`), and a direct skip rules out an
indirect commit outright (`no_indirectCommit_of_directSkip`).

The converse direction is Lemma 7's indirect half: a direct commit leaves
a trail every anchor at round `r + 3` or above reaches
(`indirectCommit_of_directCommit`), so the rule always has a candidate to
name. Under the slow path this is Lemma 3 (`reaches_spCertificate`);
under the fast path it is Lemma 5, proved at any height by descending to
round `r + 3` first (`reaches_round`) and applying Lemma 4 to the parents
there. `reaches_fpEvidence_quorum` gives the paper's `n − f` count at
every height, where the paper's own proof justifies it only at `r + 3`;
`reaches_fpEvidence_spQuorum` weakens it to the `2f + p` the indirect
rule reads.

## 7. Lemma 12, and the interface it consumes

Lemma 12 — two validators never decide a leader slot differently — is
where the model has to be careful, because the two validators evaluate
the direct rules on *different views*.

`WellFormed` is the reverse pass as a condition on a verdict assignment
rather than as a procedure, and it takes the direct rules as parameters:
`dcommit r l` is "this validator sees a direct commit of `l` at `r`", and
`dskip r` likewise. `choose` — the deterministic tie-break — is shared,
because it reads only the anchor and the round. Giving both validators
the same direct predicates would make the theorem trivial.

What two views must satisfy against each other is the shared anchored
relation's `Laws` (`LeanDag/Common/Anchored.lean`), discharged for FinWhale
in `View.lean` (`finWhaleLaws`): the commit is unique across views, a
commit in one bars a skip in the other, a direct commit is linked from
every eligible anchor and is the only block the tie-break can choose
there, a direct skip bars every link, two choices agree, and the direct
rules grow with the view. Each is one of the DAG-level theorems, under
the reading that a view is a sub-DAG, so a direct verdict in a view is a
direct verdict of the universe (`directCommit_restrict`), with the skip
rule's growth (`directSkip_mono`) the one law FinWhale owes on its own.
Lemma 12 is then the relation's agreement, and `decided_of_wellFormed`
is what brings the pass under it: every verdict of a well-formed
assignment is a derivation of the relation.

**The pass is a procedure, not only a condition.** `Pass.lean` defines
it: `slotVerdict` decides one slot from the verdicts above it — a direct
commit if there is one, a direct skip if there is one, and otherwise the
first slot above `r + 2` that is not skipped, read through the tie-break
— and `passFrom` threads that down from the horizon, where nothing is
decided, to slot `0`. `decOf` is the result, a function of the DAG and
the tie-break.

`wellFormed_decOf` proves the five fields of it, off one equation:
`decOf_eq`, that at or below the horizon a slot's verdict is
`slotVerdict` applied to the pass itself. Two of the conditions the
capstones carried are discharged with it — `mem_slotBlocks_of_decOf`,
that a committed verdict names a block of its slot, and `decOf_of_gt`,
that nothing above the horizon is decided, which is the finiteness Lemma
12 consumes. `safety_of_pass` is the capstone with those gone: two
validators running the pass on their own views deliver prefix-comparable
sequences, and nothing is assumed about their verdicts. What is left of
the three is `hk`, how far each sequence runs, which is a choice of
horizon that §10's `all_decided` settles. §12 states the result without
any of them.

`choose` is abstract in all of that, and it need not be.  `chooseLeast`
picks the least candidate in the identifier order and satisfies
`ChooseSound` — it names only blocks the anchor could indirectly commit,
and names one whenever there is one. The paper resolves the choice
"according to a deterministic rule" and gives none; this is one.

The induction is the paper's maximality argument, made downward-explicit.
Both DAGs are finite, so nothing above some `N` is decided, and the proof
runs on the distance from `N`. At each slot either a direct rule fires,
and the exclusions settle it, or both validators decided from an anchor.
The second case is what the induction is for: two differing anchors
would put a slot above `r` that one validator skips and the other
commits, which the induction hypothesis forbids (`anchor_unique`).

## 8. From one slot to the sequence

`commitSeq` is a validator's committed leader sequence: the committed
blocks of its decided slots, in slot order. Lemma 13 is that two such
sequences are prefix-comparable.

`linearise` is the delivery order: walk the leader sequence and after each
leader append the blocks of its causal history that have not been
delivered. Theorem 14 is that a longer leader sequence extends the
delivery order rather than revising it, because `linearise` only appends;
Theorem 15 is that no block is delivered twice, because each leader
appends only what the accumulator does not already hold. §12 composes
Lemma 12, Lemma 13 and Theorem 14 into one statement about two
validators of one run.

The list a leader contributes is its causal history: `histOf` is
`historyFrom` sorted by identifier, `mem_histOf` says it lists everything
the leader reaches, and `nodup_histOf` that it lists each once. The paper
asks only for "a deterministic sort", and those two facts are all
Theorems 15 and 26 read; sorting by identifier is the cheapest function
of the block with them, and `nodup_delivery` is Theorem 15 at it.

## 9. The witnesses

`LeanDagTest/FinWhale/Model.lean` settles every definition by `decide` on
concrete executions before anything is proved from it. The committee is
`f = 2` and `p = 2`, so `n = 9`, the slow-path quorum is `6`, validity
asks for `7` parents and the fast path for `7` votes; at `p = 1` the first
two coincide and the gap between them would go untested.

Three executions, because the rules exclude one another.

- `Dfast`, four rounds: the round-0 leader block is committed by both
  paths, every round-2 block is FP-evidence for it (Lemma 4 on data), and
  a round-3 block reaches a certificate in one step. The indirect rule is
  settled there by `decide`, through the decidable form of §6, and a
  round-2 block is shown not to be an anchor for its own slot.
- `Dequiv`, three rounds and a second round-0 block by the Byzantine
  leader: neither version is committed or skipped, and the two branches of
  FP-evidence separate — block `18` has seen both versions and carries the
  `f + p = 4` parents the equivocating branch asks for, block `19` has
  seen one and falls under the branch asking `f + p − 1 = 3`, and block
  `20` has seen both and carries too few of either. Validity forces block
  `18` to drop the leader's own round-1 block, which is
  `leader_not_parent_of_exposes` on data.
- `Dskip`, three rounds: no round-1 block references the leader, all nine
  validators decline, and no anchor can reverse the skip.

A fourth, `Dsync`, is a synchronised execution: three rounds in which
every block references the whole round below. The round-0 leader is
correct there, and its slot is committed by both paths. The rotation is
exercised too: `fwLeader` is a `RoundRobin`, and Lemma 22 names a correct
triple in the window from round `0`.

The pass runs on those executions: `decOf` commits slot `0` of `Dfast`
and skips slot `0` of `Dskip`, both through its own well-formedness
rather than by evaluation — the pass recurses down from the horizon,
which the kernel does not unfold — and decides nothing above the horizon.

The reverse pass has its own witness too, on verdicts rather than
blocks:
slots `3` to `5` committed directly, `1` and `2` skipped directly, and
slot `0` decided indirectly from its anchor, which the model shows is
slot `3` and nothing else. `WellFormed` is discharged for it field by
field, and Lemma 23 is then applied to that triple.

Views have one too: a reference-closed part of `Dequiv` that holds one of
the leader's two blocks and not the other, where the slot has two blocks
in the universe and one in the view. Beside it, that no block of that
execution cites both versions — the fact behind §10's selection guards,
by `decide` and again through `not_refs_conflicting`.

`LeanDagTest/FinWhale/Pace.lean` carries the liveness results down to a
schedule. FinWhale's smallest committee is `f = 1` and `p = 1`, which is
`n = 4` — the committee the development's own pacing witnesses are built
over — so `Ugrow N` is a FinWhale DAG at any leader schedule once the
leader clause is checked, and every block there references the whole
round below.

Five things run on it. The same execution carries a `ReactiveM` at one
leader per round, where both wait clauses hold by their exit and neither
fallback is needed. It carries a `Creation` with two triggers in play —
validator `3` catches up by C3 on blocks of its own round, everyone else
builds by C1 — so both interesting cases of §10's derivation are
exercised, and `commits_of_creation` yields the liveness interface with
no coverage assumption anywhere. `fastCommit_latency` runs at `δ = 2`,
and the self-parent chain carries validator `1`'s genesis block into its
own round-`1` block. And `fwRun` assembles the lot into a `Run`, which
§12 reads its properties off. The bridge of `Liveness.lean` is exhibited
separately, as production and coverage over the correct validators and
nothing further.

`LeanDagTest/FinWhale/Equivocation.lean` is the composite of §1 on data,
and the one execution here where the DoS condition is active. Sixteen
blocks over four rounds at `n = 4`: validator `0` equivocates at round
`0`, the round-`1` blocks split over the two versions, and a round-`2`
block citing two of them reaches both — so blocks `10`, `11` and `12` are
*exposed* to the equivocator and may not cite its round-`1` block, though
validity would otherwise admit it. Block `9` has seen one version only
and cites it, which is what makes the prohibition a property of the
citing block rather than of the author. All by `decide`.

The reactive structure exists over that execution, and this is what the
bridge's claim comes to: both wait clauses hold by their first disjunct,
because every correct validator's block references every correct
validator's block of the round below, and the clauses never mention the
equivocator. The round-`1` leader's block is committed by both paths —
four validators vote for it, and each round-`3` block carries a slow-path
quorum — so the equivocation costs the execution nothing.
`Run.ofDoSValidReactive` closes over it.

That run reaches round `3`, which carries the liveness interface and is
short of the `3f + 5` window `Run.agreement` asks for; non-vacuity of the
four properties is witnessed on the tall execution above, which in turn
cannot show this, nothing equivocating in it.

The list layer is exercised on concrete verdicts: a commit sequence, its
extension, and the delivery order that repeats a block of two causal
histories and delivers it once.

## 10. Liveness

Liveness asks three things of the schedule and the network: that correct
validators keep producing blocks, that what they produce reaches each
other, and that a correct leader's block is then voted for and certified.
Lemmas 16 and 17 establish the second from `∆` and the `2∆` timeout. This
arc does not prove them — timeouts and message delivery are not modelled
— and what stands in their place is `PaceCore`, the development's model
of a schedule and a network: `converges`, that a validator's holdings
reach every other within `delay` past GST; `advances` and `catchup`, the
pacemaker's progress rules; and, on the creation route below,
`holds_built` and `builds_distinct`. Everything above those is derived.

**The schedule is reactive.** FinWhale creates a round-`r` block when any
of three conditions holds: **C1**, the local DAG has the round-`(r−1)`
leader's block together with a quorum of voters for the round-`(r−2)`
leader (or an SP-skip pattern for it); **C2**, the `2∆` timeout has
expired; **C3**, the local DAG has `n − f` round-`r` blocks. The timeout
is the fallback, not the rule, so the discipline is `ReactivePace`, whose
`deadline` is a ceiling on waiting, rather than `ViewPace`, whose `waits`
is a floor. One consequence shapes the rest: **reference coverage is
unavailable**. A reactive builder omits whatever had not arrived when its
exit fired, so `SynchronisedFrom` is false in general and nothing below
uses it.

**Lemmas 18 and 19 come from the conditions themselves.** `Creation.lean`
records which condition created each block and derives both.

- **C1** holds the leader's block by its own L1, and a quorum of voters
  by L2. L2's other branch, an SP-skip pattern, is refuted by Lemma 18: a
  quorum declining to vote for a correct leader would have to be
  Byzantine, and `f < 2f + p`.
- **C2** waited the full timeout, and the drift bound places every
  reliable block of the round below in hand before the build
  (`holds_of_timeout`). This is the argument coverage would have
  supplied, made about one block instead of all of them.
- **C3** holds `n − f` blocks of the round it is building. Those meet the
  reliable validators in two or more, so one of them is a reliable
  validator other than the builder, which built strictly earlier.
  Induction on build time makes its block a vote, and a DAG closed under
  references holds whatever that block cites.

`Creation.lemma18` and `Creation.lemma19` are the results, the second by
the same induction one round up. What stays assumed of the algorithm is
parent selection — `selects_leader` and `selects_votes` — which the paper
states for C1 and uses for all three.

Both selection clauses are guarded, and the guards are not decoration. A
clause obliging a builder to reference every version of the leader's
block it holds is satisfiable by no valid DAG, since `distinct_creators`
admits one reference per author (`not_refs_conflicting`); unguarded, it
would make every execution with an equivocating leader — which is every
execution the safety half is about — vacuous. So `selects_leader` asks
only for a *reliable* leader's block, which is one block by
`correct_single`, and `selects_votes` asks not that a held vote be a
parent but that some parent by the same validator votes, which is what
the certificate counts. The C3 case departs from the paper's, which runs through the
fastest `n − 2f` honest validators; §13 gives the off-by-one in that
count and what it costs, which the induction does not have.

**Lemma 20 and Theorem 21 follow by counting.** `Creation.lemma20`
assembles the certificates: every reliable validator's round-`(r+2)`
block certifies a reliable leader's block, and they number
`n − f ≥ 2f + p`. `Creation.theorem21` is the fast path — where at most
`p` validators are actually Byzantine, the reliable validators number
`n − p`, and their votes alone are a fast commit.

**Two routes, one interface.** `CommitsCorrectLeaders` is where liveness
meets the decision layer: every correct-led slot below the horizon
carries a slow-path commit *whose certificates are reliable validators'
blocks*. The certificates are named rather than only their existence,
because a validator's view has to see them, and what a view can be shown
to hold is what reliable validators produced. `SeesCommits` is the form
Lemma 23 consumes — the deciding validator sees a direct commit at every
correct-led slot — and `sees_of_commits` and `sees_of_commits_of_held`
supply it for a validator reading the whole universe and for one reading
its own holdings. `commits_of_creation` is the route above.
`commits_of_reactive` takes `ReactivePace`'s wait clauses as given
instead — that a block either votes or waited the timeout out, which is
what Lemmas 18 and 19 conclude — and reuses the core's reactive
certificate stage unchanged. That reuse rests on an arithmetical accident
worth naming: **Mysticeti's certificate is FinWhale's SP-certificate**,
since the slow-path quorum `2f + p` is no larger than the validity quorum
`n − f` (`spCertificate_of_certifies`). Lemma 23 and everything above it
consume the interface and never learn which route produced it.

**Definition 1's latency.** Theorem 21 establishes that the fast commit
exists; Definition 1 claims it happens within two message delays. The
reactive schedule is where the second can be said, because its exit is
not bounded below by the timeout. `fastCommit_latency` gives both at
once: under `δ`-propagation past GST the votes are built within
`Δ + δ + 2·proc` of round entry — the collapsed spread, one delivery, two
processing steps — with the timeout nowhere in the bound.
`no_timeout_of_fast` is its companion: where actual delivery undercuts
the timeout, the fallback branch is never taken.

**Lemma 22, and where its proof stops working.** The lemma says any
window of `3f + 3` rounds contains three consecutive rounds with correct
leaders. The paper's proof counts maximal runs of correct leaders in the
cyclic order, then observes that such a window "contains a full cycle of
`n` rounds plus the first two rounds of the next cycle". That step needs
`3f + 3 ≥ n + 2`, and at `n = 3f + 2p − 1` it holds only for `p = 1`. The
difference `3f + 3 − n` is `4 − 2p`, independent of `f`: the window is a
cycle plus two rounds at `p = 1`, exactly one cycle at `p = 2`, and
`2p − 4` rounds short of one at `p ≥ 3`. So from `p = 2` up there is no
such decomposition to read off, and the argument does not apply.

The statement is true at every `p`, by two arguments rather than one.
`three_correct_of_roundRobin` is the cyclic half and gives a triple
within any `n + 2` rounds; it counts incidences rather than runs, which
avoids reasoning about maximal runs: if every cyclic triple held a
Byzantine leader, each Byzantine validator would answer for at most three
of the `n` triples, so `n ≤ 3f`, against `3f + 1 ≤ n`. This half uses the
fault bound alone, not `Params`. `three_correct_window` is the pigeonhole
half, for `3f + 3 ≤ n`: the window then lies inside one cycle, so its
leaders are distinct, and `f + 1` disjoint triples would need `f + 1`
distinct Byzantine validators. `lemma22` is the paper's statement, by the
first argument at `p = 1` — where `3f + 3` is exactly `n + 2` — and the
second at `p ≥ 2`.

The core's `FairRunOn` records the pigeonhole for runs of three as prose
rather than proving it, and `WaveRobin.lean` supplies runs of three by
rotating in waves instead. `three_correct_window` is that pigeonhole,
proved, for the round-robin schedule.

**Lemma 23 is a statement about one DAG, not about time.** The paper
reads it as "after GST any undecided slot eventually gets decided", where
eventually means in a later and larger DAG. Written that way it would
contradict the finiteness Lemma 12 consumes: nothing above some `N` is
decided in a DAG that stops. What holds of a single DAG is the content of
the argument, and `lemma23` states it — a slot below a committed triple
is decided. Growth enters through the hypothesis instead: a larger DAG
carries a triple further up, and every slot below it is decided.

The proof is the paper's maximality argument with the maximum made
explicit. If some slot below the triple were undecided, take the highest
such (`Nat.findGreatest`). Everything above it up to the triple is then
decided, so the first non-skipped slot above it is a commit, which is its
anchor, and `WellFormed.indirect_commit` decides it — a contradiction.
The triple is what covers the three offsets: the anchor must sit above
`r + 2`, so for a slot within two of the triple's start only its later
members qualify.

`committed_triple` supplies the triple from the interface above: Lemma
22 names three consecutive correct leaders, and each of their blocks is
directly committed. One hypothesis carries the growth there — `hsees`, that a direct
commit of the universe is a direct commit of this validator's view. Read
the other way it says the certificates have arrived, which is the
"eventually" of the paper's statement. `all_decided` composes the two,
and covers the slots before `R` as well: only the triple has to sit past
it, since the reverse pass decides everything below.

**Theorems 24, 25 and 26.** With every slot decided, Lemma 12's
agreement becomes equality: `theorem24` says two validators deliver the
*same* sequence at a common horizon, not merely comparable ones, and
`agreement_of_commits` composes it with Lemma 23 over the liveness
interface — no schedule appears in it. `lemma25` puts a committed leader
block into the commit sequence, and `mem_linearise` puts everything in
its causal history into the delivery order.

Validity needs one more step: that a correct validator's block lies in
some correct leader's causal history. Coverage would give it in one
round, and coverage is unavailable here. `Validity.lean` takes the
paper's block structure instead — every block references its author's
previous block (`SelfParented`) — so a correct validator's blocks form a
chain, each reaching all the earlier ones (`reaches_of_same_creator`),
and round robin names that validator a leader once a cycle
(`exists_round_led_by`). `theorem26_of_selfParent` is Theorem 26 on any
schedule, whatever else a builder chose to reference.

**The bridge that remains.** `Liveness.lean` keeps `populated_of_viewPace`
and `synchronised_of_viewPace`: a FinWhale DAG can be fed production and
coverage from the development's main line. That is a compatibility
statement in the sense `LeanDagTest/Mysticeti/Routes.lean` gives the word, not a
route to liveness — the coverage it yields rests on `ViewPace`'s waiting
floor, which FinWhale's pacemaker does not have.

## 11. Views, and the rules relative to one

The safety and liveness results above took each validator's direct rules
as parameters, with two conditions tying them to the universe: that a
view's direct verdict is one of the universe, and that a caught-up view
sees the universe's direct commits. `View.lean` replaces the parameters
with the rules evaluated on the validator's own sub-DAG and proves both
conditions.

A **view** is a reference-closed subset of the universe's blocks, and it
is a `Dag` in its own right — validity and non-equivocation are
inherited, and closure is its completeness. It is the block record's
view, and `View.toRecord` builds the DAG.

**Most of the vocabulary does not read the population.** `parentsVoting`,
`parentSet` and `SPCertificate` are computed from a block's references,
so they are literally the same in a view as in the universe.

**Closure carries a block into the view whenever anything in the view
votes for it.** `mem_view_of_parentsVoting` is the immediate form. The
counting form matters more: a view holding a *single* round-`(r+2)` block
holds every block a quorum of round-`(r+1)` validators votes for
(`mem_view_of_voters`), because that block's `n − f` parents meet the
quorum in `f + p` authors, one of them correct, and a correct author's
round-`(r+1)` block is one block.

**So FP-evidence is view-independent.** Its equivocation test quantifies
over the population, but the conflicting versions it can find are voted
for by the block's own parents, hence in any view holding the block. The
equivocating branch's bound on conflicting votes needs one extra step: a
conflicting block outside the view has no parents voting for it there,
and the bound holds of it for nothing.

**The skip rule is where the two directions part.** Its first condition quantifies over the slot's blocks
*as the view holds them* — the paper writes "for each leader block of `s`
(if any) in the local DAG of `vj`" — so a view's direct skip is not a
direct skip of the universe, and a validator that has seen no block of a
slot satisfies that condition for nothing. The exclusions it takes part
in therefore cannot be transported; they are proved directly
(`no_directSkip_of_commit_view`, `no_indirectCommit_of_directSkip_view`),
and both run through the *second* condition, the quorum of
Non-FP-evidence blocks. That quorum is what makes the missing block
visible: one of its round-`(r+2)` blocks already forces the committed
block into the view by the counting above, and then the same block is
FP-evidence for it — by Lemma 4 under a fast commit, by Lemma 2 under a
slow one — which is what Non-FP-evidence denies.

`finWhaleLaws` assembles the laws from the view lemmas, and
`all_decided_of_view` and `agreement_of_commits` are the capstones with
the view conditions supplied rather than assumed: two validators running
the reverse pass on their own views deliver the same sequence, each pass
landing in the relation and the relation's agreement doing the rest.

**And a view is a validator's holdings.** `Holdings.lean` closes the last
of it. `PaceCore.holds` is what a validator has at an instant, and its
two store clauses — holdings are part of the universe, holdings are
closed under references — are exactly a view's, so `holdsView` reads
the holdings as a view and `View.toRecord` makes them a DAG the rules
run on. What the network delivers is `held_of_pace`: past GST
every reliable block of every round up to the horizon has arrived by
`settled`, one instant, by `holds_roundBlocks` and monotonicity. Byzantine
authors are not covered and no schedule covers them, which is why the
liveness interface names its certificates as reliable validators' blocks
(§10) — a view can be shown to hold those and nothing else.

`all_decided_of_pass` is the result with nothing about the validator
assumed: its view is what it holds, its verdicts are the reverse pass,
and every slot below the horizon is decided.

## 12. What the protocol guarantees

Everything above is stated over whatever it needs: a verdict assignment
and its well-formedness, a view and its closure, a horizon and a bound.
That is the right shape for a proof and the wrong shape for a reader, who
wants to know what FinWhale guarantees and under what.

`Protocol.lean` is the layer that says so. `Run` collects one execution —
the blocks, the schedule and network that carried them, the rotation, the
tie-break, the self-parent edge, and the liveness input §10 supplies —
and three definitions read a validator off it: `view v` is what it holds
once the network has delivered, `verdicts` are the reverse pass on that
view, and `delivers` is the sequence it outputs, the causal histories of
its committed leader blocks in order.

`Run.ofDoSValid` builds one from a DoS-valid universe (§1) and asks for
three fewer things: the DAG *is* the universe, so `ids_eq` and `block_eq`
are `rfl`, and the self-parent edge is the core's, so `selfParented` is a
theorem rather than a field to discharge.
`Run.ofDoSValidReactive` goes further and asks for none of the decision
layer at all: a DoS-valid universe and a `ReactiveM` over it, at one slot
per round under a round-robin schedule, and the rest — the liveness
input, the tie-break and its soundness among them — is discharged
inside.

The four properties are then stated in those terms and nothing else.

| theorem | statement |
|:---|:---|
| `Run.agreement` | two correct validators deliver the same sequence |
| `Run.totalOrder` | one's sequence is a prefix of the other's, at any two horizons |
| `Run.integrity` | no block is delivered twice |
| `Run.validity` | a correct validator's block is delivered |

Their hypotheses are which validators are correct and how far the horizon
reaches — `max k stable + (3f + 5) ≤ liveHorizon`, the window Lemma 22
needs plus the two rounds an anchor sits above, past the round the
network stabilised. No verdict assignment, view, well-formedness or
finiteness condition appears in any of them.

Nothing is proved here that was not proved before. `Run.decided` is
Lemma 23, `agreement` is Theorem 24, `totalOrder` Theorem 14 over Lemma
13, `integrity` Theorem 15, `validity` Theorem 26. Five short facts sit
between them and the machinery — that a validator's holdings are a view,
that its verdicts follow the pass, that a committed verdict names a slot
block, that nothing above the horizon is decided, and that it holds every
reliable block below the horizon — each an instance of a theorem proved
elsewhere.

Fast termination is not among them, because it is not a statement about
delivery: Theorem 21 says a commit pattern exists in the DAG, and
`fastCommit_latency` says when. Both are stated in §10, where the
schedule is.

The bundle is inhabited, which is what keeps the properties from being
vacuous: `fwRun` in the witness layer is the grown execution with its
schedule, its rotation, its self-parent edge and `chooseLeast` as the
tie-break, and agreement and integrity are read off it.

## 13. What the paper should change

No statement of the paper is false on the reading this arc takes. Four of
its proofs need work, two in each half, and the liveness results rest on
properties of the network that it states informally.

Each finding names **the case its argument does not reach** before the
repair, because that is what has to be seen for a repair to mean
anything, and because in three of the four the statement itself is true
and only the proof of it fails. What follows is ordered by how much of
the argument turns on it.

| finding | the case the argument does not reach |
|:---|:---|
| Lemma 22's window | every `p ≥ 2`, least at `f = p = 2` |
| the C3 case of Lemmas 18 and 19 | `p = 1`, at every `f` |
| Lemmas 6 and 7 through SP-skip | a validator holding no block of the committed slot |
| Lemma 4's round index | none — the count is unaffected |

The repairs are all in the library, and so is the arithmetic of each
diagnosis: `window_margin`, `c3_reachable` and `c3_margin` sit beside
`equivocating_margin` in `Counting.lean`, and §9's equivocating execution
exhibits the case Lemmas 6 and 7 do not reach. What is not
machine-checked, and cannot be, is that the paper's proofs *depend* on
that arithmetic — a reading of their text, given below in enough detail
to be checked against the paper.

### Two proofs that do not establish their statements

**Lemma 22 covers `p = 1` only.** Its proof concludes from "a window of
`3f + 3` rounds contains a full cycle of `n` rounds plus the first two
rounds of the next cycle". That step needs `3f + 3 ≥ n + 2`, which at
`n = 3f + 2p − 1` holds exactly when `p ≤ 1`: the difference `3f + 3 − n`
is `4 − 2p`, independent of `f`, so the window is a cycle plus two rounds
at `p = 1`, exactly one cycle at `p = 2`, and shorter than one beyond
that. The least broken instance is `f = 2`, `p = 2`, where `n = 9` and
the window is `9` rounds — one cycle, where the sentence reads off
eleven; at `f = 3`, `p = 3` the window is `12` against a cycle of `14`.

The statement holds at every `p`, and quantifying over every window of
that length makes a shorter window a *stronger* claim rather than a
weaker one — it holds because `f` does not grow with `p`, so correct
leaders only become denser. By a second argument: where `3f + 3 ≤ n` the window's
rounds name distinct validators, and `f + 1` disjoint consecutive triples
would need `f + 1` distinct Byzantine leaders. §10 has both. An
alternative is to replace the maximal-runs count with an incidence count,
which is shorter and uniform in `p`: if every cyclic triple held a
Byzantine leader, each Byzantine validator would answer for at most three
of the `n` triples, giving `n ≤ 3f` against `n ≥ 3f + 1`.

**The C3 case of Lemmas 18 and 19 does not close at `p = 1`.** A
C3-triggered validator built because it already held `n − f` blocks of
the round it was building, so it waited on nothing and never read the
leader. The proof recovers the lemma by finding, among those blocks, one
whose author did not itself use C3, by pigeonhole against a set `H` of
validators that cannot have used it.

`H` is one member too large. A validator with `j` honest validators ahead
of it holds at most `j + 1 + f` blocks of its own round — `j` from those
ahead, its own, and at most `f` from Byzantine authors — so C3's `n − f`
becomes reachable as soon as `j ≥ n − 2f − 1`. The validators that
certainly cannot use C3 are the fastest `n − 2f − 1`, where the proof
takes `n − 2f`.

That one member is the whole margin. Write `b` for the number of
validators that actually fail. A C3-triggered validator holds at least
`n − f − b` blocks by honest authors out of `n − b` honest validators, so
"among the honest blocks received by `vi`, at least one belongs to `H`"
has margin `(n − f − b) + |H| − (n − b) = |H| − f`, independent of `b` —
the two counts move together and the actual fault count cancels. At the
proof's `|H| = n − 2f` the margin is `2p − 1`, positive at every `p`; at
the correct `|H| = n − 2f − 1` it is `2p − 2`, zero at `p = 1`. So the
argument closes for `p ≥ 2` and yields nothing at the core committee, for
every `f` — the opposite regime to Lemma 22, whose proof holds only at
`p = 1`, so no single argument in the paper covers the whole range.

The instance, in full. At `f = 1`, `p = 1`, `n = 4`, C3 asks for three
blocks of the round being built. The fastest honest validator holds at
most `0 + 1 + 1 = 2` and cannot use C3; the second holds at most
`1 + 1 + 1 = 3` and can. So `H` is the single fastest validator where the
proof counts two, and the intersection bound is `1 − 1 = 0`: the
pigeonhole names no block at all, at the smallest committee the protocol
admits.

Induction on block-creation time needs neither count, and is the
route §10 takes: a C3-triggered validator holds `n − f` blocks of the
round it is building, at least one of them from an honest validator that
created strictly earlier, so the induction hypothesis applies to that
one, and a DAG closed under references holds what that block cites. It is
uniform in `f`, `p` and the actual fault count, and the same induction
serves Lemma 19 one round up.

**Lemma 4's proof names the wrong round.** Its equivocating case says the
block "does not reference the `r − 1` block of the Byzantine leader"; the
parents of a round-`(r+2)` block sit at round `r + 1`, and the block
excluded is the leader's round-`(r+1)` one. No case is lost here — the
count of at most `f − 1` Byzantine parents is what the argument uses and
it is unaffected — but the sentence does not name the block it excludes.
§3 records the reading this arc takes.

### An argument that has to be redirected

**Lemmas 6 and 7 cannot run through the SP-skip condition.** That
condition quantifies over "each leader block of `s` (if any) in the local
DAG of `vj`".

*Where it breaks.* On the case the lemma is about: a validator that has
received **no** block of the committed slot. Its SP-skip condition is
then satisfied for nothing — there is no block of the slot for a quorum
to decline to vote for — so nothing about the committed block follows
from it, and the contradiction the proof wants has no block to run on.
The parenthesis "(if any)" is what admits the case, and the argument
above it assumes the case away.

*The repair.* The argument runs through the second condition instead: one of the `2f + p` Non-FP-evidence blocks carries `n − f`
parents, which meet the committed block's `2f + p` voters in an honest
validator whose single round-`(r+1)` block both votes for it and is that
parent — so the committed block is in the skipping validator's DAG after
all, and the same round-`(r+2)` block is FP-evidence for it by Lemma 4 or
Lemma 2. §11 carries this out. As the proofs stand, a reader is invited
to take the route that does not work.

### What the liveness proofs use without saying

These are not proofs that fail on a case, but steps whose premises are
never stated. Each is given with the case that exposes it.

**Parent selection is specified for C1 only.** Lemmas 18 and 19 both need
"what is held is selected" — the round-`(r−1)` leader's block, and the
votes for the round-`(r−2)` leader — and the case that needs it is a
block created under C2 or C3, which is the case those lemmas exist for.
It belongs in the protocol description as a property of the selection
algorithm, subject to leader-consistency.

**Two properties of the network are used implicitly**: that a block
enters a DAG only after its creator made it, and that honest validators
do not create the same round simultaneously. The first is needed by any
timing argument. The second is needed only by the `H` argument, and the
induction above dispenses with it.

**A1′ is stated where it cannot be used.** The case it addresses — that
excluding the leader's block may leave `n − f − 1` parents — is a
constraint on block validity, and every count in the safety proof rests
on block validity; but A1′ appears only in the parent-selection prose.
§1 shows the corner closes by counting under the denial-of-service
condition, where the citable authors always include a validity quorum.

**Lemma 12 presupposes a maximum.** "Let `s` be the latest leader slot
for which such inconsistent decisions were made" needs the decided slots
to be finite. The case is a DAG with no bound: without finiteness there
is no latest slot and the induction has no base to run from. They are
finite, and it should be said; §7 takes it as a hypothesis for that
reason.

**Lemma 23's "eventually" does not survive a literal reading.** Being
decided is relative to a DAG, and in a fixed DAG nothing above its reach
is decided. The content is that a slot below a committed anchor is
decided and that the DAG grows; stating it that way also makes the
interaction with Lemma 12's finiteness visible. §10 states the per-DAG
form.

### Two claims the paper does not establish

**Definition 1's latency is not proved.** Theorem 21 establishes that the
fast commit exists, not that it happens within two message delays. The
timing claim follows from C1 and C3 once the reactive exit is bounded
above, and §10 proves it: past GST, with actual delivery `δ`, the votes
are built within `Δ + δ + 2·proc` of round entry, and the timeout never
fires where `Δ + δ + 2·proc` undercuts it.

**The optimality of `n = 3f + 2p − 1` is asserted by citation.** Nothing
in the paper shows this protocol requires exactly that committee. There
is a tightness result available to it, and it is the paper's own: at
`n = 3f + 2p − 1` the equivocating branch of Lemma 4 reaches exactly the
`f + p` its FP-evidence definition demands, and at `n = 3f + 2p − 2` it
reaches `f + p − 1`, one short, for every `f` and `p` in range (§4). The
committee is the least at which the paper's argument closes, which is a
statement about this protocol rather than about the literature.

### What holds

Every statement this arc formalises is proved: Lemmas 2 to 13 and
Theorems 14 and 15 on the safety side, Lemmas 18 to 20, 22, 23 and 25 and
Theorems 21, 24 and 26 on the liveness side. The deterministic tie-break
among an anchor's candidates — the construction closest to the defect the
Black Marlin arc reports (report §18) — is safe here, and §6 says why:
the rule reads the anchor's causal history and no view. That is worth
stating in the paper, since the failure mode is live in a neighbouring
protocol.

Lemmas 16 and 17 are the exception in the other direction: they are
neither confirmed nor contradicted here, because timeouts and message
delivery are not modelled at all. §14 says what stands in their place.

## 14. What is not modelled, and what is not done

The capstones state their own side conditions, and §12 removes them from
what a reader has to check: §8 discharged the ordering hypothesis, §11
the view conditions and the holdings behind them, §7 the reverse pass,
and §9 exhibits an execution that is a schedule. Three gaps remain, and
they are of a different kind from the ones that closed: each is a piece
of the protocol this development does not model at all.

**The network's clauses are modelled, not derived.** `converges`,
`advances` and `catchup` are fields of the pacing trunk, and so are
`holds_built` and `builds_distinct` on the creation route. Each stands
for a property of the network or of the schedule, and the correspondence
is recorded in prose here and checked by eye, as it is for every other
arc in this development. It is not the kind of thing that gets proved:
the pace *is* the model of the network. The protocol's own clauses — C1,
C2, C3 and parent selection — are no longer among them: §10 derives
Lemmas 18 and 19 from those rather than assuming their conclusions.

**A1′ has no counterpart as a rule**, and parent selection has one only
as an assumption. A1′ — that advancement needs a leader-consistent set of
round-`(r−1)` blocks, or one excluding the leader's — is not modelled;
the arc takes its result, validity's leader clause. What A1′ is *for* is
settled under the denial-of-service condition, where the corner it
addresses is closed by counting rather than by a rule:
`quorumCard_le_citable` says the authors a block may cite always include
a validity quorum, so excluding the convicted ones can never leave a
builder short. Selection appears on
the creation route as `selects_leader` and `selects_votes`, which say
what the algorithm does with what it holds rather than deriving it from
an algorithm.

**How far a commit sequence runs is a choice.** `hk` says it stops at the
first undecided slot. That is not derived: it is the horizon the caller
picks, and `all_decided` is what makes a given horizon legitimate.

## 15. The partition: what defines the protocol, and what proves things about it

`LeanDag/FinWhale/Model/` holds every definition of the protocol and
nothing else. `scripts/check-arc-holes.py` enforces two rules over the
arc, as it does for Mahi-Mahi and Black Marlin: no proof holes anywhere —
no `sorry`, no bespoke axiom, no `native_decide` — and no theorem, lemma
or example in a `Model/` file.

Thirteen files, in the order a reader meets them.

| file | what it defines |
|:---|:---|
| `Model/Params.lean` | the committee `n = 3f + 2p − 1`, and the three thresholds |
| `Model/Rule.lean` | block validity, votes, FP-evidence, SP-certificates, the fast commit |
| `Model/Skip.lean` | the two halves of the direct skip rule |
| `Model/Decision.lean` | the slot's blocks, and the direct commit and skip verdicts |
| `Model/Anchor.lean` | the indirect rule, and its decidable form |
| `Model/Verdict.lean` | verdicts, the reverse pass as a condition, and the tie-break |
| `Model/Pass.lean` | the reverse pass as a procedure |
| `Model/Order.lean` | the committed sequence, the delivery order, and a leader's list |
| `Model/View.lean` | a view, and the direct rules relative to one |
| `Model/Schedule.lean` | round robin, and the self-parent clause |
| `Model/Creation.lean` | C1, C2, C3, and parent selection |
| `Model/Liveness.lean` | the interfaces the layers pass between them |
| `Model/Protocol.lean` | `Run`, and what a validator holds |

**The model layer is closed.** Every `Model/` file imports only other
`Model/` files, `LeanDag.Validators`, `LeanDag.Causality`,
`LeanDag.ViewPace` and Mathlib. The protocol can therefore be read
without reading a proof, and no part of it depends on a result about it.
`Committee.lean` is what that costs: the arithmetic of the committee —
`params_arith` and the ordering of the thresholds — was stated beside the
definitions and is now proved beside the rest.

**Four definitions sit outside `Model/`, each because it takes a proof as
an argument.** `Run.verdicts` and `Run.delivers` run the reverse pass on
the holdings read as a view, which needs the holdings to be one; that
view is `Run.viewOf`, and the two sit beside it in `Protocol.lean`.
`Dag.ofDoSValid` and `Run.ofDoSValid` are built from
`leaderClause_of_dosValid` and `selfParented_ofDoSValid`, and sit beside
them in `DoSBridge.lean`.

**What the arc does not have** is the other half of the discipline
Mahi-Mahi and Black Marlin carry: `<Result>/Statement.lean` files that
are proof-free, with the proofs generated beside them. Results here are
stated where they are proved. The checker's statement-file rule is
therefore vacuous over this arc; its model rule is not.
