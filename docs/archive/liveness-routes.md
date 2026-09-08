# Converging liveness on `ViewPace`

> **Archived.** The programme this document plans was carried out in
> full (see its own italicised preamble below, added when the work
> completed) and the single-route account now lives in `docs/report.md`
> §§4, 6, 16–18. Kept for historical record only.

*Design record, and now the record of the executed programme. The plan of
§§3–8 was carried out on branch `liveness-route-audit`: the feature arcs
are relativised (steps 1–2), the necessity witnesses, V1 and the
quantitative arc are restated over `ViewPace` (steps 3–5), and the old
routes are deleted (steps 6a–6c) — `ViewSync.lean` and `Timing.lean`
removed, `ViewGrowth` and `CatchupSync` with them, `Live`,
`DeliversQuorum`, `no_stall` and `synchronised_of_delivery` gone,
`Delivery` demoted to the storage model with the DoS capstones restated
interface-style, and report §§4, 6, 16–18 rewritten as the single-route
account. §5's prediction held: `Delivery` could not be deleted, and was
not. The open questions of §9 remain open except 9.4, settled by
`ViewPace.reached`. What follows is the plan as written before the work.*

## 1. The goal

Every liveness proof in the development should consume the `ViewPace`
route, and the other routes should eventually be deleted.

`ViewPace` (report §6.9, V17) is the partial-schedule structure: `top v` is
the highest round `v` reached, production is derived from genesis and the
pacemaker's progress rule, and *stuck* is expressible. It is the weakest of
the four routes and the only one that assumes production at a single round.

This document records what that goal costs, what it cannot have, and in
what order to take it.

## 2. Where things stand

An audit of every liveness-flavoured result in the feature modules,
classified by what its **statement** assumes:

| | count | status |
|---|--:|---|
| interface-stated (`PopulatedOn` / `SynchronisedOn` as hypotheses) | 55 | any route discharges these |
| bare (`Decided` / `IsLeaderBlock` only) | 91 | route-agnostic |
| naming `Live` / `Delivery` / `DeliversQuorum` | 42 | *see below* — mostly a false positive |
| naming `ViewSync` | 2 | genuinely route-bound |

The 42 are DoS and GC internals — `DoSAccepting`, `ByzBudget`, `byzPool`,
`joinIds` — where `Delivery` is the **object of study**, an acceptance
policy, not the production route. Their liveness capstones sit in the
interface-stated bucket. This distinction matters for §5 and is the single
most important finding of the audit.

`LeanDagTest/Mysticeti/Routes.lean` discharges three arcs from one `ViewPace`,
supplying nothing else: **Mysticeti L10**, **Odontoceti O10** (under
`Faults5`), and **chain quality CQ6**. No `Live`, no `Delivery`, no
`DeliversQuorum`, no `Timing` in any hypothesis. Compatibility is therefore
not conjecture.

Two qualifications, both already true before this work:

* **The generality does not transfer.** The Mysticeti core asks production
  over `T` and from the synchrony round on. Every feature arc still asks it
  over all of `Correct` and at every round. `ViewPace` supplies that at
  `T := Correct`, so the arcs work — but none can run at a `T` that is a
  proper subset of `Correct`, though the core can.
* **Two structures resist**, for different reasons (§7).

## 3. Reaching "all liveness on `ViewPace`"

### Phase A — relativise the consumers (mechanical)

Mirror the `CommitsAt` diff: `(∀ r ≤ N, Populated U r)` becomes
`(∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)`, and the `decided_of_leader_of_populated`
counterpart drops its three `PopulatedOn.mono` calls.

| file | sites |
|---|---|
| `Odontoceti/Liveness.lean` | 103, 212, 241 |
| `Hybrid/Liveness.lean` | 102, 198, 228 |
| `Adaptive/Liveness.lean` | 120, 175 |
| `Adaptive/Odontoceti.lean` | 260, 310 |

Order by imports: Odontoceti → Hybrid → Adaptive/Liveness →
Adaptive/Odontoceti. Low risk; the same diff has landed once already.

### Phase B — pass-throughs (trivial)

`DoS/Novelty.lean`'s `dos_resistance` and `dos_resistance'` **forward**
`hpop` rather than consuming it (`⟨hpop, …⟩`). Change the binder.

### Phase C — two that are not consumers at all

* `Network/Quorum.no_stall` is a **supplier** — it is L1, the untimed
  production route, and produces the Correct-wide shape. Relativising it
  weakens the other route's output for no gain. Leave it; it disappears
  with `Live` in §4.
* `GC/Window.populated_chop` is a **transformer**: it shifts production
  across the cut `G`. Relativising makes the output range `R - G` under
  truncated subtraction, and whether `R` is measured before or after the
  chop is a decision, not a rename. **Open question, §9.**

### Phase D — `Quality` is blocked, and says so

`Quality/Inclusion.lean`'s own header:

> the schedule side is `T ⊆ Correct`-relative, but the backbone consumes
> Correct-wide coverage, so the theorems here take full `Synchronised U R`.
> A `T`-relative variant would need a `T`-relative backbone lemma —
> possible but not attempted in this arc.

`IncludesAt` cannot be relativised until `mem_history_of_correct` (CQ5) is.
That is a real proof, and the only part of Phase A–D that could fail.

## 4. What deletion costs, route by route

Measured from the compiled dependency graph — declarations in the route,
and declarations transitively depending on them.

| route | decls | dependents | principal consumers |
|---|--:|--:|---|
| `ViewGrowth` | 94 | 23 | all internal to `ViewSync.lean` |
| `ViewSync` | 62 | 36 | `Drift.Catchup` (22) |
| `Timing` | 54 | 78 | `ViewSync` (16), **`Quantitative` (7)**, `Drift.Catchup` (3) |
| `Live` | 8 | 13 | `Network.Quorum` (5) |
| `DeliversQuorum` | 1 | 13 | `Network.Quorum` (6) |
| `Delivery` | 23 | **161** | `DoS.Novelty` (41), `GC.Bootstrap` (15), `GC.Window` (15) |

Read as a deletion order:

1. **`ViewGrowth` — cheapest.** Fully superseded by `ViewPace`; every
   dependent is inside `ViewSync.lean` itself. Delete once V15/V16 are
   retired from the report.
2. **`ViewSync` — after Catchup.** Its only substantial external consumer
   is `Drift.Catchup`, which extends it (§7).
3. **`Timing` — after the quantitative arc is ported.** `Timing` carries
   the whole of report §6.10: `Rated`, `synchronisedOn_of_rate`,
   `commits_recur_within`, `commits_recur_by_round`, `directCommit_of_wait`,
   `decided_of_wait`, and `directCommit_of_wait_two_delay` — the result that
   derives the `2Δ` timeout the deployed systems choose by hand. None of it
   exists over `ViewPace`. **This is the largest single item in the goal.**
4. **`Live` and `DeliversQuorum` — small.** Thirteen dependents each,
   concentrated in `Network.Quorum`. They go together, and with them goes
   N1 and the untimed production route (V5).

## 5. What cannot be deleted: `Delivery`

`Delivery` has 161 dependents and is **not primarily a liveness structure**.
It is the acceptance-policy model that the DoS and GC arcs are stated over:

```lean
def viewUpto  (D : Delivery U) (v : Validator) : ℕ → Finset BlockId
def ByzBudget (D : Delivery U) (κ : ℕ) : Prop
def UniformBudget (D : Delivery U) (T : ℕ) : Prop
def RefsAccepted (D : Delivery U) : Prop
def viewGap (D : Delivery U) (v w : Validator) (n : ℕ) : Finset BlockId
def joinIds (D : Delivery U) (w : Validator) (m t G : ℕ) : Finset BlockId
```

None of these is about production or coverage. They are about what a
validator *stores* and *accepts* — the subject of report §8 and §11.

So the goal must be restated for this one: **`Delivery` is demoted, not
deleted.** Its `includes` field (P7) and its liveness use disappear; its
`held`/`accepted` pair stays as the storage model. A follow-up question is
whether `ViewPace.holds` and `Delivery.held` should be unified, since they
are two spellings of *what a validator has in hand* — one time-indexed, one
round-indexed. That is a genuine simplification and is **not** attempted
here.

## 6. What is lost, and whether it matters

The routes are not redundancy. They are the report's argument that the
network assumption can be stated at four decreasing strengths, with the
weakest sufficing. Deleting them deletes that argument.

Concretely, these labelled results are stated over routes slated for
deletion:

| | result | over |
|---|---|---|
| V1 | the referencing clause, unfused from the network's | `ViewSync` |
| V2 | the timing route derived from the view-level one | `ViewSync`→`Timing` |
| V3 | build-time views agree | `ViewSync` |
| V4 | the bound factored out of convergence | `ViewSync` |
| V5 | production from untimed view convergence, without N1 | `Live` |
| V6, V7 | production derived; assumed = derived, Skolemised | `ViewGrowth` |
| V8, V9 | the untimed condition induced; N2a and L7a derived | `ViewGrowth` |
| V10, V11, V12 | the three necessity witnesses | `Timing` / `ViewSync` |
| V13–V16 | the intermediate spines | `ViewSync` / `ViewGrowth` |

**V1 is the one to think hardest about.** `covers_of_converges` is the
theorem that separates the network's clause from the protocol's — it is
where report §4.3's claim that *the network's whole contribution is one
sentence about views* is discharged. `ViewPace` inherits the separation
(its `converges` and `references` are the same two clauses) but proves
coverage directly, so V1 is not on its path. Deleting `ViewSync` without
restating V1 over `ViewPace` would remove the trust-boundary result while
keeping the claim.

**V10–V12 must be restated, not deleted.** They are the evidence that the
bound, the starting round and the reliable set are each necessary. They are
currently modelled over `Timing`/`ViewSync` witnesses. Porting them to
`ViewPace` is required work, not optional.

## 7. Two structures that resist

### `Drift.CatchupSync` — small, worth porting

125 lines, four theorems, `extends ViewSync`. Adds one clause:

```lean
  catchup : ∀ v ∈ T, ∀ u ∈ T, ∀ n ≤ N, ∀ t,
    blk u n ∈ holds v t → built v n ≤ t + proc
```

Its payoff is real: `drift_collapse` makes drift **zero**, which is what
eliminates the start spread `D₀` in report §6.12.

The port is the move `ViewGrowth` already made — restate `catchup` over any
block `u` authored at round `n` rather than `blk u n` — then
`CatchupPace extends ViewPace` and re-prove four theorems. The one thing to
watch is that `drift_collapse` uses `waits`, which `ViewPace` guards by
`n < top v`; the guard comes from `le_top_of_built`, as it did for coverage.

### `Reactive.ReactiveCore` — a redesign, not a rename

Three findings, each of which alone rules out a mechanical port.

1. **It does not use the interface at all.** It goes `vote_or_wait` →
   `votes` → `certifies` → `directCommit` → `decided`, proving
   `DirectCommit` directly. It never produces `SynchronisedOn`. So it is not
   "a different structure for the same argument" — it is a different
   argument.
2. **It contradicts `ViewPace.waits`.** Being reactive *is* not waiting the
   full timeout: it carries `built_lt` (time advances) and `deadline` (never
   wait past the timeout) where `ViewPace` has `waits` (always wait the full
   timeout). `ReactivePace extends ViewPace` is therefore unsound.
3. **Its two substantive clauses are stated over `blk`** (`vote_or_wait`,
   `prompt_vote`), so all of them need the off-`blk` generalisation, and
   `votes`/`certifies`/`directCommit`/`decided` need re-proving.

**Recommendation: do not port it.** State it in the paper for what it is —
a second route that reaches `DirectCommit` without passing through
production and coverage. That is interesting rather than embarrassing: it
shows the interface is a choice, not a necessity.

*(Superseded by the unification of branch `reactive-unification`. The
calculus changed when `PaceCore` was carved out of `ViewPace`: the shared
trunk carries everything production needs, so `ReactivePace extends
PaceCore` — not `ViewPace`, resolving finding 2 — inherits derived
production, resolving the `blk` totality of finding 3 by deletion rather
than generalisation; and finding 1 stands but is now precise, since the
two disciplines share production and differ only in how the commit
hypotheses are discharged: coverage for the full-timeout discipline,
targeted votes for the reactive one. The off-`blk` restatement of
`vote_or_wait`, `prompt_vote` and `cert_or_wait` was the same move the
Catchup port had made twice already. Option B then named the meet point:
`VotesAt` and `CertifiesAt` are the targeted half of coverage the commit
rules count, `directCommit_of_votesAt` and `directCommit_of_certifiesAt`
are the counting arguments proved once, and each discipline is a
supplier — `votesAt_of_synchronisedOn`/`certifiesAt_of_synchronisedOn`
from coverage, `ReactivePace.votes`/`ReactiveM.certifies` from the wait
clauses. Finally RS5 settled what the reactive discipline's missing
coverage actually costs: not the inclusion guarantee but its latency —
`ReactiveM.committed_of_correct_block` recovers CQ6's conclusion through
the self-parent chain (`reaches_self_ancestor`) and per-validator
fairness (`FairToEach`), one leadership rotation where coverage needs
one round. P3′ thereby acquired its first liveness consumer.)*

## 8. Recommended sequence

| | work | cost | risk |
|---|---|---|---|
| 1 | Phase A + B | 1.5 h | low |
| 2 | `CatchupPace` (§7) | 2 h | low–moderate |
| 3 | Port V10–V12 to `ViewPace` witnesses | half day | moderate |
| 4 | Restate V1 over `ViewPace`, or record its loss | 1 h | low |
| 5 | Delete `ViewGrowth`; retire V15/V16 from the report | 2 h | low |
| 6 | Port report §6.10's quantitative arc to `ViewPace` | 1–2 days | **high** |
| 7 | Delete `Timing`; delete `Live`, `DeliversQuorum`; demote `Delivery` | 1 day | moderate |
| 8 | Phase D — `T`-relative backbone, then `Quality` | half day | could fail |

Steps 1–5 get to *"every arc that consumes the interface does so from
`ViewPace`, and the necessity witnesses are stated over it."* That is the
claim the paper needs. Steps 6–8 are what "delete the other routes"
additionally requires, and step 6 dominates the cost of the whole
programme.

## 9. Open questions

1. **`populated_chop` and the cut** (§3, Phase C). Is the synchrony round
   `R` measured before or after the chop? The answer decides whether the
   relativised statement reads `R - G` or `R`.
2. **`ViewPace.holds` versus `Delivery.held`** (§5). Two spellings of the
   same notion, one time-indexed and one round-indexed. Unifying them would
   shrink the model materially, and would let the DoS budgets be stated over
   the same object as coverage. Not attempted; possibly the largest
   simplification available.
3. **Is the route hierarchy worth keeping in the report?** (§6.) If the
   paper's line is one route, §6.9's four-row table becomes an appendix at
   best. Deleting the other routes makes the report's §4.3 argument — that
   the network's contribution is *one sentence about views* — rest on
   `ViewPace` alone, which is defensible but is a different claim from the
   one currently made.
4. **Quantitative results over a partial schedule** (§8, step 6). The `2Δ`
   wait bound is derived from `Timing`. Whether it survives a schedule that
   can be stuck — and what it even means when a validator has not reached
   the round — needs thought before the port, not during it.

## 10. Postscript: catch-up folded into the trunk (August 2026)

A later decision, recorded here because it supersedes §7's framing of
`CatchupPace` as an extension. The `catchup` clause and its processing
bound `proc` were moved into `PaceCore` itself, making catch-up a clause
of the base protocol (P11) rather than an optional layer; `CatchupPace`
and `LeanDag/Drift/Catchup.lean` are gone.

What this gained, and what it cost — both sides were priced before the
move and the user chose the merge with the costs on the table:

* **Gained.** Drift left every headline statement. `ViewPace` lost
  `prompt` and `latest_mem` (the collapse argument uses neither), and
  `driftOn_of_prompt` was deleted; coverage, the spine, the rate and
  wait bounds, and the whole reactive line (`votes`, `certifies`,
  `decided`, RS5) now take `gst ≤ R` and the constant backoff
  `2Δ + proc ≤ timeout` — no `DriftOn` hypothesis, no start spread `D₀`,
  no deployment quantity anywhere in the development. Clause count is a
  wash (`prompt` + `latest_mem` out, `catchup` + `proc` in); statement
  complexity is not.
* **Cost.** The base protocol is stronger: every consumer now assumes
  the catch-up rule, including results that never needed the
  contraction. The `Delay(Δ) = D₀ + Δ` family is gone, and with it the
  plain `2Δ` external check — retained only as the `proc = 0` case
  (`directCommit_of_wait_two_delay`). The necessity witnesses had to be
  re-crafted with arrival-gated holds (`gapHolds`, `starveHolds`),
  since everything-held-from-`t = 0` models violate an unconditional
  `catchup`; and the reactive witness's timeout rose from `7` to `9` to
  clear `2Δ + proc` with the shared `proc = 5`.
* **Kept.** The drift-parametric coverage engine survives as
  `synchronisedOn_of_driftOn`: the drift-free headline consumes the
  quorum (the collapse runs through `reached`), so a sub-quorum reliable
  set — V12's two-member `T` — still needs drift supplied from outside.
* **Gated on GST** (follow-up, same month). `catchup` was subsequently
  weakened to fire only at `gst ≤ t`. The collapse proof applies the
  clause only at post-GST times, so nothing downstream moved; the gain
  is honesty about deployment — the executable rule is the GST-free
  clamped one (enter a sighted round within `proc`, never before the
  own floor), and pre-GST the clamp may bind, so the unconditional
  clause was false of every real implementation. The rush bound (CU5:
  `exists_reliable_parent`, `PaceCore.round_le_top_succ`,
  `ViewPace.exists_honest_floor`) is the other half of the same
  deployment story: valid evidence of a round certifies a reliable
  validator that paid the full timeout bill below it, so author-blind
  catch-up chases only the certified layer.
* **One `proc`.** The catch-up deadline and the reactive exit bound
  share the trunk's `proc`. They are the same kind of quantity (entry
  or build lag behind a trigger), but the sharing is a modelling choice:
  a system with fast reactive exits and slow catch-up would want two
  constants, and would pay for the split in a second parameter
  everywhere.

## 11. Postscript: the view mechanism joined to the pace line (August 2026)

Open question §9.2 --- "`ViewPace.holds` versus `Delivery.held`: two
spellings of the same notion, one time-indexed and one round-indexed;
possibly the largest simplification available" --- is now closed, and a
second gap nobody had recorded was found alongside it.

**The unrecorded gap.** `holds` was tied to the universe by *nothing*: not
`⊆ U.ids`, not causal closure. So the pacing line and the view-relative
commit rules were disjoint, and every liveness theorem concluded about
`View.full` --- a view no deployed validator ever has. `decided_mono` and
`decided_full` run the wrong way to fix it: they lift a verdict *up* to
bigger views, never down to a validator's own.

**One clause closes both.** `holds_sub` (a validator holds only blocks that
exist) makes `viewAt v t`, the causal closure of what `v` holds, a
legitimate `View` --- closure free by the `View.ofAccepted` argument. Then:

* **V18, liveness is local.** `holds_roundBlocks` is the delivery lemma;
  `decided_local_of_certifiesAt` runs L4's counting inside `viewAt v t`.
  Proved on the trunk, so both disciplines inherit it. Hypotheses are the
  main line's exactly. `decided_of_local` recovers the global form, so it is
  a strict strengthening.
* **V19, the delivery layer is induced.** `held v n` is `holds` read at
  `built v (n+1)`, filtered to round `n`. Every `Delivery` field is then a
  theorem --- notably `accepted_inj`, whose own docstring had said it was
  "forced by `distinct_creators`" without proving it. It is: P7 puts every
  held round-`n` block in the builder's references, P2 collapses duplicates.

**What did not come free**, recorded rather than papered over. `RefsAccepted` (a correct validator references *only* what it
accepted) is the **converse** of P7, which the pacing structure does not
have --- `references` is one-directional by design.
`refsAccepted_toDelivery` isolates the gap as exactly that clause. And the
correspondence is not an equivalence: a `Delivery` has no instants, so it
cannot determine a schedule. `Delivery` stays the right object for arcs that
never mention time; what is gone is the *independence* of the assumption.

**Follow-up: the converse clause (V20), and its promotion.** A validator
references only what it held. This was first named as a *predicate* on a
pacing structure rather than a trunk field, because `ugrowLag` (CU4) failed
it --- leaders building round `1` at `12` while the round-`0` blocks they
reference arrived at `14`.

That reading was wrong, and the closure work (S4) showed why: the same
witness was incoherent for causal closure too, and had to be retimed
regardless. With the leaders building at `14`, all eight witnesses in the
development satisfy the clause --- checked one by one --- so it is now the
trunk field `refs_held` (S5), and `dos_resistance_of_pace` is
unconditional. The lesson generalises: a clause that no model can satisfy
may be indicting the models rather than the clause, and the way to tell is
to ask whether the failing model describes a run an implementation could
produce.

**Follow-up: causal closure of holdings (S4).** `holds` was tied to the
universe by `holds_sub` alone, so the model admitted a validator holding a
block whose history it lacked --- a block it could neither validate (P3, P3′
read the referenced blocks) nor build upon. Two consequences: `advances`
was obliged to fire on evidence no implementation could act on, and
`viewAt` was the closure of a validator's fragments rather than its view.
`holds_closed` fixes both, and *weakens* what is assumed of an
implementation. `viewAt_ids` then gives `(viewAt v t).ids = holds v t`, so
V18 is about the blocks the validator actually has.

Two witnesses were physically incoherent in exactly this way and are
repaired. `ugapPace` (V10, V11) held own blocks without the round below
them; it now delivers every non-starved block one tick after its build,
leaving validator `2` starved and `converges` binding only from `4N+5`.
`ugrowLag` (CU4) built round `1` at `12` while its references arrived at
`14`; leaders now build at `14`, the laggard's catch-up deadline moves
`15 → 17`, and the collapse remains exact --- spread `10` at round `0`,
`Δ + proc = 3` above. Both are stronger evidence than before: a
counterexample that could not occur is weak evidence that a hypothesis
carries the argument.
