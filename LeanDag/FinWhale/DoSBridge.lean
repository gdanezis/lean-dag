import LeanDag.FinWhale.Protocol
import LeanDag.FinWhale.Reactive
import LeanDag.DoS.Exposure
/-!
# A DoS-valid Mysticeti universe is a FinWhale DAG

`FinWhale.ValidHere` and the core's `ValidWrt` differ in two clauses:
FinWhale adds the leader clause, and drops the self-parent edge that the
core requires and the paper's block structure has (`finwhale.md` §1).

Under the denial-of-service condition of `dos-equivocation-and-growth.md`
the difference vanishes, in the useful direction. `DoSValid` says a block
may not cite an author its own causal history convicts of equivocating,
and that is the leader clause with three of its four narrowings removed:
it holds of every author, at unbounded depth, permanently. So a
`BlockUniverse` satisfying it is a FinWhale DAG at any leader schedule,
with the self-parent edge thrown in — and every result of this arc
applies to it.

Two things follow beyond the construction. `SelfParented` becomes a
theorem, so Theorem 26 (Validity) loses its one remaining hypothesis. And
the DAG and the universe are the *same object*, so the `ids_eq` and
`block_eq` conditions every liveness result carries are `rfl` — a `Run`
built this way names one execution rather than two and an equation
between them.

`Run.ofDoSValidReactive` closes the last gap: over the core's reactive
schedule such a universe is a `Run`, so the four guarantees hold of it
with no further hypothesis. `LeanDagTest/FinWhale/Equivocation.lean`
exhibits one where the condition is active — validator `0` equivocates,
three round-`2` blocks are exposed to it and drop its round-`1` block —
so the composite is not vacuous. `quorumCard_le_citable` is why it cannot
become so at any height: the authors a block may cite always include a
validity quorum, so the condition never leaves a builder unable to
build.

**What this does not claim.** `DoSValid` is strictly stronger than what
FinWhale specifies: the protocol admits a DAG that cites an equivocating
non-leader, and this file says nothing about such a DAG. What it gives is
that a deployment running FinWhale over a DoS-protected DAG — which is
the deployment one would want, by the storage bound of
`dos-equivocation-and-growth.md` §5 — obtains the whole arc with no
further hypothesis.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

omit P in
/-- **The DoS condition implies the leader clause.** If a block's parents
are not leader-consistent, the two conflicting versions they reference
are both in its causal history, so the leader is exposed in it — and an
exposed author may not be cited. -/
theorem leaderClause_of_dosValid (hdos : DoSValid U)
    {b : BlockId} (hb : b ∈ U.ids) :
    Clause.leaderExcluded U.block (U.block b) := by
  intro v
  by_cases hcons : ∀ i ∈ (U.block b).refs, ∀ j ∈ (U.block b).refs, ∀ x ∈ (U.block i).refs,
      ∀ y ∈ (U.block j).refs, (U.block x).creator = v →
      (U.block y).creator = v → x = y
  · exact Or.inl hcons
  · refine Or.inr ?_
    push Not at hcons
    obtain ⟨i, hi, j, hj, x, hx, y, hy, hxc, hyc, hne⟩ := hcons
    have hxh : x ∈ history U b :=
      (mem_history_iff hb).2 (Reaches.trans (Reaches.single hi) (Reaches.single hx))
    have hyh : y ∈ history U b :=
      (mem_history_iff hb).2 (Reaches.trans (Reaches.single hj) (Reaches.single hy))
    have hround : (U.block x).round = (U.block y).round := by
      have h1 := U.round_of_mem_refs hb hi
      have h2 := U.round_of_mem_refs hb hj
      have h3 := U.round_of_mem_refs (U.refs_subset hb hi) hx
      have h4 := U.round_of_mem_refs (U.refs_subset hb hj) hy
      omega
    intro k hk hkc
    exact hdos b hb k hk (hkc ▸ ⟨x, hxh, y, hyh, hne, hxc, hyc, hround⟩)

/-- **The construction.** A DoS-valid universe, read as a FinWhale DAG at
a given leader schedule. Three validity clauses are the core's, the
fourth is the theorem above, and non-equivocation is the universe's. -/
def Dag.ofDoSValid (U : BlockUniverse Validator BlockId Payload) (leader : ℕ → Validator)
    (hdos : DoSValid U) : Dag Validator BlockId Payload where
  ids := U.ids
  block := U.block
  complete := U.complete
  valid := fun i hi =>
    { predecessor := (U.valid i hi).predecessor
      distinct_creators := (U.valid i hi).distinct_creators
      quorum := (U.valid i hi).quorum
      leader_clause := leaderClause_of_dosValid hdos hi }
  no_equivocation := U.no_equivocation

@[simp] theorem ofDoSValid_ids {leader : ℕ → Validator} (hdos : DoSValid U) :
    (Dag.ofDoSValid U leader hdos).ids = U.ids := rfl

@[simp] theorem ofDoSValid_block {leader : ℕ → Validator} (hdos : DoSValid U) :
    (Dag.ofDoSValid U leader hdos).block = U.block := rfl

/-- **And the self-parent edge comes with it**, which the FinWhale model
drops and Validity asks for. Theorem 26 needs no hypothesis here. -/
theorem selfParented_ofDoSValid {leader : ℕ → Validator} (hdos : DoSValid U) :
    SelfParented (Dag.ofDoSValid U leader hdos) :=
  fun b hb hr => (U.valid b hb).self_parent hr

omit P in
/-- **A parent set of reliable authors is never obstructed.** No correct
validator is ever exposed, so the condition costs a builder nothing that
builds on correct validators' blocks.

This is where the A1′ corner is and is not. A validator holding the
round-`(r−1)` blocks of every correct validator has `n − f` unobstructed
authors and can always build. The corner is the case where it has not yet
received them — which is why the paper states A1′ as a condition on
advancement rather than on validity, and why no validity rule can
discharge it. -/
theorem not_exposed_of_correct_parents {b : BlockId} (hb : b ∈ U.ids)
    (h : ∀ i ∈ (U.block b).refs, (U.block i).creator ∈ (Correct : Finset Validator)) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator :=
  fun i hi hexp => hexp.not_correct hb (h i hi)


/-- **A run over a DoS-valid universe.** The same data a `Run` asks for,
less three: the DAG *is* the universe, so `ids_eq` and `block_eq` are
`rfl`, and the self-parent edge is the core's. -/
def Run.ofDoSValid [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (leader : ℕ → Validator) (hdos : DoSValid U)
    (horizon : ℕ) (rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ horizon)
    (paceHorizon : ℕ) (pace : PaceCore U (Correct : Finset Validator) paceHorizon)
    (rounds_advance : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pace.top u, n ≤ pace.built u n)
    (stable : ℕ) (gst_le : pace.gst ≤ stable) (liveHorizon : ℕ)
    (commits : CommitsCorrectLeaders (Slots.identity leader) (Dag.ofDoSValid U leader hdos)
      stable liveHorizon)
    (live_le : liveHorizon ≤ paceHorizon) (roundRobin : RoundRobin leader) :
    Run Validator BlockId Payload where
  dag := Dag.ofDoSValid U leader hdos
  sched := (Slots.identity leader)
  roundId := fun _ => rfl
  paced := U
  ids_eq := rfl
  block_eq := rfl
  horizon := horizon
  rounds_le := rounds_le
  paceHorizon := paceHorizon
  pace := pace
  rounds_advance := rounds_advance
  stable := stable
  gst_le := gst_le
  liveHorizon := liveHorizon
  commits := commits
  live_le := live_le
  roundRobin := roundRobin
  selfParented := selfParented_ofDoSValid hdos

/-! ## A reactive deployment over a DoS-protected DAG

The construction above is structural: it gives the DAG, and every safety
result with it, but `Run.ofDoSValid` still asks for the liveness input.
This section supplies it from the core's reactive schedule.

**The two disciplines do not collide.** `DoSValid` forbids citing an
author a block's own history convicts of equivocating, and a reactive
builder's two citation obligations are both confined to reliable authors:
`ReactivePace.vote_or_wait` is guarded by `S.leader k ∈ T`, and
`ReactiveM.cert_or_wait`'s fallback obliges referencing only blocks whose
creator is in `T`. At `T = Correct` every block either clause demands is
authored by a correct validator, and `ExposedIn.not_correct` says a
correct validator is never exposed. So nothing the schedule requires is
anything the condition forbids.

That is particular to this route. The block-creation discipline of
`Creation.lean` obliges a builder to reference a block by the author of
*any* held vote, reliable or not, and that clause and `DoSValid` are not
jointly satisfiable where a convicted equivocator votes for a reliable
leader. -/

variable [S : Slots Validator]

omit P S in
/-- **Correct authors are always citable.** An exposed author has
equivocated, so it is Byzantine; the DoS condition therefore never
forbids citing a correct validator, which is every block either reactive
clause obliges a builder to reference. -/
theorem citable_of_correct {b : BlockId} (hb : b ∈ U.ids) {X : Validator}
    (hX : X ∈ (Correct : Finset Validator)) : ¬ ExposedIn U b X :=
  fun h => absurd hX (by simpa using h.not_correct hb)

omit P S in
/-- **The condition never exhausts a builder's parents.** Validity asks
for `n − f` parents by distinct authors, and `DoSValid` withdraws the
authors a block's own history convicts. Those are equivocators, hence
Byzantine, hence at most `f`; the correct validators are never among them
and number at least `n − f`. So the authors a block may cite always
include a validity quorum, and the two conditions cannot squeeze a
builder between them.

The margin is nil, not small: at exactly `f` Byzantine validators the
citable authors are the `n − f` correct ones and no others, so every one
of them has to be cited. That is a condition on what has arrived rather
than on what may be cited, and it is what the pacing structure supplies
past GST. -/
theorem quorumCard_le_citable {b : BlockId} (hb : b ∈ U.ids) :
    quorumCard Validator ≤ ((exposedTo U b)ᶜ).card := by
  refine le_trans card_correct (Finset.card_le_card fun X hX => ?_)
  simp only [Finset.mem_compl, mem_exposedTo]
  exact fun h => h.not_correct hb hX

/-- **A DoS-valid universe on the reactive schedule is a run.** The DAG
is the universe, the pace is the reactive one, and the liveness input is
`commits_of_reactive`; the tie-break is `chooseLeast`. Four of `Run`'s
fields that a caller would otherwise discharge are `rfl` or theorems
here: the two readings of the blocks, the self-parent edge, and the
schedule's leader being the DAG's.

The horizon of the schedule serves as the horizon of the liveness
argument, so no relation between them is asked for. -/
noncomputable def Run.ofDoSValidReactive [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (hdos : DoSValid U) {N : ℕ}
    (rm : ReactiveM U (Correct : Finset Validator) N)
    (hround : ∀ k, S.slotRound k = k) (hrr : RoundRobin S.leader)
    (horizon : ℕ) (rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ horizon)
    (rounds_advance : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ rm.top u,
      n ≤ rm.built u n)
    (stable : ℕ) (hgst : rm.gst ≤ stable)
    (hto : ∀ n, stable ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) :
    Run Validator BlockId Payload :=
  Run.ofDoSValid U S.leader hdos horizon rounds_le N rm.toPaceCore rounds_advance
    stable hgst N
    (commits_of_reactive rm rfl rfl hround (fun _ => rfl) (fun _ => rfl) rfl hgst hto)
    (le_refl N) hrr

end FinWhale

end LeanDag
