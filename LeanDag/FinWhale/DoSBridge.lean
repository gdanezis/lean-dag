import LeanDag.FinWhale.Procedure.Protocol
import LeanDag.FinWhale.Reactive
import LeanDag.DoS.Exposure
/-!
# A DoS-valid Mysticeti universe is a FinWhale DAG

`DoSValid` (`dos-equivocation-and-growth.md`) forbids citing an author a
block's own history convicts of equivocating — the leader clause with
its narrowings removed — so a `BlockUniverse` satisfying it is a
FinWhale DAG at any leader schedule, self-parent edge included, and the
whole arc applies to it with no further hypothesis.
`Run.ofDoSValidReactive` supplies the liveness input from the core's
reactive schedule; the two disciplines do not collide because both
citation obligations there are confined to reliable authors.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

omit P in
/-- **The DoS condition implies the leader clause**: two conflicting
versions an inconsistent parent set votes for are both in the block's
history, so the leader is exposed and may not be cited. -/
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
validator is ever exposed, so the condition costs nothing to a builder
that builds on correct validators' blocks. -/
theorem not_exposed_of_correct_parents {b : BlockId} (hb : b ∈ U.ids)
    (h : ∀ i ∈ (U.block b).refs, (U.block i).creator ∈ (Correct : Finset Validator)) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator :=
  fun i hi hexp => hexp.not_correct hb (h i hi)

variable [S : Slots Validator]

/-- **Correct authors are always citable**: an exposed author has
equivocated, hence is Byzantine, so the condition never forbids citing
a correct validator. -/
theorem citable_of_correct {b : BlockId} (hb : b ∈ U.ids) {X : Validator}
    (hX : X ∈ (Correct : Finset Validator)) : ¬ ExposedIn U b X :=
  fun h => absurd hX (by simpa using h.not_correct hb)

omit P S in
/-- **The condition never exhausts a builder's parents.** The authors it
withdraws are convicted equivocators, hence Byzantine and at most `f`,
so the citable authors always include a validity quorum of `n − f`. -/
theorem quorumCard_le_citable {b : BlockId} (hb : b ∈ U.ids) :
    quorumCard Validator ≤ ((exposedTo U b)ᶜ).card := by
  refine le_trans card_correct (Finset.card_le_card fun X hX => ?_)
  simp only [Finset.mem_compl, mem_exposedTo]
  exact fun h => h.not_correct hb hX

end FinWhale

end LeanDag
