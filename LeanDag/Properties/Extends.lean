import LeanDag.Properties.Candidate
/-!
# Persistence: verdicts survive a growing DAG

`docs/target-properties.md` §3.2 and §3.3. Every protocol's uniqueness
theorem compares two views of the *same* universe, so comparing a
replica that decided against one deciding later on a larger DAG needs
the first derivation moved into the second — the move this file names.

`Persist` is graded rather than absolute because the failure mode is
not a different verdict, which would be unsafety, but a derivation
ceasing to exist: a vacuous skip (nothing referenced) loses its premise
once a new block is added, where a counted skip does not. So `Persist`
carries a side condition `Ok` on the extension, and which condition a
protocol needs is a fact about its skip rule rather than bookkeeping.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **`U'` extends `U`**: it holds everything `U` held, and denotes
those blocks the same way. Nothing is said about what it adds — that is
`Novel` below, which the two fields already determine. -/
structure Extends (R : DagRule Validator BlockId Payload) (U U' : R.Universe) : Prop where
  /-- Every block of `U` is a block of `U'`. -/
  subset : ∀ b, b ∈ R.ids U → b ∈ R.ids U'
  /-- And denotes the same block: same round, author and references. -/
  block : ∀ b, b ∈ R.ids U → R.block U' b = R.block U b

/-- **What an extension adds**: a block the new universe has that the
old one lacked. -/
def Novel (R : DagRule Validator BlockId Payload) (U U' : R.Universe) (b : BlockId) : Prop :=
  b ∈ R.ids U' ∧ b ∉ R.ids U

namespace Extends

/-- **An old block references only old blocks**, so nothing that was
already present can reach what the extension added. This is the formal
content of "blocks nothing references cannot change a verdict", and it
is *derived* rather than assumed: an extension leaves old blocks alone,
and an old block's references were already inside `U`. -/
theorem old_refs_old (he : Extends R U U')
    {b : BlockId} (hb : b ∈ R.ids U) {j : BlockId} (hj : j ∈ (R.block U' b).refs) :
    j ∈ R.ids U := by
  rw [he.block b hb] at hj
  exact (R.causal U).complete b hb j hj

/-- Restated: an old block never references a novel identifier. -/
theorem not_novel_of_mem_refs (he : Extends R U U')
    {b : BlockId} (hb : b ∈ R.ids U) {j : BlockId} (hj : j ∈ (R.block U' b).refs) :
    ¬ Novel R U U' j :=
  fun hn => hn.2 (old_refs_old he hb hj)

/-- **Nothing an old block reaches is new**: `old_refs_old` propagated
along causal history. What every protocol's persistence proof turns on
— a rung test asks whether something is in reach of the anchor, and the
anchor of an old derivation is old, so the extension supplies no new
certificate, vote or candidate to any rung. -/
theorem reaches_old (he : Extends R U U')
    {A B : BlockId} (hA : A ∈ R.ids U) (h : ReachesFrom (R.block U') A B) :
    ReachesFrom (R.block U) A B ∧ B ∈ R.ids U := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hA⟩
  | @tail c b _ hstep ih =>
      have hc' : c ∈ R.ids U := ih.2
      have hb : b ∈ R.ids U := old_refs_old he hc' hstep
      refine ⟨ih.1.tail ?_, hb⟩
      have hstep' : b ∈ (R.block U' c).refs := hstep
      rw [he.block c hc'] at hstep'
      exact hstep'

/-- And so reachability from an old block is the same relation in both
universes. -/
theorem reaches_iff (he : Extends R U U')
    {A B : BlockId} (hA : A ∈ R.ids U) :
    ReachesFrom (R.block U') A B ↔ ReachesFrom (R.block U) A B := by
  refine ⟨fun h => (reaches_old he hA h).1, fun h => ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c b hAc hstep ih =>
      have hc' : c ∈ R.ids U := (R.causal U).mem_ids_of_reaches hA hAc
      refine ih.tail ?_
      have hstep' : b ∈ (R.block U c).refs := hstep
      show b ∈ (R.block U' c).refs
      rw [he.block c hc']; exact hstep'

/-- Extension is reflexive. -/
theorem refl {U : R.Universe} : Extends R U U :=
  { subset := fun _ h => h, block := fun _ _ => rfl }

/-- And transitive, so a sequence of extensions is one. -/
theorem trans {U U' U'' : R.Universe} (h : Extends R U U') (h' : Extends R U' U'') :
    Extends R U U'' where
  subset := fun b hb => h'.subset b (h.subset b hb)
  block := fun b hb => by rw [h'.block b (h.subset b hb), h.block b hb]

/-- An old block keeps its round. -/
theorem round (he : Extends R U U') {b : BlockId} (hb : b ∈ R.ids U) :
    (R.block U' b).round = (R.block U b).round := by rw [he.block b hb]

/-- And a candidate of `U` is a candidate of `U'` at the same slot. -/
theorem isCandidate {S : Slots Validator} (he : Extends R U U') {k : ℕ} {L : BlockId}
    (h : R.IsCandidate S U k L) : R.IsCandidate S U' k L := by
  obtain ⟨hm, hr, hc⟩ := h
  refine ⟨he.subset L hm, ?_, ?_⟩ <;> rw [he.block L hm] <;> assumption

end Extends

end Properties

end LeanDag
