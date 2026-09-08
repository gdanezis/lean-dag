import LeanDag.Properties.Extends
import LeanDag.Properties.Truncate
import LeanDag.Common.Participation
/-!
# What a mechanism owes a protocol, so liveness survives

`docs/target-properties.md` §3.6. Safety transports a derivation, so
only the protocol can carry it (`Persist`, `LocalTruncate`); liveness
transports a DAG, and a protocol's liveness theorem, being universally
quantified over universes, applies to the transformed one unchanged —
all the work is on the mechanism's side, and `Sustains` names it.

`Sustains` promises the blocks, not any predicate: above a settling
round `R₀` an old block keeps its membership, author, references and
its round shifted by `G`, so **every** predicate computed from those —
votes, production, a protocol's own certificate layer — transports with
it. The settling round is where a fill or truncation stops adding
content, and references are compared strictly above `R₀` so a
truncation's emptied bottom layer is admitted.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **What the commit rules count**: every `T`-authored block one round
above `r` references `L`. The carrier's reading of `LeanDag.VotesAt`. -/
def VotesAt (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c, c ∈ R.ids U → (R.block U c).creator = v →
    (R.block U c).round = r + 1 → L ∈ (R.block U c).refs

/-- **No equivocation by `T`**: at most one block per `T`-author per
round. A fault-model invariant rather than a delivery one, and the only
member of this family that a mechanism can *break*: a cut cannot, since
it removes blocks, but a fill or a re-genesis adds one and must argue
that the author it speaks for was silent there. -/
def NoEquivOn (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) : Prop :=
  ∀ i, i ∈ R.ids U → ∀ j, j ∈ R.ids U → (R.block U i).creator ∈ T →
    (R.block U i).creator = (R.block U j).creator →
    (R.block U i).round = (R.block U j).round → i = j

/-- **Production**: every member of `T` has a block at round `r`. -/
def PopulatedOn (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r : ℕ) : Prop :=
  PopulatedFrom (R.block U) (R.ids U) T r

/-- Decidable on concrete data, at any carrier. -/
instance instDecidablePopulatedOn (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r : ℕ) : Decidable (PopulatedOn R U T r) :=
  inferInstanceAs (Decidable (PopulatedFrom (R.block U) (R.ids U) T r))

/-! ## The additive half

`Sustains` is silent below `R₀`, where a fill or re-genesis adds blocks
`Sustains` cannot speak for. A mechanism that repairs production there
exhibits one singleton, `PopulatedOn R U' {v} r`, and the plumbing from
it to the reliable set is derived from `Extends` alone, once. -/

/-- **An extension that seats one author seats the set**: production by
`T` plus a singleton block by `v` gives production by `insert v T`, old
blocks surviving the extension unchanged. -/
theorem populatedOn_insert_of_extends {R : DagRule Validator BlockId Payload}
    {U U' : R.Universe} {T : Finset Validator} {v : Validator} {r : ℕ}
    (he : Extends R U U') (hnew : PopulatedOn R U' {v} r)
    (hpop : PopulatedOn R U T r) :
    PopulatedOn R U' (insert v T) r := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hwT
  · exact hnew w (Finset.mem_singleton_self w)
  · obtain ⟨b, hb, hbr, hbc⟩ := hpop w hwT
    exact ⟨b, he.subset b hb, by rw [he.block b hb]; exact hbr,
      by rw [he.block b hb]; exact hbc⟩

/-- **A mechanism sustains from round `R₀`**, re-indexing by `G`: this
is `RebasedAbove`, under the name the obligation is owed in. The
relation is the same one a truncation and a plain agreement satisfy
(`Properties/Carrier.lean`); what differs is who owes it. -/
abbrev Sustains (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (G R₀ : ℕ) : Prop := RebasedAbove R U U' G R₀

/-- **A cut cannot introduce equivocation.** It holds a subset of the
blocks at rebased rounds, and a restriction of an injection is
injective. Stated over `Truncates` rather than `Sustains` because that
is what says no block is *added*, which is the whole of the argument. -/
theorem noEquivOn_of_truncates {R : DagRule Validator BlockId Payload}
    {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}
    (h : Truncates R U U' S S' G d) {T : Finset Validator}
    (hne : NoEquivOn R U T) : NoEquivOn R U' T := by
  intro i hi j hj hic hij hround
  have hiU := (h.mem_iff i).mp hi
  have hjU := (h.mem_iff j).mp hj
  refine hne i hiU.1 j hjU.1 ?_ ?_ ?_
  · rwa [← h.creator_of hi]
  · rw [← h.creator_of hi, ← h.creator_of hj]; exact hij
  · have h1 := h.round_of hi
    have h2 := h.round_of hj
    omega

namespace RebasedAbove

variable {R : DagRule Validator BlockId Payload} {U U' : R.Universe} {G R₀ : ℕ}

/-- **Votes survive.** A `T`-block one round above `r` is old, keeps its
author and its references, so a vote it cast it casts still. -/
theorem votesAt_of (h : Sustains R U U' G R₀) {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hv : VotesAt R U T r L) : VotesAt R U' T (r - G) L := by
  intro v hvT c hc hcc hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc (by omega)
  have hUr : (R.block U c).round = r + 1 := by omega
  have hcc' : (R.block U c).creator = v := by rw [← h.creator c hcU (by omega)]; exact hcc
  rw [h.refs c hcU (by omega)]
  exact hv v hvT c hcU hcc' hUr

/-- **Production survives.** -/
theorem populatedOn_of (h : Sustains R U U' G R₀) {T : Finset Validator} {r : ℕ}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hp : PopulatedOn R U T r) : PopulatedOn R U' T (r - G) := by
  intro v hvT
  obtain ⟨b, hb, hbc, hbr⟩ := hp v hvT
  have hb' := ((h.mem b).mp ⟨hb, by omega⟩).1
  refine ⟨b, hb', ?_, ?_⟩
  · rw [h.creator b hb (by omega)]; exact hbc
  · have := h.round b hb (by omega); omega

end RebasedAbove

end Properties

end LeanDag
