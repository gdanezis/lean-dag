import LeanDag.Common.Causality
import LeanDag.Common.Schedule
/-!
# The carrier a target property talks about

`docs/target-properties.md` G0. `DagRule` is the shape `Barnacle.BaseRule`
already has — a universe type, a dependent view type, projections into
the shared `Block` vocabulary, and the decision relation — restated
here rather than imported, since mechanisms depend on properties and
properties depend on nothing: a `Properties` importing Barnacle would
tie every other mechanism to the adaptive leader count.

`Decided` is a field with no constructors, so nothing here can induct
on a derivation. Locality and persistence are *hypotheses* a protocol
discharges by induction over its own relation; the mechanism theorems
then consume them without induction. Beside `DagRule` this file gives
the `causal` law and `AgreeAbove`, the agreement notion locality reads.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **What a mechanism may read of a protocol**: a universe type, views
over it, the projections into `Block`, and the decision relation —
smaller than `Barnacle.BaseRule`, which adds what its own mechanism
needs. -/
structure DagRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type) where
  /-- The universe type of the base development. -/
  Universe : Type
  /-- The view type, indexed by universe. -/
  View : Universe → Type
  /-- The block an id denotes: round, creator and references. -/
  block : Universe → BlockId → Block Validator BlockId Payload
  /-- The ids of the universe. -/
  ids : Universe → Finset BlockId
  /-- The ids a view holds. -/
  viewIds : ∀ {U : Universe}, View U → Finset BlockId
  /-- A view holds only blocks the universe has. Every protocol's view
  type carries this proof already, so it costs an instance nothing. -/
  viewSound : ∀ {U : Universe} (V : View U), viewIds V ⊆ ids U
  /-- A view is closed under references: it holds what its blocks point
  at, which is what a window count needs to be measurement-independent
  (`Barnacle/Window/`). -/
  viewComplete : ∀ {U : Universe} (V : View U),
    ∀ i ∈ viewIds V, ∀ j ∈ (block U i).refs, j ∈ viewIds V
  /-- **A universe is a block DAG**: every reference is present and sits
  one round below. A fact about the DAG model, carried by every
  universe's validity record, rather than a rule-specific property. -/
  causal : ∀ U : Universe, CausalStructure (block U) (ids U)
  /-- The decision relation under a schedule. -/
  Decided : Slots Validator → ∀ {U : Universe}, View U → ℕ → Option BlockId → Prop

/-- **One DAG is another above a round, rebased.** At and above `R₀`
the two universes hold the same blocks, at rounds `G` apart, with the
same authors; strictly above `R₀`, the same references too. Nothing is
said below `R₀`, where a mechanism does its work. One relation serves a
truncation (`R₀ = G`), a fill or extension (no rebasing), and plain
agreement (the zero offset, `AgreeAbove`). References are compared
strictly above `R₀`: a truncation empties its bottom layer's
references, and every rule reads a vote from a parent, so a block at
exactly `R₀` contributes presence and authorship but no vote. -/
structure RebasedAbove (R : DagRule Validator BlockId Payload)
    (U U' : R.Universe) (G R₀ : ℕ) : Prop where
  /-- The same blocks at and above `R₀`. -/
  mem : ∀ b, (b ∈ R.ids U ∧ R₀ ≤ (R.block U b).round) ↔
    (b ∈ R.ids U' ∧ R₀ ≤ (R.block U' b).round + G)
  /-- At rounds `G` apart. Additive, so truncated subtraction never
  appears. -/
  round : ∀ b, b ∈ R.ids U → R₀ ≤ (R.block U b).round →
    (R.block U' b).round + G = (R.block U b).round
  /-- With the same author. -/
  creator : ∀ b, b ∈ R.ids U → R₀ ≤ (R.block U b).round →
    (R.block U' b).creator = (R.block U b).creator
  /-- And, strictly above, the same references. -/
  refs : ∀ b, b ∈ R.ids U → R₀ < (R.block U b).round →
    (R.block U' b).refs = (R.block U b).refs

/-- **Two universes agree above a round**: `RebasedAbove` at no
offset. -/
abbrev AgreeAbove (R : DagRule Validator BlockId Payload)
    (U U' : R.Universe) (r : ℕ) : Prop := RebasedAbove R U U' 0 r

namespace RebasedAbove

variable {R : DagRule Validator BlockId Payload} {U U' : R.Universe} {G R₀ : ℕ}

/-- A block of the target at or above the settling round is a block of
the source, at the shifted round. -/
theorem of_mem' (h : RebasedAbove R U U' G R₀) {b : BlockId} (hb : b ∈ R.ids U')
    (hr : R₀ ≤ (R.block U' b).round + G) :
    b ∈ R.ids U ∧ (R.block U' b).round + G = (R.block U b).round := by
  have hU := (h.mem b).mpr ⟨hb, hr⟩
  exact ⟨hU.1, h.round b hU.1 hU.2⟩

end RebasedAbove

/-- **What a block above the cut references is itself above the cut** —
a fact about causal structure alone, and the step an induction over a
derivation's anchors needs, since it says the region agreement covers
is closed under the recursion. -/
theorem DagRule.causal_refs_above {R : DagRule Validator BlockId Payload}
    {U : R.Universe} {r : ℕ}
    {b : BlockId} (hb : b ∈ R.ids U) (hr : r < (R.block U b).round)
    {j : BlockId} (hj : j ∈ (R.block U b).refs) :
    j ∈ R.ids U ∧ r ≤ (R.block U j).round := by
  refine ⟨(R.causal U).complete b hb j hj, ?_⟩
  have := (R.causal U).refs_round b hb j hj
  omega

end Properties

end LeanDag
