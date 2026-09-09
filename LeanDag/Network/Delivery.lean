import LeanDag.Common.Participation
import LeanDag.Common.BlockDag
import LeanDag.Common.Support
/-!
# The delivery layer

What each validator actually received, one round at a time, as distinct
from what the DAG records. `Delivery` contains no clock and no commit
rule: a timeout's only trace, with no time model, is a larger `held`,
which `EventuallyDelivers` then demands after `R`. The rate-limiting and
garbage-collection arcs read this and nothing of a protocol.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The all-of-`Correct` case, which is what L1 produces. -/
abbrev Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Validator) r

/-! ## The delivery layer

`held` says what a validator has
actually received, as distinct from `builds`' quorum-in-view rule and
`Synchronised`'s reference guarantee, which otherwise have to be stated
on `refs` and hoped to coincide. It contains no clock: a timeout's only
trace, with no time model, is a larger `held`, which `EventuallyDelivers`
then demands after `R`. -/

/-- What each validator had in hand, one round at a time, and which of
it it chose to build on. Two fields because delivery and policy are two
things: a structure demanding a correct validator reference everything
it `held` would be unsatisfiable the moment it holds both halves of an
equivocation, since `distinct_creators` forbids referencing both
(`dos-equivocation-and-growth.md` §4). `held` is not deduplicated,
since `U` is every block some correct validator held. -/
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  /-- Held ids are real blocks of the stated round — what keeps `Delivery`
  meaningful, since without it `held` could be junk and `includes` would
  demand blocks reference it. -/
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- What `v` chose to build on: a subset of what it held. -/
  accepted : Validator → ℕ → Finset BlockId
  /-- You can only accept what arrived. -/
  accepted_sub : ∀ v n, accepted v n ⊆ held v n
  /-- **The acceptance rule**: at most one block per author. Forced by
  `distinct_creators` — a validator holding two blocks by one author must pick
  one, because it cannot reference both. -/
  accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
    (U.block i).creator = (U.block j).creator → i = j
  /-- A correct block is always accepted. It never conflicts with anything —
  its author has only the one block for that round (T1) — so nothing is ever
  given up by taking it, and L7 needs it. -/
  accepts_correct : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ accepted v n
  /-- **The protocol rule.** A correct validator references everything it
  accepted. Implementable and observable — unlike `Synchronised` itself. -/
  includes : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs


omit [DecidableEq BlockId] in
/-- A populated round carries a quorum of authors — the step that feeds a
production induction back into its build rule, and the first consumer
`card_correct` was kept for. -/
theorem card_authorsAt_of_populated {r : ℕ} (h : Populated U r) :
    quorumCard Validator ≤ (authorsAt U r).card := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨b, hb, hbc, hbr⟩ := h w hw
  exact mem_authorsAt.mpr ⟨b, hb, hbr, hbc⟩


omit [DecidableEq BlockId] in
/-! **`SynchronisedOn`** (`Participation.lean`) is the post-stabilisation
coverage assumption: from round `R` on, every `T`-authored block
references every `T`-authored block of the round below. It does not
follow from view convergence — a block's references are frozen when
built — so it is an assumption, not a theorem. -/

/-- The all-of-`Correct` case. -/
abbrev Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Validator) R

/-! ## L7 — `Synchronised`, derived

`Synchronised` welds a protocol rule and a
network guarantee into one object stated on `refs`, since the static
model has no delivery layer to state it on separately. Splitting it
into `includes` (implementable and observable) plus
`EventuallyDelivers` (pure network) gains nothing logically — the chain
still bottoms out at delivery — but gives the timeout, which governs
when a validator builds, somewhere real to live. -/

/-- **The network assumption**: after `R`, correct blocks reach correct
validators in time to be built on. This is eventual DAG synchrony proper —
pure delivery, no protocol content. -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n

end LeanDag
