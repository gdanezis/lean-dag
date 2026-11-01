import LeanDag.Common.Participation
import LeanDag.Common.BlockDag
import LeanDag.Common.Support
/-!
# The delivery layer

What each validator actually received, one round at a time, as distinct
from what the DAG records. `Delivery` contains no clock and no commit
rule: a timeout's only trace, with no time model, is a larger `held`,
which `EventuallyDeliversOn` then demands after `R`. The rate-limiting
and garbage-collection arcs read this and nothing of a protocol.

The layer is stated on any block record, its honest set the validators
that follow the acceptance and inclusion rules; the density lemmas (L0)
at the record's quorum `q`. The delivery assumption names the receivers
`T`, the validators that stay up, and covers the blocks of every honest
author. The core's `Populated`, `Synchronised` and `EventuallyDelivers`
are the cases at `Correct`.
-/

namespace LeanDag

section General

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

omit [DecidableEq BlockId] in
/-- A round with any author at all has a block. The bridge that lets L0's
induction step back down: a cardinality bound on `authorsAt` is turned into
a witness block, which the next step then references from. -/
theorem exists_mem_of_authorsAt_card_pos {n : ℕ} (h : 0 < (authorsAt U n).card) :
    ∃ i ∈ U.ids, (U.block i).round = n := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  obtain ⟨i, hi, hir, _⟩ := mem_authorsAt.mp hv
  exact ⟨i, hi, hir⟩
omit [DecidableEq BlockId] in
/-- One step of L0: a block at round `n+1` forces a quorum of authors at
round `n`, immediate from validity — its references carry `q` distinct
creators, each holding a round-`n` block. -/
theorem card_authorsAt_of_succ [P.Mechanised] {q : ℕ} [P.Quorate q] {n : ℕ} {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = n + 1) :
    q ≤ (authorsAt U n).card :=
  le_trans (U.creators_quorum hi (by omega))
    (Finset.card_le_card (creators_refs_subset_authorsAt hi hir))
omit [DecidableEq BlockId] in
/-- **L0 — the DAG is dense below its frontier.** If any block exists at
round `r`, every round `n < r` has at least `q` distinct authors:
downward induction on the gap `r - n`, generalised over `n` so the step
can re-enter at `n+1`. -/
theorem card_authorsAt_of_lt [P.Mechanised] {q : ℕ} [P.Quorate q] {r n : ℕ} (hn : n < r)
    {i : BlockId} (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    q ≤ (authorsAt U n).card := by
  obtain ⟨d, rfl⟩ : ∃ d, r = n + 1 + d := ⟨r - n - 1, by omega⟩
  clear hn
  induction d generalizing n i with
  | zero => exact card_authorsAt_of_succ hi hir
  | succ d ih =>
      have h1 : q ≤ (authorsAt U (n + 1)).card :=
        ih (n := n + 1) (i := i) hi (by omega)
      obtain ⟨j, hj, hjr⟩ := exists_mem_of_authorsAt_card_pos (U := U) (n := n + 1)
        (by have := Validity.Quorate.pos (P := P) (q := q); omega)
      exact card_authorsAt_of_succ hj hjr


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
structure Delivery (U : BlockRecord Validator BlockId Payload P honest) where
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
  /-- An honest block is always accepted by an honest validator. It never
  conflicts with anything — its author has only the one block for that round
  (T1) — so nothing is ever given up by taking it, and L7 needs it. -/
  accepts_correct : ∀ v ∈ honest, ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ honest → a ∈ accepted v n
  /-- **The protocol rule.** An honest validator references everything it
  accepted. Implementable and observable — unlike `Synchronised` itself. -/
  includes : ∀ v ∈ honest, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs


/-- **The network assumption**: after `R`, the blocks of honest authors
reach the receivers `T` in time to be built on. This is eventual DAG
synchrony proper — pure delivery, no protocol content. A crash-prone
validator is honest but need not be among the receivers. -/
def EventuallyDeliversOn (D : Delivery U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ T, ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ honest → a ∈ D.held v n

end General

/-! ## The core

At the core's universes the honest set is `Correct`, and every correct
validator receives. -/

section Core

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The all-of-`Correct` case, which is what L1 produces. -/
abbrev Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Validator) r

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

/-! **`SynchronisedOn`** (`Participation.lean`) is the post-stabilisation
coverage assumption: from round `R` on, every `T`-authored block
references every `T`-authored block of the round below. It does not
follow from view convergence — a block's references are frozen when
built — so it is an assumption, not a theorem. -/

/-- The all-of-`Correct` case. -/
abbrev Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Validator) R

/-- **The core's network assumption**: after `R`, correct blocks reach
correct validators. -/
abbrev EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  EventuallyDeliversOn D (Correct : Finset Validator) R

end Core

end LeanDag
