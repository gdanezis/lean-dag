import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Vote profiles on one contended object

Trusted core for the paper's protocol-independent section, "Fundamental
limits of vote revocation" (`10.InherentLimitation.tex`). Definitions
only — every lemma lives in `Helpers/`, every claim in
`Revocation/Statement.lean`.

The section makes no assumption about a protocol, a committee bound, or
which votes are hidden from whom: `n` validators, at most `f` of them
Byzantine, vote for values that conflict pairwise (one object, several
candidates), and a correct validator votes for at most one of them. A
`Profile` is the *global* record of who is observed voting for what —
Byzantine validators may appear under several values — so that any
collection of observed votes is a subset of it. The section is therefore
stated independently of `Faults`: `Profile` carries its own `f` and no
committee bound, and the corollaries at the protocol's thresholds are
stated separately, over `Faults`.
-/

namespace LeanDag

namespace RedSnapper

/-- Who votes for what, on one contended object: every value conflicts
with every other, so a correct validator votes for at most one. -/
structure Profile (Validator Value : Type*) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq Value] where
  /-- The Byzantine fault bound. -/
  f : ℕ
  /-- The Byzantine validators of the profile. -/
  byzantine : Finset Validator
  /-- At most `f` validators are Byzantine. -/
  card_byzantine : byzantine.card ≤ f
  /-- The values each validator is observed voting for; empty for a
  validator that has not voted. -/
  votes : Validator → Finset Value
  /-- A correct validator votes for at most one value. -/
  honest_single : ∀ v, v ∉ byzantine → (votes v).card ≤ 1

section Counting

variable {Validator Value : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq Value]

/-- The validators observed voting for `x`. -/
def supporters (P : Profile Validator Value) (x : Value) : Finset Validator :=
  Finset.univ.filter fun v => x ∈ P.votes v

/-- The validators observed voting for a value conflicting with `x`, that
is, for any value other than `x`. A Byzantine validator may support and
oppose `x` at once. -/
def opposers (P : Profile Validator Value) (x : Value) : Finset Validator :=
  Finset.univ.filter fun v => ∃ y ∈ P.votes v, y ≠ x

/-- The validators that have voted at all. Every voter supports `x` or
opposes it, and a Byzantine one may do both. -/
def voters (P : Profile Validator Value) : Finset Validator :=
  Finset.univ.filter fun v => (P.votes v).Nonempty

end Counting

end RedSnapper

end LeanDag
