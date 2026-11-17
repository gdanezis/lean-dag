import LeanDag.Timed.Coverage
/-!
# A good DAG whose crashed validators are silent

`Timed.Good` describes a synchronised quorum `T` and nothing else. After
every crash has happened, a crashed validator authors no block, and the
validators that are neither synchronised nor crashed are at most the
Byzantine ones. `SilentGood R rel fb U Rnd N` adds a set `Z` of validators
with no block at a round from `Rnd` on, and asks that at most `fb`
validators lie outside `T ∪ Z`.
-/

namespace LeanDag

namespace Timed

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A good DAG whose crashed validators are silent from `Rnd`.** -/
def SilentGood (R : Properties.DagRule Validator BlockId Payload) (rel : Reliability Validator)
    (fb : ℕ) (U : R.Universe) (Rnd N : ℕ) : Prop :=
  ∃ T Z : Finset Validator, rel.IsQuorum T ∧ SynchronisedOn R U T Rnd ∧
    (∀ r, Rnd ≤ r → r ≤ N → Properties.PopulatedOn R U T r) ∧
    (∀ b ∈ R.ids U, (R.block U b).creator ∈ Z → (R.block U b).round < Rnd) ∧
    Fintype.card Validator ≤ (T ∪ Z).card + fb

theorem SilentGood.good {R : Properties.DagRule Validator BlockId Payload}
    {rel : Reliability Validator} {fb : ℕ} {U : R.Universe} {Rnd N : ℕ}
    (h : SilentGood R rel fb U Rnd N) : Good R rel U Rnd N := by
  obtain ⟨T, -, hq, hs, hpop, -, -⟩ := h
  exact ⟨T, hq, hs, hpop⟩

end Timed

end LeanDag
