import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.OptimalHydrozoan.Helpers.DirectRules
import LeanDag.Common.Anchored.Bounded
/-!
# Optimal-Hydrozoan: decision-relation lemmas

Generated proof infrastructure over `Optimal/Model/Decided.lean`; not
part of the audit surface. The rule's data, and each rung's choice: the
rule has no tie at either rung, so any linked candidate is the choice.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica]

@[simp] theorem optimalAnchored_waveAt (r : ℕ) :
    (optimalAnchored Replica BlockId).waveAt r = 2 := rfl

@[simp] theorem optimalAnchored_rungs : (optimalAnchored Replica BlockId).rungs = 2 := rfl

section Decidable

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

instance (V : LeanDag.Hydrozoan.View U) (L : BlockId) (r : ℕ) :
    Decidable ((optimalAnchored Replica BlockId).Commit U V L r) :=
  inferInstanceAs (Decidable (FastCommitOptInView U V L r ∨ SlowCommitInView U V L r))

instance [Fintype BlockId] (V : LeanDag.Hydrozoan.View U) (S : Slots Replica) (k : ℕ) :
    Decidable ((optimalAnchored Replica BlockId).Skip U V S k) :=
  inferInstanceAs (Decidable (SkippedLeaderOptInView (S := S) U V k))

end Decidable

variable [S : Slots Replica] {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- **Each rung has a choice**: no tie, so any linked candidate. -/
theorem exists_least {A : BlockId} {i k : ℕ} (_ : i < (optimalAnchored Replica BlockId).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧ (optimalAnchored Replica BlockId).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧ (optimalAnchored Replica BlockId).Link i U A L S k ∧
      (optimalAnchored Replica BlockId).Least (S := S) U A i k L :=
  let ⟨L, hL, hl⟩ := h
  ⟨L, hL, hl, AnchoredRule.least_of_no_tie (fun _ _ h => h)⟩

end OptimalHydrozoan

end LeanDag
