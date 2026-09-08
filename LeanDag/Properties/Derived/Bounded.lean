import LeanDag.Properties.Bounded
/-!
# The laws of a bounded verdict

`docs/target-properties.md` §11.4b. Nothing here is an obligation:
`DecidedBelow` is a definition, so what a mechanism reads of it is
theorems, proved once for every rule. `mono` says a larger bound claims
less; `reschedule` is what used to be the obligation `SchedLocal` —
schedules agreeing below the bound carry the same bounded verdicts; and
`agree` is `Agree` read through the verdict inside.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

namespace DecidedBelow

variable {S : Slots Validator} {B B' : ℕ} {U : R.Universe} {V : R.View U}
variable {k : ℕ} {v : Option BlockId}

/-- Forgetting the bound leaves an ordinary verdict. -/
theorem toDecided (h : DecidedBelow R S B V k v) : R.Decided S V k v := h.2.1

/-- The decided slot lies below the bound. -/
theorem lt_bound (h : DecidedBelow R S B V k v) : k < B := h.1

/-- The bound relaxes upward: a larger bound asks agreement of more
leaders, so it is a weaker claim. -/
theorem mono (h : DecidedBelow R S B V k v) (hBB : B ≤ B') : DecidedBelow R S B' V k v := by
  obtain ⟨hk, hd, ht⟩ := h
  exact ⟨by omega, hd, fun S' hround hlead => ht S' hround (fun m hm => hlead m (by omega))⟩

/-- **Locality in the schedule**, which was a property to prove and is
now a theorem: two schedules with one round structure, agreeing on the
leaders below the bound, carry the same bounded verdicts. -/
theorem reschedule (h : DecidedBelow R S B V k v) {S' : Slots Validator}
    (hround : S'.slotRound = S.slotRound) (hlead : ∀ m, m < B → S'.leader m = S.leader m) :
    DecidedBelow R S' B V k v :=
  ⟨h.1, h.2.2 S' hround hlead, fun S'' hround' hlead' =>
    h.2.2 S'' (by rw [hround', hround]) (fun m hm => by rw [hlead' m hm, hlead m hm])⟩

/-- Two bounded verdicts agree, at any bounds — `Agree` through the
first component. -/
theorem agree (ha : Agree R) {S : Slots Validator} {U : R.Universe} {V₁ V₂ : R.View U}
    {B₁ B₂ k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : DecidedBelow R S B₁ V₁ k v₁) (h₂ : DecidedBelow R S B₂ V₂ k v₂) : v₁ = v₂ :=
  ha S V₁ V₂ k v₁ v₂ h₁.toDecided h₂.toDecided

end DecidedBelow

end Properties

end LeanDag
