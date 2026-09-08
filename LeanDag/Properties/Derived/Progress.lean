import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Derived.Bounded
/-!
# A committed run decides everything below it

`docs/target-properties.md` §11.4c. A mechanism adding blocks cannot
stall a protocol: `LeaderCommits` gives the run, `Descends` gives
everything under it, a consequence of the two rather than a composition
of mechanisms. What the crash-recovery arc wants: a fill's fresh,
undecided candidate does not stay that way once a run of `c`
reliable-led slots above it commits.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Everything below a reliable-led run is decided.** The run's slots
commit by `LeaderCommits`, and `Descends` settles the rest. -/
theorem decidedBelow_of_run
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop}
    (hlc : LeaderCommits R Live) {S : Slots Validator} {c : ℕ}
    (hd : Descends R S c) {U : R.Universe} (V : R.View U) (T : Finset Validator) (b : ℕ)
    (hlive : Live S V T b (b + c)) (hlead : ∀ i, i < c → S.leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V i v := by
  refine hd V b (fun j hj1 hj2 => ?_)
  have hjT : S.leader j ∈ T := by
    have := hlead (j - b) (by omega)
    have hjb : b + (j - b) = j := by omega
    rwa [hjb] at this
  obtain ⟨L, hL⟩ := hlc S V T b (b + c) hlive j hj1 hj2 hjT
  exact ⟨L, hL.mono (by omega)⟩

/-- And the verdicts of the run itself. -/
theorem decidedBelow_run
    {Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop}
    (hlc : LeaderCommits R Live) {S : Slots Validator} {c : ℕ}
    {U : R.Universe} (V : R.View U) (T : Finset Validator) (b : ℕ)
    (hlive : Live S V T b (b + c)) (hlead : ∀ i, i < c → S.leader (b + i) ∈ T) :
    ∀ j, b ≤ j → j < b + c → ∃ L, DecidedBelow R S (b + c) V j (some L) := by
  intro j hj1 hj2
  have hjT : S.leader j ∈ T := by
    have := hlead (j - b) (by omega)
    have hjb : b + (j - b) = j := by omega
    rwa [hjb] at this
  obtain ⟨L, hL⟩ := hlc S V T b (b + c) hlive j hj1 hj2 hjT
  exact ⟨L, hL.mono (by omega)⟩

end Properties

end LeanDag
