import LeanDag.Properties.Support
import LeanDag.Properties.Derived.Bounded
/-!
# `LeaderCommits`, from a support

`docs/target-properties.md` §11.8. `LeaderCommits R Live` is now a
consequence of `Support`, not an obligation: `Support.live` is the
precondition in the support's own terms — certification of every
candidate of every quorum-led slot in the window, on a caught-up view —
and Law 3 turns it into the verdict. The definition stays, since the
schedule mechanisms (`Derived/Progress.lean`, `Arcs/Quality.lean`,
Barnacle) read `LeaderCommits` and never a support directly.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A reliable leader's slot commits**, within a bound one above it,
wherever the protocol's precondition `Live` holds over a slot window
containing the slot. -/
def LeaderCommits (R : DagRule Validator BlockId Payload)
    (Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop) :
    Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (T : Finset Validator) (lo K : ℕ),
    Live S V T lo K → ∀ k, lo ≤ k → k < K → S.leader k ∈ T →
      ∃ L, DecidedBelow R S (k + 1) V k (some L)

namespace Support

variable (sp : Support R)

/-- **The liveness precondition, in support terms.** A quorum, a horizon
the view is caught up to with the window a wave under it, and at every
quorum-led slot of the window production and certification. -/
def live (rel : Reliability Validator) (S : Slots Validator) {U : R.Universe}
    (V : R.View U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  rel.IsQuorum T ∧
    ∃ N, CoversUpto R V N ∧ (∀ k, k < K → S.slotRound k + sp.wave ≤ N) ∧
      ∀ k, lo ≤ k → k < K → S.leader k ∈ T →
        (∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + sp.wave → PopulatedOn R U T n) ∧
        ∀ L, R.IsCandidate S U k L → sp.certifiesAt U T (S.slotRound k) L

/-- **`LeaderCommits`, from Law 3.** -/
theorem leaderCommits {rel : Reliability Validator} (hlc : sp.Commits rel) :
    LeaderCommits R (fun S {U} V T lo K => sp.live rel S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hq, N, hcov, hN, hslot⟩ := hlive
  obtain ⟨hpop, hcert⟩ := hslot k hlo hK hlead
  exact hlc S V T k hq hpop hcert (hcov.mono (hN k hK)) hlead

end Support

end Properties

end LeanDag
