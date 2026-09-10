import LeanDag.Integration.CompRun
import LeanDag.Barnacle.Model.Live
/-!
# Validity of the composition

`Barnacle/Validity` is BN14: a good author's block two rounds below a
closed configuration's anchor lies in the causal history of the block
that configuration commits. It turns on the anchor being a candidate of
its own slot, which `Composed.anchor_isCandidate` supplies, and on the
delivery law, which is the rule's and not the mechanism's.

The only thing that moves is how the anchor's round is read: Barnacle
divides the slot by the count, a frame takes `F.roundOf`.

**Trusted core: nothing. Every declaration is a theorem.**
-/

namespace LeanDag
namespace Integration

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

namespace Composed

/-- **BN14 at a composed run.** On a good DAG there is a set of all but
`slack` validators each of whose blocks, past the synchrony round, under
the horizon, and two rounds below a closed configuration's anchor, is in
the history of the block that configuration commits.

The composed run owes nothing extra: `anchor_closed` already puts the
anchor in an epoch the run has decided, which is what reading its verdict
needs. -/
theorem delivered {R : LiveRule Validator BlockId Payload}
    (hcc : Properties.CommitsCandidate R.toBaseRule.toDagRule)
    {slack : ℕ} (hdel : R.Delivers slack)
    {W : ℕ} {P : Params}
    {pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator}
    {upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ}
    {U : R.Universe} {V : R.View U} {K H : ℕ}
    (Rn : Composed (R := R.toBaseRule.toDagRule) W P pick upd U V K H)
    (Rnd N : ℕ) (hgood : R.Good U Rnd N) :
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ b ∈ R.ids U, (R.block U b).creator ∈ T → Rnd ≤ (R.block U b).round →
        (R.block U b).round + 1 ≤ N →
        ∀ k, k < K → (R.block U b).round + 2 ≤ Rn.F.roundOf (Rn.anchor k) →
          ∃ A, Rn.vdct (Rn.anchor k) = some A ∧ b ∈ historyFrom (R.block U) A := by
  obtain ⟨T, hcard, hT⟩ := hdel.reaches U Rnd N hgood
  refine ⟨T, hcard, ?_⟩
  intro b hb hbT hRnd hN k hkK hround
  obtain ⟨⟨A, hA⟩, -⟩ := Rn.anchor_commits k hkK
  refine ⟨A, hA, ?_⟩
  obtain ⟨hAids, hAr, -⟩ := Rn.anchor_isCandidate hcc hkK (Rn.anchor_closed k hkK) hA
  refine hT b hb hbT hRnd hN A hAids ?_
  have hlink : (R.toBaseRule.toDagRule.block U A).round = (R.block U A).round := rfl
  rw [← hlink, hAr]
  exact hround

end Composed

end Integration

end LeanDag
