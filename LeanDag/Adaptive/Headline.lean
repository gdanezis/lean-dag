import LeanDag.Adaptive.Agreement.Proof
import LeanDag.Adaptive.Ledger.Proof
import LeanDag.Adaptive.Progress.Proof
import LeanDag.Adaptive.Score.Proof
/-!
# What the arc guarantees a reputation score

The arc is stated for an arbitrary `UpdateRule`, which is what makes its
safety unconditional: nothing about the score can break it, because the
theorems never look at one. That generality is a hypothesis at the point
of use, though — a designer arrives with a score and wants to know what
holds of it, not what holds of every function of its type.

These three theorems are the answer, and they name no clause a score does
not already discharge. `Score.rule_anchored` is `rfl`, so the safety
results ask a reputation score for **nothing at all**; liveness asks for
`Score.Keeps` — move the leaders, leave the widths and the interval —
and for whatever clause the schedules it emits must satisfy.

There is no new content here: each is a generic theorem of the arc with
the score's own clause supplied, which is the step that removes the
hypothesis. The content is in `Agreement/`, `Ledger/`, `Progress/` and
`Score/`.
-/

namespace LeanDag

namespace Adaptive

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## Safety -/

section Safety

variable {R : BaseRule Validator BlockId Payload} {P : Params}

/-- **AL18a — a reputation score is safe, and owes nothing for it.** Two
validators running any score over one DAG from one genesis configuration
adopt the same configuration at every height both have reached, the same
anchor, and the same verdict at every slot of every range both have
closed.

No synchrony, no fairness, no window, and no clause on the score: the
only law consumed is the base protocol's own agreement (`Properties.Agree`,
M6 at the rule's carrier). A score chosen adversarially — reading the
anchor's whole causal history and the range's committed leaders, and
reassigning on what it finds — cannot split two correct validators,
because the two things it reads are settled before either applies it. -/
theorem score_safe (hR : Properties.Agree R.toDagRule) (score : Score R)
    (C₀ : Config Validator) (U : R.Universe) (V₁ V₂ : R.View U) {K₁ K₂ : ℕ}
    (R₁ : SegRun R P (rule score) C₀ U V₁ K₁) (R₂ : SegRun R P (rule score) C₀ U V₂ K₂)
    (k : ℕ) (hk : k ≤ min K₁ K₂) :
    R₁.start k = R₂.start k ∧ R₁.cfg k = R₂.cfg k ∧ R₁.backoff k = R₂.backoff k ∧
      (k < min K₁ K₂ → R₁.anchor k = R₂.anchor k ∧
        ∀ κ, R₁.start k < (R₁.cfg k).roundOf κ →
          (R₁.cfg k).roundOf κ ≤ (R₁.cfg k).roundOf (R₁.anchor k) →
            R₁.vdct k κ = R₂.vdct k κ) :=
  Agreement.holds _ _ _ R hR P (rule score) C₀ (Score.rule_anchored score)
    U V₁ V₂ K₁ K₂ R₁ R₂ k hk

/-- **AL18b — and they read one ledger.** Agreed across validators as far
as both have closed, a prefix of itself as it grows, and holding no block
twice. The three clauses M7 asks of any ordering, at a schedule the
validators themselves chose. -/
theorem score_ledger (hR : Properties.Agree R.toDagRule)
    (hc : Properties.CommitsCandidate R.toDagRule) (score : Score R)
    (C₀ : Config Validator) :
    (∀ (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
      (R₁ : SegRun R P (rule score) C₀ U V₁ K₁) (R₂ : SegRun R P (rule score) C₀ U V₂ K₂)
      (K : ℕ), K ≤ min K₁ K₂ → R₁.ledgerUpto K = R₂.ledgerUpto K) ∧
    (∀ (U : R.Universe) (V : R.View U) (K : ℕ) (Rn : SegRun R P (rule score) C₀ U V K)
      (K₁ K₂ : ℕ), K₁ ≤ K₂ → Rn.ledgerUpto K₁ <+: Rn.ledgerUpto K₂) ∧
    (∀ (U : R.Universe) (V : R.View U) (K : ℕ) (Rn : SegRun R P (rule score) C₀ U V K)
      (K' : ℕ), K' ≤ K → (Rn.ledgerUpto K').Nodup) :=
  let h := Ledger.holds _ _ _ R hR hc P (rule score) C₀ (Score.rule_anchored score)
  ⟨fun U V₁ V₂ K₁ K₂ R₁ R₂ => (h.1 U V₁ V₂ K₁ K₂ R₁ R₂).2, h.2.1, h.2.2⟩

end Safety

/-! ## Liveness -/

section Liveness

variable {RL : LiveRule Validator BlockId Payload} {P : Params}

/-- **AL18c — and the sequence does not stop.** Under a score that keeps
the shape and a clause its output always meets, a run of every height
exists once the DAG is good far enough up.

This is the one place a score is asked for something, and the two clauses
are what a designer supplies: `Score.Keeps` — reassign leaders, leave the
widths and the interval where they were — and a property `Q` the score
preserves whose configurations are live. For the reassignment family AL16
names, `Q` is "the heads are a permutation of the base rotation" and the
liveness supply is `Barnacle.headsRun_perm`. -/
theorem score_live (hR : Properties.Agree RL.toBaseRule.toDagRule)
    (score : Score RL.toBaseRule) (hkeep : score.Keeps)
    (Q : Config Validator → Prop)
    (hQ : ∀ (U : RL.Universe) (V : RL.View U) (v : ℕ → Option BlockId)
      (C : Config Validator), Q C → Q (score U V v C))
    (C₀ : Config Validator) (c : ℕ) :
    Progress.ConfigProgress RL P (rule score) C₀ c ∧
      Progress.EveryHeight RL P (rule score) C₀ Q c :=
  Progress.holds _ _ _ RL hR P (rule score) (Score.rule_bounded P score hkeep) C₀ Q
    (Score.rule_keeps score Q hQ) c

end Liveness

end Adaptive

end LeanDag
