import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Model.Run
import LeanDag.Barnacle.Helpers.Schedule
/-!
# Agreement helpers

Not part of the audit surface. The induction behind BN3: configuration
data agreeing at `k` forces the anchors of `k` to agree — the lesser of
two anchors would be a committed slot past the threshold below the
other, against `anchor_least` — and with them the next configuration.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {getLeader : ℕ → Validator} {hk : Keyed getLeader P.maxLeaders}
variable {upd : UpdateRule R} {U : R.Universe} {V₁ V₂ : R.View U} {K₁ K₂ : ℕ}

/-- Configuration `k` agrees between two runs. -/
def ConfigAgree (R₁ : PartialRun R P getLeader hk upd U V₁ K₁)
    (R₂ : PartialRun R P getLeader hk upd U V₂ K₂) (k : ℕ) : Prop :=
  R₁.start k = R₂.start k ∧ R₁.count k = R₂.count k ∧ R₁.backoff k = R₂.backoff k

/-- Verdicts of a slot both runs have closed agree — the base rule's
agreement law, once the two schedules are seen to be one. -/
theorem vdct_agree (hR : Properties.Agree R.toDagRule) (R₁ : PartialRun R P getLeader hk upd U V₁ K₁)
    (R₂ : PartialRun R P getLeader hk upd U V₂ K₂) {k : ℕ} (hc : R₁.count k = R₂.count k)
    (hk₁ : k < K₁) (hk₂ : k < K₂) {κ : ℕ}
    (h₁ : R₁.start k < κ / R₁.count k) (h₁' : κ / R₁.count k ≤ R₁.start (k + 1))
    (h₂ : R₂.start k < κ / R₂.count k) (h₂' : κ / R₂.count k ≤ R₂.start (k + 1)) :
    R₁.vdct k κ = R₂.vdct k κ := by
  have d₁ := R₁.closed k hk₁ κ h₁ h₁'
  have d₂ := R₂.closed k hk₂ κ h₂ h₂'
  rw [Sched_congr getLeader hk hc (R₁.count_pos k) (R₁.count_le k)
    (R₂.count_pos k) (R₂.count_le k)] at d₁
  exact hR _ _ _ κ _ _ d₁ d₂

/-- The anchors agree: the lesser of two anchors is, in the other run, a
committed slot past the threshold below its anchor. -/
theorem anchor_agree (hR : Properties.Agree R.toDagRule) (R₁ : PartialRun R P getLeader hk upd U V₁ K₁)
    (R₂ : PartialRun R P getLeader hk upd U V₂ K₂) {k : ℕ} (h : ConfigAgree R₁ R₂ k)
    (hk₁ : k < K₁) (hk₂ : k < K₂) : R₁.anchor k = R₂.anchor k := by
  obtain ⟨hs, hc, _⟩ := h
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨⟨A, hA⟩, hround⟩ := R₁.anchor_commits k hk₁
    have hr₂ : R₂.start k + P.interval < R₁.anchor k / R₂.count k := by
      rw [← hs, ← hc]; exact hround
    have hnone := R₂.anchor_least k hk₂ (R₁.anchor k) hlt hr₂
    have hv := vdct_agree hR R₁ R₂ hc hk₁ hk₂ (κ := R₁.anchor k) (by omega)
      (by rw [R₁.start_succ k hk₁]; omega)
      (by omega)
      (by rw [R₂.start_succ k hk₂]
          have hd : R₁.anchor k / R₂.count k ≤ R₂.anchor k / R₂.count k :=
            Nat.div_le_div_right hlt.le
          omega)
    rw [hA, hnone] at hv
    exact Option.some_ne_none A hv
  · obtain ⟨⟨A, hA⟩, hround⟩ := R₂.anchor_commits k hk₂
    have hr₁ : R₁.start k + P.interval < R₂.anchor k / R₁.count k := by
      rw [hs, hc]; exact hround
    have hnone := R₁.anchor_least k hk₁ (R₂.anchor k) hgt hr₁
    have hv := vdct_agree hR R₁ R₂ hc hk₁ hk₂ (κ := R₂.anchor k) (by omega)
      (by rw [R₁.start_succ k hk₁]
          have hd : R₂.anchor k / R₁.count k ≤ R₁.anchor k / R₁.count k :=
            Nat.div_le_div_right hgt.le
          omega)
      (by omega) (by rw [R₂.start_succ k hk₂]; omega)
    rw [hA, hnone] at hv
    exact Option.some_ne_none A hv.symm

/-- Agreement at `k` carries to `k + 1`: the anchors agree, so the anchor
blocks agree, so one update of one state yields one configuration. -/
theorem configAgree_succ (hR : Properties.Agree R.toDagRule) (hanc : Anchored R upd)
    (R₁ : PartialRun R P getLeader hk upd U V₁ K₁)
    (R₂ : PartialRun R P getLeader hk upd U V₂ K₂) {k : ℕ} (h : ConfigAgree R₁ R₂ k)
    (hk₁ : k < K₁) (hk₂ : k < K₂) : ConfigAgree R₁ R₂ (k + 1) := by
  have ha := anchor_agree hR R₁ R₂ h hk₁ hk₂
  obtain ⟨hs, hc, hb⟩ := h
  obtain ⟨⟨A, hA⟩, hround⟩ := R₁.anchor_commits k hk₁
  have hA₂ : R₂.vdct k (R₂.anchor k) = some A := by
    rw [← ha, ← vdct_agree hR R₁ R₂ hc hk₁ hk₂ (κ := R₁.anchor k) (by omega)
      (by rw [R₁.start_succ k hk₁]; omega)
      (by rw [← hs, ← hc]; omega) (by rw [R₂.start_succ k hk₂, ← ha, ← hc]; omega)]
    exact hA
  have e₁ := R₁.update k hk₁ A hA
  have e₂ := R₂.update k hk₂ A hA₂
  rw [hc, hb] at e₁
  have e := e₁.trans ((hanc U V₁ V₂ (R₂.count k) (R₂.backoff k) A).trans e₂.symm)
  refine ⟨?_, (Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
  rw [R₁.start_succ k hk₁, R₂.start_succ k hk₂, ha, hc]

/-- **Configurations agree** up to the lower height, by induction. -/
theorem configAgree (hR : Properties.Agree R.toDagRule) (hanc : Anchored R upd)
    (R₁ : PartialRun R P getLeader hk upd U V₁ K₁)
    (R₂ : PartialRun R P getLeader hk upd U V₂ K₂) :
    ∀ k, k ≤ min K₁ K₂ → ConfigAgree R₁ R₂ k
  | 0, _ => ⟨by rw [R₁.init.1, R₂.init.1], by rw [R₁.init.2.1, R₂.init.2.1],
      by rw [R₁.init.2.2, R₂.init.2.2]⟩
  | k + 1, h => configAgree_succ hR hanc R₁ R₂ (configAgree hR hanc R₁ R₂ k (by omega))
      (by omega) (by omega)

end Barnacle

end LeanDag
