import LeanDag.Common.Anchored.ReadAlike
import LeanDag.Scheme.Model.Rule
import LeanDag.Common.History
/-!
# Where nobody equivocates, the vote is immaterial

A vote-selection rule picks one block of a slot from the voter's history.
When the slot's author has one block at that round, every rule picks it
(`sel_eq_of_noEquiv`), so on a record in which no validator equivocates
the decider reads alike at any two vote-selection rules
(`readAlike_noEquiv`).
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- **Two vote-selection rules select alike** at a block of a record in
which no validator equivocates. -/
theorem sel_eq_of_noEquiv (σ σ' : VoteSel Validator BlockId Payload P honest)
    (hU : U.NoEquivOn Finset.univ) {b : BlockId} (hb : b ∈ U.ids) (a : Validator) (r : ℕ) :
    σ.sel U b a r = σ'.sel U b a r := by
  have key : ∀ (σ₁ σ₂ : VoteSel Validator BlockId Payload P honest) (x : BlockId),
      σ₁.sel U b a r = some x → σ₂.sel U b a r = some x := by
    intro σ₁ σ₂ x hx
    obtain ⟨hxh, hxc, hxr⟩ := σ₁.sound U b a r x hx
    have hr : r < (U.block b).round := by
      by_contra hle
      rw [σ₁.below U b a r (by omega)] at hx
      exact absurd hx (by simp)
    cases h₂ : σ₂.sel U b a r with
    | none => exact absurd hxr (σ₂.complete U b a r hb hr h₂ x hxh hxc)
    | some y =>
      obtain ⟨hyh, hyc, hyr⟩ := σ₂.sound U b a r y h₂
      rw [hU y (history_subset_ids hb hyh) x (history_subset_ids hb hxh) (Finset.mem_univ _)
        (hyc.trans hxc.symm) (hyr.trans hxr.symm)]
  cases h : σ.sel U b a r with
  | none =>
    cases h' : σ'.sel U b a r with
    | none => rfl
    | some y => rw [key σ' σ y h'] at h; exact absurd h (by simp)
  | some x => exact (key σ σ' x h).symm

theorem certsAt_noEquiv (p : Params) (σ σ' : VoteSel Validator BlockId Payload P honest)
    (hU : U.NoEquivOn Finset.univ) (L : BlockId) (r : ℕ) :
    certsAt p σ U L r = certsAt p σ' U L r := by
  refine Finset.filter_congr fun C hC => ?_
  have hCU := (mem_blocksAt.mp hC).1
  have hc : carriedVotes U (σ.Votes U) C L = carriedVotes U (σ'.Votes U) C L :=
    Finset.filter_congr fun c hc => by
      unfold VoteSel.Votes; rw [sel_eq_of_noEquiv σ σ' hU (U.complete C hCU c hc)]
  unfold IsCert
  split
  · unfold VoteSel.Votes; rw [sel_eq_of_noEquiv σ σ' hU hCU]
  · unfold CarriesVotes; rw [hc]

theorem blamersAt_noEquiv [S : Slots Validator] (p : Params)
    (σ σ' : VoteSel Validator BlockId Payload P honest) (hU : U.NoEquivOn Finset.univ)
    (k : ℕ) : blamersAt p σ U k = blamersAt p σ' U k :=
  Finset.filter_congr fun b hb => by rw [sel_eq_of_noEquiv σ σ' hU (mem_blocksAt.mp hb).1]

/-- **The decider reads alike at any two vote-selection rules** on a record
in which no validator equivocates. -/
theorem readAlike_noEquiv [S : Slots Validator] (p : Params)
    (σ σ' : VoteSel Validator BlockId Payload P honest) (hU : U.NoEquivOn Finset.univ) :
    AnchoredRule.ReadAlike (schemeAnchored p σ) (schemeAnchored p σ') U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L _ => by
    show HoldsAtLeast U V _ (certsAt p σ U L _) ↔ HoldsAtLeast U V _ (certsAt p σ' U L _)
    rw [certsAt_noEquiv p σ σ' hU]
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt p σ U k) ↔ HoldsAtLeast U V _ (blamersAt p σ' U k)
    rw [blamersAt_noEquiv p σ σ' hU]
  link := fun _ _ _ _ => by
    show _ ≤ (creatorsOf U.block ((certsAt p σ U _ _).filter _)).card ↔
      _ ≤ (creatorsOf U.block ((certsAt p σ' U _ _).filter _)).card
    rw [certsAt_noEquiv p σ σ' hU]
  least := fun _ _ _ _ _ => by
    unfold AnchoredRule.Least
    refine forall_congr' fun L' => imp_congr_right fun _ => imp_congr_left ?_
    show _ ≤ (creatorsOf U.block ((certsAt p σ U _ _).filter _)).card ↔
      _ ≤ (creatorsOf U.block ((certsAt p σ' U _ _).filter _)).card
    rw [certsAt_noEquiv p σ σ' hU]

end Scheme

end LeanDag
