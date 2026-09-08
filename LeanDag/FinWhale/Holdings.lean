import LeanDag.FinWhale.Procedure.Pass
import LeanDag.FinWhale.Model.Liveness
import LeanDag.Mysticeti.ViewPace
/-!
# FinWhale — a validator's holdings are its view

This file ties the schedule-free `View.lean` and liveness results to the
pacing trunk. `PaceCore.holds` — a validator's holdings at a time — is a
view at every instant, since its store clauses are exactly what `IsView`
asks; `PaceCore.holds_roundBlocks` then gives an instant at which the
view holds every reliable block from the coverage round up, which is
what `all_decided_of_view` reads.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D : Dag Validator BlockId Payload} {S : Slots Validator}
variable {Elig : ℕ → ℕ → Prop} [DecidableRel Elig]
variable {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {M : ℕ}

/-- **A validator's holdings are a view.** `holds_sub` is the subset
clause and `holds_closed` the closure clause. -/
def holdsView (pc : PaceCore U T M) (hids : D.ids = U.ids) (hblk : D.block = U.block)
    {v : Validator} (hv : v ∈ T) (t : ℕ) : D.View :=
  ⟨pc.holds v t, by rw [hids]; exact pc.holds_sub v t,
    by rw [hblk, hids] at *; exact pc.holds_closed v hv t⟩

@[simp] theorem holdsView_ids (pc : PaceCore U T M) (hids : D.ids = U.ids)
    (hblk : D.block = U.block) {v : Validator} (hv : v ∈ T) (t : ℕ) :
    (holdsView (D := D) pc hids hblk hv t).ids = pc.holds v t := rfl

/-- **And by then the view holds every reliable block from the coverage
round up.** Byzantine authors are not covered, and no schedule covers
them: nothing obliges a validator to receive what a faulty validator
never sent. -/
theorem held_of_pace (pc : PaceCore U T M) (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hle : ∀ u ∈ T, ∀ n ≤ pc.top u, n ≤ pc.built u n)
    (hcard : quorumCard Validator ≤ T.card) {R : ℕ} (hgst : pc.gst ≤ R)
    {v : Validator} (hv : v ∈ T) :
    ∀ n, R ≤ n → n ≤ M → ∀ b ∈ blocksAt D n, (D.block b).creator ∈ T →
      b ∈ pc.holds v (settled pc) := by
  intro n hR hM b hb hbT
  simp only [blocksAt, Finset.mem_filter, hids, hblk] at hb hbT ⊢
  have hg : ∀ u ∈ T, pc.gst ≤ pc.built u n :=
    fun u hu => le_trans (le_trans hgst hR) (hle u hu n (pc.reached hcard n hM u hu))
  have harrive := pc.holds_roundBlocks hM hg v hv b hb.1 hbT hb.2
  refine pc.holds_mono v _ _ ?_ harrive
  exact Finset.le_sup (f := fun m => pc.latest m + pc.delay) (Finset.mem_range.2 (by omega))

/-! ## The capstone: a validator, with nothing about it assumed -/

variable [LinearOrder BlockId]

end FinWhale

end LeanDag
