import LeanDag.Integration.Exposure
import LeanDag.DoS.Novelty
/-!
# I15 — the delivery layer, and the storage budgets under the fill

Report §8.4's budgets range over a `Delivery U`, not over `U`, so they
cannot be stated for the fill until it has a delivery structure of its
own. The transformer changes nothing at all — the filled blocks are a
retroactive reconstruction nobody received at the time, so `held` and
`accepted` retarget unchanged. The one obligation with content is
`includes`: a filled block must reference what `v1` accepted at the
round below, so the transformer needs `v1` to have accepted nothing
while down, `hdown`, the acceptance-side counterpart of `hgap`. With
that in place the budgets transfer with no arithmetic, since an old
block's cone is unchanged.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **I15a — the delivery transformer.** The fill's delivery structure
is the original's: the recovering validator's blocks were never
delivered to anyone, being reconstructed after the fact. `hdown` is the
hypothesis `Delivery.includes` forces. -/
def skipFillD (sk : SkipMsg U) (D : Delivery U)
    (hdown : ∀ m, sk.r0 ≤ m → m < sk.r → D.accepted sk.v1 m = ∅) :
    Delivery sk.skipFill where
  held := D.held
  held_spec := by
    intro v n i hi
    obtain ⟨h1, h2⟩ := D.held_spec v n i hi
    exact ⟨sk.ids_subset_skipFill h1, by rw [sk.skipFill_block_old h1]; exact h2⟩
  accepted := D.accepted
  accepted_sub := D.accepted_sub
  accepted_inj := by
    intro v n i hi j hj hij
    have hio := (D.held_spec v n i (D.accepted_sub v n hi)).1
    have hjo := (D.held_spec v n j (D.accepted_sub v n hj)).1
    rw [sk.skipFill_block_old hio, sk.skipFill_block_old hjo] at hij
    exact D.accepted_inj v n i hi j hj hij
  accepts_correct := by
    intro v hv n a ha hac
    have hao := (D.held_spec v n a ha).1
    rw [sk.skipFill_block_old hao] at hac
    exact D.accepts_correct v hv n a ha hac
  includes := by
    intro v hv n b hb hbc hbr
    rcases Finset.mem_union.mp hb with ho | hf
    · -- an old block references what it accepted, as before
      rw [sk.skipFill_block_old ho] at hbc hbr ⊢
      exact D.includes v hv n b ho hbc hbr
    · -- a filled block: the recovering validator accepted nothing
      obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [sk.skipFill_block_fresh] at hbc hbr
      simp only [SkipData.fillBlock] at hbc hbr
      subst hbc
      rw [hdown n (by omega) (by omega)]
      exact Finset.empty_subset _

variable (sk : SkipMsg U) (D : Delivery U)
variable {hdown : ∀ m, sk.r0 ≤ m → m < sk.r → D.accepted sk.v1 m = ∅}

/-- Accepted blocks are old, so their cones are unchanged and the
accumulated view is literally the same finite set. -/
theorem viewUpto_skipFillD (v : Validator) :
    ∀ n, viewUpto (skipFillD sk D hdown) v n = viewUpto D v n := by
  intro n
  induction n with
  | zero =>
      show (D.accepted v 0).biUnion (history sk.skipFill)
        = (D.accepted v 0).biUnion (history U)
      refine Finset.biUnion_congr rfl (fun b hb => ?_)
      exact history_skipFill_old sk (D.held_spec v 0 b (D.accepted_sub v 0 hb)).1
  | succ n ih =>
      show viewUpto (skipFillD sk D hdown) v n
          ∪ (D.accepted v (n + 1)).biUnion (history sk.skipFill)
        = viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
      rw [ih]
      refine congrArg _ (Finset.biUnion_congr rfl (fun b hb => ?_))
      exact history_skipFill_old sk
        (D.held_spec v (n + 1) b (D.accepted_sub v (n + 1) hb)).1

/-- **I15b — the budget transfers.** Novelty is measured over the cone
of an accepted block against the accumulated view, both unchanged, so
the author-blind budget holds at the same constant. -/
theorem uniformBudget_skipFillD {T : ℕ} (hu : UniformBudget D T) :
    UniformBudget (skipFillD sk D hdown) T := by
  intro v hv n b hb
  have hbo : b ∈ U.ids :=
    (D.held_spec v (n + 1) b (D.accepted_sub v (n + 1) hb)).1
  have : novelty sk.skipFill (viewUpto (skipFillD sk D hdown) v n) b
      = novelty U (viewUpto D v n) b := by
    unfold novelty
    rw [viewUpto_skipFillD sk D v n, history_skipFill_old sk hbo]
  rw [this]
  exact hu v hv n b hb

/-- **I15c — the reference discipline does not transfer, and the
failure is the mechanism's own.** `RefsAccepted` says a correct
validator references only what it accepted; a filled block references
the donor's blocks, which `v1` did not accept while down. An
alternative model, acceptance at recovery time, would satisfy both at
the cost of the budget becoming a property of the fill to check rather
than inherit; which model is right is a specification question, left
open here. -/
theorem not_refsAccepted_skipFillD (hne : sk.r0 < sk.r)
    (hv1 : sk.v1 ∈ (Correct : Finset Validator)) :
    ¬ RefsAccepted (skipFillD sk D hdown) := by
  intro hra
  have hR0 : sk.r0 = (U.block sk.B1).round := rfl
  have hmem : sk.fresh (sk.r0 + 1) ∈ sk.skipFill.ids :=
    Finset.mem_union_right _
      (sk.mem_freshIds.mpr ⟨sk.r0 + 1, by omega, by omega, rfl⟩)
  have hsub := hra sk.v1 hv1 sk.r0 (sk.fresh (sk.r0 + 1)) hmem
    (by rw [sk.skipFill_block_fresh]; rfl)
    (by rw [sk.skipFill_block_fresh]; rfl)
  -- the anchor is cited by the fill, and was accepted by nobody in the gap
  have hB1mem : sk.B1 ∈ (sk.skipFill.block (sk.fresh (sk.r0 + 1))).refs := by
    rw [sk.skipFill_block_fresh]
    simp only [SkipData.fillBlock, SkipData.prev]
    exact Finset.mem_insert_self _ _
  have hin : sk.B1 ∈ D.accepted sk.v1 sk.r0 := hsub hB1mem
  rw [hdown sk.r0 (le_refl _) hne] at hin
  exact absurd hin (Finset.notMem_empty _)

end Integration

end LeanDag
