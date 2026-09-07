import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Properties.Optional.Skip
/-!
# Hydrozoan skips an unsupported slot, at `qFast` blamers

Not part of the audit surface. The discharge of
`Properties.SkipsUnsupported` for this protocol, and the grade it lands
at.

A blame is a voting-round block referencing no candidate of the slot. If
every `T`-authored block at the voting round supports no candidate, each
of them is a blame, so the blamers in view include all of `T`, and
Hydrozoan's direct skip fires as soon as `qFast ≤ |T|`. That is the
grade — and it is not one a correct quorum reaches unaided, since a
correct quorum has `q = n − f − c` members against `qFast = n − p`.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica] [S : LeanDag.Slots Replica]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- Every member of `T` slotBlames the slot. -/
theorem subset_blamesInView {V : LeanDag.Hydrozoan.View U} {T : Finset Replica} {k : ℕ}
    (hpres : ∀ v ∈ T, ∃ c ∈ V.ids, (U.block c).creator = v ∧
      (U.block c).round = S.slotRound k + 1)
    (huns : ∀ c ∈ V.ids, (U.block c).creator ∈ T → (U.block c).round = S.slotRound k + 1 →
      ∀ L, LeanDag.IsLeaderBlock U k L → L ∉ (U.block c).refs) :
    T ⊆ slotBlamesIn U V k := by
  intro v hv
  obtain ⟨c, hcV, hca, hcr⟩ := hpres v hv
  refine Finset.mem_image.mpr ⟨c, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hcV⟩, hca⟩
  · exact Finset.mem_filter.mpr ⟨V.subset_ids hcV, hcr⟩
  · intro j hj hL
    exact huns c hcV (by rw [hca]; exact hv) hcr j hL hj

/-- **The skip fires at `qFast` blamers.** -/
theorem decided_none_of_unsupported {V : LeanDag.Hydrozoan.View U} {T : Finset Replica} {k : ℕ}
    (hq : LeanDag.Hydrozoan.qFast Replica ≤ T.card)
    (hpres : ∀ v ∈ T, ∃ c ∈ V.ids, (U.block c).creator = v ∧
      (U.block c).round = S.slotRound k + 1)
    (huns : ∀ c ∈ V.ids, (U.block c).creator ∈ T → (U.block c).round = S.slotRound k + 1 →
      ∀ L, LeanDag.IsLeaderBlock U k L → L ∉ (U.block c).refs) :
    LeanDag.Hydrozoan.Decided U V k none :=
  LeanDag.Hydrozoan.Decided.directSkip
    (le_trans hq (Finset.card_le_card (subset_blamesInView hpres huns)))

omit S in
/-- **`SkipsUnsupported` at the carrier**, at the grade `qFast ≤ |T|`. -/
theorem skipsUnsupported :
    Properties.SkipsUnsupported (rule (Replica := Replica) (BlockId := BlockId))
      (fun T => LeanDag.Hydrozoan.qFast Replica ≤ T.card) := by
  intro S' U V T k hq hpres huns
  have hpres' : ∀ v ∈ T, ∃ c ∈ V.ids, (U.block c).creator = v ∧
      (U.block c).round = S'.slotRound k + 1 := fun v hv => by
    obtain ⟨c, hcV, hca, hcr⟩ := hpres v hv
    exact ⟨c, hcV, hca, hcr⟩
  have huns' : ∀ c ∈ V.ids, (U.block c).creator ∈ T → (U.block c).round = S'.slotRound k + 1 →
      ∀ L, @LeanDag.IsLeaderBlock _ _ _ _ _ S' U k L →
        L ∉ (U.block c).refs :=
    fun c hcV hT hr L hL => huns c hcV hT hr L hL
  exact decided_none_of_unsupported (S := S') hq hpres' huns'

end Hydrozoan

end LeanDag
