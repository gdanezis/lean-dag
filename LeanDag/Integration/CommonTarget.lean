import LeanDag.Integration.Margin
import LeanDag.Common.CommonCore
/-!
# I19 — Safe Skip against a common-core target

Report §16.8 leaves open which reference discipline the fill's target
should follow; the worry is availability, that a validator cites blocks
it does not hold. Choosing the target from the common core removes it
at the source: T3c (report §5.2) produces, at every round, a
correct-authored block every block two rounds later reaches
(`exists_common_correct_ancestor`), so a validator holding any recent
block already has it and everything below it. A fill built from such
blocks transmits nothing — every recipient reconstructs it from its own
DAG — and needs no synchrony or progress hypothesis, holding of every
universe.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- A block is **common at round `r`** when every block two rounds
above it reaches it. -/
def CommonAt (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) (r : ℕ) : Prop :=
  b ∈ U.ids ∧ (U.block b).round = r ∧
    ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c b

/-- **Common blocks exist at every round**, and are correct-authored —
T3c restated in the vocabulary above. -/
theorem exists_commonAt {r : ℕ} {c₀ : BlockId} (hc₀ : c₀ ∈ U.ids)
    (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b, CommonAt U b r ∧ (U.block b).creator ∈ (Correct : Finset Validator) := by
  obtain ⟨bw, hbw, hbwr, hbwc, hbws⟩ := exists_common_correct_ancestor hc₀ hc₀r
  exact ⟨bw, ⟨hbw, hbwr, hbws⟩, hbwc⟩

/-- **Everyone holds a common block.** Any validator with a block two
rounds above has it in its own causal past. -/
theorem mem_history_of_commonAt {b c : BlockId} {r : ℕ}
    (hcom : CommonAt U b r) (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    b ∈ history U c :=
  (mem_history_iff hc).mpr (hcom.2.2 c hc hcr)

/-- **And everything it cites.** Cones nest, so a common block's
references, the blocks a fill would copy, are in every later
validator's past too. -/
theorem refs_mem_history_of_commonAt {b c : BlockId} {r : ℕ}
    (hcom : CommonAt U b r) (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2)
    {i : BlockId} (hi : i ∈ (U.block b).refs) :
    i ∈ history U c :=
  (mem_history_iff hc).mpr
    ((hcom.2.2 c hc hcr).tail hi)

/-- **I19 — a fill against a common donor line transmits nothing.**
Every reference the fill copies at a gap round lies in the causal past
of every validator holding a block two rounds above it, so naming the
target suffices. -/
theorem fill_refs_available (sk : SkipMsg U)
    (hcom : ∀ k, sk.r0 < k → k ≤ sk.r → CommonAt U (sk.line k) k)
    {k : ℕ} (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = k + 2)
    {i : BlockId} (hi : i ∈ (U.block (sk.line k)).refs) :
    i ∈ history U c :=
  refs_mem_history_of_commonAt (hcom k hk1 hk2) hc hcr hi

/-- The filled block's own references, split: the copied ones are
universally held (`fill_refs_available`), and the remaining one is the
self reference, which is the recovering validator's own block. -/
theorem fill_refs_eq (sk : SkipMsg U) {k : ℕ} :
    (sk.skipFill.block (sk.fresh k)).refs
      = insert (sk.prev k) (U.block (sk.line k)).refs := by
  rw [sk.skipFill_block_fresh]
  rfl

end Integration

end LeanDag
