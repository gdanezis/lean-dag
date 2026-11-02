import LeanDag.Node.Helpers.Global
import LeanDag.Common.Record.Chop
/-!
# The run's record, cut at a round

`docs/dos-bounds.md` §5, Phase 3.2. A node under bypass may hold a block at
or below its cut whose bypassed reference no honest node knew, so the run's
record of blocks real all the way down (`globalRecord`) need not hold it. A
decision of slot `k` reads only the record cut at `slotRound k − 1`. A block
is *real down to `G`* when it lies at or below `G`, or its references are
known and real down to `G` and it is valid at the quorum (`RealDown`). The
known blocks at or above `G` that are real down to `G`, cut there as
`BlockRecord.chop` cuts, form a block record (`globalCut`).

* **Real down to a round is real down to every higher one** (`RealDown.mono`),
  and a real block is real down to every round (`RealDown.of_real`).
* **The cut of the run's record lies in it** (`mem_globalCut_of_chop`), with
  the same blocks.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (cfg : Config Validator BlockId Payload) (H : Finset Validator)
variable (tr : Trace Validator BlockId Payload)

/-- **A block real down to `G`**: at or below `G`, or with known references
real down to `G` and valid at the quorum. -/
inductive RealDown (G : ℕ) : BlockId → Prop
  | base {j : BlockId} : (content cfg H tr j).round ≤ G → RealDown G j
  | intro {j : BlockId} : G < (content cfg H tr j).round →
      (content cfg H tr j).refs ⊆ knownIds cfg H tr →
      ValidAt cfg.q Clause.none (content cfg H tr) (content cfg H tr j) →
      (∀ x ∈ (content cfg H tr j).refs, RealDown G x) → RealDown G j

open Classical in
/-- The known blocks at or above `G` that are real down to `G`. -/
noncomputable def globalCutIds (G : ℕ) : Finset BlockId :=
  (knownIds cfg H tr).filter fun j => G ≤ (content cfg H tr j).round ∧ RealDown cfg H tr G j

variable {cfg H tr}

open Classical in
theorem mem_globalCutIds {G : ℕ} {j : BlockId} :
    j ∈ globalCutIds cfg H tr G ↔
      j ∈ knownIds cfg H tr ∧ G ≤ (content cfg H tr j).round ∧ RealDown cfg H tr G j := by
  unfold globalCutIds
  exact Finset.mem_filter

/-- **Real down to a round is real down to every higher one.** -/
theorem RealDown.mono {G G' : ℕ} (hG : G ≤ G') {j : BlockId} (h : RealDown cfg H tr G j) :
    RealDown cfg H tr G' j := by
  induction h with
  | base hr => exact .base (by omega)
  | @intro j hr hs hv _ ih =>
    by_cases hj : (content cfg H tr j).round ≤ G'
    · exact .base hj
    · exact .intro (by omega) hs hv ih

/-- **A real block is real down to every round.** -/
theorem RealDown.of_real (G : ℕ) {j : BlockId} (h : Real cfg H tr j) : RealDown cfg H tr G j := by
  induction h with
  | @intro j hs hv _ ih =>
    by_cases hj : (content cfg H tr j).round ≤ G
    · exact .base hj
    · exact .intro (by omega) hs hv ih

variable (hinj : HashInjective cfg H tr) (hauth : Authentic cfg H tr)

include hinj hauth in
/-- **The run's record, cut at `G`.** -/
noncomputable def globalCut (G : ℕ) :
    BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H where
  ids := globalCutIds cfg H tr G
  block := chopBlk (content cfg H tr) G
  complete := by
    intro i hi x hx
    obtain ⟨-, hiG, hreal⟩ := mem_globalCutIds.mp hi
    rcases Nat.lt_or_ge G (content cfg H tr i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hx
      cases hreal with
      | base hr => omega
      | intro _ hs hv hr =>
        have hxr := Validity.Mechanised.pred _ _ hv x hx
        exact mem_globalCutIds.mpr ⟨hs hx, by omega, hr x hx⟩
    · rw [chopBlk_refs_of_le h] at hx
      exact absurd hx (Finset.notMem_empty x)
  valid := by
    intro i hi
    obtain ⟨-, hiG, hreal⟩ := mem_globalCutIds.mp hi
    rcases Nat.lt_or_ge G (content cfg H tr i).round with h | h
    · rw [chopBlk_of_lt h]
      cases hreal with
      | base hr => omega
      | intro _ _ hv _ => exact Validity.Mechanised.chops _ G _ hv h
    · apply Validity.Mechanised.base
      · rw [chopBlk_round]; omega
      · exact chopBlk_refs_of_le h
  no_equivocation := by
    intro i hi j hj hc hcr hr
    obtain ⟨hik, hiG, -⟩ := mem_globalCutIds.mp hi
    obtain ⟨hjk, hjG, -⟩ := mem_globalCutIds.mp hj
    simp only [chopBlk_creator, chopBlk_round] at hc hcr hr
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_knownIds hik
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_knownIds hjk
    simp only [content_of_known hinj hx, content_of_known hinj hy] at hc hcr hr hiG hjG
    have hbx := mem_persists_of_known hinj hauth hx hc
    have hby := mem_persists_of_known hinj hauth hy (hcr ▸ hc)
    rw [hcr] at hbx
    exact congrArg Prod.fst (eq_of_persists _ hbx hby (by omega))

@[simp] theorem globalCut_ids (G : ℕ) : (globalCut hinj hauth G).ids = globalCutIds cfg H tr G :=
  rfl

@[simp] theorem globalCut_block (G : ℕ) :
    (globalCut hinj hauth G).block = chopBlk (content cfg H tr) G := rfl

/-- **The cut of the run's record lies in the record cut at `G`**, with the
same blocks. -/
theorem mem_globalCut_of_chop {G : ℕ} {i : BlockId}
    (hi : i ∈ ((globalRecord hinj hauth).chop G).ids) : i ∈ (globalCut hinj hauth G).ids := by
  obtain ⟨hiU, hiG⟩ := BlockRecord.mem_chop_ids.mp hi
  obtain ⟨hk, hreal⟩ := mem_globalIds.mp hiU
  exact mem_globalCutIds.mpr ⟨hk, hiG, RealDown.of_real G hreal⟩

theorem chop_block_eq (G : ℕ) :
    ((globalRecord hinj hauth).chop G).block = (globalCut hinj hauth G).block := rfl

end Node

end LeanDag
