import LeanDag.Node.Cut.Statement
import LeanDag.Node.Helpers.CutVerdict
import LeanDag.Node.Helpers.Run
/-!
# The run's record, one for each cut — proof

The record of the cut at `G` is the run's record padded below `G`
(`padded`): fresh identifiers exist, since the identifiers are injective on
blocks. An honest disk is a cut of the run's record (`cut_before`), so its
blocks are real, and real down to `G`. An honest node's decisions are one run
of the loop on a view of the run's record (`commitInv_before`); that view,
padded below `G`, agrees with it from the round of each slot whose cut is `G`
(`viewsAbove_padded`), so each decision is a verdict there
(`ViewsAbove.decided_of_mem`). Verdicts on one record agree
(`AnchoredRule.decided_agree`).
-/

namespace LeanDag

namespace Node

namespace Cut

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

omit [Fintype Validator] in
/-- Injective identifiers leave infinitely many. -/
theorem infinite_of_idOf {cfg : Config Validator BlockId Payload}
    (hid : Function.Injective cfg.idOf) : Infinite BlockId := by
  haveI : Infinite (Block Validator BlockId Payload) :=
    Infinite.of_injective (fun n : ℕ =>
      ({ round := n, creator := cfg.me, refs := ∅, payload := cfg.genesis.payload } :
        Block Validator BlockId Payload))
      fun a b h => congrArg Block.round h
  exact Infinite.of_injective cfg.idOf hid

theorem cuts : Cuts := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hinj hid G
  haveI := infinite_of_idOf hid
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  have hq : cfg.q ≤ Fintype.card Validator := hadm.2.2.2.2
  refine ⟨padded hinjR hauthR hq G, ?_, ?_⟩
  · intro v hv i j hj hjG
    obtain ⟨hjU, hjb⟩ := (cut_before hσ hadm hf htime hinj i v hv).1 j hj
    obtain ⟨hk, hreal⟩ := mem_globalIds.mp hjU
    change content cfg H tr j = _ at hjb
    rw [← hjb] at hjG ⊢
    exact ⟨mem_paddedIds.mpr (Or.inl (mem_globalCutIds.mpr ⟨hk, hjG, RealDown.of_real G hreal⟩)),
      (padBlk_known_fields hk).1, (padBlk_known_fields hk).2.1, fun hlt => padBlk_of_lt hk hlt⟩
  · intro v hv i e he hG
    rcases commitInv_before hσ hadm hf htime hinj hv i with h0 | ⟨V, N, -, heq⟩
    · rw [h0] at he
      exact absurd he List.not_mem_nil
    · rw [heq] at he
      letI := cfg.slots
      haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
          (Payload := Payload) cfg.q Clause.none) cfg.q :=
        Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
      have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
      have hw : 2 ≤ cfg.p.waveLength := by
        rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
      obtain ⟨hl, -, hcv, -⟩ := Scheme.coveredLaws (boundedSel
        (P := ValidAt cfg.q Clause.none) (honest := H) (Validator := Validator)
        (BlockId := BlockId) (Payload := Payload)) ht
      have hva := viewsAbove_padded hinjR hauthR hq V (G := G) (R := cfg.slots.slotRound e.1)
        (by omega)
      exact ⟨_, hva.decided_of_mem cfg.p hw hl hcv (lo := 0) (Nat.zero_le _) le_rfl he⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hinj hid v hv w hw i j e he
    e' he' hk
  obtain ⟨U, -, hL⟩ := cuts Validator BlockId Payload cfg H tr hσ hadm hf htime hinj hid
    (cfg.slots.slotRound e.1 - 1)
  obtain ⟨V₁, d₁⟩ := hL v hv i e he rfl
  obtain ⟨V₂, d₂⟩ := hL w hw j e' he' (by rw [hk])
  letI := cfg.slots
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel
    (P := ValidAt cfg.q Clause.none) (honest := H) (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) ht
  rw [← hk] at d₂
  exact AnchoredRule.decided_agree hlaws trivial d₁ d₂

/-- The run's record, one for each cut. -/
theorem statement : Statement := ⟨cuts, agrees⟩

end Cut

end Node

end LeanDag
