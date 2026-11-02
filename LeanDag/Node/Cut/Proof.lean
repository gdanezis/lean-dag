import LeanDag.Node.Cut.Statement
import LeanDag.Node.Helpers.CutAbove
/-!
# The run's record, one for each cut — proof

The record of the cut at `G` is the run's record padded below `G`
(`padded`): fresh identifiers exist, since the identifiers are injective on
blocks. Along the run every honest disk is read as that record reads it from
`G` up, and every decision of a slot from round `G` up is a verdict on it
(`cutAbove_before`); neither reads a block below `G`. Verdicts on one record
agree (`AnchoredRule.decided_agree`).
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
  refine ⟨padded hinjR hauthR hq G, fun v hv i j hj hjG => ?_, fun v hv i e he hG => ?_⟩
  · exact (cutAbove_before hinjR hauthR hq hσ hadm hf G i v hv).1 j hj hjG
  · exact (cutAbove_before hinjR hauthR hq hσ hadm hf G i v hv).2 e he (by omega)

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
