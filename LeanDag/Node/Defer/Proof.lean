import LeanDag.Node.Defer.Statement
import LeanDag.Node.Helpers.Agree
/-!
# Rate limiting does not make a node decide wrongly — proof

The record is the run's (`globalRecord`), whose identifiers are known
ones (`mem_globalIds`). By induction over the trace every honest store
is a cut of it and every decision a verdict on a view of it
(`cut_before`), at every configuration; at a covered row the decider
meets its laws (`coveredLaws`), so a verdict on a view is a verdict on
every larger view (`AnchoredRule.decided_mono`).
-/

namespace LeanDag

namespace Node

namespace Defer

theorem decides : Decides := by
  intro Validator BlockId Payload _ _ _ cfg H tr hσ hadm hf htime hoff hcert hinj
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2.1, hadm.1⟩
  have key := cut_before hσ hadm hf htime hoff hcert hinj tr.length
  refine ⟨globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime),
    fun j hj => ?_, fun v hv => (key v hv).1, fun v hv e he => ?_⟩
  · obtain ⟨x, ⟨v, hv, hx⟩, rfl⟩ := exists_of_mem_knownIds (mem_globalIds.mp hj).1
    exact ⟨v, hv, x, hx, rfl⟩
  · obtain ⟨V, hd⟩ := (key v hv).2 e he
    letI := cfg.slots
    obtain ⟨-, -, -, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
      (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
    exact ⟨V, fun V' hsub => AnchoredRule.decided_mono hlaws trivial hsub hd⟩

theorem holds : Statement := decides

end Defer

end Node

end LeanDag
