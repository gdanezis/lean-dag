import LeanDag.Node.Helpers.SyncSteps
import LeanDag.Node.Helpers.Converge
/-!
# The syncs and the evidence along a trace

Before every event a node's syncs keep their shape (`syncsOn_before`), and
what it holds as evidence is evidence (`evidenceOn_before`).
-/

namespace LeanDag

namespace Node

namespace Converge

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

/-- **A node's syncs keep their shape** before every event. -/
theorem syncsOn_before (v : Validator) : ∀ i, SyncsOn (stateBefore cfg tr i v)
  | 0 => by
    have h : (stateBefore cfg tr 0 v).syncs = [] := by
      simp [stateBefore, inputsBefore, run, State.init]
    exact ⟨by rw [h]; exact List.nodup_nil,
      fun e he => by rw [h] at he; exact absurd he List.not_mem_nil⟩
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [step_before hi]
      exact (syncsOn_before v i).step inp
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact syncsOn_before v i

/-- **Only evidence convicts an author**, before every event. -/
theorem evidenceOn_before (v : Validator) : ∀ i, EvidenceOn (cfg.at v) (stateBefore cfg tr i v)
  | 0 => ⟨fun a ha => by simp [stateBefore, inputsBefore, run, State.init] at ha,
      fun e he => by simp [stateBefore, inputsBefore, run, State.init] at he⟩
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [step_before hi]
      exact EvidenceOn.step (cfg := cfg.at v) (syncsOn_before v i) (evidenceOn_before v i) inp
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact evidenceOn_before v i

/-- **An honest node holds the evidence of its disk** before every event,
under a faithful payload source. -/
theorem kept_before (hf : cfg.Faithful) (v : Validator) :
    ∀ i, Kept (cfg.at v) (stateBefore cfg tr i v)
  | 0 => fun c hc => absurd hc (Finset.notMem_empty c)
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [step_before hi]
      exact Kept.step (cfg := cfg.at v) hf (syncsOn_before v i) (kept_before hf v i) inp
    · rw [same_before fun inp h => he ⟨inp, h⟩]; exact kept_before hf v i

end Converge

end Node

end LeanDag
