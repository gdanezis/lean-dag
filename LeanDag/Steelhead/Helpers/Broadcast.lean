import LeanDag.Steelhead.Broadcast.Statement
import LeanDag.Steelhead.Helpers.Decision
import LeanDag.MahiMahi.Helpers.Synchrony
/-!
# Helpers — atomic broadcast

Generated lemma infrastructure for `Broadcast/Statement.lean`; not part
of the audit surface. The one lemma here is the asynchronous half of
validity: with the reference rule the implementation runs, where a block
references every block its author holds that its own parent does not
already cover, a block the correct validators have referenced by some
round lies in the cone of every block above that round, whoever wrote
it, since a quorum of references meets the correct validators.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **SH17e.** Every block one round above a round at which the reliable validators have all
referenced `b` reaches `b`: its own references are a quorum of that round, which meets the
reliable set; `reaches_pred_of_round_le` then carries the base case to every higher round. -/
theorem reaches_of_eventualReference {T : Finset Validator} {ρ : ℕ} {b : BlockId}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (href : ∀ q ∈ U.ids, (U.block q).round = ρ → (U.block q).creator ∈ T → Reaches U q b)
    (hpop : PopulatedOn U T ρ) :
    ∀ c ∈ U.ids, ρ + 1 ≤ (U.block c).round → Reaches U c b := by
  have hbase : ∀ c ∈ U.ids, (U.block c).round = ρ + 1 → ∃ x, x = b ∧ Reaches U c x := by
    intro c hc hcr
    have hTq : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = ρ ∧ Reaches U q b ∧
        (U.block q).creator = v := by
      intro v hv
      obtain ⟨q, hq, hqc, hqr⟩ := hpop v hv
      exact ⟨q, hq, hqr, href q hq hqr (hqc ▸ hv), hqc⟩
    have hfcard : F.f + 1 ≤ T.card := by
      have := F.card_validators
      omega
    obtain ⟨q, hq, hqb⟩ := exists_mem_refs_of_honest_support_of_card
      (Q := fun q => Reaches U q b) hTq (fun v hv => hT hv) (lt_card_add_quorumCard hfcard) hc hcr
    exact ⟨b, rfl, Reaches.trans (Reaches.single hq) hqb⟩
  intro c hc hcr
  obtain ⟨x, rfl, h⟩ := reaches_pred_of_round_le (N := ρ + 1) hbase hc hcr
  exact h

end Steelhead

end LeanDag
