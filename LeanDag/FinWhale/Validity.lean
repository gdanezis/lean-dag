import LeanDag.FinWhale.Procedure.Decided
import LeanDag.FinWhale.Rotation
import LeanDag.FinWhale.Model.Schedule
/-!
# FinWhale — Validity, on any schedule

Theorem 26 needs every correct block to reach the causal history of some
later correct leader block. Coverage would give that in one round, but
coverage belongs to the full-timeout discipline and a reactive builder
has none. `SelfParented` — every block references its author's previous
block, taken as a hypothesis rather than added to `ValidHere` — gives it
instead: a correct validator's blocks form a chain, and round robin
makes that validator a leader once a cycle.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {Elig : ℕ → ℕ → Prop}
variable {D : Dag Validator BlockId Payload} {S : Slots Validator}

/-- **A correct validator's blocks form a chain.** Each of its blocks
reaches all its earlier ones: the self-parent edge steps down one round,
and one block per correct validator per round makes the step unique. -/
theorem reaches_own (hself : SelfParented D) :
    ∀ d : ℕ, ∀ b ∈ D.ids, ∀ c ∈ D.ids,
      (D.block b).creator ∈ (Correct : Finset Validator) →
      (D.block c).creator = (D.block b).creator →
      (D.block c).round = (D.block b).round + d → ReachesFrom D.block c b := by
  intro d
  induction d with
  | zero =>
    intro b hb c hc hbc hcc hcr
    have : c = b := D.no_equivocation c hc b hb (by rw [hcc]; exact hbc) hcc (by omega)
    rw [this]
  | succ d ih =>
    intro b hb c hc hbc hcc hcr
    obtain ⟨q, hq, hqc⟩ := hself c hc (by omega)
    have hqids : q ∈ D.ids := D.complete c hc q hq
    have hqr : (D.block q).round = (D.block b).round + d := by
      have := parent_round hc hq; omega
    exact ReachesFrom.of_mem_refs hq (ih b hb q hqids hbc (by rw [hqc, hcc]) hqr)

/-- **And so a correct validator's block lies in the causal history of
every later block of its own.** -/
theorem reaches_of_same_creator (hself : SelfParented D) {b c : BlockId}
    (hb : b ∈ D.ids) (hc : c ∈ D.ids)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator))
    (hcc : (D.block c).creator = (D.block b).creator)
    (hle : (D.block b).round ≤ (D.block c).round) : ReachesFrom D.block c b :=
  reaches_own hself ((D.block c).round - (D.block b).round) b hb c hc hbc hcc (by omega)

end FinWhale

end LeanDag
