import LeanDag.FinWhale.Decided
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

/-- **Theorem 26 (Validity), on any schedule.** A correct validator's
block is delivered, once the rotation has named its author a leader above
it and that slot is committed.

Nothing here is a coverage assumption, so the reactive schedule carries
it as readily as the timed one: the block reaches the leader block
because the leader block is the *same validator's*, later. -/
theorem theorem26_of_selfParent (hself : SelfParented D)
    {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed Elig dc ds choose dec) {R N : ℕ}
    (hsees : SeesCommits S D dc R N)
    (hrr : RoundRobin S.leader) (hid : ∀ s, S.slotRound s = s) [LinearOrder BlockId]
    {b : BlockId} {k : ℕ} (hb : b ∈ D.ids)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator))
    (hbound : max ((D.block b).round) R + Fintype.card Validator + 2 ≤ N)
    (hk : max ((D.block b).round) R + Fintype.card Validator < k) :
    b ∈ linearise (histOf D) (commitSeq dec k) := by
  -- the rotation names the author a leader within the cycle above `b`
  obtain ⟨s, hlo, hhi, hlead⟩ :=
    exists_round_led_by hrr ((D.block b).creator) (max ((D.block b).round) R)
  obtain ⟨l, hslot, hdcl⟩ := hsees s (by rw [hid]; exact le_trans (le_max_right _ R) hlo)
    (by rw [hid]; omega) (by rw [hlead]; exact hbc)
  have hlu : l ∈ D.ids ∧ (D.block l).round = s ∧
      (D.block l).creator = S.leader s := by
    simp only [slotBlocks, leaderBlocksAt, blocksAt, Finset.mem_filter, hid] at hslot
    exact ⟨hslot.1.1, hslot.1.2, hslot.2⟩
  -- and the leader block is the author's own, later
  have hreach : ReachesFrom D.block l b :=
    reaches_of_same_creator hself hb hlu.1 hbc (by rw [hlu.2.2, hlead])
      (by have := le_max_left ((D.block b).round) R; omega)
  exact theorem26 (r := s) (l := l) (by omega)
    (hwf.direct_commit s l hdcl) (mem_histOf hlu.1 hreach)

end FinWhale

end LeanDag
