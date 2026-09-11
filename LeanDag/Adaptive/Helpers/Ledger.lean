import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Helpers.Ledger
import Mathlib.Data.List.Nodup

/-!
# Segmented ledger helpers

Not part of the audit surface. Barnacle's ledger helpers at a run with
two bounds (`Model/Segment.lean`): membership in a span's output, the
rounds it covers, the strict growth of `start`, and the two halves of
integrity. `mem_ledgerOf` and `ledgerOf_congr` are about `ledgerOf`
alone and are reused from the Barnacle arc rather than restated.

Two things come out easier than Barnacle's. `start_lt_succ` is the
boundary convention — `start (k + 1)` is `start k` plus a positive
interval — where Barnacle reads it off the anchor's threshold. And the
output range sits strictly below the anchor's round, so every use of
`closed` here widens its upper bound through `anchor_commits`.
-/

namespace LeanDag

namespace Adaptive

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {upd : UpdateRule R} {C₀ : Config Validator}
variable {U : R.Universe} {V : R.View U} {K : ℕ}

/-- A slot of the interval of range `k` lies in the range's rounds. -/
theorem round_of_mem_interval (Rn : SegRun R P upd C₀ U V K) {k κ : ℕ}
    (h1 : (Rn.cfg k).cum (Rn.start k + 1) ≤ κ)
    (h2 : κ < (Rn.cfg k).cum (Rn.start (k + 1) + 1)) :
    Rn.start k < (Rn.cfg k).roundOf κ ∧ (Rn.cfg k).roundOf κ ≤ Rn.start (k + 1) := by
  refine ⟨?_, ?_⟩
  · have := (Config.cum_le_iff_le_roundOf (Rn.cfg k)).1 h1
    omega
  · by_contra hcon
    have := (Config.cum_le_iff_le_roundOf (Rn.cfg k)).2
      (show Rn.start (k + 1) + 1 ≤ (Rn.cfg k).roundOf κ by omega)
    omega

/-- `start` grows strictly across a closed configuration: the boundary is
an interval further on, and an interval is positive. Barnacle needs the
anchor's threshold to see this; here it is the boundary convention. -/
theorem start_lt_succ (Rn : SegRun R P upd C₀ U V K) {k : ℕ} (hk : k < K) :
    Rn.start k < Rn.start (k + 1) := by
  rw [Rn.start_succ k hk]
  have := (Rn.bounds k).2.1
  omega

/-- `start` is monotone over the determined configurations. -/
theorem start_mono (Rn : SegRun R P upd C₀ U V K) {k k' : ℕ} (h : k ≤ k')
    (hK : k' ≤ K) : Rn.start k ≤ Rn.start k' := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih => exact le_trans (ih (by omega)) (start_lt_succ Rn (by omega)).le

/-- A block of range `k`'s ledger has a round in the range. -/
theorem round_of_mem_rangeLedger (hR : Properties.CommitsCandidate R.toDagRule)
    (Rn : SegRun R P upd C₀ U V K)
    {k : ℕ} (hk : k < K) {L : BlockId} (h : L ∈ Rn.rangeLedger k) :
    Rn.start k < (R.block U L).round ∧ (R.block U L).round ≤ Rn.start (k + 1) := by
  obtain ⟨κ, h1, h2, hv⟩ := mem_ledgerOf.mp h
  obtain ⟨hlo, hhi⟩ := round_of_mem_interval Rn h1 h2
  have hd := Rn.closed k hk κ hlo (le_of_lt (lt_of_le_of_lt hhi (Rn.anchor_commits k hk).2))
  rw [hv] at hd
  have hc := hR _ _ _ κ L hd
  have hlink : (R.toDagRule.block U L).round = (R.block U L).round := rfl
  rw [← hlink, hc.2.1]
  exact ⟨hlo, hhi⟩

/-- Within a range a block is committed by one slot: two committing slots
share the block's round and author, and `Slots.keyed` identifies them. -/
theorem slot_unique_of_rangeLedger (hR : Properties.CommitsCandidate R.toDagRule)
    (Rn : SegRun R P upd C₀ U V K)
    {k : ℕ} (hk : k < K) {κ₁ κ₂ : ℕ} {L : BlockId}
    (h₁ : (Rn.cfg k).cum (Rn.start k + 1) ≤ κ₁)
    (h₁' : κ₁ < (Rn.cfg k).cum (Rn.start (k + 1) + 1))
    (h₂ : (Rn.cfg k).cum (Rn.start k + 1) ≤ κ₂)
    (h₂' : κ₂ < (Rn.cfg k).cum (Rn.start (k + 1) + 1))
    (hv₁ : Rn.vdct k κ₁ = some L) (hv₂ : Rn.vdct k κ₂ = some L) : κ₁ = κ₂ := by
  obtain ⟨hlo₁, hhi₁⟩ := round_of_mem_interval Rn h₁ h₁'
  obtain ⟨hlo₂, hhi₂⟩ := round_of_mem_interval Rn h₂ h₂'
  have hb := (Rn.anchor_commits k hk).2
  have d₁ := Rn.closed k hk κ₁ hlo₁ (le_of_lt (lt_of_le_of_lt hhi₁ hb))
  have d₂ := Rn.closed k hk κ₂ hlo₂ (le_of_lt (lt_of_le_of_lt hhi₂ hb))
  rw [hv₁] at d₁
  rw [hv₂] at d₂
  have c₁ := hR _ _ _ κ₁ L d₁
  have c₂ := hR _ _ _ κ₂ L d₂
  apply (Rn.sched k).keyed
  simp only [Prod.mk.injEq]
  exact ⟨c₁.2.1.symm.trans c₂.2.1, c₁.2.2.symm.trans c₂.2.2⟩

/-- A closed range's ledger has no repetition. -/
theorem rangeLedger_nodup (hR : Properties.CommitsCandidate R.toDagRule)
    (Rn : SegRun R P upd C₀ U V K)
    {k : ℕ} (hk : k < K) : (Rn.rangeLedger k).Nodup := by
  unfold SegRun.rangeLedger
  set lo := (Rn.cfg k).cum (Rn.start k + 1)
  set hi := (Rn.cfg k).cum (Rn.start (k + 1) + 1)
  -- Restrict the verdicts to the interval so that injectivity is global.
  have : ledgerOf (Rn.vdct k) lo hi =
      ledgerOf (fun κ => if lo ≤ κ ∧ κ < hi then Rn.vdct k κ else none) lo hi :=
    ledgerOf_congr (fun κ h1 h2 => by rw [if_pos ⟨h1, h2⟩])
  rw [this]
  unfold ledgerOf
  refine List.Nodup.filterMap ?_ (List.nodup_range' 1)
  intro a a' b ha ha'
  simp only [Option.mem_def] at ha ha'
  split_ifs at ha ha' with h h'
  · exact slot_unique_of_rangeLedger hR Rn hk h.1 h.2 h'.1 h'.2 ha ha'
  all_goals exact absurd ‹_› (by simp_all)

/-- **A round above the boundary is decided and not output.** Segment
`k` decides every slot through the anchor's round, which lies strictly
above the boundary `start (k + 1)`; the slots of those rounds are at or
above `rangeLedger k`'s upper end, so none of them is read. Their
verdicts are what the segment discards, and the rounds are decided again
under configuration `k + 1`.

This is the naming-and-ordering split of `adaptive-leaders.md` §7 as a
statement: the configuration names leaders above its boundary, and the
output stops there. Barnacle has no counterpart, its boundary being the
anchor's own round. -/
theorem decided_and_not_output (Rn : SegRun R P upd C₀ U V K) {k : ℕ} (hk : k < K)
    {κ : ℕ} (hlo : Rn.start (k + 1) < (Rn.cfg k).roundOf κ)
    (hhi : (Rn.cfg k).roundOf κ ≤ (Rn.cfg k).roundOf (Rn.anchor k)) :
    R.Decided (Rn.cfg k).sched V κ (Rn.vdct k κ) ∧
      (Rn.cfg k).cum (Rn.start (k + 1) + 1) ≤ κ := by
  have hstart := start_lt_succ Rn hk
  refine ⟨Rn.closed k hk κ (by omega) hhi, ?_⟩
  exact (Config.cum_le_iff_le_roundOf (Rn.cfg k)).2 (by omega)

/-- **The span a segment decides reaches past the span it outputs**, by
at least one round: the anchor is strictly above the boundary. -/
theorem output_lt_decided (Rn : SegRun R P upd C₀ U V K) {k : ℕ} (hk : k < K) :
    Rn.start (k + 1) < (Rn.cfg k).roundOf (Rn.anchor k) :=
  (Rn.anchor_commits k hk).2

/-- **The ledger stops at the frontier.** Every block the run has output
by height `K'` sits at a round after `0` and at or below `start K'` — so
nothing above the round the last closed configuration reached is in the
ledger, whatever verdicts the run records above it. This is the
checkable form of the range discipline the run structure describes: a
configuration's schedule is extended above its range to name anchors,
and nothing named there is output. -/
theorem round_of_mem_ledgerUpto (hR : Properties.CommitsCandidate R.toDagRule)
    (Rn : SegRun R P upd C₀ U V K) {K' : ℕ} (hK' : K' ≤ K) {L : BlockId}
    (h : L ∈ Rn.ledgerUpto K') :
    Rn.start 0 < (R.block U L).round ∧ (R.block U L).round ≤ Rn.start K' := by
  unfold SegRun.ledgerUpto at h
  rw [List.mem_flatMap] at h
  obtain ⟨k, hk, hL⟩ := h
  rw [List.mem_range] at hk
  obtain ⟨hlo, hhi⟩ := round_of_mem_rangeLedger hR Rn (by omega) hL
  have h0 := start_mono Rn (Nat.zero_le k) (by omega)
  have h1 := start_mono Rn (show k + 1 ≤ K' by omega) (by omega)
  omega

/-- Two closed ranges' ledgers are disjoint: their blocks have rounds in
disjoint intervals. -/
theorem rangeLedger_disjoint (hR : Properties.CommitsCandidate R.toDagRule)
    (Rn : SegRun R P upd C₀ U V K)
    {k k' : ℕ} (h : k < k') (hK : k' < K) : (Rn.rangeLedger k).Disjoint (Rn.rangeLedger k') := by
  intro L hL hL'
  obtain ⟨_, hhi⟩ := round_of_mem_rangeLedger hR Rn (by omega) hL
  obtain ⟨hlo', _⟩ := round_of_mem_rangeLedger hR Rn hK hL'
  have := start_mono Rn (show k + 1 ≤ k' by omega) (by omega)
  omega


end Adaptive

end LeanDag
