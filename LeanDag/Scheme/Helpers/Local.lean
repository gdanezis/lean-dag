import LeanDag.Scheme.Model.Local
import LeanDag.Scheme.Model.LeastSel
import LeanDag.Scheme.Helpers.VotedBlock
import LeanDag.Properties.Band
/-!
# The least vote and the scheme's vote are local

Across a band, a voter's history from the slot's round up is the same
set (`AgreeBand.reaches_old`, `AgreeBand.reaches_of`), so the least block
of the slot in it is the same block. The depth-first search reads the
same parents at every block strictly above the slot's round, and the same
author and round at the blocks it tests, so it returns the same block at
any fuel that reaches the slot's round.
-/

namespace LeanDag

namespace Scheme

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {R : AnchoredRule Validator BlockId Payload P honest}
variable {U U' : BlockRecord Validator BlockId Payload P honest} {lo hi g g' : ℕ}

/-- The slot's blocks in a voter's history, across a band. -/
theorem slotIn_band (h : AgreeBand R.toDagRule U U' lo hi g g') {q : BlockId} (hq : q ∈ U.ids)
    (hqlo : lo ≤ (U.block q).round + g) (hqhi : (U.block q).round + g ≤ hi) {a : Validator}
    {r r' : ℕ} (hr : lo ≤ r + g) (hrr : r + g = r' + g') :
    slotIn U' q a r' = slotIn U q a r := by
  have hq' : q ∈ U'.ids := AnchoredRule.band_mem h hq hqlo hqhi
  have hqb := AnchoredRule.band_block h hq hqlo hqhi
  unfold slotIn
  by_cases hle : (U.block q).round ≤ r
  · rw [if_pos hle, if_pos (by omega)]
  · rw [if_neg hle, if_neg (by omega)]
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hbh, hba, hbr⟩
      have hbre : ReachesFrom U'.block q b := (mem_history_iff (U := U') hq').mp hbh
      obtain ⟨hbU, hbreU, hbeq⟩ :=
        AgreeBand.reaches_old h hq hqlo hqhi hbre (by show lo ≤ (U'.block b).round + g'; omega)
      have hbeq' : (U.block b).round + g = (U'.block b).round + g' := hbeq
      have hbb := AnchoredRule.band_block h hbU (by omega) (by omega)
      exact ⟨(mem_history_iff (U := U) hq).mpr hbreU, by rw [← hbb.2]; exact hba, by omega⟩
    · rintro ⟨hbh, hba, hbr⟩
      have hbre : ReachesFrom U.block q b := (mem_history_iff (U := U) hq).mp hbh
      have hbU : b ∈ U.ids := history_subset_ids hq hbh
      have hbb := AnchoredRule.band_block h hbU (by omega) (by
        have := round_le_of_mem_history hq hbh; omega)
      refine ⟨(mem_history_iff (U := U') hq').mpr
        (AgreeBand.reaches_of h hq hqhi hbre (by show lo ≤ (U.block b).round + g; omega)),
        by rw [hbb.2]; exact hba, by omega⟩

/-- **The least vote is local.** -/
theorem leastSel_local : (leastSel : VoteSel Validator BlockId Payload P honest).Local := by
  intro R U U' lo hi g g' q a r r' h hq hqlo hqhi hr hrr
  simp only [leastSel, slotIn_band h hq hqlo hqhi hr hrr]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem findSome?_congr {α β : Type} {f f' : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = f' x) → l.findSome? f = l.findSome? f' := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro h
    simp only [List.findSome?_cons, h x (List.mem_cons_self ..),
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

variable {ord : BlockId → Finset BlockId → List BlockId}

omit [Fintype Validator] in
/-- **The search at any fuel past the depth** gives one answer. -/
theorem votedBlockUpto_fuel (hord : ∀ b s x, x ∈ ord b s ↔ x ∈ s) {a : Validator} {r : ℕ} :
    ∀ n m b, b ∈ U.ids → (U.block b).round - r < n → (U.block b).round - r < m →
      votedBlockUpto ord U n b a r = votedBlockUpto ord U m b a r := by
  intro n
  induction n with
  | zero => intro m b _ h; omega
  | succ n ih =>
    intro m b hb hn hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [votedBlockUpto]
    split
    · rfl
    · refine findSome?_congr fun j hj => ?_
      have hjr := (hord _ _ _).mp hj
      have hjU := U.complete b hb j hjr
      have hround := U.round_of_mem_refs hb hjr
      split
      · rfl
      · exact ih m j hjU (by omega) (by omega)

/-- **The search at one fuel, across a band.** -/
theorem votedBlockUpto_band (hord : ∀ b s x, x ∈ ord b s ↔ x ∈ s)
    (h : AgreeBand R.toDagRule U U' lo hi g g') {a : Validator} {r r' : ℕ}
    (hr : lo ≤ r + g) (hrr : r + g = r' + g') :
    ∀ n b, b ∈ U.ids → r ≤ (U.block b).round → (U.block b).round + g ≤ hi →
      votedBlockUpto ord U' n b a r' = votedBlockUpto ord U n b a r := by
  intro n
  induction n with
  | zero => intro b _ _ _; rfl
  | succ n ih =>
    intro b hb hrb hbhi
    have hbb := AnchoredRule.band_block h hb (by omega) hbhi
    simp only [votedBlockUpto]
    by_cases hle : (U.block b).round ≤ r
    · rw [if_pos hle, if_pos (by omega)]
    · rw [if_neg hle, if_neg (by omega), AnchoredRule.band_refs h hb (by omega) hbhi]
      refine findSome?_congr fun j hj => ?_
      have hjr := (hord _ _ _).mp hj
      have hjU := U.complete b hb j hjr
      have hround := U.round_of_mem_refs hb hjr
      have hjb := AnchoredRule.band_block h hjU (by omega) (by omega)
      rw [hjb.2, ih j hjU (by omega) (by omega)]
      by_cases hs : (U.block j).creator = a ∧ (U.block j).round = r
      · rw [if_pos hs, if_pos ⟨hs.1, by omega⟩]
      · rw [if_neg hs, if_neg (fun h' => hs ⟨h'.1, by omega⟩)]

/-- **The scheme's vote is local.** -/
theorem votedBlockSel_local (hord : ∀ b s x, x ∈ ord b s ↔ x ∈ s) :
    (votedBlockSel ord hord : VoteSel Validator BlockId Payload P honest).Local := by
  intro R U U' lo hi g g' q a r r' h hq hqlo hqhi hr hrr
  have hq' : q ∈ U'.ids := AnchoredRule.band_mem h hq hqlo hqhi
  have hqb := AnchoredRule.band_block h hq hqlo hqhi
  show votedBlock ord U' q a r' = votedBlock ord U q a r
  unfold votedBlock
  by_cases hle : (U.block q).round ≤ r
  · simp [votedBlockUpto, hle, show (U'.block q).round ≤ r' by omega]
  · set N := (U.block q).round + (U'.block q).round + 1
    rw [votedBlockUpto_fuel hord _ N q hq' (by omega) (by omega),
      votedBlockUpto_fuel hord _ N q hq (by omega) (by omega),
      votedBlockUpto_band hord h hr hrr N q hq (by omega) hqhi]

end Scheme

end LeanDag
