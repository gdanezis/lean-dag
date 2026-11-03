import LeanDag.Scheme.Model.VotedBlock
import LeanDag.Common.History
/-!
# The scheme's vote is a vote-selection rule

When `ord` lists every parent, the depth-first search returns a block of
the slot in the voter's history, and returns nothing at a block of the
record only when that history holds no block of the slot. The search
walks the references as `historyUpto` does, and at a block of the record
a reference sits one round lower, so the pruning at the slot's round
loses nothing.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}
variable {ord : BlockId → Finset BlockId → List BlockId}

omit [Fintype Validator] in
/-- What the search returns lies in the history at that depth, at the slot. -/
theorem votedBlockUpto_sound (hord : ∀ b s x, x ∈ ord b s ↔ x ∈ s) {a : Validator} {r : ℕ} :
    ∀ {n b x}, votedBlockUpto ord U n b a r = some x →
      x ∈ historyUpto U n b ∧ (U.block x).creator = a ∧ (U.block x).round = r := by
  intro n
  induction n with
  | zero => intro b x h; simp [votedBlockUpto] at h
  | succ n ih =>
    intro b x h
    simp only [votedBlockUpto] at h
    split at h
    · simp at h
    · obtain ⟨b', hb', hfx⟩ := List.exists_of_findSome?_eq_some h
      have hb'r : b' ∈ (U.block b).refs := (hord _ _ _).mp hb'
      split at hfx
      · rename_i hslot
        cases hfx
        exact ⟨mem_historyUpto_succ.mpr (Or.inr ⟨_, hb'r, mem_historyUpto_self⟩), hslot⟩
      · obtain ⟨hx, hxc, hxr⟩ := ih hfx
        exact ⟨mem_historyUpto_succ.mpr (Or.inr ⟨b', hb'r, hx⟩), hxc, hxr⟩

variable [P.Mechanised]

omit [Fintype Validator] in
/-- At a block of the record, nothing returned means no block of the slot
lies in the history at that depth, below the block. -/
theorem votedBlockUpto_complete (hord : ∀ b s x, x ∈ ord b s ↔ x ∈ s) {a : Validator}
    {r : ℕ} : ∀ {n b}, b ∈ U.ids → votedBlockUpto ord U n b a r = none →
      ∀ x ∈ historyUpto U n b, x ≠ b → ¬ ((U.block x).creator = a ∧ (U.block x).round = r) := by
  intro n
  induction n with
  | zero => intro b _ _ x hx hxb; simp at hx; exact absurd hx hxb
  | succ n ih =>
    intro b hb h x hx hxb hslot
    have hxh : x ∈ history U b :=
      (mem_history_iff hb).mpr (reaches_of_mem_historyUpto hx)
    simp only [votedBlockUpto] at h
    split at h
    · rename_i hle
      have hxle := round_le_of_mem_history hb hxh
      have hxeq : (U.block x).round = (U.block b).round := by omega
      exact hxb (eq_of_mem_history_of_round_eq hb hxh hxeq)
    · rw [List.findSome?_eq_none_iff] at h
      obtain ⟨j, hj, hxj⟩ := (mem_historyUpto_succ.mp hx).resolve_left hxb
      have hjU := U.complete b hb j hj
      have hfj := h j ((hord _ _ _).mpr hj)
      split at hfj
      · simp at hfj
      · rename_i hjslot
        by_cases hxj' : x = j
        · subst hxj'; exact hjslot hslot
        · exact ih hjU hfj x hxj hxj' hslot

/-- **The scheme's vote is a vote-selection rule**, when `ord` lists every
parent. -/
def votedBlockSel (ord : BlockId → Finset BlockId → List BlockId)
    (hord : ∀ b s x, x ∈ ord b s ↔ x ∈ s) : VoteSel Validator BlockId Payload P honest where
  sel := votedBlock ord
  below U b a r hr := by simp [votedBlock, votedBlockUpto, hr]
  sound U b a r x hx := votedBlockUpto_sound hord hx
  complete U b a r hb hr hsel x hx hc hxr := by
    have hxb : x ≠ b := fun h => by subst h; omega
    have hxu : x ∈ historyUpto U ((U.block b).round + 1) b := hx
    exact votedBlockUpto_complete hord hb hsel x hxu hxb ⟨hc, hxr⟩

end Scheme

end LeanDag
