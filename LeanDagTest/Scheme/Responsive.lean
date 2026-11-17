import LeanDag.Scheme.Responsive.Proof
import LeanDag.Scheme.Reactive.Proof
import LeanDag.Scheme.Model.LeastSel
/-!
# Responsive runs at a hybrid committee, on data

Hybrid Mysticeti at `f = 1`, `c = 1`, `n = 3f + 2c + 1 = 6`, parent quorum
`n − f − c = 4`: the full run (`Full.run`) is a responsive run of the row
at the least vote and round-robin on one slot per round, and on it every
decision-round block certifies the leader block of slot `2`
(`ReactiveRun.certifies`), with no timeout waited.
-/

namespace LeanDagTest

namespace Responsive

open LeanDag LeanDag.Scheme

attribute [local instance] noFaults

/-- The Hybrid Mysticeti row at six validators. -/
abbrev hmP : Params := Params.hybridMysticeti 6 1 1

/-- Its validity: quorum `4`, distinct authors, self-reference. -/
abbrev hmValid : Validity (Fin 6) (Lex (ℕ × Fin 6)) Unit :=
  ValidAt 4 (Clause.distinct.and Clause.selfParent)

/-- The least vote. -/
abbrev hmσ : VoteSel (Fin 6) (Lex (ℕ × Fin 6)) Unit hmValid Finset.univ := leastSel

/-- Round-robin, one slot per round. -/
@[reducible] def hmSlots : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 6, Nat.mod_lt _ (by omega)⟩)

attribute [local instance 3000] hmSlots

/-- The row at its committee. -/
theorem hm_row : hmP.PSRow 6 1 1 := Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))

/-- **The responsive run on data.** -/
def hmRun (N : ℕ) :
    SchemeReactive (S := hmSlots) 4 hmP hmσ (Full.record (n := 6) (q := 4) (by omega) N)
      Finset.univ N :=
  Full.run 4 hmP (Responsive.psRow_cert_le hm_row) hmσ

/-- **Every decision-round block certifies the leader block of slot `2`**,
validator `2`'s round-`2` block, read off the general theorem. -/
theorem hmRun_certifies (N : ℕ) (hN : 4 ≤ N) :
    ∀ c ∈ (Full.record (n := 6) (q := 4) (by omega) N).ids,
      ((Full.record (n := 6) (q := 4) (by omega) N).block c).round = 4 →
      IsCert hmP hmσ (Full.record (n := 6) (q := 4) (by omega) N) c (toLex (2, 2)) := by
  intro c hc hcr
  refine ReactiveRun.certifies (Fin 6) (Lex (ℕ × Fin 6)) Unit hmValid Finset.univ hmP hmσ
    (S := hmSlots) _ Finset.univ N 0 4 (hmRun N) 2 (toLex (2, 2))
    (Responsive.psRow_fits hm_row).1 (Finset.subset_univ _) (by simp) (le_refl 0)
    (fun _ _ => by change 2 * 0 + 0 ≤ 1; omega) (Nat.zero_le _)
    (by change _ ≤ N; simp [Params.hybridMysticeti]; omega)
    (Finset.mem_univ _)
    ⟨Full.mem_record_ids.mpr (by simp; omega), by simp, by apply Fin.ext; simp⟩
    ((Full.record (n := 6) (q := 4) (by omega) N).block c).creator (Finset.mem_univ _) c hc rfl
    (by rw [hcr]; simp [Params.hybridMysticeti])

end Responsive

end LeanDagTest

#print axioms LeanDag.Scheme.Responsive.holds
#print axioms LeanDagTest.Responsive.hmRun_certifies
