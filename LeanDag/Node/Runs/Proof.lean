import LeanDag.Node.Runs.Statement
import LeanDag.Node.Helpers.Global
import LeanDag.Node.Helpers.Commits
/-!
# Many honest nodes — proof

The honest nodes' stores at the end of the run, with the blocks they
knew, form a record at the row's validity with honest set `H`
(`globalRecord`). Every store along each node's run grows into its last
one at horizon `0`, so agrees with the record; each node's decisions are
then nothing or one call of the loop on a view of the record
(`CommitInv.run`), and two calls on views of one record are
prefix-comparable (`Loop.prefixComparable`).
-/

namespace LeanDag

namespace Node

namespace Runs

theorem safety : Safety := by
  intro Validator BlockId Payload _ _ _ cfg H ins hσ hadm hf hauth hinj hbase v hv w hw
  haveI : (rowValid (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
      cfg.q).Quorate cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  let U := globalRecord hinj hauth hbase
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  -- each honest node's decisions are nothing or one call of the loop on `U`
  have hone : ∀ u ∈ H, commitsOf (runOf cfg ins u).2 = [] ∨
      ∃ (V : U.View) (N : ℕ), commitsOf (runOf cfg ins u).2 =
        Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N := by
    intro u hu
    have hI := inv_runOf (cfg := cfg) (ins := ins) u
    have hagree : Agrees U (runOf cfg ins u).1.store :=
      ⟨fun j hj => Finset.mem_biUnion.mpr ⟨u, hu, hj⟩,
        blk_eq_globalBlock hinj (hbase u hu) fun j hj => known_sub hu (hI.known j hj)⟩
    have h₀ : CommitInv (cfg.at u) U (State.init (cfg.at u)) [] := ⟨rfl, Or.inl rfl⟩
    have h := CommitInv.run (cfg := cfg.at u) (U := U) (f := cfg.f) (q := cfg.q) hσ ht (ins u) h₀
      hagree ((hbase u hu).trans rfl)
    rcases h.2 with h0 | ⟨V, N, -, -, hcs⟩
    · exact Or.inl h0
    · exact Or.inr ⟨V, N, hcs⟩
  rcases hone v hv with h₁ | ⟨V₁, N₁, h₁⟩ <;> rcases hone w hw with h₂ | ⟨V₂, N₂, h₂⟩
  · rw [h₁]; exact Or.inl (List.nil_prefix)
  · rw [h₁]; exact Or.inl (List.nil_prefix)
  · rw [h₂]; exact Or.inr (List.nil_prefix)
  · rw [h₁, h₂]
    exact Scheme.Loop.prefixComparable _ _ _ _ cfg.q H cfg.f cfg.p boundedSel U V₁ V₂ 0 N₁ N₂
      (S := cfg.slots) ht (Nat.zero_le _) (Nat.zero_le _)

theorem holds : Statement := safety

end Runs

end Node

end LeanDag
