import LeanDag.Node.Runs.Statement
import LeanDag.Node.Helpers.Global
/-!
# Many honest nodes — proof

The blocks the honest nodes knew form a record at the quorum with honest
set `H` (`globalRecord`), which grounds what they knew (`ground`). Along
each node's run every store is a cut of the record, and the node's
decisions are nothing or one call of the loop on a view of the record
(`CommitInv.run`); two calls on views of one record are
prefix-comparable (`Loop.prefixComparable`).
-/

namespace LeanDag

namespace Node

namespace Runs

theorem safety : Safety := by
  intro Validator BlockId Payload _ _ _ cfg H ins hσ hadm hf hauth hinj hno v hv w hw
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  let U := globalRecord hinj hauth
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hg := ground hinj hauth hadm.2.2.2.1
  -- each honest node's decisions are nothing or one call of the loop on `U`
  have hone : ∀ u ∈ H, commitsOf (runOf cfg ins u).2 = [] ∨
      ∃ (V : U.View) (N : ℕ), commitsOf (runOf cfg ins u).2 =
        Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N := by
    intro u hu
    have h₀ : CommitInv (cfg.at u) U (State.init (cfg.at u)) [] := ⟨rfl, Or.inl rfl⟩
    have h := CommitInv.run (cfg := cfg.at u) (U := U) (f := cfg.f) (q := cfg.q) hg hσ ht
      (ins u) h₀ (isCut_init hinj hauth _) Held.init (fun _ h => absurd h List.not_mem_nil)
      (fun e he => ⟨u, hu, by simp only [knownOf, List.mem_append]; exact Or.inl he⟩)
      (fun e he => ⟨u, hu, by simp only [knownOf, List.mem_append]; exact Or.inr he⟩)
      fun i hi p G bs he => hno u hu p G bs (he ▸ hi)
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
