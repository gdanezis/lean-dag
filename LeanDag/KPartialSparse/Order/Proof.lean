import LeanDag.KPartialSparse.Order.Statement
import LeanDag.KPartialSparse.Helpers.Order
/-!
# Sparse K-partial DAG — the order, proof

Each result is a helper of `Helpers/Order.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Order

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ _ _ U K D H L hH
  exact ⟨outIn_subset, outIn_eq hH⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ _ p U K D H₁ H₂ g₁ g₂ n n' hrow hdeep hI hH₁
    hH₂ hn h₁ h₂ hf₁ hf₂
  obtain ⟨hl, he⟩ := ledgerIn_grows hrow hdeep hI hH₁ hH₂ hn h₁ h₂ hf₁ hf₂
  exact ⟨hl, he, fun b b' h => precedesIn_grows hrow hdeep hI hH₁ hH₂ hn h₁ h₂ hf₁ hf₂ h⟩

theorem total : Total := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U K D H g n
  exact ⟨precedesIn_irrefl, fun _ _ _ h₁ h₂ => precedesIn_trans h₁ h₂,
    fun _ hb _ hb' hne => precedesIn_total hb hb' hne,
    fun _ _ _ hb h hk he he' => precedesIn_of_ref hb h hk he he'⟩

theorem settled : Settled := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K D H g n n' b hdec hn hb
  exact mem_ledgerIn_settled hdec hn hb

theorem excluded : Excluded := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K D H₁ H₂ g₁ g₂ n n' b hrow hdeep hI hH₁
    hH₂ h₁ h₂ hf₁ hf₂ hn hb
  exact notMem_ledgerIn_of_settled hrow hdeep hI hH₁ hH₂ h₁ h₂ hf₁ hf₂ hn hb

theorem outputs : Outputs := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U K D T R k L x hT hch hDK hL hlead hcov hpop hx
    hxc hRx hxL hD
  exact mem_out_of_covers hT hch hDK hL hlead hcov hpop hx hxc hRx hxL hD

theorem included : Included := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ _ p U K D H T R g n x hrow hdeep hI hlive hT hDK
    hH hgap hdec hf hx hxc hRx hn hsync hcov hW
  exact mem_ledgerIn_of_gap hrow hdeep hI hlive hT hDK hH hgap hdec hf hx hxc hRx hn hsync hcov hW

theorem holds : Statement := ⟨local_, agrees, total, settled, excluded, outputs, included⟩

end Order

end KPartialSparse

end LeanDag
