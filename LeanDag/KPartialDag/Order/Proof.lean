import LeanDag.KPartialDag.Order.Statement
import LeanDag.KPartialDag.Helpers.Order
/-!
# The order — proof

Each result is a helper of `Helpers/Order.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Order

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ U K D H L hH
  exact ⟨outIn_subset, outIn_eq hH⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ _ p U K D H₁ H₂ g₁ g₂ n n' hrow hK hH₁ hH₂ hn h₁ h₂
    hf₁ hf₂
  obtain ⟨hl, he⟩ := ledgerIn_grows hrow hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂
  exact ⟨hl, he, fun b b' h => precedesIn_grows hrow hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂ h⟩

theorem total : Total := by
  intro Validator BlockId Payload _ _ _ _ _ U K D H g n
  exact ⟨precedesIn_irrefl, fun _ _ _ => precedesIn_trans,
    fun _ hb _ hb' hne => precedesIn_total hb hb' hne,
    fun _ _ _ hb h hk he he' => precedesIn_of_ref hb h hk he he'⟩

theorem settled : Settled := by
  intro Validator BlockId Payload _ _ _ _ S p U K D H g n n' b hrow hH hdec hn hb
  exact mem_ledgerIn_settled hrow hH hdec hn hb

theorem excluded : Excluded := by
  intro Validator BlockId Payload _ _ _ _ S p U K D H₁ H₂ g₁ g₂ n n' b hrow hK hH₁ hH₂ h₁ h₂ hf₁
    hf₂ hn hb
  exact notMem_ledgerIn_of_settled hrow hK hH₁ hH₂ h₁ h₂ hf₁ hf₂ hn hb

theorem outputs : Outputs := by
  intro Validator BlockId Payload _ _ _ _ U K D T R L x hK ⟨hcard, hs, hpop⟩ hL hLc hx hxc hRx
    hxL hD
  exact mem_out_of_synchronisedOn hK hcard hs (fun r h1 h2 => hpop r h1 h2.le) hL hLc hx hxc
    hRx hxL hD

theorem included : Included := by
  intro Validator BlockId Payload _ _ _ _ S p U K D H T R g n x hrow hlive hK hH hgap hdec hf hx
    hxc hRx hn ⟨hcard, hs, hpop⟩ hW
  exact mem_ledgerIn_of_gap hrow hlive hK hcard hs hH hgap hdec hf hx hxc hRx hn hpop hW

theorem holds : Statement := ⟨local_, agrees, total, settled, excluded, outputs, included⟩

end Order

end KPartialDag

end LeanDag
