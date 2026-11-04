import LeanDag.KPartialDag.Order.Statement
import LeanDag.KPartialDag.Helpers.Order
/-!
# The order — proof

What a certified block outputs lies in its available sub-DAG, held by
correct nodes by `avail_correctHeld`; a node reads it by `outIn_subset` and
`outIn_eq`; two nodes have one ledger by `ledgerIn_agree`; a leader of `T`
outputs the blocks of `T` below it by `mem_out_of_synchronisedOn`, and a node
deciding its slot by `mem_ledgerIn_of_leader_mem`.
-/

namespace LeanDag

namespace KPartialDag

namespace Order

theorem available : Available := by
  intro Validator BlockId Payload _ _ _ _ U K D L r hL hC z hz
  exact avail_correctHeld hL hC hz.1

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ U K D H L hH
  exact ⟨outIn_subset, outIn_eq hH⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ U K D H₁ H₂ g₁ g₂ n hK hH₁ hH₂ h₁ h₂ hf₁ hf₂
  exact ledgerIn_agree hK hH₁ hH₂ h₁ h₂ hf₁ hf₂

theorem includes : Includes := by
  intro Validator BlockId Payload _ _ _ _ U K D T R L x hK hcard hs hpop hL hLc hx hxc hRx hxL hD
  exact mem_out_of_synchronisedOn hK hcard hs hpop hL hLc hx hxc hRx hxL hD

theorem enters : Enters := by
  intro Validator BlockId Payload _ _ _ _ S U K D H T R g k x hK hcard hs hH hlead hpop hW hk hf
    hx hxc hRx hxk hD
  exact mem_ledgerIn_of_leader_mem hK hcard hs hH hlead hpop hW hk hf hx hxc hRx hxk hD

theorem holds : Statement := ⟨available, local_, agrees, includes, enters⟩

end Order

end KPartialDag

end LeanDag
