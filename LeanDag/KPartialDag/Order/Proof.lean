import LeanDag.KPartialDag.Order.Statement
import LeanDag.KPartialDag.Helpers.Order
/-!
# The order — proof

What a certified block outputs lies in its available sub-DAG, held by
correct nodes by `avail_correctHeld`; a node reads it by `outIn_subset` and
`outIn_eq`; two nodes have one ledger by `ledgerIn_agree`; a leader of `T`
outputs the blocks of `T` below it by `mem_out_of_synchronisedOn`, and a node
deciding its slot by `mem_ledgerIn_of_leader_mem`, or every slot up to `D`
rounds above it by `mem_ledgerIn_of_gap`. A block's fate is settled by
`mem_ledgerIn_settled`; the ledger and its order grow by `ledgerIn_grows` and
`precedesIn_grows`, and the order is total by `precedesIn_irrefl`,
`precedesIn_trans`, `precedesIn_total` and `precedesIn_of_ref`.
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

theorem included : Included := by
  intro Validator BlockId Payload _ _ _ _ S U K D H T R g n x hK hcard hs hH hgap hdec hf hx hxc
    hRx hn hpop hW
  exact mem_ledgerIn_of_gap hK hcard hs hH hgap hdec hf hx hxc hRx hn hpop hW

theorem settled : Settled := by
  intro Validator BlockId Payload _ _ _ _ S U K D H g n n' b hH hdec hn hb
  exact mem_ledgerIn_settled hH hdec hn hb

theorem grows : Grows := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U K D H₁ H₂ g₁ g₂ n n' hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂
  obtain ⟨hl, he⟩ := ledgerIn_grows hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂
  exact ⟨hl, he, fun b b' h => precedesIn_grows hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂ h⟩

theorem total : Total := by
  intro Validator BlockId Payload _ _ _ _ _ _ U K D H g n
  exact ⟨precedesIn_irrefl, fun _ _ _ => precedesIn_trans,
    fun _ hb _ hb' hne => precedesIn_total hb hb' hne,
    fun _ _ _ hb h hk he he' => precedesIn_of_ref hb h hk he he'⟩

theorem holds : Statement :=
  ⟨available, local_, agrees, includes, enters, included, settled, grows, total⟩

end Order

end KPartialDag

end LeanDag
