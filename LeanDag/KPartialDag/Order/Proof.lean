import LeanDag.KPartialDag.Order.Statement
import LeanDag.KPartialDag.Helpers.Order
/-!
# The order — proof

A node reads a leader's output by `outIn_subset` and `outIn_eq`; ledgers
agree and grow by `ledgerIn_grows` and `precedesIn_grows`; the order is total
by `precedesIn_irrefl`, `precedesIn_trans`, `precedesIn_total` and
`precedesIn_of_ref`; a block's fate is settled by `mem_ledgerIn_settled`; a
leader of `T` outputs the blocks of `T` below it by
`mem_out_of_synchronisedOn`; and every block of `T` enters by
`mem_ledgerIn_of_gap`.
-/

namespace LeanDag

namespace KPartialDag

namespace Order

theorem local_ : Local := by
  intro Validator BlockId Payload _ _ _ _ U K D H L hH
  exact ⟨outIn_subset, outIn_eq hH⟩

theorem agrees : Agrees := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U K D H₁ H₂ g₁ g₂ n n' hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂
  obtain ⟨hl, he⟩ := ledgerIn_grows hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂
  exact ⟨hl, he, fun b b' h => precedesIn_grows hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂ h⟩

theorem total : Total := by
  intro Validator BlockId Payload _ _ _ _ _ _ U K D H g n
  exact ⟨precedesIn_irrefl, fun _ _ _ => precedesIn_trans,
    fun _ hb _ hb' hne => precedesIn_total hb hb' hne,
    fun _ _ _ hb h hk he he' => precedesIn_of_ref hb h hk he he'⟩

theorem settled : Settled := by
  intro Validator BlockId Payload _ _ _ _ S U K D H g n n' b hH hdec hn hb
  exact mem_ledgerIn_settled hH hdec hn hb

theorem outputs : Outputs := by
  intro Validator BlockId Payload _ _ _ _ U K D T R L x hK ⟨hcard, hs, hpop⟩ hL hLc hx hxc hRx
    hxL hD
  exact mem_out_of_synchronisedOn hK hcard hs (fun r h1 h2 => hpop r h1 h2.le) hL hLc hx hxc
    hRx hxL hD

theorem included : Included := by
  intro Validator BlockId Payload _ _ _ _ S U K D H T R g n x hK hH hgap hdec hf hx hxc hRx hn
    ⟨hcard, hs, hpop⟩ hW
  exact mem_ledgerIn_of_gap hK hcard hs hH hgap hdec hf hx hxc hRx hn hpop hW

theorem holds : Statement := ⟨local_, agrees, total, settled, outputs, included⟩

end Order

end KPartialDag

end LeanDag
