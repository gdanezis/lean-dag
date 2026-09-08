import LeanDag.Integration.DeliveryFill
/-!
# I17, I18 — the two remaining readings, made theorems

Two readings of the storage account (`integration.md` §3.5). I17: a
severed validator (past its horizon lag, `no_blocks_of_no_genesis`)
belongs to no reliable set, so at most `f` can be severed at once
without costing liveness — the horizon lag is a liveness-margin
parameter too, not only a storage one. I18: the reference discipline is
stated tighter than the storage bound needs — `RefsAccepted` charges a
block's cone to its own author's view, but the pool argument works for
any correct validator with a block at the round, so the Safe Skip
fill's blocks respect the novelty budget under either reading of what a
`Delivery` records.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## I17 — severance and the fault budget -/

/-- A validator with no blocks belongs to no populated set: production
is what membership of a reliable set asserts. -/
theorem notMem_of_no_blocks {T : Finset Validator} {r : ℕ} {v : Validator}
    (hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v)
    (hpop : PopulatedOn U T r) : v ∉ T := by
  intro hv
  obtain ⟨b, hb, hbc, -⟩ := hpop v hv
  exact hsev b hb hbc

/-- **I17.** At most `f` validators can be severed at once without
costing liveness: a reliable set of quorum size is disjoint from every
severed validator. -/
theorem card_severed_le {T S : Finset Validator} {r : ℕ}
    (hsev : ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).creator ≠ v)
    (hpop : PopulatedOn U T r)
    (hcard : quorumCard Validator ≤ T.card) :
    S.card ≤ F.f := by
  have hdisj : Disjoint T S := by
    rw [Finset.disjoint_right]
    intro v hvS hvT
    exact notMem_of_no_blocks (hsev v hvS) hpop hvT
  have hunion : (T ∪ S).card ≤ Fintype.card Validator :=
    Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint hdisj] at hunion
  have := F.card_validators
  omega

/-! ## I18 — the budget does not need the author -/

section Budget

variable {D : Delivery U} {v w : Validator} {b : BlockId} {n : ℕ}

/-- **I18.** The novelty budget holds for a block whose references lie
inside any correct validator's acceptances, provided that validator has
a block at the round — not specifically the block's own author. -/
theorem card_novelty_le_of_donor {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted w (n + 1))
    {c : BlockId} (hc : c ∈ U.ids) (hcc : (U.block c).creator = w)
    (hcr : (U.block c).round = n + 1) :
    (novelty U (viewUpto D v (n + 1)) b).card ≤ F.f * κ + 1 :=
  (card_novelty_le_viewGap_add_one hED hn hv hb hrefs).trans
    (Nat.add_le_add_right
      (card_viewGap_succ_le hbyz hED hn hv hw hc hcc hcr) 1)

end Budget

end Integration

end LeanDag
