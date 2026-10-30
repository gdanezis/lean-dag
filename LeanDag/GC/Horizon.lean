import LeanDag.Common.Slots
import LeanDag.Network.Delivery
import LeanDag.GC.Bootstrap
/-!
# The horizon policy: heterogeneous cuts, one truth

`garbage.md` **G8** and **G9**: horizons need not be equal, only
admissible. `chop_chop` composes two cuts into one, so validators at
different admissible horizons are related by that one operator rather
than incomparable; agreement across such horizons follows by chaining
`decided_agree_chop` twice (`MysticetiProperties.decided_agree_horizons_chop`).
`viewUpto_subset_viewUpto_succ` is the depth rule: post-`R`, everything
any correct validator retains by round `m` is in every correct
validator's store by `m + 1`, so a horizon trailing the frontier by
`Λ ≥ 1` discards nothing a correct peer still lacks. Stated on any block
record, the correct validators read as the receivers `T` inside its
honest set.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {U : BlockRecord Validator BlockId Payload P honest}
variable {D : Delivery U} {v w : Validator} {G : ℕ} {T : Finset Validator}

/-! ## G8 — the composition law -/

private theorem block_eq_of {b₁ b₂ : Block Validator BlockId Payload}
    (hr : b₁.round = b₂.round) (hc : b₁.creator = b₂.creator)
    (hf : b₁.refs = b₂.refs) (hp : b₁.payload = b₂.payload) : b₁ = b₂ := by
  cases b₁; cases b₂
  simp_all

private theorem universe_eq_of {U₁ U₂ : BlockRecord Validator BlockId Payload P honest}
    (hids : U₁.ids = U₂.ids) (hblock : U₁.block = U₂.block) : U₁ = U₂ := by
  cases U₁; cases U₂
  cases hids; cases hblock
  rfl

theorem chopBlk_chop {G₁ G₂ : ℕ} (hG : G₁ ≤ G₂) (i : BlockId) :
    chopBlk (chop U G₁).block (G₂ - G₁) i = chopBlk U.block G₂ i := by
  refine block_eq_of ?_ ?_ ?_ ?_
  · rw [chopBlk_round, chopBlk_round, chop_block, chopBlk_round]
    omega
  · rw [chopBlk_creator, chopBlk_creator, chop_block, chopBlk_creator]
  · rcases Nat.lt_or_ge G₂ (U.block i).round with h2 | h2
    · rw [chopBlk_refs_of_lt (by rw [chop_block, chopBlk_round]; omega),
        chopBlk_refs_of_lt h2, chop_block,
        chopBlk_refs_of_lt (by omega)]
    · rw [chopBlk_refs_of_le (by rw [chop_block, chopBlk_round]; omega),
        chopBlk_refs_of_le h2]
  · rw [chopBlk_payload, chopBlk_payload, chop_block, chopBlk_payload]

/-- **G8, the composition law.** A deeper cut is just another cut: two
admissible horizons are always related by the one operator, so every
transfer theorem composes along the tower of truncations. -/
theorem chop_chop {G₁ G₂ : ℕ} (hG : G₁ ≤ G₂) :
    chop (chop U G₁) (G₂ - G₁) = chop U G₂ := by
  refine universe_eq_of ?_ (funext (chopBlk_chop hG))
  ext i
  rw [mem_chop_ids, mem_chop_ids, mem_chop_ids, chop_block, chopBlk_round]
  constructor
  · rintro ⟨⟨hi, h1⟩, h2⟩
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, h2⟩
    exact ⟨⟨hi, by omega⟩, by omega⟩

/-! ## G9 — the depth rule -/

/-- **G9, the engine.** Post-`R`, everything **any** correct validator
retains by round `m` is in **every** correct validator's store by
`m + 1`: the keeper's round-`(m + 1)` block carries its whole store
(`viewUpto_subset_history`, S10 + `includes`), and post-`R` that block is
delivered to and accepted by every correct validator. Possession is
universal one round deep. -/
theorem viewUpto_subset_viewUpto_succ [P.SelfParent] {R m : ℕ}
    (hED : EventuallyDeliversOn D T R) (hT : T ⊆ honest) (hcar : PopulatedOn U T (m + 1))
    (hv : v ∈ T) (hw : w ∈ T) (hR : R ≤ m + 1) :
    viewUpto D v m ⊆ viewUpto D w (m + 1) := by
  obtain ⟨b, hb, hbc, hbr⟩ := hcar v hv
  have hacc : b ∈ D.accepted w (m + 1) :=
    D.accepts_correct w (hT hw) (m + 1) b
      (hED (m + 1) hR w hw b hb hbr (by rw [hbc]; exact hT hv))
      (by rw [hbc]; exact hT hv)
  exact (viewUpto_subset_history (hT hv) hb hbc hbr).trans
    (history_subset_viewUpto (le_refl _) hacc)

/-- **G9 (no desync).** What a validator prunes at any horizon, every
correct peer already holds one round later: pruning below a correct
frontier at depth `Λ ≥ 1` discards nothing a correct peer still lacks.
A validator outside the envelope is on the bootstrap path, where the
attested base takes over (G10–G12). -/
theorem pruned_subset_peer_store [P.SelfParent] {R m : ℕ}
    (hED : EventuallyDeliversOn D T R) (hT : T ⊆ honest) (hcar : PopulatedOn U T (m + 1))
    (hv : v ∈ T) (hw : w ∈ T) (hR : R ≤ m + 1) :
    (viewUpto D v m).filter (fun i => (U.block i).round < G) ⊆
      viewUpto D w (m + 1) :=
  (Finset.filter_subset _ _).trans
    (viewUpto_subset_viewUpto_succ hED hT hcar hv hw hR)

end LeanDag
