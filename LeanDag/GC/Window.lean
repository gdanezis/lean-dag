import LeanDag.GC.Chop
import LeanDag.DoS.Novelty
/-!
# The window: storage and liveness above the horizon

`garbage.md` §5. `chopD` induces a delivery for `chop U G` by shifting
rounds; the truncated store agrees with pruning a store below `G`
(G14); windowed novelty only shrinks as the cut advances (G13), so no
deferral decision ever flips the wrong way; and a validator whose
horizon trails its round by at most `Λ` retains a constant number of
blocks independent of runtime (G6, `card_retained_le`).
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {v w : Validator} {b x : BlockId} {G : ℕ}

/-! ## The store, characterized -/

/-- Membership in the accumulated store, unrolled: something accepted at
some round up to `t` carries `x` in its cone. -/
theorem mem_viewUpto {t : ℕ} :
    x ∈ viewUpto D v t ↔
      ∃ k, k ≤ t ∧ ∃ a ∈ D.accepted v k, x ∈ history U a := by
  induction t with
  | zero =>
      constructor
      · intro h
        obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp h
        exact ⟨0, le_refl 0, a, ha, hxa⟩
      · rintro ⟨k, hk, a, ha, hxa⟩
        obtain rfl : k = 0 := by omega
        exact Finset.mem_biUnion.mpr ⟨a, ha, hxa⟩
  | succ t ih =>
      rw [viewUpto_succ]
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · obtain ⟨k, hk, rest⟩ := ih.mp h
          exact ⟨k, by omega, rest⟩
        · obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp h
          exact ⟨t + 1, le_refl _, a, ha, hxa⟩
      · rintro ⟨k, hk, a, ha, hxa⟩
        rcases Nat.lt_or_ge k (t + 1) with hlt | hge
        · exact Finset.mem_union_left _ (ih.mpr ⟨k, by omega, a, ha, hxa⟩)
        · obtain rfl : k = t + 1 := by omega
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, ha, hxa⟩)

/-! ## The induced delivery -/

/-- A delivery for the truncation: round `m` of the window is round
`G + m` of the original. Nothing below the cut is consulted. -/
def chopD (D : Delivery U) (G : ℕ) : Delivery (chop U G) where
  held v m := D.held v (G + m)
  held_spec := by
    intro v m i hi
    obtain ⟨h1, h2⟩ := D.held_spec v (G + m) i hi
    refine ⟨mem_chop_ids.mpr ⟨h1, by omega⟩, ?_⟩
    rw [chop_block, chopBlk_round]
    omega
  accepted v m := D.accepted v (G + m)
  accepted_sub v m := D.accepted_sub v (G + m)
  accepted_inj := by
    intro v m i hi j hj hij
    rw [chop_block, chopBlk_creator, chopBlk_creator] at hij
    exact D.accepted_inj v (G + m) i hi j hj hij
  accepts_correct := by
    intro v hv m a ha hac
    rw [chop_block, chopBlk_creator] at hac
    exact D.accepts_correct v hv (G + m) a ha hac
  includes := by
    intro v hv m b hb hbc hbr
    rw [mem_chop_ids] at hb
    rw [chop_block, chopBlk_creator] at hbc
    rw [chop_block, chopBlk_round] at hbr
    have hsub := D.includes v hv (G + m) b hb.1 hbc (by omega)
    intro i hi
    rw [chop_block, chopBlk_refs_of_lt (by omega)]
    exact hsub hi

/-- The truncated delivery accepts at round `m` what the original accepted at `G + m`. -/
@[simp]
theorem chopD_accepted (m : ℕ) :
    (chopD D G).accepted v m = D.accepted v (G + m) := rfl

/-! ## G14 — the store correspondence -/

/-- **G14.** The truncated store *is* the store of the truncation:
pruning below `G` and accumulating in the window agree exactly. -/
theorem viewUpto_chopD (m : ℕ) :
    viewUpto (chopD D G) v m =
      (viewUpto D v (G + m)).filter fun i => G ≤ (U.block i).round := by
  ext x
  rw [Finset.mem_filter, mem_viewUpto, mem_viewUpto]
  constructor
  · rintro ⟨k, hk, a, ha, hxa⟩
    rw [chopD_accepted] at ha
    obtain ⟨ha_ids, ha_round⟩ := D.held_spec v (G + k) a (D.accepted_sub v (G + k) ha)
    have hachop : a ∈ (chop U G).ids := mem_chop_ids.mpr ⟨ha_ids, by omega⟩
    rw [history_chop hachop, Finset.mem_filter] at hxa
    exact ⟨⟨G + k, by omega, a, ha, hxa.1⟩, hxa.2⟩
  · rintro ⟨⟨k', hk', a, ha, hxa⟩, hGx⟩
    obtain ⟨ha_ids, ha_round⟩ := D.held_spec v k' a (D.accepted_sub v k' ha)
    rcases Nat.lt_or_ge k' G with hlt | hge
    · -- an acceptance below the cut carries nothing at or above it
      have := round_le_of_mem_history ha_ids hxa
      omega
    · refine ⟨k' - G, by omega, a, ?_, ?_⟩
      · rw [chopD_accepted, show G + (k' - G) = k' from by omega]
        exact ha
      · have hachop : a ∈ (chop U G).ids := mem_chop_ids.mpr ⟨ha_ids, by omega⟩
        rw [history_chop hachop, Finset.mem_filter]
        exact ⟨hxa, hGx⟩

/-! ## G13 — windowed novelty is monotone under cut-advance -/

/-- Advancing the cut only shrinks cones… -/
theorem history_chop_anti {G' : ℕ} (hGG : G ≤ G') (hb : b ∈ (chop U G').ids) :
    history (chop U G') b ⊆ history (chop U G) b := by
  have hb' : b ∈ (chop U G).ids := by
    rw [mem_chop_ids] at hb ⊢
    exact ⟨hb.1, by omega⟩
  rw [history_chop hb, history_chop hb']
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, by omega⟩

/-- …so it only shrinks novelty: **pruning cheapens blocks** — an
block within the budget never falls outside it as the window slides, and no
deferral decision ever flips the wrong way. -/
theorem novelty_chop_anti {G' : ℕ} (hGG : G ≤ G') (hb : b ∈ (chop U G').ids)
    (V : Finset BlockId) :
    novelty (chop U G') V b ⊆ novelty (chop U G) V b :=
  Finset.sdiff_subset_sdiff (history_chop_anti hGG hb) (Finset.Subset.refl _)

/-! ## The budget descends to the window -/

theorem byzBudget_chopD {κ : ℕ} (hbyz : ByzBudget D κ) :
    ByzBudget (chopD D G) κ := by
  intro v hv m b hb hbc
  rw [chop_block, chopBlk_creator] at hbc
  have h := hbyz v hv (G + m) b hb hbc
  refine le_trans (Finset.card_le_card ?_) h
  intro x hx
  obtain ⟨hb_ids, hb_round⟩ :=
    (chopD D G).held_spec v (m + 1) b ((chopD D G).accepted_sub v (m + 1) hb)
  rw [mem_novelty] at hx ⊢
  rw [history_chop hb_ids, Finset.mem_filter] at hx
  refine ⟨hx.1.1, ?_⟩
  intro hxV
  exact hx.2 (by
    rw [viewUpto_chopD]
    exact Finset.mem_filter.mpr ⟨hxV, hx.1.2⟩)

theorem refsAccepted_chopD (hra : RefsAccepted D) :
    RefsAccepted (chopD D G) := by
  intro w hw m b hb hbc hbr
  rw [mem_chop_ids] at hb
  rw [chop_block, chopBlk_creator] at hbc
  rw [chop_block, chopBlk_round] at hbr
  have hsub := hra w hw (G + m) b hb.1 hbc (by omega)
  intro i hi
  rw [chop_block, chopBlk_refs_of_lt (by omega)] at hi
  rw [chopD_accepted]
  exact hsub hi


/-- **G5.** The truncated universe never stalls above the cut: a
round-`r` block of `chop U G` is a round-`(G+r)` block of `U`, so this is
the production hypothesis with its index shifted. -/
theorem populated_chop {N : ℕ} (hpop : ∀ r ≤ N, Populated U r) (hG : G ≤ N) :
    ∀ r ≤ N - G, Populated (chop U G) r := by
  intro r hr v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop (G + r) (by omega) v hv
  refine ⟨b, mem_chop_ids.mpr ⟨hb, by omega⟩, ?_, ?_⟩
  · rw [chop_block, chopBlk_creator]; exact hbc
  · rw [chop_block, chopBlk_round]; omega

/-! ## G6 — bounded storage, the headline -/

/-- **G6.** A validator whose horizon `G` trails its round `t` by at
most `Λ` retains a constant number of blocks, independent of `t`: the
retained store is the truncated store (G14), which B4 bounds at window
depth `t − G ≤ Λ`. -/
theorem card_retained_le {κ Λ t : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ (Correct : Finset Validator))
    (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    ((viewUpto D v t).filter fun i => G ≤ (U.block i).round).card ≤
      (Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ))) := by
  have h := card_viewUpto_le (D := chopD D G)
    (byzBudget_chopD hbyz) (refsAccepted_chopD hra) hv (t - G)
  rw [viewUpto_chopD, show G + (t - G) = t from by omega] at h
  refine le_trans h (Nat.add_le_add ?_ (Nat.add_le_add_left ?_ _))
  · exact Nat.mul_le_mul_left _ (by omega)
  · exact Nat.mul_le_mul_right _ (by omega)

end LeanDag
