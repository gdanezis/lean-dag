import LeanDag.Node.Helpers.GlobalCut
import LeanDag.Node.Helpers.ReadsView
import LeanDag.Scheme.Helpers.Restart
/-!
# A decision, read on the record padded below its slot

`docs/dos-bounds.md` §5, Phase 3.2. The loop's decision of a slot `k` is a
verdict on any view agreeing with the loop's from the round of `k` up
(`ViewsAbove.decided_of_mem`). A view of the run's record, its blocks from
`G` up with the synthetic blocks below, is a view of the record padded below
`G` (`paddedView`), and agrees with it from every round `R ≥ G` up
(`viewsAbove_padded`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- An entry of a list over consecutive slots from `lo` lies in its tail from
the entry's slot. -/
theorem mem_drop_of_fst {β : Type} :
    ∀ {l : List (ℕ × β)} {lo : ℕ}, l.map Prod.fst = List.range' lo l.length →
      ∀ {e : ℕ × β}, e ∈ l → e ∈ l.drop (e.1 - lo)
  | [], _, _, _, he => absurd he List.not_mem_nil
  | a :: t, lo, hl, e, he => by
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl
    rcases List.mem_cons.mp he with rfl | he
    · rw [hl.1, Nat.sub_self]
      exact List.mem_cons_self
    · have hge : lo + 1 ≤ e.1 := by
        have h1 : e.1 ∈ t.map Prod.fst := List.mem_map_of_mem he
        rw [hl.2, List.mem_range'_1] at h1
        exact h1.1
      have ih := mem_drop_of_fst hl.2 he
      rw [show e.1 - lo = (e.1 - (lo + 1)) + 1 by omega, List.drop_succ_cons]
      exact ih

variable {P₁ P₂ : Validity Validator BlockId Payload} {H₁ H₂ : Finset Validator}
variable {R : ℕ} {U₁ : BlockRecord Validator BlockId Payload P₁ H₁}
variable {U₂ : BlockRecord Validator BlockId Payload P₂ H₂}
variable {σ₁ : VoteSel Validator BlockId Payload P₁ H₁}
variable {σ₂ : VoteSel Validator BlockId Payload P₂ H₂}
variable {V₁ : U₁.View} {V₂ : U₂.View}

/-- **A decision of the loop is a verdict on every view agreeing with the
loop's from the round of its slot up.** -/
theorem ViewsAbove.decided_of_mem [P₁.Mechanised] [P₂.Mechanised] [S : Slots Validator]
    (h : ViewsAbove R σ₁ σ₂ V₁ V₂) (p : Params) (hw : 2 ≤ p.waveLength)
    (hl : 1 ≤ p.linkSize) (hc : p.voteIsCert = false → 1 ≤ p.certThreshold)
    {lo N k : ℕ} {v : Option BlockId} (hlo : lo ≤ N + 1) (hk : R ≤ S.slotRound k)
    (he : (k, v) ∈ tryDecide p σ₁ U₁ V₁ lo N) :
    (schemeAnchored p σ₂).Decided U₂ V₂ k v := by
  obtain ⟨hmap, -⟩ := tryDecide_sound (σ := σ₁) (U := U₁) (V := V₁) hl hc hlo
  have hk' : k ∈ (tryDecide p σ₁ U₁ V₁ lo N).map Prod.fst := List.mem_map_of_mem he
  rw [hmap, List.mem_range'_1] at hk'
  have hd := mem_drop_of_fst hmap he
  rw [← tryDecide_restart (p := p) (σ := σ₁) (U := U₁) (V := V₁) hk'.1 (by omega)] at hd
  rw [h.tryDecide_eq p hw N hk] at hd
  have hkN : k ≤ N + 1 := by
    rcases Nat.lt_or_ge (N + 1) k with hlt | hle
    · unfold tryDecide at hd
      rw [Nat.sub_eq_zero_of_le hlt.le] at hd
      simp [scan] at hd
    · exact hle
  exact (tryDecide_sound (σ := σ₂) (U := U₂) (V := V₂) hl hc hkN).2 _ hd

section Padded

variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}
variable (hinj : HashInjective cfg H tr) (hauth : Authentic cfg H tr) [Infinite BlockId]
variable (hq : cfg.q ≤ Fintype.card Validator)

theorem mem_ladder_range {G : ℕ} {x : BlockId}
    (hx : x ∈ (Finset.range G).biUnion (ladder cfg H tr)) :
    ∃ v r, r < G ∧ x = fresh cfg H tr (v, r) := by
  obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v, r, Finset.mem_range.mp hr, rfl⟩

theorem ladder_sub_range {r G : ℕ} (hr : r < G) :
    ladder cfg H tr r ⊆ (Finset.range G).biUnion (ladder cfg H tr) := fun x hx =>
  Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr hr, hx⟩

include hinj hauth hq in
/-- **A view of the run's record, padded below `G`**: its blocks from `G` up,
with the synthetic blocks below. -/
noncomputable def paddedView (V : (globalRecord hinj hauth).View) (G : ℕ) :
    (padded hinj hauth hq G).View where
  ids := V.ids.filter (fun i => G ≤ (content cfg H tr i).round) ∪
    (Finset.range G).biUnion (ladder cfg H tr)
  subset_ids := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxV, hxG⟩ := Finset.mem_filter.mp hx
      obtain ⟨hk, hreal⟩ := mem_globalIds.mp (V.subset_ids hxV)
      exact mem_paddedIds.mpr (Or.inl (mem_globalCutIds.mpr ⟨hk, hxG, RealDown.of_real G hreal⟩))
    · exact Finset.mem_union_right _ hx
  complete := by
    intro i hi x hx
    change x ∈ (padBlk cfg H tr G i).refs at hx
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨hiV, hiG⟩ := Finset.mem_filter.mp hi
      have hik := (mem_globalIds.mp (V.subset_ids hiV)).1
      rw [padBlk_known hik] at hx
      split at hx
      · dsimp only at hx
        split at hx
        · exact absurd hx (Finset.notMem_empty x)
        · exact Finset.mem_union_right _ (ladder_sub_range (by omega) hx)
      · have hxV := V.complete i hiV x hx
        have hxr := ((globalRecord hinj hauth).valid i (V.subset_ids hiV)).predecessor x hx
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxV, by
          change (content cfg H tr x).round + 1 = (content cfg H tr i).round at hxr
          omega⟩)
    · obtain ⟨v, r, hr, rfl⟩ := mem_ladder_range hi
      rw [padBlk_fresh] at hx
      simp only [synth] at hx
      split at hx
      · exact absurd hx (Finset.notMem_empty x)
      · exact Finset.mem_union_right _ (ladder_sub_range (by omega) hx)

/-- **The padded view agrees with the view from every round `R ≥ G` up.** -/
theorem viewsAbove_padded (V : (globalRecord hinj hauth).View) {G R : ℕ} (hGR : G ≤ R) :
    ViewsAbove R boundedSel boundedSel V (paddedView hinj hauth hq V G) := by
  have hk : ∀ i ∈ V.ids, i ∈ knownIds cfg H tr := fun i hi =>
    (mem_globalIds.mp (V.subset_ids hi)).1
  refine ViewsAbove.of_boundedSel (fun i hi hR => ?_) (fun i hi hR => ?_)
    (fun i hi _ => (padBlk_known_fields (hk i hi)).1)
    (fun i hi _ => (padBlk_known_fields (hk i hi)).2.1) (fun i hi hR => ?_)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, by
      change R ≤ (content cfg H tr i).round at hR; omega⟩)
  · rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨hiV, -⟩ := Finset.mem_filter.mp hi
      refine ⟨hiV, ?_⟩
      change R ≤ (padBlk cfg H tr G i).round at hR
      rw [(padBlk_known_fields (hk i hiV)).1] at hR
      exact hR
    · obtain ⟨v, r, hr, rfl⟩ := mem_ladder_range hi
      change R ≤ (padBlk cfg H tr G _).round at hR
      rw [padBlk_fresh] at hR
      simp only [synth] at hR
      omega
  · change (padBlk cfg H tr G i).refs = (content cfg H tr i).refs
    rw [padBlk_of_lt (hk i hi) (by change R < (content cfg H tr i).round at hR; omega)]

end Padded

end Node

end LeanDag
