import LeanDag.Node.Helpers.CutAbove
/-!
# A kept proof decides its slot again

`docs/node-sync.md` D16. The store a proof of slot `k` builds holds blocks of
the proof, as given, at the round below the slot's without their references
and from the slot's round up with them (`proofStore_spec`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **The store a proof builds holds blocks of the proof**, as given, at the
round below the slot's or from the slot's round up, and keeps blocks without
their references only at the round below the slot's. -/
theorem proofStore_spec (k : ℕ) (L : List (BlockId × Block Validator BlockId Payload)) :
    (∀ i ∈ (proofStore cfg k L).ids, (i, (proofStore cfg k L).full i) ∈ hashed cfg L ∧
      (((proofStore cfg k L).full i).round + 1 = cfg.slots.slotRound k ∨
        cfg.slots.slotRound k ≤ ((proofStore cfg k L).full i).round)) ∧
    ∀ i, (proofStore cfg k L).kept[i]? ≠ none →
      ((proofStore cfg k L).blk i).round + 1 = cfg.slots.slotRound k := by
  let Q : Store Validator BlockId Payload → Prop := fun st =>
    (∀ i ∈ st.ids, (i, st.full i) ∈ hashed cfg L ∧
      ((st.full i).round + 1 = cfg.slots.slotRound k ∨ cfg.slots.slotRound k ≤ (st.full i).round)) ∧
    ∀ i, st.kept[i]? ≠ none → (st.blk i).round + 1 = cfg.slots.slotRound k
  have hstep : ∀ (st : Store Validator BlockId Payload) (e : BlockId × Block Validator BlockId Payload),
      e ∈ hashed cfg L → Q st → Q (proofStep cfg k st e) := by
    intro st e he ⟨h₁, h₂⟩
    unfold proofStep
    split
    · rename_i hnew
      split
      · rename_i hr
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · rw [Store.base_ids] at hi
          rw [Store.full_base]
          split
          · rename_i hie; subst hie; exact ⟨he, Or.inl hr⟩
          · rename_i hie; exact h₁ i ((Finset.mem_insert.mp hi).resolve_left hie)
        · have hk : (st.base e.1 e.2 hnew).kept = st.kept.insert e.1 e.2.refs := rfl
          rw [hk, Std.TreeMap.getElem?_insert] at hi
          rw [Store.base_blk]
          by_cases h : i = e.1
          · rw [if_pos h]; exact hr
          · have hc : ¬ compare e.1 i = Ordering.eq := fun e' => h (compare_eq_iff_eq.mp e').symm
            simp only [hc, if_false] at hi
            rw [if_neg h]; exact h₂ i hi
      · split
        · rename_i _ h'
          refine ⟨fun i hi => ?_, fun i hi => ?_⟩
          · rw [Store.insert_ids] at hi
            rw [Store.full_insert]
            split
            · rename_i hie; subst hie; exact ⟨he, Or.inr h'.1⟩
            · rename_i hie; exact h₁ i ((Finset.mem_insert.mp hi).resolve_left hie)
          · have hi' : st.kept[i]? ≠ none := hi
            have hie : i ≠ e.1 := fun h' => hi' (by rw [h']; exact Store.kept_none_of_notMem st hnew)
            rw [Store.insert_blk, if_neg hie]
            exact h₂ i hi'
        · exact ⟨h₁, h₂⟩
    · exact ⟨h₁, h₂⟩
  have hfold : ∀ (l : List (BlockId × Block Validator BlockId Payload))
      (st : Store Validator BlockId Payload), (∀ e ∈ l, e ∈ hashed cfg L) → Q st →
      Q (l.foldl (proofStep cfg k) st) := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons e l ih =>
      exact fun st hl h => ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (hstep st e (hl e List.mem_cons_self) h)
  exact hfold _ _ (fun e he => he) ⟨fun i hi => absurd hi (Finset.notMem_empty i),
    fun i hi => absurd (by simp [Store.empty]) hi⟩

omit [Fintype Validator] in
/-- **A proof's blocks enter the store it builds**: a family of the proof's
blocks, in order of round, from the round below the slot's up, each from the
slot's round up with its references in the family, one round below it, and
valid at the row, under a block map the proof agrees with. -/
theorem proofStore_holds {g : BlockId → Block Validator BlockId Payload} {k : ℕ}
    {L : List (BlockId × Block Validator BlockId Payload)} {F : Finset BlockId}
    (hsort : (hashed cfg L).Pairwise fun x y => x.2.round ≤ y.2.round)
    (hg : ∀ e ∈ hashed cfg L, g e.1 = e.2)
    (hF : ∀ x ∈ F, (x, g x) ∈ hashed cfg L ∧ cfg.slots.slotRound k ≤ (g x).round + 1)
    (hcl : ∀ x ∈ F, cfg.slots.slotRound k ≤ (g x).round → (g x).refs ⊆ F ∧
      (∀ j ∈ (g x).refs, (g j).round + 1 = (g x).round) ∧ rowValid cfg.q cfg.xp g (g x)) :
    F ⊆ (proofStore cfg k L).ids := by
  -- what of the family the rest of the list does not hold is already held
  have key : ∀ (l : List (BlockId × Block Validator BlockId Payload))
      (st : Store Validator BlockId Payload),
      l.Pairwise (fun x y => x.2.round ≤ y.2.round) → (∀ e ∈ l, g e.1 = e.2) → ReadsAs g st →
      (∀ x ∈ F, (x, g x) ∉ l → x ∈ st.ids) → F ⊆ (l.foldl (proofStep cfg k) st).ids := by
    intro l
    induction l with
    | nil => exact fun st _ _ _ hin x hx => hin x hx List.not_mem_nil
    | cons e l ih =>
      intro st hp hgl hst hin
      rw [List.foldl_cons]
      have hge : g e.1 = e.2 := hgl e List.mem_cons_self
      -- the step keeps the store's blocks and reads them as `g`
      have hsub : st.ids ⊆ (proofStep cfg k st e).ids := by
        unfold proofStep
        split
        · split
          · rw [Store.base_ids]; exact Finset.subset_insert _ _
          · split
            · rw [Store.insert_ids]; exact Finset.subset_insert _ _
            · exact subset_rfl
        · exact subset_rfl
      have hst' : ReadsAs g (proofStep cfg k st e) := by
        unfold proofStep
        split
        · split
          · intro i hi
            rw [Store.base_ids] at hi
            rw [Store.full_base]
            split
            · rename_i hie; subst hie; exact hge.symm
            · rename_i hie; exact hst i ((Finset.mem_insert.mp hi).resolve_left hie)
          · split
            · intro i hi
              rw [Store.insert_ids] at hi
              rw [Store.full_insert]
              split
              · rename_i hie; subst hie; exact hge.symm
              · rename_i hie; exact hst i ((Finset.mem_insert.mp hi).resolve_left hie)
            · exact hst
        · exact hst
      refine ih _ (List.Pairwise.of_cons hp) (fun x hx => hgl x (List.mem_cons_of_mem _ hx)) hst'
        fun x hx hxl => ?_
      by_cases hxe : (x, g x) = e
      · subst hxe
        unfold proofStep
        split
        · rename_i hnew
          obtain ⟨-, hlow⟩ := hF x hx
          split
          · rw [Store.base_ids]; exact Finset.mem_insert_self _ _
          · rename_i hnb
            have hup : cfg.slots.slotRound k ≤ (g x).round := by
              change ¬ (g x).round + 1 = cfg.slots.slotRound k at hnb
              omega
            obtain ⟨hrefs, hpred, hv⟩ := hcl x hx hup
            have hrefst : (g x).refs ⊆ st.ids := fun j hj => hin j (hrefs hj) fun hjl => by
              have hjr := hpred j hj
              rcases List.mem_cons.mp hjl with hje | hjl
              · have := congrArg (fun e => e.2.round) hje
                simp only at this
                omega
              · have := List.rel_of_pairwise_cons hp hjl
                simp only at this
                omega
            have hr := ready_of_refs (cfg := cfg) (F := 0) (y := (x, g x)) ⟨hpred, hv⟩ hst hrefst
              hnew
            have hc : st.Checks cfg.q cfg.xp x (g x) := by simpa [readyOn] using hr
            rw [dif_pos ⟨hup, hc⟩, Store.insert_ids]
            exact Finset.mem_insert_self _ _
        · rename_i hold
          exact not_not.mp hold
      · exact hsub (hin x hx fun h => (List.mem_cons.mp h).elim hxe hxl)
  exact key _ _ hsort hg (fun i hi => by simp [Store.empty] at hi)
    fun x hx hn => absurd (hF x hx).1 hn

omit [Fintype Validator] in
/-- **A store decides no slot directly whose round lies above every block's**,
at a positive skip threshold. -/
theorem tryDirect_past_top (hskip : 1 ≤ cfg.p.skipThreshold) (st : Store Validator BlockId Payload)
    {j : ℕ} (hj : ∀ i ∈ st.ids, (st.blk i).round < cfg.slots.slotRound j) :
    tryDirect (S := cfg.slots) cfg.p boundedSel st.toRecord st.view j = none := by
  have hnone : ∀ r, cfg.slots.slotRound j ≤ r → blocksAt st.toRecord r = ∅ := fun r hrt => by
    ext x
    simp only [mem_blocksAt, Finset.notMem_empty, iff_false, not_and]
    intro hx hxr
    have := hj x hx
    change (st.blk x).round = r at hxr
    omega
  unfold tryDirect
  rw [if_neg]
  · have hc : candidatesIn (S := cfg.slots) st.toRecord st.view j = ∅ := by
      ext x
      simp only [candidatesIn, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hx _ hxr
      have := hj x hx
      change (st.blk x).round = _ at hxr
      omega
    rw [hc]
    rfl
  · unfold HoldsAtLeast heldAuthors blamersAt
    rw [hnone (cfg.slots.slotRound j + cfg.p.voteOffset) (Nat.le_add_right _ _)]
    simp only [Finset.filter_empty, Finset.empty_inter]
    change ¬ cfg.p.skipThreshold ≤ (creatorsOf _ ∅).card
    simp [creatorsOf]
    omega

section Replay

variable {P : Validity Validator BlockId Payload} [P.Mechanised] {H : Finset Validator}

omit [Fintype Validator] in
/-- **A proof decides its slot as a view does**: a store built from a proof
that holds the witness of the view's decision of slot `k`, at or above the
slot's round, and reads as the view's record from the slot's round up, at the
same rounds and authors there and the same blocks above, gives the view's
verdict. -/
theorem verdictOn_of_decision (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (hl : 1 ≤ cfg.p.linkSize) (hcm : 1 ≤ cfg.p.commitThreshold)
    (hc : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    {U : BlockRecord Validator BlockId Payload P H} {V : U.View} {N k : ℕ} {d : Option BlockId}
    (hkN : k ≤ N) (hdec : decisionAt (S := cfg.slots) cfg.p boundedSel U V N k = some d)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hin : ∀ i ∈ (proofStore cfg k L).ids,
      cfg.slots.slotRound k ≤ ((proofStore cfg k L).full i).round →
        i ∈ V.ids ∧ (U.block i).round = ((proofStore cfg k L).full i).round ∧
          (U.block i).creator = ((proofStore cfg k L).full i).creator ∧
          (cfg.slots.slotRound k < ((proofStore cfg k L).full i).round →
            U.block i = (proofStore cfg k L).full i))
    (hwit : ∀ x ∈ witnessAt (S := cfg.slots) cfg.p boundedSel U V N k,
      x ∈ (proofStore cfg k L).ids ∧
        cfg.slots.slotRound k ≤ ((proofStore cfg k L).full x).round)
    (hN : ∀ i ∈ (proofStore cfg k L).ids,
      decidable cfg ((proofStore cfg k L).blk i).round - 1 ≤ N) :
    verdictOn cfg k L = some d := by
  letI := cfg.slots
  obtain ⟨-, hkept⟩ := proofStore_spec (cfg := cfg) k L
  set st := proofStore cfg k L with hst
  set R := cfg.slots.slotRound k
  -- from the slot's round up, the store keeps every block with its references
  have hfull : ∀ i, R ≤ (st.blk i).round → st.full i = st.blk i := fun i hi =>
    st.full_of_kept_none (by
      by_contra hk
      have := hkept i hk
      omega)
  have hround : ∀ i, (st.full i).round = (st.blk i).round := fun i => (st.full_fields i).1
  let A := st.ids.filter fun i => R ≤ (st.blk i).round
  have hAU : A ⊆ U.ids := fun i hi => by
    obtain ⟨hi, hir⟩ := Finset.mem_filter.mp hi
    exact V.subset_ids (hin i hi (by rw [hround]; exact hir)).1
  let W := U.historiesView A hAU
  have hWV : W.ids ⊆ V.ids := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨ha, har⟩ := Finset.mem_filter.mp ha
    exact history_subset_view (hin a ha (by rw [hround]; exact har)).1 hxa
  have hwitW : witnessAt (S := cfg.slots) cfg.p boundedSel U V N k ⊆ W.ids := fun x hx => by
    obtain ⟨hxs, hxr⟩ := hwit x hx
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨hxs, by rw [← hround]; exact hxr⟩,
      mem_history_self⟩
  have hdW := decisionAt_of_witness (S := cfg.slots) hl hcm hc N k W hWV hwitW d hdec
  -- a path from a block of `A` down to a block at or above the slot's round stays in `A`
  have hdown : ∀ a ∈ A, ∀ x, Reaches U a x → R ≤ (U.block x).round → x ∈ A := by
    intro a ha x hax hxR
    induction hax using Relation.ReflTransGen.head_induction_on with
    | refl => exact ha
    | @head y c hstep hrest ih =>
      have hstep : c ∈ (U.block y).refs := hstep
      obtain ⟨hy, hyr⟩ := Finset.mem_filter.mp ha
      obtain ⟨hyV, hyR, -, hyB⟩ := hin y hy (by rw [hround]; exact hyr)
      have hcU := U.causal.refs_round y (V.subset_ids hyV) c hstep
      have hcx := round_le_of_reaches (U.complete y (V.subset_ids hyV) c hstep) hrest
      have hyB := hyB (by omega)
      have hcy : c ∈ (st.blk y).refs := by rw [← hfull y hyr, ← hyB]; exact hstep
      have hcs := st.complete y hy c hcy
      have hcp := st.pred y hy c hcy
      refine ih (Finset.mem_filter.mpr ⟨hcs, ?_⟩)
      change (st.blk c).round + 1 = (st.blk y).round at hcp
      have := hround y
      omega
  have hVA : ViewsAbove R boundedSel boundedSel st.view W :=
    ViewsAbove.of_boundedSel
      (fun i hi hR => Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hR⟩, mem_history_self⟩)
      (fun i hi hR => by
        obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
        exact Finset.mem_filter.mp (hdown a ha i ((mem_history_iff (hAU ha)).mp hia) hR))
      (fun i hi hR => by
        change (U.block i).round = (st.blk i).round
        rw [(hin i hi (by rw [hround]; exact hR)).2.1, hround])
      (fun i hi hR => by
        change (U.block i).creator = (st.blk i).creator
        rw [(hin i hi (by rw [hround]; exact hR)).2.2.1, (st.full_fields i).2.1])
      (fun i hi hR => by
        change (U.block i).refs = (st.blk i).refs
        have hR' : R < (st.blk i).round := hR
        rw [(hin i hi (by rw [hround]; exact hR'.le)).2.2.2 (by rw [hround]; exact hR'),
          hfull i hR'.le])
  have hT := hVA.tryDecide_eq (S := cfg.slots) cfg.p hw N (lo := k) le_rfl
  have hds : decisionAt (S := cfg.slots) cfg.p boundedSel st.toRecord st.view N k = some d :=
    (decisionAt_of_mem_tryDecide (hT ▸ mem_tryDecide_of_decisionAt hkN hdW)).2
  -- scanning to the store's last slot decides alike
  set N' := max k (decidable cfg st.topRound - 1)
  have hds' : decisionAt (S := cfg.slots) cfg.p boundedSel st.toRecord st.view N' k = some d := by
    cases hdir : tryDirect (S := cfg.slots) cfg.p boundedSel st.toRecord st.view k with
    | some v =>
      unfold decisionAt decideSlot at hds ⊢
      rw [hdir] at hds ⊢
      exact hds
    | none =>
      have hskip : 1 ≤ cfg.p.skipThreshold := by
        by_contra h0
        unfold tryDirect at hdir
        rw [if_pos (by unfold HoldsAtLeast; omega)] at hdir
        cases hdir
      -- no slot is decided directly past the last slot of the store's blocks' rounds
      set N₀ := max k (st.ids.sup fun i => decidable cfg (st.blk i).round - 1)
      have hq : ∀ j, N₀ < j →
          tryDirect (S := cfg.slots) cfg.p boundedSel st.toRecord st.view j = none := by
        intro j hj
        refine tryDirect_past_top hskip st fun i hi => ?_
        by_contra hle
        have h₁ := lt_decidable (cfg := cfg) (not_lt.mp hle)
        have h₂ : decidable cfg (st.blk i).round - 1 ≤ N₀ :=
          (Finset.le_sup (f := fun i => decidable cfg (st.blk i).round - 1) hi).trans
            (le_max_right _ _)
        omega
      have hN₀N : N₀ ≤ N := max_le hkN (Finset.sup_le hN)
      have hN₀N' : N₀ ≤ N' := max_le (le_max_left _ _) ((Finset.sup_le fun i hi =>
        Nat.sub_le_sub_right (decidable_mono (by
          rw [st.topRound_eq]; exact Finset.le_sup (f := fun i => (st.blk i).round) hi)) 1).trans
        (le_max_right _ _))
      rw [decisionAt_of_quiet hq hN₀N' (le_max_left _ _)]
      rw [decisionAt_of_quiet hq hN₀N (le_max_left _ _)] at hds
      exact hds
  -- the loop's first output from `k` is that decision
  unfold verdictOn
  dsimp only
  rw [hσ]
  have hscan : scan (S := cfg.slots) cfg.p boundedSel st.toRecord st.view N' (N' + 1 - k) =
      (k, decisionAt (S := cfg.slots) cfg.p boundedSel st.toRecord st.view N' k) ::
        scan (S := cfg.slots) cfg.p boundedSel st.toRecord st.view N' (N' - k) := by
    have := le_max_left k (decidable cfg st.topRound - 1)
    rw [show N' + 1 - k = N' - k + 1 by omega, scan, decisionAt, show N' - (N' - k) = k by omega]
  unfold tryDecide
  rw [hscan, hds', List.takeWhile_cons_of_pos (by simp)]
  rfl

end Replay

end Node

end LeanDag
