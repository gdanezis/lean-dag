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
  have hstep : ∀ (st : Store Validator BlockId Payload)
      (e : BlockId × Block Validator BlockId Payload),
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
            have hie : i ≠ e.1 := fun h' =>
              hi' (by rw [h']; exact Store.kept_none_of_notMem st hnew)
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

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A walk down from a block at or above `r`, stopping at `r − 1`, steps one
round down within `D` each time**, where every block of `D` at or above `r`
has its references in `D`, one round below it: what it reaches lies in `D`,
within its steps below, and it holds the references of what it reaches at or
above `r` in fewer steps than rounds below. -/
theorem historyUptoFrom_closed {blk : BlockId → Block Validator BlockId Payload} {r : ℕ}
    {D : Finset BlockId}
    (hQ : ∀ i ∈ D, r ≤ (blk i).round → ∀ j ∈ (blk i).refs,
      j ∈ D ∧ (blk j).round + 1 = (blk i).round) :
    ∀ (m : ℕ) (w : BlockId), w ∈ D → r ≤ (blk w).round → m ≤ (blk w).round + 1 - r →
      ∀ x ∈ historyUptoFrom blk m w, x ∈ D ∧ (blk w).round ≤ m + (blk x).round ∧
        (blk x).round ≤ (blk w).round ∧ (r ≤ (blk x).round → (blk w).round < m + (blk x).round →
          (blk x).refs ⊆ historyUptoFrom blk m w) := by
  intro m
  induction m with
  | zero =>
    intro w hwD _ _ x hx
    rw [historyUptoFrom_zero, Finset.mem_singleton] at hx
    subst hx
    exact ⟨hwD, by omega, le_rfl, fun _ h => absurd h (by omega)⟩
  | succ m ih =>
    intro w hwD hw hm x hx
    rcases mem_historyUptoFrom_succ.mp hx with rfl | ⟨j, hj, hxj⟩
    · refine ⟨hwD, by omega, le_rfl, fun _ _ y hy => mem_historyUptoFrom_succ.mpr
        (Or.inr ⟨y, hy, mem_historyUptoFrom_self⟩)⟩
    · obtain ⟨hjD, hjw⟩ := hQ w hwD hw j hj
      rcases m with _ | m
      · rw [historyUptoFrom_zero, Finset.mem_singleton] at hxj
        subst hxj
        exact ⟨hjD, by omega, by omega, fun _ h => absurd h (by omega)⟩
      · obtain ⟨h₀, h₁, h₂, h₃⟩ := ih j hjD (by omega) (by omega) x hxj
        refine ⟨h₀, by omega, by omega, fun hxr hlt y hy => mem_historyUptoFrom_succ.mpr
          (Or.inr ⟨j, hj, h₃ hxr (by omega) hy⟩)⟩

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
/-- **A family of blocks enters a store that takes them in, in order of
round**, at a node that drops: each member at or above the floor `F` with its
references in the family, one round below it, and valid at the row, under a
block map the store and the blocks agree with. -/
theorem acceptOn_holds (hdr : cfg.drops = true) {g : BlockId → Block Validator BlockId Payload}
    {F : ℕ} {G : Finset BlockId}
    (hcl : ∀ x ∈ G, F ≤ (g x).round → (g x).refs ⊆ G ∧
      (∀ j ∈ (g x).refs, (g j).round + 1 = (g x).round) ∧ rowValid cfg.q cfg.xp g (g x)) :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) (st : Store Validator BlockId Payload),
      l.Pairwise (fun x y => x.2.round ≤ y.2.round) → (∀ e ∈ l, g e.1 = e.2) → ReadsAs g st →
      (∀ x ∈ G, (x, g x) ∉ l → x ∈ st.ids) →
        G ⊆ (l.foldl (fun s e => acceptOn cfg F s e.1 e.2) st).ids := by
  intro l
  induction l with
  | nil => exact fun st _ _ _ hin x hx => hin x hx List.not_mem_nil
  | cons e l ih =>
    intro st hp hgl hst hin
    rw [List.foldl_cons]
    have hge : g e.1 = e.2 := hgl e List.mem_cons_self
    refine ih _ (List.Pairwise.of_cons hp) (fun x hx => hgl x (List.mem_cons_of_mem _ hx))
      (hst.accept hge) fun x hx hxl => ?_
    by_cases hxe : (x, g x) = e
    · subst hxe
      by_cases hxs : x ∈ st.ids
      · exact (Grows.accept (cfg := cfg) F st _ _).1 hxs
      by_cases hF : F ≤ (g x).round
      · obtain ⟨hrefs, hpred, hv⟩ := hcl x hx hF
        have hrefst : (g x).refs ⊆ st.ids := fun j hj => hin j (hrefs hj) fun hjl => by
          have hjr := hpred j hj
          rcases List.mem_cons.mp hjl with hje | hjl
          · have := congrArg (fun e => e.2.round) hje
            simp only at this
            omega
          · have := List.rel_of_pairwise_cons hp hjl
            simp only at this
            omega
        have hr := ready_of_refs (cfg := cfg) (F := 0) (y := (x, g x)) ⟨hpred, hv⟩ hst hrefst hxs
        have hc : st.Checks cfg.q cfg.xp x (g x) := by simpa [readyOn] using hr
        unfold acceptOn
        rw [dif_pos ⟨hxs, hc⟩, Store.insert_ids]
        exact Finset.mem_insert_self _ _
      · unfold acceptOn
        split
        · rw [Store.insert_ids]; exact Finset.mem_insert_self _ _
        · rw [dif_pos ⟨hdr, hxs, Nat.lt_of_not_le hF⟩, Store.base_ids]
          exact Finset.mem_insert_self _ _
    · exact (Grows.accept (cfg := cfg) F st e.1 e.2).1
        (hin x hx fun h => (List.mem_cons.mp h).elim hxe hxl)

omit [Fintype Validator] in
/-- **The store a proof builds is valid at the row from the slot's round up.** -/
theorem proofStore_upperValid (k : ℕ) (L : List (BlockId × Block Validator BlockId Payload)) :
    UpperValid cfg.q cfg.xp (cfg.slots.slotRound k) (proofStore cfg k L) := by
  have hstep : ∀ (st : Store Validator BlockId Payload)
      (e : BlockId × Block Validator BlockId Payload),
      UpperValid cfg.q cfg.xp (cfg.slots.slotRound k) st →
      UpperValid cfg.q cfg.xp (cfg.slots.slotRound k) (proofStep cfg k st e) := by
    intro st e h
    unfold proofStep
    split
    · split
      · rename_i hr
        exact h.base (by omega)
      · split
        · rename_i _ h'
          exact h.insert h'.2.2.2
        · exact h
    · exact h
  have hfold : ∀ (l : List (BlockId × Block Validator BlockId Payload))
      (st : Store Validator BlockId Payload), UpperValid cfg.q cfg.xp (cfg.slots.slotRound k) st →
      UpperValid cfg.q cfg.xp (cfg.slots.slotRound k) (l.foldl (proofStep cfg k) st) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons e l ih => exact fun st h => ih _ (hstep st e h)
  exact hfold _ _ fun j hj => absurd hj (Finset.notMem_empty j)

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

variable (cfg) in
/-- **A kept proof decides its slot again**: for the slot `k` kept with the
blocks `P`, a view decides `k` as the node did, with its witness in `P` from
the slot's round up; `P` lies on the disk, from the round below the slot's
up and within the view's scan; and from the slot's round up the blocks of `P`
are the view's, at the same rounds and authors and above the slot's round
the same blocks, with their references in `P`, valid at the row. -/
def ProofHolds (s : State Validator BlockId Payload) (e : ℕ × Finset BlockId) : Prop :=
  ∃ (U : BlockRecord Validator BlockId Payload (stored Validator BlockId Payload) ∅)
    (V : U.View) (N : ℕ) (d : Option BlockId),
    (e.1, d) ∈ s.decided ∧ e.1 ≤ N ∧
    decisionAt (S := cfg.slots) cfg.p boundedSel U V N e.1 = some d ∧
    (∀ x ∈ witnessAt (S := cfg.slots) cfg.p boundedSel U V N e.1,
      x ∈ e.2 ∧ cfg.slots.slotRound e.1 ≤ (s.disk.blk x).round) ∧
    ∀ x ∈ e.2, x ∈ s.disk.ids ∧ cfg.slots.slotRound e.1 ≤ (s.disk.blk x).round + 1 ∧
      decidable cfg (s.disk.blk x).round - 1 ≤ N ∧
      (cfg.slots.slotRound e.1 ≤ (s.disk.blk x).round →
        x ∈ V.ids ∧ (U.block x).round = (s.disk.blk x).round ∧
        (U.block x).creator = (s.disk.blk x).creator ∧
        (cfg.slots.slotRound e.1 < (s.disk.blk x).round → U.block x = s.disk.full x) ∧
        (s.disk.full x).refs ⊆ e.2 ∧ rowValid cfg.q cfg.xp s.disk.full (s.disk.full x))

variable (cfg) in
/-- **The proofs a node keeps decide their slots again.** -/
def ProofsHold (s : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ s.proofs, ProofHolds cfg s e

omit [Fintype Validator] in
/-- **A kept proof decides its slot again on a state that keeps its blocks as
accepted, and the decision.** -/
theorem ProofHolds.keep {s s' : State Validator BlockId Payload} {e : ℕ × Finset BlockId}
    (h : ProofHolds cfg s e) (hd : ∀ x ∈ s.decided, x ∈ s'.decided)
    (hk : ∀ x ∈ e.2, x ∈ s.disk.ids → x ∈ s'.disk.ids ∧ s'.disk.full x = s.disk.full x) :
    ProofHolds cfg s' e := by
  obtain ⟨U, V, N, d, hdm, hkN, hdec, hwit, hP⟩ := h
  have hr : ∀ x ∈ e.2, (s'.disk.blk x).round = (s.disk.blk x).round := fun x hx => by
    rw [← (s'.disk.full_fields x).1, (hk x hx (hP x hx).1).2, (s.disk.full_fields x).1]
  have hcr : ∀ x ∈ e.2, (s'.disk.blk x).creator = (s.disk.blk x).creator := fun x hx => by
    rw [← (s'.disk.full_fields x).2.1, (hk x hx (hP x hx).1).2, (s.disk.full_fields x).2.1]
  refine ⟨U, V, N, d, hd _ hdm, hkN, hdec, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hxP, hxr⟩ := hwit x hx
    exact ⟨hxP, by rw [hr x hxP]; exact hxr⟩
  · obtain ⟨hxd, hxr, hxN, hxu⟩ := hP x hx
    rw [hr x hx]
    refine ⟨(hk x hx hxd).1, hxr, hxN, fun hxR => ?_⟩
    obtain ⟨hV, hUr, hUc, hUb, hrefs, hv⟩ := hxu hxR
    rw [hcr x hx, (hk x hx hxd).2]
    refine ⟨hV, hUr, hUc, hUb, hrefs, rowValid_congr (fun j hj => ?_) hv⟩
    rw [(hk j (hrefs hj) (hP j (hrefs hj)).1).2]
    exact ⟨rfl, rfl, rfl⟩

variable (cfg) in
/-- **`s'` keeps what the proofs of `s` read**: the decisions and proofs of
`s`, the blocks of those proofs as accepted, and its new proofs decide their
slots again; and it keeps a proof of each slot it decided, if `s` does. -/
structure KeepsProofs (s s' : State Validator BlockId Payload) : Prop where
  decided : ∀ x ∈ s.decided, x ∈ s'.decided
  sub : ∀ e ∈ s.proofs, e ∈ s'.proofs
  fresh : ∀ e ∈ s'.proofs, e ∉ s.proofs → ProofHolds cfg s' e
  disk : ∀ e ∈ s.proofs, ∀ x ∈ e.2, x ∈ s.disk.ids →
    x ∈ s'.disk.ids ∧ s'.disk.full x = s.disk.full x
  paired : (∀ x ∈ s.decided, ∃ P, (x.1, P) ∈ s.proofs) → ∀ x ∈ s'.decided, ∃ P, (x.1, P) ∈ s'.proofs

omit [Fintype Validator] in
theorem KeepsProofs.refl (s : State Validator BlockId Payload) : KeepsProofs cfg s s :=
  ⟨fun _ h => h, fun _ h => h, fun _ h hn => absurd h hn, fun _ _ _ _ h => ⟨h, rfl⟩, id⟩

omit [Fintype Validator] in
theorem KeepsProofs.trans {a b c : State Validator BlockId Payload} (h₁ : KeepsProofs cfg a b)
    (h₂ : KeepsProofs cfg b c) : KeepsProofs cfg a c := by
  refine ⟨fun x hx => h₂.decided x (h₁.decided x hx), fun e he => h₂.sub e (h₁.sub e he),
    fun e he hn => ?_, fun e he x hx hxa => ?_, h₂.paired ∘ h₁.paired⟩
  · by_cases hb : e ∈ b.proofs
    · exact (h₁.fresh e hb hn).keep h₂.decided fun x hx hxb => h₂.disk e hb x hx hxb
    · exact h₂.fresh e he hb
  · obtain ⟨hxb, hfb⟩ := h₁.disk e he x hx hxa
    obtain ⟨hxc, hfc⟩ := h₂.disk e (h₁.sub e he) x hx hxb
    exact ⟨hxc, hfc.trans hfb⟩

omit [Fintype Validator] in
/-- **Proofs that decide their slots again keep doing so.** -/
theorem ProofsHold.keeps {s s' : State Validator BlockId Payload} (hp : ProofsHold cfg s)
    (h : KeepsProofs cfg s s') : ProofsHold cfg s' := fun e he => by
  by_cases hs : e ∈ s.proofs
  · exact (hp e hs).keep h.decided fun x hx hxs => h.disk e hs x hx hxs
  · exact h.fresh e he hs

omit [Fintype Validator] in
/-- A state with the decisions and proofs, its disk grown, keeps the proofs. -/
theorem KeepsProofs.of_grows {s s' : State Validator BlockId Payload}
    (hg : Grows s.disk s'.disk) (hd : s'.decided = s.decided) (hp : s'.proofs = s.proofs) :
    KeepsProofs cfg s s' :=
  ⟨fun _ hx => hd ▸ hx, fun _ he => hp ▸ he, fun _ he hn => absurd (hp ▸ he) hn,
    fun _ _ _ _ hx => ⟨hg.1 hx, hg.full hx⟩, fun h x hx => hp ▸ h x (hd ▸ hx)⟩

omit [Fintype Validator] in
theorem KeepsProofs.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    KeepsProofs cfg s s' := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -⟩ := tryBuild_some h
  have hdp : s'.decided = s.decided ∧ s'.proofs = s.proofs := by
    obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
    unfold buildAbove at h
    dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨release_decided _, release_proofs _⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  exact KeepsProofs.of_grows ((Grows.insert s.disk).trans (Grows.of_restrips hst)) hdp.1 hdp.2

omit [Fintype Validator] in
theorem KeepsProofs.progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    KeepsProofs cfg s (Node.progress cfg fuel s).1
  | 0, s => KeepsProofs.refl s
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact (KeepsProofs.tryBuild hb).trans (KeepsProofs.progress fuel s₁)
    · exact KeepsProofs.refl s

omit [Fintype Validator] in
theorem KeepsProofs.accept (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : KeepsProofs cfg s (Node.accept cfg s id b) :=
  KeepsProofs.of_grows (by rw [accept_disk]; exact Grows.accept _ _ _ _)
    (accept_rest s id b).2.2.2.2.2.2.1 (by unfold Node.accept; split <;> (try split) <;> rfl)

omit [Fintype Validator] in
theorem KeepsProofs.absorb (s : State Validator BlockId Payload) :
    ∀ L : List (BlockId × Block Validator BlockId Payload), KeepsProofs cfg s (Node.absorb cfg s L)
  | [] => KeepsProofs.refl s
  | x :: L => by
    unfold Node.absorb
    rw [List.foldl_cons]
    exact (KeepsProofs.accept s x.1 x.2).trans (KeepsProofs.absorb _ L)

omit [Fintype Validator] in
theorem KeepsProofs.tidy (s : State Validator BlockId Payload) :
    KeepsProofs cfg s (Node.tidy s) :=
  KeepsProofs.of_grows (Grows.refl _) rfl rfl

omit [Fintype Validator] in
theorem KeepsProofs.flushSyncs : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    KeepsProofs cfg s (Node.flushSyncs cfg fuel s)
  | 0, s => KeepsProofs.refl s
  | fuel + 1, s => by
    unfold Node.flushSyncs
    dsimp only
    split
    · exact KeepsProofs.refl s
    · exact ((KeepsProofs.absorb s _).trans (KeepsProofs.tidy _)).trans
        (KeepsProofs.flushSyncs fuel _)

omit [Fintype Validator] in
theorem KeepsProofs.release (s : State Validator BlockId Payload) :
    KeepsProofs cfg s (Node.release cfg s) :=
  KeepsProofs.of_grows (Grows.of_restrips (release_disk _)) (release_decided _) (release_proofs _)

omit [Fintype Validator] in
/-- **Dropping keeps the proofs**: it lets go of no block of a proof. -/
theorem KeepsProofs.drop (s : State Validator BlockId Payload) :
    KeepsProofs cfg s (Node.drop cfg s) := by
  refine ⟨fun x hx => by rw [drop_decided]; exact hx, fun e he => by rw [drop_proofs]; exact he,
    fun e he hn => absurd (by rw [drop_proofs] at he; exact he) hn, fun e he x hx hxs => ?_,
    fun h x hx => by rw [drop_proofs]; rw [drop_decided] at hx; exact h x hx⟩
  unfold Node.drop
  split
  · obtain ⟨-, h₂, h₃⟩ := Store.eraseAll_spec (dropSet cfg s) s.disk
    have hxe : x ∈ (s.disk.eraseAll (dropSet cfg s)).ids := h₂ x hxs fun hxd => by
      unfold dropSet at hxd
      have := (List.mem_filter.mp hxd).2
      simp only [decide_eq_true_eq] at this
      exact this.2.2.2.1 e he hx
    refine ⟨hxe, ?_⟩
    change (s.disk.eraseAll (dropSet cfg s)).full x = s.disk.full x
    unfold Store.full
    rw [(h₃ x hxe).2, (h₃ x hxe).1]
  · exact ⟨hxs, rfl⟩

omit [Fintype Validator] in
/-- **The proof a decision keeps decides its slot again**: a decision of the
loop on the memory's window at the round of the next undecided slot, from a
floor at or below that round and a disk valid at the row from the floor up,
on any state with the same disk that keeps the decision. -/
theorem proofHolds_decide (hσ : cfg.σ = boundedSel) {s s' : State Validator BlockId Payload}
    (hab : UpperValid cfg.q cfg.xp s.floor s.disk) (hfl : s.floor ≤ cfg.slots.slotRound s.lo)
    {N k : ℕ} {d : Option BlockId}
    (he : (k, d) ∈ Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ
      (s.memory.window (cfg.slots.slotRound s.lo)) (s.memory.windowView (cfg.slots.slotRound s.lo))
      s.lo N)
    (hN : N = decidable cfg s.disk.topRound - 1) (hdisk : s'.disk = s.disk)
    (hdec : (k, d) ∈ s'.decided) : ProofHolds cfg s' (k, proofOf cfg s N k) := by
  letI := cfg.slots
  set R := cfg.slots.slotRound s.lo with hR
  rw [hσ] at he
  obtain ⟨hkN, hdecU⟩ := decisionAt_of_mem_tryDecide he
  have hlok : s.lo ≤ k := by
    have hlo : s.lo ≤ N + 1 := by
      by_contra h
      have : Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel (s.memory.window R)
          (s.memory.windowView R) s.lo N = [] := by
        unfold Scheme.tryDecide; rw [show N + 1 - s.lo = 0 by omega]; rfl
      rw [this] at he; exact absurd he List.not_mem_nil
    have := List.mem_map_of_mem (f := Prod.fst) he
    rw [tryDecide_fst (S := cfg.slots) hlo, List.mem_range'_1] at this
    exact this.1
  have hRk : R ≤ cfg.slots.slotRound k := cfg.slots.mono hlok
  set sk := cfg.slots.slotRound k
  -- the memory reads the disk from the floor up
  have hround : ∀ i, (s.disk.full i).round = (s.disk.blk i).round := fun i =>
    (s.disk.full_fields i).1
  have hwin : ∀ x ∈ s.disk.ids, R ≤ (s.disk.blk x).round →
      x ∈ (s.memory.windowView R).ids ∧
        ((s.memory.window R).block x).round = (s.disk.blk x).round ∧
        ((s.memory.window R).block x).creator = (s.disk.blk x).creator ∧
        (R < (s.disk.blk x).round → (s.memory.window R).block x = s.disk.full x) := by
    intro x hx hxR
    have hxm : x ∈ s.memory.ids := s.mirrors.mem_of hx (by omega)
    have hmr : (s.memory.blk x).round = (s.disk.blk x).round := s.mirrors.round hxm
    refine ⟨s.memory.mem_windowIds.mpr ⟨hxm, by omega⟩, ?_, ?_, fun hlt => ?_⟩
    · change (s.memory.windowBlk R x).round = _
      rw [Store.windowBlk_round, hmr]
    · change (s.memory.windowBlk R x).creator = _
      rw [← s.mirrors.creator hxm]
      unfold Store.windowBlk
      dsimp only
      split <;> rfl
    · change s.memory.windowBlk R x = _
      have hkn : s.disk.kept[x]? = none := by
        by_contra hk
        have := s.low x hk
        omega
      unfold Store.windowBlk
      dsimp only
      rw [if_neg (by omega), s.mirrors.blk x hxm, s.disk.full_of_kept_none hkn]
      unfold Store.windowBlk
      dsimp only
      rw [if_neg (by omega)]
  -- the witness lies on the disk at or above the slot's round
  have hwd : ∀ w ∈ witnessAt (S := cfg.slots) cfg.p boundedSel (s.memory.window R)
      (s.memory.windowView R) N k, w ∈ s.disk.ids ∧ sk ≤ (s.disk.blk w).round := by
    intro w hw
    have hwV := witnessAt_subset (S := cfg.slots) N k hw
    obtain ⟨hwm, -⟩ := s.memory.mem_windowIds.mp hwV
    have hwr := witnessAt_round (S := cfg.slots) N k w hw
    change sk ≤ (s.memory.windowBlk R w).round at hwr
    rw [Store.windowBlk_round, s.mirrors.round hwm] at hwr
    exact ⟨s.mirrors.sub hwm, hwr⟩
  -- the walks from the witness close under references from the slot's round up
  have hQ : ∀ i ∈ s.disk.ids, sk ≤ (s.disk.full i).round →
      ∀ j ∈ (s.disk.full i).refs, j ∈ s.disk.ids ∧
        (s.disk.full j).round + 1 = (s.disk.full i).round := fun i hi hir j hj => by
    obtain ⟨hrefs, hv⟩ := hab i hi (by rw [← hround]; omega)
    exact ⟨hrefs hj, hv.predecessor j hj⟩
  unfold proofOf ProofHolds
  rw [hσ, hdisk]
  dsimp only
  refine ⟨s.memory.window R, s.memory.windowView R, N, d, hdec, hkN, hdecU,
    fun x hx => ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hx, mem_historyUptoFrom_self⟩,
      (hwd x hx).1, by have := (hwd x hx).2; omega⟩, (hwd x hx).2⟩, fun x hx => ?_⟩
  obtain ⟨hxh, hxd, hxr⟩ := Finset.mem_filter.mp hx
  obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hxh
  refine ⟨hxd, by omega, ?_, fun hxk => ?_⟩
  · rw [hN]
    exact Nat.sub_le_sub_right (decidable_mono (by
      rw [s.disk.topRound_eq]; exact Finset.le_sup (f := fun i => (s.disk.blk i).round) hxd)) 1
  · obtain ⟨hxV, hxr', hxc, hxb⟩ := hwin x hxd (by omega)
    obtain ⟨hwD, hwr⟩ := hwd w hw
    obtain ⟨-, -, -, hcl⟩ := historyUptoFrom_closed hQ _ w hwD (by rw [hround]; exact hwr)
      (by rw [hround]) x hxw
    obtain ⟨hrefs, hv⟩ := hab x hxd (by omega)
    refine ⟨hxV, hxr', hxc, fun h => hxb (by omega), fun y hy => ?_, hv⟩
    have hyh := hcl (by rw [hround]; exact hxk) (by rw [hround, hround]; omega) hy
    have hyd := hrefs hy
    have hyr := hv.predecessor y hy
    rw [hround, hround] at hyr
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hw, hyh⟩, hyd, by omega⟩

omit [Fintype Validator] in
/-- **Deciding keeps the proofs**, those it adds deciding their slots again,
from a disk valid at the row from the floor up. -/
theorem KeepsProofs.decideStep (hσ : cfg.σ = boundedSel) {s : State Validator BlockId Payload}
    (hab : UpperValid cfg.q cfg.xp s.floor s.disk) :
    KeepsProofs cfg s (Node.decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hc
    refine (KeepsProofs.trans ?_ (KeepsProofs.release _)).trans (KeepsProofs.drop _)
    refine ⟨fun x hx => List.mem_append_right _ hx, fun e he => List.mem_append_right _ he,
      fun e he hn => ?_, fun _ _ x _ hx => ⟨hx, rfl⟩, fun h x hx => ?_⟩
    swap
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨_, List.mem_append_left _ (List.mem_reverse.mpr
          (List.mem_map_of_mem (f := fun e => (e.1, _)) (List.mem_reverse.mp hx)))⟩
      · obtain ⟨P, hP⟩ := h x hx
        exact ⟨P, List.mem_append_right _ hP⟩
    rcases List.mem_append.mp he with he | he
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp he)
      exact proofHolds_decide hσ hab hc.2.1 hx rfl rfl
        (List.mem_append_left _ (List.mem_reverse.mpr hx))
    · exact absurd he hn
  · exact KeepsProofs.refl s

omit [Fintype Validator] in
/-- **A pass keeps the proofs**, from a disk valid at the row from the floor
up. -/
theorem KeepsProofs.advance (hσ : cfg.σ = boundedSel) {s : State Validator BlockId Payload}
    (hab : UpperValid cfg.q cfg.xp s.floor s.disk) : KeepsProofs cfg s (Node.advance cfg s).1 := by
  have h := ((KeepsProofs.progress (cfg := cfg) (s.disk.topRound + 2) s).trans
    (KeepsProofs.decideStep hσ (UpperValid.progress _ hab))).trans (KeepsProofs.flushSyncs
      ((Node.decideStep cfg (Node.progress cfg (s.disk.topRound + 2) s).1).1.syncs.length + 1) _)
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) (Node.pass cfg s).1
  change KeepsProofs cfg s (Node.arm cfg (Node.pass cfg s).1).1
  rw [ha]
  exact h.trans (KeepsProofs.of_grows (Grows.refl _) rfl rfl)

omit [Fintype Validator] in
/-- **The passes keep the proofs**, from a disk valid at the row from the
floor up. -/
theorem KeepsProofs.quiesce (hσ : cfg.σ = boundedSel) : ∀ (n : ℕ)
    {s : State Validator BlockId Payload}, UpperValid cfg.q cfg.xp s.floor s.disk →
    KeepsProofs cfg s (Node.quiesce cfg n s).1
  | 0, s, _ => KeepsProofs.refl s
  | n + 1, s, hab => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · exact KeepsProofs.advance hσ hab
    · exact (KeepsProofs.advance hσ hab).trans (KeepsProofs.quiesce hσ n hab.advance)

omit [Fintype Validator] in
/-- **Settling keeps the proofs**, from a disk valid at the row from the
floor up. -/
theorem KeepsProofs.settle (hσ : cfg.σ = boundedSel) {s : State Validator BlockId Payload}
    (hab : UpperValid cfg.q cfg.xp s.floor s.disk) : KeepsProofs cfg s (Node.settle cfg s).1 :=
  KeepsProofs.quiesce hσ _ hab

omit [Fintype Validator] in
/-- **A proof's verdict is the decision of the store it builds**, scanning
to the last slot of its top round. -/
theorem decisionAt_of_verdictOn (hσ : cfg.σ = boundedSel) {k : ℕ}
    {L : List (BlockId × Block Validator BlockId Payload)} {d : Option BlockId}
    (hv : verdictOn cfg k L = some d) :
    decisionAt (S := cfg.slots) cfg.p boundedSel (proofStore cfg k L).toRecord
      (proofStore cfg k L).view (max k (decidable cfg (proofStore cfg k L).topRound - 1)) k =
      some d := by
  set st := proofStore cfg k L
  set N := max k (decidable cfg st.topRound - 1)
  have hv' : ((Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel st.toRecord st.view k
      N).head?).map Prod.snd = some d := by rw [← hσ]; exact hv
  obtain ⟨e', he', hed⟩ := Option.map_eq_some_iff.mp hv'
  have hmem := List.mem_of_mem_head? he'
  have he1 : e'.1 = k := by
    have hmap := tryDecide_fst (S := cfg.slots) (p := cfg.p) (σ := boundedSel) (U := st.toRecord)
      (V := st.view) (N := N) ((le_max_left k _).trans (Nat.le_succ _))
    obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
    rw [hxl, List.head?_cons, Option.some.injEq] at he'
    subst he'
    have := congrArg List.head? hmap
    rw [hxl] at this
    simp only [List.map_cons, List.head?_cons, List.length_cons, List.range'_succ,
      Option.some.injEq] at this
    exact this
  exact (decisionAt_of_mem_tryDecide (S := cfg.slots)
    ((Prod.ext he1.symm hed.symm : (k, d) = e') ▸ hmem)).2

omit [Fintype Validator] in
/-- **Deciding on a proof keeps the proofs**, the proof it adds deciding its
slot again, at a node that drops, with an injective hash and its disk under
its hash. -/
theorem KeepsProofs.decideOn (hσ : cfg.σ = boundedSel) (hdr : cfg.drops = true)
    (hid : Function.Injective cfg.idOf) {s : State Validator BlockId Payload}
    (hhash : ∀ x ∈ s.disk.ids, x = cfg.idOf (s.disk.full x)) {k : ℕ} {d : Option BlockId}
    {L : List (BlockId × Block Validator BlockId Payload)} (hv : verdictOn cfg k L = some d) :
    KeepsProofs cfg s (Node.decideOn cfg s k d L) := by
  set st := proofStore cfg k L with hst
  let s₁ : State Validator BlockId Payload :=
    { s with
      lo := k + 1
      decided := (k, d) :: s.decided
      proofs := (k, st.ids) :: s.proofs }
  set l := (hashed cfg L).mergeSort fun x y => decide (x.2.round ≤ y.2.round) with hl
  have e : Node.decideOn cfg s k d L = Node.absorb cfg (Node.release cfg s₁) l := rfl
  have h₁ : KeepsProofs cfg s₁ (Node.decideOn cfg s k d L) := by
    rw [e]; exact (KeepsProofs.release s₁).trans (KeepsProofs.absorb _ _)
  refine ⟨fun x hx => h₁.decided x (List.mem_cons_of_mem _ hx),
    fun e he => h₁.sub e (List.mem_cons_of_mem _ he), fun e he hn => ?_,
    fun e he x hx hxs => h₁.disk e (List.mem_cons_of_mem _ he) x hx hxs,
    fun h => h₁.paired fun x hx => ?_⟩
  swap
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self⟩
    · obtain ⟨P, hP⟩ := h x hx
      exact ⟨P, List.mem_cons_of_mem _ hP⟩
  by_cases hs : e ∈ s₁.proofs
  swap
  · exact h₁.fresh e he hs
  obtain rfl : e = (k, st.ids) := (List.mem_cons.mp hs).resolve_right hn
  -- the decision of the proof's store
  set N := max k (decidable cfg st.topRound - 1) with hN
  have hdec := decisionAt_of_verdictOn hσ hv
  -- the blocks of the proof, read under their hash
  obtain ⟨hspec, hkept⟩ := proofStore_spec (cfg := cfg) k L
  have hup := proofStore_upperValid (cfg := cfg) k L
  have hhL : ∀ e ∈ hashed cfg L, e.1 = cfg.idOf e.2 := fun e he =>
    of_decide_eq_true (List.mem_filter.mp he).2
  let g : BlockId → Block Validator BlockId Payload := fun x =>
    @dite _ (∃ b, cfg.idOf b = x) (Classical.propDecidable _) (fun h => h.choose)
      fun _ => st.full x
  have hg : ∀ x b, x = cfg.idOf b → g x = b := fun x b hx => by
    have h : ∃ b, cfg.idOf b = x := ⟨b, hx.symm⟩
    simp only [g]
    rw [dif_pos h]
    exact hid (h.choose_spec.trans hx)
  have hstg : ∀ x ∈ st.ids, st.full x = g x := fun x hx =>
    (hg x _ (hhL _ (hspec x hx).1)).symm
  -- every block of the proof enters the disk
  set s₂ := Node.release cfg s₁ with hs₂
  have hsf : (Node.decideOn cfg s k d L).disk =
      l.foldl (fun t e => acceptOn cfg s₂.floor t e.1 e.2) s₂.disk := by rw [e, absorb_disk]
  have hfl : cfg.slots.slotRound k ≤ s₂.floor := by
    rw [hs₂, release_floor]
    have : floorOf cfg s₁ = floorAt cfg (k + 1) := by
      unfold floorOf; rw [if_pos hdr]
    have := le_floorAt (cfg := cfg) (k + 1)
    simp only [Nat.add_sub_cancel] at this
    omega
  have hround : ∀ x, (st.full x).round = (st.blk x).round := fun x => (st.full_fields x).1
  have hgl : ∀ e ∈ l, g e.1 = e.2 := fun e he => hg e.1 e.2 (hhL e (List.mem_mergeSort.mp he))
  have hR₂ : ReadsAs g s₂.disk := fun x hx => by
    have hx' : x ∈ s.disk.ids := (release_disk (cfg := cfg) s₁).ids ▸ hx
    rw [(release_disk (cfg := cfg) s₁).full x]
    exact (hg x _ (hhash x hx')).symm
  have hsub : st.ids ⊆ (Node.decideOn cfg s k d L).disk.ids := by
    rw [hsf]
    refine acceptOn_holds hdr (g := g) (fun x hx hxF => ?_) l s₂.disk
      ((List.pairwise_mergeSort
        (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
        (fun h => by simpa using h)) hgl hR₂ fun x hx hxl => absurd ?_ hxl
    · rw [← hstg x hx] at hxF ⊢
      obtain ⟨hrefs, hv⟩ := hup x hx (by rw [← hround]; omega)
      refine ⟨hrefs, fun j hj => ?_,
        rowValid_congr (fun j hj => by rw [hstg j (hrefs hj)]; exact ⟨rfl, rfl, rfl⟩) hv⟩
      rw [← hstg j (hrefs hj)]
      exact hv.predecessor j hj
    · rw [← hstg x hx]
      exact List.mem_mergeSort.mpr (hspec x hx).1
  have hRf : ReadsAs g (Node.decideOn cfg s k d L).disk := by
    rw [hsf]; exact ReadsAs.foldl l hR₂ hgl
  have hfull : ∀ x ∈ st.ids, (Node.decideOn cfg s k d L).disk.full x = st.full x := fun x hx =>
    (hRf x (hsub hx)).trans (hstg x hx).symm
  have hfr : ∀ x ∈ st.ids, ((Node.decideOn cfg s k d L).disk.blk x).round = (st.blk x).round ∧
      ((Node.decideOn cfg s k d L).disk.blk x).creator = (st.blk x).creator := fun x hx => by
    rw [← ((Node.decideOn cfg s k d L).disk.full_fields x).1,
      ← ((Node.decideOn cfg s k d L).disk.full_fields x).2.1, hfull x hx,
      (st.full_fields x).1, (st.full_fields x).2.1]
    exact ⟨rfl, rfl⟩
  unfold ProofHolds
  dsimp only
  refine ⟨st.toRecord, st.view, N, d, h₁.decided _ List.mem_cons_self, le_max_left _ _, hdec,
    fun x hx => ?_, fun x hx => ?_⟩
  · have hxs : x ∈ st.ids := witnessAt_subset (S := cfg.slots) N k hx
    exact ⟨hxs, by rw [(hfr x hxs).1]; exact witnessAt_round (S := cfg.slots) N k x hx⟩
  · rw [(hfr x hx).1]
    have hlow := (hspec x hx).2
    rw [hround] at hlow
    refine ⟨hsub hx, by omega, ?_, fun hxk => ?_⟩
    · exact Nat.sub_le_sub_right (decidable_mono (by
        rw [st.topRound_eq]; exact Finset.le_sup (f := fun i => (st.blk i).round) hx)) 1 |>.trans
        (le_max_right _ _)
    obtain ⟨hrefs, hvx⟩ := hup x hx hxk
    rw [(hfr x hx).2, hfull x hx]
    refine ⟨hx, rfl, rfl, fun hlt => ?_, hrefs,
      rowValid_congr (fun j hj => by rw [hfull j (hrefs hj)]; exact ⟨rfl, rfl, rfl⟩) hvx⟩
    by_cases hk : st.kept[x]? = none
    · exact (st.full_of_kept_none hk).symm
    · have : (st.blk x).round + 1 = cfg.slots.slotRound k := hkept x hk
      omega

/-- **A step keeps the proofs**, at an injective hash, from the invariant
against blocks under their hash. -/
theorem KeepsProofs.step (hσ : cfg.σ = boundedSel) (hid : Function.Injective cfg.idOf)
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (hK : ∀ e ∈ K, e.1 = cfg.idOf e.2) (i : Input Validator BlockId Payload) :
    KeepsProofs cfg s (Node.step cfg s i).1 := by
  have hab := hi.above
  -- a state the step keeps the proofs to, with other syncs, top or timers, then settling
  have hset : ∀ s₀ s₁ : State Validator BlockId Payload, KeepsProofs cfg s s₀ →
      UpperValid cfg.q cfg.xp s₀.floor s₀.disk → s₁.disk = s₀.disk → s₁.floor = s₀.floor →
      s₁.decided = s₀.decided → s₁.proofs = s₀.proofs →
      KeepsProofs cfg s (Node.settle cfg s₁).1 := fun s₀ s₁ h h₀ hd hf hdc hp =>
    (h.trans (KeepsProofs.of_grows (by rw [hd]; exact Grows.refl _) hdc hp)).trans
      (KeepsProofs.settle hσ (by rw [hd, hf]; exact h₀))
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₂
        have hr₀ : cfg.genesis.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        have hp₀ : ∀ j ∈ cfg.genesis.refs, (s.disk.blk j).round + 1 = cfg.genesis.round :=
          fun j hj => absurd hj (Finset.notMem_empty j)
        exact hset (keep s _ _ h₂.1 hr₀ hp₀) _
          (KeepsProofs.of_grows (Grows.insert s.disk (hrefs := hr₀) (hpred := hp₀)) rfl rfl)
          (hab.insert (hrefs := hr₀) (hpred := hp₀) h₂.2) rfl rfl rfl rfl
      · exact KeepsProofs.refl s
    · exact KeepsProofs.refl s
  | deliver u id b =>
    simp only [Node.step]
    split
    · split
      · exact hset (Node.accept cfg s id b) _ (KeepsProofs.accept s id b)
          (hab.absorb [(id, b)]) rfl rfl rfl rfl
      · split
        · exact hset s _ (KeepsProofs.refl s) hab rfl rfl rfl rfl
        · exact KeepsProofs.refl s
    · exact KeepsProofs.refl s
  | stream u L =>
    simp only [Node.step]
    split
    · exact KeepsProofs.refl s
    · rename_i e he
      set s₀ := Node.takeIn cfg s e.2.1 (inHistory cfg e.2.1 L) with hs₀
      have h₁ : KeepsProofs cfg s s₀ ∧ UpperValid cfg.q cfg.xp s₀.floor s₀.disk := by
        rw [hs₀]
        unfold Node.takeIn
        split
        · exact ⟨(KeepsProofs.absorb s _).trans (KeepsProofs.tidy _), hab.absorb _⟩
        · exact ⟨KeepsProofs.refl s, hab⟩
      split
      · exact hset s₀ s₀ h₁.1 h₁.2 rfl rfl rfl rfl
      · exact hset s₀ _ h₁.1 h₁.2 rfl rfl rfl rfl
  | timer r =>
    simp only [Node.step]
    split <;> exact hset s _ (KeepsProofs.refl s) hab rfl rfl rfl rfl
  | syncRequest peer t fr ids => exact KeepsProofs.refl s
  | ask peer r => exact KeepsProofs.refl s
  | restart => exact hset s _ (KeepsProofs.refl s) hab rfl rfl rfl rfl
  | askProof peer k => exact KeepsProofs.refl s
  | proof u k L =>
    simp only [Node.step]
    split
    · rename_i hc
      split
      · rename_i d hv
        have hd : UpperValid cfg.q cfg.xp (Node.decideOn cfg s k d L).floor
            (Node.decideOn cfg s k d L).disk := by
          unfold Node.decideOn
          refine UpperValid.absorb ?_ _
          exact UpperValid.release hab
        exact hset (Node.decideOn cfg s k d L) _
          (KeepsProofs.decideOn hσ hc.1 hid (fun x hx => hK _ (hi.known x hx)) hv) hd
          rfl rfl rfl rfl
      · exact KeepsProofs.refl s
    · exact KeepsProofs.refl s

omit [Fintype Validator] in
/-- **The initial state keeps no proofs.** -/
theorem ProofsHold.init : ProofsHold cfg (State.init cfg) :=
  fun _ he => absurd he (by simp [State.init])

/-- **A run keeps proofs that decide their slots again**, at an injective
hash, from the invariant against blocks under their hash. -/
theorem ProofsHold.run (hσ : cfg.σ = boundedSel) (hid : Function.Injective cfg.idOf) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload}
      {K : Set (BlockId × Block Validator BlockId Payload)}
      {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
      (∀ e ∈ K, e.1 = cfg.idOf e.2) → ProofsHold cfg s → ProofsHold cfg (Node.run cfg s is).1
  | [], _, _, _, _, _, hp => hp
  | i :: is, s, K, B, hi, hK, hp => by
    obtain ⟨bs, -, hi₁⟩ := hi.step i
    refine ProofsHold.run hσ hid is hi₁ (fun e he => ?_)
      (hp.keeps (KeepsProofs.step hσ hid hi hK i))
    rcases he with (he | he) | he
    · exact hK e he
    · exact id_of_delivered (is := [i]) he
    · exact (hi₁.good e (List.mem_append_right _ he)).1

omit [Fintype Validator] in
/-- **A reply from kept proofs decides the slot as the node did**, from a disk
under its hash. -/
theorem verdictOn_reply (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (hl : 1 ≤ cfg.p.linkSize) (hcm : 1 ≤ cfg.p.commitThreshold)
    (hc : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold)
    {s : State Validator BlockId Payload} (hp : ProofsHold cfg s)
    (hhash : ∀ x ∈ s.disk.ids, x = cfg.idOf (s.disk.full x)) {k : ℕ}
    {L : List (BlockId × Block Validator BlockId Payload)} (hL : proofReply cfg s k = some L) :
    ∃ d, (k, d) ∈ s.decided ∧ verdictOn cfg k L = some d := by
  letI := cfg.slots
  unfold proofReply at hL
  obtain ⟨p, hfind, hpL⟩ := Option.map_eq_some_iff.mp hL
  have hpk : p.1 = k := by simpa using List.find?_some hfind
  obtain ⟨U, V, N, d, hdm, hkN, hdec, hwit, hP⟩ := hp p (List.mem_of_find?_eq_some hfind)
  rw [hpk] at hdm hkN hdec hwit hP
  refine ⟨d, hdm, ?_⟩
  have hround : ∀ i, (s.disk.full i).round = (s.disk.blk i).round := fun i =>
    (s.disk.full_fields i).1
  -- the reply holds the disk's blocks of the proof and those the commit ordered below the proof
  have hmemL : ∀ i b, (i, b) ∈ L → b = s.disk.full i ∧ i ∈ s.disk.ids ∧
      (i ∈ p.2 ∨ (s.disk.blk i).round + 1 < cfg.slots.slotRound k) := fun i b he => by
    rw [← hpL] at he
    obtain ⟨j, hj, hje⟩ := List.mem_map.mp (List.mem_mergeSort.mp he)
    simp only [Prod.mk.injEq] at hje
    obtain ⟨rfl, rfl⟩ := hje
    obtain ⟨hj, hjd⟩ := Finset.mem_filter.mp ((Finset.mem_sort _).mp hj)
    refine ⟨rfl, hjd, ?_⟩
    rcases Finset.mem_union.mp hj with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2
  have hinL : ∀ i ∈ p.2, (i, s.disk.full i) ∈ L := fun i hi => by
    rw [← hpL]
    exact List.mem_mergeSort.mpr (List.mem_map.mpr ⟨i, (Finset.mem_sort _).mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hi, (hP i hi).1⟩), rfl⟩)
  have hsort : L.Pairwise fun x y => x.2.round ≤ y.2.round := by
    rw [← hpL]
    exact (List.pairwise_mergeSort
      (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      (fun h => by simpa using h)
  -- a block the store holds is one of the proof
  obtain ⟨hspec, -⟩ := proofStore_spec (cfg := cfg) k L
  have hstP : ∀ i ∈ (proofStore cfg k L).ids, i ∈ p.2 ∧
      (proofStore cfg k L).full i = s.disk.full i := fun i hi => by
    obtain ⟨hiL, hr⟩ := hspec i hi
    obtain ⟨he, -, hor⟩ := hmemL i _ (List.mem_filter.mp hiL).1
    refine ⟨hor.resolve_right fun h => ?_, he⟩
    rw [he, hround] at hr
    omega
  -- the proof's blocks enter the store
  have hheld : p.2 ⊆ (proofStore cfg k L).ids :=
    proofStore_holds (g := s.disk.full) (F := p.2) (hsort.filter _)
      (fun e he => by
        obtain ⟨hb, -⟩ := hmemL e.1 e.2 (List.mem_filter.mp he).1
        exact hb.symm)
      (fun y hy => by
        obtain ⟨hyd, hyr, -, -⟩ := hP y hy
        exact ⟨List.mem_filter.mpr ⟨hinL y hy, by simpa using hhash y hyd⟩,
          by rw [hround]; exact hyr⟩)
      (fun y hy hyr => by
        rw [hround] at hyr
        obtain ⟨-, -, -, -, hrefs, hv⟩ := (hP y hy).2.2.2 hyr
        refine ⟨hrefs, fun j hj => ?_, hv⟩
        have := hv.predecessor j hj
        rwa [hround, hround] at this ⊢)
  refine verdictOn_of_decision hσ hw hl hcm hc hkN hdec (fun i hi hiR => ?_) (fun x hx => ?_)
    (fun i hi => ?_)
  · obtain ⟨hiP, he⟩ := hstP i hi
    rw [he, hround] at hiR ⊢
    obtain ⟨hV, hr, hcr, hb, -, -⟩ := (hP i hiP).2.2.2 hiR
    exact ⟨hV, hr, hcr.trans (s.disk.full_fields i).2.1.symm, hb⟩
  · obtain ⟨hxP, hxr⟩ := hwit x hx
    refine ⟨hheld hxP, ?_⟩
    rw [(hstP x (hheld hxP)).2, hround]
    exact hxr
  · obtain ⟨hiP, he⟩ := hstP i hi
    have := (hP i hiP).2.2.1
    rw [← ((proofStore cfg k L).full_fields i).1, he, hround]
    exact this

/-- **Two stores alike on what they hold**: the same identifiers, the same
blocks there, and the same kept references. -/
def Alike (st st' : Store Validator BlockId Payload) : Prop :=
  st.ids = st'.ids ∧ (∀ i ∈ st.ids, st.blk i = st'.blk i) ∧
    ∀ i : BlockId, st.kept[i]? = st'.kept[i]?

omit [Fintype Validator] in
/-- **A proof step keeps two stores alike.** -/
theorem proofStep_alike (k : ℕ) {st st' : Store Validator BlockId Payload} (h : Alike st st')
    (e : BlockId × Block Validator BlockId Payload) :
    Alike (proofStep cfg k st e) (proofStep cfg k st' e) := by
  obtain ⟨hids, hblk, hkept⟩ := h
  -- the checks read the store only at what it holds
  have hC : ∀ {a a' : Store Validator BlockId Payload}, a.ids = a'.ids →
      (∀ i ∈ a.ids, a.blk i = a'.blk i) → a.Checks cfg.q cfg.xp e.1 e.2 →
      a'.Checks cfg.q cfg.xp e.1 e.2 := by
    intro a a' hi hb ⟨hr, hp, hv⟩
    refine ⟨hi ▸ hr, fun j hj => (hb j (hr hj)) ▸ hp j hj, rowValid_of_eq (fun j hj => ?_) hv⟩
    by_cases hje : j = e.1
    · subst hje; simp
    · rw [Function.update_of_ne hje, Function.update_of_ne hje]; exact hb j (hr hj)
  have hCi : st.Checks cfg.q cfg.xp e.1 e.2 ↔ st'.Checks cfg.q cfg.xp e.1 e.2 :=
    ⟨hC hids hblk, hC hids.symm fun i hi => (hblk i (hids ▸ hi)).symm⟩
  unfold proofStep
  by_cases hn : e.1 ∉ st.ids
  · have hn' : e.1 ∉ st'.ids := hids ▸ hn
    rw [dif_pos hn, dif_pos hn']
    split
    · refine ⟨by rw [Store.base_ids, Store.base_ids, hids], fun i hi => ?_, fun i => ?_⟩
      · rw [Store.base_blk, Store.base_blk]
        split
        · rfl
        · rename_i hie
          rw [Store.base_ids] at hi
          exact hblk i ((Finset.mem_insert.mp hi).resolve_left hie)
      · change (st.kept.insert e.1 e.2.refs)[i]? = (st'.kept.insert e.1 e.2.refs)[i]?
        rw [Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_insert, hkept i]
    · by_cases hc : cfg.slots.slotRound k ≤ e.2.round ∧ st.Checks cfg.q cfg.xp e.1 e.2
      · have hc' : cfg.slots.slotRound k ≤ e.2.round ∧ st'.Checks cfg.q cfg.xp e.1 e.2 :=
          ⟨hc.1, hCi.mp hc.2⟩
        rw [dif_pos hc, dif_pos hc']
        refine ⟨by rw [Store.insert_ids, Store.insert_ids, hids], fun i hi => ?_, fun i => hkept i⟩
        rw [Store.insert_blk, Store.insert_blk]
        split
        · rfl
        · rename_i hie
          rw [Store.insert_ids] at hi
          exact hblk i ((Finset.mem_insert.mp hi).resolve_left hie)
      · have hc' : ¬ (cfg.slots.slotRound k ≤ e.2.round ∧ st'.Checks cfg.q cfg.xp e.1 e.2) :=
          fun h => hc ⟨h.1, hCi.mpr h.2⟩
        rw [dif_neg hc, dif_neg hc']
        exact ⟨hids, hblk, hkept⟩
  · have hn' : ¬ e.1 ∉ st'.ids := hids ▸ hn
    rw [dif_neg hn, dif_neg hn']
    exact ⟨hids, hblk, hkept⟩

omit [Fintype Validator] in
/-- **The stores a proof builds at two nodes are alike.** -/
theorem proofStore_alike (u v : Validator) (k : ℕ)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Alike (proofStore (cfg.at u) k L) (proofStore (cfg.at v) k L) := by
  have hfold : ∀ (l : List (BlockId × Block Validator BlockId Payload))
      (st st' : Store Validator BlockId Payload), Alike st st' →
      Alike (l.foldl (proofStep (cfg.at v) k) st) (l.foldl (proofStep (cfg.at v) k) st') := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons e l ih => exact fun st st' h => ih _ _ (proofStep_alike k h e)
  exact hfold (hashed (cfg.at v) L) (Store.empty (cfg.at u).genesis)
    (Store.empty (cfg.at v).genesis)
    ⟨rfl, fun i hi => absurd hi (Finset.notMem_empty i), fun i => rfl⟩

omit [Fintype Validator] in
/-- **A proof gives every node the same verdict.** -/
theorem verdictOn_at (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (hl : 1 ≤ cfg.p.linkSize) (hcm : 1 ≤ cfg.p.commitThreshold)
    (hc : cfg.p.voteIsCert = false → 1 ≤ cfg.p.certThreshold) {u v : Validator} {k : ℕ}
    {L : List (BlockId × Block Validator BlockId Payload)} {d : Option BlockId}
    (hv : verdictOn (cfg.at v) k L = some d) : verdictOn (cfg.at u) k L = some d := by
  obtain ⟨hids, hblk, hkept⟩ := proofStore_alike (cfg := cfg) u v k L
  set a := proofStore (cfg.at u) k L
  set b := proofStore (cfg.at v) k L
  have hfull : ∀ i ∈ a.ids, a.full i = b.full i := fun i hi => by
    unfold Store.full; rw [hkept i, hblk i hi]
  have hround : ∀ i, (b.full i).round = (b.blk i).round := fun i => (b.full_fields i).1
  have hcr : ∀ i, (b.full i).creator = (b.blk i).creator := fun i => (b.full_fields i).2.1
  obtain ⟨-, hkb⟩ := proofStore_spec (cfg := cfg.at v) k L
  refine verdictOn_of_decision (cfg := cfg.at u) hσ hw hl hcm hc (U := b.toRecord) (V := b.view)
    (le_max_left _ _) (decisionAt_of_verdictOn (cfg := cfg.at v) hσ hv) (fun i hi hik => ?_)
    (fun x hx => ?_) (fun i hi => ?_)
  · rw [hfull i hi] at hik ⊢
    refine ⟨show i ∈ b.ids from hids ▸ hi, (hround i).symm, (hcr i).symm, fun hlt => ?_⟩
    change b.blk i = b.full i
    by_cases hk : b.kept[i]? = none
    · exact (b.full_of_kept_none hk).symm
    · have h₁ : (b.blk i).round + 1 = cfg.slots.slotRound k := hkb i hk
      have h₂ : cfg.slots.slotRound k < (b.blk i).round := by rw [← hround]; exact hlt
      omega
  · have hxb : x ∈ b.ids := witnessAt_subset (S := cfg.slots) _ k hx
    refine ⟨hids ▸ hxb, ?_⟩
    rw [hfull x (hids ▸ hxb), hround]
    exact witnessAt_round (S := cfg.slots) _ k x hx
  · rw [hblk i hi]
    exact Nat.sub_le_sub_right (decidable_mono (by
      rw [b.topRound_eq]; exact Finset.le_sup (f := fun i => (b.blk i).round) (hids ▸ hi))) 1
      |>.trans (le_max_right _ _)

end Node

end LeanDag
