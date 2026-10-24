import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.SyncTrace
/-!
# Syncing makes the honest nodes converge — proof

Let honest `u` end with its own block `(j, b)` at its top, so every block
`u` made lies at or below `b`'s round, and suppose honest `v` never holds
`j`. Then `u` broadcast `(j, b)`, and `v`, given it, has had a sync for it
with `u` since (`sync_made`, `sync_stays`). Take the sync's last request,
at `R` (`last_ask`). `u` answered it with the stream of `j`'s history,
which `v` received and which led to no request. So `v` did not take the
piece's part in `j`'s history in, which fits the cap, and each reference of
`b` or of that part that neither `v` nor the part holds was asked for by
name at `R` (`step_stream_stuck`). The part is valid and in order of
round, so if each of its references were held or in it, it would have
been taken in whole and `j` with it (`foldl_all`). So some reference is
neither; it was asked for, so the stream holds it, and so does the part:
a contradiction. So `v` holds `j`, and `j`'s history with it.
-/

namespace LeanDag

namespace Node

namespace Converge

theorem converges : Converges := by
  intro Validator BlockId Payload _ _ _ cfg H tr hdel htime hinj hev hfit u hu j hown y hy v hv
  have hiu := inv_before (cfg := cfg) (tr := tr) tr.length u
  obtain ⟨hjd, hjB⟩ := hiu.own j hown
  set b := (stateBefore cfg tr tr.length u).disk.blk j with hb
  have hpers : (j, b) ∈ persists (runOf cfg tr u).2 := hjB
  -- every block `u` made lies at or below `b`'s round
  have htop : ∀ x ∈ persists (runOf cfg tr u).2, x.2.round ≤ b.round := by
    rcases hiu.rounds with ⟨-, hB⟩ | ⟨r, hr, hR⟩
    · rw [hB] at hjB; exact absurd hjB List.not_mem_nil
    · obtain ⟨j', hj', -, hjr, -⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := u) tr.length r hr
      rw [hown] at hj'
      obtain rfl := Option.some.inj hj'
      intro x hx
      rw [hjr]
      exact hR.2 x hx
  obtain ⟨hid, hc, -, -⟩ := hiu.good _ hjB
  change j = cfg.idOf b at hid
  change b.creator = u at hc
  suffices hjv : j ∈ (stateBefore cfg tr tr.length v).disk.ids by
    rw [hist_eq hinj hu hjd] at hy
    exact hist_sub hinj hv hjv hy
  by_cases huv : u = v
  · subst huv; exact hjd
  by_contra hlackL
  have hlack : ∀ τ, j ∉ (stateBefore cfg tr τ v).disk.ids := fun τ h => by
    rcases le_total τ tr.length with hτ | hτ
    · exact hlackL ((grows_before (cfg := cfg) v hτ).1 h)
    · exact hlackL (by rwa [stateBefore_of_le hτ] at h)
  have hval : 0 < b.round → cfg.q ≤ b.refs.card := fun hpos =>
    ((hiu.valid j hjd).quorum hpos).trans Finset.card_image_le
  -- `u` broadcast `(j, b)`; `v` was given it, and has had a sync for it since
  obtain ⟨p, -, hpu, hpp⟩ := mem_persists_before (cfg := cfg) u tr.length hjB
  obtain ⟨inpp, hp⟩ := event_of_map hpu
  obtain ⟨k, -, hk⟩ := hdel p u inpp hp hu (v, .deliver u j b)
    ⟨.broadcast j b, mem_broadcasts.mp (broadcasts_of_persists hpp), Ne.symm huv, rfl⟩ hv
  have hkL : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
  have hfin := sync_stays htime hev hu hv htop hlack
    (sync_made htime hev hu hv huv hpers htop hlack hid hc hval hk) tr.length (by omega)
  -- its last request, answered by `u` with the stream of `j`'s history
  obtain ⟨R, hRL, fr, ids, ⟨inpR, hR⟩, hreq, hnoR, hall⟩ := last_ask tr.length hfin
  obtain ⟨A₁, he₁, -⟩ := hall (R + 1) (by omega) (by omega)
  have hkn : (j, b) ∈ knownBefore cfg tr (R + 1) v := (inv_before (R + 1) v).pend _ he₁
  obtain ⟨R', hRR', hR'⟩ := hdel R v inpR hR hv (u, .syncRequest v j fr ids)
    ⟨.sync u j fr ids, hreq, rfl, rfl⟩ hu
  obtain ⟨hju, hjbu⟩ :=
    own_stored (own_known (v := u) htime hv hu (show R + 1 ≤ R' by omega) hkn hc)
  set st := (stateBefore cfg tr R' u).disk with hst
  set Lu := streamOf st j fr ids with hLu
  have hLmap : ∀ e ∈ Lu, e.2 = st.blk e.1 := fun e he => (mem_streamOf st j he).2
  have hjLu : j ∈ Lu.map Prod.fst := mem_streamOf_self st j hju
  have hout : Output.stream v Lu ∈ outputsAt cfg tr R' := by
    rw [outputsAt_eq hR']
    change Output.stream v Lu ∈
      (if v ∈ (stateBefore cfg tr R' u).detected ∨ Lu.isEmpty then [] else [Output.stream v Lu])
    rw [if_neg]
    · exact List.mem_singleton_self _
    · rintro (h | h)
      · exact not_detected htime hev hv hu R' h
      · rw [List.isEmpty_iff] at h
        rw [h] at hjLu
        exact absurd hjLu List.not_mem_nil
  obtain ⟨R'', hR'R'', hR''⟩ :=
    hdel R' u _ hR' hu (v, .stream u Lu) ⟨.stream v Lu, hout, rfl, rfl⟩ hv
  have hR''L : R'' < tr.length := (List.getElem?_eq_some_iff.mp hR'').1
  -- the stream led `v` to no request
  obtain ⟨A, heA, hAids⟩ := hall R'' (by omega) hR''L.le
  set s := stateBefore cfg tr R'' v with hs
  have hno : ∀ fr' ids', Output.sync u j fr' ids' ∉ (Node.step (cfg.at v) s (.stream u Lu)).2 :=
    fun fr' ids' h => hnoR R'' (by omega) hR''L _ hR'' fr' ids' (by rw [outputsAt_eq hR'']; exact h)
  have hheld : j ∉ (Node.step (cfg.at v) s (.stream u Lu)).1.disk.ids := by
    rw [← step_before hR'']; exact hlack _
  have hdet : u ∉ (Node.step (cfg.at v) s (.stream u Lu)).1.detected := by
    rw [← step_before hR'']; exact not_detected htime hev hu hv _
  obtain ⟨hadm, hasked⟩ := step_stream_stuck (syncsOn_before v R'') heA hno hheld hdet
  -- the piece's part in `j`'s history, which fits the cap
  set P := inHistory (cfg.at v) (j, b) Lu with hP
  set Lh := hashed (cfg.at v) Lu with hLh
  have hLhmap : ∀ e ∈ Lh, e.2 = st.blk e.1 := fun e he => hLmap e ((mem_hashed Lu).mp he).1
  have hjLh : (j, b) ∈ Lh := by
    obtain ⟨e, he, hej⟩ := List.mem_map.mp hjLu
    have hjb : e = (j, b) := Prod.ext hej (by rw [hLmap e he, hej, hjbu])
    exact (mem_hashed Lu).mpr ⟨hjb ▸ he, hid⟩
  have hjP : (j, b) ∈ P :=
    (mem_inHistory Lu).mpr ⟨hjLh, by change b.creator ≠ v; rw [hc]; exact huv,
      found_self Lh j (List.mem_map_of_mem (f := Prod.fst) hjLh)⟩
  have hcap : P.length ≤ (cfg.at v).cap := by
    have h₁ : P.length ≤ Lu.length := by
      rw [hP]; unfold inHistory hashed; rw [List.length_mergeSort]
      exact (List.length_filter_le _ _).trans (List.length_filter_le _ _)
    exact h₁.trans (hfit R' u _ hR' hu v Lu hout hv)
  have hRu := reads_before hinj hu R'
  have hPLu : ∀ e ∈ P, e ∈ Lu ∧ e.1 ∈ st.ids ∧ e.2 = st.blk e.1 := fun e he => by
    have heL := ((mem_hashed Lu).mp ((mem_inHistory Lu).mp he).1).1
    exact ⟨heL, (mem_streamOf st j heL).1, hLmap e heL⟩
  -- some block of the part references a block neither `v` nor the part holds
  obtain ⟨x, hxP, y', hy', hyn, hyP⟩ :
      ∃ x ∈ P, ∃ y' ∈ x.2.refs, y' ∉ s.disk.ids ∧ y' ∉ P.map Prod.fst := by
    by_contra hall'
    push Not at hall'
    refine hadm ⟨hcap, ?_⟩
    rw [absorb_disk]
    refine foldl_all (g := gT cfg H tr) P s.disk ?_ (reads_before hinj hv R'') (fun e he => ?_)
      (fun e he => ?_) (fun e he y hy => ?_) (j, b) hjP
    · rw [hP]; unfold inHistory
      exact (List.pairwise_mergeSort
        (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
        (fun h => by simpa using h)
    · obtain ⟨-, hest, heb⟩ := hPLu e he
      rw [heb, hRu _ hest]
    · obtain ⟨-, hest, heb⟩ := hPLu e he
      rw [heb]
      refine ⟨fun k hk => ?_, rowValid_congr (fun k hk => ?_) ((inv_before R' u).valid _ hest)⟩
      · rw [← hRu k (st.complete _ hest k hk)]
        exact st.pred _ hest k hk
      · rw [hRu k (st.complete _ hest k hk)]
        exact ⟨rfl, rfl, rfl⟩
    · by_cases hyd : y ∈ s.disk.ids
      · exact Or.inl hyd
      · exact Or.inr (hall' e he y hy hyd)
  obtain ⟨hxLu, hxst, hxb⟩ := hPLu x hxP
  have hxf := ((mem_inHistory Lu).mp hxP).2.2
  have hxLh := ((mem_inHistory Lu).mp hxP).1
  obtain ⟨xi, xb⟩ := x
  change xb = st.blk xi at hxb
  subst hxb
  have hxi : xi ∈ Lu.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hxLu
  have hxi' : xi ∈ Lh.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) hxLh
  -- that block was asked for by name, so the stream holds it, and so does the part
  have hyids : y' ∈ ids := hAids y' (hasked _ (List.mem_cons_of_mem _ hxP) y' hy' hyn (by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hyP (h ▸ List.mem_map_of_mem (f := Prod.fst) hjP)
    · exact hyP h))
  have hyst : y' ∈ st.ids := st.complete xi hxst y' hy'
  have hyLu : y' ∈ Lu.map Prod.fst := streamOf_closed st j hxi hy' hyst (Or.inr (Or.inl hyids))
  have hyLu' : (y', st.blk y') ∈ Lu := by
    obtain ⟨e, he, hey⟩ := List.mem_map.mp hyLu
    have : e = (y', st.blk y') := Prod.ext hey (by rw [hLmap e he, hey])
    exact this ▸ he
  have hyLh : (y', st.blk y') ∈ Lh :=
    (mem_hashed Lu).mpr ⟨hyLu', id_of_knownIn (stored_known hu hyst)⟩
  have hyP' : (y', st.blk y') ∈ P := by
    refine (mem_inHistory Lu).mpr ⟨hyLh, fun hcv => ?_,
      found_closed Lh j hxf ((pieceRefs_of_map Lh hLhmap hxi').mpr hy')
        (List.mem_map_of_mem (f := Prod.fst) hyLh)⟩
    exact hyn (own_stored (own_known (v := v) htime hu hv (show R' ≤ R'' by omega)
      ((inv_before R' u).known y' hyst) hcv)).1
  exact hyP (List.mem_map_of_mem (f := Prod.fst) hyP')

theorem holds : Statement := converges

end Converge

end Node

end LeanDag
