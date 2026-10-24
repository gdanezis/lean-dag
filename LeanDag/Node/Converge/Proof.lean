import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.SyncTrace
/-!
# Syncing makes the honest nodes converge — proof

Let honest `u` end with its own block `(j, b)` at its top, so every block
`u` made lies at or below `b`'s round, and suppose honest `v` never holds
`j`. Then `u` broadcast `(j, b)`, and `v`, given it, has had a sync for it
with `u` since (`sync_made`, `sync_stays`). Take the sync's last request,
at `R` (`last_ask`). `u` answered it with the stream of `j`'s history,
which `v` received and which led to no request. So the piece gained `v`
no block, and each reference that `v` lacks of `b` or of the piece's part
in `j`'s history was asked for by name at `R` (`step_stream_stuck`). A
block of that part that `v` lacks, at the least round, is not ready, so
it references a block `v` lacks. That block was asked for, so the stream
holds it, in the part, one round lower: a contradiction. So `v` holds `j`,
and `j`'s history with it.
-/

namespace LeanDag

namespace Node

namespace Converge

theorem converges : Converges := by
  intro Validator BlockId Payload _ _ _ cfg H tr hdel htime hinj hev u hu j hown y hy v hv
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
  obtain ⟨hstuck, hasked⟩ := step_stream_stuck (syncsOn_before v R'') heA hno hheld hdet
  -- a block of the part in `j`'s history that `v` lacks, at the least round
  set P := inHistory (cfg.at v) (j, b) Lu with hP
  have hjP : (j, b) ∈ P := by
    obtain ⟨e, he, hej⟩ := List.mem_map.mp hjLu
    have hjb : e = (j, b) := Prod.ext hej (by rw [hLmap e he, hej, hjbu])
    exact (mem_inHistory Lu).mpr ⟨hjb ▸ he, hid, by change b.creator ≠ v; rw [hc]; exact huv,
      found_self Lu j hjLu⟩
  classical
  have hex : ∃ r, ∃ x ∈ P, x.1 ∉ s.disk.ids ∧ x.2.round = r := ⟨_, (j, b), hjP, hlack R'', rfl⟩
  obtain ⟨x, hxP, hxn, hxr⟩ := Nat.find_spec hex
  have hmin : ∀ x' ∈ P, x'.1 ∉ s.disk.ids → Nat.find hex ≤ x'.2.round :=
    fun x' hx' hn => Nat.find_min' hex ⟨x', hx', hn, rfl⟩
  obtain ⟨hxLu, -, -, hxf⟩ := (mem_inHistory Lu).mp hxP
  obtain ⟨hxst, hxb⟩ := mem_streamOf st j hxLu
  obtain ⟨xi, xb⟩ := x
  change xb = st.blk xi at hxb
  subst hxb
  have hxi : xi ∈ Lu.map Prod.fst := List.mem_map_of_mem hxLu
  -- it is not ready, so it references a block `v` lacks
  have hnr : readyOn (cfg.at v) s.disk (xi, st.blk xi) = false := (hstuck _ hxP).resolve_left hxn
  have hRu := reads_before hinj hu R'
  obtain ⟨y', hy', hyn⟩ : ∃ y' ∈ (st.blk xi).refs, y' ∉ s.disk.ids := by
    by_contra hall'
    push Not at hall'
    have hvalid : (∀ k ∈ (st.blk xi).refs, (gT cfg H tr k).round + 1 = (st.blk xi).round) ∧
        rowValid (cfg.at v).q (cfg.at v).xp (gT cfg H tr) (st.blk xi) := by
      refine ⟨fun k hk => ?_, rowValid_congr (fun k hk => ?_) ((inv_before R' u).valid xi hxst)⟩
      · rw [← hRu k (st.complete xi hxst k hk)]
        exact st.pred xi hxst k hk
      · rw [hRu k (st.complete xi hxst k hk)]
        exact ⟨rfl, rfl, rfl⟩
    have := ready_of_refs hvalid (reads_before hinj hv R'') (fun k hk => hall' k hk) hxn
    rw [hnr] at this
    cases this
  -- that block was asked for by name, so the stream holds it, one round lower
  have hyids : y' ∈ ids := hAids y' (hasked _ (List.mem_cons_of_mem _ hxP) y' hy' hyn)
  have hyst : y' ∈ st.ids := st.complete xi hxst y' hy'
  have hyLu : y' ∈ Lu.map Prod.fst := streamOf_closed st j hxi hy' hyst (Or.inr (Or.inl hyids))
  have hyLu' : (y', st.blk y') ∈ Lu := by
    obtain ⟨e, he, hey⟩ := List.mem_map.mp hyLu
    have : e = (y', st.blk y') := Prod.ext hey (by rw [hLmap e he, hey])
    exact this ▸ he
  have hyP : (y', st.blk y') ∈ P := by
    refine (mem_inHistory Lu).mpr ⟨hyLu', id_of_knownIn (stored_known hu hyst), fun hcv => ?_,
      found_closed Lu j hxf ((pieceRefs_of_map Lu hLmap hxi).mpr hy') hyLu⟩
    exact hyn (own_stored (own_known (v := v) htime hu hv (show R' ≤ R'' by omega)
      ((inv_before R' u).known y' hyst) hcv)).1
  have h₁ : Nat.find hex ≤ (st.blk y').round := hmin _ hyP hyn
  have h₂ : (st.blk y').round + 1 = (st.blk xi).round := st.pred xi hxst y' hy'
  have h₃ : (st.blk xi).round = Nat.find hex := hxr
  omega

theorem holds : Statement := converges

end Converge

end Node

end LeanDag
