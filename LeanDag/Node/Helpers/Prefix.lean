import LeanDag.Node.Helpers.Wave
/-!
# The first events of a trace

`docs/validator.md` §13.12. The first `N` events of a trace are a trace
whose states before event `i ≤ N` and outputs at event `i < N` are the
trace's (`stateBefore_take`, `outputsAt_take`). If every event at or
before `t₁'` is among them, the timed assumptions up to `t₁' ≤ t₁` hold of
the prefix, and so do the assumptions on authentication and hashes.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem take_getElem? {N i : ℕ} (h : i < N) : (tr.take N)[i]? = tr[i]? := by
  rw [List.getElem?_take, if_pos h]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem take_getElem?_some {N i : ℕ} {x : Validator × Input Validator BlockId Payload}
    (h : (tr.take N)[i]? = some x) : i < N ∧ tr[i]? = some x := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

omit [Fintype Validator] [LinearOrder BlockId] in
theorem inputsBefore_take {N i : ℕ} (h : i ≤ N) (v : Validator) :
    inputsBefore (tr.take N) i v = inputsBefore tr i v := by
  unfold inputsBefore
  rw [List.take_take, min_eq_left h]

theorem stateBefore_take {N i : ℕ} (h : i ≤ N) (v : Validator) :
    stateBefore cfg (tr.take N) i v = stateBefore cfg tr i v := by
  unfold stateBefore; rw [inputsBefore_take h]

theorem outputsAt_take {N i : ℕ} (h : i < N) :
    outputsAt cfg (tr.take N) i = outputsAt cfg tr i := by
  unfold outputsAt
  rw [take_getElem? h]
  split
  · rw [stateBefore_take h.le]
  · rfl

/-- **The decisions a prefix's run outputs** are a prefix of the trace's. -/
theorem decisionsOf_take (N : ℕ) (v : Validator) :
    decisionsOf cfg (tr.take N) v <+: decisionsOf cfg tr v := by
  unfold decisionsOf runOf
  rw [inputsBefore_take (by simp)]
  obtain ⟨l, hl⟩ := inputsBefore_prefix (tr := tr) v (show (tr.take N).length ≤ tr.length by simp)
  rw [hl, run_append, commitsOf_append]
  exact List.prefix_append _ _

/-! ## Time -/

section Time

variable {time : ℕ → ℕ}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem timeMono_take (hmono : Live.TimeMono tr time) (N : ℕ) :
    Live.TimeMono (tr.take N) time := fun i j hij hj =>
  hmono i j hij (lt_of_lt_of_le hj (by simp))

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **The events by `t` of a prefix holding them all** are the trace's. -/
theorem eventsBy_take {N t : ℕ} (hN : ∀ i < tr.length, time i ≤ t → i < N) :
    eventsBy (tr.take N) time t = eventsBy tr time t := by
  unfold eventsBy
  rw [List.length_take]
  have key : ∀ L, min N tr.length ≤ L → L ≤ tr.length →
      ((List.range L).filter fun i => decide (time i ≤ t)).length =
        ((List.range (min N tr.length)).filter fun i => decide (time i ≤ t)).length := by
    intro L hL hLt
    induction L, hL using Nat.le_induction with
    | base => rfl
    | succ L hL ih =>
      rw [List.range_succ, List.filter_append, List.length_append, ih (by omega)]
      have : ¬ time L ≤ t := fun h => by have := hN L (by omega) h; omega
      simp [this]
  exact (key tr.length (min_le_right _ _) le_rfl).symm

theorem stateAt_take {N t : ℕ} (hN : ∀ i < tr.length, time i ≤ t → i < N) (v : Validator) :
    stateAt cfg (tr.take N) time v t = stateAt cfg tr time v t := by
  unfold stateAt
  rw [eventsBy_take hN, stateBefore_take]
  unfold eventsBy
  have := (List.filter_sublist (p := fun i => decide (time i ≤ t))
    (l := List.range tr.length)).length_le
  simp only [List.length_range] at this
  by_contra hlt
  push Not at hlt
  have h₁ : ∀ i ∈ (List.range tr.length).filter fun i => decide (time i ≤ t), i < N := by
    intro i hi
    obtain ⟨hi, hit⟩ := List.mem_filter.mp hi
    exact hN i (List.mem_range.mp hi) (of_decide_eq_true hit)
  have h₂ : ((List.range tr.length).filter fun i => decide (time i ≤ t)).Nodup :=
    (List.nodup_range).filter _
  have h₃ := List.Nodup.length_le_card (α := Fin N)
    (l := ((List.range tr.length).filter fun i => decide (time i ≤ t)).attach.map
      fun i => ⟨i.1, h₁ i.1 i.2⟩) (by
      rw [List.nodup_map_iff_inj_on (List.nodup_attach.mpr h₂)]
      intro a _ b _ hab
      exact Subtype.ext (Fin.mk.inj_iff.mp hab))
  simp only [List.length_map, List.length_attach, Fintype.card_fin] at h₃
  omega

/-! ## The assumptions on a prefix -/

variable {H T : Finset Validator} {gst Δ Δₛ t₁ t₁' N : ℕ}

theorem deliveredWithin_take (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (ht : t₁' ≤ t₁) (hN : ∀ i < tr.length, time i ≤ t₁' → i < N) :
    Live.DeliveredWithin cfg T (tr.take N) time gst Δ t₁' := by
  intro i u inp hi hu m hm hmT hle
  obtain ⟨hiN, hi'⟩ := take_getElem?_some hi
  rw [outputsAt_take hiN] at hm
  obtain ⟨j, hij, hj, htj⟩ := hdel i u inp hi' hu m hm hmT (by omega)
  have hjN : j < N := hN j (List.getElem?_eq_some_iff.mp hj).1 (by omega)
  exact ⟨j, hij, by rw [take_getElem? hjN]; exact hj, htj⟩

theorem timersOnTime_take (htimer : Live.TimersOnTime cfg T tr time t₁) (ht : t₁' ≤ t₁)
    (hN : ∀ i < tr.length, time i ≤ t₁' → i < N) :
    Live.TimersOnTime cfg T (tr.take N) time t₁' := by
  refine ⟨fun i u inp hi hu r a hs hle => ?_, fun j u r hj hu => ?_⟩
  · obtain ⟨hiN, hi'⟩ := take_getElem?_some hi
    rw [outputsAt_take hiN] at hs
    obtain ⟨j, hij, hj, htj⟩ := htimer.1 i u inp hi' hu r a hs (by omega)
    have hjN : j < N := hN j (List.getElem?_eq_some_iff.mp hj).1 (by omega)
    exact ⟨j, hij, by rw [take_getElem? hjN]; exact hj, htj⟩
  · obtain ⟨hjN, hj'⟩ := take_getElem?_some hj
    obtain ⟨i, hij, a, hiu, hs, hta, hno⟩ := htimer.2 j u r hj' hu
    refine ⟨i, hij, a, by rw [take_getElem? (by omega)]; exact hiu,
      by rw [outputsAt_take (by omega)]; exact hs, hta, fun k hik hkj => ?_⟩
    rw [take_getElem? (by omega)]; exact hno k hik hkj

theorem knownIn_take (N : ℕ) : Converge.knownIn cfg H (tr.take N) ⊆ Converge.knownIn cfg H tr := by
  rintro x (⟨j, v, inp, hj, hv, hd⟩ | ⟨i, u, hu, huH, hp⟩)
  · exact Or.inl ⟨j, v, inp, (take_getElem?_some hj).2, hv, hd⟩
  · rcases hi : (tr.take N)[i]? with _ | ⟨w, inp⟩
    · rw [hi] at hu; cases hu
    · have hiN := (take_getElem?_some hi).1
      refine Or.inr ⟨i, u, by rw [← take_getElem? hiN]; exact hu, huH, ?_⟩
      rw [← outputsAt_take hiN]; exact hp

theorem hashInjective_take (hinj : Converge.HashInjective cfg H tr) (N : ℕ) :
    Converge.HashInjective cfg H (tr.take N) := fun x hx y hy =>
  hinj x (knownIn_take N hx) y (knownIn_take N hy)

theorem timelyAuthentic_take (htime : Converge.TimelyAuthentic cfg H tr) (N : ℕ) :
    Converge.TimelyAuthentic cfg H (tr.take N) := by
  intro j v inp hj hv x hx hc
  obtain ⟨hjN, hj'⟩ := take_getElem?_some hj
  obtain ⟨i, hij, hiu, hib⟩ := htime j v inp hj' hv x hx hc
  exact ⟨i, hij, by rw [take_getElem? (by omega)]; exact hiu,
    by rw [outputsAt_take (by omega)]; exact hib⟩

theorem timelyCerts_take (hcert : Boot.TimelyCerts cfg H tr) (N : ℕ) :
    Boot.TimelyCerts cfg H (tr.take N) := by
  intro j v p c ds hj hv u hu huH
  obtain ⟨hjN, hj'⟩ := take_getElem?_some hj
  obtain ⟨i, hij, hiu, hip⟩ := hcert j v p c ds hj' hv u hu huH
  exact ⟨i, hij, by rw [take_getElem? (by omega)]; exact hiu,
    by rw [outputsAt_take (by omega)]; exact hip⟩

theorem chainInjective_take (hchain : Boot.ChainInjective cfg H tr) (N : ℕ) :
    Boot.ChainInjective cfg H (tr.take N) := by
  intro j v p c ds hj hv ds' hds pre hpre u hu k hk hh
  obtain ⟨-, hj'⟩ := take_getElem?_some hj
  obtain ⟨l, hl⟩ := decisionsOf_take (cfg := cfg) (tr := tr) N u
  have hku : k ≤ (decisionsOf cfg tr u).length := by
    rw [← hl, List.length_append]; omega
  have htk : (decisionsOf cfg (tr.take N) u).take k = (decisionsOf cfg tr u).take k := by
    rw [← hl, List.take_append_of_le_length hk]
  rw [htk] at hh ⊢
  exact hchain j v p c ds hj' hv ds' hds pre (hpre.trans (decisionsOf_take N v)) u hu k hku hh

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem startedBy_take (hstart : Live.StartedBy T tr time gst)
    (hN : ∀ i < tr.length, time i ≤ gst → i < N) : Live.StartedBy T (tr.take N) time gst := by
  intro v hv
  obtain ⟨i, hi, hti⟩ := hstart v hv
  have hiN : i < N := hN i (List.getElem?_eq_some_iff.mp hi).1 hti
  exact ⟨i, by rw [take_getElem? hiN]; exact hi, hti⟩

theorem exposedFrom_take {s : ℕ} (hex : Live.ExposedFrom cfg T tr time s) (N : ℕ) :
    Live.ExposedFrom cfg T (tr.take N) time s := by
  obtain ⟨X, hX⟩ := hex
  refine ⟨X, fun v hv k hk hsk => ?_⟩
  have hkN : k < N := by simp at hk; omega
  rw [stateBefore_take hkN]
  exact hX v hv k (by simp at hk; omega) hsk

/-! ## What a prefix shows by a time it holds -/

theorem topAt_take {t : ℕ} (hN : ∀ i < tr.length, time i ≤ t → i < N) (v : Validator) :
    topAt cfg (tr.take N) time v t = topAt cfg tr time v t := by
  unfold topAt; rw [stateAt_take hN]

theorem decisionsBy_take {t : ℕ} (hN : ∀ i < tr.length, time i ≤ t → i < N) (v : Validator) :
    decisionsBy cfg (tr.take N) time v t = decisionsBy cfg tr time v t := by
  unfold decisionsBy
  rw [eventsBy_take hN, inputsBefore_take]
  rw [← eventsBy_take (N := N) hN]
  exact (eventsBy_le_length _).trans (by simp)

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem find?_congr {α : Type} {p p' : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = p' x) → l.find? p = l.find? p'
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem builtAt_take {t n : ℕ} (hN : ∀ i < tr.length, time i ≤ t → i < N) (v : Validator)
    (hb : builtAt cfg tr time v n ≤ t) :
    builtAt cfg (tr.take N) time v n = builtAt cfg tr time v n := by
  unfold builtAt at hb ⊢
  set p : ℕ → Bool := fun i => decide ((tr[i]?.map Prod.fst) = some v) &&
    (persists (outputsAt cfg tr i)).any (fun e => decide (e.2.round = n)) with hp
  set L' := (tr.take N).length
  have hL' : L' = min N tr.length := List.length_take
  have hp' : (List.range L').find? (fun i => decide (((tr.take N)[i]?.map Prod.fst) = some v) &&
      (persists (outputsAt cfg (tr.take N) i)).any (fun e => decide (e.2.round = n))) =
      (List.range L').find? p := by
    refine find?_congr fun i hi => ?_
    have hiN : i < N := by have := List.mem_range.mp hi; omega
    rw [take_getElem? hiN, outputsAt_take hiN]
  rw [hp']
  have hsplit : List.range tr.length = List.range L' ++
      (List.range (tr.length - L')).map (L' + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [hsplit, List.find?_append] at hb ⊢
  rcases h₁ : (List.range L').find? p with _ | i
  · simp only [h₁, Option.none_or] at hb ⊢
    rcases h₂ : ((List.range (tr.length - L')).map (L' + ·)).find? p with _ | i₀
    · rfl
    · rw [h₂] at hb
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some h₂)
      have hk' := List.mem_range.mp hk
      have := hN (L' + k) (by omega) hb
      omega
  · rfl



/-- **A node steady on the first `N` events.** -/
theorem steady_take {v : Validator} (h : ∀ i < N, ∀ inp, tr[i]? = some (v, inp) →
      inp ≠ .restart ∧
        ∀ r, inp = .timer r → stallsTwice (cfg.at v) (stateBefore cfg tr i v) r = false) :
    Steady cfg (tr.take N) v := by
  intro i inp hi
  obtain ⟨hiN, hi'⟩ := take_getElem?_some hi
  rw [stateBefore_take hiN.le]
  exact h i hiN inp hi'

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **A path through blocks read alike where they reference anything** is a
path through the other reading. -/
theorem reachesFrom_of_agree {blk blk' : BlockId → Block Validator BlockId Payload}
    (h : ∀ c, (blk c).refs.Nonempty → blk' c = blk c) {a b : BlockId}
    (hr : ReachesFrom blk a b) : ReachesFrom blk' a b := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    refine ih.tail ?_
    change d ∈ (blk' c).refs
    rw [h c ⟨d, hcd⟩]; exact hcd

theorem syncedWithin_take (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    (hinj : Converge.HashInjective cfg H tr) (ht : t₁' ≤ t₁)
    (hN : ∀ i < tr.length, time i ≤ t₁' → i < N) :
    Live.SyncedWithin cfg H T (tr.take N) time gst Δₛ t₁' := by
  intro j v id b hj hv hb hid hle x hx hreach hhor hxc
  obtain ⟨hjN, hj'⟩ := take_getElem?_some hj
  have hagree : ∀ c, (Live.knownBlock cfg H (tr.take N) c).refs.Nonempty →
      Live.knownBlock cfg H tr c = Live.knownBlock cfg H (tr.take N) c := by
    intro c hc
    by_cases hk : ∃ y ∈ Converge.knownIn cfg H (tr.take N), y.1 = c
    · obtain ⟨y, hy, rfl⟩ := hk
      rw [knownBlock_eq (hashInjective_take hinj N) hy, knownBlock_eq hinj (knownIn_take N hy)]
    · unfold Live.knownBlock at hc
      rw [dif_neg hk] at hc
      simp [Config.genesis] at hc
  have hhor' : horAt cfg tr time v (max (time j) gst + Δₛ) ≤ x.2.round := by
    unfold horAt; rw [← stateAt_take (N := N) (fun i hi hti => hN i hi (by omega))]; exact hhor
  obtain ⟨k, hjk, hk, htk⟩ := hsync j v id b hj' hv hb hid (by omega) x (knownIn_take N hx)
    (reachesFrom_of_agree hagree hreach) hhor' hxc
  have hkN : k < N := hN k (List.getElem?_eq_some_iff.mp hk).1 (by omega)
  exact ⟨k, hjk, by rw [take_getElem? hkN]; exact hk, htk⟩

end Time

end Node

end LeanDag
