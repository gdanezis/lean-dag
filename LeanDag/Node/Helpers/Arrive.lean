import LeanDag.Node.Helpers.Shape
import LeanDag.Node.Helpers.Hold
import LeanDag.Node.Helpers.Live
/-!
# A reliable node's rounds and timers, and the arrival of blocks

`docs/validator.md` §5.2. Along a trace, a node's state changes only at
its own events (`before_succ_cases`). Each of its rounds up to its top was
built at one of its events, with the round's timer (`built_by`,
`timer_of_persist`), and a round's timer, once fired, stays fired
(`fired_stays`). A reliable block that a reliable node `v` is given is
held by `v` once its history has been synchronised, provided `v` is at
the round below the block or above (`arrives`, `arrives_zero`). Past GST
a reliable node's block built at `s` is therefore held by every reliable
node by `max s gst + Δ + Δₛ` (`block_arrives`, `round_arrives`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

theorem stateBefore_of_none {v : Validator} {i : ℕ} (he : tr[i]? = none) :
    stateBefore cfg tr (i + 1) v = stateBefore cfg tr i v := by
  have hlen : tr.length ≤ i := List.getElem?_eq_none_iff.mp he
  unfold stateBefore
  rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ i + 1)]

/-- **A node's state changes only at its own events.** -/
theorem before_succ_cases (v : Validator) (i : ℕ) :
    stateBefore cfg tr (i + 1) v = stateBefore cfg tr i v ∨
      ∃ inp, tr[i]? = some (v, inp) ∧
        stateBefore cfg tr (i + 1) v = (Node.step (cfg.at v) (stateBefore cfg tr i v) inp).1 := by
  rcases he : tr[i]? with _ | ⟨w, inp⟩
  · exact Or.inl (stateBefore_of_none he)
  · rw [stateBefore_succ he]
    split
    · rename_i hw; subst hw; exact Or.inr ⟨inp, rfl, rfl⟩
    · exact Or.inl rfl

variable {v : Validator}

/-- **Each round up to a node's top was built** at one of its earlier
events. -/
theorem built_by : ∀ (i : ℕ) {n : ℕ}, (stateBefore cfg tr i v).top.isSome →
    n ≤ (stateBefore cfg tr i v).top.getD 0 →
    ∃ b < i, (tr[b]?.map Prod.fst) = some v ∧ ∃ e ∈ persists (outputsAt cfg tr b), e.2.round = n
  | 0, n, hs, _ => by simp [stateBefore, inputsBefore, run, State.init] at hs
  | i + 1, n, hs, hn => by
    rcases before_succ_cases (cfg := cfg) (tr := tr) v i with heq | ⟨inp, he, heq⟩
    · rw [heq] at hs hn
      obtain ⟨b, hb, h⟩ := built_by i hs hn
      exact ⟨b, by omega, h⟩
    · by_cases hold : (stateBefore cfg tr i v).top.isSome ∧
          n ≤ (stateBefore cfg tr i v).top.getD 0
      · obtain ⟨b, hb, h⟩ := built_by i hold.1 hold.2
        exact ⟨b, by omega, h⟩
      · rw [heq] at hs hn
        have hρ : (stateBefore cfg tr i v).top = none ∨
            (stateBefore cfg tr i v).top.getD 0 < n := by
          rcases h : (stateBefore cfg tr i v).top with _ | t
          · exact Or.inl rfl
          · right; rw [h] at hold; simp at hold; simp; omega
        obtain ⟨e, hep, her⟩ := step_every (cfg := cfg.at v) hs n hρ hn
        exact ⟨i, by omega, by rw [he]; rfl, e, by rw [outputsAt_eq he]; exact hep, her⟩

/-- **The timer of each round a node builds is set at the same event.** -/
theorem timer_of_persist {i : ℕ} {inp : Input Validator BlockId Payload}
    (he : tr[i]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (hep : e ∈ persists (outputsAt cfg tr i)) :
    Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ outputsAt cfg tr i := by
  rw [outputsAt_eq he] at hep ⊢
  exact step_timer (cfg := cfg.at v) e hep

/-- **A fired timer stays fired** at every later event. -/
theorem fired_stays {f r : ℕ} (hf : tr[f]? = some (v, Input.timer r)) :
    ∀ k, f < k → r ∈ (stateBefore cfg tr k v).fired
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, hfk => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hfk with hlt | rfl
    · have ih := fired_stays hf k hlt
      rcases before_succ_cases (cfg := cfg) (tr := tr) v k with heq | ⟨inp, -, heq⟩
      · rw [heq]; exact ih
      · rw [heq]
        exact step_fired (cfg := cfg.at v) ih
    · rw [stateBefore_succ hf, if_pos rfl, step_timer_fst]
      exact (settle_shape (cfg := cfg.at v)
        { stateBefore cfg tr f v with fired := insert r (stateBefore cfg tr f v).fired }).fired
        (Finset.mem_insert_self _ _)

/-- **A block a node builds at an event is stored** from the next event
on. -/
theorem built_stays {p : ℕ} {inp : Input Validator BlockId Payload}
    (hp : tr[p]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ persists (outputsAt cfg tr p)) :
    Stays (stateBefore cfg tr (p + 1) v).store (stateBefore cfg tr (p + 1) v).pending x := by
  rw [outputsAt_eq hp] at hx
  rw [stateBefore_succ hp, if_pos rfl]
  exact Or.inl (step_persist (cfg := cfg.at v) x hx).1

/-! ## A node's own blocks -/

theorem persists_before_mono (v : Validator) {a : ℕ} :
    ∀ {b : ℕ}, a ≤ b →
      ∀ x ∈ persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr a v)).2,
      x ∈ persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr b v)).2 := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact fun x hx => hx
  | succ b hab ih =>
    intro x hx
    have := ih x hx
    rcases hi : tr[b]? with _ | ⟨w, inp⟩
    · have hlen : tr.length ≤ b := List.getElem?_eq_none_iff.mp hi
      rw [inputsBefore_of_le (by omega : tr.length ≤ b + 1)]
      rw [inputsBefore_of_le hlen] at this
      exact this
    · rw [inputsBefore_succ hi]
      split
      · rw [run_append_single, persists_append]; exact List.mem_append_left _ this
      · rw [List.append_nil]; exact this

theorem broadcasts_of_persists {i : ℕ} {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) : e ∈ broadcasts (outputsAt cfg tr i) := by
  unfold outputsAt at he ⊢
  split at he
  · rename_i w inp _
    obtain ⟨bs, ho, -⟩ := (Converge.inv_before (cfg := cfg) (tr := tr) i w).step inp
    rw [ho.1] at he
    exact ho.2.1 e he
  · simp [persists] at he

/-- **A block of a node that the node knew it built** before. -/
theorem own_known {H : Finset Validator} (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H)
    (E : ℕ) {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ Converge.knownBefore cfg tr E v) (hc : x.2.creator = v) :
    x ∈ persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr E v)).2 := by
  simp only [Converge.knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hd | hp
  · obtain ⟨d, hdE, inp, hd', hdel⟩ := mem_delivered_before (cfg.at v) v E hd
    obtain ⟨p, hpd, hpv, hpb⟩ := htime d v inp hd' hv x hdel (by rw [hc]; exact hv)
    rw [hc] at hpv
    obtain ⟨inpp, hp'⟩ := Converge.event_of_map hpv
    obtain ⟨j, hjp, inpj, hj', hjx⟩ := Converge.persists_of_broadcasts hp' hpb
    exact persists_before_mono v (by omega : j + 1 ≤ E) x (persists_of_event hj' hjx)
  · exact hp

/-- **A block a node builds lies at or below its top after.** -/
theorem built_le_top {b : ℕ} {inp : Input Validator BlockId Payload} (hb : tr[b]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr b)) :
    ∃ t, (stateBefore cfg tr (b + 1) v).top = some t ∧ e.2.round ≤ t := by
  have hB := persists_of_event hb he
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) v).rounds with ⟨-, h⟩ | ⟨t, ht, hR⟩
  · rw [h] at hB; cases hB
  · exact ⟨t, ht, hR.2 e hB⟩

/-- **No stored block has the identifier of a node's next block**, with
an injective hash and its peers' blocks authenticated. -/
theorem fresh_before {H : Finset Validator} (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H) {E t : ℕ}
    (ht : (stateBefore cfg tr E v).top = some t) (R : Finset BlockId) :
    cfg.idOf ⟨t + 1, v, R, cfg.payload (t + 1)⟩ ∉ (stateBefore cfg tr E v).store.ids := by
  intro hin
  set st := (stateBefore cfg tr E v).store
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) E v).known _ hin
  have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv E hk)
  have hraw : st.blk _ = (⟨t + 1, v, R, cfg.payload (t + 1)⟩ :
      Block Validator BlockId Payload) := hid hidk.symm
  have hB := own_known htime hv E hk (by change (st.blk _).creator = v; rw [hraw])
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) E v).rounds with ⟨h, -⟩ | ⟨t', ht', hR⟩
  · rw [h] at ht; cases ht
  · rw [ht] at ht'; cases ht'
    have := hR.2 _ hB
    change (st.blk _).round ≤ t at this
    rw [hraw] at this
    simp at this

/-- **A reliable node has started after its start event.** -/
theorem started_after {H : Finset Validator} (hadm : cfg.Admissible)
    (hid : Function.Injective cfg.idOf) (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H)
    {st : ℕ} (hst : tr[st]? = some (v, .start)) : (stateBefore cfg tr (st + 1) v).top.isSome := by
  rw [stateBefore_succ hst, if_pos rfl]
  set s := stateBefore cfg tr st v
  by_cases hn : s.top = none
  · have hrs := (Converge.inv_before (cfg := cfg) (tr := tr) st v).rounds
    rcases hrs with ⟨-, hB0⟩ | ⟨t, ht, -⟩
    swap
    · rw [hn] at ht; cases ht
    have hg : (cfg.at v).idOf (cfg.at v).genesis ∉ s.store.ids ∧
        rowValid (cfg.at v).q (Function.update s.store.blk ((cfg.at v).idOf (cfg.at v).genesis)
          (cfg.at v).genesis) (cfg.at v).genesis := by
      refine ⟨fun hin => ?_, ⟨fun i hi => ?_, fun h => ?_, fun i hi => ?_⟩⟩
      · have hk := (Converge.inv_before (cfg := cfg) (tr := tr) st v).known _ hin
        have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv st hk)
        have hraw : s.store.blk _ = (cfg.at v).genesis := hid hidk.symm
        have hB := own_known htime hv st hk (by
          change (s.store.blk _).creator = v; rw [hraw]; rfl)
        rw [hB0] at hB; cases hB
      · simp [Config.genesis] at hi
      · simp [Config.genesis] at h
      · simp [Config.genesis] at hi
    simp only [Node.step, if_pos (⟨hn, hadm⟩ : s.top = none ∧ (cfg.at v).Admissible), dif_pos hg]
    exact (settle_shape (cfg := cfg.at v) _).rises.2.1 rfl
  · have hstep : (Node.step (cfg.at v) s .start).1 = s := by
      simp only [Node.step, if_neg (fun h : s.top = none ∧ (cfg.at v).Admissible => hn h.1)]
    rw [hstep]
    exact Option.ne_none_iff_isSome.mp hn

/-! ## The blocks the honest nodes know -/

section Known

variable {H : Finset Validator}

theorem knownBlock_eq (hinj : Converge.HashInjective cfg H tr)
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ Converge.knownIn cfg H tr) :
    Live.knownBlock cfg H tr x.1 = x.2 := by
  have h : ∃ y ∈ Converge.knownIn cfg H tr, y.1 = x.1 := ⟨x, hx, rfl⟩
  unfold Live.knownBlock
  rw [dif_pos h]
  obtain ⟨hm, he⟩ := Classical.choose_spec h
  exact Converge.content_eq hinj hm hx he

theorem knownBlock_gT (z : BlockId) :
    (Live.knownBlock cfg H tr z).round = (Converge.gT cfg H tr z).round ∧
      (Live.knownBlock cfg H tr z).creator = (Converge.gT cfg H tr z).creator := by
  unfold Live.knownBlock Converge.gT
  split <;> simp

/-- **A path through a store's blocks** is one through the blocks known,
when the store's blocks are the ones known. -/
theorem reaches_known {st : Store Validator BlockId Payload}
    (hst : ∀ w ∈ st.ids, Live.knownBlock cfg H tr w = st.blk w) {r : BlockId}
    (hr : r ∈ st.ids) {z : BlockId} (h : ReachesFrom st.blk r z) :
    ReachesFrom (Live.knownBlock cfg H tr) r z ∧ z ∈ st.ids := by
  induction h with
  | refl => exact ⟨ReachesFrom.refl, hr⟩
  | tail hrw hstep ih =>
    rename_i w z'
    obtain ⟨ih₁, hw⟩ := ih
    change z' ∈ (st.blk w).refs at hstep
    refine ⟨ih₁.trans (ReachesFrom.single ?_), st.complete w hw z' hstep⟩
    rw [hst w hw]; exact hstep

end Known

/-! ## Arrival -/

section Arrival

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δₛ t₁ : ℕ}

/-- **A reliable block arrives** at a reliable node `v` given it: `v`
holds it after `v`'s events up to a time by which its history was
synchronised, provided `v` is at the round below it or above. -/
theorem arrives (hinj : Converge.HashInjective cfg H tr)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H)
    (hmono : Live.TimeMono tr time) (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp))
    {y : BlockId × Block Validator BlockId Payload} (hy : y ∈ persists (outputsAt cfg tr i))
    {U : BlockRecord Validator BlockId Payload P H}
    {x : State Validator BlockId Payload}
    (hx : BuildState (cfg.at u) U (knownAll cfg H tr) (stateBefore cfg tr i u) inp x)
    {y' : State Validator BlockId Payload} {o : List (Output Validator BlockId Payload)}
    (hb : tryBuild (cfg.at u) x = some (y', o)) (hyo : y ∈ persists o)
    {j : ℕ} (hj : tr[j]? = some (v, .deliver y.1 y.2)) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (ht₁ : max (time j) gst + Δₛ ≤ t₁)
    (hZs : (stateAt cfg tr time v τ).top.isSome)
    (hZn : y.2.round ≤ (stateAt cfg tr time v τ).top.getD 0 + 1) :
    y.1 ∈ (stateAt cfg tr time v τ).store.ids := by
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ :=
    (lt_eventsBy hmono hjl).mpr (le_trans (le_max_left _ _) (le_trans (Nat.le_add_right _ _) hτ))
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).store.ids
  change (stateBefore cfg tr (eventsBy tr time τ) v).top.isSome at hZs
  change _ ≤ (stateBefore cfg tr (eventsBy tr time τ) v).top.getD 0 + 1 at hZn
  set E := eventsBy tr time τ with hE
  set Zs := stateBefore cfg tr E v with hZsdef
  -- the build
  obtain ⟨r', id', b', hnew, hrefs, hpred, hxt, hbr, hbc, hid, hrv, -, -, -, -, hout⟩ :=
    tryBuild_some hb
  rw [hout, persists_built, List.mem_singleton] at hyo
  subst hyo
  simp only at hj hZn ⊢
  obtain ⟨B, hiX⟩ := hx.inv
  set raw := Live.knownBlock cfg H tr with hraw
  have hknX : ∀ w ∈ x.store.ids, (w, x.store.blk w) ∈ Converge.knownIn cfg H tr :=
    fun w hw => by
      obtain ⟨v', hv', hk⟩ := hiX.known w hw
      exact knownOf_sub hv' hk
  have hstK : ∀ w ∈ x.store.ids, raw w = x.store.blk w := fun w hw =>
    knownBlock_eq hinj (hknX w hw)
  have hyK : ((id', b') : BlockId × Block Validator BlockId Payload) ∈ Converge.knownIn cfg H tr :=
    Or.inr ⟨i, u, by rw [hi]; rfl, hTH hu, hy⟩
  have hry : raw id' = b' := knownBlock_eq hinj hyK
  have hbu : b'.creator = u := hbc
  have C : CausalStructure x.store.blk x.store.ids := x.store.toRecord.causal
  have hAv := Converge.reads_before hinj (hTH hv) E
  have hZv : ∀ w ∈ Zs.store.ids, (Zs.store.blk w).round = (raw w).round ∧
      (Zs.store.blk w).creator = (raw w).creator := fun w hw => by
    have a := hAv w hw
    obtain ⟨k₁, k₂⟩ := knownBlock_gT (cfg := cfg) (H := H) (tr := tr) w
    exact ⟨(congrArg Block.round a).trans k₁.symm, (congrArg Block.creator a).trans k₂.symm⟩
  -- the history the author built on
  let Z : Finset BlockId := insert id' (b'.refs.biUnion (historyFrom x.store.blk))
  have hZmem : ∀ z ∈ Z, z = id' ∨ ∃ r ∈ b'.refs, z ∈ historyFrom x.store.blk r ∧ z ∈ x.store.ids :=
    fun z hz => by
      rcases Finset.mem_insert.mp hz with h | h
      · exact Or.inl h
      · obtain ⟨r, hr, hzr⟩ := Finset.mem_biUnion.mp h
        exact Or.inr ⟨r, hr, hzr, C.history_subset_ids (hrefs hr) hzr⟩
  -- each of its blocks stays at `v`
  have hstays : ∀ z ∈ Z, Stays Zs.store Zs.pending (z, raw z) := by
    intro z hz
    rcases hZmem z hz with rfl | ⟨r, hr, hzr, hzx⟩
    · rw [hry]
      exact stays_from hinj (hTH hv) hyK
        (stays_succ hinj (hTH hv) hyK (Or.inr ⟨hj, by rw [hbu]; exact huv⟩)) E (by omega)
    · set xz : BlockId × Block Validator BlockId Payload := (z, x.store.blk z)
      have hxzK := hknX z hzx
      have hrz : raw z = xz.2 := hstK z hzx
      rw [hrz]
      by_cases hcr : xz.2.creator = v
      · -- one of `v`'s own blocks, which it built before
        have hxzA : xz ∈ knownAll cfg H tr := hiX.known z hzx
        have hxzp := mem_persists_of_known (hashInjective_of_trace hinj) (authentic_of_timely htime)
          hxzA (by rw [hcr]; exact hTH hv)
        rw [hcr] at hxzp
        have hρ : xz.2.round ≤ (Zs.top.getD 0) := by
          have h₁ := C.round_le_of_mem_history (hrefs hr) hzr
          have h₂ := hpred r hr
          have h₃ : (x.store.blk z).round = xz.2.round := rfl
          omega
        obtain ⟨bρ, hbρE, hbρv, e, he, her⟩ := built_by E hZs hρ
        obtain ⟨inpρ, hbρ⟩ := Converge.event_of_map hbρv
        have hep : e ∈ persists (runOf cfg tr v).2 :=
          mem_persists_iff.mpr (mem_outputs_of_event hbρ (mem_persists_iff.mp he))
        have hex : e = xz := eq_of_persists v hep hxzp her
        rw [hex] at he
        exact stays_from hinj (hTH hv) hxzK (built_stays hbρ he) E (by omega)
      · -- another's, synchronised after `v` received the author's block
        have hreach : ReachesFrom raw id' z := by
          refine ReachesFrom.of_mem_refs (by rw [hry]; exact hr) ?_
          exact (reaches_known hstK (hrefs hr) (reaches_of_mem_historyUptoFrom hzr)).1
        obtain ⟨k, hjk, hk, htk⟩ := hsync j v id' b' hj hv (by rw [hbu]; exact hu) hid ht₁ xz
          hxzK hreach hcr
        have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
        have hkE : k < E := (lt_eventsBy hmono hkl).mpr (htk.trans hτ)
        exact stays_from hinj (hTH hv) hxzK
          (stays_succ hinj (hTH hv) hxzK (Or.inr ⟨hk, hcr⟩)) E (by omega)
  -- it is closed under references
  have hcl : ∀ z ∈ Z, ∀ r ∈ (raw z).refs, r ∈ Z ∧ (raw r).round + 1 = (raw z).round := by
    intro z hz r hr
    rcases hZmem z hz with rfl | ⟨r₀, hr₀, hzr, hzx⟩
    · rw [hry] at hr ⊢
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, mem_historyFrom_self⟩), ?_⟩
      rw [hstK r (hrefs hr)]; exact hpred r hr
    · have hbz : x.store.blk z = raw z := (hstK z hzx).symm
      have hr' : r ∈ (x.store.blk z).refs := by rw [hbz]; exact hr
      have hrx := C.complete z hzx r hr'
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r₀, hr₀,
        C.history_subset_of_reaches (hrefs hr₀) ((C.mem_history_iff (hrefs hr₀)).mp hzr)
          (C.mem_history_of_mem_refs hzx hr')⟩), ?_⟩
      rw [hstK r hrx, ← hbz]; exact C.refs_round z hzx r hr'
  -- and valid at `v` once its references are
  have hrd : ∀ z ∈ Z, (raw z).refs ⊆ Zs.store.ids →
      ready (cfg.at v) Zs.store (z, raw z) = true := by
    intro z hz hzr
    have hcl' := hcl z hz
    simp only [ready, decide_eq_true_eq]
    refine ⟨hzr, fun r hr => by rw [(hZv r (hzr hr)).1]; exact (hcl' r hr).2, ?_⟩
    have hne : ∀ r ∈ (raw z).refs, r ≠ z := fun r hr h => by
      have := (hcl' r hr).2; rw [h] at this; omega
    rcases hZmem z hz with rfl | ⟨r₀, hr₀, hzr₀, hzx⟩
    · rw [hry] at hzr hne ⊢
      refine rowValid_congr (fun r hr => ?_) hrv
      rw [Function.update_of_ne (fun h => hnew (by rw [← h]; exact hrefs hr)),
        Function.update_of_ne (hne r hr)]
      rw [(hZv r (hzr hr)).1, (hZv r (hzr hr)).2, hstK r (hrefs hr)]
      exact ⟨rfl, rfl⟩
    · have hval := hiX.valid z hzx
      have hbz : x.store.blk z = raw z := (hstK z hzx).symm
      rw [hbz] at hval
      refine rowValid_congr (fun r hr => ?_) hval
      have hrx : r ∈ x.store.ids := C.complete z hzx r (by rw [hbz]; exact hr)
      rw [Function.update_of_ne (hne r hr), (hZv r (hzr hr)).1, (hZv r (hzr hr)).2,
        hstK r hrx]
      exact ⟨rfl, rfl⟩
  exact holds_of_stays (cfg := cfg.at v) (Converge.noReady_before (cfg := cfg) v E)
    (Z := Z) raw hstays hcl hrd id' (Finset.mem_insert_self _ _)

/-- **A reliable genesis block arrives** at a reliable node given it. -/
theorem arrives_zero (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {i : ℕ}
    (hiu : (tr[i]?.map Prod.fst) = some u)
    {y : BlockId × Block Validator BlockId Payload} (hy : y ∈ persists (outputsAt cfg tr i))
    (hyu : y.2.creator = u) (hy0 : y.2.round = 0)
    {j : ℕ} (hj : tr[j]? = some (v, .deliver y.1 y.2)) {τ : ℕ} (hjτ : time j ≤ τ) :
    y.1 ∈ (stateAt cfg tr time v τ).store.ids := by
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ := (lt_eventsBy hmono hjl).mpr hjτ
  have hyK : y ∈ Converge.knownIn cfg H tr := Or.inr ⟨i, u, hiu, hTH hu, hy⟩
  have hst := stays_from hinj (hTH hv) hyK
    (stays_succ hinj (hTH hv) hyK (Or.inr ⟨hj, by rw [hyu]; exact huv⟩))
    (eventsBy tr time τ) (by omega)
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).store.ids
  rcases hst with h | h
  · exact h
  · -- an honest round-0 block has no references, so it is ready
    obtain ⟨inp, hi⟩ := Converge.event_of_map hiu
    have hgood := (Converge.inv_before (cfg := cfg) (tr := tr) (i + 1) u).good y
      (persists_of_event hi hy)
    have hval := hgood.2.2.2 (Converge.gT cfg H tr) fun x hx =>
      Converge.gT_of_known hinj (Converge.knownBefore_sub (hTH hu) (i + 1) hx)
    have hr0 : ∀ r ∈ y.2.refs, False := fun r hr => by
      have := hval.predecessor r hr; omega
    have hrd : ready (cfg.at v) (stateBefore cfg tr (eventsBy tr time τ) v).store y = true := by
      simp only [ready, decide_eq_true_eq]
      exact ⟨fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        rowValid_congr (fun r hr => (hr0 r hr).elim) hval⟩
    have := Converge.noReady_before (cfg := cfg) (tr := tr) v (eventsBy tr time τ) y h
    rw [hrd] at this; cases this

end Arrival

/-! ## Arrival past GST -/

section Rounds

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

/-- **A reliable peer's block arrives**: a block a reliable node built at
an event at or before `s` is held by a reliable node `v` after `v`'s
events by `max s gst + Δ + Δₛ` or later, once `v` is at the round below
the block's or above. -/
theorem block_arrives (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {b : ℕ}
    {inp : Input Validator BlockId Payload} (hb : tr[b]? = some (u, inp))
    {e : BlockId × Block Validator BlockId Payload} (hep : e ∈ persists (outputsAt cfg tr b))
    {s : ℕ} (htb : time b ≤ s) {τ : ℕ} (hτ : max s gst + Δ + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) {t : ℕ}
    (hZt : (stateAt cfg tr time v τ).top = some t) (hnt : e.2.round ≤ t + 1) :
    e.1 ∈ (stateAt cfg tr time v τ).store.ids ∧
      ((stateAt cfg tr time v τ).store.blk e.1).round = e.2.round ∧
      ((stateAt cfg tr time v τ).store.blk e.1).creator = u ∧
      (stateAt cfg tr time v τ).store.blk e.1 = e.2 := by
  have hbu : (tr[b]?.map Prod.fst) = some u := by rw [hb]; rfl
  have hebc := broadcasts_of_persists hep
  obtain ⟨j, hbj, hj, htj⟩ := hdel b u inp hb hu (v, .deliver e.1 e.2)
    ⟨.broadcast e.1 e.2, mem_broadcasts.mp hebc, Ne.symm huv, rfl⟩ hv (by omega)
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) u).good e
    (persists_of_event hb hep)).2.1
  -- `v` holds the block
  have hin : e.1 ∈ (stateAt cfg tr time v τ).store.ids := by
    by_cases hn0 : e.2.round = 0
    · exact arrives_zero hinj hTH hmono hu hv huv hbu hep hgood hn0 hj (by omega)
    · obtain ⟨x, y', o, hx, hxb, heo⟩ := build_witness hσ hadm hf htime hinj (hTH hu) hb hep hn0
      have hZs : (stateAt cfg tr time v τ).top.isSome := by rw [hZt]; rfl
      exact arrives hinj htime hTH hmono hsync hu hv huv hb hep hx hxb heo hj (τ := τ)
        (by omega) (by omega) hZs (by rw [hZt]; simp; omega)
  refine ⟨hin, ?_⟩
  set Z := stateAt cfg tr time v τ
  have hk := Converge.knownBefore_sub (hTH hv) (eventsBy tr time τ)
    ((Converge.inv_before (cfg := cfg) (tr := tr) (eventsBy tr time τ) v).known e.1 hin)
  have hblk : Z.store.blk e.1 = e.2 :=
    Converge.content_eq hinj hk (Or.inr ⟨b, u, hbu, hTH hu, hep⟩) rfl
  exact ⟨by rw [hblk], by rw [hblk]; exact hgood, hblk⟩

/-- **A reliable peer's block of a round arrives**: past GST, a reliable
node at its round `n` or above at `s` has its round-`n` block held by a
reliable node `v` after `v`'s events by `s + Δ + Δₛ` or later, once `v`
is at round `n` or above. -/
theorem round_arrives (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {s n : ℕ} (hgs : gst ≤ s)
    (hus : (stateAt cfg tr time u s).top.isSome) (hun : n ≤ topAt cfg tr time u s) {τ : ℕ}
    (hτ : s + Δ + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) {t : ℕ}
    (hZt : (stateAt cfg tr time v τ).top = some t) (hnt : n ≤ t) :
    ∃ j ∈ (stateAt cfg tr time v τ).store.ids, ((stateAt cfg tr time v τ).store.blk j).round = n ∧
      ((stateAt cfg tr time v τ).store.blk j).creator = u := by
  obtain ⟨b, hbs, hbu, e, hep, her⟩ := built_by (eventsBy tr time s) hus hun
  obtain ⟨inp, hb⟩ := Converge.event_of_map hbu
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have htb : time b ≤ s := (lt_eventsBy hmono hbl).mp hbs
  obtain ⟨h₁, h₂, h₃, -⟩ := block_arrives hσ hadm hf htime hinj hTH
    hmono hdel hsync hu hv huv hb hep htb (τ := τ) (by omega) ht₁ hZt (by omega)
  exact ⟨e.1, h₁, h₂.trans her, h₃⟩

end Rounds

end Node

end LeanDag
