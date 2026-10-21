import LeanDag.Node.Helpers.Shape
import LeanDag.Node.Helpers.Catch
import LeanDag.Node.Helpers.Live
/-!
# A reliable node's rounds, timers and horizon along a trace

`docs/validator.md` §13.2. Along a trace without restarts at a node: its
state changes only at its own events (`before_succ_cases`); each of its
rounds up to its top was built at one of its events, with the round's
timer (`built_by`); a round's timer, once fired, stays fired while the
top stays at or below it (`fired_stays`); after the timer, the held round
is at least the top then (`held_after_timer`); and its horizon, when
above `0`, was last raised at one of its events, with an announced
certificate, to at most `Λ` below the lesser of its slot round and the
top before (`last_rise`).
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

variable {v : Validator} (hnv : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart))
include hnv

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
    · have hsi := (fired_before (cfg := cfg) hnv i).1
      have hri : inp ≠ .restart := fun h => hnv i (by rw [he, h])
      by_cases hold : (stateBefore cfg tr i v).top.isSome ∧
          n ≤ (stateBefore cfg tr i v).top.getD 0
      · obtain ⟨b, hb, h⟩ := built_by i hold.1 hold.2
        exact ⟨b, by omega, h⟩
      · rw [heq] at hs hn
        have hρ : (stateBefore cfg tr i v).top = none ∨
            (stateBefore cfg tr i v).top.getD 0 < n := by
          rcases h : (stateBefore cfg tr i v).top with _ | t
          · exact Or.inl rfl
          · right; rw [h] at hold; simp at hold; simp; omega
        obtain ⟨e, hep, her⟩ := step_every (cfg := cfg.at v) hsi hri hs n hρ hn
        exact ⟨i, by omega, by rw [he]; rfl, e, by rw [outputsAt_eq he]; exact hep, her⟩

/-- **A node's top before an event is at most the round of a block it
builds there.** -/
theorem top_le_built {i : ℕ} {inp : Input Validator BlockId Payload}
    (he : tr[i]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (hep : e ∈ persists (outputsAt cfg tr i)) :
    (stateBefore cfg tr i v).top.getD 0 ≤ e.2.round := by
  rw [outputsAt_eq he] at hep
  rcases step_above (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
    (fun h => hnv i (by rw [he, h])) e hep with h | ⟨h, h'⟩
  · exact h.le
  · rw [h, h']; rfl

/-- **The timer of each round a node builds is set at the same event.** -/
theorem timer_of_persist {i : ℕ} {inp : Input Validator BlockId Payload}
    (he : tr[i]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (hep : e ∈ persists (outputsAt cfg tr i)) :
    Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ outputsAt cfg tr i := by
  rw [outputsAt_eq he] at hep ⊢
  exact step_timer (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
    (fun h => hnv i (by rw [he, h])) e hep

/-- **A fired timer stays fired** while the top stays at or below its
round. -/
theorem fired_stays {f r : ℕ} (hf : tr[f]? = some (v, Input.timer r)) :
    ∀ k, f < k → (stateBefore cfg tr k v).top.getD 0 ≤ r → r ∈ (stateBefore cfg tr k v).fired
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, hfk, hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hfk with hlt | rfl
    · have hrk := (rises_before (cfg := cfg) hnv (Nat.le_succ k)).1
      have ih := fired_stays hf k hlt (hrk.trans hk)
      rcases before_succ_cases (cfg := cfg) (tr := tr) v k with heq | ⟨inp, he, heq⟩
      · rw [heq]; exact ih
      · rw [heq] at hk ⊢
        exact step_fired (cfg := cfg.at v) (fired_before (cfg := cfg) hnv k).1
          (fun h => hnv k (by rw [he, h])) r ih hk
    · rw [stateBefore_succ hf, if_pos rfl] at hk ⊢
      have hx : ({ stateBefore cfg tr f v with
          fired := insert r (stateBefore cfg tr f v).fired } : State Validator BlockId Payload).recovering
          = false := (fired_before (cfg := cfg) hnv f).1
      exact (settle_shape (cfg := cfg.at v) hx).2.fired r (Finset.mem_insert_self _ _) hk

/-- **After a node's timer**, the round it holds is at least its top then. -/
theorem held_after_timer {f r : ℕ} (hf : tr[f]? = some (v, Input.timer r)) :
    ∀ k, f < k → (stateBefore cfg tr f v).top.getD 0 ≤ (stateBefore cfg tr k v).held
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, hfk => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hfk with hlt | rfl
    · have ih := held_after_timer hf k hlt
      rcases before_succ_cases (cfg := cfg) (tr := tr) v k with heq | ⟨inp, he, heq⟩
      · rw [heq]; exact ih
      · rw [heq]
        rcases step_held (cfg := cfg.at v) (inp := inp) (fired_before (cfg := cfg) hnv k).1
          (fun h => hnv k (by rw [he, h])) with h | h <;> rw [h]
        · exact ih
        · exact (rises_before (cfg := cfg) hnv hlt.le).1
    · rw [stateBefore_succ hf, if_pos rfl]
      have hx : ({ stateBefore cfg tr f v with
          fired := insert r (stateBefore cfg tr f v).fired } : State Validator BlockId Payload).recovering
          = false := (fired_before (cfg := cfg) hnv f).1
      exact (settle_shape (cfg := cfg.at v) hx).1.ge

/-- **A horizon above `0` was last raised at one of the node's events**,
with an announced certificate, to at most `Λ` below the lesser of its
slot round and the top before. -/
theorem last_rise : ∀ (i : ℕ), 0 < (stateBefore cfg tr i v).store.base →
    ∃ r < i, ∃ inp, tr[r]? = some (v, inp) ∧
      (stateBefore cfg tr (r + 1) v).store.base = (stateBefore cfg tr i v).store.base ∧
      ∃ c, Output.announce c ∈ outputsAt cfg tr r ∧
        (stateBefore cfg tr i v).store.base ≤
          min (cfg.per * (c.height / cfg.m)) ((stateBefore cfg tr r v).top.getD 0) - cfg.lag
  | 0, h => by simp [stateBefore, inputsBefore, run, State.init, Store.empty] at h
  | i + 1, h => by
    have hmono := (grows_before (cfg := cfg) (tr := tr) v (Nat.le_succ i)).1
    by_cases hlt : (stateBefore cfg tr i v).store.base < (stateBefore cfg tr (i + 1) v).store.base
    · rcases before_succ_cases (cfg := cfg) (tr := tr) v i with heq | ⟨inp, he, heq⟩
      · rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
      · rw [heq] at hlt
        obtain ⟨c, hc, hcb⟩ := step_rise (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
          (fun h => hnv i (by rw [he, h])) hlt
        refine ⟨i, by omega, inp, he, rfl, c, by rw [outputsAt_eq he]; exact hc, ?_⟩
        rw [heq]; exact hcb
    · have heq : (stateBefore cfg tr (i + 1) v).store.base =
          (stateBefore cfg tr i v).store.base := le_antisymm (not_lt.mp hlt) hmono
      obtain ⟨r, hr, inp, he, hb, c, hc, hcb⟩ := last_rise i (by rw [← heq]; exact h)
      exact ⟨r, by omega, inp, he, hb.trans heq.symm, c, hc, by rw [heq]; exact hcb⟩

omit hnv in
/-- **A block a node builds at an event stays** from the next event on. -/
theorem built_stays {p : ℕ} {inp : Input Validator BlockId Payload}
    (hnv' : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart)) (hp : tr[p]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ persists (outputsAt cfg tr p)) :
    Stays (stateBefore cfg tr (p + 1) v).store (stateBefore cfg tr (p + 1) v).pending x := by
  rw [outputsAt_eq hp] at hx
  rw [stateBefore_succ hp, if_pos rfl]
  rcases step_keeps_built (cfg := cfg.at v) (fired_before (cfg := cfg) hnv' p).1
    (fun h => hnv' p (by rw [hp, h])) x hx with ⟨h, -⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-! ## A node's own blocks -/

omit hnv in
theorem persists_before_mono (v : Validator) {a : ℕ} :
    ∀ {b : ℕ}, a ≤ b → ∀ x ∈ persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr a v)).2,
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

omit hnv in
theorem broadcasts_of_persists {i : ℕ} {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) : e ∈ broadcasts (outputsAt cfg tr i) := by
  unfold outputsAt at he ⊢
  split at he
  · rename_i w inp _
    obtain ⟨bs, ho, -⟩ := (Converge.inv_before (cfg := cfg) (tr := tr) i w).step inp
    rw [ho.1] at he
    rw [ho.2]; exact he
  · simp [persists] at he

omit hnv in
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
    exact persists_before_mono v (by omega : p + 1 ≤ E) x
      (persists_of_event hp' (Converge.persists_of_broadcasts hpb))
  · exact hp

omit hnv in
/-- **A block a node builds lies at or below its top after.** -/
theorem built_le_top {b : ℕ} {inp : Input Validator BlockId Payload} (hb : tr[b]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr b)) :
    ∃ t, (stateBefore cfg tr (b + 1) v).top = some t ∧ e.2.round ≤ t := by
  have hB := persists_of_event hb he
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) v).rounds with ⟨-, h, -⟩ | ⟨t, ht, -, hR⟩
  · rw [h] at hB; cases hB
  · exact ⟨t, ht, hR.2 e hB⟩

omit hnv in
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
  have hraw : st.map.getD _ st.junk = (⟨t + 1, v, R, cfg.payload (t + 1)⟩ :
      Block Validator BlockId Payload) := hid hidk.symm
  have hB := own_known htime hv E hk (by show (st.map.getD _ st.junk).creator = v; rw [hraw])
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) E v).rounds with ⟨h, -, -⟩ | ⟨t', ht', -, hR⟩
  · rw [h] at ht; cases ht
  · rw [ht] at ht'; cases ht'
    have := hR.2 _ hB
    change (st.map.getD _ st.junk).round ≤ t at this
    rw [hraw] at this
    simp at this

omit hnv in
/-- **A reliable node has started after its start event.** -/
theorem started_after {H : Finset Validator} (hadm : cfg.Admissible)
    (hid : Function.Injective cfg.idOf) (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H)
    {st : ℕ} (hst : tr[st]? = some (v, .start)) : (stateBefore cfg tr (st + 1) v).top.isSome := by
  rw [stateBefore_succ hst, if_pos rfl]
  set s := stateBefore cfg tr st v
  by_cases hn : s.top = none
  · have hrs := (Converge.inv_before (cfg := cfg) (tr := tr) st v).rounds
    rcases hrs with ⟨-, hB0, hb0⟩ | ⟨t, ht, -⟩
    swap
    · rw [hn] at ht; cases ht
    have hg : (cfg.at v).idOf (cfg.at v).genesis ∉ s.store.ids ∧
        s.store.base ≤ (cfg.at v).genesis.round ∧
        rowValid (cfg.at v).q (Function.update s.store.blk ((cfg.at v).idOf (cfg.at v).genesis)
          (cfg.at v).genesis) (cfg.at v).genesis := by
      refine ⟨fun hin => ?_, by rw [hb0]; exact Nat.zero_le _, ⟨fun i hi => ?_, fun h => ?_,
        fun i hi => ?_⟩⟩
      · have hk := (Converge.inv_before (cfg := cfg) (tr := tr) st v).known _ hin
        have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv st hk)
        have hraw : s.store.map.getD _ s.store.junk = (cfg.at v).genesis := hid hidk.symm
        have hB := own_known htime hv st hk (by
          show (s.store.map.getD _ s.store.junk).creator = v; rw [hraw]; rfl)
        rw [hB0] at hB; cases hB
      · simp [Config.genesis] at hi
      · simp [Config.genesis] at h
      · simp [Config.genesis] at hi
    simp only [Node.step, if_pos (⟨hn, hadm⟩ : s.top = none ∧ (cfg.at v).Admissible), dif_pos hg]
    have key : ∀ x : State Validator BlockId Payload, x.recovering = false → x.top.isSome →
        (Node.settle (cfg.at v) x).1.top.isSome := fun x hx hxt =>
      (settle_shape (cfg := cfg.at v) hx).2.rises.2.1 hxt
    exact key _ rfl rfl
  · have hstep : (Node.step (cfg.at v) s .start).1 = s := by
      simp only [Node.step, if_neg (fun h : s.top = none ∧ (cfg.at v).Admissible => hn h.1)]
    rw [hstep]
    exact Option.ne_none_iff_isSome.mp hn

/-! ## Arrival -/

section Arrival

omit hnv

variable {H T : Finset Validator} {time : ℕ → ℕ} {gst Δₛ t₁ : ℕ}

/-- **A reliable block arrives** at a reliable node `v` given it: once
the node's horizon reaches the author's after the event that built it,
the node holds the block, or the block lies below its horizon, after
its events up to a time by which the block's history was synchronised. -/
theorem arrives (hl : cfg.limit = none) (hinj : Converge.HashInjective cfg H tr)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H) (hnr : Converge.NoRestart T tr)
    (hmono : Live.TimeMono tr time) (hsync : Live.SyncedWithin cfg T tr time gst Δₛ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp))
    {y : BlockId × Block Validator BlockId Payload} (hy : y ∈ broadcasts (outputsAt cfg tr i))
    {j : ℕ} (hij : i < j) (hj : tr[j]? = some (v, .deliver y.1 y.2)) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (ht₁ : max (time j) gst + Δₛ ≤ t₁)
    (hbase : (stateBefore cfg tr (i + 1) u).store.base ≤ (stateAt cfg tr time v τ).store.base) :
    y.1 ∈ (stateAt cfg tr time v τ).store.ids ∨ y.2.round < (stateAt cfg tr time v τ).store.base := by
  have hnu : ∀ k : ℕ, tr[k]? ≠ some (u, Input.restart) := fun k => hnr k u hu
  have hnv : ∀ k : ℕ, tr[k]? ≠ some (v, Input.restart) := fun k => hnr k v hv
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ :=
    (lt_eventsBy hmono hjl).mpr (le_trans (le_max_left _ _) (le_trans (Nat.le_add_right _ _) hτ))
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).store.ids ∨
    y.2.round < (stateBefore cfg tr (eventsBy tr time τ) v).store.base
  change _ ≤ (stateBefore cfg tr (eventsBy tr time τ) v).store.base at hbase
  set E := eventsBy tr time τ with hE
  set Zs := stateBefore cfg tr E v with hZs
  set st := (stateBefore cfg tr (i + 1) u).store with hst
  have hyp := Converge.persists_of_broadcasts hy
  have hyK : y ∈ Converge.knownIn cfg H tr := Or.inr ⟨i, u, by rw [hi]; rfl, hTH hu, hyp⟩
  -- the author stored its block, or it lies below the author's horizon
  have hsi : stateBefore cfg tr (i + 1) u = (Node.step (cfg.at u) (stateBefore cfg tr i u) inp).1 :=
    by rw [stateBefore_succ hi, if_pos rfl]
  have hk := step_keeps_built (cfg := cfg.at u) (inp := inp) (fired_before (cfg := cfg) hnu i).1
    (fun h => hnu i (by rw [hi, h])) y (by rw [← outputsAt_eq hi]; exact hyp)
  rw [← hsi] at hk
  rcases hk with ⟨hyst, -⟩ | hlt
  swap
  · exact Or.inr (lt_of_lt_of_le hlt hbase)
  -- the author's block and its history, as it held them
  let raw : BlockId → Block Validator BlockId Payload := fun z => st.map.getD z st.junk
  have hknown : ∀ z ∈ st.ids, (z, raw z) ∈ Converge.knownBefore cfg tr (i + 1) u := fun z hz =>
    (Converge.inv_before (cfg := cfg) (i + 1) u).known z hz
  have hknownIn : ∀ z ∈ st.ids, (z, raw z) ∈ Converge.knownIn cfg H tr := fun z hz =>
    Converge.knownBefore_sub (hTH hu) (i + 1) (hknown z hz)
  have hry : raw y.1 = y.2 := Converge.content_eq hinj (hknownIn y.1 hyst) hyK rfl
  have hyu : y.2.creator = u := by
    have hyB : y ∈ persists (run (cfg.at u) (State.init (cfg.at u)) (inputsBefore tr (i + 1) u)).2 := by
      rw [inputsBefore_succ hi, if_pos rfl, run_append_single, persists_append]
      refine List.mem_append_right _ ?_
      change y ∈ persists (Node.step (cfg.at u) (stateBefore cfg tr i u) inp).2
      rw [← outputsAt_eq hi]; exact hyp
    exact ((Converge.inv_before (cfg := cfg) (i + 1) u).good y hyB).2.1
  have C : CausalStructure st.blk st.ids := st.toRecord.causal
  have hsub : historyFrom st.blk y.1 ⊆ st.ids := C.history_subset_ids hyst
  have hblkr : ∀ z, (st.blk z).round = (raw z).round := fun z => by simp [Store.blk, lookup, raw]
  have hblkc : ∀ z, (st.blk z).creator = (raw z).creator := fun z => by
    simp [Store.blk, lookup, raw]
  have hAu := agreesWith_before hinj (hTH hu) (i + 1)
  have hAv := agreesWith_before hinj (hTH hv) E
  have hZb : st.base ≤ Zs.store.base := hbase
  -- each block of the history stays at `v`
  have hstays : ∀ z ∈ historyFrom st.blk y.1, Zs.store.base ≤ (raw z).round →
      Stays Zs.store Zs.pending (z, raw z) := by
    intro z hz hzb
    have hzst := hsub hz
    by_cases hcr : (raw z).creator = v
    · -- `v`'s own block, which it built before `u` received it
      have hK := hknown z hzst
      simp only [Converge.knownBefore, Set.mem_setOf_eq, List.mem_append] at hK
      rcases hK with hd | hp
      · obtain ⟨d, hdi, inp', hd', hdel⟩ := mem_delivered_before (cfg.at u) u (i + 1) hd
        obtain ⟨p, hpd, hpv, hpb⟩ := htime d u inp' hd' (hTH hu) (z, raw z) hdel
          (by simp only; rw [hcr]; exact hTH hv)
        simp only at hpv
        rw [hcr] at hpv
        obtain ⟨inpp, hp'⟩ := Converge.event_of_map hpv
        exact stays_from hl hinj (hTH hv) hnv (hknownIn z hzst)
          (built_stays hnv hp' (Converge.persists_of_broadcasts hpb)) E (by omega)
      · obtain ⟨-, h, -⟩ := (Converge.inv_before (cfg := cfg) (i + 1) u).good _ hp
        exact absurd (h.trans (rfl : (cfg.at u).me = u)) (by simp only; rw [hcr]; exact Ne.symm huv)
    · -- another's block, synchronised after `v` received `y`
      have hsy := hsync j v y.1 y.2 hj hv (by rw [hyu]; exact hu) i (by rw [hi, hyu]; rfl) hy
      rw [hyu] at hsy
      have hhor : horAt cfg tr time v (max (time j) gst + Δₛ) ≤ (st.blk z).round := by
        rw [hblkr]
        refine le_trans ?_ hzb
        exact (grows_before (cfg := cfg) (tr := tr) v (eventsBy_mono hτ)).1
      obtain ⟨k, hjk, hk, htk⟩ := hsy ht₁ z hz hhor (by rw [hblkc]; exact hcr)
      have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
      have hkE : k < E := (lt_eventsBy hmono hkl).mpr (htk.trans hτ)
      exact stays_from hl hinj (hTH hv) hnv (hknownIn z hzst)
        (stays_succ hl hinj (hTH hv) hnv (hknownIn z hzst) (Or.inr ⟨hk, hcr⟩)) E (by omega)
  -- the history is closed under references above `v`'s horizon
  have hcl : ∀ z ∈ historyFrom st.blk y.1, Zs.store.base < (raw z).round →
      ∀ r ∈ (raw z).refs, r ∈ historyFrom st.blk y.1 ∧ (raw r).round + 1 = (raw z).round := by
    intro z hz hzb r hr
    have hzst := hsub hz
    have hbz : st.blk z = raw z := Store.blk_of_lt (by change st.base < (raw z).round; omega)
    have hr' : r ∈ (st.blk z).refs := by rw [hbz]; exact hr
    refine ⟨C.history_subset_of_reaches hyst ((C.mem_history_iff hyst).mp hz)
      (C.mem_history_of_mem_refs hzst hr'), ?_⟩
    have := st.pred z hzst r hr'
    change (st.blk r).round + 1 = (st.blk z).round at this
    rw [hblkr, hblkr] at this; exact this
  -- each block of the history is valid at `v` once its references are
  have hrd : ∀ z ∈ historyFrom st.blk y.1, Zs.store.base < (raw z).round →
      (raw z).refs ⊆ Zs.store.ids → ready (cfg.at v) Zs.store (z, raw z) = true := by
    intro z hz hzb hzr
    have hzst := hsub hz
    have hbz : st.blk z = raw z := Store.blk_of_lt (by change st.base < (raw z).round; omega)
    have hagr : ∀ r ∈ (raw z).refs, (Zs.store.blk r).round = (st.blk r).round ∧
        (Zs.store.blk r).creator = (st.blk r).creator := by
      intro r hr
      have hrst : r ∈ st.ids := C.complete z hzst r (by change r ∈ (st.blk z).refs; rw [hbz]; exact hr)
      obtain ⟨a₁, a₂⟩ := hAv r (hzr hr)
      obtain ⟨b₁, b₂⟩ := hAu r hrst
      exact ⟨a₁.trans b₁.symm, a₂.trans b₂.symm⟩
    have hpred : ∀ r ∈ (raw z).refs, (st.blk r).round + 1 = (raw z).round := fun r hr => by
      have := st.pred z hzst r (by change r ∈ (st.blk z).refs; rw [hbz]; exact hr)
      change (st.blk r).round + 1 = (st.blk z).round at this
      rw [hbz] at this; exact this
    have hval : rowValid cfg.q st.blk (raw z) :=
      (Converge.inv_before (cfg := cfg) (i + 1) u).valid z hzst (by
        change st.base < (raw z).round; omega)
    simp only [ready, Bool.or_eq_true, decide_eq_true_eq]
    refine Or.inr ⟨hzr, fun r hr => by rw [(hagr r hr).1]; exact hpred r hr,
      rowValid_congr (fun r hr => ?_) hval⟩
    have hrz : r ≠ z := by
      intro h; subst h
      have := hpred r hr
      rw [← hblkr, hbz] at this
      omega
    rw [Function.update_of_ne hrz]
    exact ⟨(hagr r hr).1.symm, (hagr r hr).2.symm⟩
  have key := holds_of_stays (cfg := cfg.at v) (Converge.noReady_before (cfg := cfg) v E)
    (Z := historyFrom st.blk y.1) raw hstays hcl hrd
  by_cases hb' : Zs.store.base ≤ y.2.round
  · exact Or.inl (key y.1 mem_historyFrom_self (by rw [hry]; exact hb'))
  · exact Or.inr (not_le.mp hb')

end Arrival

/-! ## Horizons and rounds past GST -/

section Rounds

omit hnv

variable {H T : Finset Validator} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}

/-- **A reliable node's horizon reaches its peer's** after the event at
which the peer built a block, once its certificate caught up and its
held round and top reach the block's round. -/
theorem base_le_after (hq : 2 ≤ cfg.q)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    (hnr : Converge.NoRestart T tr) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hmono : Live.TimeMono tr time) {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v)
    {i : ℕ} {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp)) {n : ℕ}
    (htop : (stateBefore cfg tr i u).top.getD 0 ≤ n) {E : ℕ}
    (hE : ∀ k, k < tr.length → time k ≤ max (time i) gst + 3 * Δ → k < E)
    (ht₁ : max (time i) gst + 3 * Δ ≤ t₁) {t : ℕ} (hZt : (stateBefore cfg tr E v).top = some t)
    (hnt : n ≤ t) (hnh : n ≤ (stateBefore cfg tr E v).held) :
    (stateBefore cfg tr (i + 1) u).store.base ≤ (stateBefore cfg tr E v).store.base := by
  have hnu : ∀ k : ℕ, tr[k]? ≠ some (u, Input.restart) := fun k => hnr k u hu
  have hnv : ∀ k : ℕ, tr[k]? ≠ some (v, Input.restart) := fun k => hnr k v hv
  rcases Nat.eq_zero_or_pos (stateBefore cfg tr (i + 1) u).store.base with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  obtain ⟨r, hri, inpr, hr, -, c, hc, hcb⟩ := last_rise hnu (i + 1) hpos
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hrt : time r ≤ time i := hmono r i (by omega) hil
  have htr : (stateBefore cfg tr r u).top.getD 0 ≤ n :=
    ((rises_before (cfg := cfg) hnu (by omega : r ≤ i)).1).trans htop
  obtain ⟨l, -, hlv, htl, hcl⟩ := cert_catches hcmp hnr hdel hu hv huv hr hc (by omega)
  have hll : l < tr.length := by
    rcases h : tr[l]? with _ | x
    · rw [h] at hlv; cases hlv
    · exact (List.getElem?_eq_some_iff.mp h).1
  have hlE : l < E := hE l hll (by omega)
  have hcZ : c.height ≤ (stateBefore cfg tr E v).certHeight :=
    hcl.trans (rises_before (cfg := cfg) hnv (by omega : l + 1 ≤ E)).2.2.2
  have hSet : Settled (cfg.at v) (stateBefore cfg tr E v) := by
    rcases settled_before (cfg := cfg) hq hnv E with h | h
    · rw [hZt] at h; cases h
    · exact h
  have hcol := hSet.collected t hZt
  have hlo : (stateBefore cfg tr E v).certHeight ≤ (stateBefore cfg tr E v).lo :=
    (kept_before (cfg := cfg) hnv E).1.certHeight_le
  have hmin : min (stateBefore cfg tr E v).lo (stateBefore cfg tr E v).certHeight =
      (stateBefore cfg tr E v).certHeight := min_eq_right hlo
  rw [hmin] at hcol
  have hP : cfg.per * (c.height / cfg.m) ≤
      cfg.per * ((stateBefore cfg tr E v).certHeight / cfg.m) :=
    Nat.mul_le_mul_left _ (Nat.div_le_div_right hcZ)
  have hmm := min_le_min hP (show (stateBefore cfg tr r u).top.getD 0 ≤
    min t (stateBefore cfg tr E v).held from le_min (by omega) (by omega))
  change min (cfg.per * ((stateBefore cfg tr E v).certHeight / cfg.m))
    (min t (stateBefore cfg tr E v).held) - cfg.lag ≤ (stateBefore cfg tr E v).store.base at hcol
  omega

/-- **A reliable peer's block of a round arrives**: past GST, a reliable
node at its round `n` or above at `s` has its round-`n` block held by a
reliable node `v` after `v`'s events by `s + 3Δ + Δₛ` or later, once `v`
is at round `n` with its held round there and its horizon at or below. -/
theorem round_arrives (hq : 2 ≤ cfg.q) (hl : cfg.limit = none)
    (hinj : Converge.HashInjective cfg H tr) (htime : Converge.TimelyAuthentic cfg H tr)
    (hTH : T ⊆ H) (hnr : Converge.NoRestart T tr) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg T tr time gst Δₛ t₁)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {s n : ℕ} (hgs : gst ≤ s)
    (hus : (stateAt cfg tr time u s).top.isSome) (hun : n ≤ topAt cfg tr time u s) {τ : ℕ}
    (hτ : s + 3 * Δ + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) {t : ℕ}
    (hZt : (stateAt cfg tr time v τ).top = some t) (hnt : n ≤ t)
    (hnh : n ≤ (stateAt cfg tr time v τ).held) (hbn : (stateAt cfg tr time v τ).store.base ≤ n) :
    ∃ j ∈ (stateAt cfg tr time v τ).store.ids, ((stateAt cfg tr time v τ).store.blk j).round = n ∧
      ((stateAt cfg tr time v τ).store.blk j).creator = u := by
  have hnu : ∀ k : ℕ, tr[k]? ≠ some (u, Input.restart) := fun k => hnr k u hu
  have hnv : ∀ k : ℕ, tr[k]? ≠ some (v, Input.restart) := fun k => hnr k v hv
  obtain ⟨b, hbs, hbu, e, hep, her⟩ := built_by hnu (eventsBy tr time s) hus hun
  obtain ⟨inp, hb⟩ := Converge.event_of_map hbu
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have htb : time b ≤ s := (lt_eventsBy hmono hbl).mp hbs
  have hebc := broadcasts_of_persists hep
  obtain ⟨j, hbj, hj, htj⟩ := hdel b u inp hb hu (v, .deliver e.1 e.2)
    ⟨.broadcast e.1 e.2, mem_broadcasts.mp hebc, Ne.symm huv, rfl⟩ hv (by omega)
  have htop := top_le_built hnu hb hep
  rw [her] at htop
  have hbase := base_le_after (E := eventsBy tr time τ) hq hcmp hnr hdel hmono hu hv huv hb htop
    (fun k hk htk => (lt_eventsBy hmono hk).mpr (by omega)) (by omega) hZt hnt hnh
  rcases arrives hl hinj htime hTH hnr hmono hsync hu hv huv hb hebc hbj hj (τ := τ)
    (by omega) (by omega) hbase with hin | hlt
  · refine ⟨e.1, hin, ?_⟩
    set Z := stateAt cfg tr time v τ
    have hk := Converge.knownBefore_sub (hTH hv) (eventsBy tr time τ)
      ((Converge.inv_before (cfg := cfg) (tr := tr) (eventsBy tr time τ) v).known e.1 hin)
    have hc := Converge.content_eq hinj hk (Or.inr ⟨b, u, hbu, hTH hu, hep⟩) rfl
    have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) u).good e
      (persists_of_event hb hep)).2.1
    simp only at hc
    have hblk : Z.store.blk e.1 = atBase Z.store.base e.2 := by
      change atBase Z.store.base (Z.store.map.getD e.1 Z.store.junk) = _
      exact congrArg _ hc
    rw [hblk, atBase_round, atBase_creator]
    exact ⟨her, hgood⟩
  · rw [her] at hlt; omega

end Rounds

end Node

end LeanDag
