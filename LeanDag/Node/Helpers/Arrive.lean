import LeanDag.Node.Helpers.Shape
import LeanDag.Node.Helpers.Catch
import LeanDag.Node.Helpers.Live
/-!
# A reliable node's rounds, timers and horizon along a trace

`docs/validator.md` §13.2. Along a trace without restarts at a node: its
state changes only at its own events (`before_succ_cases`); each of its
rounds up to its top was built at one of its events, with the round's
timer (`built_by`); a round's timer, once fired, stays fired while the
top stays at or below it (`fired_stays`); and its horizon, when above
`0`, was last raised at one of its events, with an announced
certificate, to at most `Λ` below the lesser of its slot round and the
top after (`last_rise`). A reliable block arrives at a reliable node
given it once the node's horizon reaches the one its author built it at
(`arrives`), which past GST it does within `3Δ` (`base_le_after`), so a
reliable peer's block of a round arrives within `3Δ + Δₛ`
(`round_arrives`).
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

variable {v : Validator} (hnv : Steady cfg tr v)
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
      have hri : inp ≠ .restart := (hnv i _ he).1
      have hst := (hnv i _ he).2
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
        obtain ⟨e, hep, her⟩ := step_every (cfg := cfg.at v) hsi hri hst hs n hρ hn
        exact ⟨i, by omega, by rw [he]; rfl, e, by rw [outputsAt_eq he]; exact hep, her⟩

/-- **A node's top before an event is at most the round of a block it
builds there.** -/
theorem top_le_built {i : ℕ} {inp : Input Validator BlockId Payload}
    (he : tr[i]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (hep : e ∈ persists (outputsAt cfg tr i)) :
    (stateBefore cfg tr i v).top.getD 0 ≤ e.2.round := by
  rw [outputsAt_eq he] at hep
  rcases step_above (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
    (hnv i _ he).1 (hnv i _ he).2 e hep with h | ⟨h, h'⟩
  · exact h.le
  · rw [h, h']; rfl

/-- **The timer of each round a node builds is set at the same event.** -/
theorem timer_of_persist {i : ℕ} {inp : Input Validator BlockId Payload}
    (he : tr[i]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (hep : e ∈ persists (outputsAt cfg tr i)) :
    Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ outputsAt cfg tr i := by
  rw [outputsAt_eq he] at hep ⊢
  exact step_timer (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
    (hnv i _ he).1 (hnv i _ he).2 e hep

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
          (hnv k _ he).1 (hnv k _ he).2 r ih hk
    · rw [stateBefore_succ hf, if_pos rfl] at hk ⊢
      have hx : (timerState (cfg.at v) (stateBefore cfg tr f v) r).recovering = false :=
        timerState_idle (fired_before (cfg := cfg) hnv f).1 ((hnv f _ hf).2 r rfl)
      exact (settle_shape (cfg := cfg.at v) hx).fired r (Finset.mem_insert_self _ _) hk

/-- **A horizon above `0` was last raised at one of the node's events**,
with an announced certificate, to at most `Λ` below the lesser of its
slot round and the top after. -/
theorem last_rise : ∀ (i : ℕ), 0 < (stateBefore cfg tr i v).store.base →
    ∃ r < i, ∃ inp, tr[r]? = some (v, inp) ∧
      (stateBefore cfg tr (r + 1) v).store.base = (stateBefore cfg tr i v).store.base ∧
      ∃ c, Output.announce c ∈ outputsAt cfg tr r ∧
        (stateBefore cfg tr i v).store.base ≤
          min (cfg.per * ((c.height - 1) / cfg.m)) ((stateBefore cfg tr (r + 1) v).top.getD 0) - cfg.lag
  | 0, h => by simp [stateBefore, inputsBefore, run, State.init, Store.empty] at h
  | i + 1, h => by
    have hmono := (grows_before (cfg := cfg) (tr := tr) v (Nat.le_succ i)).1
    by_cases hlt : (stateBefore cfg tr i v).store.base < (stateBefore cfg tr (i + 1) v).store.base
    · rcases before_succ_cases (cfg := cfg) (tr := tr) v i with heq | ⟨inp, he, heq⟩
      · rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
      · rw [heq] at hlt
        obtain ⟨c, hc, hcb⟩ := step_rise (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
          (hnv i _ he).1 (hnv i _ he).2 hlt
        refine ⟨i, by omega, inp, he, rfl, c, by rw [outputsAt_eq he]; exact hc, ?_⟩
        rw [heq]; exact hcb
    · have heq : (stateBefore cfg tr (i + 1) v).store.base =
          (stateBefore cfg tr i v).store.base := le_antisymm (not_lt.mp hlt) hmono
      obtain ⟨r, hr, inp, he, hb, c, hc, hcb⟩ := last_rise i (by rw [← heq]; exact h)
      exact ⟨r, by omega, inp, he, hb.trans heq.symm, c, hc, by rw [heq]; exact hcb⟩

omit hnv in
/-- **A block a node builds at an event stays** from the next event on. -/
theorem built_stays {p : ℕ} {inp : Input Validator BlockId Payload}
    (hnv' : Steady cfg tr v) (hp : tr[p]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ persists (outputsAt cfg tr p)) :
    Stays (stateBefore cfg tr (p + 1) v).store (stateBefore cfg tr (p + 1) v).pending x := by
  rw [outputsAt_eq hp] at hx
  rw [stateBefore_succ hp, if_pos rfl]
  rcases step_keeps_built (cfg := cfg.at v) (fired_before (cfg := cfg) hnv' p).1
    (hnv' p _ hp).1 (hnv' p _ hp).2 x hx with ⟨h, -⟩ | h
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
      (settle_shape (cfg := cfg.at v) hx).rises.2.1 hxt
    exact key _ rfl rfl
  · have hstep : (Node.step (cfg.at v) s .start).1 = s := by
      simp only [Node.step, if_neg (fun h : s.top = none ∧ (cfg.at v).Admissible => hn h.1)]
    rw [hstep]
    exact Option.ne_none_iff_isSome.mp hn

/-! ## The blocks the honest nodes know -/

section Known

omit hnv

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

/-- **A path through a store's blocks above its horizon** is one through
the blocks known, when the store's blocks are the ones known. -/
theorem reaches_known {st : Store Validator BlockId Payload}
    (hst : ∀ w ∈ st.ids, Live.knownBlock cfg H tr w = st.map.getD w st.junk) {r : BlockId}
    (hr : r ∈ st.ids) {z : BlockId} (h : ReachesFrom st.blk r z) :
    ReachesFrom (Live.knownBlock cfg H tr) r z ∧ z ∈ st.ids := by
  induction h with
  | refl => exact ⟨ReachesFrom.refl, hr⟩
  | tail hrw hstep ih =>
    rename_i w z'
    obtain ⟨ih₁, hw⟩ := ih
    have hlt : st.base < (st.map.getD w st.junk).round := by
      by_contra hle
      have : (st.blk w).refs = ∅ := by
        unfold Store.blk lookup atBase; rw [if_pos (not_lt.mp hle)]
      change z' ∈ (st.blk w).refs at hstep
      rw [this] at hstep; cases hstep
    have hbw : st.blk w = Live.knownBlock cfg H tr w := (Store.blk_of_lt hlt).trans (hst w hw).symm
    refine ⟨ih₁.trans (ReachesFrom.single ?_), st.complete w hw z' hstep⟩
    change z' ∈ (st.blk w).refs at hstep
    rw [hbw] at hstep; exact hstep

end Known

/-! ## Arrival -/

section Arrival

omit hnv

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δₛ t₁ : ℕ}

/-- **A reliable block arrives** at a reliable node `v` given it: once
`v`'s horizon reaches the one its author built it at, `v` holds it, or it
lies below `v`'s horizon, after `v`'s events up to a time by which its
history was synchronised, provided `v` is at the round below it. -/
theorem arrives (hinj : Converge.HashInjective cfg H tr)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H) (hnr : ∀ v ∈ T, Steady cfg tr v)
    (hmono : Live.TimeMono tr time) (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp))
    {y : BlockId × Block Validator BlockId Payload} (hy : y ∈ persists (outputsAt cfg tr i))
    {U : BlockRecord Validator BlockId Payload P H} {A : Set (Cert Validator BlockId)}
    {x : State Validator BlockId Payload}
    (hx : BuildState (cfg.at u) U (knownAll cfg H tr) A (stateBefore cfg tr i u) inp x)
    {y' : State Validator BlockId Payload} {o : List (Output Validator BlockId Payload)}
    (hb : tryBuild (cfg.at u) x = some (y', o)) (hyo : y ∈ persists o)
    {j : ℕ} (hij : i < j) (hj : tr[j]? = some (v, .deliver y.1 y.2)) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (ht₁ : max (time j) gst + Δₛ ≤ t₁)
    (hbase : x.store.base ≤ (stateAt cfg tr time v τ).store.base)
    (hZs : (stateAt cfg tr time v τ).top.isSome)
    (hZn : y.2.round ≤ (stateAt cfg tr time v τ).top.getD 0 + 1) :
    y.1 ∈ (stateAt cfg tr time v τ).store.ids ∨
      y.2.round < (stateAt cfg tr time v τ).store.base := by
  have hnv : Steady cfg tr v := hnr v hv
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ :=
    (lt_eventsBy hmono hjl).mpr (le_trans (le_max_left _ _) (le_trans (Nat.le_add_right _ _) hτ))
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).store.ids ∨
    y.2.round < (stateBefore cfg tr (eventsBy tr time τ) v).store.base
  change _ ≤ (stateBefore cfg tr (eventsBy tr time τ) v).store.base at hbase
  change (stateBefore cfg tr (eventsBy tr time τ) v).top.isSome at hZs
  change _ ≤ (stateBefore cfg tr (eventsBy tr time τ) v).top.getD 0 + 1 at hZn
  set E := eventsBy tr time τ with hE
  set Zs := stateBefore cfg tr E v with hZsdef
  -- the build
  obtain ⟨r', id', b', hnew, hab, hrefs, hpred, hxt, hbr, hbc, hid, hrv, -, -, -, -, hout⟩ :=
    tryBuild_some hb
  rw [hout, persists_built, List.mem_singleton] at hyo
  subst hyo
  simp only at hj hZn ⊢
  have hxb : x.store.base < b'.round := by have := hx.held.le_top r' hxt; omega
  have hrefs' := hrefs hxb
  have hpred' := hpred hxb
  obtain ⟨B, hiX⟩ := hx.inv
  set raw := Live.knownBlock cfg H tr with hraw
  have hknX : ∀ w ∈ x.store.ids, (w, x.store.map.getD w x.store.junk) ∈ Converge.knownIn cfg H tr :=
    fun w hw => by
      obtain ⟨v', hv', hk⟩ := hiX.known w hw
      exact knownOf_sub hv' hk
  have hstK : ∀ w ∈ x.store.ids, raw w = x.store.map.getD w x.store.junk := fun w hw =>
    knownBlock_eq hinj (hknX w hw)
  have hyK : ((id', b') : BlockId × Block Validator BlockId Payload) ∈ Converge.knownIn cfg H tr :=
    Or.inr ⟨i, u, by rw [hi]; rfl, hTH hu, hy⟩
  have hry : raw id' = b' := knownBlock_eq hinj hyK
  have hbu : b'.creator = u := hbc
  have C : CausalStructure x.store.blk x.store.ids := x.store.toRecord.causal
  have hrawx : ∀ w ∈ x.store.ids, (raw w).round = (x.store.blk w).round ∧
      (raw w).creator = (x.store.blk w).creator := fun w hw => by
    rw [hstK w hw]; simp [Store.blk, lookup]
  have hAv := agreesWith_before hinj (hTH hv) E
  have hZv : ∀ w ∈ Zs.store.ids, (Zs.store.blk w).round = (raw w).round ∧
      (Zs.store.blk w).creator = (raw w).creator := fun w hw => by
    obtain ⟨a₁, a₂⟩ := hAv w hw
    obtain ⟨k₁, k₂⟩ := knownBlock_gT (cfg := cfg) (H := H) (tr := tr) w
    exact ⟨a₁.trans k₁.symm, a₂.trans k₂.symm⟩
  -- the history the author built on
  let Z : Finset BlockId := insert id' (b'.refs.biUnion (historyFrom x.store.blk))
  have hZmem : ∀ z ∈ Z, z = id' ∨ ∃ r ∈ b'.refs, z ∈ historyFrom x.store.blk r ∧ z ∈ x.store.ids :=
    fun z hz => by
      rcases Finset.mem_insert.mp hz with h | h
      · exact Or.inl h
      · obtain ⟨r, hr, hzr⟩ := Finset.mem_biUnion.mp h
        exact Or.inr ⟨r, hr, hzr, C.history_subset_ids (hrefs' hr) hzr⟩
  -- each of its blocks stays at `v`
  have hstays : ∀ z ∈ Z, Zs.store.base ≤ (raw z).round → Stays Zs.store Zs.pending (z, raw z) := by
    intro z hz hzb
    rcases hZmem z hz with rfl | ⟨r, hr, hzr, hzx⟩
    · rw [hry]
      exact stays_from hinj (hTH hv) hnv hyK
        (stays_succ hinj (hTH hv) hnv hyK (Or.inr ⟨hj, by rw [hbu]; exact huv⟩)) E (by omega)
    · set xz : BlockId × Block Validator BlockId Payload := (z, x.store.map.getD z x.store.junk)
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
          have h₁ := C.round_le_of_mem_history (hrefs' hr) hzr
          have h₂ := hpred' r hr
          have h₃ : (x.store.blk z).round = xz.2.round := by simp [xz, Store.blk, lookup]
          omega
        obtain ⟨bρ, hbρE, hbρv, e, he, her⟩ := built_by hnv E hZs hρ
        obtain ⟨inpρ, hbρ⟩ := Converge.event_of_map hbρv
        have hep : e ∈ persists (runOf cfg tr v).2 :=
          mem_persists_iff.mpr (mem_outputs_of_event hbρ (mem_persists_iff.mp he))
        have hex : e = xz := eq_of_persists v hep hxzp her
        rw [hex] at he
        exact stays_from hinj (hTH hv) hnv hxzK (built_stays hnv hbρ he) E (by omega)
      · -- another's, synchronised after `v` received the author's block
        have hreach : ReachesFrom raw id' z := by
          refine ReachesFrom.of_mem_refs (by rw [hry]; exact hr) ?_
          exact (reaches_known hstK (hrefs' hr) (reaches_of_mem_historyUptoFrom hzr)).1
        have hhor : horAt cfg tr time v (max (time j) gst + Δₛ) ≤ xz.2.round := by
          rw [← hrz]
          exact le_trans (grows_before (cfg := cfg) (tr := tr) v (eventsBy_mono hτ)).1 hzb
        obtain ⟨k, hjk, hk, htk⟩ := hsync j v id' b' hj hv (by rw [hbu]; exact hu) hid ht₁ xz
          hxzK hreach hhor hcr
        have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
        have hkE : k < E := (lt_eventsBy hmono hkl).mpr (htk.trans hτ)
        exact stays_from hinj (hTH hv) hnv hxzK
          (stays_succ hinj (hTH hv) hnv hxzK (Or.inr ⟨hk, hcr⟩)) E (by omega)
  -- it is closed under references above `v`'s horizon
  have hcl : ∀ z ∈ Z, Zs.store.base < (raw z).round →
      ∀ r ∈ (raw z).refs, r ∈ Z ∧ (raw r).round + 1 = (raw z).round := by
    intro z hz hzb r hr
    rcases hZmem z hz with rfl | ⟨r₀, hr₀, hzr, hzx⟩
    · rw [hry] at hr ⊢
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, mem_historyFrom_self⟩), ?_⟩
      rw [(hrawx r (hrefs' hr)).1]; exact hpred' r hr
    · have hbz : x.store.blk z = raw z := by
        rw [hstK z hzx]
        exact Store.blk_of_lt (by rw [← hstK z hzx]; omega)
      have hr' : r ∈ (x.store.blk z).refs := by rw [hbz]; exact hr
      have hrx := C.complete z hzx r hr'
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r₀, hr₀,
        C.history_subset_of_reaches (hrefs' hr₀) ((C.mem_history_iff (hrefs' hr₀)).mp hzr)
          (C.mem_history_of_mem_refs hzx hr')⟩), ?_⟩
      rw [(hrawx r hrx).1, ← hbz]; exact C.refs_round z hzx r hr'
  -- and valid at `v` once its references are
  have hrd : ∀ z ∈ Z, Zs.store.base < (raw z).round → (raw z).refs ⊆ Zs.store.ids →
      ready (cfg.at v) Zs.store (z, raw z) = true := by
    intro z hz hzb hzr
    have hcl' := hcl z hz hzb
    simp only [ready, Bool.or_eq_true, decide_eq_true_eq]
    refine Or.inr ⟨hzr, fun r hr => by rw [(hZv r (hzr hr)).1]; exact (hcl' r hr).2, ?_⟩
    have hne : ∀ r ∈ (raw z).refs, r ≠ z := fun r hr h => by
      have := (hcl' r hr).2; rw [h] at this; omega
    rcases hZmem z hz with rfl | ⟨r₀, hr₀, hzr₀, hzx⟩
    · rw [hry] at hzr hne ⊢
      refine rowValid_congr (fun r hr => ?_) hrv
      rw [Function.update_of_ne (fun h => hnew (by rw [← h]; exact hrefs' hr)),
        Function.update_of_ne (hne r hr)]
      rw [(hZv r (hzr hr)).1, (hZv r (hzr hr)).2, (hrawx r (hrefs' hr)).1, (hrawx r (hrefs' hr)).2]
      exact ⟨rfl, rfl⟩
    · have hval := hiX.valid z hzx (by rw [← hstK z hzx]; omega)
      rw [← hstK z hzx] at hval
      have hbz : x.store.blk z = raw z := by
        rw [hstK z hzx]
        exact Store.blk_of_lt (by rw [← hstK z hzx]; omega)
      refine rowValid_congr (fun r hr => ?_) hval
      have hrx : r ∈ x.store.ids := C.complete z hzx r (by rw [hbz]; exact hr)
      rw [Function.update_of_ne (hne r hr), (hZv r (hzr hr)).1, (hZv r (hzr hr)).2,
        (hrawx r hrx).1, (hrawx r hrx).2]
      exact ⟨rfl, rfl⟩
  have key := holds_of_stays (cfg := cfg.at v) (Converge.noReady_before (cfg := cfg) v E)
    (Z := Z) raw hstays hcl hrd
  by_cases hb' : Zs.store.base ≤ b'.round
  · exact Or.inl (key id' (Finset.mem_insert_self _ _) (by rw [hry]; exact hb'))
  · exact Or.inr (not_le.mp hb')

/-- **A reliable genesis block arrives** at a reliable node given it, at
horizon `0`. -/
theorem arrives_zero (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hnr : ∀ v ∈ T, Steady cfg tr v) (hmono : Live.TimeMono tr time)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {i : ℕ}
    (hiu : (tr[i]?.map Prod.fst) = some u)
    {y : BlockId × Block Validator BlockId Payload} (hy : y ∈ persists (outputsAt cfg tr i))
    (hyu : y.2.creator = u) (hy0 : y.2.round = 0)
    {j : ℕ} (hj : tr[j]? = some (v, .deliver y.1 y.2)) {τ : ℕ} (hjτ : time j ≤ τ)
    (hb0 : (stateAt cfg tr time v τ).store.base = 0) :
    y.1 ∈ (stateAt cfg tr time v τ).store.ids := by
  have hnv : Steady cfg tr v := hnr v hv
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ := (lt_eventsBy hmono hjl).mpr hjτ
  have hyK : y ∈ Converge.knownIn cfg H tr := Or.inr ⟨i, u, hiu, hTH hu, hy⟩
  have hst := stays_from hinj (hTH hv) hnv hyK
    (stays_succ hinj (hTH hv) hnv hyK (Or.inr ⟨hj, by rw [hyu]; exact huv⟩))
    (eventsBy tr time τ) (by omega)
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).store.ids
  change (stateBefore cfg tr (eventsBy tr time τ) v).store.base = 0 at hb0
  rcases hst with h | h | h
  · exact h
  · have := Converge.noReady_before (cfg := cfg) (tr := tr) v (eventsBy tr time τ) y h
    simp [ready, hb0, hy0] at this
  · rw [hb0] at h; omega

end Arrival

/-! ## Horizons and rounds past GST -/

section Rounds

omit hnv

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

/-- **A reliable node's horizon reaches the one its peer built a block
at**, once its certificate caught up with the one that raised the peer's
horizon, and its top reaches the round the peer built on. -/
theorem base_le_after (hq : 2 ≤ cfg.q)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    (hnr : ∀ v ∈ T, Steady cfg tr v) (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hmono : Live.TimeMono tr time) {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v)
    {i : ℕ} {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp))
    {U : BlockRecord Validator BlockId Payload P H} {K : Set (BlockId × Block Validator BlockId Payload)}
    {x : State Validator BlockId Payload}
    (hx : BuildState (cfg.at u) U K {c | Output.announce c ∈ outputsAt cfg tr i}
      (stateBefore cfg tr i u) inp x)
    {r' : ℕ} (hxt : x.top = some r') (htop : (stateBefore cfg tr i u).top.getD 0 ≤ r') {E : ℕ}
    (hE : ∀ k, k < tr.length → time k ≤ max (time i) gst + 3 * Δ → k < E)
    (ht₁ : max (time i) gst + 3 * Δ ≤ t₁) {t : ℕ} (hZt : (stateBefore cfg tr E v).top = some t)
    (hrt : r' ≤ t) : x.store.base ≤ (stateBefore cfg tr E v).store.base := by
  have hnu : Steady cfg tr u := hnr u hu
  have hnv : Steady cfg tr v := hnr v hv
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  -- the certificate that raised the peer's horizon, announced by event `i`, and its bound
  have hcase : x.store.base = 0 ∨ ∃ e ≤ i, ∃ inpe, tr[e]? = some (u, inpe) ∧ ∃ c,
      Output.announce c ∈ outputsAt cfg tr e ∧
      x.store.base ≤ min (cfg.per * ((c.height - 1) / cfg.m)) r' - cfg.lag := by
    rcases hx.rise with h | ⟨c, hc, hcb⟩
    · rcases Nat.eq_zero_or_pos (stateBefore cfg tr i u).store.base with h0 | hpos
      · exact Or.inl (h.trans h0)
      · obtain ⟨r, hri, inpr, hr, -, c, hc, hcb⟩ := last_rise hnu i hpos
        have h₁ := (rises_before (cfg := cfg) hnu (show r + 1 ≤ i by omega)).1
        refine Or.inr ⟨r, by omega, inpr, hr, c, hc, ?_⟩
        rw [h]
        have := min_le_min (le_refl (cfg.per * ((c.height - 1) / cfg.m))) (h₁.trans htop)
        omega
    · refine Or.inr ⟨i, le_rfl, inp, hi, c, hc, ?_⟩
      rw [hxt] at hcb
      exact hcb
  rcases hcase with h0 | ⟨e, hei, inpe, he, c, hc, hcb⟩
  · rw [h0]; exact Nat.zero_le _
  have hel : e < tr.length := (List.getElem?_eq_some_iff.mp he).1
  have het : time e ≤ time i := hmono e i hei hil
  obtain ⟨l, -, hlv, htl, hcl⟩ := cert_catches hcmp hnr hdel hu hv huv he hc (by omega)
  have hll : l < tr.length := by
    rcases h : tr[l]? with _ | z
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
  rw [horizonAt_of (fired_before (cfg := cfg) hnv E).1] at hcol
  change min (cfg.per * ((min (stateBefore cfg tr E v).lo (stateBefore cfg tr E v).certHeight - 1) /
    cfg.m)) t - cfg.lag ≤ (stateBefore cfg tr E v).store.base at hcol
  rw [hmin] at hcol
  have hP : cfg.per * ((c.height - 1) / cfg.m) ≤
      cfg.per * (((stateBefore cfg tr E v).certHeight - 1) / cfg.m) :=
    Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.sub_le_sub_right hcZ 1))
  have hmm := min_le_min hP hrt
  omega

/-- **A reliable peer's block arrives**: a block a reliable node built at
an event at or before `s`, past GST, is held by a reliable node `v` after
`v`'s events by `max s gst + 3Δ + Δₛ` or later, once `v` is at the round
below the block's or above, with its horizon at or below the block's
round. -/
theorem block_arrives (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hchain : Boot.ChainInjective cfg H tr)
    (hTH : T ⊆ H) (hnr : ∀ v ∈ T, Steady cfg tr v) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {b : ℕ}
    {inp : Input Validator BlockId Payload} (hb : tr[b]? = some (u, inp))
    {e : BlockId × Block Validator BlockId Payload} (hep : e ∈ persists (outputsAt cfg tr b))
    {s : ℕ} (htb : time b ≤ s) {τ : ℕ} (hτ : max s gst + 3 * Δ + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) {t : ℕ}
    (hZt : (stateAt cfg tr time v τ).top = some t) (hnt : e.2.round ≤ t + 1)
    (hbn : (stateAt cfg tr time v τ).store.base ≤ e.2.round) :
    e.1 ∈ (stateAt cfg tr time v τ).store.ids ∧
      ((stateAt cfg tr time v τ).store.blk e.1).round = e.2.round ∧
      ((stateAt cfg tr time v τ).store.blk e.1).creator = u ∧
      (stateAt cfg tr time v τ).store.blk e.1 = atBase (stateAt cfg tr time v τ).store.base e.2 := by
  have hnu : Steady cfg tr u := hnr u hu
  have hbu : (tr[b]?.map Prod.fst) = some u := by rw [hb]; rfl
  have hebc := broadcasts_of_persists hep
  obtain ⟨j, hbj, hj, htj⟩ := hdel b u inp hb hu (v, .deliver e.1 e.2)
    ⟨.broadcast e.1 e.2, mem_broadcasts.mp hebc, Ne.symm huv, rfl⟩ hv (by omega)
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) u).good e
    (persists_of_event hb hep)).2.1
  -- `v` holds the block
  have hin : e.1 ∈ (stateAt cfg tr time v τ).store.ids := by
    by_cases hn0 : e.2.round = 0
    · exact arrives_zero hinj hTH hnr hmono hu hv huv hbu hep hgood hn0 hj
        (by omega) (by omega)
    · obtain ⟨x, y', o, hx, hxb, heo⟩ := build_witness hσ hadm hf htime hcert hinj hchain
        (hTH hu) hnu hb hep hn0
      obtain ⟨r', id', b', -, -, -, -, hxt, hbr, -, -, -, -, -, -, -, hout⟩ := tryBuild_some hxb
      rw [hout, persists_built, List.mem_singleton] at heo
      have hr' : r' + 1 = e.2.round := by rw [heo, hbr]
      have htop : (stateBefore cfg tr b u).top.getD 0 ≤ r' := by
        have := step_above (cfg := cfg.at u) (inp := inp) (fired_before (cfg := cfg) hnu b).1
          (hnu b _ hb).1 (hnu b _ hb).2 e (by rw [← outputsAt_eq hb]; exact hep)
        rcases this with h | ⟨-, h⟩ <;> omega
      have hbase := base_le_after (E := eventsBy tr time τ) hq hcmp hnr hdel hmono hu hv huv hb hx
        hxt htop (fun k hk htk => (lt_eventsBy hmono hk).mpr (by omega)) (by omega) hZt
        (by omega)
      have hZs : (stateAt cfg tr time v τ).top.isSome := by rw [hZt]; rfl
      rcases arrives hinj htime hTH hnr hmono hsync hu hv huv hb hep hx hxb
        (by rw [hout, persists_built, heo]; exact List.mem_singleton_self _) hbj hj (τ := τ)
        (by omega) (by omega) hbase hZs (by rw [hZt]; simp; omega) with h | h
      · exact h
      · omega
  refine ⟨hin, ?_⟩
  set Z := stateAt cfg tr time v τ
  have hk := Converge.knownBefore_sub (hTH hv) (eventsBy tr time τ)
    ((Converge.inv_before (cfg := cfg) (tr := tr) (eventsBy tr time τ) v).known e.1 hin)
  have hc := Converge.content_eq hinj hk (Or.inr ⟨b, u, hbu, hTH hu, hep⟩) rfl
  simp only at hc
  have hblk : Z.store.blk e.1 = atBase Z.store.base e.2 := by
    change atBase Z.store.base (Z.store.map.getD e.1 Z.store.junk) = _
    exact congrArg _ hc
  exact ⟨by rw [hblk, atBase_round], by rw [hblk, atBase_creator]; exact hgood, hblk⟩

/-- **A reliable peer's block of a round arrives**: past GST, a reliable
node at its round `n` or above at `s` has its round-`n` block held by a
reliable node `v` after `v`'s events by `s + 3Δ + Δₛ` or later, once `v`
is at round `n` or above with its horizon at or below `n`. -/
theorem round_arrives (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hchain : Boot.ChainInjective cfg H tr)
    (hTH : T ⊆ H) (hnr : ∀ v ∈ T, Steady cfg tr v) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
    (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j v).decided.reverse ∨
        (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {s n : ℕ} (hgs : gst ≤ s)
    (hus : (stateAt cfg tr time u s).top.isSome) (hun : n ≤ topAt cfg tr time u s) {τ : ℕ}
    (hτ : s + 3 * Δ + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) {t : ℕ}
    (hZt : (stateAt cfg tr time v τ).top = some t) (hnt : n ≤ t)
    (hbn : (stateAt cfg tr time v τ).store.base ≤ n) :
    ∃ j ∈ (stateAt cfg tr time v τ).store.ids, ((stateAt cfg tr time v τ).store.blk j).round = n ∧
      ((stateAt cfg tr time v τ).store.blk j).creator = u := by
  have hnu : Steady cfg tr u := hnr u hu
  obtain ⟨b, hbs, hbu, e, hep, her⟩ := built_by hnu (eventsBy tr time s) hus hun
  obtain ⟨inp, hb⟩ := Converge.event_of_map hbu
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have htb : time b ≤ s := (lt_eventsBy hmono hbl).mp hbs
  obtain ⟨h₁, h₂, h₃, -⟩ := block_arrives hq hσ hadm hf htime hcert hinj hchain hTH hnr
    hmono hdel hsync hcmp hu hv huv hb hep htb (τ := τ) (by omega) ht₁ hZt (by omega)
    (by omega)
  exact ⟨e.1, h₁, h₂.trans her, h₃⟩

end Rounds

end Node

end LeanDag
