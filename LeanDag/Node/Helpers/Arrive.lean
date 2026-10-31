import LeanDag.Node.Helpers.Shape
import LeanDag.Node.Helpers.Live
/-!
# A reliable node's rounds and timers, and the arrival of blocks

`docs/validator.md` §5.2. Along a trace, a node's state changes only at
its own events (`before_succ_cases`). Each of its rounds up to its top was
built at one of its events, with the retry timer, when it did not jump
(`built_by`, `timer_of_persist`), and past `G` no reliable node jumps
(`Arrival.no_jump`). A round's timer, once fired, stays fired while
the node's top is not above the round (`fired_stays`). A reliable block
that a reliable node `v` is given is held by `v` once its history has
been synchronised (`arrives`,
`arrives_zero`). Past GST a reliable node's block built at `s` is
therefore held by every reliable node by `max s gst + Δ + Δₛ`
(`arrival_of_delivered`). The liveness argument reads arrival only for
blocks at their author's round at `G` or above (`Arrival`), so for a
node's top block past `G` (`top_arrives`); a block held is as built
(`held_as_built`).
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

/-- **A node's top round was built** at one of its earlier events. -/
theorem built_top : ∀ (i : ℕ), (stateBefore cfg tr i v).top.isSome →
    ∃ b < i, (tr[b]?.map Prod.fst) = some v ∧ ∃ e ∈ persists (outputsAt cfg tr b),
      e.2.round = (stateBefore cfg tr i v).top.getD 0
  | 0, hs => by simp [stateBefore, inputsBefore, run, State.init] at hs
  | i + 1, hs => by
    rcases before_succ_cases (cfg := cfg) (tr := tr) v i with heq | ⟨inp, he, heq⟩
    · rw [heq] at hs ⊢
      obtain ⟨b, hb, h⟩ := built_top i hs
      exact ⟨b, by omega, h⟩
    · by_cases hsame : (stateBefore cfg tr (i + 1) v).top = (stateBefore cfg tr i v).top
      · rw [hsame] at hs ⊢
        obtain ⟨b, hb, h⟩ := built_top i hs
        exact ⟨b, by omega, h⟩
      · rw [heq] at hsame ⊢
        obtain ⟨e, hep, het⟩ := step_built_top (cfg := cfg.at v) hsame
        exact ⟨i, by omega, by rw [he]; rfl, e, by rw [outputsAt_eq he]; exact hep,
          by rw [het]; rfl⟩

/-- **Each round up to a node's top was built** at one of its earlier
events, if no step it took recovering, or restarting, reached the
round. -/
theorem built_by : ∀ (i : ℕ) {n : ℕ}, (stateBefore cfg tr i v).top.isSome →
    n ≤ (stateBefore cfg tr i v).top.getD 0 →
    (∀ k < i, ∀ inp, tr[k]? = some (v, inp) →
      ((stateBefore cfg tr k v).recovering = true ∨ inp = .restart) →
      (stateBefore cfg tr (k + 1) v).top.getD 0 < n) →
    ∃ b < i, (tr[b]?.map Prod.fst) = some v ∧ ∃ e ∈ persists (outputsAt cfg tr b), e.2.round = n
  | 0, n, hs, _, _ => by simp [stateBefore, inputsBefore, run, State.init] at hs
  | i + 1, n, hs, hn, hj => by
    have hj' : ∀ k < i, ∀ inp, tr[k]? = some (v, inp) →
        ((stateBefore cfg tr k v).recovering = true ∨ inp = .restart) →
        (stateBefore cfg tr (k + 1) v).top.getD 0 < n := fun k hk => hj k (by omega)
    rcases before_succ_cases (cfg := cfg) (tr := tr) v i with heq | ⟨inp, he, heq⟩
    · rw [heq] at hs hn
      obtain ⟨b, hb, h⟩ := built_by i hs hn hj'
      exact ⟨b, by omega, h⟩
    · by_cases hold : (stateBefore cfg tr i v).top.isSome ∧
          n ≤ (stateBefore cfg tr i v).top.getD 0
      · obtain ⟨b, hb, h⟩ := built_by i hold.1 hold.2 hj'
        exact ⟨b, by omega, h⟩
      · have hnot : ¬ ((stateBefore cfg tr i v).recovering = true ∨ inp = .restart) :=
          fun hr => by have := hj i (by omega) inp he hr; omega
        push Not at hnot
        rw [heq] at hs hn
        have hρ : (stateBefore cfg tr i v).top = none ∨
            (stateBefore cfg tr i v).top.getD 0 < n := by
          rcases h : (stateBefore cfg tr i v).top with _ | t
          · exact Or.inl rfl
          · right; rw [h] at hold; simp at hold; simp; omega
        obtain ⟨e, hep, her⟩ := step_every (cfg := cfg.at v) hnot.2
          (Or.inl (by simpa using hnot.1)) hs n hρ hn
        exact ⟨i, by omega, by rw [he]; rfl, e, by rw [outputsAt_eq he]; exact hep, her⟩

/-- **A node recovering at an event restarted before**, at an event after
which it had no timer and no restart up to this one, and kept its top. -/
theorem recovering_restart : ∀ (k : ℕ), (stateBefore cfg tr k v).recovering = true →
    ∃ j < k, tr[j]? = some (v, .restart) ∧
      (∀ m inp, j < m → m < k → tr[m]? = some (v, inp) →
        inp ≠ .restart ∧ ∀ r, inp ≠ .timer r) ∧
      (stateBefore cfg tr k v).top = (stateBefore cfg tr j v).top
  | 0, h => by simp [stateBefore, inputsBefore, run, State.init] at h
  | k + 1, h => by
    -- the event at `k`, if not `v`'s, leaves `v` alone
    have hother : (∀ inp', tr[k]? ≠ some (v, inp')) →
        stateBefore cfg tr (k + 1) v = stateBefore cfg tr k v := by
      intro hno
      rcases he : tr[k]? with _ | ⟨w, inp''⟩
      · exact stateBefore_of_none he
      · rw [stateBefore_succ he]
        split
        · rename_i hw; subst hw
          exact absurd he (hno inp'')
        · rfl
    by_cases hv : ∃ inp, tr[k]? = some (v, inp)
    · obtain ⟨inp, he⟩ := hv
      rw [stateBefore_succ he, if_pos rfl] at h ⊢
      obtain ⟨htop, htimer, hcase⟩ := step_recovering (cfg := cfg.at v) h
      by_cases hr : inp = .restart
      · subst hr
        exact ⟨k, by omega, he, fun m _ hkm hmk _ => absurd hmk (by omega), htop⟩
      · rcases hcase with hcase | hcase
        · exact absurd hcase hr
        · obtain ⟨j, hj, hjr, hno, htop'⟩ := recovering_restart k hcase
          refine ⟨j, by omega, hjr, fun m inp' hjm hmk hm => ?_, htop.trans htop'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hmk with hmk | rfl
          · exact hno m inp' hjm hmk hm
          · rw [he] at hm
            cases hm
            exact ⟨hr, htimer⟩
    · push Not at hv
      have heq := hother hv
      rw [heq] at h ⊢
      obtain ⟨j, hj, hjr, hno, htop⟩ := recovering_restart k h
      refine ⟨j, by omega, hjr, fun m inp hjm hmk hm => ?_, htop⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmk with hmk | rfl
      · exact hno m inp hjm hmk hm
      · exact absurd hm (hv inp)

/-- **The retry timer of each round a node builds is set at the same
event**: the timer of the round below it, for twice its timeout. -/
theorem timer_of_persist {i : ℕ} {inp : Input Validator BlockId Payload}
    (he : tr[i]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (hep : e ∈ persists (outputsAt cfg tr i)) :
    Output.setTimer (e.2.round - 1) (2 * cfg.timeout (e.2.round - 1)) ∈ outputsAt cfg tr i := by
  rw [outputsAt_eq he] at hep ⊢
  exact step_timer (cfg := cfg.at v) e hep

/-- **A fired timer stays fired** at every later event while the node's
top is not above its round. -/
theorem fired_stays {f r : ℕ} (hf : tr[f]? = some (v, Input.timer r)) :
    ∀ k, f < k → (stateBefore cfg tr k v).top.getD 0 ≤ r → r ∈ (stateBefore cfg tr k v).fired
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, hfk, htk => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hfk with hlt | rfl
    · have htk' : (stateBefore cfg tr k v).top.getD 0 ≤ r :=
        ((rises_before (cfg := cfg) (tr := tr) v (Nat.le_succ k)).1).trans htk
      have ih := fired_stays hf k hlt htk'
      rcases before_succ_cases (cfg := cfg) (tr := tr) v k with heq | ⟨inp, -, heq⟩
      · rw [heq]; exact ih
      · rw [heq]
        exact step_fired (cfg := cfg.at v) ih htk'
    · rw [stateBefore_succ hf, if_pos rfl, step_timer_fst]
      exact (settle_shape (cfg := cfg.at v)
        { stateBefore cfg tr f v with
            fired := fire (stateBefore cfg tr f v) r, recovering := false }).fired
        (Finset.mem_insert_self _ _)

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

/-- **A node persists a block of a round at one event only**: its own
blocks lie at strictly increasing rounds (V1). -/
theorem persist_events_eq {j j' : ℕ} {inp inp' : Input Validator BlockId Payload}
    (hj : tr[j]? = some (v, inp)) (hj' : tr[j']? = some (v, inp'))
    {e e' : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr j))
    (he' : e' ∈ persists (outputsAt cfg tr j')) (hr : e.2.round = e'.2.round) : j = j' := by
  by_contra hne
  wlog hlt : j < j' generalizing j j' inp inp' e e'
  · exact this hj' hj he' he hr.symm (Ne.symm hne) (by omega)
  have hpw := Local.oneEach _ _ _ (cfg.at v) (inputsBefore tr (j' + 1) v)
  dsimp only at hpw
  rw [inputsBefore_succ hj', if_pos rfl, run_append_single, persists_append] at hpw
  have hA := persists_before_mono (cfg := cfg) (tr := tr) v (show j + 1 ≤ j' by omega) e
    (persists_of_event hj he)
  rw [outputsAt_eq hj'] at he'
  rw [List.map_append, List.pairwise_append] at hpw
  have := hpw.2.2 _ (List.mem_map.mpr ⟨e, hA, rfl⟩) _ (List.mem_map.mpr ⟨e', he', rfl⟩)
  omega

theorem broadcasts_of_persists {i : ℕ} {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i)) : e ∈ broadcasts (outputsAt cfg tr i) := by
  unfold outputsAt at he ⊢
  split at he
  · rename_i w inp _
    obtain ⟨bs, ho, -⟩ := (Converge.inv_before (cfg := cfg) (tr := tr) i w).step inp
    rw [ho.1] at he
    exact ho.2.1 e he
  · simp [persists] at he

/-- **A block of an honest node that an honest node `w` knew** before
event `F`, its author built before `F`. -/
theorem own_known {H : Finset Validator} (htime : Converge.TimelyAuthentic cfg H tr) {w : Validator}
    (hw : w ∈ H) (hv : v ∈ H) {F E : ℕ} (hFE : F ≤ E)
    {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ Converge.knownBefore cfg tr F w) (hc : x.2.creator = v) :
    x ∈ persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr E v)).2 := by
  simp only [Converge.knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  rcases hx with hd | hp
  · obtain ⟨d, hdF, inp, hd', hdel⟩ := mem_delivered_before (cfg.at w) w F hd
    obtain ⟨p, hpd, hpv, hpb⟩ := htime d w inp hd' hw x hdel (by rw [hc]; exact hv)
    rw [hc] at hpv
    obtain ⟨inpp, hp'⟩ := Converge.event_of_map hpv
    obtain ⟨j, hjp, inpj, hj', hjx⟩ := Converge.persists_of_broadcasts hp' hpb
    exact persists_before_mono v (by omega : j + 1 ≤ E) x (persists_of_event hj' hjx)
  · have hcw := (Local.authored _ _ _ (cfg.at w) (inputsBefore tr F w) x hp).2
    change x.2.creator = w at hcw
    have hwv : w = v := hcw.symm.trans hc
    subst hwv
    exact persists_before_mono w hFE x hp

/-- **A block a node builds lies at or below its top after.** -/
theorem built_le_top {b : ℕ} {inp : Input Validator BlockId Payload} (hb : tr[b]? = some (v, inp))
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ persists (outputsAt cfg tr b)) :
    ∃ t, (stateBefore cfg tr (b + 1) v).top = some t ∧ e.2.round ≤ t := by
  have hB := persists_of_event hb he
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) v).rounds with ⟨-, h⟩ | ⟨t, ht, hR⟩
  · rw [h] at hB; cases hB
  · exact ⟨t, ht, hR.2 e hB⟩

/-- **A block of a node's own on its disk lies at or below its top.** -/
theorem own_le_top {H : Finset Validator} (htime : Converge.TimelyAuthentic cfg H tr)
    (hv : v ∈ H) {E t : ℕ} (ht : (stateBefore cfg tr E v).top = some t) {z : BlockId}
    (hz : z ∈ (stateBefore cfg tr E v).disk.ids)
    (hc : ((stateBefore cfg tr E v).disk.blk z).creator = v) :
    ((stateBefore cfg tr E v).disk.blk z).round ≤ t := by
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) E v).known _ hz
  have hB := own_known htime hv hv le_rfl hk hc
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) E v).rounds with ⟨h, -⟩ | ⟨t', ht', hR⟩
  · rw [h] at ht; cases ht
  · rw [ht] at ht'; cases ht'
    exact hR.2 _ hB

/-- **No block on a node's disk has the identifier of its next block**, with
an injective hash and its peers' blocks authenticated. -/
theorem fresh_before {H : Finset Validator} (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H) {E t : ℕ}
    (ht : (stateBefore cfg tr E v).top = some t) (P : Payload) (R : Finset BlockId) :
    cfg.idOf ⟨t + 1, v, R, P⟩ ∉ (stateBefore cfg tr E v).disk.ids := by
  intro hin
  set st := (stateBefore cfg tr E v).disk
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) E v).known _ hin
  have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv E hk)
  have hraw : st.blk _ = (⟨t + 1, v, R, P⟩ : Block Validator BlockId Payload) := hid hidk.symm
  have hB := own_known htime hv hv le_rfl hk (by change (st.blk _).creator = v; rw [hraw])
  rcases (Converge.inv_before (cfg := cfg) (tr := tr) E v).rounds with ⟨h, -⟩ | ⟨t', ht', hR⟩
  · rw [h] at ht; cases ht
  · rw [ht] at ht'; cases ht'
    have := hR.2 _ hB
    change (st.blk _).round ≤ t at this
    rw [hraw] at this
    simp at this

/-- **A reliable node has started after its start event.** -/
theorem started_after {H : Finset Validator} (hadm : cfg.Admissible) (hfa : cfg.Faithful)
    (hid : Function.Injective cfg.idOf) (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H)
    {st : ℕ} (hst : tr[st]? = some (v, .start)) : (stateBefore cfg tr (st + 1) v).top.isSome := by
  rw [stateBefore_succ hst, if_pos rfl]
  set s := stateBefore cfg tr st v
  by_cases hn : s.top = none
  · have hrs := (Converge.inv_before (cfg := cfg) (tr := tr) st v).rounds
    rcases hrs with ⟨-, hB0⟩ | ⟨t, ht, -⟩
    swap
    · rw [hn] at ht; cases ht
    have hg : (cfg.at v).idOf (cfg.at v).genesis ∉ s.disk.ids ∧
        rowValid (cfg.at v).q (cfg.at v).xp (Function.update s.disk.blk
          ((cfg.at v).idOf (cfg.at v).genesis) (cfg.at v).genesis) (cfg.at v).genesis := by
      obtain ⟨hev, hex⟩ := hfa 0 ∅ ∅
      refine ⟨fun hin => ?_, ⟨fun i hi => ?_, fun h => ?_, fun i hi => ?_,
        by simp [Config.genesis, Config.at, hev, hex, named], fun i hi => ?_⟩⟩
      · have hk := (Converge.inv_before (cfg := cfg) (tr := tr) st v).known _ hin
        have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv st hk)
        have hraw : s.disk.blk _ = (cfg.at v).genesis := hid hidk.symm
        have hB := own_known htime hv hv le_rfl hk (by
          change (s.disk.blk _).creator = v; rw [hraw]; rfl)
        rw [hB0] at hB; cases hB
      · simp [Config.genesis] at hi
      · simp [Config.genesis] at h
      · simp [Config.genesis] at hi
      · simp [Config.genesis] at hi
    simp only [Node.step, if_pos (⟨hn, hadm⟩ : s.top = none ∧ (cfg.at v).Admissible), dif_pos hg]
    exact (settle_shape (cfg := cfg.at v) _).rises.2.1 rfl
  · have hstep : (Node.step (cfg.at v) s .start).1 = s := by
      simp only [Node.step, if_neg (fun h : s.top = none ∧ (cfg.at v).Admissible => hn h.1)]
    rw [hstep]
    exact Option.ne_none_iff_isSome.mp hn

/-! ## Arrival -/

section Arrival

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δₛ t₁ : ℕ}

/-- **A reliable block arrives** at a reliable node `v` given it: `v`
holds it from the time by which it was synchronised. -/
theorem arrives {t_r : ℕ} (hsync : Live.SyncedFrom cfg T tr time gst Δₛ t_r t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {y : BlockId × Block Validator BlockId Payload}
    (hyu : y.2.creator = u) (hid : y.1 = cfg.idOf y.2)
    (hyr : topAt cfg tr time u (max t_r gst) ≤ y.2.round)
    {j : ℕ} (hj : tr[j]? = some (v, .deliver u y.1 y.2)) (hjr : t_r ≤ time j) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (ht₁ : τ ≤ t₁) :
    y.1 ∈ (stateAt cfg tr time v τ).disk.ids :=
  hsync j v u y.1 y.2 hj hv (hyu ▸ hu) hid (hyu ▸ hyr) hjr τ hτ ht₁

end Arrival

/-! ## Arrival past GST -/

section Rounds

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

variable (cfg) in
/-- **The run past `G`**: a block a reliable node `u` built at an event at
or before `s`, at `u`'s round at `G` or above, is held by every other
reliable node `v` after `v`'s events by `max s G + A`; and past `G` no
reliable node restarts or recovers. -/
structure Arrival (T : Finset Validator) (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ)
    (G A t₁ : ℕ) : Prop where
  /-- Reliable blocks arrive. -/
  arrives : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ∀ b inp, tr[b]? = some (u, inp) →
    ∀ e ∈ persists (outputsAt cfg tr b), topAt cfg tr time u G ≤ e.2.round →
      ∀ s τ, time b ≤ s → max s G + A ≤ τ → τ ≤ t₁ → e.1 ∈ (stateAt cfg tr time v τ).disk.ids
  /-- The reliable nodes do not recover from `G` to `t₁`. -/
  recovered : G ≤ t₁ → ∀ v ∈ T, ∀ k, eventsBy tr time G ≤ k → k ≤ eventsBy tr time t₁ →
    (stateBefore cfg tr k v).recovering = false
  /-- The reliable nodes do not restart past `G` and by `t₁`. -/
  up : ∀ v ∈ T, ∀ k inp, tr[k]? = some (v, inp) → G < time k → time k ≤ t₁ → inp ≠ .restart

/-- **No reliable node jumps past `G`**: a step it takes recovering, or
restarting, by `τ ≤ t₁` leaves it below a round above its round at `G`. -/
theorem Arrival.no_jump {G A : ℕ} (harr : Arrival cfg T tr time G A t₁)
    (hmono : Live.TimeMono tr time) {v : Validator} (hv : v ∈ T) {n τ : ℕ}
    (hn : topAt cfg tr time v G < n) (hτ : τ ≤ t₁) :
    ∀ k < eventsBy tr time τ, ∀ inp, tr[k]? = some (v, inp) →
      ((stateBefore cfg tr k v).recovering = true ∨ inp = .restart) →
      (stateBefore cfg tr (k + 1) v).top.getD 0 < n := by
  intro k hkτ inp hki hrec
  have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hki).1
  have hkt : time k ≤ τ := (lt_eventsBy hmono hkl).mp hkτ
  have hkG : time k ≤ G := by
    by_contra hlt
    rcases hrec with h | h
    · have hkE : eventsBy tr time G ≤ k := by
        by_contra hk
        exact hlt ((lt_eventsBy hmono hkl).mp (by omega))
      rw [harr.recovered (by omega) v hv k hkE
        (hkτ.le.trans (eventsBy_mono hτ))] at h; cases h
    · exact harr.up v hv k inp hki (by omega) (by omega) h
  have hkE : k + 1 ≤ eventsBy tr time G := (lt_eventsBy hmono hkl).mpr hkG
  have := (rises_before (cfg := cfg) (tr := tr) v hkE).1
  change _ ≤ topAt cfg tr time v G at this
  omega

/-- **Delivery and synchronisation make blocks arrive**: past GST, a
reliable block built at `s` is delivered to every other reliable node by
`max s gst + Δ` and its history `Δₛ` later. -/
theorem arrival_of_delivered (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg T tr time gst Δₛ t₁) (hup : Live.UpFrom T tr time 0 t₁) :
    Arrival cfg T tr time gst (Δ + Δₛ) t₁ := by
  refine ⟨fun u hu v hv huv b inp hb e hep hGe s τ htb hτ ht₁ => ?_, fun _ v hv k _ hk₁ => ?_,
    fun v hv k inp hki _ hk₁ h => by
      subst h; exact absurd (hup k v hki hv hk₁) (Nat.not_lt_zero _)⟩
  swap
  · -- no reliable node restarts, so none recovers
    cases hr : (stateBefore cfg tr k v).recovering
    · rfl
    · obtain ⟨j, hjk, hj, -⟩ := recovering_restart (cfg := cfg) (tr := tr) (v := v) k hr
      have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
      exact absurd (hup j v hj hv ((lt_eventsBy hmono hjl).mp (by omega)))
        (Nat.not_lt_zero _)
  have hebc := broadcasts_of_persists hep
  obtain ⟨j, -, hj, htj⟩ := hdel b u inp hb hu (v, .deliver u e.1 e.2)
    ⟨.broadcast e.1 e.2, mem_broadcasts.mp hebc, Ne.symm huv, rfl⟩ hv (by omega)
  have hgood := (Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) u).good e
    (persists_of_event hb hep)
  exact arrives (t_r := 0)
    (fun j v u id b hj hv hc hid hr _ => hsync j v u id b hj hv hc hid (by simpa using hr)) hu hv
    hgood.2.1 hgood.1 (by simpa using hGe) hj (Nat.zero_le _) (by omega) ht₁

/-- **A reliable block held is as its author built it**: its round, its
author and its content. -/
theorem held_as_built (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hTH : T ⊆ H)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {b : ℕ}
    {inp : Input Validator BlockId Payload} (hb : tr[b]? = some (u, inp))
    {e : BlockId × Block Validator BlockId Payload} (hep : e ∈ persists (outputsAt cfg tr b))
    {τ : ℕ} (hin : e.1 ∈ (stateAt cfg tr time v τ).disk.ids) :
    ((stateAt cfg tr time v τ).disk.blk e.1).round = e.2.round ∧
      ((stateAt cfg tr time v τ).disk.blk e.1).creator = u ∧
      (stateAt cfg tr time v τ).disk.blk e.1 = e.2 := by
  have hbu : (tr[b]?.map Prod.fst) = some u := by rw [hb]; rfl
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) u).good e
    (persists_of_event hb hep)).2.1
  set Z := stateAt cfg tr time v τ
  have hk := Converge.knownBefore_sub (hTH hv) (eventsBy tr time τ)
    ((Converge.inv_before (cfg := cfg) (tr := tr) (eventsBy tr time τ) v).known e.1 hin)
  have hblk : Z.disk.blk e.1 = e.2 :=
    Converge.content_eq hinj hk (Or.inr ⟨b, u, hbu, hTH hu, hep⟩) rfl
  exact ⟨by rw [hblk], by rw [hblk]; exact hgood, hblk⟩

/-- **A reliable peer's top block arrives**: past `G`, a reliable node's
block of its round at `s` is held by a reliable node `v` after `v`'s events
by `s + A`. -/
theorem top_arrives (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    {G A : ℕ} (harr : Arrival cfg T tr time G A t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {s : ℕ} (hgs : G ≤ s)
    (hus : (stateAt cfg tr time u s).top.isSome) {τ : ℕ} (hτ : s + A ≤ τ) (ht₁ : τ ≤ t₁) :
    ∃ j ∈ (stateAt cfg tr time v τ).disk.ids,
      ((stateAt cfg tr time v τ).disk.blk j).round = topAt cfg tr time u s ∧
      ((stateAt cfg tr time v τ).disk.blk j).creator = u := by
  obtain ⟨b, hbs, hbu, e, hep, her⟩ := built_top (eventsBy tr time s) hus
  change e.2.round = topAt cfg tr time u s at her
  obtain ⟨inp, hb⟩ := Converge.event_of_map hbu
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have htb : time b ≤ s := (lt_eventsBy hmono hbl).mp hbs
  have hGs : topAt cfg tr time u G ≤ topAt cfg tr time u s :=
    (rises_before (cfg := cfg) (tr := tr) u (eventsBy_mono (tr := tr) (time := time) hgs)).1
  have h₁ := harr.arrives u hu v hv huv b inp hb e hep (her ▸ hGs) s τ htb
    (by rw [max_eq_left hgs]; omega) ht₁
  obtain ⟨h₂, h₃, -⟩ := held_as_built htime hinj hTH hu hv hb hep h₁
  exact ⟨e.1, h₁, h₂.trans her, h₃⟩

end Rounds

end Node

end LeanDag
