import LeanDag.Node.Helpers.Shape
import LeanDag.Node.Helpers.Hold
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

/-- **A block a node builds at an event is on its disk** from the next event
on. -/
theorem built_stays {p : ℕ} {inp : Input Validator BlockId Payload}
    (hp : tr[p]? = some (v, inp))
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ persists (outputsAt cfg tr p)) :
    Stays (stateBefore cfg tr (p + 1) v).disk (stateBefore cfg tr (p + 1) v).pending x := by
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

/-- **No block on a node's disk has the identifier of its next block**, with
an injective hash and its peers' blocks authenticated. -/
theorem fresh_before {H : Finset Validator} (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hv : v ∈ H) {E t : ℕ}
    (ht : (stateBefore cfg tr E v).top = some t) (R : Finset BlockId) :
    cfg.idOf ⟨t + 1, v, R, cfg.payload (t + 1)⟩ ∉ (stateBefore cfg tr E v).disk.ids := by
  intro hin
  set st := (stateBefore cfg tr E v).disk
  have hk := (Converge.inv_before (cfg := cfg) (tr := tr) E v).known _ hin
  have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv E hk)
  have hraw : st.blk _ = (⟨t + 1, v, R, cfg.payload (t + 1)⟩ :
      Block Validator BlockId Payload) := hid hidk.symm
  have hB := own_known htime hv hv le_rfl hk (by change (st.blk _).creator = v; rw [hraw])
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
    have hg : (cfg.at v).idOf (cfg.at v).genesis ∉ s.disk.ids ∧
        rowValid (cfg.at v).q (Function.update s.disk.blk ((cfg.at v).idOf (cfg.at v).genesis)
          (cfg.at v).genesis) (cfg.at v).genesis := by
      refine ⟨fun hin => ?_, ⟨fun i hi => ?_, fun h => ?_, fun i hi => ?_⟩⟩
      · have hk := (Converge.inv_before (cfg := cfg) (tr := tr) st v).known _ hin
        have hidk := Converge.id_of_knownIn (Converge.knownBefore_sub hv st hk)
        have hraw : s.disk.blk _ = (cfg.at v).genesis := hid hidk.symm
        have hB := own_known htime hv hv le_rfl hk (by
          change (s.disk.blk _).creator = v; rw [hraw]; rfl)
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

/-- **A path through the blocks known** from a block of a store stays in
the store, when the store's blocks are the ones known. -/
theorem mem_of_reaches_known {st : Store Validator BlockId Payload}
    (hst : ∀ w ∈ st.ids, Live.knownBlock cfg H tr w = st.blk w) {r : BlockId}
    (hr : r ∈ st.ids) {z : BlockId} (h : ReachesFrom (Live.knownBlock cfg H tr) r z) :
    z ∈ st.ids := by
  induction h with
  | refl => exact hr
  | tail hrw hstep ih =>
    rename_i w z'
    change z' ∈ (Live.knownBlock cfg H tr w).refs at hstep
    rw [hst w ih] at hstep
    exact st.complete w ih z' hstep

end Known

/-! ## Arrival -/

section Arrival

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δₛ t₁ : ℕ}

/-- **A reliable block arrives** at a reliable node `v` given it: `v`
holds it after `v`'s events up to a time by which its history was
synchronised. -/
theorem arrives (hinj : Converge.HashInjective cfg H tr)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H)
    (hmono : Live.TimeMono tr time) {t_r : ℕ}
    (hsync : Live.SyncedFrom cfg H T tr time gst Δₛ t_r t₁)
    {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) {i : ℕ}
    {inp : Input Validator BlockId Payload} (hi : tr[i]? = some (u, inp))
    {y : BlockId × Block Validator BlockId Payload} (hy : y ∈ persists (outputsAt cfg tr i))
    {U : BlockRecord Validator BlockId Payload P H}
    {x : State Validator BlockId Payload}
    (hx : BuildState (cfg.at u) U (knownAll cfg H tr) (stateBefore cfg tr i u) inp x)
    {y' : State Validator BlockId Payload} {o : List (Output Validator BlockId Payload)}
    (hb : tryBuild (cfg.at u) x = some (y', o)) (hyo : y ∈ persists o)
    {j : ℕ} (hj : tr[j]? = some (v, .deliver y.1 y.2)) (hjr : t_r ≤ time j) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (ht₁ : max (time j) gst + Δₛ ≤ t₁) :
    y.1 ∈ (stateAt cfg tr time v τ).disk.ids := by
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ :=
    (lt_eventsBy hmono hjl).mpr (le_trans (le_max_left _ _) (le_trans (Nat.le_add_right _ _) hτ))
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).disk.ids
  set E := eventsBy tr time τ with hE
  set Zs := stateBefore cfg tr E v with hZsdef
  -- the build
  obtain ⟨r', id', b', hnew, hrefs, hpred, hxt, hbr, hbc, hid, hrv, -, -, -, -, hout⟩ :=
    tryBuild_some hb
  rw [hout, persists_built, List.mem_singleton] at hyo
  subst hyo
  simp only at hj ⊢
  obtain ⟨B, hiX⟩ := hx.inv
  set raw := Live.knownBlock cfg H tr with hraw
  have hknX : ∀ w ∈ x.disk.ids, (w, x.disk.blk w) ∈ Converge.knownIn cfg H tr :=
    fun w hw => by
      obtain ⟨v', hv', hk⟩ := hiX.known w hw
      exact knownOf_sub hv' hk
  have hstK : ∀ w ∈ x.disk.ids, raw w = x.disk.blk w := fun w hw =>
    knownBlock_eq hinj (hknX w hw)
  have hyK : ((id', b') : BlockId × Block Validator BlockId Payload) ∈ Converge.knownIn cfg H tr :=
    Or.inr ⟨i, u, by rw [hi]; rfl, hTH hu, hy⟩
  have hry : raw id' = b' := knownBlock_eq hinj hyK
  have hbu : b'.creator = u := hbc
  have C : CausalStructure x.disk.blk x.disk.ids := x.disk.toRecord.causal
  have hAv := Converge.reads_before hinj (hTH hv) E
  have hZv : ∀ w ∈ Zs.disk.ids, (Zs.disk.blk w).round = (raw w).round ∧
      (Zs.disk.blk w).creator = (raw w).creator := fun w hw => by
    have a := hAv w hw
    obtain ⟨k₁, k₂⟩ := knownBlock_gT (cfg := cfg) (H := H) (tr := tr) w
    exact ⟨(congrArg Block.round a).trans k₁.symm, (congrArg Block.creator a).trans k₂.symm⟩
  -- the history the author built on
  let Z : Finset BlockId := insert id' (b'.refs.biUnion (historyFrom x.disk.blk))
  have hZmem : ∀ z ∈ Z, z = id' ∨ ∃ r ∈ b'.refs, z ∈ historyFrom x.disk.blk r ∧ z ∈ x.disk.ids :=
    fun z hz => by
      rcases Finset.mem_insert.mp hz with h | h
      · exact Or.inl h
      · obtain ⟨r, hr, hzr⟩ := Finset.mem_biUnion.mp h
        exact Or.inr ⟨r, hr, hzr, C.history_subset_ids (hrefs hr) hzr⟩
  -- each of its blocks stays at `v`
  have hstays : ∀ z ∈ Z, Stays Zs.disk Zs.pending (z, raw z) := by
    intro z hz
    rcases hZmem z hz with rfl | ⟨r, hr, hzr, hzx⟩
    · rw [hry]
      exact stays_from hinj (hTH hv) hyK
        (stays_succ hinj (hTH hv) hyK (Or.inr ⟨hj, by rw [hbu]; exact huv⟩)) E (by omega)
    · set xz : BlockId × Block Validator BlockId Payload := (z, x.disk.blk z)
      have hxzK := hknX z hzx
      have hrz : raw z = xz.2 := hstK z hzx
      rw [hrz]
      by_cases hcr : xz.2.creator = v
      · -- one of `v`'s own blocks, which the author knew, so `v` built it before
        have hreach : ReachesFrom raw id' z := by
          refine ReachesFrom.of_mem_refs (by rw [hry]; exact hr) ?_
          exact (reaches_known hstK (hrefs hr) (reaches_of_mem_historyUptoFrom hzr)).1
        obtain ⟨p, hpj, hpu, hpb⟩ := htime j v _ hj (hTH hv) (id', b')
          (by simp only [delivered, List.flatMap_cons, List.flatMap_nil, List.append_nil]
              rw [if_pos (show id' = (cfg.at v).idOf b' from hid)]
              exact List.mem_singleton_self _) (by rw [hbu]; exact hTH hu)
        rw [hbu] at hpu
        obtain ⟨inpp, hp'⟩ := Converge.event_of_map hpu
        obtain ⟨q, hqp, inpq, hq', hqy⟩ := Converge.persists_of_broadcasts hp' hpb
        have hyS := Converge.persist_stored (cfg := cfg) hq' hqy
        set S := (stateBefore cfg tr (q + 1) u).disk
        have hSK : ∀ w ∈ S.ids, raw w = S.blk w := fun w hw =>
          knownBlock_eq hinj (Converge.knownBefore_sub (hTH hu) (q + 1)
            ((Converge.inv_before (cfg := cfg) (tr := tr) (q + 1) u).known w hw))
        have hzS : z ∈ S.ids := mem_of_reaches_known hSK hyS.1 hreach
        have hk := (Converge.inv_before (cfg := cfg) (tr := tr) (q + 1) u).known z hzS
        rw [← hSK z hzS, hrz] at hk
        have hxzp := own_known htime (hTH hu) (hTH hv) (show q + 1 ≤ E by omega) hk hcr
        obtain ⟨bρ, hbρE, hbρv, hbρx⟩ := mem_persists_before (cfg := cfg) v E hxzp
        obtain ⟨inpρ, hbρ⟩ := Converge.event_of_map hbρv
        exact stays_from hinj (hTH hv) hxzK (built_stays hbρ hbρx) E (by omega)
      · -- another's, synchronised after `v` received the author's block
        have hreach : ReachesFrom raw id' z := by
          refine ReachesFrom.of_mem_refs (by rw [hry]; exact hr) ?_
          exact (reaches_known hstK (hrefs hr) (reaches_of_mem_historyUptoFrom hzr)).1
        obtain ⟨k, hjk, hk, htk⟩ := hsync j v id' b' hj hv (by rw [hbu]; exact hu) hid hjr ht₁ xz
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
    · have hbz : x.disk.blk z = raw z := (hstK z hzx).symm
      have hr' : r ∈ (x.disk.blk z).refs := by rw [hbz]; exact hr
      have hrx := C.complete z hzx r hr'
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r₀, hr₀,
        C.history_subset_of_reaches (hrefs hr₀) ((C.mem_history_iff (hrefs hr₀)).mp hzr)
          (C.mem_history_of_mem_refs hzx hr')⟩), ?_⟩
      rw [hstK r hrx, ← hbz]; exact C.refs_round z hzx r hr'
  -- and valid at `v` once its references are
  have hrd : ∀ z ∈ Z, (raw z).refs ⊆ Zs.disk.ids →
      readyOn (cfg.at v) Zs.disk (z, raw z) = true := by
    intro z hz hzr
    have hcl' := hcl z hz
    simp only [readyOn, Store.Checks, decide_eq_true_eq]
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
      have hbz : x.disk.blk z = raw z := (hstK z hzx).symm
      rw [hbz] at hval
      refine rowValid_congr (fun r hr => ?_) hval
      have hrx : r ∈ x.disk.ids := C.complete z hzx r (by rw [hbz]; exact hr)
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
    y.1 ∈ (stateAt cfg tr time v τ).disk.ids := by
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjE : j < eventsBy tr time τ := (lt_eventsBy hmono hjl).mpr hjτ
  have hyK : y ∈ Converge.knownIn cfg H tr := Or.inr ⟨i, u, hiu, hTH hu, hy⟩
  have hst := stays_from hinj (hTH hv) hyK
    (stays_succ hinj (hTH hv) hyK (Or.inr ⟨hj, by rw [hyu]; exact huv⟩))
    (eventsBy tr time τ) (by omega)
  change y.1 ∈ (stateBefore cfg tr (eventsBy tr time τ) v).disk.ids
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
    have hrd : readyOn (cfg.at v) (stateBefore cfg tr (eventsBy tr time τ) v).disk y = true := by
      simp only [readyOn, Store.Checks, decide_eq_true_eq]
      exact ⟨fun r hr => (hr0 r hr).elim, fun r hr => (hr0 r hr).elim,
        rowValid_congr (fun r hr => (hr0 r hr).elim) hval⟩
    have := Converge.noReady_before (cfg := cfg) (tr := tr) v (eventsBy tr time τ) y h
    rw [hrd] at this; cases this

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
theorem arrival_of_delivered (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁) (hup : Live.UpFrom T tr time 0 t₁) :
    Arrival cfg T tr time gst (Δ + Δₛ) t₁ := by
  refine ⟨fun u hu v hv huv b inp hb e hep _ s τ htb hτ ht₁ => ?_, fun _ v hv k _ hk₁ => ?_,
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
  have hbu : (tr[b]?.map Prod.fst) = some u := by rw [hb]; rfl
  have hebc := broadcasts_of_persists hep
  obtain ⟨j, hbj, hj, htj⟩ := hdel b u inp hb hu (v, .deliver e.1 e.2)
    ⟨.broadcast e.1 e.2, mem_broadcasts.mp hebc, Ne.symm huv, rfl⟩ hv (by omega)
  have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (b + 1) u).good e
    (persists_of_event hb hep)).2.1
  by_cases hn0 : e.2.round = 0
  · exact arrives_zero hinj hTH hmono hu hv huv hbu hep hgood hn0 hj (by omega)
  · obtain ⟨x, y', o, hx, hxb, heo, -⟩ := build_witness hσ hadm hf htime hinj (hTH hu) hb hep hn0
    exact arrives hinj htime hTH hmono (t_r := 0)
      (fun j v id b hj hv hc hid _ => hsync j v id b hj hv hc hid) hu hv huv hb hep hx hxb heo
      hj (Nat.zero_le _) (τ := τ) (by omega) (by omega)

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
