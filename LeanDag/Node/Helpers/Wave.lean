import LeanDag.Node.Helpers.Drift
/-!
# The wave facts of a node's timed run

`docs/validator.md` §5.3. Past a synchronisation point, with drift
within `A = Δ + Δₛ` (`drift`) and `2A < timeout`, a reliable node that
waited the timeout at a round holds every reliable block of it before it
builds the next (`waited_holds`): its own stays stored, and another's
arrives `A` after it was built, before the node's timer fired. By `A`
after every reliable node reached a round, each holds every reliable
block up to it (`reliable_held`). The file also counts a node's output
decisions (`decisionsBy_length`) and bounds the slots at a round
(`lt_decidable`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}

/-! ## Holdings -/

section Holds

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Under nondecreasing times, the events strictly before `t` are those at
times below it. -/
theorem lt_eventsBefore (hmono : Live.TimeMono tr time) {i t : ℕ} (hi : i < tr.length) :
    i < eventsBefore tr time t ↔ time i < t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : eventsBefore tr time 0 = 0 := by
      unfold eventsBefore
      simp
    rw [this]; omega
  · have heq : eventsBefore tr time t = eventsBy tr time (t - 1) := by
      unfold eventsBefore eventsBy
      congr 1
      exact List.filter_congr fun j _ => by simp only [decide_eq_decide]; omega
    rw [heq, lt_eventsBy hmono hi]
    omega

/-- **A node is at round `n` before it builds round `n + 1`**: at an
index past an event building round `n`, before every event at or after
the first build of round `n + 1`. -/
theorem top_eq_between {v : Validator}
    (hmono : Live.TimeMono tr time) {E n i₀ : ℕ} {inp : Input Validator BlockId Payload}
    (hi₀ : tr[i₀]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i₀)) (her : e.2.round = n) (hi₀E : i₀ < E)
    (hlt : ∀ k < E, k < tr.length → time k < builtAt cfg tr time v (n + 1)) :
    (stateBefore cfg tr E v).top = some n := by
  obtain ⟨t₀, ht₀, hrt₀⟩ := built_le_top hi₀ he
  obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) v (show i₀ + 1 ≤ E by omega)
  rw [ht₀] at h₁ h₂
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (h₂ rfl)
  rw [ht'] at h₁ ⊢
  simp only [Option.getD_some] at h₁
  by_contra hne
  have hge : n + 1 ≤ t' := by
    have : t' ≠ n := fun h => hne (by rw [h])
    omega
  obtain ⟨k, hkE, hkv, e', he', her'⟩ := built_by E (by rw [ht']; rfl)
    (show n + 1 ≤ _ by rw [ht']; exact hge)
  obtain ⟨i', hi'k, hbt', -⟩ := builtAt_first (cfg := cfg) time hkv ⟨e', he', her'⟩
  obtain ⟨_inpk, hk⟩ := Converge.event_of_map hkv
  have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
  have := hlt k hkE hkl
  have := hmono i' k hi'k hkl
  omega

variable {N n₀ t : ℕ} (hσ : cfg.σ = boundedSel)
  (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
  (hinj : Converge.HashInjective cfg H tr)
  (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
  (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
  (hD : ∀ n, n₀ ≤ n → n ≤ N → ∀ u ∈ T, ∀ w ∈ T, gst ≤ builtAt cfg tr time u n ∧
    builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (Δ + Δₛ))
  (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
  (hN : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (Δ + Δₛ) ≤ t₁)
include hσ hadm hf htime hinj hTH hmono harr hD hst hN ht₁

/-- **A reliable node that waited the timeout holds the reliable blocks of
the round**, before it builds the next, when `2A < timeout`. -/
theorem waited_holds (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) {u v : Validator} (hu : u ∈ T)
    (hv : v ∈ T) {n : ℕ} (hn₀ : n₀ ≤ n) (hnN : n + 1 ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcu : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = u)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = n)
    (hwait : builtAt cfg tr time v n + cfg.timeout n ≤ builtAt cfg tr time v (n + 1)) :
    c ∈ heldBefore cfg tr time v (builtAt cfg tr time v (n + 1)) := by
  have hτ := hto n
  obtain ⟨i₁, -, e₁, hi₁, -, -, hbt₁, hi₁t⟩ :=
    built_of_top hmono (hst v hv) ((hN v hv).trans' hnN)
  obtain ⟨i₀, _inp₀, e₀, hi₀, he₀, he₀r, hbt₀, -⟩ :=
    built_of_top hmono (hst v hv) ((hN v hv).trans' (by omega : n ≤ N))
  set Eb := eventsBefore tr time (time i₁) with hEbdef
  have hlt : ∀ k < Eb, k < tr.length → time k < builtAt cfg tr time v (n + 1) := fun k hk hkl => by
    rw [hbt₁]; exact (lt_eventsBefore hmono hkl).mp hk
  have hi₀l : i₀ < tr.length := (List.getElem?_eq_some_iff.mp hi₀).1
  have hi₀E : i₀ < Eb := (lt_eventsBefore hmono hi₀l).mpr (by omega)
  unfold heldBefore
  rw [hbt₁, ← hEbdef]
  -- the block's build
  obtain ⟨i, inp, e, hi, he, rfl, her, hbt⟩ :=
    event_of_mem (time := time) hinj htime (hTH hu) hcU hcu
  rw [hcr] at her hbt
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hgu, hdu⟩ := hD n hn₀ (by omega) u hu v hv
  obtain ⟨-, hdv⟩ := hD n hn₀ (by omega) v hv u hu
  by_cases huv : u = v
  · subst huv
    exact own_held hi he ((lt_eventsBefore hmono hil).mpr (by omega))
  -- another's, arrived `A` after it was built
  set τ := time i + (Δ + Δₛ) with hτdef
  have hτE : eventsBy tr time τ ≤ Eb := by
    by_contra h
    have hk : Eb < tr.length := lt_of_lt_of_le (not_le.mp h) (eventsBy_le_length τ)
    have h₁ := (lt_eventsBy hmono hk).mp (not_le.mp h)
    have h₂ := (lt_eventsBefore hmono hk).not.mp (lt_irrefl _)
    omega
  have hZt : (stateAt cfg tr time v τ).top = some n :=
    top_eq_between hmono hi₀ he₀ he₀r ((lt_eventsBy hmono hi₀l).mpr (by omega))
      fun k hk hkl => hlt k (by omega) hkl
  have hin := harr u hu v hv huv i inp hi e he (time i) τ le_rfl
    (by rw [max_eq_left (by omega)]) (by omega)
  exact (grows_before (cfg := cfg) (tr := tr) v hτE).1 hin

/-- **By `A` after every reliable node reached a round, each holds every
reliable block up to it**. -/
theorem reliable_held {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {r : ℕ} (hr₀ : n₀ ≤ r)
    (hrN : r ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcu : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = u)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = r) :
    c ∈ (stateAt cfg tr time v (t + (Δ + Δₛ))).store.ids := by
  obtain ⟨i, inp, e, hi, he, rfl, her, hbt⟩ :=
    event_of_mem (time := time) hinj htime (hTH hu) hcU hcu
  rw [hcr] at her hbt
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hit : time i ≤ t := hbt ▸ builtAt_le_of_top hmono (hst u hu) ((hN u hu).trans' hrN)
  have hgi : gst ≤ time i := hbt ▸ (hD r hr₀ hrN u hu u hu).1
  by_cases huv : u = v
  · subst huv
    exact own_held hi he ((lt_eventsBy hmono hil).mpr (by omega))
  obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) v
    (eventsBy_mono (tr := tr) (time := time) (show t ≤ t + (Δ + Δₛ) by omega))
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (h₂ (hst v hv))
  have hNt' : N ≤ t' := by
    have := (hN v hv).trans h₁
    change N ≤ (stateBefore cfg tr (eventsBy tr time (t + (Δ + Δₛ))) v).top.getD 0 at this
    rw [ht'] at this
    exact this
  exact harr u hu v hv huv i inp hi e he (time i) (t + (Δ + Δₛ)) le_rfl
    (by rw [max_eq_left hgi]; omega) ht₁

/-- **A reliable block that did not pass the tests references every
reliable block of the round below**, past the synchronisation point: its
builder waited the timeout, and holds them (`waited_holds`), or was behind,
and holds an earlier reliable block of its round that did not pass the
tests either, else the references it lends would have (`behind_earlier`,
`ready_transfer`), and which references them, by induction on the event
that built it. -/
theorem refs_all (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg T tr time) (hid : Function.Injective cfg.idOf)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) :
    ∀ i₀ {v : Validator} {inp : Input Validator BlockId Payload}
      {x : State Validator BlockId Payload} {n : ℕ} {c : BlockId}, v ∈ T → n₀ ≤ n → n + 1 ≤ N →
    c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids →
    ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = v →
    ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = n + 1 →
    tr[i₀]? = some (v, inp) → builtAt cfg tr time v (n + 1) = time i₀ →
    BuildState (cfg.at v) (globalRecord (hashInjective_of_trace hinj)
      (authentic_of_timely htime)) (knownAll cfg H tr) (stateBefore cfg tr i₀ v) inp x →
    x.top = some n → c ∉ x.store.ids →
    (∃ y o, tryBuild (cfg.at v) x = some (y, o) ∧
      (c, (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block c) ∈
        persists o ∧
      (c, (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block c) ∈
        persists (outputsAt cfg tr i₀)) →
    ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block c).refs =
      refsAt (cfg.at v) x.store n x.own →
    Grows x.store (stateBefore cfg tr (i₀ + 1) v).store →
    (n ∈ x.fired ∨ behind (cfg.at v) x.store n) →
    refsAt (cfg.at v) x.store n x.own = refsFor (cfg.at v) x.store n x.own →
    ¬ (reachReady (cfg.at v) x.store (refsAt (cfg.at v) x.store n x.own) n = true ∧
      certReady (cfg.at v) x.store (refsAt (cfg.at v) x.store n x.own) n = true) →
    ∀ b ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids,
      ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        b).creator ∈ T →
      ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        b).round = n →
      b ∈ ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
        c).refs := by
  set U := globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime) with hU
  intro i₀
  induction i₀ using Nat.strong_induction_on with
  | _ i₀ ih =>
  intro v inp x n c hv hn₀ hnN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild hcrefs hgx hexit hfor hnr
    b hbU hbT hbr
  obtain ⟨y, o, hb, heo, he⟩ := hbuild
  have hi₀l : i₀ < tr.length := (List.getElem?_eq_some_iff.mp hi₀).1
  -- it suffices that the build state holds the block
  suffices hbx : b ∈ x.store.ids by
    rw [hcrefs, hfor]
    exact mem_refsFor_of_cut hbs.cut hbx (by rw [← hbs.cut.round hbx, hbr])
      (by rw [← hbs.cut.creator hbx]; exact hTH hbT) fun _ => hbs.own _ hxt
  rcases hexit with hfired | hbeh
  · -- it waited the timeout
    have hj : ∃ j ≤ i₀, tr[j]? = some (v, Input.timer n) := by
      rcases hbs.fired _ hfired with h | h
      · obtain ⟨j, hj, hjt⟩ := fired_before (cfg := cfg) i₀ _ h
        exact ⟨j, hj.le, hjt⟩
      · exact ⟨i₀, le_rfl, by rw [hi₀, h]⟩
    obtain ⟨j, hj, hjt⟩ := hj
    have hwt := timer_after_built time hmono hwait hv hi₀l hj hjt
    have hbh := waited_holds hσ hadm hf htime hinj hTH hmono harr hD hst hN ht₁ hto hbT hv hn₀
      hnN hbU rfl hbr (by rw [hbt]; exact hwt)
    rw [hbt] at hbh
    exact hbs.grows.1 ((grows_before (cfg := cfg) (tr := tr) v (eventsBefore_le time hmono i₀)).1
      hbh)
  · -- it was behind: an earlier reliable block of the round
    obtain ⟨w', hw'T, hw'v, j, hji, inp', z, hj', hz, hzr, hzx, hzb⟩ :=
      behind_earlier htime hinj hTH hcT (hTH hv) hi₀ hbs hb heo he hxt hgx hbeh
    have hzU : z.1 ∈ U.ids := (hbs.cut _ hzx).1
    have hzB : U.block z.1 = z.2 := (hbs.cut.eq hzx).trans hzb
    have hzc : (U.block z.1).creator = w' := by
      rw [hzB]
      exact (Local.authored _ _ _ (cfg.at w') _ z (persists_of_event hj' hz)).2
    have hzr' : (U.block z.1).round = n + 1 := by rw [hzB, hzr]
    obtain ⟨iw, inpw, xw, hiw, hbtw, hbsw, hxtw, hzxw, ⟨yw, ow, hbw, heow, hew⟩, hzrefs, hzsub,
      hgxw, hexitw⟩ := built_block time hσ hadm hf htime hinj (hTH hw'T) hzU hzc hzr'
    have hiwj : iw = j := persist_events_eq hiw hj' hew hz (by rw [hzr', hzr])
    subst hiwj
    -- the earlier block did not pass the tests, else the node would have
    have hnrw : ¬ (reachReady (cfg.at w') xw.store (refsAt (cfg.at w') xw.store n xw.own) n = true ∧
        certReady (cfg.at w') xw.store (refsAt (cfg.at w') xw.store n xw.own) n = true) := by
      intro hrw
      apply hnr
      obtain ⟨r', id, bb, hnew, hrefs, -, hxt', hbbr, -, -, hrv, -, -, -, -, hout'⟩ :=
        tryBuild_some hbw
      rw [hout', persists_built, List.mem_singleton] at heow
      have hzid : z.1 = id := (Prod.mk.inj heow).1
      have hzbb : U.block z.1 = bb := (Prod.mk.inj heow).2
      rw [hxtw, Option.some.injEq] at hxt'
      subst hxt'
      have hbbrefs : bb.refs = refsAt (cfg.at w') xw.store n xw.own := by
        rw [← hzbb]; exact hzrefs
      obtain ⟨hRq, hRd⟩ := refs_of_rowValid (cfg := cfg.at w') hnew hrefs (by omega) hrv
      rw [hbbrefs] at hRq hRd
      obtain ⟨o', hoo, hoi, hor, hoc⟩ := hbs.own n hxt
      have hZR : (x.store.blk z.1).refs = refsAt (cfg.at w') xw.store n xw.own := by
        rw [← hbs.cut.eq hzx, hzrefs]
      -- no stored block has the identifier of a next block of the node's own
      have hfresh : ∀ R, (cfg.at v).idOf ⟨n + 1, (cfg.at v).me, R, (cfg.at v).payload (n + 1)⟩ ∉
          x.store.ids := by
        intro R hin
        obtain ⟨B, hiX⟩ := hbs.inv
        obtain ⟨v', hv', hk⟩ := hiX.known _ hin
        have hidk := Converge.id_of_knownIn (knownOf_sub hv' hk)
        have hraw : x.store.blk _ = (⟨n + 1, v, R, cfg.payload (n + 1)⟩ :
            Block Validator BlockId Payload) := hid hidk.symm
        have := U.eq_of_creator_eq (hbs.cut _ hin).1 hcU (hTH hv)
          (by rw [hbs.cut.eq hin, hraw]) hcv (by rw [hbs.cut.eq hin, hraw, hcr])
        exact hcx (this ▸ hin)
      obtain ⟨hRR, hlZ, hlb⟩ := lent_buildable (cfg := cfg.at v) hbsw.cut hbs.cut hzsub hRq hRd
        hzx (by rw [hzb, hzr]) hZR hoi hor hoc (hTH hv) hfresh
      have hready := ready_transfer (cfg := cfg.at v) hσ (fun h => certThreshold_pos hadm h)
        hbsw.cut hbs.cut hzsub hRR hlZ hrw.1 hrw.2
      rw [hoo]
      exact refsAt_ready (cfg := cfg.at v) hzx (by rw [hzb, hzr])
        (by rw [← hbs.cut.creator hzx, hzc]; exact hw'v) hready hlb
    have hexitw' : (n ∈ xw.fired ∨ behind (cfg.at w') xw.store n) ∧
        refsAt (cfg.at w') xw.store n xw.own = refsFor (cfg.at w') xw.store n xw.own := by
      rcases hexitw with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact absurd h hnrw
      · exact ⟨Or.inl h₁, h₂⟩
      · exact ⟨Or.inr h₁, h₂⟩
    have hbz := ih iw hji hw'T hn₀ hnN hzU hzc hzr' hiw hbtw hbsw hxtw hzxw
      ⟨yw, ow, hbw, heow, hew⟩ hzrefs hgxw hexitw'.1 hexitw'.2 hnrw b hbU hbT hbr
    rw [hbs.cut.eq hzx] at hbz
    exact x.store.complete z.1 hzx b hbz

/-- **Reach or reference, at a reliable node**, past the synchronisation
point: a block of `v` at the round above slot `k`'s round plus `m`, below
the vote offset, reaches the slot's reliable leader block, or references
every block of the leader of the round below. -/
theorem reach_or_refs_node (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg T tr time) (hid : Function.Injective cfg.idOf)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) {v : Validator} (hv : v ∈ T)
    {k m : ℕ} (hRk : n₀ ≤ cfg.slots.slotRound k) (hlead : cfg.slots.leader k ∈ T) {L : BlockId}
    (hL : IsLeaderBlock (S := cfg.slots)
      (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) k L)
    (hm : m < cfg.p.voteOffset) (hmN : cfg.slots.slotRound k + m + 1 ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcv : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = v)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = cfg.slots.slotRound k + m + 1) :
    Reaches (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) c L ∨
      ∀ b ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids,
        ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
          b).creator = cfg.slots.leader k →
        ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
          b).round = cfg.slots.slotRound k + m →
        b ∈ ((globalRecord (hashInjective_of_trace hinj)
          (authentic_of_timely htime)).block c).refs := by
  obtain ⟨i₀, inp, x, hi₀, hbt, hbs, hxt, hcx, hbuild, hcrefs, hsub, hgx, hexit⟩ :=
    built_block time hσ hadm hf htime hinj (hTH hv) hcU hcv hcr
  by_cases hready : reachReady (cfg.at v) x.store
        (refsAt (cfg.at v) x.store (cfg.slots.slotRound k + m) x.own)
        (cfg.slots.slotRound k + m) = true ∧
      certReady (cfg.at v) x.store (refsAt (cfg.at v) x.store (cfg.slots.slotRound k + m) x.own)
        (cfg.slots.slotRound k + m) = true
  · exact Or.inl (reaches_of_reachReady (cfg := cfg.at v) hbs.cut hready.1 hsub hm rfl
      (hTH hlead) hL hcrefs)
  · right
    have hexit' := hexit.resolve_left hready
    have h₁ : (cfg.slots.slotRound k + m ∈ x.fired ∨
        behind (cfg.at v) x.store (cfg.slots.slotRound k + m)) ∧
        refsAt (cfg.at v) x.store (cfg.slots.slotRound k + m) x.own =
          refsFor (cfg.at v) x.store (cfg.slots.slotRound k + m) x.own := by
      rcases hexit' with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨Or.inl h, h'⟩
      · exact ⟨Or.inr h, h'⟩
    intro b hbU hbc hbr
    exact refs_all hσ hadm hf htime hinj hTH hmono harr hD hst hN ht₁ hto hwait hid hcT i₀ hv
      (by omega) hmN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild hcrefs hgx h₁.1 h₁.2 hready b hbU
      (by rw [hbc]; exact hlead) hbr

/-- **Certify or reference, at a reliable node**, past the
synchronisation point: where votes are certified a round later, a block of
`v` at the round above slot `k`'s vote round certifies the slot's reliable
leader block, or references every reliable vote of that round. -/
theorem cert_or_refs_node (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg T tr time) (hid : Function.Injective cfg.idOf)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hvc : cfg.p.voteIsCert = false)
    {v : Validator} (hv : v ∈ T) {k : ℕ} (hRk : n₀ ≤ cfg.slots.slotRound k)
    (hlead : cfg.slots.leader k ∈ T) {L : BlockId}
    (hL : IsLeaderBlock (S := cfg.slots)
      (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) k L)
    (hkN : cfg.slots.slotRound k + cfg.p.voteOffset + 1 ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcv : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = v)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = cfg.slots.slotRound k + cfg.p.voteOffset + 1) :
    Scheme.IsCert cfg.p boundedSel
        (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) c L ∨
      ∀ b ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids,
        ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
          b).creator ∈ T →
        ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
          b).round = cfg.slots.slotRound k + cfg.p.voteOffset →
        boundedSel.Votes (globalRecord (hashInjective_of_trace hinj)
          (authentic_of_timely htime)) b L →
        b ∈ ((globalRecord (hashInjective_of_trace hinj)
          (authentic_of_timely htime)).block c).refs := by
  obtain ⟨i₀, inp, x, hi₀, hbt, hbs, hxt, hcx, hbuild, hcrefs, hsub, hgx, hexit⟩ :=
    built_block time hσ hadm hf htime hinj (hTH hv) hcU hcv hcr
  by_cases hready : reachReady (cfg.at v) x.store
        (refsAt (cfg.at v) x.store (cfg.slots.slotRound k + cfg.p.voteOffset) x.own)
        (cfg.slots.slotRound k + cfg.p.voteOffset) = true ∧
      certReady (cfg.at v) x.store
        (refsAt (cfg.at v) x.store (cfg.slots.slotRound k + cfg.p.voteOffset) x.own)
        (cfg.slots.slotRound k + cfg.p.voteOffset) = true
  · exact Or.inl (isCert_of_certReady (cfg := cfg.at v) hσ hbs.cut hready.2 hsub hvc rfl
      (hTH hlead) hL hcrefs)
  · right
    have hexit' := hexit.resolve_left hready
    have h₁ : (cfg.slots.slotRound k + cfg.p.voteOffset ∈ x.fired ∨
        behind (cfg.at v) x.store (cfg.slots.slotRound k + cfg.p.voteOffset)) ∧
        refsAt (cfg.at v) x.store (cfg.slots.slotRound k + cfg.p.voteOffset) x.own =
          refsFor (cfg.at v) x.store (cfg.slots.slotRound k + cfg.p.voteOffset) x.own := by
      rcases hexit' with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨Or.inl h, h'⟩
      · exact ⟨Or.inr h, h'⟩
    intro b hbU hbT hbr _
    exact refs_all hσ hadm hf htime hinj hTH hmono harr hD hst hN ht₁ hto hwait hid hcT i₀ hv
      (by omega) hkN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild hcrefs hgx h₁.1 h₁.2 hready b hbU
      hbT hbr

end Holds

section Outputs

variable {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}

/-- **The decisions a node output number its next undecided slot.** -/
theorem decisionsBy_length (v : Validator) (τ : ℕ) :
    (decisionsBy cfg tr time v τ).length = (stateAt cfg tr time v τ).lo := by
  obtain ⟨ha, hL⟩ := run_appends (cfg := cfg.at v) (inputsBefore tr (eventsBy tr time τ) v)
    Ledger.init
  have h := congrArg List.length ha
  have h₀ : (State.init (cfg.at v)).decided = [] := rfl
  rw [h₀, List.reverse_nil, List.nil_append, List.length_reverse] at h
  unfold decisionsBy
  rw [← h]
  exact hL.length

omit [Fintype Validator] in
/-- Every slot at a round at most `R` is below `decidable R`. -/
theorem lt_decidable {k R : ℕ} (hk : cfg.slots.slotRound k ≤ R) : k < decidable cfg R := by
  change cfg.per * (k / cfg.m) ≤ R at hk
  unfold decidable
  have h₁ : k / cfg.m ≤ R / cfg.per :=
    (Nat.le_div_iff_mul_le cfg.per_pos).mpr (by rw [Nat.mul_comm]; exact hk)
  exact lt_of_lt_of_le (Nat.lt_mul_div_succ k cfg.m_pos)
    (Nat.mul_le_mul_left _ (by omega))

end Outputs

end Node

end LeanDag
