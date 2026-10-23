import LeanDag.Node.Helpers.Catch
/-!
# The wave facts of a node's timed run

`docs/validator.md` §5.3. From a round `n₀ ≥ R₀` above every reliable
node's round at GST, with `2A < timeout` for `A = Δ + Δₛ`, a reliable
node that waited a round's timer holds every reliable block of it before
it builds the next (`waited_holds`): it armed the timer with a quorum of
the round, whose `f + 1` reliable authors bring every reliable node to
the round `A` later (`catches_up`), and their blocks arrive `A` after,
before the timer fired. By `A` after every reliable node reached a round,
each holds every reliable block up to it (`reliable_held`). The file also counts a node's output
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

/-- **A reliable node that armed a round's timer holds every reliable block
of the round `2A` later**: from round `R₀` on, the quorum it held has
`f + 1` reliable authors (`quorum_reliable`), so every reliable node is at
the round `A` later (`catches_up`), and its block arrives `A` after. -/
theorem waited_holds {R₀ : ℕ} (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time) (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
    (hstart : Live.StartedBy T tr time gst) (hout : Live.OutsideBelow cfg H T tr R₀)
    {u : Validator} (hu : u ∈ T) {i : ℕ} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (u, inp)) {n : ℕ} (htop : (stateBefore cfg tr (i + 1) u).top = some n)
    (hqn : cfg.q ≤ ((stateBefore cfg tr (i + 1) u).disk.authorsAt n).card)
    (hgi : gst ≤ time i) (hRn : R₀ ≤ n) {τ : ℕ} (hτ : time i + 2 * (Δ + Δₛ) ≤ τ) (hτ₁ : τ ≤ t₁)
    {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcT : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator ∈ T)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = n) :
    c ∈ (stateAt cfg tr time u τ).disk.ids := by
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  set S := ((stateBefore cfg tr (i + 1) u).disk.authorsAt n).filter (· ∈ T) with hSdef
  have hS := quorum_reliable hadm hf htime hout (hTH hu) hRn hqn
  -- its reliable authors are at the round by `time i`
  have hSn : ∀ w ∈ S, (stateAt cfg tr time w (time i)).top.isSome ∧
      n ≤ topAt cfg tr time w (time i) := by
    intro w hw
    obtain ⟨hwA, hwT⟩ := Finset.mem_filter.mp hw
    obtain ⟨z, hzR, hzc⟩ := mem_creatorsOf.mp hwA
    have hz : z ∈ (stateBefore cfg tr (i + 1) u).disk.ids ∧
        ((stateBefore cfg tr (i + 1) u).disk.blk z).round = n := by
      rw [Store.atRound_eq] at hzR
      simpa [blocksAt, Store.toRecord] using hzR
    obtain ⟨j, hj, inpj, hj', hjz⟩ := persisted_of_stored htime (hTH hu) (hTH hwT) hz.1 hzc
    have := top_of_built hmono hj' hjz (τ := time i) (hmono j i (by omega) hil)
    exact ⟨this.1, by simpa [hz.2] using this.2⟩
  -- so every reliable node is `A` later
  have hall : ∀ w ∈ T, n ≤ topAt cfg tr time w (time i + (Δ + Δₛ)) := fun w hw =>
    catches_up hq hσ hadm hf hid htime hinj hTH hmono harr hstart
      (fun w hw => (Finset.mem_filter.mp hw).2) hS hgi (by omega) hSn hw
  -- the block's build
  obtain ⟨ic, inpc, e, hic, he, rfl, her, hbt⟩ :=
    event_of_mem (time := time) hinj htime (hTH hcT) hcU rfl
  rw [hcr] at her hbt
  have hicl : ic < tr.length := (List.getElem?_eq_some_iff.mp hic).1
  have hws := started_at hadm hid htime hTH hmono hstart hcT (τ := time i + (Δ + Δₛ)) (by omega)
  have hbw := builtAt_le_of_top hmono hws (hall _ hcT)
  by_cases huw : ((globalRecord (hashInjective_of_trace hinj)
      (authentic_of_timely htime)).block e.1).creator = u
  · rw [huw] at hic
    exact own_held hic he ((lt_eventsBy hmono hicl).mpr (by omega))
  · exact harr _ hcT u hu huw ic inpc hic e he (time i + (Δ + Δₛ)) τ (by omega)
      (by rw [max_eq_left (by omega)]; omega) hτ₁

variable {N n₀ t R₀ : ℕ} (hσ : cfg.σ = boundedSel)
  (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
  (hinj : Converge.HashInjective cfg H tr)
  (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
  (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
  (hbelow : ∀ v ∈ T, topAt cfg tr time v gst < n₀)
  (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
  (hN : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (Δ + Δₛ) ≤ t₁)
include hσ hadm hf htime hinj hTH hmono harr hbelow hst hN ht₁

/-- **By `A` after every reliable node reached a round, each holds every
reliable block up to it**. -/
theorem reliable_held {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {r : ℕ} (hr₀ : n₀ ≤ r)
    (hrN : r ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcu : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = u)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = r) :
    c ∈ (stateAt cfg tr time v (t + (Δ + Δₛ))).disk.ids := by
  obtain ⟨i, inp, e, hi, he, rfl, her, hbt⟩ :=
    event_of_mem (time := time) hinj htime (hTH hu) hcU hcu
  rw [hcr] at her hbt
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hit : time i ≤ t := hbt ▸ builtAt_le_of_top hmono (hst u hu) ((hN u hu).trans' hrN)
  have hgt : gst ≤ t := by
    by_contra h
    have := (rises_before (cfg := cfg) (tr := tr) v
      (eventsBy_mono (tr := tr) (time := time) (show t ≤ gst by omega))).1
    have h₁ := hbelow v hv
    have h₂ := hN v hv
    change topAt cfg tr time v t ≤ topAt cfg tr time v gst at this
    omega
  by_cases huv : u = v
  · subst huv
    exact own_held hi he ((lt_eventsBy hmono hil).mpr (by omega))
  exact harr u hu v hv huv i inp hi e he t (t + (Δ + Δₛ)) hit (by rw [max_eq_left hgt]) ht₁

/-- **A reliable block that did not pass the tests references every
reliable block of the round below**, from round `n₀` on: its builder
waited the round's timer, armed with a quorum of the round, and holds them
(`timer_set`, `waited_holds`), or was behind, and holds an earlier
reliable block of its round that did not pass the tests either, else the
references it lends would have (`behind_earlier`, `ready_transfer`), and
which references them, by induction on the event that built it. -/
theorem refs_all (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg T tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst) (hout : Live.OutsideBelow cfg H T tr R₀)
    (hR₀ : R₀ ≤ n₀) :
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
    x.top = some n → c ∉ x.disk.ids →
    (∃ y o, tryBuild (cfg.at v) x = some (y, o) ∧
      (c, (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block c) ∈
        persists o ∧
      (c, (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block c) ∈
        persists (outputsAt cfg tr i₀)) →
    ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block c).refs =
      refsAt (cfg.at v) x.disk n x.own →
    Grows x.disk (stateBefore cfg tr (i₀ + 1) v).disk →
    (n ∈ x.fired ∨ behind (cfg.at v) x.disk n) →
    refsAt (cfg.at v) x.disk n x.own = refsFor (cfg.at v) x.disk n x.own →
    ¬ (reachReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk n x.own) n = true ∧
      certReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk n x.own) n = true) →
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
  suffices hbx : b ∈ x.disk.ids by
    rw [hcrefs, hfor]
    exact mem_refsFor_of_cut hbs.cut hbx (by rw [← hbs.cut.round hbx, hbr])
      (by rw [← hbs.cut.creator hbx]; exact hTH hbT) fun _ => hbs.own _ hxt
  rcases hexit with hfired | hbeh
  · -- it waited the round's timer, armed with a quorum of the round
    have hj : ∃ j ≤ i₀, tr[j]? = some (v, Input.timer n) := by
      rcases hbs.fired _ hfired with h | h
      · obtain ⟨j, hj, hjt⟩ := fired_before (cfg := cfg) i₀ _ h
        exact ⟨j, hj.le, hjt⟩
      · exact ⟨i₀, le_rfl, by rw [hi₀, h]⟩
    obtain ⟨j, hj, hjt⟩ := hj
    obtain ⟨i, hij, hiv, t', ht', hnt, hq'⟩ := timer_set hwait hv hjt
    obtain ⟨inpi, hi⟩ := Converge.event_of_map hiv
    have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
    -- the node had not built round `n + 1` when it set the timer
    have htn : t' = n := by
      by_contra hne
      obtain ⟨b', hb'i, hb'v, e', he', her'⟩ := built_by (cfg := cfg) (tr := tr) (i + 1)
        (by rw [ht']; rfl) (show n + 1 ≤ _ by rw [ht']; simp only [Option.getD_some]; omega)
      obtain ⟨inpb, hb'⟩ := Converge.event_of_map hb'v
      have hex : e' = (c, U.block c) := eq_of_persists v
        (mem_persists_iff.mpr (mem_outputs_of_event hb' (mem_persists_iff.mp he')))
        (mem_persists_iff.mpr (mem_outputs_of_event hi₀ (mem_persists_iff.mp he)))
        (by rw [her', hcr])
      have hst' := Converge.persist_stored (cfg := cfg) hb' he'
      rw [hex] at hst'
      exact hcx (hbs.grows.1
        ((grows_before (cfg := cfg) (tr := tr) v (show b' + 1 ≤ i₀ by omega)).1 hst'.1))
    subst htn
    obtain ⟨hti, hqn⟩ := hq' rfl (by have := hbelow v hv; omega)
    -- it set the timer past GST
    have hgi : gst ≤ time i := by
      by_contra h
      have hiE : i + 1 ≤ eventsBy tr time gst := (lt_eventsBy hmono hil).mpr (by omega)
      have h₁ := (rises_before (cfg := cfg) (tr := tr) v hiE).1
      rw [ht'] at h₁
      have h₂ := hbelow v hv
      change _ ≤ topAt cfg tr time v gst at h₁
      simp only [Option.getD_some] at h₁
      omega
    have hi₀t : time i₀ ≤ t :=
      hbt ▸ builtAt_le_of_top hmono (hst v hv) ((hN v hv).trans' hnN)
    have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hjt).1
    have htj := hmono j i₀ hj hi₀l
    have hτ := hto t'
    have hbh := waited_holds hq hσ hadm hf hid htime hinj hTH hmono harr hstart hout hv hi ht' hqn
      hgi (le_trans hR₀ hn₀) (τ := time i + 2 * (Δ + Δₛ)) le_rfl (by omega) hbU hbT hbr
    have hE : eventsBy tr time (time i + 2 * (Δ + Δₛ)) ≤ i₀ := by
      by_contra h
      have := (lt_eventsBy (t := time i + 2 * (Δ + Δₛ)) hmono hi₀l).mp (by omega)
      omega
    exact hbs.grows.1 ((grows_before (cfg := cfg) (tr := tr) v hE).1 hbh)
  · -- it was behind: an earlier reliable block of the round
    obtain ⟨w', hw'T, hw'v, j, hji, inp', z, hj', hz, hzr, hzx, hzb⟩ :=
      behind_earlier htime hinj hTH hf hout (hTH hv) hi₀ hbs hb heo he hxt hgx hbeh
        (by omega)
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
    have hnrw : ¬ (reachReady (cfg.at w') xw.disk (refsAt (cfg.at w') xw.disk n xw.own) n = true ∧
        certReady (cfg.at w') xw.disk (refsAt (cfg.at w') xw.disk n xw.own) n = true) := by
      intro hrw
      apply hnr
      obtain ⟨r', id, bb, hnew, hrefs, -, hxt', hbbr, -, -, hrv, -, -, -, -, hout'⟩ :=
        tryBuild_some hbw
      rw [hout', persists_built, List.mem_singleton] at heow
      have hzid : z.1 = id := (Prod.mk.inj heow).1
      have hzbb : U.block z.1 = bb := (Prod.mk.inj heow).2
      rw [hxtw, Option.some.injEq] at hxt'
      subst hxt'
      have hbbrefs : bb.refs = refsAt (cfg.at w') xw.disk n xw.own := by
        rw [← hzbb]; exact hzrefs
      obtain ⟨hRq, hRd⟩ := refs_of_rowValid (cfg := cfg.at w') hnew hrefs (by omega) hrv
      rw [hbbrefs] at hRq hRd
      obtain ⟨o', hoo, hoi, hor, hoc⟩ := hbs.own n hxt
      have hZR : (x.disk.blk z.1).refs = refsAt (cfg.at w') xw.disk n xw.own := by
        rw [← hbs.cut.eq hzx, hzrefs]
      -- no stored block has the identifier of a next block of the node's own
      have hfresh : ∀ R, (cfg.at v).idOf ⟨n + 1, (cfg.at v).me, R, (cfg.at v).payload (n + 1)⟩ ∉
          x.disk.ids := by
        intro R hin
        obtain ⟨B, hiX⟩ := hbs.inv
        obtain ⟨v', hv', hk⟩ := hiX.known _ hin
        have hidk := Converge.id_of_knownIn (knownOf_sub hv' hk)
        have hraw : x.disk.blk _ = (⟨n + 1, v, R, cfg.payload (n + 1)⟩ :
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
    have hexitw' : (n ∈ xw.fired ∨ behind (cfg.at w') xw.disk n) ∧
        refsAt (cfg.at w') xw.disk n xw.own = refsFor (cfg.at w') xw.disk n xw.own := by
      rcases hexitw with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact absurd h hnrw
      · exact ⟨Or.inl h₁, h₂⟩
      · exact ⟨Or.inr h₁, h₂⟩
    have hbz := ih iw hji hw'T hn₀ hnN hzU hzc hzr' hiw hbtw hbsw hxtw hzxw
      ⟨yw, ow, hbw, heow, hew⟩ hzrefs hgxw hexitw'.1 hexitw'.2 hnrw b hbU hbT hbr
    rw [hbs.cut.eq hzx] at hbz
    exact x.disk.complete z.1 hzx b hbz

/-- **Reach or reference, at a reliable node**, from round `n₀` on: a block
of `v` at the round above slot `k`'s round plus `m`, below
the vote offset, reaches the slot's reliable leader block, or references
every block of the leader of the round below. -/
theorem reach_or_refs_node (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg T tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst) (hout : Live.OutsideBelow cfg H T tr R₀)
    (hR₀ : R₀ ≤ n₀) {v : Validator} (hv : v ∈ T)
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
  by_cases hready : reachReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own)
        (cfg.slots.slotRound k + m) = true ∧
      certReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own)
        (cfg.slots.slotRound k + m) = true
  · exact Or.inl (reaches_of_reachReady (cfg := cfg.at v) hbs.cut hready.1 hsub hm rfl
      (hTH hlead) hL hcrefs)
  · right
    have hexit' := hexit.resolve_left hready
    have h₁ : (cfg.slots.slotRound k + m ∈ x.fired ∨
        behind (cfg.at v) x.disk (cfg.slots.slotRound k + m)) ∧
        refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own =
          refsFor (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own := by
      rcases hexit' with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨Or.inl h, h'⟩
      · exact ⟨Or.inr h, h'⟩
    intro b hbU hbc hbr
    exact refs_all hσ hadm hf htime hinj hTH hmono harr hbelow hst hN ht₁ hq hto hwait hid hstart
      hout hR₀ i₀ hv (by omega) hmN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild hcrefs hgx h₁.1 h₁.2
      hready b hbU
      (by rw [hbc]; exact hlead) hbr

/-- **Certify or reference, at a reliable node**, from round `n₀` on:
where votes are certified a round later, a block of
`v` at the round above slot `k`'s vote round certifies the slot's reliable
leader block, or references every reliable vote of that round. -/
theorem cert_or_refs_node (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg T tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst) (hout : Live.OutsideBelow cfg H T tr R₀)
    (hR₀ : R₀ ≤ n₀) (hvc : cfg.p.voteIsCert = false)
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
  by_cases hready : reachReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own)
        (cfg.slots.slotRound k + cfg.p.voteOffset) = true ∧
      certReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own)
        (cfg.slots.slotRound k + cfg.p.voteOffset) = true
  · exact Or.inl (isCert_of_certReady (cfg := cfg.at v) hσ hbs.cut hready.2 hsub hvc rfl
      (hTH hlead) hL hcrefs)
  · right
    have hexit' := hexit.resolve_left hready
    have h₁ : (cfg.slots.slotRound k + cfg.p.voteOffset ∈ x.fired ∨
        behind (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset)) ∧
        refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own =
          refsFor (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own := by
      rcases hexit' with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨Or.inl h, h'⟩
      · exact ⟨Or.inr h, h'⟩
    intro b hbU hbT hbr _
    exact refs_all hσ hadm hf htime hinj hTH hmono harr hbelow hst hN ht₁ hq hto hwait hid hstart
      hout hR₀ i₀ hv (by omega) hkN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild hcrefs hgx h₁.1 h₁.2
      hready b hbU
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
