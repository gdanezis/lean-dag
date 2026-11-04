import LeanDag.Node.Helpers.Catch
/-!
# The wave facts of a node's timed run

`docs/validator.md` §5.3. From a round `n₀` above every reliable node's
round at GST, with `2A < timeout` for `A = Δ + Δₛ`, once an honest node
armed a round's timer every reliable node holds every reliable block of
the round `2A` later, before the timer fires (`waited_holds`): the quorum
it held has `f + 1` reliable authors, which bring every reliable node to
the round `A` later (`catches_up`), and their blocks arrive `A` after.
An honest block that did not pass the reach and certificate tests was
built after that, on the timer or behind an earlier such block
(`held_before`), so a reliable one references every reliable block of
the round below (`refs_all`). By `A` after every reliable node reached a round,
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

/-- **A known block with the identifier of a base's block above its round is
that block.** -/
theorem eq_of_known (hid : Function.Injective cfg.idOf)
    {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {B E₀ E₁ : ℕ}
    (hbase : Base cfg H tr R B E₀ E₁) {b : BlockId} {c : Block Validator BlockId Payload}
    (hk : (b, c) ∈ Converge.knownIn cfg H tr) (hbU : b ∈ R.ids)
    (hbB : B < (R.block b).round) : c = R.block b := by
  obtain ⟨w, hw, hk'⟩ := hbase.real b hbU hbB
  exact hid ((Converge.id_of_knownIn hk).symm.trans (Converge.id_of_knownIn (knownOf_sub hw hk')))

/-- **A node below a round at GST built no block of that round before**, at
the events up to GST. -/
theorem not_built_before (hmono : Live.TimeMono tr time) {E₀ : ℕ}
    (hE₀ : E₀ ≤ eventsBy tr time gst) {v : Validator} {r : ℕ}
    (hr : topAt cfg tr time v gst < r + 1) :
    ∀ k < E₀, (tr[k]?.map Prod.fst) = some v →
      ∀ e ∈ persists (outputsAt cfg tr k), e.2.round ≠ r + 1 := by
  intro k hk hkv e he her
  obtain ⟨inp, hkt⟩ := Converge.event_of_map hkv
  have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hkt).1
  have hkg : time k ≤ gst := (lt_eventsBy hmono hkl).mp (by omega)
  have := (top_of_built hmono hkt he hkg).2
  omega

/-- **Within a base from GST to `t₁`, an honest node's steps past GST are
regular.** -/
theorem regular_past {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H}
    {B E₀ E₁ : ℕ} (hbase : Base cfg H tr R B E₀ E₁) (hE₀ : E₀ ≤ eventsBy tr time gst)
    (hE₁ : eventsBy tr time t₁ ≤ E₁) {v : Validator} (hv : v ∈ H) {τ : ℕ} (hτ : τ ≤ t₁) :
    ∀ k, eventsBy tr time gst ≤ k → k < eventsBy tr time τ →
      Regular (cfg.at v) (stateBefore cfg tr k v) (stateBefore cfg tr (k + 1) v) :=
  fun k hk₁ hk₂ => by
    have := eventsBy_mono (tr := tr) (time := time) hτ
    exact (hbase.window v hv k (hE₀.trans hk₁) (by omega)).2.2 (by omega)

/-- **Once an honest node armed a round's timer, every reliable node holds
every reliable block of the round `2A` later**: the quorum it held has
`f + 1` reliable authors (`quorum_reliable`), above every reliable node's
round at GST, so it armed past GST, every reliable node is at the round
`A` later (`catches_up`), and its block arrives `A` after. -/
theorem waited_holds (hq : 2 ≤ cfg.q) (hadm : cfg.Admissible) (hfa : cfg.Faithful)
    (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {B E₀ E₁ : ℕ}
    (hbase : Base cfg H tr R B E₀ E₁) (hE₀ : E₀ ≤ eventsBy tr time gst)
    (hE₁ : eventsBy tr time t₁ ≤ E₁)
    (hTB : ∀ v ∈ T, B ≤ topAt cfg tr time v gst ∧
      (cfg.drops = true → B + 1 ≤ topAt cfg tr time v gst))
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁) (hstart : Live.StartedBy T tr time gst)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) {n₀ : ℕ}
    (hbelow : ∀ v ∈ T, topAt cfg tr time v gst < n₀) (hB₀ : B < n₀)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    (hE : ∀ v ∈ T, nE ≤ topAt cfg tr time v gst)
    {u : Validator} (hu : u ∈ H) {i : ℕ} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (u, inp)) {n : ℕ}
    (hqn : cfg.q ≤ ((stateBefore cfg tr (i + 1) u).disk.authorsAt n).card)
    (hn₀ : n₀ ≤ n) {τ : ℕ} (hτ : time i + 2 * (Δ + Δₛ) ≤ τ) (hτ₁ : τ ≤ t₁)
    {v : Validator} (hv : v ∈ T) {c : BlockId} (hcU : c ∈ R.ids)
    (hcT : (R.block c).creator ∈ T) (hcr : (R.block c).round = n) :
    c ∈ (stateAt cfg tr time v τ).disk.ids := by
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  set S := ((stateBefore cfg tr (i + 1) u).disk.authorsAt n).filter (· ∈ T) with hSdef
  have hS : cfg.f + 1 ≤ S.card := quorum_reliable hadm hTc hqn
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
    obtain ⟨j, hj, inpj, hj', hjz⟩ := persisted_of_stored htime hu (hTH hwT) hz.1 hzc
    have := top_of_built hmono hj' hjz (τ := time i) (hmono j i (by omega) hil)
    have hzf : ((stateBefore cfg tr (i + 1) u).disk.full z).round = n := by
      rw [((stateBefore cfg tr (i + 1) u).disk.full_fields z).1]; exact hz.2
    exact ⟨this.1, by simpa [hzf] using this.2⟩
  -- so it armed past GST
  have hgi : gst ≤ time i := by
    obtain ⟨w, hw⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    by_contra h
    have hr := (rises_before (cfg := cfg) (tr := tr) w
      (eventsBy_mono (tr := tr) (time := time) (show time i ≤ gst by omega))).1
    have h₁ := hbelow w (Finset.mem_filter.mp hw).2
    have h₂ := (hSn w hw).2
    change topAt cfg tr time w (time i) ≤ topAt cfg tr time w gst at hr
    omega
  -- so every reliable node is `A` later
  have hall : ∀ w ∈ T, n ≤ topAt cfg tr time w (time i + (Δ + Δₛ)) := fun w hw =>
    catches_up hq hadm hfa hf hid htime hinj hbase hTH hmono harr hstart
      (fun w hw => (Finset.mem_filter.mp hw).2) hS hgi (by omega)
      (hE₀.trans (eventsBy_mono (by omega)))
      ((eventsBy_mono (tr := tr) (time := time) (show time i + (Δ + Δₛ) ≤ t₁ by omega)).trans hE₁)
      hSn hsp hw (hE w hw) (hTB w hw).1 (hTB w hw).2
  -- the block's build
  obtain ⟨ic, inpc, e, hic, he, rfl, her, hbt⟩ :=
    event_of_base (time := time) hinj htime hbase (hTH hcT) hcU rfl (by omega)
  rw [hcr] at her hbt
  have hicl : ic < tr.length := (List.getElem?_eq_some_iff.mp hic).1
  have hws := started_at hadm hfa hid htime hTH hmono hstart hcT (τ := time i + (Δ + Δₛ)) (by omega)
  have hbw := builtAt_le_of_top hmono hws (hall _ hcT)
    (harr.no_jump hmono hcT ((hbelow _ hcT).trans_le hn₀) (by omega)
      (regular_past hbase hE₀ hE₁ (hTH hcT) (by omega)))
  by_cases hvw : (R.block e.1).creator = v
  · rw [hvw] at hic
    exact (Converge.persist_stored hic he ((lt_eventsBy hmono hicl).mpr (by omega))
      (hbase.keep (hTH hv) ((eventsBy_mono (tr := tr) (time := time) hτ₁).trans hE₁)
        (fun _ => by rw [her]; omega))).1
  · exact harr.arrives _ hcT v hv hvw ic inpc hic e he
      (by rw [her]; exact ((hbelow _ hcT).trans_le hn₀).le) (time i + (Δ + Δₛ)) τ (by omega)
      (by rw [max_eq_left (by omega)]; omega) hτ₁

/-- **No honest author has two known blocks of a round.** -/
theorem known_twin (htime : Converge.TimelyAuthentic cfg H tr)
    {y z : BlockId × Block Validator BlockId Payload} (hy : y ∈ knownAll cfg H tr)
    (hz : z ∈ knownAll cfg H tr) (hne : y.1 ≠ z.1) (hc : y.2.creator = z.2.creator)
    (hr : y.2.round = z.2.round) : y.2.creator ∉ H := fun hu => by
  obtain ⟨w, hw, hyw⟩ := hy
  obtain ⟨w', hw', hzw⟩ := hz
  have h₁ := own_known (E := tr.length) htime hw hu le_rfl hyw rfl
  have h₂ := own_known (E := tr.length) htime hw' hu le_rfl hzw hc.symm
  exact hne (congrArg Prod.fst (eq_of_persists _ h₁ h₂ hr))

variable {N n₀ t : ℕ} (hσ : cfg.σ = boundedSel)
  (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f)
  (htime : Converge.TimelyAuthentic cfg H tr)
  (hinj : Converge.HashInjective cfg H tr) (hev : Converge.EvidenceAuthentic cfg H tr)
  (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
  (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
  (hbelow : ∀ v ∈ T, topAt cfg tr time v gst < n₀)
  (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
  (hN : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (Δ + Δₛ) ≤ t₁)
  {R : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H} {B E₀ E₁ : ℕ}
  (hbase : Base cfg H tr R B E₀ E₁) (hE₀ : E₀ ≤ eventsBy tr time gst)
  (hE₁ : eventsBy tr time t₁ ≤ E₁) (hB₀ : B < n₀)
  (hBV : (B + 1 + cfg.p.voteOffset ≤ n₀ ∧ ∀ v ∈ H, topAt cfg tr time v gst < n₀) ∨
      B = 0 ∧ cfg.drops = false)
  (hTB : ∀ v ∈ T, B ≤ topAt cfg tr time v gst ∧
    (cfg.drops = true → B + 1 ≤ topAt cfg tr time v gst))
include hσ hadm hfa hf htime hinj hev hTH hmono harr hbelow hst hN ht₁ hbase hE₀ hE₁ hB₀ hBV hTB

/-- **By `A` after every reliable node reached a round, each holds every
reliable block up to it**. -/
theorem reliable_held {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {r : ℕ} (hr₀ : n₀ ≤ r)
    (hrN : r ≤ N) {c : BlockId}
    (hcU : c ∈ R.ids)
    (hcu : (R.block c).creator = u)
    (hcr : (R.block c).round = r) :
    c ∈ (stateAt cfg tr time v (t + (Δ + Δₛ))).disk.ids := by
  obtain ⟨i, inp, e, hi, he, rfl, her, hbt⟩ :=
    event_of_base (time := time) hinj htime hbase (hTH hu) hcU hcu (by omega)
  rw [hcr] at her hbt
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hgt : gst ≤ t := by
    by_contra h
    have := (rises_before (cfg := cfg) (tr := tr) v
      (eventsBy_mono (tr := tr) (time := time) (show t ≤ gst by omega))).1
    have h₁ := hbelow v hv
    have h₂ := hN v hv
    change topAt cfg tr time v t ≤ topAt cfg tr time v gst at this
    omega
  have hit : time i ≤ t := hbt ▸ builtAt_le_of_top hmono (hst u hu) ((hN u hu).trans' hrN)
    (harr.no_jump hmono hu ((hbelow u hu).trans_le hr₀) (by omega)
      (regular_past hbase hE₀ hE₁ (hTH hu) (by omega)))
  by_cases huv : u = v
  · subst huv
    exact (Converge.persist_stored hi he ((lt_eventsBy hmono hil).mpr (by omega))
      (hbase.keep (hTH hv) ((eventsBy_mono (tr := tr) (time := time) ht₁).trans hE₁)
        (fun _ => by rw [her]; omega))).1
  exact harr.arrives u hu v hv huv i inp hi e he
    (by rw [her]; exact ((hbelow u hu).trans_le hr₀).le) t (t + (Δ + Δₛ)) hit
    (by rw [max_eq_left hgt]) ht₁

/-- **An honest block that did not pass the tests comes after every
reliable block of the round below reached every reliable node**, from
round `n₀` on: its builder waited the round's timer, armed with a quorum
of the round a timeout before, and `2A` after the arming every reliable
node holds them (`timer_set`, `waited_holds`); or it was behind, and holds
an earlier honest block of its round that did not pass the tests either,
else the references it lends would have (`behind_honest`,
`ready_transfer`), by induction on the event that built it. -/
theorem held_before (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg H tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hn₁ : 1 ≤ n₀)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    (hE : ∀ v ∈ T, nE ≤ topAt cfg tr time v gst) (hnE : nE < n₀) :
    ∀ j {h : Validator} {inp : Input Validator BlockId Payload}
      {x : State Validator BlockId Payload} {n : ℕ} {c : BlockId}, h ∈ H → n₀ ≤ n →
    time j ≤ t →
    c ∈ R.ids →
    (R.block c).creator = h →
    (R.block c).round = n + 1 →
    tr[j]? = some (h, inp) →
    BuildState (cfg.at h) R B (knownAll cfg H tr) (stateBefore cfg tr j h) inp x →
    x.top = some n → c ∉ x.disk.ids →
    (∃ y o, tryBuild (cfg.at h) x = some (y, o) ∧
      (c, R.block c) ∈
        persists o ∧
      (c, R.block c) ∈
        persists (outputsAt cfg tr j)) →
    DiskRises (cfg.at h) x (stateBefore cfg tr (j + 1) h) →
    (n ∈ x.fired ∨ behind (cfg.at h) x.disk n) →
    ¬ (reachReady (cfg.at h) x.disk (refsAt (cfg.at h) x.disk n x.own x.evidence) n
      (excluded (cfg.at h) x.disk n x.evidence) = true ∧
      certReady (cfg.at h) x.disk (refsAt (cfg.at h) x.disk n x.own x.evidence) n
        (excluded (cfg.at h) x.disk n x.evidence) = true) →
    ∃ τ < time j, ∀ v ∈ T,
      ∀ b ∈ R.ids,
      (R.block b).creator ∈ T →
      (R.block b).round = n →
      b ∈ (stateAt cfg tr time v τ).disk.ids := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro h inp x n c hh hn₀ hjt hcU hcv hcr hj₀ hbs hxt hcx hbuild hgx hexit hnr
  obtain ⟨y, o, hb, heo, he⟩ := hbuild
  have hj₀l : j < tr.length := (List.getElem?_eq_some_iff.mp hj₀).1
  have hjE : j < E₁ := ((lt_eventsBy hmono hj₀l).mpr (show time j ≤ t₁ by omega)).trans_le hE₁
  have hnV : cfg.drops = true → B + 1 + cfg.p.voteOffset ≤ n := fun hd => by
    rcases hBV with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact absurd (h.symm.trans hd) Bool.false_ne_true
  have hBn : B ≤ n - cfg.p.voteOffset := by rcases hBV with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  rcases hexit with hfired | hbeh
  · -- it waited the round's timer, armed with a quorum of the round
    have hj : ∃ k ≤ j, tr[k]? = some (h, Input.timer n) := by
      rcases hbs.fired _ hfired with h' | h'
      · obtain ⟨k, hk, hkt⟩ := fired_before (cfg := cfg) j _ h'
        exact ⟨k, hk.le, hkt⟩
      · exact ⟨j, le_rfl, by rw [hj₀, h']⟩
    obtain ⟨k, hk, hkt⟩ := hj
    obtain ⟨i, hik, hiv, t', ht', hnt, hq'⟩ := timer_set hwait hh hkt
    obtain ⟨inpi, hi⟩ := Converge.event_of_map hiv
    -- the node was not above round `n` when it set the timer: from then on it
    -- would build above `n + 1` only
    have htn : t' = n := by
      by_contra hne
      have hge : n + 1 ≤ (stateBefore cfg tr j h).top.getD 0 := by
        have := (rises_before (cfg := cfg) (tr := tr) h (show i + 1 ≤ j by omega)).1
        rw [ht'] at this; simp only [Option.getD_some] at this; omega
      rw [outputsAt_eq hj₀] at he
      rcases step_above (cfg := cfg.at h) _ he with h0 | h0
      · rw [h0] at hge; simp at hge
      · simp only at h0; rw [hcr] at h0; omega
    subst htn
    obtain ⟨hti, hqn⟩ := hq' rfl (by omega)
    replace hqn := hqn.resolve_left fun h => by
      have := hbase.floor_drops hh (show i + 1 ≤ E₁ by omega) h.1
      have := h.2
      omega
    have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hkt).1
    have htk := hmono k j hk hj₀l
    have hτ := hto t'
    refine ⟨time i + 2 * (Δ + Δₛ), by omega, fun v hv b hbU hbT hbr => ?_⟩
    exact waited_holds hq hadm hfa hf hid htime hinj hbase hE₀ hE₁ hTB hTH hmono harr hstart hTc
      hbelow hB₀ hsp hE hh hi hqn hn₀ le_rfl (by omega) hv hbU hbT hbr
  · -- it was behind: an earlier honest block of the round
    obtain ⟨w', hw'H, hw'h, j', hj'j, inp', z, hj', hz, hzr, hzx, hzb⟩ :=
      behind_honest htime hinj hf hh hj₀ hbs hb heo he hcr hgx
        (hbase.keep hh (show j + 1 ≤ E₁ by omega) (fun _ => by omega)) hbeh
    have hzr₀ : (x.disk.blk z.1).round = n + 1 := by
      rw [← (x.disk.full_fields z.1).1, hzb, hzr]
    have hzU : z.1 ∈ R.ids := hbs.cut.above_mem hzx (by omega)
    have hzB : R.block z.1 = z.2 := (hbs.cut.above_eq hzx (by omega)).trans hzb
    have hzc : (R.block z.1).creator = w' := by
      rw [hzB]
      exact (Local.authored _ _ _ (cfg.at w') _ z (persists_of_event hj' hz)).2
    have hzr' : (R.block z.1).round = n + 1 := by rw [hzB, hzr]
    obtain ⟨iw, inpw, xw, oww, hiw, -, hbsw, hshw, hzxw, ⟨yw, ow, hbw, heow, hew⟩, hzrefs, hzsub,
      hgxw, hexitw, hzpay⟩ := built_block time hσ htime hinj hbase hw'H hzU hzc hzr' (by omega)
        hnV ⟨j', by omega, by rw [hj']; rfl, z, hz, hzr⟩
        (fun hd => not_built_before hmono hE₀ (by
          rcases hBV with ⟨-, h⟩ | ⟨-, h⟩
          · have := h w' hw'H; omega
          · exact absurd (h.symm.trans hd) Bool.false_ne_true))
    have hiwj : iw = j' := persist_events_eq hiw hj' hew hz (by rw [hzr', hzr])
    subst hiwj
    -- the earlier block did not pass the tests, else the node would have
    have hnrw : ¬ (reachReady (cfg.at w') xw.disk (refsAt (cfg.at w') xw.disk n oww xw.evidence) n
      (excluded (cfg.at w') xw.disk n xw.evidence) = true ∧
        certReady (cfg.at w') xw.disk (refsAt (cfg.at w') xw.disk n oww xw.evidence) n
          (excluded (cfg.at w') xw.disk n xw.evidence) = true) := by
      intro hrw
      apply hnr
      obtain ⟨Bx, hiXx⟩ := hbs.inv
      obtain ⟨Bw, hiXw⟩ := hbsw.inv
      have hxn : x.top.getD 0 ≤ n := by rw [hxt]; rfl
      have hzr₁ : (x.disk.blk z.1).round = n + 1 := by
        rw [← (x.disk.full_fields z.1).1, hzb, hzr]
      have hkz : x.disk.kept[z.1]? = none :=
        hbs.unkept hxn hnV (by rw [hzr₁]; exact le_trans (Nat.sub_le _ _) (Nat.le_succ n))
      have hZR : (x.disk.blk z.1).refs = refsAt (cfg.at w') xw.disk n oww xw.evidence := by
        rw [← x.disk.full_of_kept_none hkz, ← hbs.cut.above_eq hzx (by omega), hzrefs]
      -- no block on disk has the identifier of a next block of the node's own
      have hfresh : ∀ (P : Payload) Q,
          (cfg.at h).idOf ⟨n + 1, (cfg.at h).me, Q, P⟩ ∉ x.disk.ids := by
        intro P Q hin
        obtain ⟨Bs, hiX⟩ := hbs.inv
        obtain ⟨v', hv', hk⟩ := hiX.known _ hin
        have hidk := Converge.id_of_knownIn (knownOf_sub hv' hk)
        have hraw : x.disk.full _ = (⟨n + 1, h, Q, P⟩ : Block Validator BlockId Payload) :=
          hid hidk.symm
        have hin₁ := (x.disk.full_fields ((cfg.at h).idOf ⟨n + 1, (cfg.at h).me, Q, P⟩)).1
        rw [hraw] at hin₁
        change n + 1 = _ at hin₁
        have heq := hbs.cut.above_eq hin (by omega)
        have := R.eq_of_creator_eq (hbs.cut.above_mem hin (by omega)) hcU hh
          (by rw [heq, hraw]) hcv (by rw [heq, hraw, hcr])
        exact hcx (this ▸ hin)
      obtain ⟨Bs, hiX⟩ := hbs.inv
      have hxF := hbs.floor_le hxn hnV
      obtain ⟨hlZ, hlb⟩ := lent_buildable (cfg := cfg.at h)
        (fun j hj hjr => hiX.above j hj (by omega)) hzx hzr₁ hkz hfa hfresh x.evidence
        fun j hj hjr => (hbs.holds hfa).exposed hj (hiX.above j hj (by omega)).2
      have hRR : refsAt (cfg.at w') xw.disk n oww xw.evidence ⊆ lent x.disk z.1 := by
        unfold lent; rw [hZR]
      have ho : ∀ k, oww = some k → (xw.disk.blk k).creator = (cfg.at w').me := fun k hk => by
        rcases hshw.2.2 with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
        · obtain ⟨k', hk', -, -, hkc⟩ := hbsw.own n ht
          rw [hoe, hk'] at hk
          cases hk
          exact hkc
        · rw [hon] at hk; cases hk
      -- the node leaves out every author the lender left out
      have hXX : excluded (cfg.at w') xw.disk n xw.evidence ⊆
          excluded (cfg.at h) x.disk n x.evidence :=
        excluded_lent hfa hbsw hbs (Or.inr (by have := hbsw.floor_le hshw.2.1 hnV; omega)) ho hzx
          (by rw [hzr₁]; omega) hzpay
      -- the lent references lie at round `n`
      have hRw : ∀ b ∈ refsAt (cfg.at w') xw.disk n oww xw.evidence, (xw.disk.blk b).round = n :=
        fun b hb => by
          rcases mem_refsAt_of hb with h' | h'
          · exact (Store.mem_atRound.mp h').2
          · rcases hshw.2.2 with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
            · obtain ⟨k', hk', -, hkr, -⟩ := hbsw.own n ht
              rw [hoe, hk'] at h'; cases h'; exact hkr
            · rw [hon] at h'; cases h'
      have hready := ready_transfer (cfg := cfg.at h) hσ (fun h => certThreshold_pos hadm h)
        hbsw.cut hbs.cut hBn hzsub hRR hlZ (fun a _ ha => hbsw.unkept hshw.2.1 hnV ha)
        (fun a _ ha => hbs.unkept hxn hnV ha) hRw (fun b hb => by
          have := x.disk.pred z.1 hzx b (hRR hb)
          change (x.disk.blk b).round + 1 = (x.disk.blk z.1).round at this
          omega) hXX hrw.1 hrw.2
      -- the lent references avoid the authors the node leaves out
      have hAD := refs_avoid_spread (r := n) hsp hiw hw'H hbsw hew (by rw [hzr']; omega) ho
      have hav : ∀ k ∈ lent x.disk z.1, (x.disk.blk k).creator ∉
          excluded (cfg.at h) x.disk n x.evidence := fun k hk hmk => by
        have hk' : k ∈ refsAt (cfg.at w') xw.disk n oww xw.evidence := by
          rw [← hZR]; exact hk
        have hkx : k ∈ x.disk.ids := x.disk.complete z.1 hzx k hk
        have hkn : (x.disk.blk k).round = n := by
          have := x.disk.pred z.1 hzx k hk
          change (x.disk.blk k).round + 1 = (x.disk.blk z.1).round at this
          omega
        have hcr : (x.disk.blk k).creator = (xw.disk.blk k).creator := by
          rw [← hbs.cut.above_creator hkx (by omega),
            ← hbsw.cut.above_creator (hzsub hk') (by rw [hRw k hk']; omega)]
        exact hAD k hk' (hcr ▸ excluded_sub_spread hsp hbs (Or.inr ⟨hfa, by omega⟩) hmk)
      exact refsAt_ready (cfg := cfg.at h) hzx hzr₁
        (by rw [← hbs.cut.above_creator hzx (by omega), hzc]; exact hw'h) hready hlb hav
    have hexitw' : n ∈ xw.fired ∨ behind (cfg.at w') xw.disk n := by
      rcases hexitw with h' | ⟨h₁, -⟩
      · exact absurd h' hnrw
      · exact h₁.imp (·.2) id
    -- so it built above its top, on its own block
    have hxtw : xw.top = some n ∧ oww = xw.own := by
      rcases hshw.2.2 with h' | ⟨-, -, h₁, h₂⟩
      · exact h'
      · exact absurd ⟨h₁, h₂⟩ hnrw
    have hj'l : iw < tr.length := (List.getElem?_eq_some_iff.mp hiw).1
    have htj' := hmono iw j hj'j.le hj₀l
    obtain ⟨τ, hτ, hall⟩ := ih iw hj'j hw'H hn₀ (by omega) hzU hzc hzr' hiw hbsw hxtw.1 hzxw
      ⟨yw, ow, hbw, heow, hew⟩ hgxw hexitw' (hxtw.2 ▸ hnrw)
    exact ⟨τ, by omega, hall⟩

/-- **A reliable block that did not pass the tests references every
reliable block of the round below**, from round `n₀` on: when it was
built, every reliable block of the round below had reached its builder
(`held_before`). -/
theorem refs_all (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg H tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hqT : cfg.q ≤ T.card)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    (hE : ∀ v ∈ T, nE ≤ topAt cfg tr time v gst) :
    ∀ i₀ {v : Validator} {inp : Input Validator BlockId Payload}
      {x : State Validator BlockId Payload} {n : ℕ} {c : BlockId}, v ∈ T → n₀ ≤ n → n + 1 ≤ N →
    c ∈ R.ids →
    (R.block c).creator = v →
    (R.block c).round = n + 1 →
    tr[i₀]? = some (v, inp) → builtAt cfg tr time v (n + 1) = time i₀ →
    BuildState (cfg.at v) R B (knownAll cfg H tr) (stateBefore cfg tr i₀ v) inp x →
    x.top = some n → c ∉ x.disk.ids →
    (∃ y o, tryBuild (cfg.at v) x = some (y, o) ∧
      (c, R.block c) ∈
        persists o ∧
      (c, R.block c) ∈
        persists (outputsAt cfg tr i₀)) →
    (R.block c).refs =
      refsAt (cfg.at v) x.disk n x.own x.evidence →
    DiskRises (cfg.at v) x (stateBefore cfg tr (i₀ + 1) v) →
    (n ∈ x.fired ∨ behind (cfg.at v) x.disk n) →
    (refsAt (cfg.at v) x.disk n x.own x.evidence = refsFor (cfg.at v) x.disk n x.own x.evidence ∨
      buildable (cfg.at v) x.disk n (refsFor (cfg.at v) x.disk n x.own x.evidence) x.evidence =
        false) →
    ¬ (reachReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk n x.own x.evidence) n
      (excluded (cfg.at v) x.disk n x.evidence) = true ∧
      certReady (cfg.at v) x.disk (refsAt (cfg.at v) x.disk n x.own x.evidence) n
        (excluded (cfg.at v) x.disk n x.evidence) = true) →
    ∀ b ∈ R.ids,
      (R.block b).creator ∈ T →
      (R.block b).round = n →
      b ∈ (R.block c).refs := by
  intro i₀ v inp x n c hv hn₀ hnN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild hcrefs hgx hexit hfor hnr
    b hbU hbT hbr
  have hi₀l : i₀ < tr.length := (List.getElem?_eq_some_iff.mp hi₀).1
  have hi₀t : time i₀ ≤ t :=
    hbt ▸ builtAt_le_of_top hmono (hst v hv) ((hN v hv).trans' hnN)
      (harr.no_jump hmono hv ((hbelow v hv).trans_le (by omega)) (by
        have h₁ := hbelow v hv
        have h₂ := hN v hv
        by_contra hlt
        have h₃ := (rises_before (cfg := cfg) (tr := tr) v
          (eventsBy_mono (tr := tr) (time := time) (show t ≤ gst by omega))).1
        change topAt cfg tr time v t ≤ topAt cfg tr time v gst at h₃
        omega) (regular_past hbase hE₀ hE₁ (hTH hv) (by omega)))
  have hn₁ : 1 ≤ n₀ := by have := hbelow v hv; omega
  obtain ⟨τ, hτ, hall⟩ := held_before hσ hadm hfa hf htime hinj hev hTH hmono harr hbelow hst hN
      ht₁ hbase hE₀ hE₁ hB₀ hBV hTB hq hto
    hwait hid hstart hTc hn₁ hsp hE (by have := hE v hv; have := hbelow v hv; omega) i₀ (hTH hv)
    hn₀ hi₀t hcU hcv hcr hi₀ hbs hxt hcx hbuild hgx hexit hnr
  have hE : eventsBy tr time τ ≤ i₀ := by
    by_contra h
    have := (lt_eventsBy (t := τ) hmono hi₀l).mp (by omega)
    omega
  have hi₀E : i₀ < E₁ := ((lt_eventsBy hmono hi₀l).mpr (show time i₀ ≤ t₁ by omega)).trans_le hE₁
  have hnV : cfg.drops = true → B + 1 + cfg.p.voteOffset ≤ n := fun hd => by
    rcases hBV with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact absurd (h.symm.trans hd) Bool.false_ne_true
  have hxF := hbs.floor_le (show x.top.getD 0 ≤ n by rw [hxt]; rfl) hnV
  -- the blocks of round `n` at `τ` stay on the disk up to the build
  have hheld : ∀ b ∈ R.ids, (R.block b).creator ∈ T → (R.block b).round = n → b ∈ x.disk.ids :=
    fun b hbU hbT hbr => by
      have hb : b ∈ (stateBefore cfg tr (eventsBy tr time τ) v).disk.ids := hall v hv b hbU hbT hbr
      have hbn : ((stateBefore cfg tr (eventsBy tr time τ) v).disk.blk b).round = n := by
        rw [← ((stateBefore cfg tr (eventsBy tr time τ) v).disk.full_fields b).1,
          eq_of_known hid hbase (Converge.knownBefore_sub (hTH hv) _
            ((Converge.inv_before (cfg := cfg) (tr := tr) _ v).known b hb)) hbU (by omega), hbr]
      have h₁ := (Converge.diskRises_before (cfg := cfg) (tr := tr) v hE).2 b hb (by
        rw [hbn]; exact hbase.keep (hTH hv) hi₀E.le fun _ => by omega)
      have hbn' : ((stateBefore cfg tr i₀ v).disk.blk b).round = n := by
        rw [← (Store.full_fields _ b).1, h₁.2, (Store.full_fields _ b).1, hbn]
      exact (hbs.grows.2 b h₁.1 (Or.inr (by rw [hbn']; omega))).1
  have hbx : b ∈ x.disk.ids := hheld b hbU hbT hbr
  -- the evidence the honest nodes knew names no honest author
  have hK : ∀ y ∈ knownAll cfg H tr, ∀ e ∈ (cfg.at v).xp.ev y.2.payload, e.2.1 ≠ e.2.2 →
      e.1 ∉ H := fun y hy e he hne => by
    obtain ⟨w, hw, hyw⟩ := hy
    exact hev y (knownOf_sub hw hyw) e he hne
  have hnx : ∀ a ∈ H, a ∉ excluded (cfg.at v) x.disk n x.evidence :=
    fun a ha => hbs.not_excluded hK (fun _ hy _ hz h₁ h₂ h₃ => known_twin htime hy hz h₁ h₂ h₃)
      ha (Or.inr ⟨hfa, by omega⟩)
  have hfor' : refsAt (cfg.at v) x.disk n x.own x.evidence =
      refsFor (cfg.at v) x.disk n x.own x.evidence := by
    refine hfor.resolve_right fun hnb => ?_
    -- every reliable author has a round-`n` block on the disk, left out by none
    have hTA : T ⊆ authorsIn x.disk.toRecord x.disk.ids n \ excluded (cfg.at v) x.disk n
        x.evidence := by
      intro w hw
      obtain ⟨i, inpi, e, hi, he, her, -, hit⟩ := built_of_top (cfg := cfg) hmono (hst w hw)
        ((hN w hw).trans' (by omega)) (harr.no_jump hmono hw ((hbelow w hw).trans_le hn₀)
          (by
            have h₁ := hbelow w hw
            have h₂ := hN w hw
            by_contra hlt
            have h₃ := (rises_before (cfg := cfg) (tr := tr) w
              (eventsBy_mono (tr := tr) (time := time) (show t ≤ gst by omega))).1
            change topAt cfg tr time w t ≤ topAt cfg tr time w gst at h₃
            omega) (regular_past hbase hE₀ hE₁ (hTH hw) (by omega)))
      have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
      have hiE : i + 1 ≤ E₁ :=
        ((lt_eventsBy hmono hil).mpr (show time i ≤ t₁ by omega)).trans_le hE₁
      obtain ⟨heU, heR, heC⟩ := built_mem hbase (hTH hw) hi he hiE (by rw [her]; omega)
        (hbase.keep (hTH hw) hiE (fun _ => by rw [her]; omega))
      have hex := hheld e.1 heU (by rw [heC]; exact hw) (by rw [heR, her])
      obtain ⟨Bs, hiX⟩ := hbs.inv
      obtain ⟨v', hv', hk⟩ := hiX.known _ hex
      have hxe := eq_of_known hid hbase (knownOf_sub hv' hk) heU (by rw [heR, her]; omega)
      refine Finset.mem_sdiff.mpr ⟨mem_authorsIn.mpr ⟨e.1, hex, ?_, ?_⟩, hnx w (hTH hw)⟩
      · change (x.disk.blk e.1).round = n
        rw [← (x.disk.full_fields e.1).1, hxe, heR, her]
      · change (x.disk.blk e.1).creator = w
        rw [← (x.disk.full_fields e.1).2.1, hxe, heC]
    have hfresh : (cfg.at v).idOf (blockOn (cfg.at v) x.disk n
        (refsFor (cfg.at v) x.disk n x.own x.evidence) x.evidence) ∉ x.disk.ids := by
      intro hin
      obtain ⟨Bs, hiX⟩ := hbs.inv
      obtain ⟨v', hv', hk⟩ := hiX.known _ hin
      have hidk := Converge.id_of_knownIn (knownOf_sub hv' hk)
      have hraw : x.disk.full ((cfg.at v).idOf (blockOn (cfg.at v) x.disk n
          (refsFor (cfg.at v) x.disk n x.own x.evidence) x.evidence)) =
          blockOn (cfg.at v) x.disk n (refsFor (cfg.at v) x.disk n x.own x.evidence) x.evidence :=
        hid hidk.symm
      have heq := hbs.cut.above_eq hin
        (by rw [← (x.disk.full_fields _).1, hraw]; show B < n + 1; omega)
      have := R.eq_of_creator_eq
        (hbs.cut.above_mem hin (by rw [← (x.disk.full_fields _).1, hraw]; show B ≤ n + 1; omega))
        hcU (hTH hv)
        (by rw [heq, hraw]; rfl) hcv (by rw [heq, hraw, hcr]; rfl)
      exact hcx (this ▸ hin)
    obtain ⟨o', hoo, hoi, hor, hoc⟩ := hbs.own n hxt
    obtain ⟨Bs, hiX⟩ := hbs.inv
    have hb := refsFor_buildable (cfg := cfg.at v) (st := x.disk) (o := x.own) x.evidence hfa
      (fun j hj hjr => (hbs.holds hfa).exposed hj (hiX.above j hj (by omega)).2)
      (fun j hj => by rw [hoo] at hj; cases hj; exact ⟨hoi, hor, hoc⟩)
      (hqT.trans (Finset.card_le_card hTA)) hfresh
    rw [hnb] at hb
    cases hb
  rw [hcrefs, hfor']
  obtain ⟨Bs, hiX⟩ := hbs.inv
  obtain ⟨v', hv', hk⟩ := hiX.known _ hbx
  have hxb := eq_of_known hid hbase (knownOf_sub hv' hk) hbU (by omega)
  have hbr' : (x.disk.blk b).round = n := by rw [← (x.disk.full_fields b).1, hxb, hbr]
  have hbc : (x.disk.blk b).creator = (R.block b).creator := by
    rw [← (x.disk.full_fields b).2.1, hxb]
  exact mem_refsFor_of_cut hbs.cut (by omega) hbx hbr' (by rw [hbc]; exact hTH hbT)
    (fun _ => hbs.own _ hxt) (hnx _ (by rw [hbc]; exact hTH hbT))

/-- **Reach or reference, at a reliable node**, from round `n₀` on: a block
of `v` at the round above slot `k`'s round plus `m`, below
the vote offset, reaches the slot's reliable leader block, or references
every block of the leader of the round below. -/
theorem reach_or_refs_node (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg H tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hqT : cfg.q ≤ T.card)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    (hE : ∀ v ∈ T, nE ≤ topAt cfg tr time v gst)
    {v : Validator} (hv : v ∈ T) {k m : ℕ} (hRk : n₀ ≤ cfg.slots.slotRound k) (hlead :
        cfg.slots.leader k ∈ T) {L : BlockId}
    (hL : IsLeaderBlock (S := cfg.slots)
      R k L)
    (hm : m < cfg.p.voteOffset) (hmN : cfg.slots.slotRound k + m + 1 ≤ N) {c : BlockId}
    (hcU : c ∈ R.ids)
    (hcv : (R.block c).creator = v)
    (hcr : (R.block c).round = cfg.slots.slotRound k + m + 1) :
    Reaches R c L ∨
      ∀ b ∈ R.ids,
        (R.block b).creator = cfg.slots.leader k →
        (R.block b).round = cfg.slots.slotRound k + m →
        b ∈ (R.block c).refs := by
  have hnV : cfg.drops = true → B + 1 + cfg.p.voteOffset ≤ cfg.slots.slotRound k := fun hd => by
    rcases hBV with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact absurd (h.symm.trans hd) Bool.false_ne_true
  obtain ⟨ie, inpe, e, hie, hee, hec, her, hbe⟩ :=
    event_of_base (time := time) hinj htime hbase (hTH hv) hcU hcv (by rw [hcr]; omega)
  have hiel : ie < tr.length := (List.getElem?_eq_some_iff.mp hie).1
  have hiet : time ie ≤ t := hbe ▸ builtAt_le_of_top hmono (hst v hv)
    ((hN v hv).trans' (by rw [hcr]; omega))
    (harr.no_jump hmono hv ((hbelow v hv).trans_le (by rw [hcr]; omega)) (by omega)
      (regular_past hbase hE₀ hE₁ (hTH hv) (by omega)))
  obtain ⟨i₀, inp, x, ow, hi₀, hbt, hbs, hsh, hcx, hbuild, hcrefs, hsub, hgx, hexit, -⟩ :=
    built_block time hσ htime hinj hbase (hTH hv) hcU hcv hcr (by omega)
      (fun hd => by have := hnV hd; omega)
      ⟨ie, ((lt_eventsBy hmono hiel).mpr (show time ie ≤ t₁ by omega)).trans_le hE₁,
        by rw [hie]; rfl, e, hee, by rw [her, hcr]⟩
      (fun _ => not_built_before hmono hE₀ (by have := hbelow v hv; omega))
  -- the evidence the honest nodes knew names no honest author, so no honest
  -- leader is left out
  have hlX : cfg.slots.leader k ∉
      excluded (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.evidence :=
    hbs.not_excluded (fun y hy e he hne => by
      obtain ⟨w, hw, hyw⟩ := hy
      exact hev y (knownOf_sub hw hyw) e he hne)
      (fun _ hy _ hz h₁ h₂ h₃ => known_twin htime hy hz h₁ h₂ h₃) (hTH hlead)
      (Or.inr ⟨hfa, (hbs.floor_le hsh.2.1
        fun hd => (hnV hd).trans (Nat.le_add_right _ _)).trans (Nat.sub_le _ _)⟩)
  by_cases hready : reachReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + m) ow x.evidence)
        (cfg.slots.slotRound k + m)
        (excluded (cfg.at v) x.disk (cfg.slots.slotRound k + m)
          x.evidence) = true ∧
      certReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + m) ow x.evidence)
        (cfg.slots.slotRound k + m)
        (excluded (cfg.at v) x.disk (cfg.slots.slotRound k + m)
          x.evidence) = true
  · exact Or.inl (reaches_of_reachReady (cfg := cfg.at v) hbs.cut hready.1 hsub
      (hB₀.le.trans hRk) hm rfl
      (hTH hlead) hlX hL hcrefs)
  · right
    -- not a jump, whose references pass the tests: above its top, on its own block
    obtain ⟨hxt, how⟩ : x.top = some _ ∧ ow = x.own := by
      rcases hsh.2.2 with h' | ⟨-, -, h₁, h₂⟩
      · exact h'
      · exact absurd ⟨h₁, h₂⟩ hready
    subst how
    have hexit' := hexit.resolve_left hready
    have h₁ : (cfg.slots.slotRound k + m ∈ x.fired ∨
        behind (cfg.at v) x.disk (cfg.slots.slotRound k + m)) ∧
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own x.evidence =
          refsFor (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own x.evidence ∨
          buildable (cfg.at v) x.disk (cfg.slots.slotRound k + m)
            (refsFor (cfg.at v) x.disk (cfg.slots.slotRound k + m) x.own x.evidence) x.evidence =
                false) := by
      obtain ⟨h, h'⟩ := hexit'
      exact ⟨h.imp (·.2) id, h'⟩
    intro b hbU hbc hbr
    exact refs_all hσ hadm hfa hf htime hinj hev hTH hmono harr hbelow hst hN ht₁ hbase hE₀ hE₁ hB₀
      hBV hTB hq hto
      hwait hid hstart hTc hqT hsp hE i₀ hv (by omega) hmN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild
      hcrefs hgx h₁.1 h₁.2 hready b hbU
      (by rw [hbc]; exact hlead) hbr

/-- **Certify or reference, at a reliable node**, from round `n₀` on:
where votes are certified a round later, a block of
`v` at the round above slot `k`'s vote round certifies the slot's reliable
leader block, or references every reliable vote of that round. -/
theorem cert_or_refs_node (hq : 2 ≤ cfg.q) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (hwait : Live.TimersAfterSet cfg H tr time) (hid : Function.Injective cfg.idOf)
    (hstart : Live.StartedBy T tr time gst)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hqT : cfg.q ≤ T.card)
    {D : Finset Validator} {nE : ℕ} (hsp : Live.Spread cfg H tr D nE)
    (hE : ∀ v ∈ T, nE ≤ topAt cfg tr time v gst)
    (hvc : cfg.p.voteIsCert = false)
    {v : Validator} (hv : v ∈ T) {k : ℕ} (hRk : n₀ ≤ cfg.slots.slotRound k)
    (hlead : cfg.slots.leader k ∈ T) {L : BlockId}
    (hL : IsLeaderBlock (S := cfg.slots)
      R k L)
    (hkN : cfg.slots.slotRound k + cfg.p.voteOffset + 1 ≤ N) {c : BlockId}
    (hcU : c ∈ R.ids)
    (hcv : (R.block c).creator = v)
    (hcr : (R.block c).round = cfg.slots.slotRound k + cfg.p.voteOffset + 1) :
    Scheme.IsCert cfg.p boundedSel
        R c L ∨
      ∀ b ∈ R.ids,
        (R.block b).creator ∈ T →
        (R.block b).round = cfg.slots.slotRound k + cfg.p.voteOffset →
        boundedSel.Votes R b L →
        b ∈ (R.block c).refs := by
  have hnV : cfg.drops = true → B + 1 + cfg.p.voteOffset ≤ cfg.slots.slotRound k := fun hd => by
    rcases hBV with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact absurd (h.symm.trans hd) Bool.false_ne_true
  obtain ⟨ie, inpe, e, hie, hee, hec, her, hbe⟩ :=
    event_of_base (time := time) hinj htime hbase (hTH hv) hcU hcv (by rw [hcr]; omega)
  have hiel : ie < tr.length := (List.getElem?_eq_some_iff.mp hie).1
  have hiet : time ie ≤ t := hbe ▸ builtAt_le_of_top hmono (hst v hv)
    ((hN v hv).trans' (by rw [hcr]; omega))
    (harr.no_jump hmono hv ((hbelow v hv).trans_le (by rw [hcr]; omega)) (by omega)
      (regular_past hbase hE₀ hE₁ (hTH hv) (by omega)))
  obtain ⟨i₀, inp, x, ow, hi₀, hbt, hbs, hsh, hcx, hbuild, hcrefs, hsub, hgx, hexit, -⟩ :=
    built_block time hσ htime hinj hbase (hTH hv) hcU hcv hcr (by omega)
      (fun hd => by have := hnV hd; omega)
      ⟨ie, ((lt_eventsBy hmono hiel).mpr (show time ie ≤ t₁ by omega)).trans_le hE₁,
        by rw [hie]; rfl, e, hee, by rw [her, hcr]⟩
      (fun _ => not_built_before hmono hE₀ (by have := hbelow v hv; omega))
  -- the evidence the honest nodes knew names no honest author, so no honest
  -- leader is left out
  have hlX : cfg.slots.leader k ∉
      excluded (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.evidence :=
    hbs.not_excluded (fun y hy e he hne => by
      obtain ⟨w, hw, hyw⟩ := hy
      exact hev y (knownOf_sub hw hyw) e he hne)
      (fun _ hy _ hz h₁ h₂ h₃ => known_twin htime hy hz h₁ h₂ h₃) (hTH hlead)
      (Or.inr ⟨hfa, (hbs.floor_le hsh.2.1
        fun hd => (hnV hd).trans (Nat.le_add_right _ _)).trans (Nat.sub_le _ _)⟩)
  by_cases hready : reachReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) ow x.evidence)
        (cfg.slots.slotRound k + cfg.p.voteOffset)
        (excluded (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset)
          x.evidence) = true ∧
      certReady (cfg.at v) x.disk
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) ow x.evidence)
        (cfg.slots.slotRound k + cfg.p.voteOffset)
        (excluded (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset)
          x.evidence) = true
  · obtain ⟨Bx, hiXx⟩ := hbs.inv
    refine Or.inl (isCert_of_certReady (cfg := cfg.at v) hσ hbs.cut hready.2 hsub hvc
      (hB₀.le.trans hRk) rfl
      (hTH hlead) hlX (fun i _ hi => hbs.unkept hsh.2.1
        (fun hd => (hnV hd).trans (Nat.le_add_right _ _))
        (show cfg.slots.slotRound k + cfg.p.voteOffset - cfg.p.voteOffset ≤ _ by
          rw [Nat.add_sub_cancel]; exact hi))
      (fun b hb => ?_) hL hcrefs)
    rcases mem_refsAt_of hb with h' | h'
    · exact (Store.mem_atRound.mp h').2
    · rcases hsh.2.2 with ⟨ht, hoe⟩ | ⟨-, hon, -⟩
      · obtain ⟨k', hk', -, hkr, -⟩ := hbs.own _ ht
        rw [hoe, hk'] at h'; cases h'; exact hkr
      · rw [hon] at h'; cases h'
  · right
    -- not a jump, whose references pass the tests: above its top, on its own block
    obtain ⟨hxt, how⟩ : x.top = some _ ∧ ow = x.own := by
      rcases hsh.2.2 with h' | ⟨-, -, h₁, h₂⟩
      · exact h'
      · exact absurd ⟨h₁, h₂⟩ hready
    subst how
    have hexit' := hexit.resolve_left hready
    have h₁ : (cfg.slots.slotRound k + cfg.p.voteOffset ∈ x.fired ∨
        behind (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset)) ∧
        (refsAt (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own x.evidence =
          refsFor (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own x.evidence ∨
          buildable (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset)
            (refsFor (cfg.at v) x.disk (cfg.slots.slotRound k + cfg.p.voteOffset) x.own x.evidence)
                x.evidence = false) := by
      obtain ⟨h, h'⟩ := hexit'
      exact ⟨h.imp (·.2) id, h'⟩
    intro b hbU hbT hbr _
    exact refs_all hσ hadm hfa hf htime hinj hev hTH hmono harr hbelow hst hN ht₁ hbase hE₀ hE₁ hB₀
      hBV hTB hq hto
      hwait hid hstart hTc hqT hsp hE i₀ hv (by omega) hkN hcU hcv hcr hi₀ hbt hbs hxt hcx hbuild
      hcrefs hgx h₁.1 h₁.2 hready b hbU
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

end Outputs

end Node

end LeanDag
