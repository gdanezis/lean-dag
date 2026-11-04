import LeanDag.Node.Helpers.CatchUp
import LeanDag.Node.Helpers.Base
/-!
# Syncing with dropping on

`docs/dos-bounds.md` Phase 3.2 item 4.3. A node's disk holds the
references of its blocks from its floor up (`Inv.above`), so a node that
holds a block holds what a node with a floor at or above its own needs to
accept it (`needs_held`). Under `SyncedHeld`, a reliable node given a
reliable author's block that a reliable node with a floor at or below its
own holds then holds it within `Δₛ` past GST, or its floor lies above it
(`synced_held`). A node that drops has its floor at the floor at its next
undecided slot (`floorAt`, `floor_eq_before`), so a node that
decided as far as another has a floor at or above the other's
(`floor_le_floor`); and it keeps its own blocks from its floor up
(`Converge.persist_stored`), so a reliable node syncs a reliable author's
block when its floor is at or above the author's (`synced_from_author`).

In a steady window (`Live.Steady`: no reliable node decides, each at the
floor at its next undecided slot `L` or above) the floors are the floor
at slot `L` (`floorAt`, `Steady.floor`), every step is regular (`Steady.regular`), a
reliable block delivered in it is synced (`syncedFrom_steady`), and so, as
past a recovery, reliable blocks arrive (`arrival_steady`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

/-- **A store valid from `F` up holds what a node with a floor at or above
`F` needs to accept a block it holds**, at an injective hash and a store
under its hash. -/
theorem needs_held (hid : Function.Injective cfg.idOf) {st : Store Validator BlockId Payload}
    (hh : ∀ j ∈ st.ids, j = cfg.idOf (st.full j)) {F F' : ℕ}
    (hs : UpperValid cfg.q cfg.xp F st) (hF : F ≤ F') {b : Block Validator BlockId Payload}
    (hb : cfg.idOf b ∈ st.ids) {x : Block Validator BlockId Payload}
    (hx : Live.Needs cfg F' b x) : cfg.idOf x ∈ st.ids := by
  have key : ∀ y : Block Validator BlockId Payload, cfg.idOf y ∈ st.ids → F' ≤ y.round →
      ∀ z : Block Validator BlockId Payload, cfg.idOf z ∈ y.refs → cfg.idOf z ∈ st.ids := by
    intro y hy hyr z hz
    have hfy : st.full (cfg.idOf y) = y := hid (hh _ hy).symm
    have hr : F ≤ (st.blk (cfg.idOf y)).round := by
      rw [← (st.full_fields _).1, hfy]; omega
    exact (hs _ hy hr).1 (by rw [hfy]; exact hz)
  induction hx with
  | ref hr hz => exact key b hb hr _ hz
  | step _ hyr hz ih => exact key _ ih hyr _ hz

/-- **A reliable node syncs a block a reliable node holds from a floor at
or below its own**: given a reliable author's block, at the author's round
at GST or above, that a reliable node `w` with a floor at or below the
receiver's holds at the delivery, the receiver holds it within `Δₛ` past
GST, or its floor lies above it, at an injective hash. -/
theorem synced_held (hid : Function.Injective cfg.idOf) {T : Finset Validator}
    {time : ℕ → ℕ} {gst Δₛ t₁ : ℕ} (hsync : Live.SyncedHeld cfg T tr time gst Δₛ t₁) {j : ℕ}
    {v u : Validator} {id : BlockId} {b : Block Validator BlockId Payload}
    (hj : tr[j]? = some (v, .deliver u id b)) (hv : v ∈ T) (hb : b.creator ∈ T)
    (hidb : id = cfg.idOf b) (hr : topAt cfg tr time b.creator gst ≤ b.round) {w : Validator}
    (hw : w ∈ T) (hbw : cfg.idOf b ∈ (stateBefore cfg tr j w).disk.ids)
    (hF : (stateBefore cfg tr j w).floor ≤ (stateBefore cfg tr j v).floor) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (hτ₁ : τ ≤ t₁) :
    id ∈ (stateAt cfg tr time v τ).disk.ids ∨ b.round < (stateAt cfg tr time v τ).floor :=
  hsync j v u id b hj hv hb hidb hr (fun _ hx => ⟨w, hw, needs_held hid
    (fun i hi => knownBefore_hashed ((Converge.inv_before j w).known i hi))
    (Converge.inv_before j w).above hF hbw hx⟩) τ hτ hτ₁

/-- **What a node at floor `F` needs to accept a block lies at or above `F`
only when the block does.** -/
theorem Needs.le_round {F : ℕ} {b x : Block Validator BlockId Payload}
    (h : Live.Needs cfg F b x) : F ≤ b.round := by
  induction h with
  | ref hr _ => exact hr
  | step _ _ _ ih => exact ih

/-- **A node that drops has its floor at the floor at its next undecided
slot** (`floorAt`). -/
theorem floor_eq_before (hdr : cfg.drops = true) (v : Validator) (i : ℕ) :
    (stateBefore cfg tr i v).floor = floorAt cfg (stateBefore cfg tr i v).lo := by
  have hdr' : (cfg.at v).drops = true := hdr
  refine le_antisymm ?_ ?_
  · have h := (Converge.inv_before (cfg := cfg) (tr := tr) i v).floor
    unfold floorOf at h
    rw [if_pos hdr'] at h
    exact h
  · rcases (Converge.diskRises_before (cfg := cfg) (tr := tr) v (Nat.zero_le i)).1.2 hdr' with
      h | h
    · rw [stateBefore_zero] at h
      simp only [State.init] at h
      rw [h, floorAt_zero]
      exact Nat.zero_le _
    · exact h

/-- **A node that drops and decided as far as another has a floor at or
above the other's.** -/
theorem floor_le_floor (hdr : cfg.drops = true) (u v : Validator) (i : ℕ)
    (h : (stateBefore cfg tr i u).lo ≤ (stateBefore cfg tr i v).lo) :
    (stateBefore cfg tr i u).floor ≤ (stateBefore cfg tr i v).floor := by
  have hdr' : (cfg.at u).drops = true := hdr
  have hu := (Converge.inv_before (cfg := cfg) (tr := tr) i u).floor
  unfold floorOf at hu
  rw [if_pos hdr'] at hu
  rw [floor_eq_before hdr v i]
  exact hu.trans (floorAt_mono h)

/-- **A reliable node syncs a reliable author's block when its floor is at
or above the author's** at the delivery: the author keeps its block from
its floor up, and the block's history with it (`synced_held`); below the
receiver's floor the block needs nothing. -/
theorem synced_from_author (hid : Function.Injective cfg.idOf) {T : Finset Validator}
    {time : ℕ → ℕ} {gst Δₛ t₁ : ℕ} (hsync : Live.SyncedHeld cfg T tr time gst Δₛ t₁)
    {a j : ℕ} {u v w : Validator} {inp : Input Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (ha : tr[a]? = some (u, inp))
    (hb : (id, b) ∈ persists (outputsAt cfg tr a)) (haj : a < j)
    (hj : tr[j]? = some (v, .deliver w id b)) (hu : u ∈ T) (hv : v ∈ T)
    (hr : topAt cfg tr time u gst ≤ b.round)
    (hF : (stateBefore cfg tr j u).floor ≤ (stateBefore cfg tr j v).floor) {τ : ℕ}
    (hτ : max (time j) gst + Δₛ ≤ τ) (hτ₁ : τ ≤ t₁) :
    id ∈ (stateAt cfg tr time v τ).disk.ids ∨ b.round < (stateAt cfg tr time v τ).floor := by
  have hcr : b.creator = u :=
    (Local.authored _ _ _ (cfg.at u) _ _ (persists_of_event ha hb)).2
  have hidb : id = cfg.idOf b :=
    (Local.authored _ _ _ (cfg.at u) _ _ (persists_of_event ha hb)).1
  subst hcr
  by_cases hbr : (stateBefore cfg tr j v).floor ≤ b.round
  · have hin := (Converge.persist_stored ha hb haj (Or.inr (hF.trans hbr))).1
    exact synced_held hid hsync hj hv hu hidb hr hu (hidb ▸ hin) hF hτ hτ₁
  · exact hsync j v w id b hj hv hu hidb hr
      (fun x hx => absurd (Needs.le_round hx) hbr) τ hτ hτ₁

/-! ## A steady window -/

section Steady

variable {T : Finset Validator} {time : ℕ → ℕ} {G t₁ L : ℕ}

/-- **In a steady window a node's floor is the floor at its slot**, at a
node that drops. -/
theorem Steady.floor (hdr : cfg.drops = true) (hst : Live.Steady cfg T tr time G t₁ L)
    {v : Validator} (hv : v ∈ T) {k : ℕ} (h₁ : eventsBy tr time G ≤ k)
    (h₂ : k ≤ eventsBy tr time t₁) :
    (stateBefore cfg tr k v).floor = floorAt cfg L := by
  obtain ⟨hlo, -⟩ := hst v hv k h₁ h₂
  rw [floor_eq_before hdr v k, hlo]

/-- **In a steady window every step is regular** (`Regular`). -/
theorem Steady.regular (hdr : cfg.drops = true) (hst : Live.Steady cfg T tr time G t₁ L)
    {v : Validator} (hv : v ∈ T) {k : ℕ} (h₁ : eventsBy tr time G ≤ k)
    (h₂ : k + 1 ≤ eventsBy tr time t₁) :
    Regular (cfg.at v) (stateBefore cfg tr k v) (stateBefore cfg tr (k + 1) v) := by
  intro _
  obtain ⟨hlo, htop⟩ := hst v hv k h₁ (by omega)
  obtain ⟨hlo', -⟩ := hst v hv (k + 1) (by omega) h₂
  have hf := Steady.floor hdr hst hv h₁ (by omega)
  have hf' := Steady.floor hdr hst hv (by omega) h₂
  refine ⟨by rw [hf]; exact htop, ?_, by rw [hlo, hlo'], by rw [hf, hf']⟩
  change floorAt cfg (stateBefore cfg tr k v).lo ≤ _
  rw [hlo, hf]

/-- **In a steady window past GST a reliable author's block is synced**,
once delivered after the window opens, at a node that drops: the floors
meet at the round of the window's slot, at or below the block's round, and
the author holds the block (`synced_from_author`). -/
theorem syncedFrom_steady {H : Finset Validator} (hid : Function.Injective cfg.idOf)
    (hdr : cfg.drops = true) (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H)
    (hmono : Live.TimeMono tr time) {gst Δₛ : ℕ}
    (hsync : Live.SyncedHeld cfg T tr time gst Δₛ t₁) (hst : Live.Steady cfg T tr time G t₁ L)
    (hgG : gst ≤ G) : Live.SyncedFrom cfg T tr time gst Δₛ (G + 1) t₁ := by
  intro j v u id b hj hv hc hidb hr hGj τ hτ hτ₁
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  -- its author built it before
  obtain ⟨i, hij, hiu, hxb⟩ := htime j v (.deliver u id b) hj (hTH hv) (id, b)
    (by simp [delivered, hidb]; rfl) (hTH hc)
  obtain ⟨inpi, hi⟩ := Converge.event_of_map hiu
  obtain ⟨a, hai, inpa, ha, hpa⟩ := Converge.persists_of_broadcasts hi hxb
  -- the window holds at the delivery and at `τ`
  have hEj : eventsBy tr time G ≤ j := by
    by_contra h
    have := (lt_eventsBy (t := G) hmono hjl).mp (by omega)
    omega
  have hjE : j ≤ eventsBy tr time t₁ := ((lt_eventsBy hmono hjl).mpr (by omega)).le
  have hEτ : eventsBy tr time G ≤ eventsBy tr time τ := eventsBy_mono (by omega)
  have hτE : eventsBy tr time τ ≤ eventsBy tr time t₁ := eventsBy_mono hτ₁
  have hF : (stateBefore cfg tr j b.creator).floor ≤ (stateBefore cfg tr j v).floor := by
    rw [Steady.floor hdr hst hc hEj hjE, Steady.floor hdr hst hv hEj hjE]
  have hrg : topAt cfg tr time b.creator gst ≤ b.round :=
    ((rises_before (cfg := cfg) (tr := tr) b.creator
      (eventsBy_mono (tr := tr) (time := time) (le_max_right (G + 1) gst))).1).trans hr
  rcases synced_from_author hid hsync ha hpa (by omega) hj hc hv hrg hF hτ hτ₁ with h | h
  · exact h
  · -- the block lies at the author's round at `G` or above, so at the floor or above
    exfalso
    have hfτ : (stateAt cfg tr time v τ).floor = floorAt cfg L :=
      Steady.floor hdr hst hv hEτ hτE
    have htG := (hst b.creator hc (eventsBy tr time G) le_rfl (eventsBy_mono (by omega))).2
    have hGm : topAt cfg tr time b.creator G ≤ topAt cfg tr time b.creator (max (G + 1) gst) :=
      (rises_before (cfg := cfg) (tr := tr) b.creator
        (eventsBy_mono (tr := tr) (time := time) (by omega))).1
    change floorAt cfg L ≤ topAt cfg tr time b.creator G at htG
    omega

/-- **Reliable blocks arrive in a steady window**, at a node that drops: as
past a recovery (`arrival_of_recovered`), the window's start in the place
of the recovery's, since a block delivered after it is synced
(`syncedFrom_steady`) and every step in it is regular (`Steady.regular`),
so a reliable author sends its blocks again. -/
theorem arrival_steady {H : Finset Validator} (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f)
    (hid : Function.Injective cfg.idOf) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdr : cfg.drops = true) {gst Δ Δₛ : ℕ} (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (hsync : Live.SyncedHeld cfg T tr time gst Δₛ t₁) (hup : Live.UpFrom T tr time 0 t₁)
    (hfire : Live.TimersFireUp cfg T tr time t₁) (hstart : Live.StartedBy T tr time gst)
    (hst : Live.Steady cfg T tr time G t₁ L) (hgG : gst ≤ G)
    (hW : max (G + 1) gst +
      (T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max (G + 1) gst) - 1)) ≤ t₁) :
    Arrival cfg T tr time
      (max (G + 1) gst +
        T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max (G + 1) gst) - 1))
      (Δ + Δₛ) t₁ := by
  refine arrival_of_recovered hσ hadm hfa hf hid htime hinj hTH hmono
    (fun i u inp hi hu _ m hm hmT ht => hdel i u inp hi hu m hm hmT ht)
    (syncedFrom_steady hid hdr htime hTH hmono hsync hst hgG)
    (fun k v hk hv h => absurd (hup k v hk hv h) (Nat.not_lt_zero _)) hfire hstart
    fun u hu k inp hk h₁ h₂ => ?_
  have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
  refine Steady.regular hdr hst hu ?_ ((lt_eventsBy hmono hkl).mpr (by omega))
  by_contra h
  have := (lt_eventsBy (t := G) hmono hkl).mp (by omega)
  omega

omit [Fintype Validator] in
/-- A store valid at the row from `F` up is so from any higher round. -/
theorem UpperValid.mono {q : ℕ} {E : Exposure Validator BlockId Payload} {F F' : ℕ}
    {st : Store Validator BlockId Payload} (h : UpperValid q E F st) (hF : F ≤ F') :
    UpperValid q E F' st :=
  fun j hj hr => h j hj (hF.trans hr)

/-- **While no honest next undecided slot passes `L`, the record padded below
the round under the floor at slot `L` is a base from that round on**, given
the window's growth, floors and regular steps from `E₀`, at a node that
drops: it takes in what the honest nodes knew (`grounds_padded`), and a
known block at or below that round (`cutAbove_known`); every honest disk is
read as it from there up (`cutAbove_before`). -/
theorem base_below {H : Finset Validator} [Infinite BlockId] (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hq : cfg.q ≤ Fintype.card Validator)
    (hdr : cfg.drops = true) {E₀ E₁ : ℕ}
    (hle : ∀ v ∈ H, ∀ k, k ≤ E₁ → (stateBefore cfg tr k v).lo ≤ L)
    (hwin : ∀ v ∈ H, ∀ k, E₀ ≤ k → k ≤ E₁ →
      (∀ k', k ≤ k' → k' ≤ E₁ →
          Grows (stateBefore cfg tr k v).disk (stateBefore cfg tr k' v).disk) ∧
        (stateBefore cfg tr k v).floor ≤ (stateBefore cfg tr k v).top.getD 0 ∧
        (k + 1 ≤ E₁ →
          Regular (cfg.at v) (stateBefore cfg tr k v) (stateBefore cfg tr (k + 1) v))) :
    Base cfg H tr
      (padded (hashInjective_of_trace hinj) (authentic_of_timely htime) hq
        (floorAt cfg L - 1))
      (floorAt cfg L - 1) E₀ E₁ := by
  refine ⟨fun v _ => grounds_padded (hashInjective_of_trace hinj) (authentic_of_timely htime) hq
      (floorAt cfg L - 1) v,
    fun _ x hx hle => cutAbove_known (hashInjective_of_trace hinj) (authentic_of_timely htime) hq
      hx hle, fun c hc hcr => ?_, fun v hv k h₂ => ?_, hwin⟩
  · -- a block of the padded record above its padding is a known one
    rcases mem_paddedIds.mp hc with hc | ⟨x, hx, rfl⟩
    · obtain ⟨hck, -, -⟩ := mem_globalCutIds.mp hc
      obtain ⟨y, hy, rfl⟩ := exists_of_mem_knownIds hck
      have hcont := content_of_known (hashInjective_of_trace hinj) hy
      change (y.1, padBlk cfg H tr _ y.1) ∈ _
      change floorAt cfg L - 1 < (padBlk cfg H tr _ y.1).round at hcr
      rw [padBlk_known hck] at hcr ⊢
      rw [if_neg (by rw [hcont]; split_ifs at hcr with h <;> simp_all <;> omega), hcont]
      exact hy
    · exfalso
      have := round_fresh_lt (cfg := cfg) (H := H) (tr := tr) (G := floorAt cfg L - 1) hx
      change floorAt cfg L - 1 < (padBlk cfg H tr _ (fresh cfg H tr x)).round at hcr
      omega
  · have hsl := floorAt_mono (cfg := cfg) (hle v hv k h₂)
    have hF : (stateBefore cfg tr k v).floor ≤ floorAt cfg (stateBefore cfg tr k v).lo := by
      have := (Converge.inv_before (cfg := cfg) (tr := tr) k v).floor
      unfold floorOf at this; rw [if_pos (show (cfg.at v).drops = true from hdr)] at this
      exact this
    exact ⟨(cutAbove_before (hashInjective_of_trace hinj) (authentic_of_timely htime) hq hσ hadm
        hf (floorAt cfg L - 1) k v hv).1 (by omega),
      ((Converge.inv_before (cfg := cfg) (tr := tr) k v).above).mono (by omega),
      fun _ => by omega⟩

/-- **In a steady window of the honest nodes, the record padded below the
round under the floor at slot `L` is a base from that round on** (`base_below`),
at a node that drops: in the window its floor is the floor at slot `L`
(`Steady.floor`), at or below its top, it grows while its next undecided
slot stays (`Converge.grows_of_lo`), and its steps are regular
(`Steady.regular`). -/
theorem base_steady {H : Finset Validator} [Infinite BlockId] (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hq : cfg.q ≤ Fintype.card Validator)
    (hdr : cfg.drops = true) (hst : Live.Steady cfg H tr time G t₁ L) (hGt : G ≤ t₁) :
    Base cfg H tr
      (padded (hashInjective_of_trace hinj) (authentic_of_timely htime) hq
        (floorAt cfg L - 1))
      (floorAt cfg L - 1) (eventsBy tr time G) (eventsBy tr time t₁) := by
  refine base_below hσ hadm hf htime hinj hq hdr (fun v hv k h₂ => ?_)
    fun v hv k h₁ h₂ => ?_
  · -- up to the window's end the next undecided slot is at most `L`
    rw [← (hst v hv (eventsBy tr time t₁) (eventsBy_mono hGt) le_rfl).1]
    exact (rises_before (cfg := cfg) (tr := tr) v h₂).2.2
  · obtain ⟨hlo, -⟩ := hst v hv k h₁ h₂
    have hfl := Steady.floor hdr hst hv h₁ h₂
    exact ⟨fun k' hk hk' => Converge.grows_of_lo v hk
        (by rw [(hst v hv k' (by omega) hk').1, hlo]),
      by rw [hfl]; exact (hst v hv k h₁ h₂).2, fun hk => Steady.regular hdr hst hv h₁ hk⟩

end Steady

end Node

end LeanDag
