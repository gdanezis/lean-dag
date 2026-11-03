import LeanDag.Node.Helpers.CatchUp
/-!
# Syncing with dropping on

`docs/dos-bounds.md` Phase 3.2 item 4.3. A node's disk holds the
references of its blocks from its floor up (`Inv.above`), so a node that
holds a block holds what a node with a floor at or above its own needs to
accept it (`needs_held`). Under `SyncedHeld`, a reliable node given a
reliable author's block that a reliable node with a floor at or below its
own holds then holds it within `Δₛ` past GST, or its floor lies above it
(`synced_held`). A node that drops has its floor at the round of its next
undecided slot once it decided a slot (`floor_eq_before`), so a node that
decided as far as another has a floor at or above the other's
(`floor_le_floor`); and it keeps its own blocks from its floor up
(`Converge.persist_stored`), so a reliable node syncs a reliable author's
block when its floor is at or above the author's (`synced_from_author`).
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

/-- **A node that drops has its floor at the round of its next undecided
slot** once it decided a slot. -/
theorem floor_eq_before (hdr : cfg.drops = true) (v : Validator) (i : ℕ)
    (hlo : 0 < (stateBefore cfg tr i v).lo) :
    (stateBefore cfg tr i v).floor = cfg.slots.slotRound (stateBefore cfg tr i v).lo := by
  have hdr' : (cfg.at v).drops = true := hdr
  refine le_antisymm ?_ ?_
  · have h := (Converge.inv_before (cfg := cfg) (tr := tr) i v).floor
    unfold floorOf at h
    rw [if_pos hdr'] at h
    exact h
  · rcases (Converge.diskRises_before (cfg := cfg) (tr := tr) v (Nat.zero_le i)).1.2 hdr' with
      h | h
    · rw [stateBefore_zero] at h
      simp [State.init] at h
      omega
    · exact h

/-- **A node that drops and decided as far as another has a floor at or
above the other's.** -/
theorem floor_le_floor (hdr : cfg.drops = true) (u v : Validator) (i : ℕ)
    (hv : 0 < (stateBefore cfg tr i v).lo)
    (h : (stateBefore cfg tr i u).lo ≤ (stateBefore cfg tr i v).lo) :
    (stateBefore cfg tr i u).floor ≤ (stateBefore cfg tr i v).floor := by
  have hdr' : (cfg.at u).drops = true := hdr
  have hu := (Converge.inv_before (cfg := cfg) (tr := tr) i u).floor
  unfold floorOf at hu
  rw [if_pos hdr'] at hu
  rw [floor_eq_before hdr v i hv]
  exact hu.trans (cfg.slots.mono h)

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

end Node

end LeanDag
