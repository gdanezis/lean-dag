import LeanDag.Node.Helpers.CatchUp
/-!
# Syncing with dropping on

`docs/dos-bounds.md` Phase 3.2 item 4.3. A node's disk holds the
references of its blocks from its floor up (`Inv.above`), so a node that
holds a block holds what a node with a floor at or above its own needs to
accept it (`needs_held`). Under `SyncedHeld`, a reliable node given a
reliable author's block that a reliable node with a floor at or below its
own holds then holds it within `Δₛ` past GST, or its floor lies above it
(`synced_held`).
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

end Node

end LeanDag
