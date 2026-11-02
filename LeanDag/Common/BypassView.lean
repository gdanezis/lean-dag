import LeanDag.Common.BypassLedger
import LeanDag.Common.Record.Chop
/-!
# What a node holds under bypass

`docs/sync-auth.md` §8. A *bypass view* (`BypassView`) is the set of
blocks a node holds when it applies the rule of §8 with the ordered set
`C` and the horizon `H`: it holds `C`, and every reference of a block it
holds is held, or lies at a round `r` with `r + 1 < H` and is bypassed in
`C`. Unlike a view, it need not hold the history of its blocks.

* **The cut is a view** (`BypassView.chop`): at or above a round `G` with
  `H ≤ G + 1`, a bypass view is a view of the record cut at `G`, since no
  reference at round `G` or above is bypassed. The decisions of a rule
  read on the cut are those of `LeanDag/GC`.
* **A commit reads only what the node holds** (`flushOn_eq`): the blocks a
  commit orders, computed from a block map that agrees with the record on
  the held blocks and is arbitrary elsewhere (`flushOn`), are the blocks
  of `flush`.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **A bypass view**: blocks held, the ordered set `C` among them, every
reference of a held block held or, below the horizon `H`, bypassed in `C`. -/
structure BypassView (U : BlockRecord Validator BlockId Payload P honest) (q H : ℕ)
    (C : Finset BlockId) where
  /-- The ids the node holds. -/
  ids : Finset BlockId
  /-- The node holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- The node holds the ordered blocks. -/
  ordered : C ⊆ ids
  /-- A reference of a held block is held, or bypassed below the horizon. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs,
    j ∈ ids ∨ ((U.block j).round + 1 < H ∧ Bypassed U C q j)

variable {U : BlockRecord Validator BlockId Payload P honest}

/-- A view holding `C` is a bypass view. -/
def BlockRecord.View.toBypassView (V : U.View) {q H : ℕ} {C : Finset BlockId}
    (hC : C ⊆ V.ids) : BypassView U q H C where
  ids := V.ids
  subset_ids := V.subset_ids
  ordered := hC
  complete := fun i hi j hj => Or.inl (V.complete i hi j hj)

namespace BypassView

variable [P.Mechanised] {q H : ℕ} {C : Finset BlockId}

/-- **The cut is a view**: at or above `G`, with `H ≤ G + 1`, a bypass
view is a view of the record cut at `G`. -/
def chop (W : BypassView U q H C) (G : ℕ) (hG : H ≤ G + 1) : (U.chop G).View where
  ids := W.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := Finset.filter_subset_filter _ W.subset_ids
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    change j ∈ (chopBlk U.block G i).refs at hj
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hj
      have hjr := BlockRecord.round_of_mem_refs (W.subset_ids hi.1) hj
      rcases W.complete i hi.1 j hj with hjW | ⟨hlt, -⟩
      · exact Finset.mem_filter.mpr ⟨hjW, by omega⟩
      · omega
    · rw [chopBlk_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)

theorem chop_ids (W : BypassView U q H C) {G : ℕ} (hG : H ≤ G + 1) :
    (W.chop G hG).ids = W.ids.filter fun i => G ≤ (U.block i).round := rfl

end BypassView

/-! ## A commit, from the blocks held -/

/-- The authors of the blocks of `V` at round `r + 1` that do not reference
`x`, read from the block map `blk`. -/
def bypassersOn (blk : BlockId → Block Validator BlockId Payload) (V : Finset BlockId)
    (x : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf blk (V.filter fun y => (blk y).round = r + 1 ∧ x ∉ (blk y).refs)

/-- `layer`, read from the block map `blk`: the round of a block `d + 1`
rounds below `L` is read off `L`. -/
def layerOn (blk : BlockId → Block Validator BlockId Payload) (q H : ℕ)
    (C : Finset BlockId) (L : BlockId) : ℕ → Finset BlockId
  | 0 => if L ∈ C then ∅ else {L}
  | d + 1 => ((layerOn blk q H C L d).biUnion fun y => (blk y).refs).filter fun x =>
      x ∉ C ∧ ¬ ((blk L).round - (d + 1) + 1 < H ∧
        q ≤ (bypassersOn blk (C ∪ layerOn blk q H C L d) x ((blk L).round - (d + 1))).card)

/-- `flush`, read from the block map `blk`. -/
def flushOn (blk : BlockId → Block Validator BlockId Payload) (q H : ℕ)
    (C : Finset BlockId) (L : BlockId) : Finset BlockId :=
  (Finset.range ((blk L).round + 1)).biUnion (layerOn blk q H C L)

/-- Over held blocks, the bypassers read from a block map that agrees with
the record are the record's. -/
theorem bypassersOn_eq {blk : BlockId → Block Validator BlockId Payload}
    {V : Finset BlockId} (hV : V ⊆ U.ids) (hblk : ∀ i ∈ V, blk i = U.block i)
    (x : BlockId) (r : ℕ) :
    bypassersOn blk V x r = bypassers U V x (r + 1) := by
  ext v
  simp only [bypassersOn, mem_creatorsOf, Finset.mem_filter, mem_bypassers]
  constructor
  · rintro ⟨y, ⟨hyV, hyr, hxy⟩, hyc⟩
    rw [hblk y hyV] at hyr hxy hyc
    exact ⟨y, hyV, hV hyV, hyr, hxy, hyc⟩
  · rintro ⟨y, hyV, -, hyr, hxy, hyc⟩
    exact ⟨y, ⟨hyV, by rw [hblk y hyV]; exact hyr, by rw [hblk y hyV]; exact hxy⟩,
      by rw [hblk y hyV]; exact hyc⟩

variable [P.Mechanised] {q H : ℕ} {C : Finset BlockId}

/-- Each layer read from the block map is the record's, and is held. -/
theorem layerOn_eq (W : BypassView U q H C) {blk : BlockId → Block Validator BlockId Payload}
    (hblk : ∀ i ∈ W.ids, blk i = U.block i) {L : BlockId} (hL : L ∈ W.ids) :
    ∀ d, layerOn blk q H C L d = layer U q H C L d ∧ layer U q H C L d ⊆ W.ids
  | 0 => by
    refine ⟨by simp only [layerOn, layer], ?_⟩
    unfold layer
    split_ifs
    · exact Finset.empty_subset _
    · exact Finset.singleton_subset_iff.mpr hL
  | d + 1 => by
    obtain ⟨heq, hsub⟩ := layerOn_eq W hblk hL d
    have hLU := W.subset_ids hL
    have hV : C ∪ layer U q H C L d ⊆ W.ids := Finset.union_subset W.ordered hsub
    have hbyp : ∀ x, ∀ y ∈ layer U q H C L d, x ∈ (U.block y).refs →
        ((blk L).round - (d + 1) + 1 < H ∧
          q ≤ (bypassersOn blk (C ∪ layer U q H C L d) x ((blk L).round - (d + 1))).card ↔
        (U.block x).round + 1 < H ∧ Bypassed U (C ∪ layer U q H C L d) q x) := by
      intro x y hy hxy
      obtain ⟨hyU, hyr⟩ := round_of_mem_layer hLU d y hy
      have hxr := BlockRecord.round_of_mem_refs hyU hxy
      have hr : (blk L).round - (d + 1) = (U.block x).round := by
        rw [hblk L hL]; omega
      rw [hr, bypassersOn_eq (hV.trans W.subset_ids) (fun i hi => hblk i (hV hi))]
      rfl
    have hlayer : layerOn blk q H C L (d + 1) = layer U q H C L (d + 1) := by
      ext x
      simp only [layerOn, heq, Finset.mem_filter, Finset.mem_biUnion]
      rw [mem_layer_succ]
      constructor
      · rintro ⟨⟨y, hy, hxy⟩, hxC, hb⟩
        rw [hblk y (hsub hy)] at hxy
        exact ⟨⟨y, hy, hxy⟩, hxC, fun h => hb ((hbyp x y hy hxy).mpr h)⟩
      · rintro ⟨⟨y, hy, hxy⟩, hxC, hb⟩
        exact ⟨⟨y, hy, by rw [hblk y (hsub hy)]; exact hxy⟩, hxC,
          fun h => hb ((hbyp x y hy hxy).mp h)⟩
    refine ⟨hlayer, fun x hx => ?_⟩
    obtain ⟨⟨y, hy, hxy⟩, -, hb⟩ := mem_layer_succ.mp hx
    rcases W.complete y (hsub hy) x hxy with hxW | ⟨hlt, hbC⟩
    · exact hxW
    · exact absurd ⟨hlt, hbC.mono Finset.subset_union_left⟩ hb

/-- **A commit reads only what the node holds**: computed from a block map
that agrees with the record on the held blocks, a commit of a held leader
orders the blocks of `flush`. -/
theorem flushOn_eq (W : BypassView U q H C) {blk : BlockId → Block Validator BlockId Payload}
    (hblk : ∀ i ∈ W.ids, blk i = U.block i) {L : BlockId} (hL : L ∈ W.ids) :
    flushOn blk q H C L = flush U q H C L := by
  simp only [flushOn, flush, hblk L hL]
  exact Finset.biUnion_congr rfl fun d _ => (layerOn_eq W hblk hL d).1

/-- The blocks a commit of a held leader orders are held. -/
theorem flush_subset (W : BypassView U q H C) {L : BlockId} (hL : L ∈ W.ids) :
    flush U q H C L ⊆ W.ids := fun _ hx =>
  let ⟨d, _, hd⟩ := mem_flush.mp hx
  (layerOn_eq W (blk := U.block) (fun _ _ => rfl) hL d).2 hd

end LeanDag
