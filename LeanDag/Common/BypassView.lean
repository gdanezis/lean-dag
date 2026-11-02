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
* **A commit reads only the blocks it is given** (`flushOn_eq_of`): a commit
  computed from a block map that agrees with the record on a set holding the
  ordered blocks and the leader, and that reads only blocks of that set,
  orders the blocks of `flush`.
* **A node under bypass** (`BypassRun`): from holding nothing, a node
  accepts blocks whose references it follows only up to bypassed blocks,
  may drop blocks that are bypassed and not ordered, and decides the slots
  in order, on the blocks it holds or on a proof it receives; a commit
  orders, from the blocks it holds, the leader's history, and a commit
  decided on a proof takes in the blocks it orders with it (`absorb`). In
  every state it reaches, what it holds is a bypass view of its ordered set
  at the horizon of its next slot, and what it has ordered is the ledger of
  its verdicts (`BypassRun.inv`).
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

omit [P.Mechanised] in
/-- **Accepting blocks**: blocks whose references are held, accepted with
them, or bypassed below the horizon keep a bypass view. -/
def extend (W : BypassView U q H C) (N : Finset BlockId) (hN : N ⊆ U.ids)
    (hcl : ∀ i ∈ N, ∀ j ∈ (U.block i).refs,
      j ∈ W.ids ∪ N ∨ ((U.block j).round + 1 < H ∧ Bypassed U C q j)) :
    BypassView U q H C where
  ids := W.ids ∪ N
  subset_ids := Finset.union_subset W.subset_ids hN
  ordered := W.ordered.trans Finset.subset_union_left
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (W.complete i hi j hj).imp (Finset.mem_union_left _) id
    · exact hcl i hi j hj

omit [P.Mechanised] in
/-- **Bypass persists**: under a higher horizon and a larger ordered set,
still held, a bypass view is one still. -/
def raise (W : BypassView U q H C) {H' : ℕ} {C' : Finset BlockId} (hH : H ≤ H')
    (hC : C ⊆ C') (hC' : C' ⊆ W.ids) : BypassView U q H' C' where
  ids := W.ids
  subset_ids := W.subset_ids
  ordered := hC'
  complete := fun i hi j hj =>
    (W.complete i hi j hj).imp id fun h => ⟨by omega, h.2.mono hC⟩

omit [P.Mechanised] in
/-- **Dropping bypassed blocks**: without blocks that are not ordered and
are bypassed below the horizon, a bypass view is one still. -/
def drop (W : BypassView U q H C) (X : Finset BlockId)
    (hX : ∀ x ∈ X, x ∉ C ∧ (U.block x).round + 1 < H ∧ Bypassed U C q x) :
    BypassView U q H C where
  ids := W.ids \ X
  subset_ids := Finset.sdiff_subset.trans W.subset_ids
  ordered := fun x hx => Finset.mem_sdiff.mpr ⟨W.ordered hx, fun h => (hX x h).1 hx⟩
  complete := by
    intro i hi j hj
    by_cases hjX : j ∈ X
    · exact Or.inr (hX j hjX).2
    · exact (W.complete i (Finset.mem_sdiff.mp hi).1 j hj).imp
        (fun h => Finset.mem_sdiff.mpr ⟨h, hjX⟩) id

omit [P.Mechanised] in
/-- **Taking blocks in with a commit**: with the horizon and the ordered set
raised, blocks whose references are held, taken in with them, or bypassed under
the new horizon and ordered set join a bypass view. -/
def absorb (W : BypassView U q H C) (N : Finset BlockId) (hN : N ⊆ U.ids) {H' : ℕ}
    {C' : Finset BlockId} (hH : H ≤ H') (hC : C ⊆ C') (hC' : C' ⊆ W.ids ∪ N)
    (hcl : ∀ i ∈ N, ∀ j ∈ (U.block i).refs,
      j ∈ W.ids ∪ N ∨ ((U.block j).round + 1 < H' ∧ Bypassed U C' q j)) :
    BypassView U q H' C' where
  ids := W.ids ∪ N
  subset_ids := Finset.union_subset W.subset_ids hN
  ordered := hC'
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (W.complete i hi j hj).imp (Finset.mem_union_left _)
        fun h => ⟨by omega, h.2.mono hC⟩
    · exact hcl i hi j hj

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

/-- **A commit reads only the blocks it is given**: computed from a block map
that agrees with the record on a set `A` holding the ordered blocks and the
leader, a commit that reads only blocks of `A` orders the blocks of `flush`. -/
theorem flushOn_eq_of {A : Finset BlockId} (hA : A ⊆ U.ids) (hCA : C ⊆ A)
    {blk : BlockId → Block Validator BlockId Payload} (hblk : ∀ i ∈ A, blk i = U.block i)
    {L : BlockId} (hL : L ∈ A) (hsub : flushOn blk q H C L ⊆ A) :
    flushOn blk q H C L = flush U q H C L := by
  have hLU := hA hL
  have hon : ∀ d, d ≤ (U.block L).round → layerOn blk q H C L d ⊆ A := fun d hd x hx =>
    hsub (Finset.mem_biUnion.mpr ⟨d, Finset.mem_range.mpr (by rw [hblk L hL]; omega), hx⟩)
  have key : ∀ d, d ≤ (U.block L).round → layerOn blk q H C L d = layer U q H C L d := by
    intro d
    induction d with
    | zero => intro _; simp only [layerOn, layer]
    | succ d ih =>
      intro hd
      have heq := ih (by omega)
      have hsubd : layer U q H C L d ⊆ A := heq ▸ hon d (by omega)
      have hV : C ∪ layer U q H C L d ⊆ A := Finset.union_subset hCA hsubd
      ext x
      simp only [layerOn, heq, Finset.mem_filter, Finset.mem_biUnion]
      rw [mem_layer_succ]
      have hbyp : ∀ y ∈ layer U q H C L d, x ∈ (U.block y).refs →
          ((blk L).round - (d + 1) + 1 < H ∧
            q ≤ (bypassersOn blk (C ∪ layer U q H C L d) x ((blk L).round - (d + 1))).card ↔
          (U.block x).round + 1 < H ∧ Bypassed U (C ∪ layer U q H C L d) q x) := by
        intro y hy hxy
        obtain ⟨hyU, hyr⟩ := round_of_mem_layer hLU d y hy
        have hxr := BlockRecord.round_of_mem_refs hyU hxy
        have hr : (blk L).round - (d + 1) = (U.block x).round := by
          rw [hblk L hL]; omega
        rw [hr, bypassersOn_eq (hV.trans hA) (fun i hi => hblk i (hV hi))]
        rfl
      constructor
      · rintro ⟨⟨y, hy, hxy⟩, hxC, hb⟩
        rw [hblk y (hsubd hy)] at hxy
        exact ⟨⟨y, hy, hxy⟩, hxC, fun h => hb ((hbyp y hy hxy).mpr h)⟩
      · rintro ⟨⟨y, hy, hxy⟩, hxC, hb⟩
        exact ⟨⟨y, hy, by rw [hblk y (hsubd hy)]; exact hxy⟩, hxC,
          fun h => hb ((hbyp y hy hxy).mp h)⟩
  simp only [flushOn, flush, hblk L hL]
  exact Finset.biUnion_congr rfl fun d hd => key d (by simp at hd; omega)

/-- `bypassLedger`, read from the block map `blk`. -/
def ledgerOn [S : Slots Validator] (blk : BlockId → Block Validator BlockId Payload) (q : ℕ)
    (g : ℕ → Option BlockId) : ℕ → Finset BlockId
  | 0 => ∅
  | n + 1 =>
    match g n with
    | none => ledgerOn blk q g n
    | some L => ledgerOn blk q g n ∪ flushOn blk q (S.slotRound n) (ledgerOn blk q g n) L

/-- **The ledger read from a view is the record's**, and held, when every
committed leader is in the view and the block map agrees with the record on it. -/
theorem ledgerOn_eq [S : Slots Validator] (V : U.View)
    {blk : BlockId → Block Validator BlockId Payload} (hblk : ∀ i ∈ V.ids, blk i = U.block i)
    {g : ℕ → Option BlockId} :
    ∀ n, (∀ k < n, ∀ L, g k = some L → L ∈ V.ids) →
      ledgerOn blk q g n = bypassLedger U q g n ∧ bypassLedger U q g n ⊆ V.ids
  | 0, _ => ⟨rfl, Finset.empty_subset _⟩
  | n + 1, hg => by
    obtain ⟨ih, hsub⟩ := ledgerOn_eq V hblk n fun k hk => hg k (by omega)
    cases hgn : g n with
    | none => simp only [ledgerOn, bypassLedger, hgn, ih]; exact ⟨trivial, hsub⟩
    | some L =>
      have hL := hg n (by omega) L hgn
      let W : BypassView U q (S.slotRound n) (bypassLedger U q g n) := V.toBypassView hsub
      have hf := flushOn_eq W hblk hL
      simp only [ledgerOn, bypassLedger, hgn, ih, hf]
      exact ⟨trivial, Finset.union_subset hsub (flush_subset W hL)⟩

/-! ## A node under bypass -/

/-- **A node under bypass**, with the decision `Dec` read on the blocks it
holds or on a proof it receives: it holds `held`, has decided the slots below
`n` with the verdicts `g`, and has ordered `led`. It accepts blocks whose
references are held, accepted with them, or bypassed below the horizon
`slotRound n` in `led`, and may drop blocks that are not ordered and are
bypassed there. A commit orders the leader's history, read from a block map
that agrees with the record on the held blocks; a commit decided on a proof
takes in the blocks it orders with it (`absorb`), whose references may be
bypassed by the commit itself. -/
inductive BypassRun [S : Slots Validator] (U : BlockRecord Validator BlockId Payload P honest)
    (q : ℕ) (Dec : Finset BlockId → ℕ → Option BlockId → Prop) (g : ℕ → Option BlockId) :
    Finset BlockId → ℕ → Finset BlockId → Prop
  | init : BypassRun U q Dec g ∅ 0 ∅
  | accept {held : Finset BlockId} {n : ℕ} {led : Finset BlockId} (N : Finset BlockId) :
      BypassRun U q Dec g held n led → N ⊆ U.ids →
      (∀ i ∈ N, ∀ j ∈ (U.block i).refs, j ∈ held ∪ N ∨
        ((U.block j).round + 1 < S.slotRound n ∧ Bypassed U led q j)) →
      BypassRun U q Dec g (held ∪ N) n led
  | drop {held : Finset BlockId} {n : ℕ} {led : Finset BlockId} (X : Finset BlockId) :
      BypassRun U q Dec g held n led →
      (∀ x ∈ X, x ∉ led ∧ (U.block x).round + 1 < S.slotRound n ∧ Bypassed U led q x) →
      BypassRun U q Dec g (held \ X) n led
  | skip {held : Finset BlockId} {n : ℕ} {led : Finset BlockId} (D : Finset BlockId) :
      BypassRun U q Dec g held n led → g n = none → Dec D n none →
      BypassRun U q Dec g held (n + 1) led
  | commit {held : Finset BlockId} {n : ℕ} {led : Finset BlockId} {L : BlockId}
      (blk : BlockId → Block Validator BlockId Payload) :
      BypassRun U q Dec g held n led → g n = some L → Dec held n (some L) → L ∈ held →
      (∀ i ∈ held, blk i = U.block i) →
      BypassRun U q Dec g held (n + 1) (led ∪ flushOn blk q (S.slotRound n) led L)
  | absorb {held : Finset BlockId} {n : ℕ} {led : Finset BlockId} {L : BlockId}
      (N D : Finset BlockId) (blk : BlockId → Block Validator BlockId Payload) :
      BypassRun U q Dec g held n led → g n = some L → Dec D n (some L) → N ⊆ U.ids →
      L ∈ held ∪ N → (∀ i ∈ held ∪ N, blk i = U.block i) →
      flushOn blk q (S.slotRound n) led L ⊆ held ∪ N →
      (∀ i ∈ N, ∀ j ∈ (U.block i).refs, j ∈ held ∪ N ∨
        ((U.block j).round + 1 < S.slotRound (n + 1) ∧
          Bypassed U (led ∪ flushOn blk q (S.slotRound n) led L) q j)) →
      BypassRun U q Dec g (held ∪ N) (n + 1) (led ∪ flushOn blk q (S.slotRound n) led L)

namespace BypassRun

variable [S : Slots Validator] {Dec : Finset BlockId → ℕ → Option BlockId → Prop}
variable {g : ℕ → Option BlockId} {held led : Finset BlockId} {n : ℕ}

/-- **The invariant of a node under bypass**: what it has ordered is the
ledger of its verdicts, and what it holds is a bypass view of it at the
horizon `slotRound n`. -/
theorem inv (h : BypassRun U q Dec g held n led) :
    led = bypassLedger U q g n ∧ ∃ W : BypassView U q (S.slotRound n) led, W.ids = held := by
  induction h with
  | init => exact ⟨rfl, ⟨⟨∅, Finset.empty_subset _, subset_rfl, by simp⟩, rfl⟩⟩
  | accept N _ hN hcl ih =>
    obtain ⟨hled, W, rfl⟩ := ih
    exact ⟨hled, W.extend N hN hcl, rfl⟩
  | drop X _ hX ih =>
    obtain ⟨hled, W, rfl⟩ := ih
    exact ⟨hled, W.drop X hX, rfl⟩
  | @skip held n led _ _ hg _ ih =>
    obtain ⟨hled, W, rfl⟩ := ih
    refine ⟨by simp only [bypassLedger, hg, hled], W.raise (S.mono (Nat.le_succ n)) subset_rfl
      W.ordered, rfl⟩
  | @commit held n led L blk _ hg _ hL hblk ih =>
    obtain ⟨hled, W, rfl⟩ := ih
    rw [flushOn_eq W hblk hL]
    refine ⟨by simp only [bypassLedger, hg, hled], ?_⟩
    exact ⟨W.raise (S.mono (Nat.le_succ n)) Finset.subset_union_left
      (Finset.union_subset W.ordered (flush_subset W hL)), rfl⟩
  | @absorb held n led L N D blk _ hg _ hN hL hblk hsub hcl ih =>
    obtain ⟨hled, W, rfl⟩ := ih
    have hA : W.ids ∪ N ⊆ U.ids := Finset.union_subset W.subset_ids hN
    have hf := flushOn_eq_of hA (W.ordered.trans Finset.subset_union_left) hblk hL hsub
    refine ⟨by rw [hf]; simp only [bypassLedger, hg, hled], ?_⟩
    exact ⟨W.absorb N hN (S.mono (Nat.le_succ n)) Finset.subset_union_left
      (Finset.union_subset (W.ordered.trans Finset.subset_union_left) hsub) hcl, rfl⟩

omit [P.Mechanised] in
/-- **The decisions of a run**: every slot below `n` was decided on the
blocks held at the time. -/
theorem decided (h : BypassRun U q Dec g held n led) :
    ∀ k, k < n → ∃ held', Dec held' k (g k) := by
  induction h with
  | init => intro k hk; omega
  | accept _ _ _ _ ih => exact ih
  | drop _ _ _ ih => exact ih
  | @skip held n led D _ hg hd ih =>
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih k hk
    · exact ⟨D, hg ▸ hd⟩
  | @commit held n led L blk _ hg hd _ _ ih =>
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih k hk
    · exact ⟨held, hg ▸ hd⟩
  | @absorb held n led L N D blk _ hg hd _ _ _ _ _ ih =>
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih k hk
    · exact ⟨D, hg ▸ hd⟩

end BypassRun

end LeanDag
