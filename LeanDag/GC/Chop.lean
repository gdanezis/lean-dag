import LeanDag.Common.Slots
import LeanDag.Network.Delivery
import LeanDag.Common.Record.Chop
import LeanDag.DoS.Exposure
/-!
# The horizon: truncation as rebasing

**A universe transform** (`Transforms`): `chop` rebases the DAG above
a horizon. The arc gives the operator and its lemmas; the witness that
the cut stands in `Properties.Truncates`, and the verdicts that cross
it, are the protocol's — `Mysticeti/Record.lean` for the core.

`garbage.md` §2, §4 — **G1** (truncation is a universe, with the
one-way `DoSValid` transfer) and **G2** (verdict invariance). `chop U G`
keeps blocks of round `≥ G`, rebases by `−G`, and empties the new base
layer's references, so every validity clause and rule reading rounds
above the base layer carries over unchanged. The `DoSValid` transfer is
one-way by design: exposure shrinks under truncation, so an
equivocation whose witnessing pair falls below the cut is forgiven.
-/

namespace LeanDag

/-! The block-level operator `chopBlk` is `BlockRecord.lean`'s. -/

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ} {b i j : BlockId}

/-! ## The core's universe -/

/-! **The cut** is the block record's (`Record/Chop.lean`); `chop`,
`mem_chop_ids` and `chop_block` are its names, read here at the core. -/
export BlockRecord (chop mem_chop_ids chop_block)

/-! ## Transfer lemmas: rounds, layers, reachability, cones -/

/-- A step in the truncation is a step in the original. -/
theorem reaches_of_reaches_chop (h : Reaches (chop U G) b i) :
    Reaches U b i := by
  induction h with
  | refl => exact Reaches.refl
  | tail _ hstep ih =>
      exact ih.trans (Reaches.single (chopBlk_refs_subset hstep))

/-- A path of the original whose endpoint stays at or above the cut never
dips below it, so it survives truncation whole. -/
theorem reaches_chop_of_reaches (hb : b ∈ U.ids) (h : Reaches U b i)
    (hi : G ≤ (U.block i).round) : Reaches (chop U G) b i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Reaches.refl
  | head hstep hrest ih =>
      rename_i x y
      have hy_ids : y ∈ U.ids := U.complete x hb y hstep
      have hy_round := U.round_of_mem_refs hb hstep
      have hi_le := round_le_of_reaches hy_ids hrest
      refine Relation.ReflTransGen.head ?_ (ih hy_ids)
      show y ∈ (chopBlk U.block G x).refs
      rw [chopBlk_refs_of_lt (by omega)]
      exact hstep

theorem reaches_chop_iff (hb : b ∈ (chop U G).ids) :
    Reaches (chop U G) b i ↔ Reaches U b i ∧ G ≤ (U.block i).round := by
  rw [mem_chop_ids] at hb
  constructor
  · intro h
    have hi_ids := mem_ids_of_reaches (mem_chop_ids.mpr hb) h
    rw [mem_chop_ids] at hi_ids
    exact ⟨reaches_of_reaches_chop h, hi_ids.2⟩
  · rintro ⟨h, hi⟩
    exact reaches_chop_of_reaches hb.1 h hi

/-- **The cone above the cut**: truncation intersects every cone with the
window. This is the lemma the windowed budget (`garbage.md` G13) and the
statute of limitations both run on. -/
theorem history_chop (hb : b ∈ (chop U G).ids) :
    history (chop U G) b =
      (history U b).filter fun i => G ≤ (U.block i).round := by
  have hbU : b ∈ U.ids := (mem_chop_ids.mp hb).1
  ext i
  rw [mem_history_iff hb, reaches_chop_iff hb, Finset.mem_filter,
    mem_history_iff hbU]

/-! ## The statute of limitations, and its one-way door -/

/-- Exposure in the truncation is exposure in the original: the witnessing
pair survives un-rebasing. -/
theorem exposedIn_of_exposedIn_chop {X : Validator}
    (hb : b ∈ (chop U G).ids) (h : ExposedIn (chop U G) b X) :
    ExposedIn U b X := by
  obtain ⟨x, hx, y, hy, hpair⟩ := h
  rw [history_chop hb, Finset.mem_filter] at hx hy
  have hbU := (mem_chop_ids.mp hb).1
  refine ⟨x, hx.1, y, hy.1, ?_⟩
  obtain ⟨hne, hxc, hyc, hround⟩ := hpair
  refine ⟨hne, ?_, ?_, ?_⟩
  · rw [← chopBlk_creator (blk := U.block) (G := G)]; exact hxc
  · rw [← chopBlk_creator (blk := U.block) (G := G)]; exact hyc
  · have hxG := hx.2
    have hyG := hy.2
    have hr := hround
    rw [chop_block, chopBlk_round, chopBlk_round] at hr
    omega

/-- **G1, DoS half — the one-way door.** The condition survives
truncation; the converse fails by design (the statute of limitations,
witnessed in `LeanDagTest/GC/Chop.lean`). -/
theorem dosValid_chop (hdos : DoSValid U) : DoSValid (chop U G) := by
  intro b hb i hi
  intro hexp
  have hbU := (mem_chop_ids.mp hb).1
  have hiU : i ∈ (U.block b).refs := chopBlk_refs_subset hi
  have := hdos b hbU i hiU
  rw [← chopBlk_creator (blk := U.block) (G := G)] at this
  exact this (exposedIn_of_exposedIn_chop hb hexp)

end LeanDag
