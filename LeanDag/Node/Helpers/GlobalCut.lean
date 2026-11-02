import LeanDag.Node.Helpers.Global
import LeanDag.Common.Record.Chop
import Mathlib.Data.Nat.Pairing
/-!
# The run's record, padded below a round

`docs/dos-bounds.md` §5, Phase 3.2. A node under bypass may hold a block at
or below its cut whose bypassed reference no honest node knew, so the run's
record of blocks real all the way down (`globalRecord`) need not hold it. A
decision of slot `k` reads the record only from `slotRound k` up. A block is
*real down to `G`* when it lies at or below `G`, or its references are known
and real down to `G` and it is valid at the quorum (`RealDown`).

The blocks real down to `G` and at or above it, with synthetic ancestors
below `G`, form a block record at the original rounds (`padded`): one fresh
identifier for each author and round below `G` (`fresh`), each synthetic
block referencing every synthetic block of the round below (`ladder`,
`synth`), and the blocks at `G` referencing those of `G − 1`. Above `G` a
known block is its own (`padBlk_of_lt`); at `G` it keeps its round, author
and payload (`padBlk_known_fields`).

* **Real down to a round is real down to every higher one** (`RealDown.mono`),
  and a real block is real down to every round (`RealDown.of_real`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (cfg : Config Validator BlockId Payload) (H : Finset Validator)
variable (tr : Trace Validator BlockId Payload)

/-- **A block real down to `G`**: at or below `G`, or with known references
real down to `G` and valid at the quorum. -/
inductive RealDown (G : ℕ) : BlockId → Prop
  | base {j : BlockId} : (content cfg H tr j).round ≤ G → RealDown G j
  | intro {j : BlockId} : G < (content cfg H tr j).round →
      (content cfg H tr j).refs ⊆ knownIds cfg H tr →
      ValidAt cfg.q Clause.none (content cfg H tr) (content cfg H tr j) →
      (∀ x ∈ (content cfg H tr j).refs, RealDown G x) → RealDown G j

open Classical in
/-- The known blocks at or above `G` that are real down to `G`. -/
noncomputable def globalCutIds (G : ℕ) : Finset BlockId :=
  (knownIds cfg H tr).filter fun j => G ≤ (content cfg H tr j).round ∧ RealDown cfg H tr G j

variable {cfg H tr}

open Classical in
theorem mem_globalCutIds {G : ℕ} {j : BlockId} :
    j ∈ globalCutIds cfg H tr G ↔
      j ∈ knownIds cfg H tr ∧ G ≤ (content cfg H tr j).round ∧ RealDown cfg H tr G j := by
  unfold globalCutIds
  exact Finset.mem_filter

/-- **Real down to a round is real down to every higher one.** -/
theorem RealDown.mono {G G' : ℕ} (hG : G ≤ G') {j : BlockId} (h : RealDown cfg H tr G j) :
    RealDown cfg H tr G' j := by
  induction h with
  | base hr => exact .base (by omega)
  | @intro j hr hs hv _ ih =>
    by_cases hj : (content cfg H tr j).round ≤ G'
    · exact .base hj
    · exact .intro (by omega) hs hv ih

/-- **A real block is real down to every round.** -/
theorem RealDown.of_real (G : ℕ) {j : BlockId} (h : Real cfg H tr j) : RealDown cfg H tr G j := by
  induction h with
  | @intro j hs hv _ ih =>
    by_cases hj : (content cfg H tr j).round ≤ G
    · exact .base hj
    · exact .intro (by omega) hs hv ih

variable (hinj : HashInjective cfg H tr) (hauth : Authentic cfg H tr)

/-! ## The record padded below a round

The cut rebases rounds. Keeping them instead, the blocks real down to `G`
are given synthetic ancestors: one fresh identifier for each author and
round below `G`, each block referencing every block of the round below, and
the blocks at `G` reference those of `G − 1` (`padded`). It is a block
record at the original rounds, so decisions on it read as on any record. -/

section Padded

variable [Infinite BlockId]

theorem knownIds_compl_infinite :
    ((↑(knownIds cfg H tr) : Set BlockId)ᶜ).Infinite :=
  (Finset.finite_toSet _).infinite_compl

variable (cfg H tr) in
/-- **A fresh identifier** for an author and a round, known to no honest node. -/
noncomputable def fresh (x : Validator × ℕ) : BlockId :=
  haveI := (knownIds_compl_infinite (cfg := cfg) (H := H) (tr := tr)).to_subtype
  (Infinite.natEmbedding ↥((↑(knownIds cfg H tr) : Set BlockId)ᶜ)
    (Nat.pair (Fintype.equivFin Validator x.1) x.2)).1

theorem fresh_notMem (x : Validator × ℕ) : fresh cfg H tr x ∉ knownIds cfg H tr := by
  haveI := (knownIds_compl_infinite (cfg := cfg) (H := H) (tr := tr)).to_subtype
  exact (Infinite.natEmbedding ↥((↑(knownIds cfg H tr) : Set BlockId)ᶜ) _).2

theorem fresh_injective : Function.Injective (fresh cfg H tr) := by
  haveI := (knownIds_compl_infinite (cfg := cfg) (H := H) (tr := tr)).to_subtype
  intro x y h
  have h1 := Subtype.ext h
  have h2 := (Infinite.natEmbedding _).injective h1
  obtain ⟨ha, hb⟩ := Nat.pair_eq_pair.mp h2
  exact Prod.ext ((Fintype.equivFin Validator).injective (Fin.ext ha)) hb

variable (cfg H tr) in
/-- The synthetic blocks of round `r`, one for each author. -/
noncomputable def ladder (r : ℕ) : Finset BlockId :=
  Finset.univ.image fun v => fresh cfg H tr (v, r)

variable (cfg H tr) in
/-- The synthetic block of an author at a round. -/
noncomputable def synth (x : Validator × ℕ) : Block Validator BlockId Payload :=
  { round := x.2, creator := x.1, refs := if x.2 = 0 then ∅ else ladder cfg H tr (x.2 - 1),
    payload := cfg.genesis.payload }

variable (cfg H tr) in
open Classical in
/-- **The block map padded below `G`.** -/
noncomputable def padBlk (G : ℕ) (j : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x : Validator × ℕ, fresh cfg H tr x = j then
    synth cfg H tr (Classical.choose h)
  else if (content cfg H tr j).round ≤ G then
    { content cfg H tr j with refs := if G = 0 then ∅ else ladder cfg H tr (G - 1) }
  else content cfg H tr j

theorem padBlk_fresh (G : ℕ) (x : Validator × ℕ) :
    padBlk cfg H tr G (fresh cfg H tr x) = synth cfg H tr x := by
  have h : ∃ y : Validator × ℕ, fresh cfg H tr y = fresh cfg H tr x := ⟨x, rfl⟩
  unfold padBlk
  rw [dif_pos h, fresh_injective (Classical.choose_spec h)]

theorem padBlk_known {G : ℕ} {j : BlockId} (hj : j ∈ knownIds cfg H tr) :
    padBlk cfg H tr G j =
      if (content cfg H tr j).round ≤ G then
        { content cfg H tr j with refs := if G = 0 then ∅ else ladder cfg H tr (G - 1) }
      else content cfg H tr j := by
  have h : ¬ ∃ x : Validator × ℕ, fresh cfg H tr x = j :=
    fun ⟨x, hx⟩ => fresh_notMem x (hx ▸ hj)
  unfold padBlk
  rw [dif_neg h]

/-- Above `G`, a known block is its own. -/
theorem padBlk_of_lt {G : ℕ} {j : BlockId} (hj : j ∈ knownIds cfg H tr)
    (hr : G < (content cfg H tr j).round) :
    padBlk cfg H tr G j = content cfg H tr j := by
  rw [padBlk_known hj, if_neg (by omega)]

/-- A known block keeps its round, author and payload. -/
theorem padBlk_known_fields {G : ℕ} {j : BlockId} (hj : j ∈ knownIds cfg H tr) :
    (padBlk cfg H tr G j).round = (content cfg H tr j).round ∧
      (padBlk cfg H tr G j).creator = (content cfg H tr j).creator ∧
      (padBlk cfg H tr G j).payload = (content cfg H tr j).payload := by
  rw [padBlk_known hj]
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem card_creators_ladder (r : ℕ) (G : ℕ) :
    (creatorsOf (padBlk cfg H tr G)
      (ladder cfg H tr r)).card = Fintype.card Validator := by
  have : creatorsOf (padBlk cfg H tr G)
      (ladder cfg H tr r) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun v => mem_creatorsOf.mpr
      ⟨fresh cfg H tr (v, r),
        Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [padBlk_fresh]
    rfl
  rw [this, Finset.card_univ]

theorem round_ladder {r G : ℕ} {x : BlockId} (hx : x ∈ ladder cfg H tr r) :
    (padBlk cfg H tr G x).round = r := by
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  rw [padBlk_fresh]; rfl

variable (cfg H tr) in
/-- The identifiers of the record padded below `G`. -/
noncomputable def paddedIds (G : ℕ) : Finset BlockId :=
  globalCutIds cfg H tr G ∪ (Finset.range G).biUnion (ladder cfg H tr)

theorem mem_paddedIds {G : ℕ} {j : BlockId} :
    j ∈ paddedIds cfg H tr G ↔
      j ∈ globalCutIds cfg H tr G ∨ ∃ x : Validator × ℕ, x.2 < G ∧ fresh cfg H tr x = j := by
  simp only [paddedIds, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, ladder,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨r, hr, v, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(v, r), hr, rfl⟩
  · rintro (h | ⟨⟨v, r⟩, hr, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, v, rfl⟩

theorem ladder_sub {r G : ℕ} (hr : r < G) :
    ladder cfg H tr r ⊆ paddedIds cfg H tr G := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
  exact mem_paddedIds.mpr (Or.inr ⟨(v, r), hr, rfl⟩)

include hinj hauth in
/-- **The run's record, padded below `G`**, at quorum `q ≤ n`. -/
noncomputable def padded (hq : cfg.q ≤ Fintype.card Validator) (G : ℕ) :
    BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H where
  ids := paddedIds cfg H tr G
  block := padBlk cfg H tr G
  complete := by
    intro i hi x hx
    rcases mem_paddedIds.mp hi with hi | ⟨⟨v, r⟩, hr, rfl⟩
    · obtain ⟨hik, hiG, hreal⟩ := mem_globalCutIds.mp hi
      rw [padBlk_known hik] at hx
      split at hx
      · dsimp only at hx
        split at hx
        · exact absurd hx (Finset.notMem_empty x)
        · exact ladder_sub (by omega) hx
      · cases hreal with
        | base hr => omega
        | intro hlt hs hv hrx =>
          have hxr := Validity.Mechanised.pred _ _ hv x hx
          exact mem_paddedIds.mpr (Or.inl (mem_globalCutIds.mpr ⟨hs hx, by omega, hrx x hx⟩))
    · rw [padBlk_fresh] at hx
      simp only [synth] at hx
      split at hx
      · exact absurd hx (Finset.notMem_empty x)
      · exact ladder_sub (by omega) hx
  valid := by
    intro i hi
    rcases mem_paddedIds.mp hi with hi | ⟨⟨v, r⟩, hr, rfl⟩
    · obtain ⟨hik, hiG, hreal⟩ := mem_globalCutIds.mp hi
      by_cases hle : (content cfg H tr i).round ≤ G
      · rw [padBlk_known hik, if_pos hle]
        refine ⟨fun x hx => ?_, fun h0 => ?_, trivial⟩
        · dsimp only at hx ⊢
          split at hx
          · exact absurd hx (Finset.notMem_empty x)
          · rw [round_ladder hx]; omega
        · dsimp only at h0 ⊢
          split
          · omega
          · change cfg.q ≤ (creatorsOf _ _).card
            rw [card_creators_ladder]; exact hq
      · rw [padBlk_of_lt hik (by omega)]
        cases hreal with
        | base hr => omega
        | intro hlt hs hv hrx =>
          refine ⟨fun x hx => ?_, fun h0 => ?_, trivial⟩
          · rw [(padBlk_known_fields (G := G) (hs hx)).1]
            exact hv.predecessor x hx
          · have hc : creatorsOf (padBlk cfg H tr G) (content cfg H tr i).refs =
                creatorsOf (content cfg H tr) (content cfg H tr i).refs :=
              Finset.image_congr fun x hx => (padBlk_known_fields (G := G) (hs hx)).2.1
            change cfg.q ≤ (creatorsOf _ _).card
            rw [hc]
            exact hv.quorum h0
    · rw [padBlk_fresh]
      refine ⟨fun x hx => ?_, fun h0 => ?_, trivial⟩
      · simp only [synth] at hx ⊢
        split at hx
        · exact absurd hx (Finset.notMem_empty x)
        · rw [round_ladder hx]; omega
      · simp only [synth] at h0 ⊢
        change cfg.q ≤ (creatorsOf _ _).card
        rw [if_neg (by omega), card_creators_ladder]
        exact hq
  no_equivocation := by
    intro i hi j hj hc hcr hr
    have hround : ∀ k ∈ paddedIds cfg H tr G,
        (k ∈ globalCutIds cfg H tr G ∧ G ≤ (padBlk cfg H tr G k).round) ∨
          ∃ x : Validator × ℕ, x.2 < G ∧ fresh cfg H tr x = k ∧
            padBlk cfg H tr G k = synth cfg H tr x := by
      intro k hk
      rcases mem_paddedIds.mp hk with hk | ⟨x, hx, rfl⟩
      · obtain ⟨hkk, hkG, -⟩ := mem_globalCutIds.mp hk
        exact Or.inl ⟨hk, (padBlk_known_fields hkk).1 ▸ hkG⟩
      · exact Or.inr ⟨x, hx, rfl, padBlk_fresh G x⟩
    rcases hround i hi with ⟨hi', hiG⟩ | ⟨x, hx, rfl, hix⟩ <;>
      rcases hround j hj with ⟨hj', hjG⟩ | ⟨y, hy, rfl, hjy⟩
    · obtain ⟨hik, -, -⟩ := mem_globalCutIds.mp hi'
      obtain ⟨hjk, -, -⟩ := mem_globalCutIds.mp hj'
      have fi := padBlk_known_fields (G := G) hik
      have fj := padBlk_known_fields (G := G) hjk
      rw [fi.2.1] at hc hcr
      rw [fj.2.1] at hcr
      rw [fi.1, fj.1] at hr
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_knownIds hik
      obtain ⟨y, hy, rfl⟩ := exists_of_mem_knownIds hjk
      simp only [content_of_known hinj hx, content_of_known hinj hy] at hc hcr hr
      have hbx := mem_persists_of_known hinj hauth hx hc
      have hby := mem_persists_of_known hinj hauth hy (hcr ▸ hc)
      rw [hcr] at hbx
      exact congrArg Prod.fst (eq_of_persists _ hbx hby hr)
    · rw [hjy] at hr; simp only [synth] at hr; omega
    · rw [hix] at hr; simp only [synth] at hr; omega
    · rw [hix, hjy] at hcr hr
      simp only [synth] at hcr hr
      exact congrArg _ (Prod.ext hcr hr)

end Padded

end Node

end LeanDag
