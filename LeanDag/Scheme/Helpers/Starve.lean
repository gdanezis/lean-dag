import LeanDag.Scheme.Helpers.Async
import LeanDag.Scheme.Model.AsyncPace
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Fin
/-!
# The asynchronous rows: buffer rounds past two add nothing

On `n` validators, the first `f` Byzantine, the `m = n − q` honest
validators `f, …, f + m − 1` are starved: their blocks are referenced only
by their own kind. Every block of a starved validator references the whole
round below; every other block references the round below less the starved
validators' blocks, which is `q` authors. A block outside the starved set
then never reaches a starved block (`not_starved_of_reaches`), at any
depth, while every block above round `0` reaches every round-`0` block
outside it. The safe set at round `0` is the honest validators outside the
starved set, `q − f` of them, at every vote offset (`card_safeAt_starve`):
the two-buffer count `q ≤ |safe| + f` is attained, and further buffer
rounds do not raise it.

The record is what validators produce under eventual delivery when each
references, at each round, every block of the round below it holds, and
the starved validators' blocks reach the others one round late
(`starvePace`, `refs_starve_eq_held`).
-/

namespace LeanDag

namespace Scheme

namespace Starve

variable (n f q : ℕ)

/-- Validator `v` is starved: `f ≤ v < f + (n − q)`. -/
def starved (v : Fin n) : Bool := decide (f ≤ v.val ∧ v.val < f + (n - q))

/-- The honest validators: all but the first `f`. -/
def honestSet : Finset (Fin n) := Finset.univ.filter fun v => f ≤ v.val

/-- Validator `v`'s round-`r` block, identified by `(r, v)`. -/
def blk (b : Lex (ℕ × Fin n)) : Block (Fin n) (Lex (ℕ × Fin n)) Unit where
  round := (ofLex b).1
  creator := (ofLex b).2
  refs := if (ofLex b).1 = 0 then ∅ else
    (Finset.univ.filter fun w => starved n f q (ofLex b).2 || !starved n f q w).image
      fun w => toLex ((ofLex b).1 - 1, w)
  payload := ()

variable {n f q}

@[simp] theorem blk_round (b : Lex (ℕ × Fin n)) : (blk n f q b).round = (ofLex b).1 := rfl
@[simp] theorem blk_creator (b : Lex (ℕ × Fin n)) : (blk n f q b).creator = (ofLex b).2 := rfl

theorem mem_blk_refs {b j : Lex (ℕ × Fin n)} :
    j ∈ (blk n f q b).refs ↔ (ofLex j).1 + 1 = (ofLex b).1 ∧
      (starved n f q (ofLex b).2 = true ∨ starved n f q (ofLex j).2 = false) := by
  unfold blk
  dsimp only
  split
  · rename_i h
    simp only [Finset.notMem_empty, false_iff, not_and]
    intro h'
    omega
  · rename_i h
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [ofLex_toLex]
      exact ⟨by omega, hw⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(ofLex j).2, h2, ?_⟩
      rw [← toLex_ofLex j]
      congr 1
      ext <;> simp; omega

/-- The record up to round `N`. -/
def record (hqn : q ≤ n) (N : ℕ) :
    BlockRecord (Fin n) (Lex (ℕ × Fin n)) Unit (ValidAt q (Clause.distinct.and Clause.selfParent))
      (honestSet n f) where
  ids := ((Finset.range (N + 1)) ×ˢ Finset.univ).map toLex.toEmbedding
  block := blk n f q
  complete i hi j hj := by
    simp only [Finset.mem_map, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true,
      Equiv.coe_toEmbedding] at hi ⊢
    obtain ⟨x, hx, rfl⟩ := hi
    have h := (mem_blk_refs.mp hj).1
    simp only [ofLex_toLex] at h
    exact ⟨ofLex j, by omega, toLex_ofLex j⟩
  valid i _ := by
    refine ⟨fun j hj => (mem_blk_refs.mp hj).1, fun hr => ?_, fun j hj l hl hjl => ?_,
      fun hr => ?_⟩
    · -- the non-starved validators, `q` of them, are among the creators
      have hsub : (Finset.univ.filter fun w => starved n f q w = false) ⊆
          creators (blk n f q) (blk n f q i) := by
        intro w hw
        refine mem_creatorsOf.mpr ⟨toLex ((ofLex i).1 - 1, w), mem_blk_refs.mpr ?_, by simp⟩
        simp only [ofLex_toLex]
        exact ⟨by simp only [blk_round] at hr; omega, Or.inr (Finset.mem_filter.mp hw).2⟩
      refine le_trans ?_ (Finset.card_le_card hsub)
      have hcard : (Finset.univ.filter fun w : Fin n => starved n f q w = true).card ≤ n - q := by
        calc _ ≤ (Finset.Ico f (f + (n - q))).card := by
              refine Finset.card_le_card_of_injOn (fun w => w.val) (fun w hw => ?_)
                (fun a _ b _ h => Fin.ext h)
              have := (Finset.mem_filter.mp hw).2
              simp only [starved, decide_eq_true_eq] at this
              simp only [Finset.coe_Ico, Set.mem_Ico]
              exact this
          _ = n - q := by simp
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun w => starved n f q w = true)
      simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at hsplit
      omega
    · simp only [blk_creator] at hjl
      have h1 := (mem_blk_refs.mp hj).1
      have h2 := (mem_blk_refs.mp hl).1
      rw [← toLex_ofLex j, ← toLex_ofLex l]
      congr 1
      exact Prod.ext (by omega) hjl
    · refine ⟨toLex ((ofLex i).1 - 1, (ofLex i).2), mem_blk_refs.mpr ?_, by simp⟩
      simp only [ofLex_toLex]
      refine ⟨by simp only [blk_round] at hr; omega, ?_⟩
      cases starved n f q (ofLex i).2 <;> simp
  no_equivocation i _ j _ _ hc hr := by
    rw [← toLex_ofLex i, ← toLex_ofLex j]
    exact congrArg toLex (Prod.ext hr hc)

variable {hqn : q ≤ n} {N : ℕ}

theorem mem_record_ids {b : Lex (ℕ × Fin n)} :
    b ∈ (record (f := f) hqn N).ids ↔ (ofLex b).1 ≤ N := by
  simp only [record, Finset.mem_map, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩; simp only [ofLex_toLex]; omega
  · intro h; exact ⟨ofLex b, by omega, toLex_ofLex b⟩

/-- **A block outside the starved set never reaches a starved block.** -/
theorem not_starved_of_reaches {b j : Lex (ℕ × Fin n)} (hb : starved n f q (ofLex b).2 = false)
    (h : Reaches (record (f := f) hqn N) b j) : starved n f q (ofLex j).2 = false := by
  induction h with
  | refl => exact hb
  | tail _ hstep ih =>
    rcases (mem_blk_refs.mp hstep).2 with h' | h'
    · rw [ih] at h'; exact absurd h' (by simp)
    · exact h'

/-- **Every block above round `0` reaches every round-`0` block outside the
starved set**, down the chain of its author. -/
theorem reaches_of_not_starved {v : Fin n} (hv : starved n f q v = false) :
    ∀ k, 1 ≤ k → k ≤ N → ∀ b : Lex (ℕ × Fin n), (ofLex b).1 = k →
      Reaches (record (f := f) hqn N) b (toLex (0, v)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hkN b hb
    have hstep : toLex (k, v) ∈ (blk n f q b).refs :=
      mem_blk_refs.mpr ⟨by simp [hb], Or.inr (by simpa using hv)⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Reaches.single hstep
    · exact Reaches.trans (Reaches.single hstep) (ih hk (by omega) _ (by simp))

/-- **The safe set at round `0`** is the honest validators outside the
starved set, at every vote offset within the horizon. -/
theorem safeAt_starve {p : Params} (hvo : 1 ≤ p.voteOffset) (hN : p.voteOffset ≤ N)
    (hfq : f < q) :
    safeAt p (record (f := f) hqn N) 0 =
      Finset.univ.filter fun v : Fin n => f + (n - q) ≤ v.val := by
  ext v
  have hmem : v ∈ honestSet n f ↔ f ≤ v.val := by simp [honestSet]
  rw [mem_safeAt, hmem, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvf, L, hL, hLr, hLc, hsafe⟩
    by_contra hlt
    push Not at hlt
    have hreach := hsafe (toLex (p.voteOffset, ⟨f + (n - q), by omega⟩))
      (mem_record_ids.mpr (by simpa using hN)) (by change p.voteOffset = 0 + p.voteOffset; omega)
    have := not_starved_of_reaches (hqn := hqn) (N := N)
      (by simp [starved]) hreach
    simp only [starved, decide_eq_false_iff_not, not_and, not_lt] at this
    have hLv : (ofLex L).2 = v := hLc
    rw [hLv] at this
    have := this hvf
    omega
  · intro hv
    have hns : starved n f q v = false := by simp [starved]; omega
    refine ⟨by omega, toLex (0, v), mem_record_ids.mpr (by simp), rfl, rfl,
      fun b hb hbr => ?_⟩
    change (ofLex b).1 = 0 + p.voteOffset at hbr
    rw [Nat.zero_add] at hbr
    exact reaches_of_not_starved hns p.voteOffset hvo hN b hbr

theorem card_filter_le_val (n m : ℕ) :
    (Finset.univ.filter fun v : Fin n => m ≤ v.val).card = n - min n m := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun v : Fin n => v.val < m)
  simp only [Finset.card_univ, Fintype.card_fin, not_lt] at h
  rw [Fin.card_filter_val_lt] at h
  omega

/-- **`q − f` safe validators**, at every vote offset within the horizon. -/
theorem card_safeAt_starve {p : Params} (hvo : 1 ≤ p.voteOffset) (hN : p.voteOffset ≤ N)
    (hfq : f < q) : (safeAt p (record (f := f) hqn N) 0).card = q - f := by
  rw [safeAt_starve hvo hN hfq, card_filter_le_val]
  omega

/-- The Byzantine validators are the first `f`. -/
theorem card_compl_honestSet (hfn : f ≤ n) : (honestSet n f)ᶜ.card = f := by
  have : (honestSet n f)ᶜ = Finset.univ.filter fun v : Fin n => v.val < f := by
    ext v; simp [honestSet]
  rw [this, Fin.card_filter_val_lt]
  omega

/-- Every validator builds every round up to the horizon. -/
theorem populated_record {r : ℕ} (hr : r ≤ N) :
    PopulatedOn (record (f := f) hqn N) Finset.univ r :=
  fun v _ => ⟨toLex (r, v), mem_record_ids.mpr (by simpa using hr), rfl, rfl⟩

/-- What `v` holds at time `t`: every block below round `t − 1`, and of
round `t − 1` the blocks outside the starved set, or all of them if `v`
is starved. Round `r` is built at time `r`. -/
def held (N : ℕ) (v : Fin n) (t : ℕ) : Finset (Lex (ℕ × Fin n)) :=
  (record (f := f) hqn N).ids.filter fun b =>
    (ofLex b).1 + 1 < t ∨
      ((ofLex b).1 + 1 = t ∧ (starved n f q v = true ∨ starved n f q (ofLex b).2 = false))

/-- **The starving record, produced under eventual delivery**: the starved
validators' blocks reach the others one round late. -/
def starvePace (N : ℕ) : AsyncPace q (record (f := f) hqn N) (honestSet n f) N where
  top := fun _ => N
  built_of_le_top := fun v _ r hr =>
    ⟨toLex (r, v), mem_record_ids.mpr (by simpa using hr), rfl, rfl⟩
  holds := held (hqn := hqn) N
  holds_sub := fun _ _ => Finset.filter_subset _ _
  holds_closed := fun v _ t b hb j hj => by
    obtain ⟨hbU, hbt⟩ := Finset.mem_filter.mp hb
    have hjr := (mem_blk_refs.mp hj).1
    refine Finset.mem_filter.mpr ⟨(record (f := f) hqn N).complete b hbU j hj, Or.inl ?_⟩
    rcases hbt with h | ⟨h, -⟩
    · change (ofLex b).1 + 1 < t at h; omega
    · change (ofLex b).1 + 1 = t at h; omega
  holds_mono := fun v s t hst b hb => by
    obtain ⟨hbU, hbt⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨hbU, ?_⟩
    rcases Nat.lt_or_ge s t with hlt | hge
    · rcases hbt with h | ⟨h, -⟩ <;> exact Or.inl (by omega)
    · have : s = t := by omega
      subst this; exact hbt
  holds_own := fun v _ b hb hbc => ⟨(ofLex b).1 + 1, Finset.mem_filter.mpr ⟨hb, Or.inr ⟨rfl, by
    change (ofLex b).2 = v at hbc
    rw [hbc]
    cases starved n f q v <;> simp⟩⟩⟩
  converges := fun v _ w _ t => ⟨1, fun b hb => by
    obtain ⟨hbU, hbt⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hbU, Or.inl (by rcases hbt with h | ⟨h, -⟩ <;> omega)⟩⟩
  advancesAt := fun _ _ _ h _ _ => h

/-- **Each block references every block of the round below its author
holds** when it builds. -/
theorem refs_starve_eq_held {v : Fin n} {b : Lex (ℕ × Fin n)}
    (hb : b ∈ (record (f := f) hqn N).ids)
    (hbc : (ofLex b).2 = v) :
    (blk n f q b).refs =
      ((starvePace (f := f) (hqn := hqn) N).holds v (ofLex b).1).filter
        fun j => (ofLex j).1 + 1 = (ofLex b).1 := by
  ext j
  change j ∈ (blk n f q b).refs ↔ j ∈ (held (hqn := hqn) N v (ofLex b).1).filter _
  simp only [held, Finset.mem_filter]
  rw [mem_blk_refs, hbc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨mem_record_ids.mpr (by have := mem_record_ids.mp hb; omega), Or.inr ⟨h1, h2⟩⟩, h1⟩
  · rintro ⟨⟨-, h | ⟨-, h2⟩⟩, h1⟩
    · omega
    · exact ⟨h1, h2⟩

end Starve

end Scheme

end LeanDag
