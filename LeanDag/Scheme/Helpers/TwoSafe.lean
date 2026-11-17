import LeanDag.Scheme.Helpers.Async
import LeanDag.Scheme.Model.AsyncPace
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Fin
/-!
# The asynchronous rows: one buffer round can leave two safe validators

On `n = b + 2k + 1` validators, `q = b + k + 1`, the first `b` Byzantine,
validators `b` and `b + 1` are `x₁` and `x₂`, and validator `b + 2 + y` has
label `y < m = 2k − 1`. A round-`1` block references the round-`0` blocks
of the Byzantine validators, of `x₁` and `x₂`, and of the `k − 1` labels
from a centre along the cycle of labels: its own label for a labelled
author, `0` for `x₁`, `k − 1` for `x₂`. A Byzantine validator has one
round-`1` block per label `x`, centred one past `x`. At round `2`, `x₁` and
`x₂` reference every honest round-`1` block; the validator labelled
`ℓ = x + 1` references the Byzantine blocks for `x`, the honest blocks of
the `k` labels from `ℓ`, and the block of `x₁` or `x₂` whose window misses
`x`. No round-`2` block then reaches the round-`0` block of `x`, while every
round-`2` block reaches `x₁` and `x₂`: at a vote offset of two the safe set
at round `0` is `{x₁, x₂}` (`card_safeAt_twoSafe`).

The record is what validators produce under eventual delivery when each
references, at each round, every block of the round below it holds
(`twoPace`, `refs_eq_held`).
-/

namespace LeanDag

namespace Scheme

namespace TwoSafe

variable (b k : ℕ)

/-- The block identifiers: round, author, and the Byzantine authors' label. -/
abbrev Id := Lex (ℕ × Lex (Fin (b + 2 * k + 1) × ℕ))

/-- Block `x`'s round. -/
def rd (x : Id b k) : ℕ := (ofLex x).1

/-- Block `x`'s author. -/
def au (x : Id b k) : Fin (b + 2 * k + 1) := (ofLex (ofLex x).2).1

/-- Block `x`'s label, for a Byzantine author's round-`1` block. -/
def vr (x : Id b k) : ℕ := (ofLex (ofLex x).2).2

/-- The block of round `r` by `v` with label `i`. -/
def mk (r : ℕ) (v : Fin (b + 2 * k + 1)) (i : ℕ) : Id b k := toLex (r, toLex (v, i))

variable {b k} in
@[simp] theorem rd_mk (r : ℕ) (v : Fin (b + 2 * k + 1)) (i : ℕ) : rd b k (mk b k r v i) = r := rfl
variable {b k} in
@[simp] theorem au_mk (r : ℕ) (v : Fin (b + 2 * k + 1)) (i : ℕ) : au b k (mk b k r v i) = v := rfl
variable {b k} in
@[simp] theorem vr_mk (r : ℕ) (v : Fin (b + 2 * k + 1)) (i : ℕ) : vr b k (mk b k r v i) = i := rfl

variable {b k} in
theorem mk_rd (x : Id b k) : mk b k (rd b k x) (au b k x) (vr b k x) = x := by
  simp [mk, rd, au, vr]

variable {b k} in
theorem mk_inj {r r' : ℕ} {v v' : Fin (b + 2 * k + 1)} {i i' : ℕ}
    (h : mk b k r v i = mk b k r' v' i') : r = r' ∧ v = v' ∧ i = i' := by
  have h1 := congrArg (rd b k) h
  have h2 := congrArg (au b k) h
  have h3 := congrArg (vr b k) h
  simp only [rd_mk, au_mk, vr_mk] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The distance from label `l` to label `y` along the cycle of `2k − 1` labels. -/
def cdist (l y : ℕ) : ℕ := if l ≤ y then y - l else y + (2 * k - 1) - l

/-- The label after `i` on the cycle. -/
def succL (i : ℕ) : ℕ := if i + 1 = 2 * k - 1 then 0 else i + 1

/-- The label before `l` on the cycle. -/
def predL (l : ℕ) : ℕ := if l = 0 then 2 * k - 2 else l - 1

/-- Validator `w` is labelled within `len` of label `l`. -/
def inWin (l len : ℕ) (w : Fin (b + 2 * k + 1)) : Prop :=
  b + 2 ≤ w.val ∧ cdist k l (w.val - (b + 2)) < len

instance (l len : ℕ) (w : Fin (b + 2 * k + 1)) : Decidable (inWin b k l len w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The centre of the window of author `v`'s round-`1` block `i`. -/
def center (v : Fin (b + 2 * k + 1)) (i : ℕ) : ℕ :=
  if v.val < b then succL k i else if v.val = b then 0 else if v.val = b + 1 then k - 1
  else v.val - (b + 2)

/-- `x₁` or `x₂`, whichever's window misses the label before `v`'s. -/
def sel (v : Fin (b + 2 * k + 1)) : ℕ :=
  if k - 1 ≤ predL k (v.val - (b + 2)) then b else b + 1

/-- The authors a round-`1` block centred at `l` references. -/
def A1 (l : ℕ) : Finset (Fin (b + 2 * k + 1)) :=
  Finset.univ.filter fun w => w.val < b + 2 ∨ inWin b k l (k - 1) w

/-- The authors a labelled round-`2` block references. -/
def A2 (v : Fin (b + 2 * k + 1)) : Finset (Fin (b + 2 * k + 1)) :=
  Finset.univ.filter fun w => w.val < b ∨ inWin b k (v.val - (b + 2)) k w ∨ w.val = sel b k v

/-- The references of block `x`. -/
def refsOf (x : Id b k) : Finset (Id b k) :=
  if (rd b k x) = 1 then
    (A1 b k (center b k (au b k x) (vr b k x))).image fun w => mk b k 0 w (0)
  else if (rd b k x) = 2 then
    if (au b k x).val < b + 2 then
      (Finset.univ.filter fun w : Fin (b + 2 * k + 1) => b ≤ w.val).image
        fun w => mk b k 1 w (0)
    else
      (A2 b k (au b k x)).image fun w =>
        mk b k 1 w (if w.val < b then predL k ((au b k x).val - (b + 2)) else 0)
  else ∅

/-- Block `x`. -/
def blk (x : Id b k) : Block (Fin (b + 2 * k + 1)) (Id b k) Unit where
  round := (rd b k x)
  creator := (au b k x)
  refs := refsOf b k x
  payload := ()

/-- The blocks that exist. -/
def IsId (x : Id b k) : Prop :=
  (rd b k x = 0 ∧ (vr b k x) = 0) ∨
  (rd b k x = 1 ∧ ((b ≤ (au b k x).val ∧ (vr b k x) = 0) ∨
    ((au b k x).val < b ∧ (vr b k x) < 2 * k - 1))) ∨
  (rd b k x = 2 ∧ b ≤ (au b k x).val ∧ (vr b k x) = 0)

instance (x : Id b k) : Decidable (IsId b k x) := by unfold IsId; infer_instance

/-- The honest validators: all but the first `b`. -/
def honestSet : Finset (Fin (b + 2 * k + 1)) := Finset.univ.filter fun v => b ≤ v.val

/-- The identifiers, as a finite set. -/
def ids : Finset (Id b k) :=
  ((Finset.range 3 ×ˢ (Finset.univ : Finset (Fin (b + 2 * k + 1))) ×ˢ Finset.range (2 * k)).image
    fun t => mk b k t.1 t.2.1 t.2.2).filter (IsId b k)

variable {b k}

theorem mem_ids {x : Id b k} (hk : 1 ≤ k) : x ∈ ids b k ↔ IsId b k x := by
  unfold ids
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨⟨(rd b k x, (au b k x), (vr b k x)), ?_, mk_rd x⟩, h⟩
    unfold IsId at h
    simp only
    omega

theorem mem_refsOf {x j : Id b k} : j ∈ refsOf b k x ↔
    (rd b k x = 1 ∧ ∃ w ∈ A1 b k (center b k (au b k x) (vr b k x)),
      j = mk b k 0 w (0)) ∨
    (rd b k x = 2 ∧ (au b k x).val < b + 2 ∧ ∃ w : Fin (b + 2 * k + 1), b ≤ w.val ∧
      j = mk b k 1 w (0)) ∨
    (rd b k x = 2 ∧ b + 2 ≤ (au b k x).val ∧ ∃ w ∈ A2 b k (au b k x),
      j = mk b k 1 w (if w.val < b then predL k ((au b k x).val - (b + 2)) else 0)) := by
  unfold refsOf
  split_ifs with h1 h2 h3
  · simp only [Finset.mem_image, h1, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact Or.inl ⟨w, hw, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact ⟨w, hw, rfl⟩
      · omega
      · omega
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact Or.inr (Or.inl ⟨h2, h3, w, hw, rfl⟩)
    · rintro (⟨h, -⟩ | ⟨-, -, w, hw, rfl⟩ | ⟨-, h, -⟩)
      · omega
      · exact ⟨w, hw, rfl⟩
      · omega
  · simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact Or.inr (Or.inr ⟨h2, by omega, w, hw, rfl⟩)
    · rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, w, hw, rfl⟩)
      · omega
      · omega
      · exact ⟨w, hw, rfl⟩
  · simp only [Finset.notMem_empty, false_iff, not_or, not_and]
    exact ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h2⟩

/-! ## The arithmetic of the cycle -/

theorem cdist_self (l : ℕ) : cdist k l l = 0 := by unfold cdist; simp

/-- From the label after `x`, label `x` is the farthest. -/
theorem cdist_succL {x : ℕ} (hx : x < 2 * k - 1) :
    cdist k (succL k x) x = 2 * k - 2 := by
  unfold cdist succL; split_ifs <;> omega

theorem predL_succL {x : ℕ} (_hx : x < 2 * k - 1) : predL k (succL k x) = x := by
  unfold predL succL
  by_cases h : x + 1 = 2 * k - 1
  · simp only [h, if_true]; omega
  · simp only [h, if_false, Nat.add_one_ne_zero]; omega

theorem succL_lt {x : ℕ} (_hk : 1 ≤ k) (hx : x < 2 * k - 1) : succL k x < 2 * k - 1 := by
  unfold succL; split_ifs <;> omega

theorem predL_lt {l : ℕ} (hk : 1 ≤ k) (hl : l < 2 * k - 1) : predL k l < 2 * k - 1 := by
  unfold predL; split_ifs <;> omega

theorem succL_predL {l : ℕ} (hk : 1 ≤ k) (hl : l < 2 * k - 1) : succL k (predL k l) = l := by
  unfold predL succL
  by_cases h : l = 0
  · simp only [h, if_true]; split_ifs <;> omega
  · simp only [h, if_false]; split_ifs <;> omega

/-- Distances along the cycle add, below one turn. -/
theorem cdist_far {l y x : ℕ} (hl : l < 2 * k - 1) (hy : y < 2 * k - 1)
    (_hx : x < 2 * k - 1) (hlx : cdist k l x = 2 * k - 2) (hly : cdist k l y < k) :
    k - 1 ≤ cdist k y x := by
  unfold cdist at *; split_ifs at * <;> omega

/-! ## The record -/

theorem val_lt (v : Fin (b + 2 * k + 1)) : v.val < b + 2 * k + 1 := v.isLt

theorem refsOf_pred {x j : Id b k} (h : j ∈ refsOf b k x) : (rd b k j) + 1 = (rd b k x) := by
  rcases mem_refsOf.mp h with ⟨h1, w, -, rfl⟩ | ⟨h1, -, w, -, rfl⟩ | ⟨h1, -, w, -, rfl⟩ <;>
    simp [h1]

/-- The window of `len` labels from `l` holds `len` validators. -/
theorem card_win {l len : ℕ} (hl : l < 2 * k - 1) (hlen : len ≤ 2 * k - 1) :
    len ≤ (Finset.univ.filter (inWin b k l len)).card := by
  classical
  let g : Fin len → Fin (b + 2 * k + 1) := fun e => ⟨b + 2 + (if l + e.val < 2 * k - 1 then
    l + e.val else l + e.val - (2 * k - 1)), by have := e.isLt; split_ifs <;> omega⟩
  have hmaps : Set.MapsTo g ↑(Finset.univ : Finset (Fin len))
      ↑(Finset.univ.filter (inWin b k l len)) := by
    intro e _
    have := e.isLt
    simp only [g, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, inWin, cdist]
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega
  have hinj : Set.InjOn g ↑(Finset.univ : Finset (Fin len)) := by
    intro e _ e' _ h
    have h1 := e.isLt
    have h2 := e'.isLt
    have := congrArg Fin.val h
    simp only [g] at this
    apply Fin.ext
    split_ifs at this <;> omega
  have := Finset.card_le_card_of_injOn g hmaps hinj
  simpa using this

theorem card_lt_val (c : ℕ) (hc : c ≤ b + 2 * k + 1) :
    (Finset.univ.filter fun w : Fin (b + 2 * k + 1) => w.val < c).card = c := by
  rw [Fin.card_filter_val_lt]; omega

theorem card_A1 {l : ℕ} (hk : 1 ≤ k) (hl : l < 2 * k - 1) : b + k + 1 ≤ (A1 b k l).card := by
  classical
  have hsplit : A1 b k l = (Finset.univ.filter fun w : Fin (b + 2 * k + 1) => w.val < b + 2) ∪
      Finset.univ.filter (inWin b k l (k - 1)) := by
    ext w; simp [A1]
  have hdisj : Disjoint (Finset.univ.filter fun w : Fin (b + 2 * k + 1) => w.val < b + 2)
      (Finset.univ.filter (inWin b k l (k - 1))) := by
    rw [Finset.disjoint_filter]; intro w _ h1 h2; exact absurd h2.1 (by omega)
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_lt_val _ (by omega)]
  have := card_win (b := b) (k := k) (l := l) (len := k - 1) hl (by omega)
  omega

theorem card_A2 {v : Fin (b + 2 * k + 1)} (hk : 1 ≤ k) (hv : b + 2 ≤ v.val) :
    b + k + 1 ≤ (A2 b k v).card := by
  classical
  have hl : v.val - (b + 2) < 2 * k - 1 := by have := val_lt v; omega
  have hsel : sel b k v < b + 2 * k + 1 := by unfold sel; split_ifs <;> omega
  have hsplit : (Finset.univ.filter fun w : Fin (b + 2 * k + 1) => w.val < b) ∪
      (Finset.univ.filter (inWin b k (v.val - (b + 2)) k) ∪ {⟨sel b k v, hsel⟩}) ⊆ A2 b k v := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hw
    simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with h | h | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr rfl)
  refine le_trans ?_ (Finset.card_le_card hsplit)
  have hsel' : b ≤ sel b k v ∧ sel b k v < b + 2 := by unfold sel; split_ifs <;> omega
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, card_lt_val _ (by omega),
    Finset.card_singleton]
  · have := card_win (b := b) (k := k) (l := v.val - (b + 2)) (len := k) hl (by omega)
    omega
  · rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, inWin, not_and]
    omega
  · rw [Finset.disjoint_union_right, Finset.disjoint_singleton_right]
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_filter]; intro w _ h1 h2; exact absurd h2.1 (by omega)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]; omega

theorem creators_eq_image {x : Id b k} (A : Finset (Fin (b + 2 * k + 1))) (r : ℕ)
    (g : Fin (b + 2 * k + 1) → ℕ) (h : refsOf b k x = A.image fun w => mk b k r w (g w)) :
    creators (blk b k) (blk b k x) = A := by
  unfold creators creatorsOf
  change (refsOf b k x).image _ = A
  rw [h, Finset.image_image]
  convert Finset.image_id (s := A)
  funext w
  rfl

theorem refs_inj {x i j : Id b k} (hi : i ∈ refsOf b k x) (hj : j ∈ refsOf b k x)
    (h : (au b k i) = (au b k j)) : i = j := by
  rcases mem_refsOf.mp hi with ⟨h1, w, -, rfl⟩ | ⟨h1, h2, w, -, rfl⟩ | ⟨h1, h2, w, -, rfl⟩ <;>
  rcases mem_refsOf.mp hj with ⟨h1', w', -, rfl⟩ | ⟨h1', h2', w', -, rfl⟩ | ⟨h1', h2', w', -, rfl⟩ <;>
  simp only [au_mk] at h <;> subst h <;> first | rfl | omega

/-- The record. -/
def record (hk : 2 ≤ k) (hbk : b ≤ k) :
    BlockRecord (Fin (b + 2 * k + 1)) (Id b k) Unit
      (ValidAt (b + k + 1) (Clause.distinct.and Clause.selfParent)) (honestSet b k) where
  ids := ids b k
  block := blk b k
  complete i hi j hj := by
    rw [mem_ids (by omega)] at hi ⊢
    have hv := val_lt (au b k j)
    rcases mem_refsOf.mp hj with ⟨h1, w, -, rfl⟩ | ⟨h1, -, w, hw, rfl⟩ | ⟨h1, h2, w, hw, rfl⟩
    · simp [IsId]
    · simp [IsId, hw]
    · have hl : (au b k i).val - (b + 2) < 2 * k - 1 := by
        have := val_lt (au b k i); omega
      have hp := predL_lt (k := k) (by omega) hl
      have hA := (Finset.mem_filter.mp hw).2
      unfold IsId
      rw [rd_mk, au_mk, vr_mk]
      by_cases hwb : w.val < b
      · rw [if_pos hwb]
        exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨hwb, hp⟩⟩)
      · rw [if_neg hwb]
        have hbw : b ≤ w.val := by
          rcases hA with h | h | h
          · omega
          · exact le_trans (by omega) h.1
          · rw [h]; unfold sel; split_ifs <;> omega
        exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨hbw, rfl⟩⟩)
  valid i hi := by
    rw [mem_ids (by omega)] at hi
    refine ⟨fun j hj => refsOf_pred hj, fun hr => ?_, ⟨fun j hj l hl hjl => refs_inj hj hl hjl,
      fun hr => ?_⟩⟩
    · change 0 < (rd b k i) at hr
      unfold IsId at hi
      rcases hi with ⟨h0, -⟩ | ⟨h1, hv⟩ | ⟨h2, hv, -⟩
      · omega
      · rw [creators_eq_image (A1 b k (center b k (au b k i) (vr b k i))) 0 (fun _ => 0)
          (by unfold refsOf; simp [h1])]
        refine card_A1 (by omega) ?_
        unfold center succL
        have := val_lt (au b k i)
        split_ifs <;> omega
      · by_cases hlo : (au b k i).val < b + 2
        · rw [creators_eq_image (Finset.univ.filter fun w : Fin (b + 2 * k + 1) => b ≤ w.val) 1
            (fun _ => 0) (by unfold refsOf; simp [h2, hlo])]
          have h := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin (b + 2 * k + 1)))) (fun w => w.val < b)
          rw [Finset.card_univ, Fintype.card_fin, card_lt_val _ (by omega)] at h
          simp only [not_lt] at h
          omega
        · rw [creators_eq_image (A2 b k (au b k i)) 1
            (fun w => if w.val < b then predL k ((au b k i).val - (b + 2)) else 0)
            (by unfold refsOf; simp [h2, hlo])]
          exact card_A2 (by omega) (by omega)
    · change 0 < (rd b k i) at hr
      change ∃ j ∈ refsOf b k i, (au b k j) = (au b k i)
      have hv := val_lt (au b k i)
      unfold IsId at hi
      rcases hi with ⟨h0, -⟩ | ⟨h1, hvi⟩ | ⟨h2, hvb, -⟩
      · omega
      · refine ⟨mk b k 0 (au b k i) (0), mem_refsOf.mpr (Or.inl ⟨h1, _, ?_, rfl⟩), rfl⟩
        simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and, inWin, center]
        by_cases hlo : (au b k i).val < b + 2
        · exact Or.inl hlo
        · right
          simp only [show ¬ (au b k i).val < b by omega, if_false,
            show ¬ (au b k i).val = b by omega, show ¬ (au b k i).val = b + 1 by omega]
          rw [cdist_self]; omega
      · by_cases hlo : (au b k i).val < b + 2
        · exact ⟨mk b k 1 (au b k i) (0),
            mem_refsOf.mpr (Or.inr (Or.inl ⟨h2, hlo, _, hvb, rfl⟩)), rfl⟩
        · refine ⟨mk b k 1 (au b k i) (0),
            mem_refsOf.mpr (Or.inr (Or.inr ⟨h2, by omega, au b k i, ?_, ?_⟩)), rfl⟩
          · simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and, inWin]
            right; left
            rw [cdist_self]; omega
          · simp [show ¬ (au b k i).val < b by omega]
  no_equivocation i hi j hj hh hc hr := by
    rw [mem_ids (by omega)] at hi hj
    change (au b k i) ∈ honestSet b k at hh
    change (au b k i) = (au b k j) at hc
    change (rd b k i) = (rd b k j) at hr
    have hb : b ≤ (au b k i).val := by simpa [honestSet] using hh
    have h3 : (vr b k i) = (vr b k j) := by
      unfold IsId at hi hj; rw [← hc] at hj; omega
    rw [← mk_rd i, ← mk_rd j, hr, hc, h3]

variable {hk : 2 ≤ k} {hbk : b ≤ k}

/-- A path two rounds down passes through a reference. -/
theorem reaches_two {y L : Id b k} (hy : y ∈ ids b k) (h : Reaches (record hk hbk) y L)
    (hyr : (rd b k y) = 2) (hLr : (rd b k L) = 0) :
    ∃ j ∈ refsOf b k y, L ∈ refsOf b k j := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨j, hj, hjL⟩
  · omega
  have hjr := refsOf_pred hj
  have hjU : j ∈ (record hk hbk).ids := (record hk hbk).complete y hy j hj
  rcases Relation.ReflTransGen.cases_head hjL with rfl | ⟨j', hj', hj'L⟩
  · omega
  have hj'r := refsOf_pred hj'
  rcases Relation.ReflTransGen.cases_head hj'L with rfl | ⟨j'', hj'', -⟩
  · exact ⟨j, hj, hj'⟩
  · have := refsOf_pred hj''
    omega

/-- **The safe set at round `0`** is `{x₁, x₂}`, at a vote offset of two. -/
theorem safeAt_twoSafe {p : Params} (hvo : p.voteOffset = 2) :
    safeAt p (record hk hbk) 0 =
      Finset.univ.filter fun v : Fin (b + 2 * k + 1) => v.val = b ∨ v.val = b + 1 := by
  ext v
  have hvlt := val_lt v
  rw [mem_safeAt, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, hvo, Nat.zero_add]
  constructor
  · rintro ⟨hvh, L, hL, hLr, hLc, hsafe⟩
    have hvb : b ≤ v.val := by simpa [honestSet] using hvh
    by_contra hx
    have hx2 : b + 2 ≤ v.val := by omega
    obtain ⟨x, hxdef⟩ : ∃ x, x = v.val - (b + 2) := ⟨_, rfl⟩
    have hxm : x < 2 * k - 1 := by omega
    obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = succL k x := ⟨_, rfl⟩
    have hℓ : ℓ < 2 * k - 1 := hℓdef ▸ succL_lt (by omega) hxm
    have hpℓ : predL k ℓ = x := hℓdef ▸ predL_succL hxm
    have hfar : cdist k ℓ x = 2 * k - 2 := hℓdef ▸ cdist_succL (k := k) hxm
    obtain ⟨yv, hyv⟩ : ∃ yv : Fin (b + 2 * k + 1), yv.val = b + 2 + ℓ :=
      ⟨⟨b + 2 + ℓ, by omega⟩, rfl⟩
    have hyU : mk b k 2 yv (0) ∈ ids b k := (mem_ids (by omega)).mpr
      (Or.inr (Or.inr ⟨rfl, show b ≤ yv.val by omega, rfl⟩))
    obtain ⟨j, hj, hLj⟩ := reaches_two hyU (hsafe _ hyU rfl) rfl hLr
    have hyl : yv.val - (b + 2) = ℓ := by omega
    have hLv : (au b k L) = v := hLc
    rcases mem_refsOf.mp hj with ⟨h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, w, hw, rfl⟩
    · simp at h1
    · simp only [au_mk] at h2; omega
    simp only [au_mk, hyl, hpℓ] at hLj
    obtain ⟨-, w', hw', hL'⟩ | ⟨h, -⟩ | ⟨h, -⟩ := mem_refsOf.mp hLj
    · rw [hL'] at hLv
      simp only [au_mk] at hLv
      subst hLv
      simp only [au_mk, vr_mk] at hw'
      simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and, inWin] at hw'
      rcases hw' with h | ⟨-, hwin⟩
      · omega
      rw [← hxdef] at hwin
      simp only [A2, Finset.mem_filter, Finset.mem_univ, true_and, inWin, sel, au_mk, hyl,
        hpℓ] at hw
      have hwlt := val_lt w
      by_cases hwb : w.val < b
      · simp only [center, hwb, ↓reduceIte] at hwin
        rw [← hℓdef] at hwin
        omega
      · rw [center, if_neg hwb] at hwin
        rcases hw with h | ⟨hw2, hwd⟩ | hws
        · omega
        · rw [if_neg (show ¬ w.val = b by omega), if_neg (show ¬ w.val = b + 1 by omega)] at hwin
          have := cdist_far (k := k) (l := ℓ) (y := w.val - (b + 2)) (x := x) hℓ (by omega) hxm
            hfar hwd
          omega
        · split_ifs at hws with hc
          · rw [if_pos hws] at hwin
            unfold cdist at hwin; split_ifs at hwin <;> omega
          · rw [if_neg (show ¬ w.val = b by omega), if_pos hws] at hwin
            unfold cdist at hwin; split_ifs at hwin <;> omega
    · simp at h
    · simp at h
  · intro hv
    refine ⟨by simp [honestSet]; omega, mk b k 0 v (0), (mem_ids (by omega)).mpr
      (Or.inl ⟨rfl, rfl⟩), rfl, rfl, fun y hy hyr => ?_⟩
    change (rd b k y) = 2 at hyr
    have hyI := (mem_ids (by omega)).mp hy
    -- a round-`1` block every round-`2` block references, which references `v`
    obtain ⟨w, hw⟩ : ∃ w : Fin (b + 2 * k + 1), mk b k 1 w (0) ∈ refsOf b k y ∧
        (w.val = b ∨ w.val = b + 1) := by
      by_cases hlo : (au b k y).val < b + 2
      · exact ⟨⟨b, by omega⟩, mem_refsOf.mpr (Or.inr (Or.inl ⟨hyr, hlo, _, le_rfl, rfl⟩)),
          Or.inl rfl⟩
      · have hsel : sel b k (au b k y) < b + 2 * k + 1 := by unfold sel; split_ifs <;> omega
        have hsel' : b ≤ sel b k (au b k y) ∧ sel b k (au b k y) < b + 2 := by
          unfold sel; split_ifs <;> omega
        refine ⟨⟨sel b k (au b k y), hsel⟩, mem_refsOf.mpr (Or.inr (Or.inr
          ⟨hyr, by omega, ⟨sel b k (au b k y), hsel⟩, ?_, ?_⟩)), ?_⟩
        · simp [A2]
        · simp [show ¬ sel b k (au b k y) < b by omega]
        · unfold sel; split_ifs <;> simp
    refine Reaches.trans (Reaches.single hw.1) (Reaches.single ?_)
    change mk b k 0 v (0) ∈ refsOf b k (mk b k 1 w (0))
    refine mem_refsOf.mpr (Or.inl ⟨rfl, v, ?_, rfl⟩)
    simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and]
    left; omega

/-- **Two safe validators**, at a vote offset of two. -/
theorem card_safeAt_twoSafe {p : Params} (hvo : p.voteOffset = 2) :
    (safeAt p (record hk hbk) 0).card = 2 := by
  rw [safeAt_twoSafe hvo]
  have : (Finset.univ.filter fun v : Fin (b + 2 * k + 1) => v.val = b ∨ v.val = b + 1) =
      {⟨b, by omega⟩, ⟨b + 1, by omega⟩} := by
    ext v; simp [Fin.ext_iff]
  rw [this, Finset.card_pair (by simp [Fin.ext_iff])]

theorem card_compl_honestSet : (honestSet b k)ᶜ.card = b := by
  have : (honestSet b k)ᶜ = Finset.univ.filter fun v : Fin (b + 2 * k + 1) => v.val < b := by
    ext v; simp [honestSet]
  rw [this, card_lt_val _ (by omega)]

/-- Every honest validator builds every round up to `2`. -/
theorem populated {r : ℕ} (hr : r ≤ 2) : PopulatedOn (record hk hbk) (honestSet b k) r := by
  intro v hv
  have hvb : b ≤ v.val := by simpa [honestSet] using hv
  refine ⟨mk b k r v (0), (mem_ids (by omega)).mpr ?_, rfl, rfl⟩
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl <;> simp [IsId, hvb]

/-- What `v` holds at time `t`: every block below round `t − 1`, and of
round `t − 1` the references of `v`'s round-`t` block. Round `r` is built
at time `r`. -/
def held (v : Fin (b + 2 * k + 1)) (t : ℕ) : Finset (Id b k) :=
  (ids b k).filter fun x =>
    (rd b k x) + 1 < t ∨ (rd b k x + 1 = t ∧ x ∈ refsOf b k (mk b k t v (0)))

/-- **The record, produced under eventual delivery.** -/
def twoPace : AsyncPace (b + k + 1) (record hk hbk) (honestSet b k) 2 where
  top := fun _ => 2
  built_of_le_top := fun v hv r hr => populated hr v hv
  holds := held
  holds_sub := fun _ _ => Finset.filter_subset _ _
  holds_closed := fun v _ t x hx j hj => by
    obtain ⟨hxU, hxt⟩ := Finset.mem_filter.mp hx
    have hjr := refsOf_pred hj
    refine Finset.mem_filter.mpr ⟨(record hk hbk).complete x hxU j hj, Or.inl ?_⟩
    rcases hxt with h | ⟨h, -⟩ <;> omega
  holds_mono := fun v s t hst x hx => by
    obtain ⟨hxU, hxt⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxU, ?_⟩
    rcases Nat.lt_or_ge s t with hlt | hge
    · rcases hxt with h | ⟨h, -⟩ <;> exact Or.inl (by omega)
    · have : s = t := by omega
      subst this; exact hxt
  holds_own := fun v _ x hx _ => ⟨(rd b k x) + 2, Finset.mem_filter.mpr ⟨hx, Or.inl (by omega)⟩⟩
  converges := fun v _ w _ t => ⟨1, fun x hx => by
    obtain ⟨hxU, hxt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxU, Or.inl (by rcases hxt with h | ⟨h, -⟩ <;> omega)⟩⟩
  advancesAt := fun _ _ _ h _ _ => h

/-- **An honest block references every block of the round below its author
holds** when it builds. -/
theorem refs_eq_held (hk : 2 ≤ k) (hbk : b ≤ k) {x : Id b k} (hx : x ∈ ids b k)
    (hxh : (au b k x) ∈ honestSet b k) :
    refsOf b k x = (held (au b k x) (rd b k x)).filter
      fun j => (rd b k j) + 1 = (rd b k x) := by
  have hx0 : (vr b k x) = 0 := by
    have hb : b ≤ (au b k x).val := by simpa [honestSet] using hxh
    rcases (mem_ids (by omega)).mp hx with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩ | ⟨-, -, h⟩
    · exact h
    · exact h
    · omega
    · exact h
  have hxe : mk b k (rd b k x) (au b k x) (0) = x := by
    rw [← hx0]; exact mk_rd x
  ext j
  simp only [held, Finset.mem_filter]
  constructor
  · intro hj
    have hjr := refsOf_pred hj
    exact ⟨⟨(record hk hbk).complete x hx j hj, Or.inr ⟨hjr, by rwa [hxe]⟩⟩, hjr⟩
  · rintro ⟨⟨-, h | ⟨-, h⟩⟩, hjr⟩
    · omega
    · rwa [hxe] at h

end TwoSafe

end Scheme

end LeanDag
