import LeanDag.Adaptive.Frame
/-!
# A policy that emits the whole schedule

`Policy` varies who leads and holds the rest of the schedule fixed. A
`Schedule` varies all three parts of it: how many slots an epoch holds,
how many an epoch's rounds hold, and which validator holds each place.
Each reads the verdicts of epochs two below the thing being scheduled and
nothing else, which is `Policy.adapted` read of the other two functions.

`epochFrame` and `frameOf` are the two `Frame`s a schedule gives at a
verdict function. Neither is a recursion: `len` and `widthOf` take the
index directly, and it is the *clauses* that name the frames the indices
are read against.

**Trusted core: `Schedule` is a definition.** It asks nothing of a rule.
-/

namespace LeanDag
namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A schedule-emitting policy.** -/
structure Schedule (R : DagRule Validator BlockId Payload) where
  /-- How many slots each epoch holds. -/
  len : (ℕ → Option BlockId) → ℕ → ℕ
  len_pos : ∀ v e, 0 < len v e
  /-- How many slots each round holds. -/
  widthOf : (ℕ → Option BlockId) → ℕ → ℕ
  widthOf_pos : ∀ v r, 0 < widthOf v r
  /-- The bound the descent reads. -/
  maxWidth : ℕ
  widthOf_le : ∀ v r, widthOf v r ≤ maxWidth
  /-- Who leads each slot. -/
  pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator
  /-- **Distinct positions of a round are led by distinct validators**,
  at every width the schedule can choose. -/
  keyed : ∀ (U : R.Universe) (V : R.View U) v r i j,
    i < widthOf v r → j < widthOf v r →
    pick U V v ((Frame.mk (widthOf v) (widthOf_pos v)).index r i)
      = pick U V v ((Frame.mk (widthOf v) (widthOf_pos v)).index r j) → i = j
  /-- **The epoch length reads the verdicts of epochs two below it.** -/
  len_adapted : ∀ v w e,
    (∀ j, (Frame.mk (len v) (len_pos v)).roundOf j + 2 ≤ e → w j = v j) →
    len w e = len v e
  /-- **The width reads the verdicts of epochs two below the epoch its
  round's slots begin in.** -/
  widthOf_adapted : ∀ v w r,
    (∀ j, (Frame.mk (len v) (len_pos v)).roundOf j + 2 ≤
        (Frame.mk (len v) (len_pos v)).roundOf ((Frame.mk (widthOf v) (widthOf_pos v)).cum r) →
      w j = v j) →
    widthOf w r = widthOf v r
  /-- **The leader reads them too**, measured at the epochs of the run
  being compared against. -/
  pick_adapted : ∀ (U : R.Universe) (V₁ V₂ : R.View U) v w k,
    (∀ j, (Frame.mk (len v) (len_pos v)).roundOf j + 2 ≤
        (Frame.mk (len v) (len_pos v)).roundOf k → w j = v j) →
    pick U V₁ w k = pick U V₂ v k

namespace Schedule

variable (P : Schedule R) (v : ℕ → Option BlockId)

/-- The epochs a schedule gives at a verdict function. -/
abbrev epochFrame : Frame := ⟨P.len v, P.len_pos v⟩

/-- The rounds it gives at the same. -/
abbrev frameOf : Frame := ⟨P.widthOf v, P.widthOf_pos v⟩

@[simp] theorem epochFrame_width (e : ℕ) : (P.epochFrame v).width e = P.len v e := rfl

@[simp] theorem frameOf_width (r : ℕ) : (P.frameOf v).width r = P.widthOf v r := rfl

/-- The assignment it gives: position `i` of round `r` is led by the
policy at that position's slot. -/
def asgOf (U : R.Universe) (V : R.View U) : ℕ → ℕ → Validator :=
  fun r i => P.pick U V v ((P.frameOf v).index r i)

theorem asgOf_keyed (U : R.Universe) (V : R.View U) :
    ∀ r i j, i < (P.frameOf v).width r → j < (P.frameOf v).width r →
      P.asgOf v U V r i = P.asgOf v U V r j → i = j :=
  P.keyed U V v

/-- **A schedule that reads nothing.** Any epoch lengths, any widths and
any assignment lawful at those widths, all fixed in advance: the three
adaptedness clauses hold because none of the functions consults a
verdict. It is the arc's conservativity anchor, and it shows the clauses
are satisfiable together at epoch lengths and per-round widths that both
vary. -/
noncomputable def ofFixed (E F : Frame) (M : ℕ) (hM : ∀ r, F.width r ≤ M)
    (a : ℕ → ℕ → Validator)
    (hk : ∀ r i j, i < F.width r → j < F.width r → a r i = a r j → i = j) :
    Schedule R where
  len := fun _ e => E.width e
  len_pos := fun _ e => E.width_pos e
  widthOf := fun _ r => F.width r
  widthOf_pos := fun _ r => F.width_pos r
  maxWidth := M
  widthOf_le := fun _ r => hM r
  pick := fun _ _ _ k => a (F.roundOf k) (k - F.cum (F.roundOf k))
  keyed := fun _ _ _ r i j hi hj h => by
    have hi' : i < F.width r := hi
    have hj' : j < F.width r := hj
    have h' : a (F.roundOf (F.index r i)) (F.index r i - F.cum (F.roundOf (F.index r i)))
        = a (F.roundOf (F.index r j)) (F.index r j - F.cum (F.roundOf (F.index r j))) := h
    rw [F.roundOf_index hi', F.roundOf_index hj'] at h'
    exact hk r i j hi' hj' (by simpa [Frame.index] using h')
  len_adapted := fun _ _ _ _ => rfl
  widthOf_adapted := fun _ _ _ _ => rfl
  pick_adapted := fun _ _ _ _ _ _ _ => rfl

@[simp] theorem ofFixed_epochFrame (E F : Frame) (M hM a hk) (v : ℕ → Option BlockId) :
    (ofFixed (R := R) E F M hM a hk).epochFrame v = E := rfl

@[simp] theorem ofFixed_frameOf (E F : Frame) (M hM a hk) (v : ℕ → Option BlockId) :
    (ofFixed (R := R) E F M hM a hk).frameOf v = F := rfl

@[simp] theorem ofFixed_len (E F : Frame) (M hM a hk) (v : ℕ → Option BlockId) (e : ℕ) :
    (ofFixed (R := R) E F M hM a hk).len v e = E.width e := rfl

@[simp] theorem ofFixed_widthOf (E F : Frame) (M hM a hk) (v : ℕ → Option BlockId) (r : ℕ) :
    (ofFixed (R := R) E F M hM a hk).widthOf v r = F.width r := rfl

end Schedule

end Adaptive

end LeanDag
