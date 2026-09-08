import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.Properties.Agreement
import LeanDag.Properties.Band
/-!
# Transport composes

`docs/target-properties.md` §11.3. A mechanism owes a rebase
(`Properties/Carrier.lean`), and a validator running two mechanisms has
applied two — the claim here is that two rebases are one. Offsets add;
the settling round of the composite is the higher of the two, read in
the source's frame, so the second mechanism's round has the first's
offset added before the comparison. `Arcs/Stack.lean` composes a
`Stack` of mechanisms into one `Rebased` with these lemmas, which every
verdict then crosses at once.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

namespace RebasedAbove

/-- **Two rebases are one.** The offsets add. The settling round is the
later of the two in `U`'s frame: `R₂` is a round of `U'`, so it is
compared against `R₁` only after `G₁` is added back. -/
theorem trans {U U' U'' : R.Universe} {G₁ R₁ G₂ R₂ : ℕ}
    (h : RebasedAbove R U U' G₁ R₁) (h' : RebasedAbove R U' U'' G₂ R₂) :
    RebasedAbove R U U'' (G₁ + G₂) (max R₁ (R₂ + G₁)) where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      have h1 := (h.mem b).mp ⟨hb, le_trans (le_max_left _ _) hr⟩
      have hro := h.round b hb (le_trans (le_max_left _ _) hr)
      have h2 := (h'.mem b).mp ⟨h1.1, by have := le_max_right R₁ (R₂ + G₁); omega⟩
      have hro' := h'.round b h1.1 (by omega)
      exact ⟨h2.1, by omega⟩
    · rintro ⟨hb, hr⟩
      have h2 := (h'.mem b).mpr ⟨hb, by omega⟩
      have hro' := h'.round b h2.1 h2.2
      have h1 := (h.mem b).mpr ⟨h2.1, by omega⟩
      exact ⟨h1.1, by have := h.round b h1.1 h1.2; omega⟩
  round := fun b hb hr => by
    have h1 := (h.mem b).mp ⟨hb, le_trans (le_max_left _ _) hr⟩
    have hro := h.round b hb (le_trans (le_max_left _ _) hr)
    have hro' := h'.round b h1.1 (by have := le_max_right R₁ (R₂ + G₁); omega)
    omega
  creator := fun b hb hr => by
    have h1 := (h.mem b).mp ⟨hb, le_trans (le_max_left _ _) hr⟩
    have hro := h.round b hb (le_trans (le_max_left _ _) hr)
    rw [h'.creator b h1.1 (by have := le_max_right R₁ (R₂ + G₁); omega)]
    exact h.creator b hb (le_trans (le_max_left _ _) hr)
  refs := fun b hb hr => by
    have h1 := (h.mem b).mp ⟨hb, le_of_lt (lt_of_le_of_lt (le_max_left _ _) hr)⟩
    have hro := h.round b hb (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hr))
    rw [h'.refs b h1.1 (by have := le_max_right R₁ (R₂ + G₁); omega)]
    exact h.refs b hb (lt_of_le_of_lt (le_max_left _ _) hr)

/-- A mechanism that rebases from a round rebases from any later one,
which is what lets two settling rounds be compared at all. -/
theorem mono {U U' : R.Universe} {G R₀ R₁ : ℕ}
    (h : RebasedAbove R U U' G R₀) (hR : R₀ ≤ R₁) : RebasedAbove R U U' G R₁ where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      have hm := (h.mem b).mp ⟨hb, le_trans hR hr⟩
      exact ⟨hm.1, by have := h.round b hb (le_trans hR hr); omega⟩
    · rintro ⟨hb, hr⟩
      have hm := (h.mem b).mpr ⟨hb, le_trans hR hr⟩
      exact ⟨hm.1, by have := h.round b hm.1 hm.2; omega⟩
  round := fun b hb hr => h.round b hb (le_trans hR hr)
  creator := fun b hb hr => h.creator b hb (le_trans hR hr)
  refs := fun b hb hr => h.refs b hb (lt_of_le_of_lt hR hr)

/-- Doing nothing rebases by nothing, from round zero. -/
theorem refl {U : R.Universe} : RebasedAbove R U U 0 0 where
  mem := fun _ => by simp
  round := fun _ _ _ => rfl
  creator := fun _ _ _ => rfl
  refs := fun _ _ _ => rfl

end RebasedAbove

namespace Rebases

variable {S S' S'' : Slots Validator} {G₁ d₁ G₂ d₂ : ℕ}

/-- **And two schedule rebases are one.** Offsets and base slots both
add, which is what makes a stack of truncations a truncation. -/
theorem trans (h : Rebases S S' G₁ d₁) (h' : Rebases S' S'' G₂ d₂) :
    Rebases S S'' (G₁ + G₂) (d₁ + d₂) where
  slotRound := fun k => by
    have h1 := h.slotRound (d₂ + k)
    have h2 := h'.slotRound k
    have e : d₁ + (d₂ + k) = d₁ + d₂ + k := by omega
    rw [e] at h1; omega
  leader := fun k => by
    have e : d₁ + (d₂ + k) = d₁ + d₂ + k := by omega
    rw [h'.leader k, h.leader (d₂ + k), e]
  base := by
    have h1 := h.slotRound d₂
    have h2 := h'.base
    omega

/-- **A rebase determines the schedule it produces**: two schedules
rebased alike from one original are the same schedule. What this is
for: `Integration/Joiner.lean` compares truncating an adaptive schedule
with adapting a truncated one, both rebases by the same offset, and
this settles it with no unfolding. -/
theorem unique {S S₁ S₂ : Slots Validator} {G d : ℕ}
    (h₁ : Rebases S S₁ G d) (h₂ : Rebases S S₂ G d) : S₁ = S₂ := by
  have hr : S₁.slotRound = S₂.slotRound := by
    funext k
    have a := h₁.slotRound k
    have b := h₂.slotRound k
    omega
  have hl : S₁.leader = S₂.leader := by
    funext k; rw [h₁.leader k, h₂.leader k]
  cases S₁; cases S₂; congr

end Rebases

/-- **A stack of truncations is a truncation.** Both halves compose, and
the settling round of the composite is `G₁ + G₂` because a cut settles at
its own horizon. -/
theorem Truncates.trans {U U' U'' : R.Universe} {S S' S'' : Slots Validator}
    {G₁ d₁ G₂ d₂ : ℕ} (h : Truncates R U U' S S' G₁ d₁)
    (h' : Truncates R U' U'' S' S'' G₂ d₂) :
    Truncates R U U'' S S'' (G₁ + G₂) (d₁ + d₂) :=
  { (h.toRebasedAbove.trans h'.toRebasedAbove).mono
      (by omega : max G₁ (G₂ + G₁) ≤ G₁ + G₂),
    h.toRebases.trans h'.toRebases with }


/-! ## One relation per mechanism, and safety across it -/

/-- **What one mechanism delivers, universe and schedule together.** -/
structure Rebased (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (S S' : Slots Validator) (G R₀ d : ℕ) : Prop
    extends RebasedAbove R U U' G R₀, Rebases S S' G d

/-- The schedule is a rebase of itself. -/
theorem Rebases.refl {S : Slots Validator} : Rebases S S 0 0 where
  slotRound := fun k => by simp
  leader := fun k => by simp
  base := Nat.zero_le _

namespace Rebased

variable {U U' U'' : R.Universe} {S S' S'' : Slots Validator}

/-- A cut is a rebase at its horizon. -/
theorem of_truncates {G d : ℕ} (h : Truncates R U U' S S' G d) : Rebased R U U' S S' G G d :=
  { h.toRebasedAbove, h.toRebases with }

/-- A fill or a re-genesis is a rebase at no offset, on the same schedule. -/
theorem of_sustains {R₀ : ℕ} (h : Sustains R U U' 0 R₀) : Rebased R U U' S S 0 R₀ 0 :=
  { h, Rebases.refl with }

/-- Doing nothing is a rebase. -/
theorem refl : Rebased R U U S S 0 0 0 := { RebasedAbove.refl, Rebases.refl with }

/-- **Two rebases are one.** -/
theorem trans {G₁ R₁ d₁ G₂ R₂ d₂ : ℕ} (h : Rebased R U U' S S' G₁ R₁ d₁)
    (h' : Rebased R U' U'' S' S'' G₂ R₂ d₂) :
    Rebased R U U'' S S'' (G₁ + G₂) (max R₁ (R₂ + G₁)) (d₁ + d₂) :=
  { h.toRebasedAbove.trans h'.toRebasedAbove, h.toRebases.trans h'.toRebases with }

end Rebased

/-! ## Safety across a rebase

`LocalTruncate.of_banded` is this at a cut, where the settling round is
the horizon; a fill settles higher than it shifts, so the general form
carries the settling round separately. -/

variable {U U' : R.Universe} {S S' : Slots Validator} {G R₀ d : ℕ}

/-- **A verdict above the settling round transports across any rebase**,
to the rebased numbering, on views that agree above the settling round.
An `↔`, as `LocalTruncate` is. -/
theorem decided_of_rebased (h : Banded R) (hr : Rebased R U U' S S' G R₀ d)
    {V : R.View U} {V' : R.View U'} (hv : ViewAgreeAbove R V V' R₀)
    (k : ℕ) (hk : R₀ ≤ S.slotRound (d + k)) (v : Option BlockId) :
    R.Decided S V (d + k) v ↔ R.Decided S' V' k v := by
  have hsk := hr.slotRound k
  constructor
  · intro hdec
    obtain ⟨top, htop⟩ := h S U V (d + k) v hdec
    refine htop 0 G d 0 S' U' V' k (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m = m' + d := by omega
      subst hmm
      have := hr.slotRound m'
      have hc : d + m' = m' + d := by omega
      rw [hc] at this
      omega
    · intro m m' hm _
      have hmm : m = m' + d := by omega
      subst hmm
      have hc : m' + d = d + m' := by omega
      rw [hc]
      exact (hr.leader m').symm
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact ((hr.mem b).mp ⟨hb, by omega⟩).1
      · intro b hb hband
        have hR : R₀ ≤ (R.block U b).round := by
          rcases hband with ⟨h1, _⟩ | ⟨hm, h1, _⟩
          · omega
          · have := (hr.of_mem' hm (by omega)).2; omega
        exact ⟨by have := hr.round b hb hR; omega, hr.creator b hb hR⟩
      · intro b hb h1 h2
        exact hr.refs b hb (by omega)
    · intro b hbV h1 h2
      exact (hv b (R.viewSound V hbV) (by omega)).mp hbV
  · intro hdec
    obtain ⟨top, htop⟩ := h S' U' V' k v hdec
    refine htop G 0 0 d S U V (d + k) (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m' = m + d := by omega
      subst hmm
      have := hr.slotRound m
      have hc : d + m = m + d := by omega
      rw [hc] at this
      omega
    · intro m m' hm _
      have hmm : m' = m + d := by omega
      subst hmm
      have hc : m + d = d + m := by omega
      rw [hc]
      exact hr.leader m
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact (hr.of_mem' hb (by omega)).1
      · intro b hb hband
        have hR : R₀ ≤ (R.block U' b).round + G := by
          rcases hband with ⟨h1, _⟩ | ⟨hm, h1, _⟩
          · omega
          · have := hr.round b hm (by omega); omega
        obtain ⟨hbU, hround⟩ := hr.of_mem' hb hR
        exact ⟨by omega, (hr.creator b hbU (by omega)).symm⟩
      · intro b hb h1 h2
        obtain ⟨hbU, hround⟩ := hr.of_mem' hb (by omega)
        exact (hr.refs b hbU (by omega)).symm
    · intro b hbV h1 h2
      have hbU' : b ∈ R.ids U' := R.viewSound V' hbV
      obtain ⟨hbU, hround⟩ := hr.of_mem' hbU' (by omega)
      exact (hv b hbU (by omega)).mpr hbV

/-- **Cross-rebase agreement**, from any view of the rebased universe. -/
theorem decided_agree_rebased (ha : Agree R) (hb : Banded R)
    (hr : Rebased R U U' S S' G R₀ d) {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' R₀) {W : R.View U'} {k : ℕ} (hk : R₀ ≤ S.slotRound (d + k))
    {w v : Option BlockId} (hW : R.Decided S' W k w) (hV : R.Decided S V (d + k) v) : w = v :=
  ha S' W V' k w v hW ((decided_of_rebased hb hr hv k hk v).mp hV)

end Properties

end LeanDag
