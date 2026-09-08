import LeanDag.FinWhale.View
import Mathlib.Order.Interval.Finset.Nat
import LeanDag.FinWhale.Procedure.Model.Pass
/-!
# FinWhale — the reverse pass, as a procedure

`WellFormed` states what the reverse pass must satisfy; this file
defines the pass (`passFrom`, running the slots downward from the
horizon) and proves it satisfies `WellFormed`. `decOf_eq` is the
equation the five `WellFormed` fields are read off. What this does not
discharge is `hk`, the horizon condition `all_decided` establishes.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type}

variable {D : Dag Validator BlockId Payload} {choose : BlockId → ℕ → Option BlockId} {N : ℕ}
variable {S : Slots Validator}
variable {Elig : ℕ → ℕ → Prop} [DecidableRel Elig]

/-- Above the horizon nothing is decided. -/
theorem passFrom_of_gt {s : ℕ} (h : N < s) :
    passFrom S Elig D choose N s = fun _ => Verdict.undecided := by
  rw [passFrom]
  simp [h]

/-- At or above the slot the pass has reached, the pass is the pass from
that slot. -/
theorem passFrom_of_ge : ∀ k s r : ℕ, N + 1 - s ≤ k → s ≤ r →
    passFrom S Elig D choose N s r = passFrom S Elig D choose N r r := by
  intro k
  induction k with
  | zero =>
    intro s r hk hr
    rw [passFrom, dif_pos (by omega), passFrom, dif_pos (by omega)]
  | succ k ih =>
    intro s r hk hr
    rcases Nat.lt_or_ge N s with h | h
    · rw [passFrom_of_gt h, passFrom_of_gt (by omega)]
    · rcases eq_or_lt_of_le hr with rfl | hlt
      · rfl
      · rw [passFrom, dif_neg (by omega)]
        simp only [if_neg (by omega : ¬ r = s)]
        exact ih (s + 1) r (by omega) (by omega)

omit [LinearOrder BlockId] in
/-- The indirect verdict reads the verdicts above `r + 2` and no others,
so assignments agreeing there give the same answer. -/
theorem anchorVerdict_congr {above above' : ℕ → Verdict BlockId} {r : ℕ}
    (h : ∀ a, Elig r a → a ≤ N → above a = above' a) :
    anchorVerdict Elig choose N above r = anchorVerdict Elig choose N above' r := by
  have hc : anchorCands Elig N above r = anchorCands Elig N above' r := by
    ext a
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Iic]
    constructor
    · rintro ⟨h2, h1, h3⟩
      exact ⟨h2, h1, by rw [← h a h1 h2]; exact h3⟩
    · rintro ⟨h2, h1, h3⟩
      exact ⟨h2, h1, by rw [h a h1 h2]; exact h3⟩
  unfold anchorVerdict
  by_cases hne : (anchorCands Elig N above' r).Nonempty
  · have hne0 : (anchorCands Elig N above r).Nonempty := hc ▸ hne
    rw [dif_pos hne0, dif_pos hne]
    have hmin : (anchorCands Elig N above r).min' hne0 = (anchorCands Elig N above' r).min' hne := by
      congr 1
    rw [hmin]
    have hb : Elig r ((anchorCands Elig N above' r).min' hne) ∧
        (anchorCands Elig N above' r).min' hne ≤ N := by
      have hmem := Finset.min'_mem _ hne
      simp only [anchorCands, Finset.mem_filter, Finset.mem_Iic] at hmem
      exact ⟨hmem.2.1, hmem.1⟩
    rw [h _ hb.1 hb.2]
  · rw [dif_neg (fun hx => hne (hc ▸ hx)), dif_neg hne]

/-- The same, for the whole slot verdict: the direct rules read the DAG,
not the verdicts. -/
theorem slotVerdict_congr {above above' : ℕ → Verdict BlockId} {r : ℕ}
    (h : ∀ a, Elig r a → a ≤ N → above a = above' a) :
    slotVerdict S Elig D choose N above r = slotVerdict S Elig D choose N above' r := by
  unfold slotVerdict
  rw [anchorVerdict_congr h]

/-- **The equation the pass satisfies.** At or below the horizon, a
slot's verdict is `slotVerdict` applied to the pass itself. -/
theorem decOf_eq (hlt : ∀ r a, Elig r a → r < a) {r : ℕ} (hr : r ≤ N) :
    decOf S Elig D choose N r = slotVerdict S Elig D choose N (decOf S Elig D choose N) r := by
  have hself : passFrom S Elig D choose N 0 r = passFrom S Elig D choose N r r :=
    passFrom_of_ge (N + 1) 0 r (by omega) (by omega)
  rw [decOf, hself, passFrom, dif_neg (by omega), if_pos rfl]
  refine slotVerdict_congr fun a h1 h2 => ?_
  have hlt' : r < a := hlt r a h1
  rw [passFrom_of_ge (N + 1) (r + 1) a (by omega) (by omega),
    passFrom_of_ge (N + 1) 0 a (by omega) (by omega)]

/-- Above the horizon the pass decides nothing. -/
theorem decOf_of_gt {r : ℕ} (hr : N < r) : decOf S Elig D choose N r = Verdict.undecided := by
  rw [decOf, passFrom_of_ge (N + 1) 0 r (by omega) (by omega), passFrom_of_gt hr]

/-! ## The pass is well formed -/

variable {D : Dag Validator BlockId Payload}

omit [LinearOrder BlockId] in
/-- A slot with a direct skip lies two rounds below the horizon: the skip
exhibits round-`(r+2)` blocks. -/
theorem round_le_of_directSkip {N r : ℕ} (hN : ∀ b ∈ D.ids, (D.block b).round ≤ N)
    (h : DirectSkip S D r) : S.slotRound r + 2 ≤ N := by
  obtain ⟨-, nonev, hnon, hnonb⟩ := h
  have := params_arith (Validator := Validator)
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  obtain ⟨b, hb, -, -⟩ := hnonb v hv
  simp only [blocksAt, Finset.mem_filter] at hb
  have := hN b hb.1
  omega

/-- **The anchor the pass finds is the anchor.** Where the candidates are
nonempty their least member is the first non-skipped slot above
`r + 2`. -/
theorem anchor_min' {r : ℕ} (hne : (anchorCands Elig N (decOf S Elig D choose N) r).Nonempty) :
    Anchor Elig (decOf S Elig D choose N) r
      ((anchorCands Elig N (decOf S Elig D choose N) r).min' hne) := by
  have hb : Elig r ((anchorCands Elig N (decOf S Elig D choose N) r).min' hne) ∧
      (anchorCands Elig N (decOf S Elig D choose N) r).min' hne ≤ N ∧
      decOf S Elig D choose N ((anchorCands Elig N (decOf S Elig D choose N) r).min' hne)
        ≠ Verdict.skip := by
    have hmem := Finset.min'_mem _ hne
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Iic] at hmem
    exact ⟨hmem.2.1, hmem.1, hmem.2.2⟩
  refine ⟨hb.1, hb.2.2, fun t ht1 ht2 => ?_⟩
  by_contra hskip
  have hmemt : t ∈ anchorCands Elig N (decOf S Elig D choose N) r := by
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨by have := hb.2.1; omega, ht1, hskip⟩
  have hle : (anchorCands Elig N (decOf S Elig D choose N) r).min' hne ≤ t :=
    Finset.min'_le _ t hmemt
  omega

/-- And an anchor below the horizon is that least member. -/
theorem eq_min'_of_anchor {r a : ℕ} (hanc : Anchor Elig (decOf S Elig D choose N) r a)
    (ha : a ≤ N) :
    ∃ hne : (anchorCands Elig N (decOf S Elig D choose N) r).Nonempty,
      (anchorCands Elig N (decOf S Elig D choose N) r).min' hne = a := by
  have hmem : a ∈ anchorCands Elig N (decOf S Elig D choose N) r := by
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨ha, hanc.1, hanc.2.1⟩
  refine ⟨⟨a, hmem⟩, ?_⟩
  have hle := Finset.min'_le _ a hmem
  rcases eq_or_lt_of_le hle with h | h
  · exact h
  · exact absurd (anchor_min' ⟨a, hmem⟩).2.1
      (by rw [hanc.2.2 _ (anchor_min' ⟨a, hmem⟩).1 h]; simp)

/-- An anchor above the horizon means no candidate at all: everything
between is skipped, and nothing above the horizon is decided. -/
theorem anchorCands_eq_empty {r a : ℕ} (hanc : Anchor Elig (decOf S Elig D choose N) r a)
    (ha : N < a) : ¬ (anchorCands Elig N (decOf S Elig D choose N) r).Nonempty := by
  rintro ⟨t, ht⟩
  simp only [anchorCands, Finset.mem_filter, Finset.mem_Iic] at ht
  exact ht.2.2 (hanc.2.2 t ht.2.1 (by omega))

/-- **The reverse pass is well formed.** Its direct rules are the DAG's
own, and `choose` is whatever deterministic rule the validator applies.
`hN` is the horizon: no block of the view sits above it. -/
theorem wellFormed_decOf {N M : ℕ} (hN : ∀ b ∈ D.ids, (D.block b).round ≤ N)
    (hlt : ∀ r a, Elig r a → r < a)
    (hrle : ∀ r, S.slotRound r ≤ N → r ≤ M)
    (choose : BlockId → ℕ → Option BlockId) :
    WellFormed Elig (fun r l => l ∈ slotBlocks S D r ∧ DirectCommit D l)
      (fun r => DirectSkip S D r) choose (decOf S Elig D choose M) where
  direct_commit r l := by
    rintro ⟨hslot, hcom⟩
    have hru : (D.block l).round = S.slotRound r ∧ l ∈ D.ids := by
      simp only [slotBlocks, leaderBlocksAt, blocksAt, Finset.mem_filter] at hslot
      exact ⟨hslot.1.2, hslot.1.1⟩
    have hr : r ≤ M := hrle r (by have := hN l hru.2; omega)
    have hne : (directCommits S D r).Nonempty := ⟨l, Finset.mem_filter.2 ⟨hslot, hcom⟩⟩
    rw [decOf_eq hlt hr, slotVerdict, dif_pos hne]
    have hmem : (directCommits S D r).min' hne ∈ slotBlocks S D r ∧
        DirectCommit D ((directCommits S D r).min' hne) := by
      have h := Finset.min'_mem _ hne
      simp only [directCommits, Finset.mem_filter] at h
      exact h
    rw [direct_commit_unique hmem.1 hslot hmem.2 hcom]
  direct_skip r hskip := by
    have hr : r ≤ M := hrle r (by have := round_le_of_directSkip hN hskip; omega)
    have hne : ¬ (directCommits S D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact no_directSkip_of_commit hl.1 hl.2 hskip
    rw [decOf_eq hlt hr, slotVerdict, dif_neg hne, if_pos hskip]
  indirect_undecided r a hdc hds hanc hau := by
    rcases Nat.lt_or_ge M r with hr | hr
    · exact decOf_of_gt hr
    have hne : ¬ (directCommits S D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact hdc ⟨l, hl.1, hl.2⟩
    rw [decOf_eq hlt hr, slotVerdict, dif_neg hne, if_neg hds, anchorVerdict]
    rcases Nat.lt_or_ge M a with hbig | hsmall
    · rw [dif_neg (anchorCands_eq_empty hanc hbig)]
    · obtain ⟨hc, hmin⟩ := eq_min'_of_anchor hanc hsmall
      rw [dif_pos hc, hmin, hau]
  indirect_commit r a A hdc hds hanc hcom := by
    have ha : a ≤ M := by
      by_contra hbig
      rw [decOf_of_gt (by omega : M < a)] at hcom
      cases hcom
    have hr : r ≤ M := by have := hlt r a hanc.1; omega
    have hne : ¬ (directCommits S D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact hdc ⟨l, hl.1, hl.2⟩
    obtain ⟨hc, hmin⟩ := eq_min'_of_anchor hanc ha
    rw [decOf_eq hlt hr, slotVerdict, dif_neg hne, if_neg hds, anchorVerdict, dif_pos hc, hmin,
      hcom]
    rfl
  has_anchor r hdc hds hdecided := by
    rcases Nat.lt_or_ge M r with hr | hr
    · exact absurd (decOf_of_gt hr) hdecided
    have hne : ¬ (directCommits S D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact hdc ⟨l, hl.1, hl.2⟩
    by_cases hc : (anchorCands Elig M (decOf S Elig D choose M) r).Nonempty
    · exact ⟨_, anchor_min' hc⟩
    · have hund : decOf S Elig D choose M r = Verdict.undecided := by
        rw [decOf_eq hlt hr, slotVerdict, dif_neg hne, if_neg hds, anchorVerdict, dif_neg hc]
      exact absurd hund hdecided

/-! ## What the pass discharges -/

/-- **A committed verdict names a block of its slot.** Either the pass
took a direct commit, which is one, or the tie-break named it, and
`ChooseSound` says what it names is a candidate. -/
theorem mem_slotBlocks_of_decOf {D' : Dag Validator BlockId Payload} {N : ℕ}
    {choose : BlockId → ℕ → Option BlockId}
    (hsub : ∀ r, slotBlocks S D' r ⊆ slotBlocks S D r) (hch : ChooseSound S D choose)
    (hlt : ∀ r a, Elig r a → r < a)
    {r : ℕ} {A : BlockId} (h : decOf S Elig D' choose N r = Verdict.commit A) :
    A ∈ slotBlocks S D r := by
  rcases Nat.lt_or_ge N r with hr | hr
  · rw [decOf_of_gt hr] at h; cases h
  rw [decOf_eq hlt hr, slotVerdict] at h
  by_cases hne : (directCommits S D' r).Nonempty
  · rw [dif_pos hne] at h
    have hmem : (directCommits S D' r).min' hne ∈ slotBlocks S D' r := by
      have hx := Finset.min'_mem _ hne
      simp only [directCommits, Finset.mem_filter] at hx
      exact hx.1
    have : (directCommits S D' r).min' hne = A := by injection h
    exact hsub r (this ▸ hmem)
  · rw [dif_neg hne] at h
    by_cases hskip : DirectSkip S D' r
    · rw [if_pos hskip] at h; cases h
    rw [if_neg hskip, anchorVerdict] at h
    by_cases hc : (anchorCands Elig N (decOf S Elig D' choose N) r).Nonempty
    · rw [dif_pos hc] at h
      rcases hv : decOf S Elig D' choose N ((anchorCands Elig N (decOf S Elig D' choose N) r).min' hc) with A' | - | -
      · rcases hch2 : choose A' r with - | b
        · simp only [hv, hch2] at h
          cases h
        · simp only [hv, hch2] at h
          have hb : b = A := by injection h
          exact hb ▸ (hch.sound A' r b hch2).1
      · simp only [hv] at h
        cases h
      · simp only [hv] at h
        cases h
    · rw [dif_neg hc] at h; cases h

end FinWhale

end LeanDag
