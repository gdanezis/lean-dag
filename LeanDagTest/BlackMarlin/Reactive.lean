import LeanDagTest.BlackMarlin.Liveness
import LeanDagTest.Reactive.Model
import LeanDag.BlackMarlin.Reactive.Proof
/-!
# Black Marlin witnesses — the reactive schedule on data

`black-marlin.md` §10. Two witnesses, because the round rule and the
pacing structure are answerable to different questions.

`ConcludesAt` and its three clauses are settled by `decide` on `Ufull`,
the covered four-round model of the liveness witness: round `3` may be
concluded there — a quorum, the round-3 anchor, and the anchors of
rounds `2` and `1` both supported — and round `4` may not, the DAG
having stopped.

The pacing structure is witnessed on `Ugrow`, the growing model the
core's reactive arc uses, with the same holdings and the same build
spacing of `6`. Two constants differ. Processing is `7` rather than `5`,
because Black Marlin's exit is bounded by the round rule rather than by
holding one block. The timeout is `25` rather than `9`, which is what
makes both routes fire on one model: the fallback needs
`2Δ + proc ≤ timeout` and the fast path needs `Δ + δ + 2 · proc` under
it, and at `Δ = 2`, `δ = 2` those read `11 ≤ 25` and `18 < 25`.
-/

namespace LeanDagTest

namespace BlackMarlin

open LeanDag LeanDag.BlackMarlin

/-- The rotation of BML5 at four validators, as in the liveness witness. -/
local instance bmRR' : Rotation (Fin 4) := Liveness.roundRobin 4 (by omega)

/-! ## The round rule on `Ufull` -/

/-- Round `3` may be concluded: a quorum of authors, the round-3 anchor,
and the anchors of rounds `2` and `1` both carrying a quorum of
support. -/
example : ConcludesAt Ufull (View.full Ufull) 3 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro ρ hρ
    have h : ρ = 2 := by omega
    subst h
    decide
  · intro ρ hρ
    have h : ρ = 1 := by omega
    subst h
    decide

/-- Each clause separately, so the conjunction above is not carried by
one of them. -/
example : QuorumIn Ufull (View.full Ufull) 3 ∧ AnchorIn Ufull (View.full Ufull) 3 ∧
    SuppAnchorIn Ufull (View.full Ufull) 2 ∧
    SuppAnchorIn Ufull (View.full Ufull) 1 := by decide

/-- Anti-vacuity: round `4` may not be concluded — the DAG stops at
round `3`, so the quorum clause already fails. -/
example : ¬ QuorumIn Ufull (View.full Ufull) 4 := by decide

/-- And round `0` has no supported anchor beneath it to check, which the
additive form of the two lower clauses makes vacuous rather than a
separate case. -/
example : ∀ ρ, ρ + 1 = 0 → SuppAnchorIn Ufull (View.full Ufull) ρ := by omega

/-! ## The pacing structure on `Ugrow`

The core's reactive witness with two constants changed. Every field but
the last two is that witness's, unchanged. -/

/-- Black Marlin's pace on `Ugrow`: builds at spacing `6`, processing
`7`, timeout `25`, `Δ = 2`, GST at `0`. -/
def ugrowBM (N : ℕ) : Pace (Ugrow N) {1, 2, 3} N where
  top _ := N
  built v n := (v : ℕ) + 6 * n
  timeout _ := 25
  proc := 7
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  timeout_pos _ := by omega
  latest n := 3 + 6 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  built_lt _ _ _ _ := by omega
  deadline _ _ _ _ := by omega
  refs_held v hv n b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    intro j hj
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [ugrow_block, mem_growBlock_refs] at hj
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inl (by omega)⟩
  holds := reactHolds N
  holds_sub _ _ := by
    simp only [reactHolds, ugrow_ids]; exact Finset.filter_subset _ _
  holds_closed v hv t b hb j hj := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [ugrow_block, mem_growBlock_refs] at hj
    have hjd : j / 4 + 1 = b / 4 := by omega
    refine ⟨by omega, Or.inl ?_⟩
    rcases hb.2 with h | ⟨_, h⟩ <;> omega
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [ugrow_block] using this
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hb4, by omega⟩⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h
    · omega
    · omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t _ hheld := by
    have hv4 := v.isLt
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hheld
    refine ⟨hn, ?_⟩
    rcases hheld.2 with h | ⟨_, h⟩ <;> omega
  anchor_or_wait v hv r _ _ A hA c hc hcc hcr := by
    -- the exit is always available here: every block references the whole
    -- round below, the anchor among it
    left
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    obtain ⟨hmem, hround, -⟩ := hA
    simp only [ugrow_ids, Finset.mem_range] at hmem hc
    simp only [ugrow_block, rrBlock_round] at hround hcr
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  prompt_conclude v _ r _ t hbuilt _ := by
    have hv4 := v.isLt
    change (v : ℕ) + 6 * r ≤ t at hbuilt
    change (v : ℕ) + 6 * (r + 1) ≤ t + 7
    omega

/-! ## The results, on the pace

Rounds `1`, `2`, `3` are anchored by validators `1`, `2`, `3`, all
reliable — the run of three the exit needs, which round robin at four
validators supplies once per cycle. -/

/-- **BMR2 on data**: the run of two at rounds `1` and `2` is committed,
with no coverage hypothesis and no drift hypothesis. -/
example (N : ℕ) (hN : 3 ≤ N) :
    ∃ L, IsAnchor (Ugrow N) 1 L ∧ Committed (Ugrow N) L 1 :=
  (Reactive.holds (Fin 4) ℕ Unit (Ugrow N) {1, 2, 3} N (ugrowBM N)).2.1 0 1
    (by decide) (by decide) (le_refl 0)
    (fun n _ => by change 2 * 2 + 7 ≤ 25; omega)
    (Nat.zero_le _) (by omega) (by decide) (by decide)

/-- **BMR5 on data**: past GST, round `4` is entered within
`Δ + δ + 2 · proc = 18` of round `3` — the run takes `6`. -/
example (N : ℕ) (hN : 5 ≤ N) (v : Fin 4) (hv : v ∈ ({1, 2, 3} : Finset (Fin 4))) :
    (ugrowBM N).built v 4 ≤ (ugrowBM N).built v 3 + 2 + 2 + 2 * 7 :=
  ((Reactive.holds (Fin 4) ℕ Unit (Ugrow N) {1, 2, 3} N (ugrowBM N)).2.2.2.2.1
      1 v 2 0 0 (by decide) hv (by omega)
      (fun n hn1 hn2 b hb hbT hbr => by
        obtain ⟨h1, h3⟩ := mem_T_bounds hv
        simp only [ugrow_ids, Finset.mem_range] at hb
        simp only [ugrow_block, rrBlock_round] at hbr
        change b ∈ reactHolds N v (b % 4 + 6 * n + 2)
        simp only [reactHolds, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, Or.inl (by omega)⟩)
      (by decide) (by decide) (by decide)
      (fun n hn1 hn2 A hA u hu c hc hcc hcr => by
        obtain ⟨h1, h3⟩ := mem_T_bounds hu
        obtain ⟨hmem, hround, -⟩ := hA
        simp only [ugrow_ids, Finset.mem_range] at hmem hc
        simp only [ugrow_block, rrBlock_round] at hround hcr
        simp only [ugrow_block, mem_growBlock_refs]
        omega)).2 (le_refl 0) (by omega)

#print axioms LeanDag.BlackMarlin.Reactive.holds

end BlackMarlin

end LeanDagTest
