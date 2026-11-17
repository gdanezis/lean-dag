import LeanDagTest.KPartialSparse.Timed
/-!
# Sparse K-partial DAG — a restart witness

The timed witness with `G = 10`, where validator `2` restarts at time `9`: it
then holds only its disk, its own blocks, with the round-`0` blocks below
them, and loses the others' round-`1` blocks. The timeline meets the rules for
nodes and checks claims through the restart, and by Theorem 5 a run resumes
above round `0`, reached by every correct validator by time `25`.
-/

namespace LeanDagTest

namespace KPartialSparse

open LeanDag LeanDag.KPartialSparse
open LeanDag.KPartialDag (Timeline)
open scoped LeanDag.KPartialDag

/-- Validator `2` holds only its disk and the blocks below it at time `9`. -/
def rHeld (v : Fin 4) (t : ℕ) : Finset ℕ := if v = 2 ∧ t = 9 then upto 0 ∪ tDisk 2 9 else tHeld v t

/-- The timeline with the restart. -/
def rTl : Timeline (Fin 4) ℕ := ⟨rHeld, tDisk, tBuilt⟩

theorem rHeld_eq {v : Fin 4} {t : ℕ} (h : ¬ (v = 2 ∧ t = 9)) : rTl.held v t = tTl.held v t :=
  if_neg h

theorem rHeld_restart : rTl.held 2 9 = upto 0 ∪ tDisk 2 9 := by
  change rHeld 2 9 = _
  unfold rHeld; simp

/-- What validator `2` holds after the restart: blocks of rounds `0` and `1`,
built by time `7`. -/
theorem restart_mem {b : ℕ} (hb : b ∈ upto 0 ∪ tDisk 2 9) :
    b ∈ wIds ∧ b / 4 ≤ 1 ∧ tBuilt b ≤ 7 ∧ (b / 4 = 1 → (wBlock b).creator = 2) := by
  rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨hb, hbr⟩ := Finset.mem_filter.mp hb
    refine ⟨hb, by omega, by unfold tBuilt; omega, fun h => by omega⟩
  · obtain ⟨hb, hbc, hbt⟩ := Finset.mem_filter.mp hb
    unfold tBuilt at hbt
    exact ⟨hb, by omega, by unfold tBuilt; omega, fun _ => hbc⟩

/-- No build time and no build time less `γ` is `9`. -/
theorem built_ne (b : ℕ) : tBuilt b ≠ 9 ∧ tBuilt b - 2 ≠ 9 := by unfold tBuilt; omega

theorem rb9 (b : ℕ) : ¬ ((wU.block b).creator = 2 ∧ rTl.built b = 9) := fun h => (built_ne b).1 h.2

theorem rb9' (b : ℕ) : ¬ ((wU.block b).creator = 2 ∧ rTl.built b - 2 = 9) :=
  fun h => (built_ne b).2 h.2

theorem rRules : TimedRules (S := wSlots) wU rTl wT 10 1 4 2 0 6 where
  stable := (wRules 10).stable
  large := (wRules 10).large
  held_ids := by
    intro v t
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart]; exact fun b hb => (restart_mem hb).1
    · rw [rHeld_eq hvt]; exact (wRules 10).held_ids v t
  mono := by
    intro v hv t t' hG htt'
    rw [rHeld_eq (by omega), rHeld_eq (by omega)]; exact (wRules 10).mono v hv t t' hG htt'
  delivers := by
    intro v hv t hG b hb hbc w hw
    rw [rHeld_eq (by omega)] at hb; rw [rHeld_eq (by omega)]
    exact (wRules 10).delivers v hv t hG b hb hbc w hw
  closed := by
    intro v hv t b hb hbc
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb ⊢
      obtain ⟨hbi, hbr, -, -⟩ := restart_mem hb
      intro j hj
      have hlt := (wU.valid b hbi).below j hj
      change (wBlock j).round < (wBlock b).round at hlt
      rw [round_wBlock, round_wBlock] at hlt
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨wU.complete b hbi j hj, by omega⟩)
    · rw [rHeld_eq hvt] at hb ⊢; exact (wRules 10).closed v hv t b hb hbc
  grounded := by
    intro v hv t b hb hbc hR
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb ⊢
      obtain ⟨hbi, hbr, -, -⟩ := restart_mem hb
      change 0 < (wBlock b).round at hR
      change QuorumIn wU (upto 0 ∪ tDisk 2 9) ((wBlock b).round - 1)
      rw [round_wBlock] at hR ⊢
      rw [show b / 4 - 1 = 0 by omega]
      exact quorumIn_mono Finset.subset_union_left (waitsFor_upto 0 (by omega)).1
    · rw [rHeld_eq hvt] at hb ⊢; exact (wRules 10).grounded v hv t b hb hbc hR
  backed := by
    intro v hv t b hb hbc L hL
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb
      obtain ⟨hbi, hbr, -, -⟩ := restart_mem hb
      rw [claims_low b hbi (by omega)] at hL; simp at hL
    · rw [rHeld_eq hvt] at hb ⊢; exact (wRules 10).backed v hv t b hb hbc L hL
  causal := by
    intro v hv t b hb hbc
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb
      have := (restart_mem hb).2.2.1
      change tBuilt b ≤ 9; omega
    · rw [rHeld_eq hvt] at hb; exact (wRules 10).causal v hv t b hb hbc
  prior := by
    intro v hv t b hb hbc hbv
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb
      have := (restart_mem hb).2.2.1
      change tBuilt b < 9; omega
    · rw [rHeld_eq hvt] at hb; exact (wRules 10).prior v hv t b hb hbc hbv
  disk_held := by
    intro v hv t
    by_cases hvt : v = 2 ∧ t = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart]; exact Finset.subset_union_right
    · rw [rHeld_eq hvt]; exact (wRules 10).disk_held v hv t
  stores := (wRules 10).stores
  waits := by
    intro b hb hbc r hbr hR
    rw [rHeld_eq (rb9' b), rHeld_eq (rb9 b)]
    change (wBlock b).round = r + 1 at hbr
    rw [round_wBlock] at hbr
    have h6 := round_le_six hb
    have hW := waitsFor_upto r (by omega)
    refine Or.inl ⟨by change 2 ≤ tBuilt b; unfold tBuilt; omega,
      waitsFor_mono (upto_subset (by change 4 + 3 * r + 1 ≤ tBuilt b - 2; unfold tBuilt; omega)) hW,
      waitsFor_mono (upto_subset (by change 4 + 3 * r + 1 ≤ tBuilt b; unfold tBuilt; omega)) hW⟩
  prompt := by
    intro v hv r t hr hrN hw
    refine (wRules 10).prompt v hv r t hr hrN ?_
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by rw [rHeld_eq (by omega)] at h2; exact h2⟩
    · exact Or.inr (Or.inl ⟨h1, by rw [rHeld_eq (by omega)] at h2; exact h2⟩)
    · exact Or.inr (Or.inr ⟨h1, by rw [rHeld_eq (by omega)] at h2; exact h2⟩)
  votes := by
    intro b hb hbc k hk hkr hL
    rw [rHeld_eq (rb9 b)] at hL; exact (wRules 10).votes b hb hbc k hk hkr hL
  covers := by
    intro b hb hbc hbl x hx hxc hxr
    rw [rHeld_eq (rb9 b)] at hx; exact (wRules 10).covers b hb hbc hbl x hx hxc hxr
  self_ref := (wRules 10).self_ref
  claims := by
    intro b hb hbc k hk L hL hc
    rw [rHeld_eq (rb9 b)] at hc; exact (wRules 10).claims b hb hbc k hk L hL hc

/-- The restarted timeline checks claims at `K = 6` and threshold `3`. -/
theorem rChecked : TimedChecks wU rTl 6 3 := by
  refine ⟨fun b hb hbc m hm => ?_, fun b hb hbc L hL => ?_, fun v hv s b hb hbc m hm => ?_,
    fun v hv s b hb hbc L hL => ?_⟩
  · rw [rHeld_eq (rb9 b)]; exact wChecked.refs_checked b hb hbc m hm
  · rw [rHeld_eq (rb9 b)]; exact wChecked.claims_backed b hb hbc L hL
  · by_cases hvt : v = 2 ∧ s = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb ⊢
      obtain ⟨hbi, hbr, -, -⟩ := restart_mem hb
      have hlt := (wU.valid b hbi).below m hm
      change (wBlock m).round < (wBlock b).round at hlt
      rw [round_wBlock, round_wBlock] at hlt
      obtain ⟨h1, h2⟩ := referenceable_upto (wU.complete b hbi m hm) (r := 0) (by omega)
      exact ⟨h1.trans Finset.subset_union_left,
        fun X hX L hL => backs_mono Finset.subset_union_left (h2 X hX L hL)⟩
    · rw [rHeld_eq hvt] at hb ⊢; exact wChecked.carries v hv s b hb hbc m hm
  · by_cases hvt : v = 2 ∧ s = 9
    · obtain ⟨rfl, rfl⟩ := hvt
      rw [rHeld_restart] at hb
      obtain ⟨hbi, hbr, -, -⟩ := restart_mem hb
      rw [claims_low b hbi (by omega)] at hL; simp at hL
    · rw [rHeld_eq hvt] at hb ⊢; exact wChecked.carries_claims v hv s b hb hbc L hL

/-- **Theorem 5, resuming after a restart**: with `G = 10` and validator `2`
restarting at time `9`, validator `0` has built round `2` by `G`, so a timed run
starts above round `0`, which every correct validator reaches by time `25`. -/
theorem rResumes : ∃ R', 0 < R' ∧ (R' ≤ 6 → TimedRun (S := wSlots) wU rTl wT 10 1 4 2 R' 6 ∧
    ReachedBy wU rTl wT R' 25) :=
  Reactive.resumes (Fin 4) ℕ (Finset ℕ) wU rTl wT 10 1 4 2 0 6 rRules (bid 2 0)
    (by decide) (by decide) (by change tBuilt (bid 2 0) ≤ 10; unfold tBuilt; rw [bid_div]) (by
      change 0 < (wBlock (bid 2 0)).round
      rw [round_wBlock, bid_div]; omega)

/-- **The restart keeps the claim disciplines**. -/
theorem rDisciplines : Checks wU 6 3 ∧ Truthful wU 3 :=
  Reactive.checked (Fin 4) ℕ (Finset ℕ) wU rTl 6 3 rRules.held_ids rChecked

/-- From `G = 10` on, the restarted timeline fetches as the timed one. -/
theorem rFetches : Fetches (S := wSlots) wU rTl wT 6 10 1 := by
  intro v hv t hG j A hA hAH z hz
  rw [rHeld_eq (by omega)] at hAH ⊢
  exact wFetches v hv t (Nat.zero_le _) j A hA hAH z hz

/-- **Theorem 5, recovering**: after validator `2` restarts at time `9`, past
any slot, every correct validator decides every slot below the end of a run of
slots led by them, once the record reaches its last certificates. -/
theorem rRecovers (k : ℕ) : ∃ b, k ≤ b ∧ (certRound (Scheme.Params.mysticeti 4 1)
    (wSlots.slotRound (b + 3 - 1)) ≤ 6 → ∃ t, ∀ v ∈ wT, ∃ g : ℕ → Option ℕ, ∀ i, i < b + 3 →
      NodeDecided (S := wSlots) (Scheme.Params.mysticeti 4 1) wU 6 (rTl.held v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn wU 6 (rTl.held v t) L ((wU.block L).round - 1)) :=
  Reactive.recovers (Fin 4) ℕ (Finset ℕ) (Scheme.Params.mysticeti 4 1) wU rTl wT 10 1 4 2 0 6 6 1
    1 3 wRow.1 (fun h => absurd h (by decide)) wDisciplined wLive rRules (by omega) (by omega)
    (by omega) rFetches (by omega) (fun b i hi => by change i + (3 - 1) < b + 3 - 1; omega)
    (fun k => ⟨k, le_rfl, fun _ _ => lead_mem _⟩) (bid 2 0) (by decide) (by decide)
    (by change tBuilt (bid 2 0) ≤ 10; unfold tBuilt; rw [bid_div])
    (by change 0 < (wBlock (bid 2 0)).round; rw [round_wBlock, bid_div]; omega) k

end KPartialSparse

end LeanDagTest
