import LeanDagTest.Barnacle.Progress
import LeanDag.Barnacle.Heads.Proof
import LeanDagTest.Barnacle.Rules.MysticetiLive.Proof
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
/-!
# Barnacle witnesses — the heads descent on data

* **Runs of heads.** Round-robin on four validators with `T = {1, 2, 3}`
  has three consecutive `T`-led heads within six rounds of any round —
  directly (`ρ := r + (5 − r % 4) % 4`) and through BN9d; six is tight
  (`r = 2` needs `ρ = 5`). `T = {1, 2}` has no run of three at *any*
  gap: the pigeonhole's committee bound `3 · 2 + 1 ≤ 4` fails, and so
  does the run. The same for the good set `{0, 1, 3}` the descent below
  uses, whose only run is `ρ ≡ 3 (mod 4)`.
* **Mysticeti's own `Good` on data.** `mysticetiLive.Good Usun 1 7`: the
  correct quorum `{1, 2, 3}` synchronised from round `1` and populating
  rounds `1` to `7`; synchrony is an unbounded `∀ n`, bounded by the top
  round and then decided. The real descent law at this committee gives
  a committed slot on `Usun` through `MysticetiLive.holds`.
* **The descent producing a skip.** `bnLiveSk` — Mysticeti with `Good`
  pinning `Usk`, `Rnd = 1`, `N = 8` — has the descent laws at slack `1`
  for the good set `T = {0, 1, 3}`: every validator but `2`, the author
  of the under-referenced block. This `T` contains the Byzantine
  validator `0`, legitimately: L4 and `goodLeaders` bound the good set
  by cardinality, not by correctness — `slack` counts missing
  validators, not faults. Real Mysticeti never calls `Usk` good from
  round `1` at any horizon (`Correct = {1, 2, 3}` is not synchronised
  there), which is what the test rule's `Good` adds and what puts the
  skip within eight rounds. The heads of rounds `3, 4, 5` are validators
  `3, 0, 1`, all in `T`, so BN9b at `ρ = 3` decides every slot at rounds
  `0` to `2` — verdicts `some 0`, `some 5` and, for the skipped slot,
  `none`, each identified by `agree` — and commits the head of `3`; the
  application sits on the horizon exactly, `ρ = 4` does not fit. BN9a on
  the stretch `[3, 5]` decides the same three slots, slot `0` through
  the least committed anchor a wave above it.
* **The paper's A4 on data.** `MysticetiLive.holds` — Mysticeti under
  round-robin at count `2`, gap `6` — applied to `U44`, eleven sunny
  rounds on four validators, with the real `Good` to horizon `10`: the
  theorem yields a committed slot within rounds `1` to `7` and a verdict
  for slot `2`. At eight rounds the gap-`6` clauses are empty.
-/

namespace LeanDagTest

namespace Barnacle

open LeanDag LeanDag.Barnacle

/-! ## Runs of heads, on four validators -/

theorem rr_headsRun_data : HeadsRun (roundRobin 4 (by omega)) {1, 2, 3} 3 6 := by
  intro r
  refine ⟨r + (5 - r % 4) % 4, by omega, by omega, ?_⟩
  intro i hi
  have : r % 4 < 4 := Nat.mod_lt _ (by omega)
  simp only [roundRobin, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

-- Tightness: `c₀ = 5` fails at `r = 2`.
example : ¬ HeadsRun (roundRobin 4 (by omega)) {1, 2, 3} 3 5 := by
  intro h
  obtain ⟨ρ, h1, h2, h3⟩ := h 2
  have : ρ = 2 ∨ ρ = 3 ∨ ρ = 4 := by omega
  rcases this with rfl | rfl | rfl
  · exact absurd (h3 2 (by omega)) (by decide)
  · exact absurd (h3 1 (by omega)) (by decide)
  · exact absurd (h3 0 (by omega)) (by decide)

-- The pigeonhole hypothesis is needed: `T = {1, 2}` has no three consecutive residues.
example (c₀ : ℕ) : ¬ HeadsRun (roundRobin 4 (by omega)) {1, 2} 3 c₀ := by
  intro h
  obtain ⟨ρ, -, -, h3⟩ := h 0
  have hi : ∀ i, i < 3 → (ρ + i) % 4 = 1 ∨ (ρ + i) % 4 = 2 := by
    intro i hi
    have := h3 i hi
    simp only [roundRobin, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at this
    omega
  have := hi 0 (by omega); have := hi 1 (by omega); have := hi 2 (by omega)
  omega

-- Through BN9d.
example : HeadsRun (roundRobin 4 (by omega)) {1, 2, 3} 3 6 :=
  Heads.holds.2.1 4 (by omega) {1, 2, 3} 1 3 (by decide) (by decide)

-- The good set of the descent below, `{0, 1, 3}`: its only run is
-- `ρ ≡ 3 (mod 4)`, so six is tight there too (`r = 0` needs `ρ = 3`).
example : HeadsRun (roundRobin 4 (by omega)) {0, 1, 3} 3 6 :=
  Heads.holds.2.1 4 (by omega) {0, 1, 3} 1 3 (by decide) (by decide)
example : ¬ HeadsRun (roundRobin 4 (by omega)) {0, 1, 3} 3 5 := by
  intro h
  obtain ⟨ρ, h1, h2, h3⟩ := h 0
  have : ρ = 0 ∨ ρ = 1 ∨ ρ = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact absurd (h3 2 (by omega)) (by decide)
  · exact absurd (h3 1 (by omega)) (by decide)
  · exact absurd (h3 0 (by omega)) (by decide)

/-! ## Mysticeti's `Good` on `Usun` -/

/-- The correct validators of the four-validator committee. -/
theorem bnCorrect : (Correct : Finset (Fin 4)) = {1, 2, 3} := by decide

/-- `Usun` is synchronised over `{1, 2, 3}` from round `1`: every block
of round `n + 1` references every block of round `n`. Bounded by the top
round, then decided. -/
theorem usun_sync : SynchronisedOn Usun {1, 2, 3} 1 := by
  intro n hn b hb hround hbT a ha hround' haT
  have h7 : ∀ b : Fin 32, (Usun.block b).round ≤ 7 := by decide
  have hn6 : n ≤ 6 := by have := h7 b; omega
  interval_cases n <;> revert b a <;> decide

theorem usun_good :
    (mysticetiLive (Validator := Fin 4) (BlockId := Fin 32) (Payload := Unit)).Good Usun 1 7 :=
  ⟨{1, 2, 3}, ⟨by decide, by decide⟩, usun_sync, fun r h1 h2 => by
    interval_cases r <;> decide⟩

-- Population fails at round `8`: `Good Usun 1 8` needs a block there.
example : ¬ PopulatedOn Usun {1, 2, 3} 8 := by decide

/-- The real descent law at this committee: `goodLeaders` returns some
`T` of at least three validators, and rounds `1` to `4` cover every
residue, so some slot among them commits — through `MysticetiLive.holds`.
The conclusion is as weak as an existential `T` allows. -/
example : ∃ κ, 1 ≤ κ ∧ κ ≤ 4 ∧
    ∃ L, bnRule32.Decided sched1 (View.full Usun) κ (some L) := by
  obtain ⟨T, hcard, hT0⟩ :=
    (MysticetiLive.holds.1 (Fin 4) (Fin 32) Unit).goodLeaders Usun 1 7 usun_good
  have hT := fun S κ => hT0 S (View.full Usun) κ
    (coversUpto_full (Mysticeti.holds (Fin 4) (Fin 32) Unit) Usun 7)
  have h3 : 3 ≤ T.card := by
    have h4 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
    have hf : Faults.f (Fin 4) = 1 := rfl
    rw [h4, hf] at hcard
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  fin_cases v
  · exact ⟨4, by omega, by omega, hT sched1 4 (by decide) (by decide) hv⟩
  · exact ⟨1, by omega, by omega, hT sched1 1 (by decide) (by decide) hv⟩
  · exact ⟨2, by omega, by omega, hT sched1 2 (by decide) (by decide) hv⟩
  · exact ⟨3, by omega, by omega, hT sched1 3 (by decide) (by decide) hv⟩

/-! ## The paper's A4 for Mysticeti, at `n = 4` -/

example : (mysticetiLive (Validator := Fin 4) (BlockId := Fin 32) (Payload := Unit)).LiveOn
    (Sched bnLeader bnWin 2 (by decide) (by decide)) 6 :=
  MysticetiLive.holds.2 4 (by omega) (Fin 32) Unit 4 bnWin 2 (by decide) (by decide)

/-! ## The descent producing a skip, on `Usk` -/

/-- `Usk` is synchronised over `{0, 1, 3}` from round `1`: the one
under-referenced block has author `2`. -/
theorem usk_sync : SynchronisedOn Usk {0, 1, 3} 1 := by
  intro n hn b hb hround hbT a ha hround' haT
  have h7 : ∀ b : Fin 32, (Usk.block b).round ≤ 7 := by decide
  have hn6 : n ≤ 6 := by have := h7 b; omega
  interval_cases n <;> revert b a <;> decide

-- Neither the correct set nor everyone is synchronised on `Usk`: block
-- `13` (author `1`, round `3`) does not reference block `10`.
example : ¬ SynchronisedOn Usk {1, 2, 3} 1 := fun h =>
  absurd (h 2 (by omega) 13 (by decide) (by decide) (by decide) 10 (by decide) (by decide)
    (by decide))
    (by decide)
example : ¬ SynchronisedOn Usk {0, 1, 2, 3} 1 := fun h =>
  absurd (h 2 (by omega) 12 (by decide) (by decide) (by decide) 10 (by decide) (by decide)
    (by decide))
    (by decide)

/-- Real Mysticeti never calls `Usk` good from round `1`: a correct
quorum is `{1, 2, 3}` itself, and it is not synchronised. -/
theorem usk_not_good (N : ℕ) :
    ¬ (mysticetiLive (Validator := Fin 4) (BlockId := Fin 32) (Payload := Unit)).Good Usk 1 N := by
  rintro ⟨T, ⟨hsub, hcard⟩, hsync, -⟩
  change T ⊆ Correct at hsub
  rw [bnCorrect] at hsub
  have h3 : 3 ≤ T.card := by
    change Fintype.card (Fin 4) - Faults.f (Fin 4) ≤ T.card at hcard
    have h4 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
    have hf : Faults.f (Fin 4) = 1 := rfl
    rw [h4, hf] at hcard
    omega
  have hT : T = {1, 2, 3} := Finset.eq_of_subset_of_card_le hsub (by simpa using h3)
  subst hT
  exact absurd (hsync 2 (by omega) 13 (by decide) (by decide) (by decide) 10 (by decide) (by decide)
    (by decide)) (by decide)

theorem usk_pop : ∀ r, 1 ≤ r → r ≤ 7 → PopulatedOn Usk {0, 1, 3} r := by
  intro r h1 h2
  interval_cases r <;> decide

/-- On any schedule, a `{0, 1, 3}`-led slot of `Usk` at a round from `1`
whose wave fits under `8` commits on the full view — L4 on data. -/
theorem usk_goodT : ∀ (S : Slots (Fin 4)) (κ : ℕ),
    1 ≤ S.slotRound κ → S.slotRound κ + 3 ≤ 8 →
    S.leader κ ∈ ({0, 1, 3} : Finset (Fin 4)) →
    ∃ L, bnRule32.Decided S (bnLiveSk.full Usk) κ (some L) := by
  intro S κ hRnd hN hlead
  letI := S
  obtain ⟨L, -, hdec⟩ := decided_of_leader_mem (T := {0, 1, 3}) (by decide) usk_sync hRnd
    (usk_pop _ hRnd (by omega)) (usk_pop _ (by omega) (by omega))
    (usk_pop _ (by omega) (by omega)) hlead
  exact ⟨L, hdec⟩

/-- The descent laws for the `Usk` test rule, at slack `1`. -/
theorem bnLiveSk_descent : bnLiveSk.Descent 1 where
  goodLeaders := by
    rintro U Rnd N ⟨rfl, rfl, rfl⟩
    refine ⟨{0, 1, 3}, by decide, fun S V κ hcov h1 h2 h3 => ?_⟩
    obtain ⟨L, hL⟩ := usk_goodT S κ h1 h2 h3
    -- every block of `Usk` lies at a round the view covers
    have hround : ∀ b ∈ Usk.ids, (Usk.block b).round ≤ 8 := by decide
    exact ⟨L, AnchoredRule.decided_mono coreLaws trivial (S := S) (fun b hb => hcov b hb (hround b hb)) hL⟩
  indirect := (MysticetiLive.descent (Fin 4) (Fin 32) Unit).indirect

/-- Slot `2` of `Sched 1` is directly skipped on `Usk`. -/
theorem usk_skip2 : bnRule32.Decided sched1 (bnLiveSk.full Usk) 2 none :=
  Decided.directSkip (S := sched1) (by decide)

/-- **BN9b on data.** The heads of rounds `3, 4, 5` are `T`-led, so every
slot at rounds `0` to `2` is decided and the head of `3` is committed;
the verdicts are identified with the direct ones by `agree`. The
application sits on the horizon: `ρ + 2w ≤ N + 1` is `9 ≤ 9`. -/
example : ∃ v₀ v₁ v₂ L,
    bnRule32.Decided sched1 (bnLiveSk.full Usk) 0 v₀ ∧
    bnRule32.Decided sched1 (bnLiveSk.full Usk) 1 v₁ ∧
    bnRule32.Decided sched1 (bnLiveSk.full Usk) 2 v₂ ∧
    bnRule32.Decided sched1 (bnLiveSk.full Usk) (1 * 3) (some L) ∧
    v₀ = some 0 ∧ v₁ = some 5 ∧ v₂ = none ∧ L = 15 := by
  obtain ⟨hdec, L, hL⟩ :=
    (Heads.holds.1 (Fin 4) (Fin 32) Unit bnLiveSk 1 bnLeader 4 bnWin 0).2.1
    bnLiveSk_descent (Nat.succ_pos 2) Usk (bnLiveSk.full Usk) 1 8 {0, 1, 3}
    (fun S κ h1 h2 h3 => usk_goodT S κ h1 h2 h3) 1 (by decide) (by decide) 3 (by decide)
    (by decide) (by decide)
  obtain ⟨v₀, h0⟩ := hdec 0 (by decide) (by decide)
  obtain ⟨v₁, h1⟩ := hdec 1 (by decide) (by decide)
  obtain ⟨v₂, h2⟩ := hdec 2 (by decide) (by decide)
  refine ⟨v₀, v₁, v₂, L, h0, h1, h2, hL, ?_, ?_, ?_, ?_⟩
  · exact laws32.agree _ _ (bnLiveSk.full Usk) 0 _ _ h0
      (Decided.directCommit (S := sched1) (by decide) (by decide))
  · exact laws32.agree _ _ (bnLiveSk.full Usk) 1 _ _ h1
      (Decided.directCommit (S := sched1) (by decide) (by decide))
  · exact laws32.agree _ _ (bnLiveSk.full Usk) 2 _ _ h2 usk_skip2
  · exact Option.some.inj (laws32.agree _ _ (bnLiveSk.full Usk) 3 _ _ hL
      (Decided.directCommit (S := sched1) (by decide) (by decide)))

-- One round up does not fit under the horizon.
example : ¬ (4 + 3 + 3 ≤ 8 + 1) := by decide

-- `Correct` is not a good set of `Usk` at all, and its heads would not
-- serve either: the head of round `4` is the Byzantine validator `0`.
example : ¬ (∀ i, i < 3 → bnLeader (3 + i) ∈ ({1, 2, 3} : Finset (Fin 4))) := by decide

/-- **BN9a on data.** The stretch `[3, 5]` of `Sched 1` on `Usk` — three direct
commits, top `21` at round `5` — decides slots `0`, `1`, `2`; `agree` reads the
verdicts: `some 0`, `some 5`, `none`. -/
example : ∃ v₀ v₁ v₂,
    bnRule32.Decided sched1 (bnLiveSk.full Usk) 0 v₀ ∧
    bnRule32.Decided sched1 (bnLiveSk.full Usk) 1 v₁ ∧
    bnRule32.Decided sched1 (bnLiveSk.full Usk) 2 v₂ ∧
    v₀ = some 0 ∧ v₁ = some 5 ∧ v₂ = none := by
  have hw : bnLiveSk.waveLength = 3 := rfl
  have hstretch := (Heads.holds.1 (Fin 4) (Fin 32) Unit bnLiveSk 1 bnLeader 4 bnWin 0).1
    bnLiveSk_descent sched1 Usk (bnLiveSk.full Usk) 3 5
    (fun i hi => by simp only [Sched_slotRound, Nat.div_one]; omega)
    (fun j hlo hhi => by
      have : j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl
      · exact ⟨some 15, Decided.directCommit (S := sched1) (by decide) (by decide)⟩
      · exact ⟨some 16, Decided.directCommit (S := sched1) (by decide) (by decide)⟩
      · exact ⟨some 21, Decided.directCommit (S := sched1) (by decide) (by decide)⟩)
    ⟨21, Decided.directCommit (S := sched1) (by decide) (by decide)⟩
  obtain ⟨v₀, h0⟩ := hstretch 0 (by omega)
  obtain ⟨v₁, h1⟩ := hstretch 1 (by omega)
  obtain ⟨v₂, h2⟩ := hstretch 2 (by omega)
  refine ⟨v₀, v₁, v₂, h0, h1, h2, ?_, ?_, ?_⟩
  · exact laws32.agree _ _ (bnLiveSk.full Usk) 0 _ _ h0
      (Decided.directCommit (S := sched1) (by decide) (by decide))
  · exact laws32.agree _ _ (bnLiveSk.full Usk) 1 _ _ h1
      (Decided.directCommit (S := sched1) (by decide) (by decide))
  · exact laws32.agree _ _ _ 2 _ _ h2 usk_skip2

-- The span hypothesis is consumed: top `4` does not clear slot `2`.
example :
    ¬ (∀ i, i < 3 → sched1.slotRound i + bnLiveSk.waveLength ≤ sched1.slotRound 4) := by
  intro h
  have := h 2 (by omega)
  simp only [Sched_slotRound, Nat.div_one] at this
  have hw : bnLiveSk.waveLength = 3 := rfl
  omega

/-! ## The paper's A4 on data: eleven rounds -/

/-- Eleven sunny rounds on four validators, `Fin 44`. -/
def sun44 : Fin 44 → Block (Fin 4) (Fin 44) Unit := fun i =>
  { round := (i : ℕ) / 4
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩
    refs := if (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter fun j : Fin 44 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4)
    payload := () }

def U44 : BlockUniverse (Fin 4) (Fin 44) Unit where
  ids := Finset.univ
  block := sun44
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem u44_sync : SynchronisedOn U44 {1, 2, 3} 1 := by
  intro n hn b hb hround hbT a ha hround' haT
  have h10 : ∀ b : Fin 44, (U44.block b).round ≤ 10 := by decide
  have : n ≤ 9 := by have := h10 b; omega
  interval_cases n <;> revert b a <;> decide

theorem u44_good :
    (mysticetiLive (Validator := Fin 4) (BlockId := Fin 44) (Payload := Unit)).Good U44 1 10 :=
  ⟨{1, 2, 3}, ⟨by decide, by decide⟩, u44_sync, fun r h1 h2 => by
    interval_cases r <;> decide⟩

abbrev rr4 : ℕ → Fin 4 := roundRobin 4 (by omega)
abbrev sched2_44 : Slots (Fin 4) :=
  Sched rr4 (roundRobin_keyed 4 (by omega)) 2 (by decide) (by decide)
abbrev rule44 : BaseRule (Fin 4) (Fin 44) Unit := mysticeti

/-- The real theorem, the real `Good`, a verdict on data: under two leaders,
some slot at a round in `[1, 7]` of `U44` is committed. -/
example : ∃ κ, 1 ≤ sched2_44.slotRound κ ∧ sched2_44.slotRound κ ≤ 1 + 6 ∧
    ∃ L, rule44.Decided sched2_44 (View.full U44) κ (some L) :=
  ((MysticetiLive.holds.2 4 (by omega) (Fin 44) Unit 4 (roundRobin_keyed 4 (by omega)) 2
    (by decide) (by decide)) U44 (View.full U44) 1 10 u44_good
    (coversUpto_full (Mysticeti.holds (Fin 4) (Fin 44) Unit) U44 10)).2 1 (by omega) (by decide)

-- And clause 1: slot 2 (round 1, head) is decided by the theorem.
example : ∃ v, rule44.Decided sched2_44 (View.full U44) 2 v :=
  ((MysticetiLive.holds.2 4 (by omega) (Fin 44) Unit 4 (roundRobin_keyed 4 (by omega)) 2
    (by decide) (by decide)) U44 (View.full U44) 1 10 u44_good
    (coversUpto_full (Mysticeti.holds (Fin 4) (Fin 44) Unit) U44 10)).1 2 (by decide) (by decide)

-- One direct commit by `decide` on Fin 44: slot 2 = (round 1, offset 0), leader 1, block 5.
theorem u44_commit2 : rule44.Decided sched2_44 (View.full U44) 2 (some 5) :=
  Decided.directCommit (S := sched2_44) (by decide) (by decide)

-- Horizon 9 would make the theorem's product vacuous.
example : ¬ (1 + 6 + 3 ≤ 9) := by decide

#print axioms LeanDag.Barnacle.Heads.holds
#print axioms LeanDag.Barnacle.MysticetiLive.holds

end Barnacle

end LeanDagTest
