import LeanDagTest.Barnacle.Instances
/-!
# Barnacle witnesses — a bare majority, attacked

Nemo-Nemo's descent laws hold at the slack a majority may miss,
`n − majority`, and its `Good` asks only for *some* synchronised,
populated majority. This file is the adversarial check of that
choice: three validators, none crashed, a bare majority `T = {0, 2}`
that references only itself, and a live validator `1` outside it that
authors every round and is never referenced by `T`. `U3` is good over
`T` from round `0` to horizon `7` while the whole committee is not
synchronised at all. `Nemo.holds`'s round-robin liveness is applied at
gap `4` with both clauses non-vacuous — rounds `0` and `1` under the
first, `r ∈ {0, 1}` under the second — and the theorem's verdicts are
pinned through `agree`: validator `1`'s slots are *skipped*, off the
heads of the rounds a wave above them, at count `1` and at count `3`;
the committed slot the second clause finds is never validator `1`'s.
The slack is exact at `n = 3`: no descent law holds at slack `0`.

The crash-fault instance here is local and of high priority — nobody
crashed — so that `Live` is the whole committee and the majority is
strictly inside it.
-/

namespace LeanDagTest

namespace Barnacle

namespace Majority

open LeanDag LeanDag.Barnacle

instance (priority := high) attackFaults : LeanDag.Nemo.CrashFaults (Fin 3) where
  f := 1
  crashed := ∅
  card_crashed := by decide
  card_validators := by decide

-- The local instance is the one in force: nobody crashed.
example : LeanDag.Nemo.Live (Fin 3) = Finset.univ := by decide

/-- Block `i` sits at round `i / 3`, authored by `i % 3`. -/
def blk3 : Fin 24 → Block (Fin 3) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 3 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else
    { round := (i : ℕ) / 3, creator := ⟨(i : ℕ) % 3, Nat.mod_lt _ (by omega)⟩,
      refs := if (i : ℕ) % 3 = 1 then
          {⟨3 * ((i : ℕ) / 3 - 1), by have := i.isLt; omega⟩,
           ⟨3 * ((i : ℕ) / 3 - 1) + 1, by have := i.isLt; omega⟩}
        else
          {⟨3 * ((i : ℕ) / 3 - 1), by have := i.isLt; omega⟩,
           ⟨3 * ((i : ℕ) / 3 - 1) + 2, by have := i.isLt; omega⟩},
      payload := () }

def U3 : LeanDag.Nemo.Universe (Fin 3) (Fin 24) Unit where
  ids := Finset.univ
  block := blk3
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem u3_sync : SynchronisedOn U3 {0, 2} 0 := by
  intro n hn b hb hround hbT a ha hround' haT
  have h7 : ∀ b : Fin 24, (U3.block b).round ≤ 7 := by decide
  have hn6 : n ≤ 6 := by have := h7 b; omega
  interval_cases n <;> revert b a <;> decide

-- The whole committee is not synchronised: block `3` (round 1, author 0) omits block `1`.
example : ¬ SynchronisedOn U3 Finset.univ 0 := fun h =>
  absurd (h 0 le_rfl 3 (by decide) (by decide) (by decide) 1 (by decide) (by decide) (by decide))
    (by decide)

-- Validator 1's blocks are never referenced by anyone but validator 1.
example : (LeanDag.supporters U3 4 2 : Finset (Fin 3)) = {1} := by decide
example : (LeanDag.supporters U3 1 1 : Finset (Fin 3)) = {1} := by decide

theorem u3_good :
    (nemoLive (Validator := Fin 3) (BlockId := Fin 24) (Payload := Unit)).Good U3 0 7 :=
  ⟨{0, 2}, ⟨by decide, by decide⟩, u3_sync, fun r h1 h2 => by interval_cases r <;> decide⟩

example : ¬ PopulatedOn U3 {0, 2} 8 := by decide

abbrev rr3 : ℕ → Fin 3 := roundRobin 3 (by omega)
theorem rr3_keyed : Keyed rr3 3 := roundRobin_keyed 3 (by omega)
def rr3Lead : ℕ → ℕ → Fin 3 := leadOf rr3
theorem rr3LeadKeyed : LeadKeyed rr3Lead 3 := leadKeyed_of_keyed (by omega) rr3_keyed
abbrev C1 : Config (Fin 3) := Config.uniform rr3Lead rr3LeadKeyed 1 (by omega) (by omega) 3
abbrev C3 : Config (Fin 3) := Config.uniform rr3Lead rr3LeadKeyed 3 (by omega) (by omega) 3
theorem C1_head : C1.head = rr3 := by funext ρ; rfl
theorem C3_head : C3.head = rr3 := by funext ρ; rfl
abbrev S1 : Slots (Fin 3) := C1.sched
abbrev S3 : Slots (Fin 3) := C3.sched
abbrev N3 : BaseRule (Fin 3) (Fin 24) Unit := nemo

/-- `Nemo.RoundRobinLive` applied at `n = 3`, count `1`, gap `4`, horizon `7`. -/
theorem live_m1 :
    (∀ κ, 0 ≤ S1.slotRound κ → S1.slotRound κ + 4 + 2 ≤ 7 →
      ∃ v, N3.Decided S1 (View.full U3) κ v) ∧
    (∀ r, 0 ≤ r → r + 4 + 2 ≤ 7 →
      ∃ κ, r ≤ S1.slotRound κ ∧ S1.slotRound κ ≤ r + 4 ∧
        ∃ L, N3.Decided S1 (View.full U3) κ (some L)) :=
  Nemo.holds.2.2 3 (by omega) (Fin 24) Unit C1 C1_head U3
    (View.full U3) 0 7 u3_good
    (coversUpto_full (Nemo.holds.1 (Fin 3) (Fin 24) Unit).full_ids U3 7)

theorem live_m3 :
    (∀ κ, 0 ≤ S3.slotRound κ → S3.slotRound κ + 4 + 2 ≤ 7 →
      ∃ v, N3.Decided S3 (View.full U3) κ v) ∧
    (∀ r, 0 ≤ r → r + 4 + 2 ≤ 7 →
      ∃ κ, r ≤ S3.slotRound κ ∧ S3.slotRound κ ≤ r + 4 ∧
        ∃ L, N3.Decided S3 (View.full U3) κ (some L)) :=
  Nemo.holds.2.2 3 (by omega) (Fin 24) Unit C3 C3_head U3
    (View.full U3) 0 7 u3_good
    (coversUpto_full (Nemo.holds.1 (Fin 3) (Fin 24) Unit).full_ids U3 7)

/-! ### Count 1: slot 1 (round 1, leader 1) — skipped off the head of round 3 -/

theorem hand1_slot3 : N3.Decided S1 (View.full U3) 3 (some 9) :=
  LeanDag.Nemo.Decided.directCommit (S := S1) (by decide) (by decide)

theorem hand1_slot1 : N3.Decided S1 (View.full U3) 1 none := by
  refine LeanDag.Nemo.Decided.indirectSkip (S := S1) (j := 3) (A := 9) (by omega) (by decide)
    hand1_slot3 ?_ ?_
  · intro i h1 h2 h3
    have : i = 2 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 24, N3.IsLeaderBlock S1 U3 1 M → M = 4 := by decide
    have := hall L hL
    subst this
    show ¬ Nemo.CertifiedIn _ _ _ _
    decide

/-- The theorem's verdict for slot 1 at count 1 is the hand skip. -/
theorem promise_m1_slot1 :
    ∃ v, N3.Decided S1 (View.full U3) 1 v ∧ v = none := by
  obtain ⟨v, hv⟩ := live_m1.1 1 (by decide) (by decide)
  exact ⟨v, hv, (Nemo.holds.1 (Fin 3) (Fin 24) Unit).agree S1 _ _ 1 v none hv hand1_slot1⟩

-- Slot 4 (round 4, leader 1) skips likewise off the head of round 6.
theorem hand1_slot6 : N3.Decided S1 (View.full U3) 6 (some 18) :=
  LeanDag.Nemo.Decided.directCommit (S := S1) (by decide) (by decide)

theorem hand1_slot4 : N3.Decided S1 (View.full U3) 4 none := by
  refine LeanDag.Nemo.Decided.indirectSkip (S := S1) (j := 6) (A := 18) (by omega) (by decide)
    hand1_slot6 ?_ ?_
  · intro i h1 h2 h3
    have : i = 5 := by omega
    subst this
    exact absurd h3 (by decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 24, N3.IsLeaderBlock S1 U3 4 M → M = 13 := by decide
    have := hall L hL
    subst this
    show ¬ Nemo.CertifiedIn _ _ _ _
    decide

/-- Clause 2 at `r = 1`: the committed slot the theorem finds in `[1, 5]` is
one of `2, 3, 5` — never one of validator 1's. -/
theorem promise_m1_r1 :
    ∃ κ, (κ = 2 ∨ κ = 3 ∨ κ = 5) ∧
      ∃ L, N3.Decided S1 (View.full U3) κ (some L) := by
  obtain ⟨κ, h1, h2, L, hL⟩ := live_m1.2 1 (by omega) (by omega)
  simp only [Config.sched_slotRound, Config.uniform_roundOf, Nat.div_one] at h1 h2
  refine ⟨κ, ?_, L, hL⟩
  have hne1 : κ ≠ 1 := fun h => by
    subst h
    exact absurd ((Nemo.holds.1 (Fin 3) (Fin 24) Unit).agree S1 _ _ 1 _ _ hL hand1_slot1)
      (by simp)
  have hne4 : κ ≠ 4 := fun h => by
    subst h
    exact absurd ((Nemo.holds.1 (Fin 3) (Fin 24) Unit).agree S1 _ _ 4 _ _ hL hand1_slot4)
      (by simp)
  omega

/-! ### Count 3: slots 1 and 3, both led by validator 1 -/

theorem hand3_slot6 : N3.Decided S3 (View.full U3) 6 (some 8) :=
  LeanDag.Nemo.Decided.directCommit (S := S3) (by decide) (by decide)

theorem hand3_slot1 : N3.Decided S3 (View.full U3) 1 none := by
  refine LeanDag.Nemo.Decided.indirectSkip (S := S3) (j := 6) (A := 8) (by omega) (by decide)
    hand3_slot6 ?_ ?_
  · intro i h1 h2 h3
    exact absurd h3 (by interval_cases i <;> decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 24, N3.IsLeaderBlock S3 U3 1 M → M = 1 := by decide
    have := hall L hL
    subst this
    show ¬ Nemo.CertifiedIn _ _ _ _
    decide

theorem hand3_slot9 : N3.Decided S3 (View.full U3) 9 (some 9) :=
  LeanDag.Nemo.Decided.directCommit (S := S3) (by decide) (by decide)

theorem hand3_slot3 : N3.Decided S3 (View.full U3) 3 none := by
  refine LeanDag.Nemo.Decided.indirectSkip (S := S3) (j := 9) (A := 9) (by omega) (by decide)
    hand3_slot9 ?_ ?_
  · intro i h1 h2 h3
    exact absurd h3 (by interval_cases i <;> decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 24, N3.IsLeaderBlock S3 U3 3 M → M = 4 := by decide
    have := hall L hL
    subst this
    show ¬ Nemo.CertifiedIn _ _ _ _
    decide

theorem promise_m3 :
    (∃ v, N3.Decided S3 (View.full U3) 1 v ∧ v = none) ∧
    (∃ v, N3.Decided S3 (View.full U3) 3 v ∧ v = none) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := live_m3.1 1 (by decide) (by decide)
    exact ⟨v, hv, (Nemo.holds.1 (Fin 3) (Fin 24) Unit).agree S3 _ _ 1 v none hv hand3_slot1⟩
  · obtain ⟨v, hv⟩ := live_m3.1 3 (by decide) (by decide)
    exact ⟨v, hv, (Nemo.holds.1 (Fin 3) (Fin 24) Unit).agree S3 _ _ 3 v none hv hand3_slot3⟩

/-! ### Exactness of the slack at `n = 3`: no descent law at slack `0` -/

theorem not_descent_zero :
    ¬ (nemoLive (Validator := Fin 3) (BlockId := Fin 24) (Payload := Unit)).Descent 0 := by
  intro hD
  obtain ⟨T, hcard, hT⟩ := hD.goodLeaders U3 0 7 u3_good
  have hTuniv : T = Finset.univ :=
    Finset.eq_univ_of_card T (le_antisymm (Finset.card_le_univ T) (by simpa using hcard))
  obtain ⟨L, hL⟩ := hT S1 (View.full U3) 1
    (coversUpto_full (Nemo.holds.1 (Fin 3) (Fin 24) Unit).full_ids U3 7)
    (by decide) (by decide) (by rw [hTuniv]; exact Finset.mem_univ _)
  exact absurd ((Nemo.holds.1 (Fin 3) (Fin 24) Unit).agree S1 _ _ 1 _ _ hL hand1_slot1) (by simp)

#print axioms promise_m1_slot1
#print axioms promise_m3
#print axioms not_descent_zero

#print axioms live_m1
#print axioms promise_m3
#print axioms not_descent_zero

end Majority

end Barnacle

end LeanDagTest
