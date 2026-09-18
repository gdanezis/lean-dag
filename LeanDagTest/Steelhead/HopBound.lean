import LeanDagTest.Steelhead.ByzantineFloor
import LeanDag.Steelhead.Helpers.Coin
/-!
# Steelhead witnesses: the per-hop bound

Theorem 2 of the paper bounds the anchor search from a Byzantine-led slot
by its coins: each hop of the search lands on a Byzantine-led slot with
probability at most `b/n`, so that two hops cost `(b/n)^2` at most. One
universe, `hb36`: nine rounds `0..8` at the constant wavelength `3`, the
committee of the other witnesses (validator `0` Byzantine, `f = 1`,
quorum `3`), the chain schedule of an arbitrary coin, and validators `1`
and `2` omitting validator `0`'s block at rounds `4`, `5` and `7`, so
that its blocks of rounds `3`, `4` and `6` each carry two votes and two
blames: no certificate, no direct skip. On it the first two landings of
the chain from slot `0` are both led by validator `0` under either of two
disjoint coin patterns:

* rounds `3` and `6` draw `0`: slot `3` is undecided, its floor `6` is
  undecided, and the chain lands on `3` and then on `6`;
* round `3` draws `0`, round `6` does not, and rounds `4` and `7` draw
  `0`: the honest coin of round `6` commits slot `6` directly, which
  skips slot `3` through the anchor, so the chain passes over `3` to the
  undecided slot `4`, and from its floor `7` lands there, undecided too.

The patterns have probabilities `1/16` and `3/256` under the uniform
coin, `19/256` together, above the `(b/n)^2 = 1/16` that two hops at
`b/n` each would cost. The two hops are not two independent draws: the
coin of round `6` both decides whether slot `3` is skipped and leads the
landing above it, so where a hop lands is not a function of the coins
drawn below the floor it hops from.

The wavelength is constant, since the anchor rule reads the same at any
wave and the smallest wave keeps the universe at thirty-six blocks; the
schedule is one slot per round.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead
open scoped ENNReal

set_option maxRecDepth 8192

/-! ## `hb36`: nine rounds, validator `0`'s blocks at rounds `3`, `4` and `6` half-referenced -/

/-- The round of a block: `4m + v` is validator `v`'s round-`m` block. -/
def hbRound (i : ℕ) : ℕ := i / 4

/-- The creator of a block. -/
def hbCreator (i : ℕ) : ℕ := i % 4

/-- The creator is one of the four validators. -/
theorem hbCreator_lt (i : ℕ) : hbCreator i < 4 := Nat.mod_lt _ (by omega)

/-- Whether validator `v`'s round-`m` block omits block `j` of the round below: validators `1`
and `2` omit validator `0`'s block at rounds `4`, `5` and `7`, blocks `12`, `16` and `24`. -/
def hbOmits (m v j : ℕ) : Bool :=
  (v == 1 || v == 2) && (m == 4 && j == 12 || m == 5 && j == 16 || m == 7 && j == 24)

/-- Every non-genesis block references the round below less the block `hbOmits` names. -/
def hbBlk : Fin 36 → Block (Fin 4) (Fin 36) Unit := fun i =>
  { round := hbRound i, creator := ⟨hbCreator i, hbCreator_lt i⟩,
    refs := if hbRound i = 0 then ∅ else
      Finset.univ.filter fun j : Fin 36 =>
        hbRound j + 1 = hbRound i ∧ hbOmits (hbRound i) (hbCreator i) j = false,
    payload := () }

/-- The universe of the thirty-six blocks: complete, valid and free of equivocation. -/
def hb36 : BlockUniverse (Fin 4) (Fin 36) Unit where
  ids := Finset.univ
  block := hbBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The omissions at rounds `4`, `5` and `7`, and the full round elsewhere.
example : (hb36.block 16).refs = {12, 13, 14, 15} := by decide
example : (hb36.block 17).refs = {13, 14, 15} := by decide
example : (hb36.block 21).refs = {17, 18, 19} := by decide
example : (hb36.block 23).refs = {16, 17, 18, 19} := by decide
example : (hb36.block 29).refs = {25, 26, 27} := by decide
example : (hb36.block 31).refs = {24, 25, 26, 27} := by decide
example : (hb36.block 32).refs = {28, 29, 30, 31} := by decide

/-- Every block sits at round `8` or below. -/
theorem hb36_round_le : ∀ b : Fin 36, (hb36.block b).round ≤ 8 := by decide

/-! ## Validator `0`'s blocks: two votes, two blames, no certificate -/

-- Block `12`, validator `0`'s round-`3` block: voted for by `16` and `19`, blamed by `17` and
-- `18`, certified by nothing at round `5`.
example : (blocksAt hb36 4).filter (fun q => MahiMahi.Votes hb36 q 12) = {16, 19} := by decide
example : (blocksAt hb36 4).filter (fun q => MahiMahi.Blames hb36 q 0 3) = {17, 18} := by decide
example : MahiMahi.certificates hb36 3 12 3 = ∅ := by decide

-- Block `16`, its round-`4` block: voted for by `20` and `23`, blamed by `21` and `22`.
example : (blocksAt hb36 5).filter (fun q => MahiMahi.Votes hb36 q 16) = {20, 23} := by decide
example : (blocksAt hb36 5).filter (fun q => MahiMahi.Blames hb36 q 0 4) = {21, 22} := by decide
example : MahiMahi.certificates hb36 3 16 4 = ∅ := by decide

-- Block `24`, its round-`6` block: voted for by `28` and `31`, blamed by `29` and `30`.
example : (blocksAt hb36 7).filter (fun q => MahiMahi.Votes hb36 q 24) = {28, 31} := by decide
example : (blocksAt hb36 7).filter (fun q => MahiMahi.Blames hb36 q 0 6) = {29, 30} := by decide
example : MahiMahi.certificates hb36 3 24 6 = ∅ := by decide

-- Block `28`, its round-`7` block: the whole of round `8` votes for it, and the universe holds
-- no round `9` to certify it.
example : (blocksAt hb36 8).filter (fun q => MahiMahi.Votes hb36 q 28) = {32, 33, 34, 35} := by
  decide
example : MahiMahi.certificates hb36 3 28 7 = ∅ := by decide

-- Every honest block of rounds `3`, `4` and `6` is certified by the whole of its decision round.
example : ∀ L : Fin 36, (hb36.block L).round = 3 → (hb36.block L).creator ≠ 0 →
    MahiMahi.certificates hb36 3 L 3 = {20, 21, 22, 23} := by decide
example : ∀ L : Fin 36, (hb36.block L).round = 4 → (hb36.block L).creator ≠ 0 →
    MahiMahi.certificates hb36 3 L 4 = {24, 25, 26, 27} := by decide
example : ∀ L : Fin 36, (hb36.block L).round = 6 → (hb36.block L).creator ≠ 0 →
    MahiMahi.certificates hb36 3 L 6 = {32, 33, 34, 35} := by decide

/-! ## The direct verdicts -/

/-- **Slot `3` has no direct verdict when validator `0` leads it**: block `12` has no
certificate, and round `4` holds two blames. -/
theorem hb36_slot3_direct :
    (∀ L : Fin 36, (hb36.block L).round = 3 → (hb36.block L).creator = 0 →
      ¬ (steelheadAnchored (Fin 4) (Fin 36) Unit w3).Commit hb36 (View.full hb36) L 3 1) ∧
    ¬ MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 0 3 := by
  decide

/-- **Slot `4` has no direct verdict when validator `0` leads it**: block `16` has no
certificate, and round `5` holds two blames. -/
theorem hb36_slot4_direct :
    (∀ L : Fin 36, (hb36.block L).round = 4 → (hb36.block L).creator = 0 →
      ¬ (steelheadAnchored (Fin 4) (Fin 36) Unit w3).Commit hb36 (View.full hb36) L 4 1) ∧
    ¬ MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 0 4 := by
  decide

/-- **Slot `6` has no direct verdict when validator `0` leads it**: block `24` has no
certificate, and round `7` holds two blames. -/
theorem hb36_slot6_direct :
    (∀ L : Fin 36, (hb36.block L).round = 6 → (hb36.block L).creator = 0 →
      ¬ (steelheadAnchored (Fin 4) (Fin 36) Unit w3).Commit hb36 (View.full hb36) L 6 1) ∧
    ¬ MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 0 6 := by
  decide

/-- **Slot `7` has no direct verdict when validator `0` leads it**: the universe holds no round
`9` to certify block `28`, and round `8` holds no blame. -/
theorem hb36_slot7_direct :
    (∀ L : Fin 36, (hb36.block L).round = 7 → (hb36.block L).creator = 0 →
      ¬ (steelheadAnchored (Fin 4) (Fin 36) Unit w3).Commit hb36 (View.full hb36) L 7 1) ∧
    ¬ MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 0 7 := by
  decide

/-- **An honest leader of slot `6` is committed directly**: validator `u ≠ 0`'s round-`6` block
`24 + u` is certified by the whole of round `8`. -/
theorem hb36_slot6_commit : ∀ u : Fin 4, u ≠ 0 → ∃ L : Fin 36, (hb36.block L).round = 6 ∧
    (hb36.block L).creator = u ∧
    (steelheadAnchored (Fin 4) (Fin 36) Unit w3).Commit hb36 (View.full hb36) L 6 1 := by
  decide

/-- **Validator `0`'s candidate for slot `3` is certified nowhere**: block `12`'s certificate
set is empty, so no anchor's cone links it. -/
theorem hb36_slot3_cert : ∀ L : Fin 36, (hb36.block L).round = 3 → (hb36.block L).creator = 0 →
    MahiMahi.certificates hb36 3 L 3 = ∅ := by
  decide

/-! ## The verdicts at the chain schedule of an arbitrary coin -/

/-- Eligibility at the chain schedule and the constant wave: an anchor of slot `k` is a slot at
round `k + 3` or above. -/
theorem hb36_eligible_iff (coin : ℕ → Fin 4) (k j : ℕ) :
    (steelheadAnchored (Fin 4) (Fin 36) Unit w3).Eligible (S := chainSlots coin) k j ↔
      k + 3 ≤ j := by
  change k + (3 - 1) < j ↔ k + 3 ≤ j
  omega

/-- A candidate's slot sits at round `8` or below, whatever the coin. -/
theorem hb36_slot_le {coin : ℕ → Fin 4} {j : ℕ} {A : Fin 36}
    (hA : IsLeaderBlock (S := chainSlots coin) hb36 j A) : j ≤ 8 := by
  have := hb36_round_le A
  have hr : (hb36.block A).round = j := hA.2.1
  omega

/-- **No slot at round `9` or above commits**, whatever the coin: there is no candidate up there,
and an indirect commit rests on an anchor higher still. -/
theorem hb36_not_commit_above {coin : ℕ → Fin 4} {j : ℕ} (hj : 9 ≤ j) (A : Fin 36) :
    ¬ Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) j (some A) := by
  intro h
  cases h with
  | directCommit hL _ =>
    have := hb36_slot_le hL
    omega
  | indirectCommit hkj he hj' _ _ _ _ _ _ =>
    have := hb36_slot_le (AnchoredRule.isLeaderBlock_of_decided (S := chainSlots coin) hj')
    have := (hb36_eligible_iff coin _ _).mp he
    omega

/-- **Slot `6` is undecided when round `6` draws validator `0`**: neither direct verdict holds,
and any anchor lies at round `9` or above, where nothing commits. -/
theorem hb36_slot6_undecided {coin : ℕ → Fin 4} (h6 : coin 6 = 0) (v : Option (Fin 36)) :
    ¬ Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) 6 v := by
  intro h
  cases h with
  | @directCommit _ L hL hc =>
    have hc' : (hb36.block L).creator = coin 6 := hL.2.2
    rw [h6] at hc'
    exact hb36_slot6_direct.1 L hL.2.1 hc' hc
  | directSkip hs =>
    change MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 (coin 6) 6 at hs
    rw [h6] at hs
    exact hb36_slot6_direct.2 hs
  | indirectCommit hkj he hj' _ _ _ _ _ _ =>
    exact hb36_not_commit_above (by have := (hb36_eligible_iff coin _ _).mp he; omega) _ hj'
  | indirectSkip hkj he hj' _ _ =>
    exact hb36_not_commit_above (by have := (hb36_eligible_iff coin _ _).mp he; omega) _ hj'

/-- **Slot `3` is undecided when rounds `3` and `6` draw validator `0`**: neither direct verdict
holds, and any anchor is slot `6`, which is undecided, or lies above it, which needs slot `6`
skipped. -/
theorem hb36_slot3_undecided {coin : ℕ → Fin 4} (h3 : coin 3 = 0) (h6 : coin 6 = 0)
    (v : Option (Fin 36)) :
    ¬ Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) 3 v := by
  intro h
  cases h with
  | @directCommit _ L hL hc =>
    have hc' : (hb36.block L).creator = coin 3 := hL.2.2
    rw [h3] at hc'
    exact hb36_slot3_direct.1 L hL.2.1 hc' hc
  | directSkip hs =>
    change MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 (coin 3) 3 at hs
    rw [h3] at hs
    exact hb36_slot3_direct.2 hs
  | indirectCommit hkj he hj' hmid _ _ _ _ _ =>
    rcases Nat.eq_or_lt_of_le ((hb36_eligible_iff coin _ _).mp he) with rfl | hlt
    · exact hb36_slot6_undecided h6 _ hj'
    · exact hb36_slot6_undecided h6 none
        (hmid 6 (by omega) hlt ((hb36_eligible_iff coin _ _).mpr le_rfl))
  | indirectSkip hkj he hj' hmid _ =>
    rcases Nat.eq_or_lt_of_le ((hb36_eligible_iff coin _ _).mp he) with rfl | hlt
    · exact hb36_slot6_undecided h6 _ hj'
    · exact hb36_slot6_undecided h6 none
        (hmid 6 (by omega) hlt ((hb36_eligible_iff coin _ _).mpr le_rfl))

/-- **Slot `7` is undecided when round `7` draws validator `0`**: neither direct verdict holds,
and any anchor lies at round `10` or above, where nothing commits. -/
theorem hb36_slot7_undecided {coin : ℕ → Fin 4} (h7 : coin 7 = 0) (v : Option (Fin 36)) :
    ¬ Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) 7 v := by
  intro h
  cases h with
  | @directCommit _ L hL hc =>
    have hc' : (hb36.block L).creator = coin 7 := hL.2.2
    rw [h7] at hc'
    exact hb36_slot7_direct.1 L hL.2.1 hc' hc
  | directSkip hs =>
    change MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 (coin 7) 7 at hs
    rw [h7] at hs
    exact hb36_slot7_direct.2 hs
  | indirectCommit hkj he hj' _ _ _ _ _ _ =>
    exact hb36_not_commit_above (by have := (hb36_eligible_iff coin _ _).mp he; omega) _ hj'
  | indirectSkip hkj he hj' _ _ =>
    exact hb36_not_commit_above (by have := (hb36_eligible_iff coin _ _).mp he; omega) _ hj'

/-- **Slot `4` is undecided when rounds `4` and `7` draw validator `0`**: neither direct verdict
holds, and any anchor is slot `7`, which is undecided, or lies above it, which needs slot `7`
skipped. -/
theorem hb36_slot4_undecided {coin : ℕ → Fin 4} (h4 : coin 4 = 0) (h7 : coin 7 = 0)
    (v : Option (Fin 36)) :
    ¬ Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) 4 v := by
  intro h
  cases h with
  | @directCommit _ L hL hc =>
    have hc' : (hb36.block L).creator = coin 4 := hL.2.2
    rw [h4] at hc'
    exact hb36_slot4_direct.1 L hL.2.1 hc' hc
  | directSkip hs =>
    change MahiMahi.DirectSkipIn hb36 (View.full hb36) 3 (coin 4) 4 at hs
    rw [h4] at hs
    exact hb36_slot4_direct.2 hs
  | indirectCommit hkj he hj' hmid _ _ _ _ _ =>
    rcases Nat.eq_or_lt_of_le ((hb36_eligible_iff coin _ _).mp he) with rfl | hlt
    · exact hb36_slot7_undecided h7 _ hj'
    · exact hb36_slot7_undecided h7 none
        (hmid 7 (by omega) hlt ((hb36_eligible_iff coin _ _).mpr le_rfl))
  | indirectSkip hkj he hj' hmid _ =>
    rcases Nat.eq_or_lt_of_le ((hb36_eligible_iff coin _ _).mp he) with rfl | hlt
    · exact hb36_slot7_undecided h7 _ hj'
    · exact hb36_slot7_undecided h7 none
        (hmid 7 (by omega) hlt ((hb36_eligible_iff coin _ _).mpr le_rfl))

/-- **Slot `3` is skipped when round `3` draws validator `0` and round `6` does not**: the
honest coin commits slot `6` directly, no slot lies between at wave `3`, and block `12`, the one
candidate of slot `3`, has no certificate for the anchor's cone to hold. -/
theorem hb36_slot3_skipped {coin : ℕ → Fin 4} (h3 : coin 3 = 0) (h6 : coin 6 ≠ 0) :
    Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) 3 none := by
  obtain ⟨A, hAr, hAc, hA⟩ := hb36_slot6_commit _ h6
  have hlead : IsLeaderBlock (S := chainSlots coin) hb36 6 A := ⟨Finset.mem_univ _, hAr, hAc⟩
  refine AnchoredRule.Decided.indirectSkip_single (S := chainSlots coin) rfl (by omega)
    ((hb36_eligible_iff coin _ _).mpr le_rfl)
    (Decided.directCommit (S := chainSlots coin) hlead hA) ?_ ?_
  · intro m _ hm hme
    have := (hb36_eligible_iff coin _ _).mp hme
    omega
  · intro L hL
    have hLc : (hb36.block L).creator = coin 3 := hL.2.2
    rw [h3] at hLc
    change ¬ LinkedVia hb36 A (MahiMahi.certificates hb36 3 L 3)
    rw [hb36_slot3_cert L hL.2.1 hLc]
    simp [LinkedVia]

/-! ## The landings of the chain from slot `0` -/

/-- **Under the first pattern the chain lands on `3` and then on `6`**: slot `3` is undecided, so
the hop from slot `0` stops at its floor, and slot `6` is undecided, so the hop from `3` stops at
its floor too. -/
theorem hb36_landings_first {coin : ℕ → Fin 4} (h3 : coin 3 = 0) (h6 : coin 6 = 0) :
    floorChain (S := chainSlots coin) w3 hb36 (View.full hb36) 0 1 = 3 ∧
      floorChain (S := chainSlots coin) w3 hb36 (View.full hb36) 0 2 = 6 := by
  have l1 : floorLanding (S := chainSlots coin) w3 hb36 (View.full hb36) 0 = 3 :=
    floorLanding_eq_floor (S := chainSlots coin) (hb36_slot3_undecided h3 h6 none)
  refine ⟨l1, ?_⟩
  change floorLanding (S := chainSlots coin) w3 hb36 (View.full hb36)
    (floorLanding (S := chainSlots coin) w3 hb36 (View.full hb36) 0) = 6
  rw [l1]
  exact floorLanding_eq_floor (S := chainSlots coin) (hb36_slot6_undecided h6 none)

/-- **Under the second pattern the chain lands on `4` and then on `7`**: slot `3` is skipped and
slot `4` undecided, so the hop from slot `0` passes its floor and stops at `4`; slot `7` is
undecided, so the hop from `4` stops at its floor. -/
theorem hb36_landings_second {coin : ℕ → Fin 4} (h3 : coin 3 = 0) (h6 : coin 6 ≠ 0)
    (h4 : coin 4 = 0) (h7 : coin 7 = 0) :
    floorChain (S := chainSlots coin) w3 hb36 (View.full hb36) 0 1 = 4 ∧
      floorChain (S := chainSlots coin) w3 hb36 (View.full hb36) 0 2 = 7 := by
  classical
  have hex : ∃ y, 0 + w3 ((chainSlots coin).kind 0) ≤ y ∧
      ¬ Steelhead.Decided (S := chainSlots coin) w3 hb36 (View.full hb36) y none :=
    ⟨4, by change 0 + 3 ≤ 4; omega, hb36_slot4_undecided h4 h7 none⟩
  have l1 : floorLanding (S := chainSlots coin) w3 hb36 (View.full hb36) 0 = 4 := by
    unfold floorLanding
    rw [dif_pos hex, Nat.find_eq_iff]
    refine ⟨⟨by change 0 + 3 ≤ 4; omega, hb36_slot4_undecided h4 h7 none⟩,
      fun n hn ⟨hn3, hskip⟩ => ?_⟩
    change 0 + 3 ≤ n at hn3
    obtain rfl : n = 3 := by omega
    exact hskip (hb36_slot3_skipped h3 h6)
  refine ⟨l1, ?_⟩
  change floorLanding (S := chainSlots coin) w3 hb36 (View.full hb36)
    (floorLanding (S := chainSlots coin) w3 hb36 (View.full hb36) 0) = 7
  rw [l1]
  exact floorLanding_eq_floor (S := chainSlots coin) (hb36_slot7_undecided h7 none)

/-! ## The probability of two Byzantine-led landings -/

/-- **The event that the first two landings are Byzantine-led**: the coins of rounds `0` to `8`,
read as a coin map, elect a Byzantine validator at each of the first two landings of the chain
from slot `0`. -/
def hbBad : Set (Fin 9 → Fin 4) :=
  {g | ∀ i, i < 2 → coinOfRounds g 0
    (floorChain (S := chainSlots (coinOfRounds g 0)) w3 hb36 (View.full hb36) 0 (i + 1))
      ∈ (Faults.byzantine : Finset (Fin 4))}

/-- **The first pattern**: rounds `3` and `6` draw validator `0`. -/
def hbFirst : Finset (Fin 9 → Fin 4) :=
  Fintype.piFinset fun i => if i = 3 ∨ i = 6 then {0} else Finset.univ

/-- **The second pattern**: rounds `3`, `4` and `7` draw validator `0`, and round `6` does not. -/
def hbSecond : Finset (Fin 9 → Fin 4) :=
  Fintype.piFinset fun i =>
    if i = 3 ∨ i = 4 ∨ i = 7 then {0} else if i = 6 then Finset.univ.erase 0 else Finset.univ

/-- The first pattern, as draws. -/
theorem mem_hbFirst {g : Fin 9 → Fin 4} : g ∈ hbFirst ↔ g 3 = 0 ∧ g 6 = 0 := by
  rw [hbFirst, Fintype.mem_piFinset]
  constructor
  · intro h
    have h3 := h 3
    have h6 := h 6
    simp at h3 h6
    exact ⟨h3, h6⟩
  · rintro ⟨h3, h6⟩ i
    by_cases hi : i = 3 ∨ i = 6
    · rw [if_pos hi]
      rcases hi with rfl | rfl
      · exact Finset.mem_singleton.mpr h3
      · exact Finset.mem_singleton.mpr h6
    · rw [if_neg hi]
      exact Finset.mem_univ _

/-- The second pattern, as draws. -/
theorem mem_hbSecond {g : Fin 9 → Fin 4} :
    g ∈ hbSecond ↔ g 3 = 0 ∧ g 6 ≠ 0 ∧ g 4 = 0 ∧ g 7 = 0 := by
  rw [hbSecond, Fintype.mem_piFinset]
  constructor
  · intro h
    have h3 := h 3
    have h4 := h 4
    have h6 := h 6
    have h7 := h 7
    simp at h3 h4 h6 h7
    exact ⟨h3, h6, h4, h7⟩
  · rintro ⟨h3, h6, h4, h7⟩ i
    by_cases hi : i = 3 ∨ i = 4 ∨ i = 7
    · rw [if_pos hi]
      rcases hi with rfl | rfl | rfl
      · exact Finset.mem_singleton.mpr h3
      · exact Finset.mem_singleton.mpr h4
      · exact Finset.mem_singleton.mpr h7
    · rw [if_neg hi]
      by_cases hi6 : i = 6
      · rw [if_pos hi6, hi6]
        exact Finset.mem_erase.mpr ⟨h6, Finset.mem_univ _⟩
      · rw [if_neg hi6]
        exact Finset.mem_univ _

/-- The first pattern fixes two of nine coins: `4^7` maps. -/
theorem card_hbFirst : hbFirst.card = 4 ^ 7 := by
  rw [hbFirst, Fintype.card_piFinset]
  decide

/-- The second pattern fixes three coins and excludes one value of a fourth: `3 · 4^5` maps. -/
theorem card_hbSecond : hbSecond.card = 3 * 4 ^ 5 := by
  rw [hbSecond, Fintype.card_piFinset]
  decide

/-- The patterns disagree on round `6`. -/
theorem disjoint_hbFirst_hbSecond : Disjoint hbFirst hbSecond :=
  Finset.disjoint_left.mpr fun _ h1 h2 => (mem_hbSecond.mp h2).2.1 (mem_hbFirst.mp h1).2

/-- The coin map reads a draw back below the horizon. -/
theorem coinOfRounds_of_lt {K : ℕ} (g : Fin K → Fin 4) (d : Fin 4) {r : ℕ} (h : r < K) :
    coinOfRounds g d r = g ⟨r, h⟩ :=
  dif_pos h

/-- **Both patterns make the first two landings Byzantine-led**: under the first the chain lands
on `3` and `6`, under the second on `4` and `7`, and the pattern draws validator `0` there. -/
theorem hbFirst_union_hbSecond_subset : (↑(hbFirst ∪ hbSecond) : Set (Fin 9 → Fin 4)) ⊆ hbBad := by
  intro g hg
  rw [Finset.mem_coe, Finset.mem_union, mem_hbFirst, mem_hbSecond] at hg
  rw [hbBad, Set.mem_setOf_eq]
  intro i hi
  rcases hg with ⟨h3, h6⟩ | ⟨h3, h6, h4, h7⟩
  · have c3 : coinOfRounds g 0 3 = 0 := by rw [coinOfRounds_of_lt g 0 (by omega)]; exact h3
    have c6 : coinOfRounds g 0 6 = 0 := by rw [coinOfRounds_of_lt g 0 (by omega)]; exact h6
    obtain ⟨l1, l2⟩ := hb36_landings_first (coin := coinOfRounds g 0) c3 c6
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [show (0 : ℕ) + 1 = 1 from rfl, l1, c3]
      decide
    · rw [show (1 : ℕ) + 1 = 2 from rfl, l2, c6]
      decide
  · have c3 : coinOfRounds g 0 3 = 0 := by rw [coinOfRounds_of_lt g 0 (by omega)]; exact h3
    have c6 : coinOfRounds g 0 6 ≠ 0 := by rw [coinOfRounds_of_lt g 0 (by omega)]; exact h6
    have c4 : coinOfRounds g 0 4 = 0 := by rw [coinOfRounds_of_lt g 0 (by omega)]; exact h4
    have c7 : coinOfRounds g 0 7 = 0 := by rw [coinOfRounds_of_lt g 0 (by omega)]; exact h7
    obtain ⟨l1, l2⟩ := hb36_landings_second (coin := coinOfRounds g 0) c3 c6 c4 c7
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [show (0 : ℕ) + 1 = 1 from rfl, l1, c4]
      decide
    · rw [show (1 : ℕ) + 1 = 2 from rfl, l2, c7]
      decide

/-- **The two patterns together weigh `19/256`**: `4^7 + 3 · 4^5` of the `4^9` maps. -/
theorem hbFirst_union_hbSecond_measure :
    (PMF.uniformOfFintype (Fin 9 → Fin 4)).toOuterMeasure ↑(hbFirst ∪ hbSecond) =
      ((4 ^ 7 + 3 * 4 ^ 5 : ℕ) : ℝ≥0∞) / ((4 ^ 9 : ℕ) : ℝ≥0∞) := by
  rw [uniform_prob_mem, Finset.card_union_of_disjoint disjoint_hbFirst_hbSecond, card_hbFirst,
    card_hbSecond, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- `(1/4)^2 = 16/256 < 19/256`. -/
theorem hb36_ratio_lt :
    (((1 : ℕ) : ℝ≥0∞) / ((4 : ℕ) : ℝ≥0∞)) ^ 2 <
      ((4 ^ 7 + 3 * 4 ^ 5 : ℕ) : ℝ≥0∞) / ((4 ^ 9 : ℕ) : ℝ≥0∞) := by
  rw [← ENNReal.toReal_lt_toReal (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by simp)))
    (ENNReal.div_ne_top (by simp) (by simp))]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast]
  norm_num

/-- **The per-hop bound fails at two hops**: under the uniform coin of nine rounds, the first two
landings of the chain from slot `0` are both Byzantine-led with probability at least `19/256`,
above the `(b/n)^2 = 1/16` of two hops at `b/n` each. -/
theorem hb36_hop_bound_fails :
    (((Faults.byzantine : Finset (Fin 4)).card : ℝ≥0∞) / Fintype.card (Fin 4)) ^ 2 <
      (PMF.uniformOfFintype (Fin 9 → Fin 4)).toOuterMeasure hbBad := by
  have hb : (Faults.byzantine : Finset (Fin 4)).card = 1 := by decide
  rw [hb, Fintype.card_fin]
  calc (((1 : ℕ) : ℝ≥0∞) / ((4 : ℕ) : ℝ≥0∞)) ^ 2
      < ((4 ^ 7 + 3 * 4 ^ 5 : ℕ) : ℝ≥0∞) / ((4 ^ 9 : ℕ) : ℝ≥0∞) := hb36_ratio_lt
    _ = (PMF.uniformOfFintype (Fin 9 → Fin 4)).toOuterMeasure ↑(hbFirst ∪ hbSecond) :=
        hbFirst_union_hbSecond_measure.symm
    _ ≤ (PMF.uniformOfFintype (Fin 9 → Fin 4)).toOuterMeasure hbBad :=
        (PMF.uniformOfFintype (Fin 9 → Fin 4)).toOuterMeasure.mono hbFirst_union_hbSecond_subset

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms hb36_hop_bound_fails

end LeanDagTest
