import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Model.Decision
/-!
# Steelhead witnesses: the Byzantine floor

Theorem 2 of the paper says an asynchronous slot whose Byzantine leader
equivocates "is decided by its anchor once the first honest-led slot
above its floor commits, at most `b` slots higher". The anchor search
stops at the first commit-or-undecided slot at or above the floor, so a
slot at the floor whose Byzantine leader also equivocates is the anchor,
and the search waits on it (`steelhead.md` §7). One universe, `bf30`:
seven rounds `0..6` at the constant wavelength `3`, the committee of the
other witnesses (validator `0` Byzantine, `f = 1`, quorum `3`), and a
schedule naming validator `0` at slots `0`, `3` and `6` and validator `1`
elsewhere, as a coin may. On it:

* validator `0` equivocates at rounds `0` and `3`; at the round above
  each, two validators reference one of its blocks and two the other, so
  each of its candidates has two votes, no certificate and no blame:
  slots `0` and `3` are neither directly committed nor directly skipped;
* the honest-led slot `4` is directly committed, the whole of round `6`
  certifying its candidate;
* **slot `0` is undecided in the full view** although slot `4`, the
  first honest-led slot above its floor `3`, is committed: the anchor
  search stops at the undecided slot `3`, whose own floor `6` the
  universe does not decide. The chain of floors is one wave a hop, and
  the same Byzantine validator may lead every hop.

The wavelength is constant, since the anchor rule reads the same at any
wave and the smallest wave keeps the universe at thirty blocks; the
schedule is one slot per round.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

set_option maxRecDepth 8192

/-- One slot per round, validator `0` at every third slot and validator `1` elsewhere. -/
local instance bfSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨if k % 3 = 0 then 0 else 1, by split <;> omega⟩)

/-- The constant wavelength `3`. -/
abbrev w3 : ℕ → ℕ := fun _ => 3

/-! ## `bf30`: seven rounds, validator `0` equivocating at rounds `0` and `3` -/

/-- The round of a block: `4m + v` is validator `v`'s round-`m` block for `m ≤ 6`; blocks `28` and
`29` are validator `0`'s second blocks at rounds `0` and `3`. -/
def bfRound (i : ℕ) : ℕ := if i = 28 then 0 else if i = 29 then 3 else i / 4

/-- The creator of a block. -/
def bfCreator (i : ℕ) : ℕ := if 28 ≤ i then 0 else i % 4

theorem bfCreator_lt (i : ℕ) : bfCreator i < 4 := by
  unfold bfCreator
  split
  · omega
  · exact Nat.mod_lt _ (by omega)

/-- Whether validator `v`'s round-`m` block omits block `j` of the round below: at rounds `1` and
`4` validators `1` and `3` reference validator `0`'s first block and validators `0` and `2` its
second. -/
def bfOmits (m v j : ℕ) : Bool :=
  (m == 1 && ((v == 1 || v == 3) && j == 28 || (v == 0 || v == 2) && j == 0)) ||
    (m == 4 && ((v == 1 || v == 3) && j == 29 || (v == 0 || v == 2) && j == 12))

/-- Every non-genesis block references the round below less the block `bfOmits` names. -/
def bfBlk : Fin 30 → Block (Fin 4) (Fin 30) Unit := fun i =>
  { round := bfRound i, creator := ⟨bfCreator i, bfCreator_lt i⟩,
    refs := if bfRound i = 0 then ∅ else
      Finset.univ.filter fun j : Fin 30 =>
        bfRound j + 1 = bfRound i ∧ bfOmits (bfRound i) (bfCreator i) j = false,
    payload := () }

def bf30 : BlockUniverse (Fin 4) (Fin 30) Unit where
  ids := Finset.univ
  block := bfBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The split references at rounds `1` and `4`, and the full round elsewhere.
example : (bf30.block 4).refs = {1, 2, 3, 28} := by decide
example : (bf30.block 5).refs = {0, 1, 2, 3} := by decide
example : (bf30.block 16).refs = {13, 14, 15, 29} := by decide
example : (bf30.block 17).refs = {12, 13, 14, 15} := by decide
example : (bf30.block 29).refs = {8, 9, 10, 11} := by decide
example : (bf30.block 24).refs = {20, 21, 22, 23} := by decide

-- Every block sits at round `6` or below.
theorem bf30_round_le : ∀ b : Fin 30, (bf30.block b).round ≤ 6 := by decide

/-! ## The two Byzantine-led slots: two votes each way, no quorum either way -/

-- Slot `0`'s candidates are blocks `0` and `28`, each voted for by two validators at round `1`.
example : ∀ L : Fin 30, IsLeaderBlock bf30 0 L ↔ L = 0 ∨ L = 28 := by decide
example : (blocksAt bf30 1).filter (fun q => MahiMahi.Votes bf30 q 0) = {5, 7} := by decide
example : (blocksAt bf30 1).filter (fun q => MahiMahi.Votes bf30 q 28) = {4, 6} := by decide
example : MahiMahi.certificates bf30 3 0 0 = ∅ := by decide
example : MahiMahi.certificates bf30 3 28 0 = ∅ := by decide

-- Slot `3`'s candidates are blocks `12` and `29`, each voted for by two validators at round `4`.
example : ∀ L : Fin 30, IsLeaderBlock bf30 3 L ↔ L = 12 ∨ L = 29 := by decide
example : (blocksAt bf30 4).filter (fun q => MahiMahi.Votes bf30 q 12) = {17, 19} := by decide
example : (blocksAt bf30 4).filter (fun q => MahiMahi.Votes bf30 q 29) = {16, 18} := by decide
example : MahiMahi.certificates bf30 3 12 3 = ∅ := by decide
example : MahiMahi.certificates bf30 3 29 3 = ∅ := by decide

/-- Neither candidate of slot `0` is directly committed, and the slot is not directly skipped. -/
theorem bf30_slot0_direct :
    (∀ L, IsLeaderBlock bf30 0 L →
      ¬ (steelheadAnchored (Fin 4) (Fin 30) Unit w3).Commit bf30 (View.full bf30) L 0) ∧
    ¬ (steelheadAnchored (Fin 4) (Fin 30) Unit w3).Skip bf30 (View.full bf30) bfSlots 0 := by
  decide

/-- Neither candidate of slot `3` is directly committed, and the slot is not directly skipped. -/
theorem bf30_slot3_direct :
    (∀ L, IsLeaderBlock bf30 3 L →
      ¬ (steelheadAnchored (Fin 4) (Fin 30) Unit w3).Commit bf30 (View.full bf30) L 3) ∧
    ¬ (steelheadAnchored (Fin 4) (Fin 30) Unit w3).Skip bf30 (View.full bf30) bfSlots 3 := by
  decide

/-! ## The honest-led slot above the floor commits -/

-- Slot `4`'s candidate is block `17` (round `4`, author `1`); the whole of round `6` certifies it.
example : IsLeaderBlock bf30 4 17 := by decide
example : MahiMahi.certificates bf30 3 17 4 = {24, 25, 26, 27} := by decide

theorem bf30_slot4 : Steelhead.Decided w3 bf30 (View.full bf30) 4 (some 17) :=
  Decided.directCommit (by decide) (by decide)

/-! ## The floor is undecided, so the slot below it waits -/

/-- Slot `6`'s candidate is block `24`, whose certificate round the universe lacks. -/
theorem bf30_slot6_direct : ∀ L, IsLeaderBlock bf30 6 L →
    ¬ (steelheadAnchored (Fin 4) (Fin 30) Unit w3).Commit bf30 (View.full bf30) L 6 := by
  decide

/-- Eligibility at the constant wave: an anchor of slot `k` is a slot at round `k + 3` or above. -/
theorem bf30_eligible_iff (k j : ℕ) :
    (steelheadAnchored (Fin 4) (Fin 30) Unit w3).Eligible (S := bfSlots) k j ↔ k + 3 ≤ j := by
  rw [AnchoredRule.eligible_iff]
  simp only [zero_lt_one, Nat.div_one, Fin.mk.injEq, forall_eq', imp_self, implies_true,
    Slots.uniform_slotRound, one_mul]
  change k + (3 - 1) + 1 ≤ j ↔ k + 3 ≤ j
  omega

/-- **No slot at round `6` or above commits**: at `6` the certificate round is missing, above `6`
there is no leader block, and an indirect commit rests on an anchor above, which has none. -/
theorem bf30_not_commit_above {j : ℕ} (hj : 6 ≤ j) (A : Fin 30) :
    ¬ Steelhead.Decided w3 bf30 (View.full bf30) j (some A) := by
  intro h
  have hlead : ∀ {j' : ℕ} {A' : Fin 30}, IsLeaderBlock bf30 j' A' → j' ≤ 6 := by
    intro j' A' hA'
    have h1 := bf30_round_le A'
    have h2 : (bf30.block A').round = j' := by simpa using hA'.2.1
    omega
  cases h with
  | directCommit hL hc =>
    have := hlead hL
    obtain rfl : j = 6 := by omega
    exact bf30_slot6_direct A hL hc
  | indirectCommit hkj he hj' _ _ _ _ _ _ =>
    have := hlead (AnchoredRule.isLeaderBlock_of_decided hj')
    omega

/-- **Slot `3` is undecided**: neither direct verdict holds, and any anchor lies at round `6` or
above, where nothing commits. -/
theorem bf30_slot3_undecided (v : Option (Fin 30)) :
    ¬ Steelhead.Decided w3 bf30 (View.full bf30) 3 v := by
  intro h
  cases h with
  | directCommit hL hc => exact bf30_slot3_direct.1 _ hL hc
  | directSkip hs => exact bf30_slot3_direct.2 hs
  | indirectCommit hkj he hj' _ _ _ _ _ _ =>
    exact bf30_not_commit_above ((bf30_eligible_iff _ _).mp he) _ hj'
  | indirectSkip hkj he hj' _ _ =>
    exact bf30_not_commit_above ((bf30_eligible_iff _ _).mp he) _ hj'

/-- **Slot `0` is undecided**: neither direct verdict holds, and any anchor is slot `3`, which
is undecided, or lies above it, which needs slot `3` skipped. -/
theorem bf30_slot0_undecided (v : Option (Fin 30)) :
    ¬ Steelhead.Decided w3 bf30 (View.full bf30) 0 v := by
  intro h
  cases h with
  | directCommit hL hc => exact bf30_slot0_direct.1 _ hL hc
  | directSkip hs => exact bf30_slot0_direct.2 hs
  | indirectCommit hkj he hj' hmid _ _ _ _ _ =>
    have h3 := (bf30_eligible_iff _ _).mp he
    rcases Nat.eq_or_lt_of_le h3 with rfl | hlt
    · exact bf30_slot3_undecided _ hj'
    · exact bf30_slot3_undecided none
        (hmid 3 (by omega) hlt ((bf30_eligible_iff _ _).mpr le_rfl))
  | indirectSkip hkj he hj' hmid _ =>
    have h3 := (bf30_eligible_iff _ _).mp he
    rcases Nat.eq_or_lt_of_le h3 with rfl | hlt
    · exact bf30_slot3_undecided _ hj'
    · exact bf30_slot3_undecided none
        (hmid 3 (by omega) hlt ((bf30_eligible_iff _ _).mpr le_rfl))

/-! ## The chain of floors on data, and the schedule that bounds it -/

/-- **Slot `6` is undecided**: its certificate round is missing, round `7` holds no blame, and
any anchor lies at round `9` or above, where nothing commits. -/
theorem bf30_slot6_undecided (v : Option (Fin 30)) :
    ¬ Steelhead.Decided w3 bf30 (View.full bf30) 6 v := by
  intro h
  cases h with
  | directCommit hL hc => exact bf30_slot6_direct _ hL hc
  | directSkip hs => exact absurd hs (by decide)
  | indirectCommit hkj he hj' _ _ _ _ _ _ =>
    exact bf30_not_commit_above (by have := (bf30_eligible_iff _ _).mp he; omega) _ hj'
  | indirectSkip hkj he hj' _ _ =>
    exact bf30_not_commit_above (by have := (bf30_eligible_iff _ _).mp he; omega) _ hj'

/-- **Two hops of the floor chain** (SH6g's `FloorHop`): the anchor search leaves slot `0` at its
floor `3`, which the view does not skip, and leaves slot `3` at its floor `6`, which it does not
skip either. Nothing lies between a slot and its floor at the constant wave `3`, so neither hop
passes over a skipped slot. -/
theorem bf30_floor_hops :
    Steelhead.FloorHop w3 bf30 (View.full bf30) 0 3 ∧
      Steelhead.FloorHop w3 bf30 (View.full bf30) 3 6 := by
  have hw : ∀ r, w3 r = 3 := fun _ => rfl
  exact ⟨⟨by have := hw 0; omega, fun _ h1 h2 => absurd h2 (by have := hw 0; omega),
      bf30_slot3_undecided none⟩,
    ⟨by have := hw 3; omega, fun _ h1 h2 => absurd h2 (by have := hw 3; omega),
      bf30_slot6_undecided none⟩⟩

/-- **Every landing is led by the Byzantine validator**, so SH6g's last hypothesis, a reliably led
landing, fails at each hop. That is the whole distance between this universe and SH6g's
conclusion: the chain exists and hops twice, and slot `0` is still undecided. -/
theorem bf30_landings_byzantine :
    bfSlots.leader 3 = 0 ∧ bfSlots.leader 6 = 0 ∧ (0 : Fin 4) ∉ (Correct : Finset (Fin 4)) := by
  decide

/-! ### The round-robin schedule (SH6h)

What bounds the chain is the schedule, and `RoundRobinFairRun` reads no DAG at all. At `n = 4`
with the reliable set `{1, 2, 3}` its side condition `c · (n − |T|) < n` holds up to `c = 3` and
fails at `c = 4`, and so does the run itself: every four consecutive rounds hold one led by
validator `0`. The synchronous wave `3` clears the bound at the `3f + 1` committee and the
asynchronous wave `4` does not, which is why the asynchronous rounds rest on the coin. -/

/-- The implementation's known schedule at `n = 4`: round `r` is led by `r mod 4`. -/
abbrev rrSchedule : Slots (Fin 4) := Slots.identity fun r => ⟨r % 4, Nat.mod_lt r (by omega)⟩

/-- The reliable set of the witness committee, a quorum of three. -/
abbrev rrT : Finset (Fin 4) := {1, 2, 3}

-- The side condition of SH6h's first half at the synchronous wave, and its failure at wave `4`.
example : 3 * (4 - rrT.card) < 4 := by decide
example : ¬ (4 * (4 - rrT.card) < 4) := by decide

/-- **Three consecutive rounds led by the reliable set**, past every round: rounds `4m + 1` to
`4m + 3`. This is SH6h's first half on data, at the `c` the synchronous wave asks for. -/
theorem rr_fairRun_three : FairRunOn (S := rrSchedule) rrT 3 := by
  have hmem : ∀ m : Fin 4, m.val ≠ 0 → m ∈ rrT := by decide
  intro k
  refine ⟨4 * k + 1, by omega, fun i hi => hmem _ ?_⟩
  change (4 * k + 1 + i) % 4 ≠ 0
  omega

/-- **No four consecutive rounds are**: one of any four rounds is `0 mod 4`, validator `0`'s.
The bound `c · (n − |T|) < n` is tight here, so the asynchronous wave is not covered. -/
theorem rr_not_fairRun_four : ¬ FairRunOn (S := rrSchedule) rrT 4 := by
  intro h
  obtain ⟨k', _, hk⟩ := h 0
  have h0 := hk ((4 - k' % 4) % 4) (by omega)
  have hz : rrSchedule.leader (k' + (4 - k' % 4) % 4) = (0 : Fin 4) := by
    apply Fin.ext
    change (k' + (4 - k' % 4) % 4) % 4 = 0
    omega
  rw [hz] at h0
  exact absurd h0 (by decide)

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms bf30
#print axioms bf30_slot4
#print axioms bf30_slot0_undecided
#print axioms bf30_floor_hops
#print axioms rr_fairRun_three

end LeanDagTest
