import LeanDagTest.Barnacle.Model
import LeanDagTest.Barnacle.Rules.Odontoceti.Proof
import LeanDagTest.Barnacle.Rules.Nemo.Proof
import LeanDag.Barnacle.Aimd.Proof
import LeanDagTest.Nemo.Model
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
/-!
# Barnacle witnesses — the two-round rules on data

Odontoceti, the paper's Blue Bottle, on the six-validator model of
`LeanDagTest/Odontoceti/Model.lean` (`Uodo`, four sunny rounds;
`Uskip`, with a direct skip and an indirect commit). What this file
exhibits:

* the window count under the two-round rule: on `Uodo` with the anchor
  at round `3` and a three-round interval, two rounds score at every
  count, against an expected `(3 − 2 + 1) · m` — where Mysticeti's
  three-round wave scored one; the wave length is read off the rule;
* Odontoceti's own `Good` on `Uodo`, and its descent law yielding a
  committed slot through `Odontoceti.holds`;
* the laws through `Odontoceti.holds`: agreement of two views' verdicts
  on `Uskip`; and its `indirect` descent law doing the work — the
  indirect commit of `Uskip`'s slot `1` off its anchor, and on a twin
  universe where both twins of a Byzantine leader pass the thick-link
  test at the slot's actual anchor, the *least* twin committed and the
  greater refused.

Nemo-Nemo on the three-validator model of `LeanDagTest/Nemo.lean`
(`Unemo`: validator `2` halts after round `1`):

* the window count under the crash rule: with the anchor at round `4`
  and a three-round interval, one slot scores at count `1` — the
  crashed validator's round has no candidate, and the round below the
  anchor has one supporter in the window — against an expected two: the
  window is unhealthy, the count holds at the floor and the back-off
  moves, the mechanism reacting to a halt;
* Nemo's own `Good` on `Unemo` over the live pair `{0, 1}`, a majority
  of three, and the descent law at the majority slack yielding a
  committed slot through `Nemo.holds` — with no fault class consumed
  beyond `Good`;
* the laws through `Nemo.holds`, with no fault class at all; `Good` on
  `Unemo` fails one round past the universe; and the arithmetic of the
  majority slack — `n − majority = (n − 1) / 2`, equal to `f` exactly
  at `n = 2f + 1` and `n = 2f + 2`. `Majority.lean` then attacks the
  slack on a DAG good over a bare majority with an adversarial live
  validator outside it.
-/

namespace LeanDagTest

namespace Barnacle

set_option maxRecDepth 2048

open LeanDag LeanDag.Barnacle

/-- Odontoceti over the six-validator committee. -/
abbrev bnOdo : BaseRule (Fin 6) (Fin 24) Unit := odontoceti

/-- Round-robin on six validators, keyed up to six. -/
def bnLeader6' : ℕ → Fin 6 := roundRobin 6 (by omega)

theorem bnWin6' : Keyed bnLeader6' 6 := roundRobin_keyed 6 (by omega)

/-- At most six leaders and a three-round interval. -/
def bnPo : Params := ⟨6, 3, 96, 100, by decide⟩

def bnLead6' : ℕ → ℕ → Fin 6 := leadOf bnLeader6'

theorem bnLeadKeyed6' : LeadKeyed bnLead6' 6 := leadKeyed_of_keyed (by omega) bnWin6'

/-- The configuration at count `m`, three-round interval. -/
def bnCfgO (m : ℕ) (hm : 0 < m) (hmax : m ≤ 6) : Config (Fin 6) :=
  Config.uniform bnLead6' bnLeadKeyed6' m hm hmax 3

abbrev bnCO1 : Config (Fin 6) := bnCfgO 1 (by decide) (by decide)
abbrev bnCO3 : Config (Fin 6) := bnCfgO 3 (by decide) (by decide)
abbrev bnCO6 : Config (Fin 6) := bnCfgO 6 (by decide) (by decide)

theorem bnCO6_head : bnCO6.head = bnLeader6' := by funext ρ; rfl

/-! ## The window count at wave length two -/

-- Anchor `20` (round `3`, author `2`); the window is rounds `0` to `3`.
-- Rounds `0` and `1` score: their supporters, at rounds `1` and `2`, are
-- all in the anchor's history; round `2`'s only supporter in the window
-- is the anchor itself.
example : observed bnOdo bnCO1 Uodo 20 = 2 := by decide
example : observed bnOdo bnCO3 Uodo 20 = 6 := by decide
example : expected bnOdo bnCO1 3 = 2 := by decide
example : expected bnOdo bnCO3 3 = 6 := by decide
example : (Aimd.rule bnOdo bnPo bnLead6' bnLeadKeyed6' bnCO1 0 Uodo
    (View.full Uodo) 20).1.slotsAt 0 = 2 := by decide
example : (Aimd.rule bnOdo bnPo bnLead6' bnLeadKeyed6' bnCO6 0 Uodo
    (View.full Uodo) 20).1.slotsAt 0 = 6 := by decide

/-! ## Odontoceti's `Good` on `Uodo`, and its descent law -/

theorem odoCorrect : (Correct : Finset (Fin 6)) = {1, 2, 3, 4, 5} := by decide

/-- The model's own synchrony from round `0`, over the correct set. -/
theorem uodo_sync : SynchronisedOn Uodo {1, 2, 3, 4, 5} 1 := by
  rw [← odoCorrect]
  exact fun n hn => uodo_synchronised n (by omega)

theorem uodo_good :
    (odontocetiLive (Validator := Fin 6) (BlockId := Fin 24) (Payload := Unit)).Good Uodo 1 3 :=
  ⟨{1, 2, 3, 4, 5}, ⟨by decide, by decide⟩, uodo_sync, fun r h1 h2 => by
    interval_cases r <;> decide⟩

/-- Through `Odontoceti.holds`: the good set commits a round-`1` slot.
`goodLeaders` bounds `T` by cardinality only — five of six — so no
validator can be assumed in it; at count `6` every validator leads a
slot of round `1`, and a member of `T` leads one of them. -/
example : ∃ κ, bnCO6.sched.slotRound κ = 1 ∧
    ∃ L, bnOdo.Decided bnCO6.sched (View.full Uodo) κ (some L) := by
  obtain ⟨T, hcard, hT0⟩ :=
    (Odontoceti.holds.2.1 (Fin 6) (Fin 24) Unit).goodLeaders Uodo 1 3 uodo_good
  have hT := fun S κ => hT0 S (View.full Uodo) κ
    (coversUpto_full (Odontoceti.holds.1 (Fin 6) (Fin 24) Unit).full_ids Uodo 3)
  have h5 : 5 ≤ T.card := by
    have h := hcard
    simp only [Fintype.card_fin] at h
    change 6 ≤ T.card + 1 at h
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  fin_cases v
  · exact ⟨11, by decide, hT _ 11 (by decide) (by decide) hv⟩
  · exact ⟨6, by decide, hT _ 6 (by decide) (by decide) hv⟩
  · exact ⟨7, by decide, hT _ 7 (by decide) (by decide) hv⟩
  · exact ⟨8, by decide, hT _ 8 (by decide) (by decide) hv⟩
  · exact ⟨9, by decide, hT _ 9 (by decide) (by decide) hv⟩
  · exact ⟨10, by decide, hT _ 10 (by decide) (by decide) hv⟩

/-! ## The laws, on `Uskip` -/

/-- Agreement through `Odontoceti.holds`: the direct skip of slot `0`
and any verdict on any view agree. -/
example : ∀ (V : View (Fin 6) (Fin 36) Unit Uskip) (v : Option (Fin 36)),
    (odontoceti (Validator := Fin 6) (BlockId := Fin 36) (Payload := Unit)).Decided odoSlots
      V 0 v →
    v = none := fun V v h =>
  (Odontoceti.holds.1 (Fin 6) (Fin 36) Unit).agree odoSlots V (View.full Uskip) 0 v none h
    uskip_slot0

/-! ## The `indirect` law, on `Uskip` and on twins -/

abbrev O36 : BaseRule (Fin 6) (Fin 36) Unit := odontoceti

/-- `indirect` at `uskip_slot1`'s slot: anchor slot 3 (block 21), nothing eligible between. -/
theorem uskip_indirect : ∃ v, O36.Decided odoSlots (View.full Uskip) 1 v ∧ v = some 7 := by
  obtain ⟨v, hv⟩ := (Odontoceti.holds.2.1 (Fin 6) (Fin 36) Unit).indirect odoSlots
    (View.full Uskip) 1 3 21 (by decide) uskip_slot3
    (fun i' h1 h2 h3 => by
      simp only [odoSlots_slotRound] at h3
      change 1 + 2 ≤ i' at h3
      omega)
  exact ⟨v, hv, (Odontoceti.holds.1 (Fin 6) (Fin 36) Unit).agree odoSlots _ _ 1 v (some 7) hv
    uskip_slot1⟩

/-- `Utwin6` with the slot-2 leader block `15` referencing all of round 1. -/
def twinBlk' : Fin 25 → Block (Fin 6) (Fin 25) Unit := fun i =>
  if (i : ℕ) = 15 then
    { round := 2, creator := 2, refs := {7, 8, 9, 10, 11, 12}, payload := () }
  else twinBlk i

def Utwin6' : BlockUniverse (Fin 6) (Fin 25) Unit where
  ids := Finset.univ
  block := twinBlk'
  complete := by decide
  valid := by decide
  no_equivocation := by decide

abbrev O25 : BaseRule (Fin 6) (Fin 25) Unit := odontoceti

theorem twin'_slot2 : Odontoceti.Decided Utwin6' (View.full Utwin6') 2 (some 15) :=
  Odontoceti.Decided.directCommit (by decide) (by decide)

-- Slot 1 is not committed (its candidate is block 8; nothing at round 2 in
-- `Utwin6'` is decided directly for slot 1? — only what matters: slot 2 is the
-- first eligible slot, so the intermediate premise is vacuous).

/-- At the slot's *actual* anchor both twins pass. -/
theorem twin'_both_pass_at_anchor :
    Odontoceti.ThickLink Utwin6' 15 0 0 ∧ Odontoceti.ThickLink Utwin6' 15 6 0 := by
  constructor <;> decide

/-- The arc's `indirect` law yields a verdict for slot 0 … -/
theorem twin'_indirect : ∃ v, O25.Decided odoSlots (View.full Utwin6') 0 v :=
  (Odontoceti.holds.2.1 (Fin 6) (Fin 25) Unit).indirect odoSlots (View.full Utwin6') 0 2 15
    (by decide) twin'_slot2
    (fun i' h1 h2 h3 => by
      simp only [odoSlots_slotRound] at h3
      change 0 + 2 ≤ i' at h3
      omega)

/-- … and by hand the least twin commits: the `¬ L' < 0` clause is trivial. -/
theorem twin'_slot0 : Odontoceti.Decided Utwin6' (View.full Utwin6') 0 (some 0) :=
  Odontoceti.Decided.indirectCommit (i := 0) (by omega) (by decide) twin'_slot2
    (fun i h1 h2 h3 => by
      have : i = 1 := by omega
      subst this
      exact absurd h3 (by decide))
    (by decide) (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide)
    (fun _ _ _ hlt => absurd (show _ < (0 : Fin 25) from hlt) (Nat.not_lt_zero _))

/-- So the law's verdict is the least twin, and the greater twin is refused. -/
theorem twin'_least :
    (∃ v, O25.Decided odoSlots (View.full Utwin6') 0 v ∧ v = some 0) ∧
      ¬ O25.Decided odoSlots (View.full Utwin6') 0 (some 6) := by
  obtain ⟨v, hv⟩ := twin'_indirect
  refine ⟨⟨v, hv, (Odontoceti.holds.1 (Fin 6) (Fin 25) Unit).agree odoSlots _ _ 0 v (some 0) hv
    twin'_slot0⟩, fun h => ?_⟩
  have := (Odontoceti.holds.1 (Fin 6) (Fin 25) Unit).agree odoSlots _ _ 0 _ _ h twin'_slot0
  simp at this

#print axioms uskip_indirect
#print axioms twin'_least

/-! ## Nemo-Nemo on `Unemo` -/

/-- Nemo-Nemo over three validators; no fault class. -/
abbrev bnNemo : BaseRule (Fin 3) (Fin 14) Unit := nemo

def bnLeader3 : ℕ → Fin 3 := roundRobin 3 (by omega)

theorem bnWin3 : Keyed bnLeader3 3 := roundRobin_keyed 3 (by omega)

/-- At most three leaders and a three-round interval. -/
def bnPn : Params := ⟨3, 3, 96, 100, by decide⟩

def bnLead3 : ℕ → ℕ → Fin 3 := leadOf bnLeader3

theorem bnLeadKeyed3 : LeadKeyed bnLead3 3 := leadKeyed_of_keyed (by omega) bnWin3

/-- The configuration at count `m`, three-round interval. -/
def bnCfgN (m : ℕ) (hm : 0 < m) (hmax : m ≤ 3) : Config (Fin 3) :=
  Config.uniform bnLead3 bnLeadKeyed3 m hm hmax 3

abbrev bnCN1 : Config (Fin 3) := bnCfgN 1 (by decide) (by decide)
abbrev bnCN3 : Config (Fin 3) := bnCfgN 3 (by decide) (by decide)

-- Anchor `11` (round `4`, author `1`); window rounds `1` to `4`. Round `1`
-- scores (block `4`, both round-`2` blocks support it); round `2`'s head
-- is the crashed validator's, with no candidate; round `3`'s only
-- supporter in the window is the anchor. One against an expected two:
-- unhealthy, the count stays at the floor and the back-off moves.
example : observed bnNemo bnCN1 Unemo 11 = 1 := by decide
example : expected bnNemo bnCN1 4 = 2 := by decide
example : (Aimd.rule bnNemo bnPn bnLead3 bnLeadKeyed3 bnCN1 0 Unemo
    (View.full Unemo) 11).1.slotsAt 0 = 1 ∧
    (Aimd.rule bnNemo bnPn bnLead3 bnLeadKeyed3 bnCN1 0 Unemo (View.full Unemo) 11).2 = 1 := by
  decide

/-- **BN7d's unhealthy branch, through the theorem.** The one window in
this development that a good DAG fails: `100 · 1 < 96 · 2`, so the rule
takes the *other* step — the count at `count … false`, which at the floor
is the floor, and the back-off moved on. The healthy branch is exercised
on `Usun`; this is the direction that shows the test is a test. -/
example : (Aimd.rule bnNemo bnPn bnLead3 bnLeadKeyed3 bnCN1 0 Unemo
      (View.full Unemo) 11).1.slotsAt = (fun _ => Aimd.count bnPn (bnCN1.slotsAt 4) 0 false) ∧
    (Aimd.rule bnNemo bnPn bnLead3 bnLeadKeyed3 bnCN1 0 Unemo (View.full Unemo) 11).2 = 0 + 1 :=
  let h := (Aimd.holds (Fin 3) (Fin 14) Unit bnNemo bnPn bnLead3 bnLeadKeyed3).2.2.2.1 bnCN1 0
    Unemo (View.full Unemo) 11
  ⟨h.2.2.2.2.1 (by decide), h.2.2.2.2.2 (by decide)⟩

/-- And it carries the leaders and the interval across either way. -/
example : (Aimd.rule bnNemo bnPn bnLead3 bnLeadKeyed3 bnCN1 0 Unemo
      (View.full Unemo) 11).1.lead = bnLead3 ∧
    (Aimd.rule bnNemo bnPn bnLead3 bnLeadKeyed3 bnCN1 0 Unemo
      (View.full Unemo) 11).1.interval = bnCN1.interval :=
  let h := (Aimd.holds (Fin 3) (Fin 14) Unit bnNemo bnPn bnLead3 bnLeadKeyed3).2.2.2.1 bnCN1 0
    Unemo (View.full Unemo) 11
  ⟨h.1, h.2.1⟩
-- At count `3` every validator leads every round: round `1` scores three
-- slots, round `2` two (validator `2` has no block), round `3` none.
example : observed bnNemo bnCN3 Unemo 11 = 5 := by decide
example : expected bnNemo bnCN3 4 = 6 := by decide

/-- The model's own synchrony from round `0`, over the live pair. -/
theorem unemo_sync : SynchronisedOn Unemo {0, 1} 1 := by
  have h : LeanDag.Nemo.Live (Fin 3) = {0, 1} := by decide
  rw [← h]
  exact fun n hn => unemo_synchronised n (by omega)

theorem unemo_good :
    (nemoLive (Validator := Fin 3) (BlockId := Fin 14) (Payload := Unit)).Good Unemo 1 5 :=
  ⟨{0, 1}, ⟨by decide, by decide⟩, unemo_sync, fun r h1 h2 => by interval_cases r <;> decide⟩

-- Not to round `6`: the universe ends at round `5`.
example : ¬ PopulatedOn Unemo {0, 1} 6 := by decide

/-- Through `Nemo.holds`: the good set — two of three, by cardinality
alone — commits a round-`1` slot at count `3`, where every validator
leads one; the crashed validator's round-`1` block is supported too. -/
example : ∃ κ, bnCN3.sched.slotRound κ = 1 ∧
    ∃ L, bnNemo.Decided bnCN3.sched (View.full Unemo) κ (some L) := by
  obtain ⟨T, hcard, hT0⟩ :=
    (Nemo.holds.2.1 (Fin 3) (Fin 14) Unit).goodLeaders Unemo 1 5 unemo_good
  have hT := fun S κ => hT0 S (View.full Unemo) κ
    (coversUpto_full (Nemo.holds.1 (Fin 3) (Fin 14) Unit).full_ids Unemo 5)
  have h2 : 2 ≤ T.card := by
    have h := hcard
    simp only [Fintype.card_fin] at h
    change 3 ≤ T.card + (3 - 2) at h
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  fin_cases v
  · exact ⟨5, by decide, hT _ 5 (by decide) (by decide) hv⟩
  · exact ⟨3, by decide, hT _ 3 (by decide) (by decide) hv⟩
  · exact ⟨4, by decide, hT _ 4 (by decide) (by decide) hv⟩

/-- Agreement through `Nemo.holds`: slot `2`, the crashed validator's,
skips on every view. -/
example : ∀ (V : LeanDag.Nemo.View (Fin 3) (Fin 14) Unit Unemo) (v : Option (Fin 14)),
    bnNemo.Decided nemoSlots V 2 v → v = none := fun V v h =>
  (Nemo.holds.1 (Fin 3) (Fin 14) Unit).agree nemoSlots V (View.full Unemo) 2 v none h
    nemo_slot2

/-! ## `Good` has a horizon, and the slack in numbers -/

/-- The horizon is real for `Good` itself, not just for `PopulatedOn`. -/
theorem unemo_not_good_6 :
    ¬ (nemoLive (Validator := Fin 3) (BlockId := Fin 14) (Payload := Unit)).Good Unemo 1 6 := by
  rintro ⟨T, ⟨-, hcard⟩, -, hpop⟩
  have h2 : 2 ≤ T.card := by
    change Fintype.card (Fin 3) - (Fintype.card (Fin 3) - LeanDag.Nemo.majority (Fin 3))
      ≤ T.card at hcard
    have hmaj : LeanDag.Nemo.majority (Fin 3) = 2 := by decide
    rw [Fintype.card_fin, hmaj] at hcard
    exact hcard
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  obtain ⟨b, -, -, hbr⟩ := hpop 6 (by omega) le_rfl v hv
  have hno : ∀ b : Fin 14, (Unemo.block b).round ≠ 6 := by decide
  exact hno b hbr

/-- On `Unemo`, a good set need not be live, and it never matters: the
non-live majority `{0, 2}` fails `PopulatedOn` at round 2 already. -/
example : ¬ PopulatedOn Unemo {0, 2} 2 := by decide

/-! ### The slack, arithmetically -/

theorem slack_eq (n : ℕ) (hn : 0 < n) :
    n - LeanDag.Nemo.majority (Fin n) = (n - 1) / 2 := by
  unfold LeanDag.Nemo.majority; rw [Fintype.card_fin]; omega

theorem slack_ge_f (n f : ℕ) (h : 2 * f + 1 ≤ n) :
    f ≤ n - LeanDag.Nemo.majority (Fin n) := by
  unfold LeanDag.Nemo.majority; rw [Fintype.card_fin]; omega

theorem slack_eq_f_iff (n f : ℕ) (h : 2 * f + 1 ≤ n) :
    n - LeanDag.Nemo.majority (Fin n) = f ↔ n = 2 * f + 1 ∨ n = 2 * f + 2 := by
  unfold LeanDag.Nemo.majority; rw [Fintype.card_fin]; omega

example : LeanDag.Nemo.majority (Fin 1) = 1 ∧ LeanDag.Nemo.majority (Fin 2) = 2 := by decide
example : 1 - LeanDag.Nemo.majority (Fin 1) = 0 ∧ 2 - LeanDag.Nemo.majority (Fin 2) = 0 := by
  decide
example : 5 - LeanDag.Nemo.majority (Fin 5) = 2 ∧ 6 - LeanDag.Nemo.majority (Fin 6) = 2 := by
  decide

#print axioms LeanDag.Barnacle.Odontoceti.holds
#print axioms LeanDag.Barnacle.Nemo.holds

end Barnacle

end LeanDagTest
