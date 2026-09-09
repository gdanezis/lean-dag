import LeanDag.Mysticeti.Record
import LeanDag.GC.Bootstrap
import LeanDagTest.DoS.Exclusion
/-!
# The bootstrap, witnessed

`garbage.md` P8's data half for G11/G6b/G7/G12, on `Uexcl` — which finally
gets the delivery schedule its six rounds deserve.

**`Dexcl`**: acceptance is *the references of the validator's own next
block*, so `includes` and `RefsAccepted` hold with equality — the honest
protocol exactly. Validator 1 accepted equivocation half `0`; validator 2
accepted half `4`; validator 3 accepted neither.

**G11 on data — the lag is real.** At attestation round 1, half `0` is
carried only by its acceptor's block `5`: one author, the `f+1` filter
drops it, and window block `5` would dangle. One backbone round later
(`t = 2`) every correct cone carries it and it clears the filter. `t ≥
m + 2` is not slack — the witness sits exactly on the boundary.

**G12 on data.** The joiner's assembly at `G = 1`, window frontier `m = 2`,
attestation `t = 4`: base `{5,6,7}` (the correct round-1 layer) plus window
`{8,9,10}` — six blocks, downward closed in the truncation, and any
decision it reaches agrees with any full-history validator's.

**G6b/G7 on data.** The fetch is 6 blocks against the constant 15; the
relay obligation for block `11` is its 7-block truncated cone against the
constant 10.
-/

namespace LeanDagTest

open LeanDag

/-! ## The delivery schedule -/

/-- Who accepted what, per round: the refs of the acceptor's next block
(rounds 0–4), the final round taken whole (round 5 — no next block
constrains it), nothing for the Byzantine validator 0. -/
def exclAcc (v : Fin 4) (n : ℕ) : Finset (Fin 20) :=
  if n = 0 then
    if v = 1 then {0, 1, 2, 3}
    else if v = 2 then {4, 1, 2, 3}
    else if v = 3 then {1, 2, 3}
    else ∅
  else if v = 0 then ∅
  else if n = 1 then {5, 6, 7}
  else if n = 2 then {8, 9, 10}
  else if n = 3 then {11, 12, 13}
  else if n = 4 then {14, 15, 16}
  else if n = 5 then {17, 18, 19}
  else ∅

private theorem exclAcc_eq_empty {v : Fin 4} {n : ℕ} (h : 5 < n) :
    exclAcc v n = ∅ := by
  unfold exclAcc
  by_cases hv : v = 0
  · rw [if_neg (by omega), if_pos hv]
  · rw [if_neg (by omega), if_neg hv, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem excl_round_le : ∀ b : Fin 20, (Uexcl.block b).round ≤ 5 := by
  decide

/-- The honest delivery layer over `Uexcl`: `held = accepted = refs of the
next own block`. -/
def Dexcl : Delivery Uexcl where
  held := exclAcc
  held_spec := by
    intro v n
    by_cases hn : n ≤ 5
    · revert v
      interval_cases n <;> decide
    · intro i hi
      rw [exclAcc_eq_empty (by omega)] at hi
      exact absurd hi (Finset.notMem_empty i)
  accepted := exclAcc
  accepted_sub := fun _ _ => Finset.Subset.refl _
  accepted_inj := by
    intro v n
    by_cases hn : n ≤ 5
    · revert v
      interval_cases n <;> decide
    · intro i hi
      rw [exclAcc_eq_empty (by omega)] at hi
      exact absurd hi (Finset.notMem_empty i)
  accepts_correct := fun _ _ _ a ha _ => ha
  includes := by
    intro v hv n b hb hbc hbr
    by_cases hn : n ≤ 4
    · revert v hv b hb hbc hbr
      interval_cases n <;> decide
    · exfalso
      have := excl_round_le b
      omega

theorem dexcl_refsAccepted : RefsAccepted Dexcl := by
  intro w hw n b hb hbc hbr
  by_cases hn : n ≤ 4
  · revert w hw b hb hbc hbr
    interval_cases n <;> decide
  · exfalso
    have := excl_round_le b
    omega

theorem dexcl_eventuallyDelivers : EventuallyDelivers Dexcl 0 := by
  intro n _
  by_cases hn : n ≤ 5
  · interval_cases n <;> decide
  · intro v hv a ha har hac
    have := excl_round_le a
    omega

/-- Sharp: after round 0 the schedule accepts nothing Byzantine, so the
budget holds at zero. -/
theorem dexcl_byz : ByzBudget Dexcl 0 := by
  intro v hv n
  by_cases hn : n ≤ 4
  · revert v hv
    interval_cases n <;> decide
  · intro b hb
    rw [show Dexcl.accepted v (n + 1) = exclAcc v (n + 1) from rfl,
      exclAcc_eq_empty (by omega)] at hb
    exact absurd hb (Finset.notMem_empty b)

/-! ## G11 on data — nothing obtainable is filtered out -/

-- Validator 1 accepted equivocation half 0 at round 0…
example : (0 : Fin 20) ∈ viewUpto Dexcl 1 0 := by decide

-- …one lag too early the base misses it: at attestation round 1 only
-- carrier 5 (author 1) holds it, and the f+1 filter drops it…
example : (0 : Fin 20) ∉ Base Uexcl 1 0 := by decide

-- …and one backbone round later it clears the filter in every sample.
example : (0 : Fin 20) ∈ Base Uexcl 2 0 := by decide

-- G11 applied: the same membership from the theorem, at its boundary
-- t = m + 2 exactly.
example : (0 : Fin 20) ∈ Base Uexcl 2 0 :=
  accepted_mem_base (D := Dexcl) (v := 1)
    (SynchronisedOn.mono (by decide) uexcl_synchronised)
    (by decide) (by decide) (by decide) (uexcl_populated 1 (by omega))
    (uexcl_populated 2 (by omega)) (by omega) (by omega)

/-! ## G12 on data — the joiner's assembly -/

-- The attested base at G = 1, sampled at t = 4: the correct round-1
-- layer exactly.
example : Base Uexcl 4 1 = {5, 6, 7} := by decide

-- The joiner's fetch: base {5,6,7} plus window {8,9,10} above the cut.
example : joinIds Dexcl 1 2 4 1 = {5, 6, 7, 8, 9, 10} := by decide

-- The assembly is a view of the truncation (closure holds: window blocks
-- 8,9,10 reference {5,6,7}, all caught by the base), with those ids.
example : (joinView (D := Dexcl) (w := 1) (G := 1)
      (SynchronisedOn.mono (by decide) uexcl_synchronised) (by decide)
      (uexcl_populated 3 (by omega)) (uexcl_populated 4 (by omega))
      (by omega) (by omega)).ids = {5, 6, 7, 8, 9, 10} := by decide

/-- **G12 applied.** Whatever the joiner decides for slot 0 of the
truncation at `G = 1` — judging from base plus window alone — matches
whatever any full-history validator decides for slot 1. -/
example {jv fv : Option (Fin 20)}
    (hJ : Decided (S := fairSlots.chop 1 1 (by decide)) (chop Uexcl 1)
      (joinView (D := Dexcl) (w := 1) (G := 1)
        (SynchronisedOn.mono (by decide) uexcl_synchronised) (by decide)
        (uexcl_populated 3 (by omega)) (uexcl_populated 4 (by omega))
        (by omega) (by omega)) 0 jv)
    (hV : Decided Uexcl (View.full Uexcl) 1 fv) : jv = fv :=
  bootstrap_agree MysticetiProperties.onRecord MysticetiProperties.agree
    MysticetiProperties.banded (by decide)
    (SynchronisedOn.mono (by decide) uexcl_synchronised) (by decide)
    (uexcl_populated 3 (by omega)) (uexcl_populated 4 (by omega))
    (by omega) (by omega) hJ hV

/-! ## G6b/G7 on data — the constants -/

-- The fetch: 6 blocks against the G6 constant 3·4 + (3 + 3·0) = 15
-- (κ = 0, Λ = 3).
example : (joinIds Dexcl 1 2 4 1).card = 6 := by decide

example : (joinIds Dexcl 1 2 4 1).card ≤
    (Correct : Finset (Fin 4)).card * (3 + 1) +
      ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
        3 * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 0))) :=
  card_joinIds_le dexcl_byz dexcl_refsAccepted dexcl_eventuallyDelivers
    (by decide) (by omega) (by omega) (by omega) (by omega)

-- The relay obligation for block 11 (validator 1's round-3 block) at
-- G = 1: its truncated cone is 7 blocks against the constant 9 + 1
-- (κ = 0, Λ = 1).
example : (history (chop Uexcl 1) 11).card = 7 := by decide

example : (history (chop Uexcl 1) 11).card ≤
    ((Correct : Finset (Fin 4)).card * (1 + 1) +
      ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
        1 * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 0)))) + 1 :=
  card_serve_le (w := 1) (n := 2) (Λ := 1) dexcl_byz dexcl_refsAccepted
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)

#print axioms accepted_mem_base
#print axioms card_joinIds_le
#print axioms bootstrap_agree
#print axioms card_serve_le

end LeanDagTest
