import LeanDag.DoS.Novelty
import LeanDag.DoS.Composition
import LeanDagTest.DoS.Density
import LeanDagTest.DoS.Doubling
import LeanDag.Network.Quorum
/-!
# The novelty budget, witnessed

`dos-equivocation-and-growth.md` §6. Three witnesses, per the §8 house
rule — the definitions get data before anything leans on them.

**The shape of the reveal (`Udouble`).** Against the correct bystander's
view — the 27 correct blocks — the reveal block 41 carries **fifteen novel
blocks**, all fifteen of them Byzantine and most of them at round 0, where
a correct tip whose cone is already held carries exactly **one**. Every
`κ` from 1 to 14 therefore defers the reveal and never defers a correct
block. Antitonicity on data: after absorbing branch N (block 39's cone),
the reveal's novelty drops from 15 to 8 — trickling is possible, but each
step is paid for.

**The telescope (`Utwin`, `Udouble`).** `StepNovelty Utwin 5` holds and
`StepNovelty Utwin 4` fails (block 8's forced merge costs exactly 5), so
the bound `|H| ≤ 5r + 1` is applied at its edge: `9 ≤ 11`. On `Udouble`
the correct chains step by exactly `2f+1 = 9` and the telescope is tight:
`|H(30)| = 19 = 9·2 + 1`.

**The budget over a real `Delivery` (`Dtwin`).** The delivery schedule in
which every correct validator accepts the correct blocks of each round —
and validators 1 and 2 accepted one half of the equivocation each at
round 0 — satisfies the author-blind `UniformBudget Dtwin 3` and the
sharp `ByzBudget Dtwin 0`: no Byzantine block is ever
accepted after round 0 (`κ = 0`), and the dearest correct acceptance costs
3 (`Κ = 3`): block 6 charges validator 1 for itself, for the correct
genesis 2 it never held (the D25 miss), *and* for the equivocation half 4
it carries — the pre-`R` divergence and the Byzantine freight both ride
in on correct carriers, priced inside `Κ`, which is the hysteresis
threshold doing exactly its §6 job. The C3 lemmas then apply with
`R = 1`: the round-0 gap between validators 3 and 1
is precisely the Byzantine half `{0}` that validator 1 accepted and
validator 3 never saw — the gap *is* the budget's spend, on data.
-/

namespace LeanDagTest

open LeanDag

/-! ## The shape of the reveal -/

/-- The correct bystander's view after rounds 0, 1, 2 of `Udouble`. -/
def dblV0 : Finset (Fin 42) := {4, 5, 6, 7, 8, 9, 10, 11, 12}
def dblV1 : Finset (Fin 42) := dblV0 ∪ {17, 18, 19, 20, 21, 22, 23, 24, 25}
def dblV2 : Finset (Fin 42) := dblV1 ∪ {30, 31, 32, 33, 34, 35, 36, 37, 38}

set_option maxRecDepth 2048 in
/-- **Novelty at depth**: the reveal delivers fifteen never-public blocks
at once — the four extra geneses, the second helper genesis, every
Byzantine connector, and itself. -/
theorem udouble_reveal_novelty :
    novelty Udouble dblV2 41 =
      {41, 39, 40, 26, 27, 28, 29, 0, 1, 2, 3, 13, 14, 15, 16} := by decide

set_option maxRecDepth 2048 in
example : (novelty Udouble dblV2 41).card = 15 := by decide

-- A correct tip whose cone the view already holds costs exactly one.
set_option maxRecDepth 2048 in
example : novelty Udouble dblV1 30 = {30} := by decide

set_option maxRecDepth 2048 in
-- Antitone on data: absorb branch N (block 39's cone) and the reveal's
-- price drops from 15 to 8. Deferral is a rate limiter, not a verdict.
example : (novelty Udouble (dblV2 ∪ history Udouble 39) 41).card = 8 := by
  decide

/-! ## The telescope -/

-- `Utwin`: the forced merge (block 8 takes both halves' carriers) costs
-- exactly 5, so `StepNovelty` holds at 5 and fails at 4 — the constant is
-- the data's, not slack.
example : StepNovelty Utwin 5 := by decide
example : ¬ StepNovelty Utwin 4 := by decide

/-- The telescope applied at its edge: `|H(8)| = 9 ≤ 5·2 + 1`. -/
example : (history Utwin 8).card ≤ 5 * (Utwin.block 8).round + 1 :=
  card_history_le_of_stepNovelty (by decide) (by decide) (by decide)

example : (history Utwin 8).card = 9 := by decide

set_option maxRecDepth 2048 in
/-- On `Udouble` the correct chains step by exactly `2f+1 = 9`… -/
theorem udouble_stepNovelty : StepNovelty Udouble 9 := by decide

set_option maxRecDepth 2048 in
/-- …and the telescope is **tight**: `|H(30)| = 19 = 9·2 + 1`. -/
example : (history Udouble 30).card = 9 * (Udouble.block 30).round + 1 := by
  decide

example : (history Udouble 30).card ≤ 9 * (Udouble.block 30).round + 1 :=
  card_history_le_of_stepNovelty udouble_stepNovelty (by decide) (by decide)

/-! ## A delivery schedule for `Utwin` -/

/-- Who accepted what, per round: validators 1 and 2 each accepted one
half of validator 0's equivocation at round 0 (spending their D25 miss
budget on excluding each other); everyone accepts every correct block;
nothing Byzantine is accepted after round 0. -/
def twinAcc (v : Fin 4) (n : ℕ) : Finset (Fin 9) :=
  if n = 0 then
    if v = 1 then {0, 1, 3}
    else if v = 2 then {2, 3, 4}
    else if v = 3 then {1, 2, 3}
    else ∅
  else if n = 1 then if v = 0 then ∅ else {5, 6, 7}
  else if n = 2 then if v = 0 then ∅ else {8}
  else ∅

private theorem twinAcc_eq_empty {v : Fin 4} {n : ℕ} (h0 : ¬n = 0)
    (h1 : ¬n = 1) (h2 : ¬n = 2) : twinAcc v n = ∅ := by
  simp [twinAcc, h0, h1, h2]

private theorem twin_round_le : ∀ b : Fin 9, (Utwin.block b).round ≤ 2 := by
  decide

/-- The delivery layer of the story `LeanDagTest/Density.lean` tells:
`held = accepted` (nothing arrives that is not built on), and the two
adopters never see each other's half before the merge. -/
def Dtwin : Delivery Utwin where
  held := twinAcc
  held_spec := by
    intro v n i hi
    by_cases h0 : n = 0
    · subst h0
      exact (by decide : ∀ v : Fin 4, ∀ i ∈ twinAcc v 0,
        i ∈ Utwin.ids ∧ (Utwin.block i).round = 0) v i hi
    by_cases h1 : n = 1
    · subst h1
      exact (by decide : ∀ v : Fin 4, ∀ i ∈ twinAcc v 1,
        i ∈ Utwin.ids ∧ (Utwin.block i).round = 1) v i hi
    by_cases h2 : n = 2
    · subst h2
      exact (by decide : ∀ v : Fin 4, ∀ i ∈ twinAcc v 2,
        i ∈ Utwin.ids ∧ (Utwin.block i).round = 2) v i hi
    · rw [twinAcc_eq_empty h0 h1 h2] at hi
      exact absurd hi (Finset.notMem_empty i)
  accepted := twinAcc
  accepted_sub := fun _ _ => Finset.Subset.refl _
  accepted_inj := by
    intro v n i hi j hj hij
    by_cases h0 : n = 0
    · subst h0
      exact (by decide : ∀ v : Fin 4, ∀ i ∈ twinAcc v 0, ∀ j ∈ twinAcc v 0,
        (Utwin.block i).creator = (Utwin.block j).creator → i = j) v i hi j hj hij
    by_cases h1 : n = 1
    · subst h1
      exact (by decide : ∀ v : Fin 4, ∀ i ∈ twinAcc v 1, ∀ j ∈ twinAcc v 1,
        (Utwin.block i).creator = (Utwin.block j).creator → i = j) v i hi j hj hij
    by_cases h2 : n = 2
    · subst h2
      exact (by decide : ∀ v : Fin 4, ∀ i ∈ twinAcc v 2, ∀ j ∈ twinAcc v 2,
        (Utwin.block i).creator = (Utwin.block j).creator → i = j) v i hi j hj hij
    · rw [twinAcc_eq_empty h0 h1 h2] at hi
      exact absurd hi (Finset.notMem_empty i)
  accepts_correct := fun _ _ _ a ha _ => ha
  includes := by
    intro v hv n b hb hbc hbr
    by_cases h0 : n = 0
    · subst h0
      exact (by decide : ∀ v : Fin 4, v ∈ (Correct : Finset (Fin 4)) →
        ∀ b ∈ Utwin.ids, (Utwin.block b).creator = v →
        (Utwin.block b).round = 1 → twinAcc v 0 ⊆ (Utwin.block b).refs)
        v hv b hb hbc hbr
    by_cases h1 : n = 1
    · subst h1
      exact (by decide : ∀ v : Fin 4, v ∈ (Correct : Finset (Fin 4)) →
        ∀ b ∈ Utwin.ids, (Utwin.block b).creator = v →
        (Utwin.block b).round = 2 → twinAcc v 1 ⊆ (Utwin.block b).refs)
        v hv b hb hbc hbr
    · exfalso
      have := twin_round_le b
      omega

/-! ## The budget, satisfied on data -/

/-- **The author-blind cap, satisfied**: every acceptance of the schedule —
correct or Byzantine, no creator guard anywhere — costs at most 3, and the
dearest one costs exactly that: block 6 charges validator 1 for itself,
for the missed genesis 2, and for the equivocation half 4 it carries. The
Byzantine freight rides in on correct carriers, priced — the C3 story. -/
theorem dtwin_uniform : UniformBudget Dtwin 3 := by
  intro v hv n b hb
  by_cases h0 : n = 0
  · subst h0
    exact (by decide : ∀ v ∈ (Correct : Finset (Fin 4)),
      ∀ b ∈ Dtwin.accepted v 1,
        (novelty Utwin (viewUpto Dtwin v 0) b).card ≤ 3) v hv b hb
  by_cases h1 : n = 1
  · subst h1
    exact (by decide : ∀ v ∈ (Correct : Finset (Fin 4)),
      ∀ b ∈ Dtwin.accepted v 2,
        (novelty Utwin (viewUpto Dtwin v 1) b).card ≤ 3) v hv b hb
  · exfalso
    rw [show Dtwin.accepted v (n + 1) = twinAcc v (n + 1) from rfl,
      twinAcc_eq_empty (by omega) (by omega) (by omega)] at hb
    exact absurd hb (Finset.notMem_empty b)

/-- The analysis side at its sharpest: nothing Byzantine is ever accepted
after round 0, so the Byzantine clause holds with `κ = 0` — every
acceptance from round 1 on is correct-authored. -/
theorem dtwin_byz : ByzBudget Dtwin 0 := by
  intro v hv n b hb hbc
  by_cases h0 : n = 0
  · subst h0
    exact absurd ((by decide : ∀ v : Fin 4, ∀ b ∈ Dtwin.accepted v 1,
      (Utwin.block b).creator ∈ (Correct : Finset (Fin 4))) v b hb) hbc
  by_cases h1 : n = 1
  · subst h1
    exact absurd ((by decide : ∀ v : Fin 4, ∀ b ∈ Dtwin.accepted v 2,
      (Utwin.block b).creator ∈ (Correct : Finset (Fin 4))) v b hb) hbc
  · rw [show Dtwin.accepted v (n + 1) = twinAcc v (n + 1) from rfl,
      twinAcc_eq_empty (by omega) (by omega) (by omega)] at hb
    exact absurd hb (Finset.notMem_empty b)

-- The forward sandwich: the guard-free cap discharges the guarded form.
example : ByzBudget Dtwin 3 := dtwin_uniform.byzBudget

/-- Delivery is complete from round 1 on: the network misses only the
pre-`R` geneses (validator 1 never held correct genesis 2, validator 2
never held 1 — the D25 exclusions). -/
theorem dtwin_delivers : EventuallyDelivers Dtwin 1 := by
  intro n hn v hv a ha har hac
  by_cases h1 : n = 1
  · subst h1
    exact (by decide : ∀ v ∈ (Correct : Finset (Fin 4)), ∀ a ∈ Utwin.ids,
      (Utwin.block a).round = 1 →
      (Utwin.block a).creator ∈ (Correct : Finset (Fin 4)) →
      a ∈ Dtwin.held v 1) v hv a ha har hac
  by_cases h2 : n = 2
  · subst h2
    exact (by decide : ∀ v ∈ (Correct : Finset (Fin 4)), ∀ a ∈ Utwin.ids,
      (Utwin.block a).round = 2 →
      (Utwin.block a).creator ∈ (Correct : Finset (Fin 4)) →
      a ∈ Dtwin.held v 2) v hv a ha har hac
  · exfalso
    have := twin_round_le a
    omega

/-! ## C3, applied -/

example : (viewUpto Dtwin 3 2).card = 9 := by decide

/-! The C3 chain on data. The gap between validator 1 and validator 3 at
round 0 is precisely `{0}` — the Byzantine half validator 1 accepted and
validator 3 never saw. The gap **is** the budget's spend. -/

example : viewGap Dtwin 3 1 0 = {0} := by decide
example : viewGap Dtwin 1 3 1 = ∅ := by decide

/-- C3a applied: at `n = 1 ≥ R`, the merge block 8 (built from validator
3's acceptances) costs validator 1 at most the gap plus one — here the
gap is empty and the bound is tight: `1 ≤ 0 + 1`. -/
example : (novelty Utwin (viewUpto Dtwin 1 1) 8).card ≤
    (viewGap Dtwin 1 3 1).card + 1 :=
  card_novelty_le_viewGap_add_one (v := 1) (w := 3) dtwin_delivers (le_refl 1)
    (by decide) (by decide) (by decide)

example : (novelty Utwin (viewUpto Dtwin 1 1) 8).card = 1 := by decide

/-! ## The collapse, the derived threshold, and the capstone -/

/-- The reference discipline: every correct block of `Utwin` references
exactly what its author accepted. -/
theorem dtwin_refsAccepted : RefsAccepted Dtwin := by
  intro w hw n b hb hbc hbr
  by_cases h0 : n = 0
  · subst h0
    exact (by decide : ∀ w ∈ (Correct : Finset (Fin 4)), ∀ b ∈ Utwin.ids,
      (Utwin.block b).creator = w → (Utwin.block b).round = 1 →
      (Utwin.block b).refs ⊆ Dtwin.accepted w 0) w hw b hb hbc hbr
  by_cases h1 : n = 1
  · subst h1
    exact (by decide : ∀ w ∈ (Correct : Finset (Fin 4)), ∀ b ∈ Utwin.ids,
      (Utwin.block b).creator = w → (Utwin.block b).round = 2 →
      (Utwin.block b).refs ⊆ Dtwin.accepted w 1) w hw b hb hbc hbr
  · exfalso
    have := twin_round_le b
    omega

/-- Production to the horizon `N = 1`, read off the layout directly. -/
theorem utwin_populated : ∀ r ≤ 1, Populated Utwin r := by
  intro r hr
  interval_cases r <;>
    exact fun v hv => (by decide : ∀ v ∈ (Correct : Finset (Fin 4)),
      ∃ b ∈ Utwin.ids, (Utwin.block b).creator = v ∧
        (Utwin.block b).round = _) v hv

/-! ## B4 on data — the pool, and full asynchrony -/

-- The global Byzantine pool is exactly the two accepted equivocation
-- halves, and with `κ = 0` it freezes there: nothing Byzantine ever
-- enters a correct view again.
example : byzPool Dtwin 0 = {0, 4} := by decide
example : byzPool Dtwin 2 = {0, 4} := by decide

/-- **B4 applied** — the unconditional bound, no synchrony hypothesis
anywhere: `3·3 + (3·1 + 0) = 12` against the actual 9. -/
example : (viewUpto Dtwin 3 2).card ≤
    (Correct : Finset (Fin 4)).card * (2 + 1) +
      ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
        2 * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 0))) :=
  card_viewUpto_le dtwin_byz dtwin_refsAccepted (by decide) 2

/-- **The unconditional capstone applied**: liveness and linear storage
under full asynchrony — `EventuallyDelivers` appears nowhere. -/
example : (∀ r ≤ 1, Populated Utwin r) ∧
    ∀ v ∈ (Correct : Finset (Fin 4)), ∀ n,
      (viewUpto Dtwin v n).card ≤
        (Correct : Finset (Fin 4)).card * (n + 1) +
          ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
            n * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 0))) :=
  populated_and_card_viewUpto_le utwin_populated dtwin_byz
    dtwin_refsAccepted

/-- **The headline applied** — `dos_resistance` from enforceable conditions
only: growth, quorum delivery, the author-blind cap at `T = 3`, and the
reference discipline. Nothing in the hypotheses consults an identity. -/
example : (∀ r ≤ 1, Populated Utwin r) ∧
    ∀ v ∈ (Correct : Finset (Fin 4)), ∀ n,
      (viewUpto Dtwin v n).card ≤
        (Correct : Finset (Fin 4)).card * (n + 1) +
          ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
            n * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 3))) :=
  dos_resistance utwin_populated dtwin_uniform
    dtwin_refsAccepted

/-! ## The composition — the pool freezes -/

/-- Exposure-complete on data: every correct round-2 block's cone exposes
the lone Byzantine author (the merge block 8, exposed to validator 0). -/
theorem utwin_allExposed : AllExposed Utwin 1 := by decide

/-- **B5 applied** — both conditions composed: from round `m+1 = 2` on,
validator 1's view is the correct production plus the **frozen** pool —
`9 ≤ 3·3 + 2`. The Byzantine term has stopped growing. -/
example : (viewUpto Dtwin 1 2).card ≤
    (Correct : Finset (Fin 4)).card * (2 + 1) + (byzPool Dtwin 2).card :=
  card_viewUpto_le_of_allExposed utwin_dosValid dtwin_refsAccepted
    utwin_allExposed (by decide) (le_refl 2)
    (fun _r h1 h2 => (by omega : False).elim)

example : (byzPool Dtwin 2).card = 2 := by decide

/-- B5 with the budget's explicit constant: `9 ≤ 9 + (3 + 0)`. -/
example : (viewUpto Dtwin 1 2).card ≤
    (Correct : Finset (Fin 4)).card * (2 + 1) +
      ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
        (1 + 1) * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 0))) :=
  card_viewUpto_le_of_allExposed' utwin_dosValid dtwin_byz dtwin_refsAccepted
    utwin_allExposed (by decide) (le_refl 2)
    (fun _r h1 h2 => (by omega : False).elim)

#print axioms dtwin_uniform
#print axioms udouble_reveal_novelty
#print axioms udouble_stepNovelty

end LeanDagTest
