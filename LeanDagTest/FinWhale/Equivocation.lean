import LeanDagTest.Mysticeti.Growth
import LeanDag.FinWhale.DoSBridge
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
/-!
# FinWhale witnesses — a DoS-valid execution with a real equivocation

`DoSBridge.lean` proves that a DoS-valid universe on the core's reactive
schedule is a `Run`. That theorem is worth only as much as its hypotheses
are jointly satisfiable, and the arc's other reactive execution has no
equivocation at all, so `DoSValid` holds there for want of anything to
forbid. This file exhibits one where the condition is active.

Four validators at `f = 1` and `p = 1`, so `n = 4`; validator `0` is
Byzantine and equivocates at round `0` with blocks `0` and `4`. Round-`1`
blocks split over the twins — `5` and `6` cite `0`, `7` cites `4` — so a
round-`2` block citing two of them reaches both versions and is
**exposed** to validator `0`. Blocks `10`, `11` and `12` are in exactly
that position: each is exposed, and each therefore may not cite `5`, the
equivocator's round-`1` block, though validity would otherwise admit it.
They cite `6`, `7`, `8` instead, and the universe is DoS-valid.

The point is what survives that. The reactive schedule's two citation
obligations are confined to reliable authors, and `citable_of_correct`
says a correct validator is never exposed, so nothing the schedule
demands is anything the condition forbids. `eqReactive` is the
`ReactiveM` over this execution, and `eqRun` is the composite of
`Run.ofDoSValidReactive` — which is therefore not vacuous.
-/

namespace LeanDagTest

namespace FinWhaleEquiv

open LeanDag LeanDag.FinWhale

/-- The fast-path budget: `n + 1 = 3f + 2p = 5`. -/
local instance eqParams : Params (Fin 4) where
  p := 1
  p_pos := by omega
  p_le_f := by decide
  card_add_one := by decide

private def mk (r : ℕ) (c : Fin 4) (rs : Finset (Fin 16)) :
    Block (Fin 4) (Fin 16) Unit :=
  { round := r, creator := c, refs := rs, payload := () }

/-- Sixteen blocks over four rounds. Validator `0` equivocates at round
`0` with `0` and `4`; the round-`1` blocks split over the two, and the
round-`2` blocks by correct validators drop the equivocator. -/
def eqBlk : Fin 16 → Block (Fin 4) (Fin 16) Unit :=
  ![ mk 0 0 ∅,             -- 0   the first twin
     mk 0 1 ∅,             -- 1
     mk 0 2 ∅,             -- 2
     mk 0 3 ∅,             -- 3
     mk 0 0 ∅,             -- 4   the second twin
     mk 1 0 {0, 1, 2, 3},  -- 5   the equivocator, on its first twin
     mk 1 1 {0, 1, 2, 3},  -- 6   sees the first twin only
     mk 1 2 {4, 1, 2, 3},  -- 7   sees the second twin only
     mk 1 3 {1, 2, 3},     -- 8   sees neither
     mk 2 0 {5, 6, 8},     -- 9   still unexposed, so may cite `5`
     mk 2 1 {6, 7, 8},     -- 10  exposed: `6` and `7` carry both twins
     mk 2 2 {6, 7, 8},     -- 11  exposed
     mk 2 3 {6, 7, 8},     -- 12  exposed
     mk 3 1 {10, 11, 12},  -- 13
     mk 3 2 {10, 11, 12},  -- 14
     mk 3 3 {10, 11, 12} ] -- 15

/-- **The universe.** Validity, completeness and non-equivocation of the
correct validators, all by `decide`. -/
def Uequiv : BlockUniverse (Fin 4) (Fin 16) Unit where
  ids := Finset.univ
  block := eqBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The condition, and that it is active -/

/-- **The execution is DoS-valid.** -/
theorem uequiv_dosValid : DoSValid Uequiv := by decide

/-- **And validator `0` really equivocates**: two distinct round-`0`
blocks of its own. -/
example : EquivPair Uequiv 0 0 4 := by decide

/-- **The condition bites.** Block `10` is exposed to the equivocator, so
`DoSValid` forbids it to cite `5` — and it does not, though `5` is a
round-`1` block whose author is not otherwise excluded. -/
example : ExposedIn Uequiv 10 0 ∧ (5 : Fin 16) ∉ (Uequiv.block 10).refs := by decide

/-- **Block `9` is not exposed**, and cites `5` accordingly: the
prohibition is on the blocks that have seen both versions, not on the
author. -/
example : ¬ ExposedIn Uequiv 9 0 ∧ (5 : Fin 16) ∈ (Uequiv.block 9).refs := by decide

/-- **No correct validator is ever exposed**, which is what makes the
reactive obligations compatible with the condition. -/
example : ∀ b : Fin 16, ∀ X : Fin 4, X ∈ (Correct : Finset (Fin 4)) →
    ¬ ExposedIn Uequiv b X := by decide

/-! ## The DAG -/

/-- The leader schedule: one slot a round, validator `k % 4` leading
round `k`, so round `0` is led by the Byzantine validator. -/
@[reducible] def eqSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, Nat.mod_lt _ (by omega)⟩)

attribute [local instance 3000] eqSlots

@[simp] theorem eqSlots_slotRound (k : ℕ) : eqSlots.slotRound k = k := by simp

/-- **The FinWhale DAG**, from the condition alone. -/
def Dequiv : Dag (Fin 4) (Fin 16) Unit :=
  Dag.ofDoSValid Uequiv eqSlots.leader uequiv_dosValid

/-- The self-parent edge comes with it. -/
example : SelfParented Dequiv := selfParented_ofDoSValid uequiv_dosValid

/-- The slot of round `0` holds both twins, and they conflict. -/
example : slotBlocks (Slots.identity eqSlots.leader) Dequiv 0 = {0, 4} ∧ Conflicting Dequiv 0 4 := by decide

/-! ## The reactive schedule over it

A synchronous execution: every reliable validator holds everything at
every instant, enters round `n` at time `n`, and the timeout is one
tick. Nothing here is delicate — the point of the structure is that it
*exists* over a universe where the exposure condition is active. -/

/-- The pacing trunk. -/
def eqPace : PaceCore Uequiv (Correct : Finset (Fin 4)) 3 where
  top := fun _ => 3
  built := fun _ n => n
  timeout := fun _ => 3
  gst := 0
  delay := 0
  proc := 3
  latest := fun n => n
  holds := fun _ _ => Finset.univ
  rounds_le := by decide
  built_of_le_top := by
    intro v hv n hn
    interval_cases n <;> revert v hv <;> decide
  le_top_of_built := by decide
  timeout_pos := fun _ => by omega
  built_le_latest := fun _ _ _ _ => le_refl _
  holds_sub := fun _ _ => by simp [Uequiv]
  holds_closed := fun _ _ _ _ _ _ _ => Finset.mem_univ _
  refs_held := fun _ _ _ _ _ _ _ => Finset.subset_univ _
  holds_own := fun _ _ _ _ _ _ _ _ => Finset.mem_univ _
  holds_mono := fun _ _ _ _ => Finset.Subset.refl _
  converges := fun _ _ _ _ _ _ => Finset.Subset.refl _
  advances := fun _ _ _ hn _ _ => hn
  catchup := fun _ _ n hn _ _ _ _ _ _ _ => ⟨hn, by omega⟩

/-- **The reactive structure.** Both wait clauses hold by their first
disjunct: every correct validator's block references every correct
validator's block of the round below, so it votes, and two rounds up it
certifies. -/
def eqReactive : ReactiveM Uequiv (Correct : Finset (Fin 4)) 3 :=
  { eqPace with
    built_lt := fun _ _ _ _ => by simp [eqPace]
    deadline := fun _ _ _ _ => by simp [eqPace]
    vote_or_wait := by
      intro v hv k hN hlead L hL c hc hcc hcr
      refine Or.inl ?_
      simp only [eqSlots_slotRound] at hN hcr
      obtain ⟨hLids, hLr, hLc⟩ := hL
      simp only [eqSlots_slotRound] at hLr
      have hk : k ≤ 2 := by omega
      interval_cases k <;> revert hlead hLc hLr hcc hcr <;> revert hv <;>
        revert v L c <;> decide
    prompt_vote := by
      intro v _ k _ _ L _ t hbuilt _ _
      simp only [eqSlots_slotRound] at hbuilt ⊢
      show k + 1 ≤ t + 3
      simp only [eqPace] at hbuilt
      omega
    cert_or_wait := by
      intro v hv k hN hlead L hL c hc hcc hcr
      refine Or.inl ?_
      simp only [eqSlots_slotRound] at hN hcr
      obtain ⟨hLids, hLr, hLc⟩ := hL
      simp only [eqSlots_slotRound] at hLr
      have hk : k ≤ 1 := by omega
      interval_cases k <;> revert hlead hLc hLr hcc hcr <;> revert hv <;>
        revert v L c <;> decide }

/-- **The composite.** A DoS-valid universe with a live equivocation, on
the reactive schedule, is a run — so `Run.ofDoSValidReactive` is not
vacuous. -/
noncomputable def eqRun : Run (Fin 4) (Fin 16) Unit :=
  Run.ofDoSValidReactive Uequiv uequiv_dosValid eqReactive (fun k => by simp)
    (by
      refine ⟨Equiv.refl (Fin 4), fun r => ?_⟩
      apply Fin.ext
      show r % 4 = ZMod.val ((r : ZMod 4))
      exact (ZMod.val_natCast (n := 4) r).symm)
    3 (by decide) (fun _ _ _ _ => by simp [eqReactive, eqPace]) 0 (by simp [eqReactive, eqPace])
    (fun n _ => by simp [eqReactive, eqPace])

/-! ## What the protocol does on it

The round-`1` leader is validator `1`, whose block is `6`. It is
committed by both paths — four validators vote for it at round `2`,
which is `n − p = 3` and more, and the three round-`3` blocks each carry
a slow-path quorum of votes among their parents. So the equivocation
costs the execution nothing, which is the whole point of a rule that
counts votes rather than reading the equivocator. -/

example : eqSlots.leader 1 ∈ (Correct : Finset (Fin 4)) := by decide

example : FastCommit Dequiv 6 ∧ SPCommit Dequiv 6 := by decide

example : DirectCommit Dequiv 6 := by decide

/-- And neither twin of the Byzantine slot is committed or skipped: the
rule leaves round `0` undecided directly, as it should. -/
example : ¬ DirectCommit Dequiv 0 ∧ ¬ DirectCommit Dequiv 4 := by decide

/-! ## The condition never exhausts a builder's parents

`quorumCard_le_citable` says the authors a block may cite always include
a validity quorum. Here the bound is met with equality and nothing to
spare: block `10` has convicted validator `0`, the three correct
validators are all that remain, and `n − f = 3` is exactly what validity
asks for — so it cites all three and could not have cited fewer. -/

example : exposedTo Uequiv 10 = {0} ∧ ((exposedTo Uequiv 10)ᶜ).card = 3 := by decide

example : quorumCard (Fin 4) ≤ ((exposedTo Uequiv 10)ᶜ).card :=
  quorumCard_le_citable (by decide)

example : parentSet Dequiv 10 = {1, 2, 3} := by decide

/-! ## The case Lemmas 6 and 7 do not reach

The paper's skip rule has a first condition quantifying over "each leader
block of `s` (if any) in the local DAG of `vj`", and Lemmas 6 and 7 argue
against a commit through it. The case it does not reach is a validator
holding **no** block of the committed slot, where the condition is
satisfied for nothing.

That case is realisable here. Slot `1` is led by validator `1` and its
block `6` is committed in the universe. `Vmiss` is a reference-closed
part of the execution that holds every round-`0` and round-`1` block
except `6` — a validator that has not yet received the committed block —
and in it the slot is empty, so the condition holds with no block to hold
of. -/

/-- Everything below round `2` except the committed block. -/
def Vmiss : Finset (Fin 16) := {0, 1, 2, 3, 4, 5, 7, 8}

/-- As a view of `Dequiv`. -/
def VmissView : Dequiv.View := ⟨Vmiss, by decide, by decide⟩

/-- **The commit is real, and the view holds no block of its slot.** -/
example : DirectCommit Dequiv 6 ∧
    slotBlocks (Slots.identity eqSlots.leader) (VmissView.toRecord) 1 = ∅ := by decide

/-- **So the SP-skip half is satisfied for nothing there** — vacuously,
over an empty slot — which is what leaves the paper's argument without a
block to run on. -/
example : ∀ l ∈ slotBlocks (Slots.identity eqSlots.leader) (VmissView.toRecord) 1,
    SPSkip (VmissView.toRecord) l := by decide

/-- The arc's own exclusions do not go through that condition, and hold
here: no view of this DAG directly skips a slot whose block is
committed. -/
example : ¬ DirectSkip (Slots.identity eqSlots.leader) (VmissView.toRecord) 1 := by decide

/-! ## The horizon

`eqRun` runs to round `3`, which is enough for the liveness interface —
slot `1` is correct-led and committed — and short of the `3f + 5` window
`Run.agreement` asks for. Non-vacuity of the four properties is witnessed
separately, on the tall execution of `Pace.lean`; what this file settles
is that the composite hypothesis of `Run.ofDoSValidReactive` is
satisfiable at all where equivocation is live, which the tall execution
cannot show because nothing equivocates in it. -/

#print axioms eqReactive
#print axioms eqRun

end FinWhaleEquiv

end LeanDagTest
