import LeanDagTest.Barnacle.Agreement
import LeanDagTest.Adaptive.Asynchronous
import LeanDag.Integration.BarnacleCheckpoint

/-!
# Checkpoints over Barnacle and segmented runs, on data

`commitFinalized_barnacle` applied to two concrete runs of Mysticeti on
four validators, one per boundary.

* **Barnacle** (`Boundary.atAnchor`): `run2` and `run2'` on `Usun`
  (`LeanDagTest/Barnacle/Agreement.lean`), under the AIMD rule.
  Validator `2` holds the view `Vsun'` without block `31`, and the
  others hold the full view `Vsun`. Slot `5`, the anchor of
  configuration `0`, commits block `21` and is finalized.
* **Adaptive** (`Boundary.atThreshold`): `segRun` on `Usk`
  (`LeanDagTest/Adaptive/Asynchronous.lean`), under the constant rule.
  Slot `3` commits block `15`. Configuration `2` outputs it, and
  configuration `0` decides it above its own boundary without
  outputting it. The bridge finalizes the same checkpoint from either
  configuration.

The fault model has three reliable, available signers `0`, `1`, `2` at
quorum `3`. Validator `3` is Byzantine and proposes a forked checkpoint,
which has no certificate. The VM maps slot `κ` and block `L` to height
`κ + 1`, with the history listing the block of every slot below `κ`
followed by `L`. Agreement makes that history the same on every view.
-/

namespace LeanDagTest

namespace BarnacleCheckpoint

open LeanDag LeanDag.Barnacle LeanDag.Checkpoint LeanDag.Integration
open LeanDagTest.Barnacle LeanDagTest.Adaptive

/-- Signers `0`, `1`, `2` are reliable and available; validator `3` is not. -/
def faults : SigningFaults (Fin 4) where
  q := 3
  reliableSigner := {0, 1, 2}
  recoveryCorrect := {0, 1, 2}
  alive := {0, 1, 2}
  recoveryCorrect_subset_alive := subset_refl _
  intersect := by decide
  reach := by decide

/-- The checkpoint validator `3` proposes instead of the committed one. -/
def forked : CheckpointData ℕ where
  height := 1
  epoch := 0
  history := [99]

section Ledger

variable (S : Slots (Fin 4)) (U : BlockUniverse (Fin 4) (Fin 32) Unit)

open Classical in
/-- The block some view commits at slot `κ`, and `0` if no view commits
one there. -/
noncomputable def slotBlock (κ : ℕ) : ℕ :=
  if h : ∃ (V : View (Fin 4) (Fin 32) Unit U) (L : Fin 32),
      bnRule32.Decided S V κ (some L) then
    (Classical.choose (Classical.choose_spec h)).val
  else 0

variable {S U} in
/-- By agreement, every view that commits slot `κ` commits `slotBlock κ`. -/
theorem slotBlock_eq {V : View (Fin 4) (Fin 32) Unit U} {κ : ℕ} {L : Fin 32}
    (h : bnRule32.Decided S V κ (some L)) : slotBlock S U κ = L.val := by
  have hex : ∃ (V : View (Fin 4) (Fin 32) Unit U) (L : Fin 32),
      bnRule32.Decided S V κ (some L) := ⟨V, L, h⟩
  rw [slotBlock, dif_pos hex]
  exact congrArg Fin.val (Option.some.inj
    (agree32 S _ _ κ _ _ (Classical.choose_spec (Classical.choose_spec hex)) h))

/-- The history at height `h`: the blocks of slots `0` to `h - 1`. -/
noncomputable def ledger (h : ℕ) : List ℕ := (List.range h).map (slotBlock S U)

/-- Executing block `L` at slot `κ` appends `L` to the history of the
slots below `κ`. -/
noncomputable def ledgerVM : DeterministicVM (BlockId := Fin 32) (Value := ℕ) where
  checkpointAfterCommit := fun κ L =>
    { height := κ + 1, epoch := 0, history := ledger S U κ ++ [L.val] }

variable (view : Fin 4 → View (Fin 4) (Fin 32) Unit U)

/-- A reliable signer proposes the checkpoint of every slot its own view
commits. Validator `3` proposes `forked`. -/
noncomputable def execution : faults.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ h => ledger S U h
  emitted := fun m =>
    (m.sender ∈ faults.alive ∧ ∃ κ L,
      bnRule32.Decided S (view m.sender) κ (some L) ∧
        m.checkpoint = (ledgerVM S U).checkpointAfterCommit κ L) ∨
    (m.sender = 3 ∧ m.checkpoint = forked)
  recorded := fun v c =>
    v ∈ faults.recoveryCorrect ∧ ∃ κ L,
      bnRule32.Decided S (view v) κ (some L) ∧ c = (ledgerVM S U).checkpointAfterCommit κ L
  genesis_prefix := fun _ _ => List.nil_prefix
  local_extension := by
    intro _ _ h₁ h₂ _ le
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
    rw [ledger, ledger, List.range_add, List.map_append]
    exact List.prefix_append _ _
  emitted_from_state := by
    rintro ⟨v, c⟩ (⟨_, κ, L, hd, rfl⟩ | ⟨rfl, -⟩) hv
    · simp [ledgerVM, ledger, List.range_succ, slotBlock_eq hd]
    · exact absurd hv (by decide : (3 : Fin 4) ∉ faults.reliableSigner)
  local_height := by
    rintro ⟨v, c⟩ (⟨_, κ, L, hd, rfl⟩ | ⟨rfl, -⟩) hv
    · simp [ledgerVM, ledger]
    · exact absurd hv (by decide : (3 : Fin 4) ∉ faults.reliableSigner)

/-- The signing rule of this execution, at the views `view`. -/
noncomputable def signingRule :
    SigningFaults.Execution.SigningRule faults (execution S U view) bnRule32.toDagRule
      S U (ledgerVM S U) where
  quorum := by decide
  view := view
  proposes := fun v hv _ _ hd => Or.inl ⟨hv, _, _, hd, rfl⟩
  witnesses := by
    intro v hv c he Q
    refine ⟨{ sender := v, certificate := Q, recorded := fun hv' => ⟨hv', ?_⟩ }, rfl⟩
    rcases he with ⟨-, h⟩ | ⟨h3, -⟩
    · exact h
    · exact absurd (h3 ▸ hv : (3 : Fin 4) ∈ faults.alive) (by decide)

/-- `forked` has no first-phase certificate: only validator `3` proposes
it, two signers short of the quorum. -/
theorem forked_uncertified :
    IsEmpty (SigningFaults.Execution.CheckpointQC faults (execution S U view) forked) := by
  refine ⟨fun Q => ?_⟩
  have hsub : Q.signers ⊆ {3} := by
    intro v hv
    rcases Q.messages v hv with ⟨-, κ, L, -, hc⟩ | ⟨h3, -⟩
    · simp only [forked, ledgerVM, CheckpointData.mk.injEq] at hc
      obtain ⟨hκ, -, hh⟩ := hc
      obtain rfl : κ = 0 := by omega
      simp [ledger] at hh
      omega
    · exact Finset.mem_singleton.mpr h3
  have := Finset.card_le_card hsub
  have := Q.quorum
  simp [faults] at *
  omega

end Ledger

/-! ## Barnacle: two views, at the anchor -/

/-- Validator `2` holds `Vsun'`, the others `Vsun`. -/
def sunView (v : Fin 4) : View (Fin 4) (Fin 32) Unit Usun :=
  if v = 2 then Vsun' else Vsun

/-- One run per validator, on its own view. -/
def sunRuns : ∀ v, PartialRun bnRule32 bnP bnUpd32 bnC1 Usun (sunView v) 1
  | ⟨0, _⟩ => run2
  | ⟨1, _⟩ => run2
  | ⟨2, _⟩ => run2'
  | ⟨3, _⟩ => run2

/-- **Slot `5`, the anchor of configuration `0`, is finalized.** -/
theorem sun_finalized :
    Nonempty (SigningFaults.Execution.FinalityQC faults
      (execution bnC1.sched Usun sunView)
      ((ledgerVM bnC1.sched Usun).checkpointAfterCommit 5 21)) :=
  commitFinalized_barnacle faults _ _ agree32 (fun _ _ _ _ _ _ _ => rfl)
    (signingRule bnC1.sched Usun sunView) sunRuns (c := 0) (by decide) (v₀ := 0) rfl
    (κ := 5) (L := 21) rfl (by decide) (by decide)

/-- The same slot, read from validator `2`'s run on the smaller view. -/
example :
    Nonempty (SigningFaults.Execution.FinalityQC faults
      (execution bnC1.sched Usun sunView)
      ((ledgerVM bnC1.sched Usun).checkpointAfterCommit 5 21)) :=
  commitFinalized_barnacle faults _ _ agree32 (fun _ _ _ _ _ _ _ => rfl)
    (signingRule bnC1.sched Usun sunView) sunRuns (c := 0) (by decide) (v₀ := 2) rfl
    (κ := 5) (L := 21) rfl (by decide) (by decide)

/-- The finalized history lists the blocks of slots `1` to `4` that the
run commits. -/
example : ((ledgerVM bnC1.sched Usun).checkpointAfterCommit 5 21).history =
    [slotBlock bnC1.sched Usun 0, 5, 10, 15, 16, 21] := by
  have h : ∀ κ (L : Fin 32), bnRule32.Decided bnC1.sched Vsun κ (some L) →
      slotBlock bnC1.sched Usun κ = L.val := fun _ _ => slotBlock_eq
  simp only [ledgerVM, ledger, List.range_succ, List.range_zero, List.map_append,
    List.map_nil, List.map_cons, List.nil_append]
  rw [h 1 5 (Decided.directCommit (S := bnC1.sched) (by decide) (by decide)),
    h 2 10 (Decided.directCommit (S := bnC1.sched) (by decide) (by decide)),
    h 3 15 (Decided.directCommit (S := bnC1.sched) (by decide) (by decide)),
    h 4 16 (Decided.directCommit (S := bnC1.sched) (by decide) (by decide))]
  rfl

example : IsEmpty (SigningFaults.Execution.CheckpointQC faults
    (execution bnC1.sched Usun sunView) forked) :=
  forked_uncertified _ _ _

/-! ## Adaptive: a segmented run, at the threshold -/

/-- Every validator holds the full view of `Usk` and runs `segRun`. -/
def skView : Fin 4 → View (Fin 4) (Fin 32) Unit Usk := fun _ => View.full Usk

/-- **Slot `3` is finalized from configuration `2`**, whose range outputs it. -/
theorem sk_finalized :
    Nonempty (SigningFaults.Execution.FinalityQC faults
      (execution bnC1I1.sched Usk skView)
      ((ledgerVM bnC1I1.sched Usk).checkpointAfterCommit 3 15)) :=
  commitFinalized_barnacle faults _ _ agree32 (fun _ _ _ _ _ _ _ => rfl)
    (signingRule bnC1I1.sched Usk skView) (fun _ => segRun) (c := 2) (by decide) (v₀ := 0)
    rfl (κ := 3) (L := 15) rfl (by decide) (by decide)

-- Configuration `0` decides slot `3` above its boundary and does not output it.
example : bnC1I1.roundOf 3 > segRun.start 1 ∧ (15 : Fin 32) ∉ segRun.rangeLedger 0 := by
  decide

/-- **The same checkpoint from configuration `0`.** The bridge reads the
decision, not the output range. -/
example :
    Nonempty (SigningFaults.Execution.FinalityQC faults
      (execution bnC1I1.sched Usk skView)
      ((ledgerVM bnC1I1.sched Usk).checkpointAfterCommit 3 15)) :=
  commitFinalized_barnacle faults _ _ agree32 (fun _ _ _ _ _ _ _ => rfl)
    (signingRule bnC1I1.sched Usk skView) (fun _ => segRun) (c := 0) (by decide) (v₀ := 0)
    rfl (κ := 3) (L := 15) rfl (by decide) (by decide)

#print axioms sun_finalized
#print axioms sk_finalized

end BarnacleCheckpoint

end LeanDagTest
