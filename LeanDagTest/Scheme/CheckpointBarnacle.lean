import LeanDagTest.Scheme.Checkpoint
import LeanDagTest.Barnacle.Model

/-!
# Checkpoints over a leader-scheduling run of the unified decider

`commitFinalized_barnacle_scheme` applied to a concrete run: the scheme's
rule at the Mysticeti row as a Barnacle base rule, on `U7`, in the
configuration `bnC1I1` (one leader per round, interval one) under the
constant update rule. The run closes configuration `0` at slot `2`; slots
`1` and `2` commit blocks `5` and `10` and are finalized. This is
`run1c` of `LeanDagTest/Barnacle/Agreement.lean` with the base rule
replaced by `schemeBase myst σL`, so the theorem's hypotheses, an
`Anchored` update rule and a run at the scheme's base rule, are met
together.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme LeanDag.Checkpoint LeanDag.Integration
open LeanDag.Barnacle LeanDagTest.Barnacle

/-- The scheme's rule at the Mysticeti row, as a Barnacle base rule. -/
abbrev schedBase : BaseRule (Fin 4) (Fin 24) Unit := schemeBase myst σL

/-- The run: configuration `0` decides slots `1` and `2` and is closed by
slot `2`; the constant rule leaves the configuration unchanged. -/
def schedRun : PartialRun schedBase bnPI1 (constRule schedBase) bnC1I1 U7 V7 1 where
  start := fun k => if k = 0 then 0 else 2
  cfg := fun _ => bnC1I1
  backoff := fun _ => 0
  anchor := fun _ => 2
  vdct := vd1
  init := ⟨rfl, rfl, rfl⟩
  bounds := fun _ => ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), by decide, by decide⟩
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one, if_true] at h1 h2
    have : κ = 1 ∨ κ = 2 := by omega
    rcases this with rfl | rfl
    · exact AnchoredRule.Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · exact AnchoredRule.Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨10, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one, if_true] at h
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    rfl

open Classical in
/-- The block some view commits at slot `κ` of the configuration's
schedule, and `0` if no view commits one there. -/
noncomputable def schedBlock (κ : ℕ) : ℕ :=
  if h : ∃ (V : View (Fin 4) (Fin 24) Unit U7) (L : Fin 24),
      (schemeRule myst σL).Decided bnC1I1.sched V κ (some L) then
    (Classical.choose (Classical.choose_spec h)).val
  else 0

/-- By agreement, every view that commits slot `κ` commits `schedBlock κ`. -/
theorem schedBlock_eq {V : View (Fin 4) (Fin 24) Unit U7} {κ : ℕ} {L : Fin 24}
    (h : (schemeRule myst σL).Decided bnC1I1.sched V κ (some L)) :
    schedBlock κ = L.val := by
  have hex : ∃ (V : View (Fin 4) (Fin 24) Unit U7) (L : Fin 24),
      (schemeRule myst σL).Decided bnC1I1.sched V κ (some L) := ⟨V, L, h⟩
  rw [schedBlock, dif_pos hex]
  exact congrArg Fin.val (Option.some.inj
    (Scheme.agree u7Tolerates bnC1I1.sched _ _ κ _ _
      (Classical.choose_spec (Classical.choose_spec hex)) h))

/-- The history at height `h`: the blocks of slots `0` to `h - 1`. -/
noncomputable def schedLedger (h : ℕ) : List ℕ := (List.range h).map schedBlock

/-- Executing block `L` at slot `κ` appends `L` to the history of the
slots below `κ`. -/
noncomputable def schedVM : DeterministicVM (BlockId := Fin 24) (Value := ℕ) where
  checkpointAfterCommit := fun κ L =>
    { height := κ + 1, epoch := 0, history := schedLedger κ ++ [L.val] }

/-- A rule-following validator proposes the checkpoint of every slot its
view commits under the configuration's schedule. -/
noncomputable def schedExecution : u7Signing.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ h => schedLedger h
  emitted := fun m =>
    m.sender ∈ u7Signing.alive ∧ ∃ κ L,
      (schemeRule myst σL).Decided bnC1I1.sched V7 κ (some L) ∧
        m.checkpoint = schedVM.checkpointAfterCommit κ L
  recorded := fun v c =>
    v ∈ u7Signing.recoveryCorrect ∧ ∃ κ L,
      (schemeRule myst σL).Decided bnC1I1.sched V7 κ (some L) ∧
        c = schedVM.checkpointAfterCommit κ L
  genesis_prefix := fun _ _ => List.nil_prefix
  local_extension := by
    intro _ _ h₁ h₂ _ le
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
    rw [schedLedger, schedLedger, List.range_add, List.map_append]
    exact List.prefix_append _ _
  emitted_from_state := by
    rintro ⟨v, c⟩ ⟨_, κ, L, hd, rfl⟩ _
    simp [schedVM, schedLedger, List.range_succ, schedBlock_eq hd]
  local_height := by
    rintro ⟨v, c⟩ ⟨_, κ, L, hd, rfl⟩ _
    simp [schedVM, schedLedger]

/-- The signing rule at the configuration's schedule; every validator
holds `V7`. -/
noncomputable def schedSigning :
    SigningFaults.Execution.SigningRule u7Signing schedExecution schedBase.toDagRule
      bnC1I1.sched U7 schedVM where
  quorum := by decide
  view := fun _ => V7
  proposes := fun _ hv _ _ hd => ⟨hv, _, _, hd, rfl⟩
  witnesses := fun v _ _ he Q =>
    ⟨{ sender := v
       certificate := Q
       recorded := fun hv' => ⟨hv', he.2⟩ },
     rfl⟩

/-- **Slot `2`, the anchor of configuration `0`, is finalized.** -/
theorem sched_finalized :
    Nonempty (SigningFaults.Execution.FinalityQC u7Signing schedExecution
      (schedVM.checkpointAfterCommit 2 10)) :=
  commitFinalized_barnacle_scheme u7Signing schedExecution schedVM u7Tolerates
    (fun _ _ _ _ _ _ _ => rfl) schedSigning (fun _ => schedRun) (c := 0) (by decide)
    (v₀ := 0) rfl (κ := 2) (L := 10) rfl (by decide) (by decide)

/-- And slot `1`, below the anchor. -/
example :
    Nonempty (SigningFaults.Execution.FinalityQC u7Signing schedExecution
      (schedVM.checkpointAfterCommit 1 5)) :=
  commitFinalized_barnacle_scheme u7Signing schedExecution schedVM u7Tolerates
    (fun _ _ _ _ _ _ _ => rfl) schedSigning (fun _ => schedRun) (c := 0) (by decide)
    (v₀ := 0) rfl (κ := 1) (L := 5) rfl (by decide) (by decide)

/-- The finalized history lists the blocks the run commits. -/
example : (schedVM.checkpointAfterCommit 2 10).history = [schedBlock 0, 5, 10] := by
  have h1 : schedBlock 1 = 5 :=
    schedBlock_eq (schedRun.closed 0 (by decide) 1 (by decide) (by decide))
  simp [schedVM, schedLedger, List.range_succ, h1]

#print axioms sched_finalized

end Scheme

end LeanDagTest
