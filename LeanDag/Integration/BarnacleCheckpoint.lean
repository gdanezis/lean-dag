import LeanDag.Barnacle.Helpers.Agreement
import LeanDag.Checkpoint.CommitProofs

/-!
# Checkpoints over Barnacle runs

A Barnacle validator decides each configuration's slots against that
configuration's schedule (`Run.closed`), and slots are numbered per
configuration. The bridge therefore applies one configuration at a
time: the rule's schedule is the configuration's, and the VM is the one
for that configuration. `Barnacle.configAgree` makes every online
correct validator's configuration `c` the same, `anchor_agree` its
range, and `vdct_agree` its verdict; its own `closed` clause is then the
settled-on-its-own-view hypothesis `CommitFinalized` asks for. The
boundary is any, so the segmented adaptive run (`Adaptive.SegRun`) is
covered as Barnacle's is. Nothing is added to the checkpoint layer.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Checkpoint LeanDag.Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type} {Value : Type*}
variable {R : BaseRule Validator BlockId Payload} {Par : Params} {B : Boundary Validator}
variable {upd : UpdateRule R} {C₀ : Config Validator} {U : R.Universe}
variable (M : SigningFaults Validator) (E : M.Execution Value)
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

/-- **Barnacle runs finalize a checkpoint**, one configuration at a time.
One run per validator on its own view, closed past configuration `c`;
the rule's schedule is the configuration's as any one run holds it, and
what that run commits at a slot of the configuration's range, every
online correct validator proposes. -/
theorem commitFinalized_barnacle (ha : Agree R.toDagRule) (hanc : Anchored R upd)
    {C : Config Validator}
    (P : SigningFaults.Execution.SigningRule M E R.toDagRule C.sched U vm)
    {K : ℕ} (Rn : ∀ v, Run R Par B upd C₀ U (P.view v) K)
    {c : ℕ} (hc : c < K) {v₀ : Validator} (hcfg : (Rn v₀).cfg c = C)
    {κ : ℕ} {L : BlockId} (h : (Rn v₀).vdct c κ = some L)
    (hlo : (Rn v₀).start c < C.roundOf κ)
    (hhi : C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor c)) :
    Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit κ L)) := by
  have commit : R.Decided C.sched (P.view v₀) κ (some L) := by
    have hd := (Rn v₀).closed c hc κ (by rw [hcfg]; exact hlo) (by rw [hcfg]; exact hhi)
    rwa [h, hcfg] at hd
  refine SigningFaults.Execution.commitFinalized M E vm ha _ P commit ?_
  intro v _
  have hagree := configAgree ha hanc (Rn v) (Rn v₀) c (by omega)
  have hanc' := anchor_agree ha (Rn v) (Rn v₀) hagree hc hc
  obtain ⟨hs, hcfg', -⟩ := hagree
  have hlo' : (Rn v).start c < ((Rn v).cfg c).roundOf κ := by rw [hs, hcfg', hcfg]; exact hlo
  have hhi' : ((Rn v).cfg c).roundOf κ ≤ ((Rn v).cfg c).roundOf ((Rn v).anchor c) := by
    rw [hcfg', hanc', hcfg]; exact hhi
  have hv := vdct_agree ha (Rn v) (Rn v₀) hcfg' hc hc hlo' hhi'
    (by rw [hcfg]; exact hlo) (by rw [hcfg]; exact hhi)
  have hd := (Rn v).closed c hc κ hlo' hhi'
  rw [hv, h, hcfg', hcfg] at hd
  exact ⟨L, hd⟩

end Integration

end LeanDag
