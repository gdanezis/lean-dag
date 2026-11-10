import LeanDag.Scheme.Properties
import LeanDag.Checkpoint.CommitProofs
import LeanDag.Integration.FaultClasses
import LeanDag.Integration.BarnacleCheckpoint
import LeanDag.Barnacle.Model.Anchored

/-!
# Checkpoints over the unified decider

Instantiates the generic checkpoint bridge (`Checkpoint/CommitSpec.lean`,
`Checkpoint/CommitProofs.lean`) at `schemeRule p σ`.

The bridge needs two facts about the decider, both proved in
`Scheme/Properties.lean`:
- `Scheme.agree`: at a tolerated row, all views commit the same block per slot.
- `familySupport_commits`: production plus certification across a wave forces
  a commit.

Each theorem below supplies these facts and restates the bridge's conclusion
for the scheme. The results hold at every row `p` with `p.Tolerates honest f q`.

Three layers:
- `*_scheme`: the fault model `M : SigningFaults` is a parameter.
- `*_classes`: the fault model is `FaultClasses` (`Integration/FaultClasses.lean`),
  Byzantine, crash-prone and alive-but-corrupt sets at `3f + 2c + fa < n`. The
  row's fault budget is the classes' `f`, the DAG's honest set contains everyone
  outside the Byzantine class, the checkpoint quorum is `n − f − c`, and the
  reliability quorum is discharged, with AbC validators present.
- `commitFinalized_barnacle_scheme`: the bridge over leader-scheduling runs of
  the scheme's rule.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Checkpoint LeanDag.Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type} {Value : Type*}
variable {P : Validity Validator BlockId Payload} [P.Mechanised] {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest}

section Generic

variable (M : SigningFaults Validator) (E : M.Execution Value)
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

/-- Existence: a commit yields a finality certificate.

Inputs: a commit of `block` at `slot` in some view `V`, and a commit of some
block at `slot` in the own view of every rule-following validator (`M.alive`).
Output: a `FinalityQC` for `vm.checkpointAfterCommit slot block`. Its
`checkpointQC` field is the first-phase certificate. -/
theorem commitFinalized_scheme {q f : ℕ} [P.Quorate q] (ht : p.Tolerates honest f q)
    (S : Slots Validator) {U : (schemeRule p σ).Universe}
    (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm)
    {V : (schemeRule p σ).View U} {slot : ℕ} {block : BlockId}
    (commit : (schemeRule p σ).Decided S V slot (some block))
    (hall : ∀ v ∈ M.alive,
      ∃ b, (schemeRule p σ).Decided S (Pr.view v) slot (some b)) :
    Nonempty (SigningFaults.Execution.FinalityQC M E
      (vm.checkpointAfterCommit slot block)) :=
  SigningFaults.Execution.commitFinalized M E vm (Scheme.agree ht) S Pr commit hall

/-- Liveness: a well-formed wave yields a finality certificate, with no
commit assumed.

Inputs, each over the rule-following validators `M.alive`:
- `hlive`: the row's commit threshold fits within the reliable set.
- `hq`: they form a reliability quorum.
- `hpop`: they produce blocks at every round of the slot's wave.
- `hcert`: every candidate for the slot is certified by them.
- `hcov`: each one's view covers the whole wave.
- `hlead`: the slot's leader is one of them.
Output: some candidate `L` commits and gets a `FinalityQC`. -/
theorem liveCommitFinalized_scheme {q f : ℕ} [P.Quorate q] (ht : p.Tolerates honest f q)
    {rel : Reliability Validator}
    (hlive : p.commitThreshold ≤ Fintype.card Validator - rel.slack)
    (S : Slots Validator) {U : (schemeRule p σ).Universe}
    (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm) {slot : ℕ}
    (hq : rel.IsQuorum M.alive)
    (hpop : ∀ n, S.slotRound slot ≤ n →
      n ≤ S.slotRound slot + (familySupport p σ).waveAt (S.kind slot) →
      Properties.PopulatedOn (schemeRule p σ) U M.alive n)
    (hcert : ∀ L, (schemeRule p σ).IsCandidate S U slot L →
      (familySupport p σ).certifiesAt U M.alive (S.slotRound slot)
        (S.kind slot) L)
    (hcov : ∀ v ∈ M.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
      (S.slotRound slot + (familySupport p σ).waveAt (S.kind slot)))
    (hlead : S.leader slot ∈ M.alive) :
    ∃ L, (schemeRule p σ).IsCandidate S U slot L ∧
      Nonempty (SigningFaults.Execution.FinalityQC M E
        (vm.checkpointAfterCommit slot L)) :=
  SigningFaults.Execution.liveCommitFinalized M E vm (familySupport p σ) rel
    (Scheme.agree ht) Scheme.commitsCandidate (familySupport_commits hlive)
    S Pr hq hpop hcert hcov hlead

/-- Uniqueness: two commits for one slot, in any two views, produce the same
checkpoint. Follows from `Scheme.agree` and `vm` being deterministic. -/
theorem checkpointUnique_scheme {q f : ℕ} [P.Quorate q] (ht : p.Tolerates honest f q)
    (S : Slots Validator) {U : (schemeRule p σ).Universe}
    {V₁ V₂ : (schemeRule p σ).View U} {slot : ℕ} {block₁ block₂ : BlockId}
    (commit₁ : (schemeRule p σ).Decided S V₁ slot (some block₁))
    (commit₂ : (schemeRule p σ).Decided S V₂ slot (some block₂)) :
    vm.checkpointAfterCommit slot block₁ = vm.checkpointAfterCommit slot block₂ :=
  commitCheckpointUnique vm (Scheme.agree ht) S commit₁ commit₂

end Generic

/-! ## At the three fault classes

The row and the checkpoint layer read one fault model. `hh` says the DAG's
honest set leaves out Byzantine validators only, so crash-prone and
alive-but-corrupt validators are honest for the decider; the row's fault
budget is then the classes' `f`. -/

section Classes

variable (F : FaultClasses Validator) (E : F.signing.Execution Value)
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

/-- A row covered at the classes' Byzantine bound tolerates the classes. -/
theorem tolerates_of_classes {q : ℕ} (hh : honestᶜ ⊆ F.byzantine)
    (hq : q ≤ Fintype.card Validator) (hcov : p.Covered (Fintype.card Validator) F.f q) :
    p.Tolerates honest F.f q :=
  ⟨le_trans (Finset.card_le_card hh) F.card_byzantine, hq, hcov⟩

/-- Existence at the classes: a commit settled on every rule-following
validator's view yields a finality certificate at the quorum `n − f − c`,
with AbC validators among the signers. -/
theorem commitFinalized_classes {q : ℕ} [P.Quorate q] (hh : honestᶜ ⊆ F.byzantine)
    (hq : q ≤ Fintype.card Validator) (hrow : p.Covered (Fintype.card Validator) F.f q)
    (S : Slots Validator) {U : (schemeRule p σ).Universe}
    (Pr : SigningFaults.Execution.SigningRule F.signing E (schemeRule p σ) S U vm)
    {V : (schemeRule p σ).View U} {slot : ℕ} {block : BlockId}
    (commit : (schemeRule p σ).Decided S V slot (some block))
    (hall : ∀ v ∈ F.signing.alive,
      ∃ b, (schemeRule p σ).Decided S (Pr.view v) slot (some b)) :
    Nonempty (SigningFaults.Execution.FinalityQC F.signing E
      (vm.checkpointAfterCommit slot block)) :=
  commitFinalized_scheme F.signing E vm (tolerates_of_classes F hh hq hrow) S Pr commit hall

/-- Liveness at the classes, with AbC validators present. `hlive` is the
first conjunct of `Params.Live p n f c`; the reliability quorum is
`FaultClasses.isQuorum_alive`. -/
theorem liveCommitFinalized_classes {q : ℕ} [P.Quorate q] (hh : honestᶜ ⊆ F.byzantine)
    (hq : q ≤ Fintype.card Validator) (hrow : p.Covered (Fintype.card Validator) F.f q)
    (hlive : p.commitThreshold ≤ Fintype.card Validator - F.f - F.c)
    (S : Slots Validator) {U : (schemeRule p σ).Universe}
    (Pr : SigningFaults.Execution.SigningRule F.signing E (schemeRule p σ) S U vm) {slot : ℕ}
    (hpop : ∀ n, S.slotRound slot ≤ n →
      n ≤ S.slotRound slot + (familySupport p σ).waveAt (S.kind slot) →
      Properties.PopulatedOn (schemeRule p σ) U F.signing.alive n)
    (hcert : ∀ L, (schemeRule p σ).IsCandidate S U slot L →
      (familySupport p σ).certifiesAt U F.signing.alive (S.slotRound slot)
        (S.kind slot) L)
    (hcov : ∀ v ∈ F.signing.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
      (S.slotRound slot + (familySupport p σ).waveAt (S.kind slot)))
    (hlead : S.leader slot ∈ F.signing.alive) :
    ∃ L, (schemeRule p σ).IsCandidate S U slot L ∧
      Nonempty (SigningFaults.Execution.FinalityQC F.signing E
        (vm.checkpointAfterCommit slot L)) :=
  liveCommitFinalized_scheme F.signing E vm (tolerates_of_classes F hh hq hrow)
    (rel := F.reliability) (by rw [F.reliability_slack]; omega) S Pr F.isQuorum_alive
    hpop hcert hcov hlead

end Classes

/-! ## Over leader-scheduling runs

The scheme's wave is the same at every slot kind, so its anchored rule is a
Barnacle base rule, and `commitFinalized_barnacle` applies with
`Scheme.agree`. The update rule and its `Anchored` law are the caller's. -/

section Scheduling

variable (M : SigningFaults Validator) (E : M.Execution Value)
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

/-- The scheme's rule as a Barnacle base rule. -/
abbrev schemeBase (p : Params) (σ : VoteSel Validator BlockId Payload P honest) :
    Barnacle.BaseRule Validator BlockId Payload :=
  Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)

/-- One run per validator on its own view, closed past configuration `c`,
finalizes what any of them commits in the configuration, at every tolerated
row. -/
theorem commitFinalized_barnacle_scheme {q f : ℕ} [P.Quorate q] (ht : p.Tolerates honest f q)
    {Par : Barnacle.Params} {B : Barnacle.Boundary Validator}
    {upd : Barnacle.UpdateRule (schemeBase p σ)} (hanc : Barnacle.Anchored (schemeBase p σ) upd)
    {C₀ C : Barnacle.Config Validator} {U : (schemeBase p σ).Universe}
    (Pr : SigningFaults.Execution.SigningRule M E (schemeBase p σ).toDagRule C.sched U vm)
    {K : ℕ} (Rn : ∀ v, Barnacle.Run (schemeBase p σ) Par B upd C₀ U (Pr.view v) K)
    {c : ℕ} (hc : c < K) {v₀ : Validator} (hcfg : (Rn v₀).cfg c = C)
    {κ : ℕ} {L : BlockId} (h : (Rn v₀).vdct c κ = some L)
    (hlo : (Rn v₀).start c < C.roundOf κ)
    (hhi : C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor c)) :
    Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit κ L)) :=
  commitFinalized_barnacle M E vm (Scheme.agree ht) hanc Pr Rn hc hcfg h hlo hhi

end Scheduling

end Integration

end LeanDag
