import LeanDag.Scheme.Properties
import LeanDag.Checkpoint.CommitProofs

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

The fault model `M : SigningFaults` stays a parameter. Pick an instance per
deployment, e.g. `FlexibleFaults.signing` in `Integration/HybridCheckpoint.lean`.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Checkpoint LeanDag.Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type} {Value : Type*}
variable {P : Validity Validator BlockId Payload} [P.Mechanised] {honest : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest}
variable (M : SigningFaults Validator) (E : M.Execution Value)
variable (vm : DeterministicVM (BlockId := BlockId) (Value := Value))

/-- Safety: a commit yields a finality certificate.

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

Inputs:
- `hlive`: the row's commit threshold fits within the reliable set.
- `hq`: the recovery-correct validators form a reliability quorum.
- `hpop`: they produce blocks at every round of the slot's wave.
- `hcert`: every candidate for the slot is certified by them.
- `hcov`: every rule-following validator's view covers the whole wave.
- `hlead`: the slot's leader is recovery-correct.
Output: some candidate `L` commits and gets a `FinalityQC`. -/
theorem liveCommitFinalized_scheme {q f : ℕ} [P.Quorate q] (ht : p.Tolerates honest f q)
    {rel : Reliability Validator}
    (hlive : p.commitThreshold ≤ Fintype.card Validator - rel.slack)
    (S : Slots Validator) {U : (schemeRule p σ).Universe}
    (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm) {slot : ℕ}
    (hq : rel.IsQuorum M.recoveryCorrect)
    (hpop : ∀ n, S.slotRound slot ≤ n →
      n ≤ S.slotRound slot + (familySupport p σ).waveAt (S.kind slot) →
      Properties.PopulatedOn (schemeRule p σ) U M.recoveryCorrect n)
    (hcert : ∀ L, (schemeRule p σ).IsCandidate S U slot L →
      (familySupport p σ).certifiesAt U M.recoveryCorrect (S.slotRound slot)
        (S.kind slot) L)
    (hcov : ∀ v ∈ M.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
      (S.slotRound slot + (familySupport p σ).waveAt (S.kind slot)))
    (hlead : S.leader slot ∈ M.recoveryCorrect) :
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

end Integration

end LeanDag
