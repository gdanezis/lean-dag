import LeanDag.Scheme.Model.Crash
import LeanDag.Checkpoint.CommitSpec
import LeanDag.Scheme.Model.Schedules
import LeanDag.Barnacle.Live.Statement
import LeanDag.Barnacle.Aimd.Rule
import LeanDag.Adaptive.Score.Rule
import LeanDag.Scheme.Schedules.Statement
import LeanDag.Barnacle.Model.Run
/-!
# The mechanisms composed — statement

`docs/mechanisms.md` M5. How the mechanisms over the family compose.

* **Checkpoints over a responsive run** (`CheckpointsResponsive`): at a
  tolerated row whose quorum meets the commit and certificate thresholds,
  when the validators following the signing rule run the family
  responsively past GST and their views are caught up to a slot's wave,
  a slot one of them leads reaches second-tier finality: some candidate of
  it gets a finality certificate.
* **Checkpoints with crashes** (`CheckpointsCrash`): the same, when they
  run the family with crashes and restarts, past `max gst tr`.
* **Scheduling with crashes** (`ScheduledCrash`): an adaptive schedule
  that reaches every height over responsive runs reaches it when each
  configuration is run with crashes and restarts (`crashGood`).
* **All four, partially synchronously** (`HammerHeadComposed`,
  `AimdComposed`): under a HammerHead score permuting round-robin, or
  Barnacle's AIMD rule, with the validators running each configuration
  responsively with crashes and restarts from `δ` past its start, runs of
  every height exist on every signer's view, and every slot a closed
  configuration commits reaches second-tier finality.
* **Atomic broadcast over scheduled runs** (Theorem 2's safety and
  validity): a scheduled run's delivered sequence (`runDeliver`) holds at
  most one block of each round and author and only blocks of the record
  (`ScheduledIntegrity`); two runs' sequences never order two blocks both
  ways, and a block delivered at one height is delivered by every run at
  every higher height (`ScheduledAgreed`); under the weak-reference rule, a
  block every reliable validator holds by `t` is delivered once the ledger
  holds a leader of round `t + 2` or later (`ScheduledValidity`), which,
  at Barnacle's boundary, a run of height `t + 2` has
  (`AnchorLedger`).
* **All three, asynchronously** (`AsyncComposed`): with crashes and
  restarts, under Barnacle's AIMD rule with heads drawn by a coin, and with
  checkpoints, runs of every height on every signer's view, finalizing what
  each closed configuration commits, fail to exist with probability at most
  `J · badBlockBoundAt c w ^ M`. The same holds under a HammerHead score
  whose coin draws from reputation tables supporting `k` validators with
  weight `e` (`AsyncHammerHeadComposed`), at `|Tbls| · J ·
  badBlockBoundAt m (e (k + s − n)) w ^ M`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Compose

open Checkpoint

/-- **Checkpoints over a responsive run.** -/
def CheckpointsResponsive : Prop :=
  ∀ (Validator BlockId Payload Value : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (q f : ℕ) [P.Quorate q]
    (M : SigningFaults Validator) (E : M.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) (rel : Reliability Validator),
    p.Tolerates honest f q → p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ (S : Slots Validator) (U : (schemeRule p σ).Universe)
      (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm)
      (V : (schemeRule p σ).View U) (slot : ℕ),
      reactiveLive p σ rel S V M.alive slot (slot + 1) →
      (∀ v ∈ M.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
        (S.slotRound slot + (p.waveLength - 1))) →
      S.leader slot ∈ M.alive →
      ∃ L, (schemeRule p σ).IsCandidate S U slot L ∧
        Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit slot L))

/-- **Checkpoints with crashes and restarts.** -/
def CheckpointsCrash : Prop :=
  ∀ (Validator BlockId Payload Value : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (q f : ℕ) [P.Quorate q]
    (M : SigningFaults Validator) (E : M.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) (rel : Reliability Validator),
    p.Tolerates honest f q → p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ (S : Slots Validator) (U : (schemeRule p σ).Universe)
      (Pr : SigningFaults.Execution.SigningRule M E (schemeRule p σ) S U vm)
      (V : (schemeRule p σ).View U) (slot : ℕ),
      crashLive p σ rel S V M.alive slot (slot + 1) →
      (∀ v ∈ M.alive, Properties.CoversUpto (schemeRule p σ) (Pr.view v)
        (S.slotRound slot + (p.waveLength - 1))) →
      S.leader slot ∈ M.alive →
      ∃ L, (schemeRule p σ).IsCandidate S U slot L ∧
        Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit slot L))

open Barnacle in
/-- The goodness asked of a run of height `K`, with crashes: its
configuration is run with crashes and restarts from `δ` past its start up to
the round its step needs, or the run already extends past it. -/
def CrashGoodRuns {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    [P.Mechanised] {honest : Finset Validator} (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator)
    (B : Barnacle.Params) (Bd : Boundary Validator)
    (upd : UpdateRule (schemeLiveReactive p σ rel).toBaseRule) (C₀ : Config Validator)
    (Q : Config Validator → Prop) (c δ : ℕ) (U : (schemeLiveReactive p σ rel).Universe)
    (V : (schemeLiveReactive p σ rel).View U) : Prop :=
  ∀ K (Rn : Run (schemeLiveReactive p σ rel).toBaseRule B Bd upd C₀ U V K), Q (Rn.cfg K) →
    crashGood p σ rel (Rn.cfg K).sched U (Rn.start K + δ)
        (Rn.start K + max (B.maxInterval + 1) δ + 2 * c + (schemeLiveReactive p σ rel).waveLength) ∨
      ∃ Rn' : Run (schemeLiveReactive p σ rel).toBaseRule B Bd upd C₀ U V (K + 1),
        Rn'.start (K + 1) ≤ Rn.start K + max (B.maxInterval + 1) δ + c ∧ Q (Rn'.cfg (K + 1))

open Barnacle in
/-- **Scheduling with crashes.** -/
def ScheduledCrash : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator)
    (B : Barnacle.Params) (Bd : Boundary Validator)
    (upd : UpdateRule (schemeLiveReactive p σ rel).toBaseRule) (C₀ : Config Validator)
    (Q : Config Validator → Prop) (c δ : ℕ),
    Live.RunsExistFrom (schemeLiveReactive p σ rel) B Bd upd C₀ Q c δ →
    C₀.InBounds B → Q C₀ →
    ∀ (U : (schemeLiveReactive p σ rel).Universe) (V : (schemeLiveReactive p σ rel).View U)
      (N : ℕ), (schemeLiveReactive p σ rel).toBaseRule.CoversUpto U V N →
      CrashGoodRuns p σ rel B Bd upd C₀ Q c δ U V →
      ∀ K, horizonFrom B (schemeLiveReactive p σ rel) c δ K ≤ N →
        Nonempty (Run (schemeLiveReactive p σ rel).toBaseRule B Bd upd C₀ U V K)

open Barnacle in
/-- **All four under HammerHead**: responsive, with crashes, under a
HammerHead score permuting round-robin, with checkpoints. -/
def HammerHeadComposed : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload Value : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n))
    (M : SigningFaults (Fin n)) (E : M.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)),
    p.Tolerates honest f q → p.CertFits (n - rel.slack) → p.Scheduled n rel.slack →
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∀ (B : Barnacle.Params) (score : Adaptive.Score (schemeLiveReactive p σ rel).toBaseRule)
      (C₀ : Config (Fin n)) (δ : ℕ),
      score.Keeps → (∀ U V v C, PermRR hn C → PermRR hn (score U V v C)) →
      C₀.InBounds B → PermRR hn C₀ →
      ∀ (U : (schemeLiveReactive p σ rel).Universe) (C : Config (Fin n))
        (Pr : SigningFaults.Execution.SigningRule M E
          (schemeLiveReactive p σ rel).toBaseRule.toDagRule C.sched U vm) (N : ℕ),
        (∀ v, (schemeLiveReactive p σ rel).toBaseRule.CoversUpto U (Pr.view v) N) →
        (∀ v, CrashGoodRuns p σ rel B Boundary.atThreshold (Adaptive.rule score) C₀ (PermRR hn)
          (n + p.waveLength - 1) δ U (Pr.view v)) →
        ∀ K, horizonFrom B (schemeLiveReactive p σ rel) (n + p.waveLength - 1) δ K ≤ N →
          ∃ Rn : ∀ v, Run (schemeLiveReactive p σ rel).toBaseRule B Boundary.atThreshold
              (Adaptive.rule score) C₀ U (Pr.view v) K,
            ∀ (k : ℕ), k < K → ∀ (v₀ : Fin n), (Rn v₀).cfg k = C →
              ∀ (κ : ℕ) (L : BlockId), (Rn v₀).vdct k κ = some L →
                (Rn v₀).start k < C.roundOf κ → C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor k) →
                Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit κ L))

open Barnacle in
/-- **All four under Barnacle's AIMD rule**: responsive, with crashes, under
the AIMD rule on a leader function whose first leader is round-robin, with
checkpoints. -/
def AimdComposed : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload Value : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n))
    (M : SigningFaults (Fin n)) (E : M.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)),
    p.Tolerates honest f q → p.CertFits (n - rel.slack) → p.Scheduled n rel.slack →
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n)) (lead : ℕ → ℕ → Fin n)
      (hl : LeadKeyed lead B.maxLeaders), (∀ ρ, lead ρ 0 = roundRobin n hn ρ) →
      ∀ (C₀ : Config (Fin n)) (δ : ℕ), C₀.InBounds B → C₀.head = roundRobin n hn →
      ∀ (U : (schemeLiveReactive p σ rel).Universe) (C : Config (Fin n))
        (Pr : SigningFaults.Execution.SigningRule M E
          (schemeLiveReactive p σ rel).toBaseRule.toDagRule C.sched U vm) (N : ℕ),
        (∀ v, (schemeLiveReactive p σ rel).toBaseRule.CoversUpto U (Pr.view v) N) →
        (∀ v, CrashGoodRuns p σ rel B Bd (Aimd.rule _ B lead hl) C₀
          (fun C => C.head = roundRobin n hn) (n + p.waveLength - 1) δ U (Pr.view v)) →
        ∀ K, horizonFrom B (schemeLiveReactive p σ rel) (n + p.waveLength - 1) δ K ≤ N →
          ∃ Rn : ∀ v, Run (schemeLiveReactive p σ rel).toBaseRule B Bd
              (Aimd.rule _ B lead hl) C₀ U (Pr.view v) K,
            ∀ (k : ℕ), k < K → ∀ (v₀ : Fin n), (Rn v₀).cfg k = C →
              ∀ (κ : ℕ) (L : BlockId), (Rn v₀).vdct k κ = some L →
                (Rn v₀).start k < C.roundOf κ → C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor k) →
                Nonempty (SigningFaults.Execution.FinalityQC M E (vm.checkpointAfterCommit κ L))

open Barnacle in
open scoped ENNReal in
/-- **All three under asynchrony**: crashes and restarts, Barnacle's AIMD
rule with heads drawn by a coin, and checkpoints. -/
def AsyncComposed : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload Value : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n))
    (Ms : SigningFaults (Fin n)) (E : Ms.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value)) (J M c : ℕ) (dflt : Fin n),
    p.Tolerates honest f q → p.CertFits q →
    p.commitThreshold ≤ Fintype.card (Fin n) - rel.slack →
    haveI : Nonempty (Fin n) := ⟨dflt⟩
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n)) (lead : (ℕ → Fin n) → ℕ → ℕ → Fin n)
      (hl : ∀ h, LeadKeyed (lead h) B.maxLeaders), (∀ h ρ, lead h ρ 0 = h ρ) →
      ∀ C₀ : (ℕ → Fin n) → Config (Fin n), (∀ h, (C₀ h).InBounds B ∧ (C₀ h).head = h) →
      ∀ (U : (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).Universe)
        (T : Finset (Fin n)) (Nr qp : ℕ) (ac : AsyncCrashRun qp U T Nr),
        rel.IsQuorum T → T ⊆ honest → qp ≤ T.card →
      ∀ (N : ℕ), N ≤ Nr →
      ∀ (C : Config (Fin n)) (Pr : SigningFaults.Execution.SigningRule Ms E
          (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule.toDagRule
          C.sched U vm),
        (∀ v, (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule.CoversUpto
          U (Pr.view v) N) →
        N + 1 ≤ J * (M * (p.waveLength - 1 + 1)) →
        (∀ r, r < J * (M * (p.waveLength - 1 + 1)) → c ≤ (safeAt p U r).card) →
        ∀ K, horizon B (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1))))
            (2 * (M * (p.waveLength - 1 + 1))) K ≤ N →
          (PMF.uniformOfFintype (Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin n)).toOuterMeasure
              {g | ¬ ∃ Rn : ∀ v, Run
                  (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B Bd
                  (Aimd.rule _ B (lead (coinHead dflt g)) (hl _)) (C₀ (coinHead dflt g)) U
                  (Pr.view v) K,
                ∀ (k : ℕ), k < K → ∀ (v₀ : Fin n), (Rn v₀).cfg k = C →
                  ∀ (κ : ℕ) (L : BlockId), (Rn v₀).vdct k κ = some L →
                    (Rn v₀).start k < C.roundOf κ → C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor k) →
                    Nonempty (SigningFaults.Execution.FinalityQC Ms E
                      (vm.checkpointAfterCommit κ L))} ≤
            (J : ℝ≥0∞) * Steelhead.Coin.badBlockBoundAt (Fin n) c (p.waveLength - 1 + 1) ^ M

open Barnacle in
open scoped ENNReal in
/-- **All three under asynchrony, with HammerHead**: crashes and restarts,
a HammerHead score whose coin draws from reputation tables, and
checkpoints. -/
def AsyncHammerHeadComposed : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload Value : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n))
    (Ms : SigningFaults (Fin n)) (E : Ms.Execution Value)
    (vm : DeterministicVM (BlockId := BlockId) (Value := Value))
    (J M m k e s : ℕ) (dflt : Fin m) (Tbls : Finset (Fin m → Fin n)),
    p.Tolerates honest f q → p.CertFits q →
    p.commitThreshold ≤ Fintype.card (Fin n) - rel.slack →
    (∀ tbl ∈ Tbls, Supports tbl k e) →
    haveI : Nonempty (Fin m) := ⟨dflt⟩
    ∀ (B : Barnacle.Params)
      (score : (ℕ → Fin m) →
        Adaptive.Score (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule)
      (C₀ : (ℕ → Fin m) → Config (Fin n)),
      (∀ u', (score u').Keeps) →
      (∀ u' U V v C, (∃ tbl ∈ Tbls, C.head = fun ρ => tbl (u' ρ)) →
        ∃ tbl ∈ Tbls, (score u' U V v C).head = fun ρ => tbl (u' ρ)) →
      (∀ u', (C₀ u').InBounds B ∧ ∃ tbl ∈ Tbls, (C₀ u').head = fun ρ => tbl (u' ρ)) →
      ∀ (U : (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).Universe)
        (T : Finset (Fin n)) (Nr qp : ℕ) (ac : AsyncCrashRun qp U T Nr),
        rel.IsQuorum T → T ⊆ honest → qp ≤ T.card →
      ∀ (N : ℕ), N ≤ Nr →
      ∀ (C : Config (Fin n)) (Pr : SigningFaults.Execution.SigningRule Ms E
          (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule.toDagRule
          C.sched U vm),
        (∀ v, (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule.CoversUpto
          U (Pr.view v) N) →
        N + 1 ≤ J * (M * (p.waveLength - 1 + 1)) →
        (∀ r, r < J * (M * (p.waveLength - 1 + 1)) → s ≤ (safeAt p U r).card) →
        ∀ K, horizon B (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1))))
            (2 * (M * (p.waveLength - 1 + 1))) K ≤ N →
          (PMF.uniformOfFintype (Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin m)).toOuterMeasure
              {g | ¬ ∃ Rn : ∀ v, Run
                  (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
                  Boundary.atThreshold (Adaptive.rule (score (coinHead dflt g)))
                  (C₀ (coinHead dflt g)) U (Pr.view v) K,
                ∀ (k' : ℕ), k' < K → ∀ (v₀ : Fin n), (Rn v₀).cfg k' = C →
                  ∀ (κ : ℕ) (L : BlockId), (Rn v₀).vdct k' κ = some L →
                    (Rn v₀).start k' < C.roundOf κ → C.roundOf κ ≤ C.roundOf ((Rn v₀).anchor k') →
                    Nonempty (SigningFaults.Execution.FinalityQC Ms E
                      (vm.checkpointAfterCommit κ L))} ≤
            (Tbls.card : ℝ≥0∞) * ((J : ℝ≥0∞) *
              Steelhead.Coin.badBlockBoundAt (Fin m) (e * (k + s - n)) (p.waveLength - 1 + 1) ^ M)

/-- **A scheduled run's delivered sequence holds each round and author at
most once, no block twice, and only blocks of the record.** -/
def ScheduledIntegrity : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) (Par : Barnacle.Params)
    (B : Barnacle.Boundary Validator)
    (upd : Barnacle.UpdateRule (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)))
    (C₀ : Barnacle.Config Validator) (U : BlockRecord Validator BlockId Payload P honest)
    (V : U.View) (K : ℕ)
    (Rn : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀ U V K)
    (wk : BlockId → Finset BlockId) (K' : ℕ),
    ((runDeliver Rn wk K').map (roundAuthor U)).Nodup ∧ (runDeliver Rn wk K').Nodup ∧
      ∀ b ∈ runDeliver Rn wk K', b ∈ U.ids

/-- **Scheduled runs agree on what they deliver**, at the rows the
inequalities cover and under an anchored update rule: two runs' sequences
never order two blocks both ways (Sailfish's Total order), a block one
delivers after another the other delivers after it too (Sui and Duan's),
and a block delivered at one height is delivered by every run at every
height at least as high (Agreement). -/
def ScheduledAgreed : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised] (q : ℕ)
    [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (Par : Barnacle.Params)
    (B : Barnacle.Boundary Validator)
    (upd : Barnacle.UpdateRule (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)))
    (C₀ : Barnacle.Config Validator),
    p.Tolerates honest f q →
    Barnacle.Anchored (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) upd →
    ∀ (U : BlockRecord Validator BlockId Payload P honest) (V₁ V₂ : U.View) (K₁ K₂ : ℕ)
      (R₁ : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀
        U V₁ K₁)
      (R₂ : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀
        U V₂ K₂)
      (wk : BlockId → Finset BlockId) (K'₁ K'₂ : ℕ), K'₁ ≤ K₁ → K'₂ ≤ K₂ →
      (∀ x y, Before (runDeliver R₁ wk K'₁) x y → ¬ Before (runDeliver R₂ wk K'₂) y x) ∧
      (∀ x y, Before (runDeliver R₁ wk K'₁) x y → y ∈ runDeliver R₂ wk K'₂ →
        Before (runDeliver R₂ wk K'₂) x y) ∧
      (K'₁ ≤ K'₂ → ∀ b ∈ runDeliver R₁ wk K'₁, b ∈ runDeliver R₂ wk K'₂)

/-- **Validity over a scheduled run**, under the weak-reference rule: a
block of a reliable validator, held by every reliable validator by time
`t ≥ round m`, is delivered once the run's ledger holds a leader of round
`t + 2` or later. -/
def ScheduledValidity : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised] (q : ℕ)
    [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (Par : Barnacle.Params)
    (B : Barnacle.Boundary Validator)
    (upd : Barnacle.UpdateRule (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)))
    (C₀ : Barnacle.Config Validator) (U : BlockRecord Validator BlockId Payload P honest)
    (V : U.View) (K : ℕ)
    (Rn : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀ U V K)
    (wk : BlockId → Finset BlockId) (T : Finset Validator)
    (holds : Validator → ℕ → Finset BlockId) (built : Validator → ℕ → ℕ),
    T ⊆ honest → Fintype.card Validator < q + T.card → WeakRule U wk T holds built →
    (∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t) →
    (∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v →
      (U.block b).round ≤ built v (U.block b).round) →
    ∀ (m : BlockId) (t K' : ℕ), m ∈ U.ids → (U.block m).creator ∈ T →
      (U.block m).round ≤ t → (∀ v ∈ T, m ∈ holds v t) →
      (∃ A ∈ Rn.ledgerUpto K', A ∈ U.ids ∧ t + 2 ≤ (U.block A).round) →
      m ∈ runDeliver Rn wk K'

/-- **At Barnacle's boundary the ledger holds each closed configuration's
pivot**: a run of height `K` has, for each `k < K`, a leader of round
`k + 1` or later in its ledger to `K`. -/
def AnchorLedger : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (Par : Barnacle.Params)
    (upd : Barnacle.UpdateRule (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)))
    (C₀ : Barnacle.Config Validator) (U : BlockRecord Validator BlockId Payload P honest)
    (V : U.View) (K : ℕ)
    (Rn : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par
      Barnacle.Boundary.atAnchor upd C₀ U V K),
    ∀ k, k < K → ∃ A ∈ Rn.ledgerUpto K, A ∈ U.ids ∧ k + 1 ≤ (U.block A).round

/-- The mechanisms composed. -/
def Statement : Prop :=
  CheckpointsResponsive ∧ CheckpointsCrash ∧ ScheduledCrash ∧ HammerHeadComposed ∧ AimdComposed ∧
    AsyncComposed ∧ AsyncHammerHeadComposed ∧ ScheduledIntegrity ∧ ScheduledAgreed ∧
    ScheduledValidity ∧ AnchorLedger

end Compose

end Scheme

end LeanDag
