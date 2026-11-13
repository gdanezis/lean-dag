import LeanDag.Scheme.Model.Schedules
import LeanDag.Barnacle.Agreement.Statement
import LeanDag.Barnacle.Ledger.Statement
import LeanDag.Barnacle.Live.Statement
import LeanDag.Barnacle.Aimd.Rule
import LeanDag.Adaptive.Score.Rule
/-!
# The decider under Barnacle and HammerHead schedules — statement

`docs/scheme.md` §14. The decider at `p` and `σ`, read as the live rule
`schemeLive p σ rel`:

* **is safe under every update rule** (`Safe`): at every row tolerating
  the record's faults, two runs agree on the configurations and verdicts,
  and an anchored update rule gives one ledger that grows and holds each
  block once;
* **has the descent laws** at slack `rel.slack` (`Descends`), when the
  reliable validators are honest and meet the certificate and commit
  thresholds;
* **reaches every height** under every schedule whose heads come in runs
  of a wave (`RunsExist`);
* **under Barnacle's AIMD rule** on a round-robin leader function
  (`Aimd`), and **under every HammerHead score** that permutes a
  round-robin schedule (`HammerHead`), is safe and reaches every height,
  at a row meeting `Params.Scheduled`;
* **the partially synchronous rows meet `Params.Scheduled`**
  (`RowsScheduled`), Hybrid Mysticeti from `n ≥ 3f + 3c + 1`;
* **run responsively** (`schemeLiveReactive`), the DAG good under a
  schedule when a quorum runs it responsively under that schedule, has
  the descent laws at every reliability whose quorum meets the commit
  and certificate thresholds (`ReactiveDescends`);
* **with crashed validators silent** (`schemeLiveSilent`,
  `Timed.SilentGood`), a crashed leader's slot is skipped directly, so the
  decider has the descent laws and decides every slot a synchronised or
  silent validator leads (`SilentDescends`), and on one slot per round,
  under a permutation of round-robin, it reaches every height under every
  update rule that keeps that shape, HammerHead's among them, at
  `(waveLength − 1)·fb + slack + 1 ≤ n` (`SilentLive`, `HammerHeadSilent`);
  Mysticeti, Blue Bottle PS, Orcaella and Hybrid Mysticeti meet this at
  their committees (`RowsSkipScheduled`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Schedules

open Barnacle (Config Boundary UpdateRule UpdBounded UpdKeeps HeadsRun roundRobin LeadKeyed)

/-- **Run responsively, the decider has the descent laws** under every
schedule, at every reliability whose quorum meets the commit and
certificate thresholds: on a DAG run responsively under `S`, the reliable
validators commit every slot of `S` they lead. -/
def ReactiveDescends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator),
    p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    (schemeLiveReactive p σ rel).Descent rel.slack

/-- **The decider is safe under every update rule.** -/
def Safe : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised] (q : ℕ)
    [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator),
    p.Tolerates honest f q →
    ∀ (B : Barnacle.Params) (Bd : Boundary Validator)
      (upd : UpdateRule (schemeLive p σ rel).toBaseRule) (C₀ : Config Validator),
      Barnacle.Agreement.RunAgreement (schemeLive p σ rel).toBaseRule B Bd upd C₀ ∧
      (Barnacle.Anchored (schemeLive p σ rel).toBaseRule upd →
        Barnacle.Ledger.LedgerAgreement (schemeLive p σ rel).toBaseRule B Bd upd C₀ ∧
        Barnacle.Ledger.LedgerPrefix (schemeLive p σ rel).toBaseRule B Bd upd C₀ ∧
        Barnacle.Ledger.LedgerNodup (schemeLive p σ rel).toBaseRule B Bd upd C₀)

/-- **The decider has the descent laws at slack `rel.slack`**, when the
reliable validators are honest and `n − rel.slack` meets the certificate
and commit thresholds. -/
def Descends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator) (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator),
    rel.correct ⊆ honest → 2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength) →
    p.certThreshold ≤ Fintype.card Validator - rel.slack →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    (schemeLive p σ rel).Descent rel.slack

/-- **The decider reaches every height** under an update rule that keeps
the heads `head`, when every set missing at most `rel.slack` validators
leads `p.waveLength` consecutive heads within every `c₀ + 1` rounds. -/
def RunsExist : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised] (q : ℕ)
    [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator)
    (c₀ : ℕ) (head : ℕ → Validator),
    p.Tolerates honest f q → rel.correct ⊆ honest →
    p.certThreshold ≤ Fintype.card Validator - rel.slack →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + rel.slack →
      HeadsRun head T p.waveLength c₀) →
    ∀ (B : Barnacle.Params) (Bd : Boundary Validator)
      (upd : UpdateRule (schemeLive p σ rel).toBaseRule),
      UpdBounded B upd → UpdKeeps upd (fun C => C.head = head) →
      ∀ C₀ : Config Validator, C₀.head = head →
        Barnacle.Live.RunsExist (schemeLive p σ rel) B Bd upd C₀ c₀

/-- **Barnacle's AIMD rule over the decider reaches every height**, on a
leader function whose first leader is round-robin, with gap
`n + waveLength − 1`. -/
def Aimd : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)),
    p.Tolerates honest f q → rel.correct ⊆ honest → p.Scheduled n rel.slack →
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n)) (lead : ℕ → ℕ → Fin n)
      (hl : LeadKeyed lead B.maxLeaders), (∀ ρ, lead ρ 0 = roundRobin n hn ρ) →
      ∀ C₀ : Config (Fin n), C₀.head = roundRobin n hn →
        Barnacle.Live.RunsExist (schemeLive p σ rel) B Bd
          (Barnacle.Aimd.rule _ B lead hl) C₀ (n + p.waveLength - 1)

/-- **A HammerHead score over the decider is safe, and reaches every
height** when it keeps the shape and its output's heads are a permutation
of round-robin, with gap `n + waveLength − 1`. -/
def HammerHead : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)),
    p.Tolerates honest f q →
    ∀ (B : Barnacle.Params) (score : Adaptive.Score (schemeLive p σ rel).toBaseRule)
      (C₀ : Config (Fin n)),
      (Barnacle.Agreement.RunAgreement (schemeLive p σ rel).toBaseRule B Boundary.atThreshold
          (Adaptive.rule score) C₀ ∧
        Barnacle.Ledger.LedgerAgreement (schemeLive p σ rel).toBaseRule B Boundary.atThreshold
          (Adaptive.rule score) C₀ ∧
        Barnacle.Ledger.LedgerPrefix (schemeLive p σ rel).toBaseRule B Boundary.atThreshold
          (Adaptive.rule score) C₀ ∧
        Barnacle.Ledger.LedgerNodup (schemeLive p σ rel).toBaseRule B Boundary.atThreshold
          (Adaptive.rule score) C₀) ∧
      (rel.correct ⊆ honest → p.Scheduled n rel.slack → score.Keeps →
        (∀ U V v C, PermRR hn C → PermRR hn (score U V v C)) → PermRR hn C₀ →
        Barnacle.Live.RunsExist (schemeLive p σ rel) B Boundary.atThreshold
          (Adaptive.rule score) C₀ (n + p.waveLength - 1))

/-- **The partially synchronous rows fit round-robin scheduling**, at slack
`f` for the Byzantine rows and `f + c` for the hybrid ones: Mysticeti and
Cordial Miners PS from `3f + 1`, Blue Bottle PS from `5f + 1`, Orcaella
from `5f + 3c + 1`, Nemo-Nemo from `2c + 1`, and Hybrid Mysticeti from
`3f + 3c + 1`. -/
def RowsScheduled : Prop :=
  ∀ n f c : ℕ,
    (3 * f + 1 ≤ n → (Params.mysticeti n f).Scheduled n f ∧
      (Params.cordialMinersPS n f).Scheduled n f) ∧
    (5 * f + 1 ≤ n → (Params.blueBottlePS n f).Scheduled n f) ∧
    (5 * f + 3 * c + 1 ≤ n → (Params.orcaella n f c).Scheduled n (f + c)) ∧
    (2 * c + 1 ≤ n → (Params.nemoNemo n c).Scheduled n c) ∧
    (3 * f + 3 * c + 1 ≤ n → (Params.hybridMysticeti n f c).Scheduled n (f + c))

/-- **With crashed validators silent, the decider has the descent laws and
decides every slot a synchronised or silent validator leads**, the latter
when the vote round is one above the proposal and `n − rel.slack` meets the
skip threshold. -/
def SilentDescends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator) (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (fb : ℕ),
    rel.correct ⊆ honest → 2 ≤ p.waveLength → (p.voteIsCert = false → 3 ≤ p.waveLength) →
    p.certThreshold ≤ Fintype.card Validator - rel.slack →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    (schemeLiveSilent p σ rel fb).Descent rel.slack ∧
    (p.voteOffset = 1 → p.skipThreshold ≤ Fintype.card Validator - rel.slack →
      (schemeLiveSilent p σ rel fb).Decisive rel.slack fb)

/-- **With crashed validators silent, the decider reaches every height on one
slot per round** under every update rule that keeps the heads a permutation
of round-robin, at a row meeting `Params.SkipScheduled`, with gap
`n + waveLength − 1`. -/
def SilentLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)) (fb : ℕ),
    p.Tolerates honest f q → rel.correct ⊆ honest → p.SkipScheduled n rel.slack fb →
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n))
      (upd : UpdateRule (schemeLiveSilent p σ rel fb).toBaseRule),
      UpdBounded B upd → UpdKeeps upd (SinglePermRR hn) →
      ∀ C₀ : Config (Fin n), SinglePermRR hn C₀ →
        Barnacle.Live.RunsExist (schemeLiveSilent p σ rel fb) B Bd upd C₀ (n + p.waveLength - 1)

/-- **A HammerHead score over the decider with silent crashes reaches every
height** on one slot per round, when it keeps the shape and its output's
heads are a permutation of round-robin, at a row meeting
`Params.SkipScheduled`. -/
def HammerHeadSilent : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)) (fb : ℕ),
    p.Tolerates honest f q → rel.correct ⊆ honest → p.SkipScheduled n rel.slack fb →
    ∀ (B : Barnacle.Params) (score : Adaptive.Score (schemeLiveSilent p σ rel fb).toBaseRule)
      (C₀ : Config (Fin n)), score.Keeps →
      (∀ U V v C, PermRR hn C → PermRR hn (score U V v C)) → SinglePermRR hn C₀ →
      Barnacle.Live.RunsExist (schemeLiveSilent p σ rel fb) B Boundary.atThreshold
        (Adaptive.rule score) C₀ (n + p.waveLength - 1)

/-- **The rows with a direct skip meet `Params.SkipScheduled`** at their
committees, at `fb = f`: Mysticeti from `3f + 1`, Blue Bottle PS from
`5f + 1`, Orcaella from `5f + 3c + 1` and Hybrid Mysticeti from
`3f + 2c + 1`, the latter two at slack `f + c`. -/
def RowsSkipScheduled : Prop :=
  ∀ n f c : ℕ,
    (3 * f + 1 ≤ n → (Params.mysticeti n f).SkipScheduled n f f) ∧
    (5 * f + 1 ≤ n → (Params.blueBottlePS n f).SkipScheduled n f f) ∧
    (5 * f + 3 * c + 1 ≤ n → (Params.orcaella n f c).SkipScheduled n (f + c) f) ∧
    (3 * f + 2 * c + 1 ≤ n → (Params.hybridMysticeti n f c).SkipScheduled n (f + c) f)

/-- Safety, the descent laws, every height under Barnacle and HammerHead,
the rows that fit round-robin, and the same with silent crashes. -/
def Statement : Prop :=
  Safe ∧ Descends ∧ RunsExist ∧ Aimd ∧ HammerHead ∧ RowsScheduled ∧ SilentDescends ∧
    SilentLive ∧ HammerHeadSilent ∧ RowsSkipScheduled ∧ ReactiveDescends

end Schedules

end Scheme

end LeanDag
