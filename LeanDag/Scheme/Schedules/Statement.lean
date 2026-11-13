import LeanDag.Scheme.Model.Schedules
import LeanDag.Scheme.Model.Params
import Mathlib.Data.Prod.Lex
import LeanDag.Steelhead.Coin.Statement
import Mathlib.Probability.Distributions.Uniform
import LeanDag.Barnacle.Agreement.Statement
import LeanDag.Barnacle.Ledger.Statement
import LeanDag.Barnacle.Live.Statement
import LeanDag.Barnacle.Model.Chains
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
  and certificate thresholds (`ReactiveDescends`), and reaches every
  height under a schedule whose heads run, under Barnacle's AIMD rule and
  under every HammerHead score permuting round-robin, each configuration's
  schedule good only from `δ` past its start, before which its validators
  do not know it (`RunsExistReactive`, `AimdReactive`,
  `HammerHeadReactive`);
* **run asynchronously** (`schemeLiveAsync`), the DAG good under a
  schedule when a quorum populates every round and the first slots of a
  wave of rounds in every window are led by safe validators, every
  configuration is live (`AsyncConfigLive`);
* **with crashed validators silent** (`schemeLiveSilent`,
  `Timed.SilentGood`), a crashed leader's slot is skipped directly, so the
  decider has the descent laws and decides every slot a synchronised or
  silent validator leads (`SilentDescends`), and on one slot per round,
  under a permutation of round-robin, it reaches every height under every
  update rule that keeps that shape, HammerHead's among them, at
  `(waveLength − 1)·fb + slack + 1 ≤ n` (`SilentLive`, `HammerHeadSilent`);
  Mysticeti, Blue Bottle PS, Orcaella and Hybrid Mysticeti meet this at
  their committees (`RowsSkipScheduled`);
* **at every leader count, under schedules with bounded anchor chains**
  (`Config.BoundedChains`): from every round's first slot, the scan to the
  first committed slot, through the skipped slots of crashed leaders and
  the scans of Byzantine-led slots a wave above them, ends within `c₀`
  rounds. Under every update rule keeping such schedules, the decider
  reaches every height with crashed validators silent (`ChainsSilent`) and
  run responsively, each configuration's schedule good from `δ` past its
  start (`ChainsReactive`), at gap `c₀ + 2·waveLength`.

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

/-- **Run responsively under a schedule whose heads run, the decider reaches
every height**, each configuration's schedule good only from `δ` past its
start — its validators wait for its leaders once they know it, and for the
old configuration's until its range closes. -/
def RunsExistReactive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator)
    (c₀ : ℕ) (head : ℕ → Validator),
    p.Tolerates honest f q → p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + rel.slack →
      HeadsRun head T p.waveLength c₀) →
    ∀ (B : Barnacle.Params) (Bd : Boundary Validator)
      (upd : UpdateRule (schemeLiveReactive p σ rel).toBaseRule),
      UpdBounded B upd → UpdKeeps upd (fun C => C.head = head) →
      ∀ (C₀ : Config Validator) (δ : ℕ),
        Barnacle.Live.RunsExistFrom (schemeLiveReactive p σ rel) B Bd upd C₀
          (fun C => C.head = head) c₀ δ

/-- **Barnacle's AIMD rule over the decider, run responsively, reaches
every height**, on a leader function whose first leader is round-robin. -/
def AimdReactive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)),
    p.Tolerates honest f q → p.CertFits (n - rel.slack) → p.Scheduled n rel.slack →
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n)) (lead : ℕ → ℕ → Fin n)
      (hl : LeadKeyed lead B.maxLeaders), (∀ ρ, lead ρ 0 = roundRobin n hn ρ) →
      ∀ (C₀ : Config (Fin n)) (δ : ℕ),
        haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        Barnacle.Live.RunsExistFrom (schemeLiveReactive p σ rel) B Bd
          (Barnacle.Aimd.rule _ B lead hl) C₀ (fun C => C.head = roundRobin n hn)
          (n + p.waveLength - 1) δ

/-- **A HammerHead score over the decider, run responsively, reaches every
height** when it keeps the shape and its output's heads are a permutation
of round-robin. -/
def HammerHeadReactive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)),
    p.Tolerates honest f q → p.CertFits (n - rel.slack) → p.Scheduled n rel.slack →
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    ∀ (B : Barnacle.Params) (score : Adaptive.Score (schemeLiveReactive p σ rel).toBaseRule)
      (C₀ : Config (Fin n)) (δ : ℕ),
      score.Keeps → (∀ U V v C, PermRR hn C → PermRR hn (score U V v C)) →
        Barnacle.Live.RunsExistFrom (schemeLiveReactive p σ rel) B Boundary.atThreshold
          (Adaptive.rule score) C₀ (PermRR hn) (n + p.waveLength - 1) δ

/-- **Responsive goodness is inhabited at every partially synchronous
row**: on the full record, under every schedule and from every round, a
quorum runs the decider responsively up to the horizon. -/
def ReactiveGoodInhabited : Prop :=
  ∀ (n : ℕ) [NeZero n] (p : Params) (f c : ℕ), p.PSRow n f c →
    ∀ (rel : Reliability (Fin n)), rel.IsQuorum Finset.univ →
    ∀ (σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
        (ValidAt (n - f - c) (Clause.distinct.and Clause.selfParent)) Finset.univ) (N : ℕ),
      ∃ U : BlockRecord (Fin n) (Lex (ℕ × Fin n)) Unit
          (ValidAt (n - f - c) (Clause.distinct.and Clause.selfParent)) Finset.univ,
        (∀ r ≤ N, ∀ v : Fin n, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r) ∧
        ∀ (S : Slots (Fin n)) (Rnd : ℕ), reactiveGood p σ rel S U Rnd N

/-- **Run asynchronously, every configuration is live**: at every
reliability whose quorum meets the commit and certificate thresholds, on a
DAG good asynchronously under a configuration's schedule, its slots are
decided, each window of `c₀` rounds commits, and the slots below the good
start are decided. -/
def AsyncConfigLive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator) (c₀ : ℕ),
    p.CertFits q → p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ C : Config Validator,
      (schemeLiveAsync p σ rel c₀).LiveOn C.sched c₀ ∧
        (schemeLiveAsync p σ rel c₀).SettlesBelow C.sched c₀

/-- **Barnacle's AIMD rule over the decider, run asynchronously, reaches every
height** when its heads are `h`, a quorum populates every round, and `h`'s
safe heads come in runs within `c₀` rounds. -/
def AsyncAimdRuns : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)) (c₀ : ℕ),
    p.Tolerates honest f q → p.CertFits q →
    p.commitThreshold ≤ Fintype.card (Fin n) - rel.slack →
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n)) (lead : ℕ → ℕ → Fin n)
      (hl : LeadKeyed lead B.maxLeaders) (h : ℕ → Fin n), (∀ ρ, lead ρ 0 = h ρ) →
      ∀ C₀ : Config (Fin n), C₀.InBounds B → C₀.head = h →
      ∀ (U : (schemeLiveAsync p σ rel c₀).Universe) (V : (schemeLiveAsync p σ rel c₀).View U)
        (N : ℕ) (T : Finset (Fin n)), rel.IsQuorum T → T ⊆ honest →
        (∀ r ≤ N, PopulatedOn U T r) → SafeHeadRuns p U h c₀ 0 N →
        (schemeLiveAsync p σ rel c₀).toBaseRule.CoversUpto U V N →
        ∀ K, Barnacle.horizon B (schemeLiveAsync p σ rel c₀) c₀ K ≤ N →
          Nonempty (Barnacle.Run (schemeLiveAsync p σ rel c₀).toBaseRule B Bd
            (Barnacle.Aimd.rule _ B lead hl) C₀ U V K)

open scoped ENNReal in
/-- **Barnacle's AIMD rule over the decider, its heads drawn by a coin,
reaches every height with probability tending to `1`.** The record is fixed
before the coin (the adversary does not see it); the rounds up to the
horizon fill `J` windows of `M` waves; every round's safe set holds at least
`c` validators. The heads are `J · M` blocks of a wave of uniform coins
(`coinHead`), and the other leaders of a round follow from its head
(`lead h ρ 0 = h ρ`). A run of height `K` fails to exist with probability at
most `J · badBlockBoundAt c w ^ M`. -/
def AsyncAimdLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n))
    (J M c : ℕ) (dflt : Fin n),
    p.Tolerates honest f q → p.CertFits q →
    p.commitThreshold ≤ Fintype.card (Fin n) - rel.slack →
    haveI : Nonempty (Fin n) := ⟨dflt⟩
    ∀ (B : Barnacle.Params) (Bd : Boundary (Fin n)) (lead : (ℕ → Fin n) → ℕ → ℕ → Fin n)
      (hl : ∀ h, LeadKeyed (lead h) B.maxLeaders), (∀ h ρ, lead h ρ 0 = h ρ) →
      ∀ C₀ : (ℕ → Fin n) → Config (Fin n), (∀ h, (C₀ h).InBounds B ∧ (C₀ h).head = h) →
      ∀ (U : (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).Universe)
        (V : (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).View U)
        (N : ℕ) (T : Finset (Fin n)), rel.IsQuorum T → T ⊆ honest →
        (∀ r ≤ N, PopulatedOn U T r) →
        (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule.CoversUpto U V N →
        N + 1 ≤ J * (M * (p.waveLength - 1 + 1)) →
        (∀ r, r < J * (M * (p.waveLength - 1 + 1)) → c ≤ (safeAt p U r).card) →
        ∀ K, Barnacle.horizon B (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1))))
            (2 * (M * (p.waveLength - 1 + 1))) K ≤ N →
          (PMF.uniformOfFintype (Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin n)).toOuterMeasure
              {g | IsEmpty (Barnacle.Run
                (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B Bd
                (Barnacle.Aimd.rule _ B (lead (coinHead dflt g)) (hl _)) (C₀ (coinHead dflt g))
                U V K)} ≤
            (J : ℝ≥0∞) * Steelhead.Coin.badBlockBoundAt (Fin n) c (p.waveLength - 1 + 1) ^ M

/-- **A HammerHead score over the decider, run asynchronously, reaches every
height** when each configuration's heads read a table of `Tbls` at the
coin's index `u`, the score keeps that form, a quorum populates every round,
and every table's heads come in safe runs within `c₀` rounds. -/
def AsyncHammerHeadRuns : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n)) (c₀ m : ℕ)
    (u : ℕ → Fin m) (Tbls : Finset (Fin m → Fin n)),
    p.Tolerates honest f q → p.CertFits q →
    p.commitThreshold ≤ Fintype.card (Fin n) - rel.slack →
    ∀ (B : Barnacle.Params) (score : Adaptive.Score (schemeLiveAsync p σ rel c₀).toBaseRule)
      (C₀ : Config (Fin n)),
      score.Keeps →
      (∀ U V v C, (∃ tbl ∈ Tbls, C.head = fun ρ => tbl (u ρ)) →
        ∃ tbl ∈ Tbls, (score U V v C).head = fun ρ => tbl (u ρ)) →
      C₀.InBounds B → (∃ tbl ∈ Tbls, C₀.head = fun ρ => tbl (u ρ)) →
      ∀ (U : (schemeLiveAsync p σ rel c₀).Universe) (V : (schemeLiveAsync p σ rel c₀).View U)
        (N : ℕ) (T : Finset (Fin n)), rel.IsQuorum T → T ⊆ honest →
        (∀ r ≤ N, PopulatedOn U T r) →
        (∀ tbl ∈ Tbls, SafeHeadRuns p U (fun ρ => tbl (u ρ)) c₀ 0 N) →
        (schemeLiveAsync p σ rel c₀).toBaseRule.CoversUpto U V N →
        ∀ K, Barnacle.horizon B (schemeLiveAsync p σ rel c₀) c₀ K ≤ N →
          Nonempty (Barnacle.Run (schemeLiveAsync p σ rel c₀).toBaseRule B Boundary.atThreshold
            (Adaptive.rule score) C₀ U V K)

open scoped ENNReal in
/-- **A HammerHead score over the decider, with a coin drawing from the
reputation distribution, reaches every height with probability tending to
`1`.** Each configuration's heads read one of the tables `Tbls` (a
reputation distribution, every table supporting `k` validators with weight
`e`) at a uniform index of `m` drawn per round (`coinHead`); every round's
safe set holds at least `s` validators; the rounds up to the horizon fill
`J` windows of `M` waves. A run of height `K` fails to exist with
probability at most `|Tbls| · J · badBlockBoundAt m (e (k + s − n)) w ^ M`,
positive per coin when `k + s > n`: at two buffer rounds a quorum support
suffices (`s = q − f`), and at one buffer round where `n ≥ 5f + 3c + 1`. -/
def AsyncHammerHeadLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest) (rel : Reliability (Fin n))
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
        (V : (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).View U)
        (N : ℕ) (T : Finset (Fin n)), rel.IsQuorum T → T ⊆ honest →
        (∀ r ≤ N, PopulatedOn U T r) →
        (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule.CoversUpto U V N →
        N + 1 ≤ J * (M * (p.waveLength - 1 + 1)) →
        (∀ r, r < J * (M * (p.waveLength - 1 + 1)) → s ≤ (safeAt p U r).card) →
        ∀ K, Barnacle.horizon B (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1))))
            (2 * (M * (p.waveLength - 1 + 1))) K ≤ N →
          (PMF.uniformOfFintype (Fin (J * M) → Fin (p.waveLength - 1 + 1) → Fin m)).toOuterMeasure
              {g | IsEmpty (Barnacle.Run
                (schemeLiveAsync p σ rel (2 * (M * (p.waveLength - 1 + 1)))).toBaseRule B
                Boundary.atThreshold (Adaptive.rule (score (coinHead dflt g)))
                (C₀ (coinHead dflt g)) U V K)} ≤
            (Tbls.card : ℝ≥0∞) * ((J : ℝ≥0∞) *
              Steelhead.Coin.badBlockBoundAt (Fin m) (e * (k + s - n)) (p.waveLength - 1 + 1) ^ M)

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

/-- **The rows that fit round-robin scheduling**, at slack `f` for the
Byzantine rows and `f + c` for the hybrid ones: Mysticeti and Cordial
Miners PS from `3f + 1`, Blue Bottle PS and Blue Bottle Async from
`5f + 1`, Orcaella and Async Orcaella from `5f + 3c + 1`, Nemo-Nemo from
`2c + 1`, and Hybrid Mysticeti from `3f + 3c + 1`. -/
def RowsScheduled : Prop :=
  ∀ n f c : ℕ,
    (3 * f + 1 ≤ n → (Params.mysticeti n f).Scheduled n f ∧
      (Params.cordialMinersPS n f).Scheduled n f) ∧
    (5 * f + 1 ≤ n → (Params.blueBottlePS n f).Scheduled n f) ∧
    (5 * f + 3 * c + 1 ≤ n → (Params.orcaella n f c).Scheduled n (f + c)) ∧
    (2 * c + 1 ≤ n → (Params.nemoNemo n c).Scheduled n c) ∧
    (3 * f + 3 * c + 1 ≤ n → (Params.hybridMysticeti n f c).Scheduled n (f + c)) ∧
    (5 * f + 1 ≤ n → (Params.blueBottleAsync n f).Scheduled n f) ∧
    (5 * f + 3 * c + 1 ≤ n → (Params.asyncOrcaella n f c).Scheduled n (f + c))

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

/-- **With crashed validators silent, schedules with bounded anchor chains
reach every height**, at any leader count, under every update rule that
keeps them, at gap `c₀ + 2·waveLength`. -/
def ChainsSilent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised] (q : ℕ)
    [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator) (fb c₀ : ℕ),
    p.Tolerates honest f q → rel.correct ⊆ honest →
    p.certThreshold ≤ Fintype.card Validator - rel.slack →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    p.skipThreshold ≤ Fintype.card Validator - rel.slack → p.voteOffset = 1 →
    ∀ (B : Barnacle.Params) (Bd : Boundary Validator)
      (upd : UpdateRule (schemeLiveSilent p σ rel fb).toBaseRule) (Q : Config Validator → Prop),
      UpdBounded B upd → UpdKeeps upd Q →
      (∀ C : Config Validator, Q C → C.BoundedChains rel.slack fb p.waveLength c₀) →
      ∀ C₀ : Config Validator, Q C₀ →
        Barnacle.Live.RunsExist (schemeLiveSilent p σ rel fb) B Bd upd C₀ (c₀ + 2 * p.waveLength)

/-- **Run responsively, schedules with bounded anchor chains reach every
height**, at any leader count, under every update rule that keeps them,
each configuration's schedule good only from `δ` past its start, at gap
`c₀ + 2·waveLength`. -/
def ChainsReactive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator) (c₀ : ℕ),
    p.Tolerates honest f q → p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ (B : Barnacle.Params) (Bd : Boundary Validator)
      (upd : UpdateRule (schemeLiveReactive p σ rel).toBaseRule) (Q : Config Validator → Prop),
      UpdBounded B upd → UpdKeeps upd Q →
      (∀ C : Config Validator, Q C → C.BoundedChains rel.slack rel.slack p.waveLength c₀) →
      ∀ (C₀ : Config Validator) (δ : ℕ),
        Barnacle.Live.RunsExistFrom (schemeLiveReactive p σ rel) B Bd upd C₀ Q
          (c₀ + 2 * p.waveLength) δ

/-- Safety, the descent laws, every height under Barnacle and HammerHead,
the rows that fit round-robin, and the same with silent crashes. -/
def Statement : Prop :=
  Safe ∧ Descends ∧ RunsExist ∧ Aimd ∧ HammerHead ∧ RowsScheduled ∧ SilentDescends ∧
    SilentLive ∧ HammerHeadSilent ∧ RowsSkipScheduled ∧ ReactiveDescends ∧ RunsExistReactive ∧
    AimdReactive ∧ HammerHeadReactive ∧ ReactiveGoodInhabited ∧ AsyncConfigLive ∧ AsyncAimdRuns ∧
    AsyncAimdLive ∧ AsyncHammerHeadRuns ∧ AsyncHammerHeadLive ∧ ChainsSilent ∧ ChainsReactive

end Schedules

end Scheme

end LeanDag
