import LeanDag.Scheme.Model.Reactive
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Reactive.Mysticeti
import LeanDag.Properties.Arcs.Quality
/-!
# The family, run reactively — statement

`docs/scheme.md` §13. A responsive validator builds as soon as what the
rule counts has arrived, with the timeout only as a fallback
(`SchemeReactive`), the pacemaker advancing on a quorum `q` of round
authors. At every row and vote, and at every reliability (the core's
`n − f`, Hydrozoan's `n − f − c`, Nemo's majority), past GST with the
timeout clearing `2Δ + proc`:

* **every reliable decision-round block certifies** a reliably-led slot's
  leader block (`Certifies`), when the reliable set is `q` strong: every
  reliable block from the proposal to the vote round reaches it, so every
  reliable vote-round block votes;
* **the reactive precondition is the family support's** (`Live`), so
* **a reliably-led slot commits** (`Commits`, the generic `LeaderCommits`),
  when the reliability's quorum meets the commit and certificate
  thresholds; the hybrid committees (`3f + 2c + 1`, `2c + 1`), which the
  core's fault class excludes, are among them;
* **no reliable block is censored** (`Includes`), on records whose blocks
  reference their author's previous block, under a schedule fair to each
  reliable validator: a reliable validator's block enters the ledger
  through a slot its author leads;
* **Reactive Mysticeti is an instance** (`OfMysticeti`): every Reactive
  Mysticeti execution with a correct reliable set is the family run
  reactively at the Mysticeti row, pacing at `n − f`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace ReactiveRun

open Properties

attribute [local instance] noFaults

/-- **Every reliable decision-round block certifies** a reliably-led slot's
leader block. -/
def Certifies : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N R q : ℕ)
    (rs : SchemeReactive q p σ U T N) (k : ℕ) (L : BlockId),
    p.CertFits q →
    T ⊆ honest → q ≤ T.card → rs.gst ≤ R →
    (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    R ≤ S.slotRound k → S.slotRound k + (p.waveLength - 1) ≤ N → S.leader k ∈ T →
    IsLeaderBlock U k L →
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + (p.waveLength - 1) → IsCert p σ U c L

/-- **The reactive precondition is the family support's**, at every
reliability. -/
def Live : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (S : Slots Validator) (U : (schemeRule p σ).Universe)
    (V : (schemeRule p σ).View U) (T : Finset Validator) (lo K : ℕ),
    p.CertFits (Fintype.card Validator - rel.slack) →
    reactiveLive p σ rel S V T lo K →
    (familySupport p σ).live rel S V T lo K

/-- **Run reactively, a reliably-led slot commits**, at every reliability
whose quorum meets the commit and certificate thresholds. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator),
    p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    LeaderCommits (schemeRule p σ)
      (fun S {U} V T lo K => reactiveLive p σ rel S (U := U) V T lo K)

/-- **Run reactively, no reliable block is censored**, on records whose
blocks reference their author's previous block, at every reliability
whose quorum meets the thresholds and whose reliable validators are
honest. -/
def Includes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator),
    (∀ blk b, P blk b → Clause.selfParent blk b) → rel.correct ⊆ honest →
    p.CertFits (Fintype.card Validator - rel.slack) →
    p.commitThreshold ≤ Fintype.card Validator - rel.slack →
    ∀ (S : Slots Validator) (T : Finset Validator), T ⊆ rel.correct →
    (∀ v ∈ T, ∀ n, ∃ k, n ≤ k ∧ S.leader k = v) →
    ∀ (m : ℕ), ∀ v ∈ T, ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      ∀ (U : (schemeRule p σ).Universe) (V : (schemeRule p σ).View U),
        reactiveLive p σ rel S V T k' (k' + 1) →
        ∃ L, (schemeRule p σ).Decided S V k' (some L) ∧
          ∀ b ∈ (schemeRule p σ).ids U, ((schemeRule p σ).block U b).creator = v →
            ((schemeRule p σ).block U b).round = m →
            b ∈ historyFrom ((schemeRule p σ).block U) L ∧
              ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
                b ∈ Arcs.ledgerSetOf (schemeRule p σ) U g n

/-- **Reactive Mysticeti is the family run reactively**, at the Mysticeti row
and every vote, when its reliable set is correct. -/
def OfMysticeti : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [Nonempty Validator] [LinearOrder BlockId] [S : Slots Validator]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (N : ℕ),
    T ⊆ (Correct : Finset Validator) → ReactiveM U T N →
    Nonempty (SchemeReactive (quorumCard Validator)
      (Params.mysticeti (Fintype.card Validator) F.f) σ U T N)

/-- The family, run reactively. -/
def Statement : Prop := Certifies ∧ Live ∧ Commits ∧ Includes ∧ OfMysticeti

end ReactiveRun

end Scheme

end LeanDag
