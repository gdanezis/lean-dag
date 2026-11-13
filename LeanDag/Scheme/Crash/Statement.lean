import LeanDag.Scheme.Model.Crash
import LeanDag.Scheme.Responsive.Statement
import LeanDag.Properties.Derived.LeaderCommits
/-!
# Crash recovery, partially synchronous — statement

`docs/mechanisms.md` M2. Validators may stop and start again, any number of
times and all at once, until a time `tr`; from `tr` on the reliable
validators stay up (`CrashRun`). A validator keeps on disk what it holds
and builds, rebuilds every round it missed on restart, and sets its timers
again; the network reaches it only while it runs.

* **A crash run is a responsive run past `max gst tr`** (`ToReactive`):
  the same record, rounds, build times and holdings, with GST at
  `max gst tr`.
* **The crash precondition is the reactive one** (`Live`), at every
  reliability, so
* **a reliably led slot commits** (`Commits`) past `max gst tr`, at every
  reliability whose quorum meets the commit and certificate thresholds.
* **Validity at every partially synchronous row** (`RowsValidity`): a
  reliable validator's block is delivered by every reliable validator when
  its author leads a slot past `max gst tr` at or above the block's round
  and a run of reliably led slots follows within the horizon.
* **Every validator may crash at once** (`Inhabited`): at every partially
  synchronous row, a crash run exists in which every validator builds round
  `0`, all are down from time `1` to `D`, and all rebuild on restart.

Safety needs nothing of the crash run: a validator that keeps its blocks on
disk builds no round twice, so the blocks form a `BlockRecord` and every
safety theorem of the family applies to it as it is.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Crash

open Properties

attribute [local instance] noFaults

/-- **A crash run is a responsive run past `max gst tr`.** -/
def ToReactive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N q : ℕ)
    (cr : CrashRun q p σ U T N),
    ∃ rs : SchemeReactive q p σ U T N,
      rs.gst = max cr.gst cr.tr ∧ rs.top = cr.top ∧ rs.built = cr.built ∧
        rs.holds = cr.holds ∧ rs.timeout = cr.timeout ∧ rs.delay = cr.delay ∧ rs.proc = cr.proc

/-- **The crash precondition is the reactive one**, at every reliability. -/
def Live : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (S : Slots Validator) (U : (schemeRule p σ).Universe)
    (V : (schemeRule p σ).View U) (T : Finset Validator) (lo K : ℕ),
    crashLive p σ rel S V T lo K → reactiveLive p σ rel S V T lo K

/-- **With crashes, a reliably led slot commits**, at every reliability
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
      (fun S {U} V T lo K => crashLive p σ rel S (U := U) V T lo K)

/-- **Validity with crashes, at every partially synchronous row**, at its
own committee and parent quorum `n − f − c`. -/
def RowsValidity : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params) (f c : ℕ)
    [P.Quorate (Fintype.card Validator - f - c)],
    p.PSRow (Fintype.card Validator) f c → honestᶜ.card ≤ f →
    ∀ (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
      (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N R d : ℕ)
      (cr : CrashRun (Fintype.card Validator - f - c) p σ U T N),
      T ⊆ honest → Fintype.card Validator - f - c ≤ T.card → max cr.gst cr.tr ≤ R →
      (∀ n, R ≤ n → 2 * cr.delay + cr.proc ≤ cr.timeout n) →
      (∀ blk b, P blk b → Clause.selfParent blk b) →
      0 < d → (schemeAnchored p σ).SpansEligible (S := S) d →
      ∀ (P_k : Validator) (m : BlockId) (k b₀ : ℕ),
        P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k →
        S.leader k = P_k → R ≤ S.slotRound k → (U.block m).round ≤ S.slotRound k → k < b₀ →
        (∀ i, i < d → S.leader (b₀ + i) ∈ T) →
        S.slotRound (b₀ + d - 1) + (p.waveLength - 1) ≤ N →
        ∀ (P_j : Validator) (hj : P_j ∈ T), cr.toReactive.toAsyncPace.Delivers p σ hj m

/-- **Every validator may crash at once**: at every partially synchronous
row, a crash run in which every validator builds round `0`, all are down
from `1` to `D`, and all stay up from `D + 1` on. -/
def Inhabited : Prop :=
  ∀ (n : ℕ) [NeZero n] (p : Params) (f c : ℕ), p.PSRow n f c →
    ∀ [Slots (Fin n)]
      (σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
        (ValidAt (n - f - c) (Clause.distinct.and Clause.selfParent)) Finset.univ) (N D : ℕ),
      ∃ (U : BlockRecord (Fin n) (Lex (ℕ × Fin n)) Unit
          (ValidAt (n - f - c) (Clause.distinct.and Clause.selfParent)) Finset.univ)
        (cr : CrashRun (n - f - c) p σ U Finset.univ N),
        cr.gst = 0 ∧ cr.tr = D + 1 ∧ (∀ v t, 1 ≤ t → t ≤ D → ¬ cr.up v t) ∧
        (∀ r, 2 * cr.delay + cr.proc ≤ cr.timeout r) ∧
        ∀ r ≤ N, ∀ v : Fin n, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

/-- Crash recovery, partially synchronous. -/
def Statement : Prop := ToReactive ∧ Live ∧ Commits ∧ RowsValidity ∧ Inhabited

end Crash

end Scheme

end LeanDag
