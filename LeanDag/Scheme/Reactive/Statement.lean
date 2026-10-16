import LeanDag.Scheme.Model.Reactive
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Reactive.Mysticeti
/-!
# The family, run reactively — statement

`docs/scheme.md` §13. A responsive validator builds as soon as what the
rule counts has arrived, with the timeout only as a fallback
(`SchemeReactive`). At every row and vote, past GST with the timeout
clearing `2Δ + proc`:

* **every reliable decision-round block certifies** a reliably-led slot's
  leader block (`Certifies`): every reliable block from the proposal to
  the vote round reaches it, so every reliable vote-round block votes;
* **the reactive precondition is the family support's** (`Live`), so
* **a reliably-led slot commits** (`Commits`, the generic `LeaderCommits`);
* **Reactive Mysticeti is an instance** (`OfMysticeti`): every Reactive
  Mysticeti execution with a correct reliable set is the family run
  reactively at the Mysticeti row.

The pacing reads the core's quorum `n − f`, so the rows run reactively are
those whose committee the core's fault model admits (`n ≥ 3f + 1`, with
crash faults counted in `f` where they are).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace ReactiveRun

open Properties

/-- **Every reliable decision-round block certifies** a reliably-led slot's
leader block. -/
def Certifies : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N R : ℕ)
    (rs : SchemeReactive p σ U T N) (k : ℕ) (L : BlockId),
    2 ≤ p.waveLength →
    (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ quorumCard Validator) →
    T ⊆ honest → quorumCard Validator ≤ T.card → rs.gst ≤ R →
    (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    R ≤ S.slotRound k → S.slotRound k + (p.waveLength - 1) ≤ N → S.leader k ∈ T →
    IsLeaderBlock U k L →
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + (p.waveLength - 1) → IsCert p σ U c L

/-- **The reactive precondition is the family support's.** -/
def Live : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (Hon : Finset Validator)
    (S : Slots Validator) (U : (schemeRule p σ Hon).Universe) (V : (schemeRule p σ Hon).View U)
    (T : Finset Validator) (lo K : ℕ),
    2 ≤ p.waveLength →
    (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ quorumCard Validator) →
    reactiveLive p σ Hon S V T lo K →
    (familySupport p σ Hon).live (coreReliability Validator) S V T lo K

/-- **Run reactively, a reliably-led slot commits**, at a commit threshold
the quorum meets. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (Hon : Finset Validator),
    2 ≤ p.waveLength →
    (p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ quorumCard Validator) →
    p.commitThreshold ≤ quorumCard Validator →
    LeaderCommits (schemeRule p σ Hon)
      (fun S {U} V T lo K => reactiveLive p σ Hon S (U := U) V T lo K)

/-- **Reactive Mysticeti is the family run reactively**, at the Mysticeti row
and every vote, when its reliable set is correct. -/
def OfMysticeti : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] [S : Slots Validator]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (N : ℕ),
    T ⊆ (Correct : Finset Validator) → ReactiveM U T N →
    Nonempty (SchemeReactive (Params.mysticeti (Fintype.card Validator) F.f) σ U T N)

/-- The family, run reactively. -/
def Statement : Prop := Certifies ∧ Live ∧ Commits ∧ OfMysticeti

end ReactiveRun

end Scheme

end LeanDag
