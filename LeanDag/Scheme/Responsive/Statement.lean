import LeanDag.Scheme.AtomicBroadcast.Statement
import LeanDag.Scheme.Model.Params
import Mathlib.Data.Prod.Lex
/-!
# Responsive liveness at every partially synchronous row — statement

`docs/mechanisms.md` M1. A responsive validator builds as soon as what the
rule counts has arrived, with the timeout only as a fallback
(`SchemeReactive`). At each partially synchronous row at its committee
(`Params.PSRow`), with parent quorum `n − f − c`:

* **a responsive run exists** (`Inhabited`): on `n` validators, at every
  vote rule and every schedule, the full record up to any round is run by
  a `SchemeReactive` over all validators, past GST from time `0`, its
  timeout clearing `2Δ + proc`;
* **Validity holds** (`RowsValidity`): in a responsive run past GST whose
  reliable set is honest and holds `n − f − c` validators, on records whose
  blocks reference their author's previous block, a block of a reliable
  validator `P_k` is delivered by every reliable validator once `P_k` leads
  a slot past GST at or above the block's round and a run of reliably led
  slots follows within the horizon. The author's own delivery, Sui and
  Duan's Liveness, is the case `P_j = P_k`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Responsive

attribute [local instance] noFaults

/-- **A responsive run exists at every partially synchronous row**: the
full record on `n` validators up to round `N`, at the row's parent
quorum, run responsively by all validators past GST from time `0`. -/
def Inhabited : Prop :=
  ∀ (n : ℕ) [NeZero n] (p : Params) (f c : ℕ), p.PSRow n f c →
    ∀ [Slots (Fin n)]
      (σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
        (ValidAt (n - f - c) (Clause.distinct.and Clause.selfParent)) Finset.univ) (N : ℕ),
      ∃ (U : BlockRecord (Fin n) (Lex (ℕ × Fin n)) Unit
          (ValidAt (n - f - c) (Clause.distinct.and Clause.selfParent)) Finset.univ)
        (rs : SchemeReactive (n - f - c) p σ U Finset.univ N),
        rs.gst = 0 ∧ (∀ r, 2 * rs.delay + rs.proc ≤ rs.timeout r) ∧
        ∀ r ≤ N, ∀ v : Fin n, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

/-- **Validity at every partially synchronous row**, at its own committee
and parent quorum `n − f − c`. -/
def RowsValidity : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params) (f c : ℕ)
    [P.Quorate (Fintype.card Validator - f - c)],
    p.PSRow (Fintype.card Validator) f c → honestᶜ.card ≤ f →
    ∀ (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
      (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N R d : ℕ)
      (rs : SchemeReactive (Fintype.card Validator - f - c) p σ U T N),
      T ⊆ honest → Fintype.card Validator - f - c ≤ T.card → rs.gst ≤ R →
      (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
      (∀ blk b, P blk b → Clause.selfParent blk b) →
      0 < d → (schemeAnchored p σ).SpansEligible (S := S) d →
      ∀ (P_k : Validator) (m : BlockId) (k b₀ : ℕ),
        P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k →
        S.leader k = P_k → R ≤ S.slotRound k → (U.block m).round ≤ S.slotRound k → k < b₀ →
        (∀ i, i < d → S.leader (b₀ + i) ∈ T) →
        S.slotRound (b₀ + d - 1) + (p.waveLength - 1) ≤ rs.waits →
        ∀ (P_j : Validator) (hj : P_j ∈ T), rs.toAsyncPace.Delivers p σ hj m

/-- Responsive liveness at every partially synchronous row. -/
def Statement : Prop := Inhabited ∧ RowsValidity

end Responsive

end Scheme

end LeanDag
