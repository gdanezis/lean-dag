import LeanDag.Scheme.Model.Deliver
import LeanDag.Scheme.Model.Reactive
import LeanDag.Scheme.Model.AsyncLive
import LeanDag.Scheme.Model.Async
import LeanDag.Steelhead.Coin.Statement
import Mathlib.Probability.Distributions.Uniform
/-!
# Byzantine atomic broadcast — statement

The decider family against the two definitions of Byzantine atomic
broadcast it is compared with:

* **Sailfish** (Shrestha, Shrothrium, Kate, Nayak, IEEE S&P 2025),
  Definition 1, after Bullshark: agreement, integrity and validity of
  reliable broadcast, and total order.
* **Sui and Duan**, *Signature-Free Atomic Broadcast with Optimal O(n²)
  Messages and O(1) Expected Time* (IEEE S&P 2025), Definition 2.1:
  agreement, total order, liveness and integrity.

A delivered message `a_deliver(m, r, P_k)` is a block, which carries its
round `r` and its author `P_k`. A validator's deliveries are its
delivered sequence (`deliverSeq`): the loop's output from slot `0` on its
view, each committed leader's causal history in order of round and block
id, keeping the first block of each round and author. Delivered sequences
only grow (`Grows`, `RunGrows`), so the order of a sequence is the order
in which its blocks are output.

An honest party of the papers is a validator holding a view of the
record. The safety properties hold for any two views, at every row the
inequalities cover (`Params.Tolerates`; every row of the table is covered,
`Table.RowsCovered`). Agreement holds for the reliable validators of a run
(`AsyncPace`), asynchronous or, with its clock forgotten, partially
synchronous (`SchemeReactive.toAsyncPace`).

* `Integrity` (Sailfish): for every round `r` and author `P_k`, at most
  one block of `r` and `P_k` is delivered.
* `IntegritySD` (Sui and Duan): no block is delivered twice, and every
  delivered block was built by some validator: it is a block of the record.
* `TotalOrder` (Sailfish): if one validator delivers `x` before `y`, no
  validator delivers `y` before `x`.
* `TotalOrderSD` (Sui and Duan): if one validator delivers `x` before
  `y`, any validator delivering `y` has delivered `x` before it.
* `Agreement` (both): if a reliable validator delivers `b`, every reliable
  validator delivers `b` from some time on.
* `ValidityPS` (Sailfish), partially synchronous: a reliable validator's
  block is eventually delivered by every reliable validator, when its
  author leads a slot past GST at or above the block's round and a run of
  reliably-led slots follows within the horizon. `LivenessPS` (Sui and
  Duan) is the author's own delivery.
* `ValidityRoundRobin`: `ValidityPS` under round-robin on one slot per
  round, at `waveLength · (n − |T|) < n`, for every reliable block at
  least two rotations below the horizon.
* `ValidityAsync` (Sailfish) and `LivenessAsync` (Sui and Duan),
  asynchronous, against an adversary that does not see the coin: when the
  author's block of some round `r` is referenced by every reliable block
  of round `r + 1`, the block fails to be eventually delivered with
  probability at most `badBlockBoundAt c d ^ M` over `M` blocks of `d`
  coins from round `r + 2` on, which vanishes as `M` grows
  (`badBlockBound_tendsto_zero`). Without such a round the claim fails:
  references reach one round down, so a reliable validator kept late at
  every round has blocks no later block references.

Validity is stated on records whose blocks reference their author's
previous block (`Clause.selfParent`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace AtomicBroadcast

open scoped ENNReal

attribute [local instance] noFaults


/-- **A delivered sequence only grows** as the view grows and the scan
reaches further, at the rows the inequalities cover. -/
def Grows : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V₁ V₂ : U.View) (N₁ N₂ : ℕ),
    p.Tolerates honest f q → V₁.ids ⊆ V₂.ids → N₁ ≤ N₂ →
    deliverSeq p σ U V₁ N₁ <+: deliverSeq p σ U V₂ N₂

/-- **A reliable validator's delivered sequence only grows** along a run,
at the rows the inequalities cover. -/
def RunGrows : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (M : ℕ),
    p.Tolerates honest f q →
    ∀ v (hv : v ∈ T) (t t' : ℕ), t ≤ t' → ap.deliverAt p σ hv M t <+: ap.deliverAt p σ hv M t'

/-- **Integrity, Sailfish's form**: for every round `r` and author `P_k`,
a validator delivers at most one block of round `r` by `P_k`, whatever
its content. -/
def Integrity : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (N : ℕ)
    (r : ℕ) (P_k : Validator),
    ((deliverSeq p σ U V N).filter
      (fun b => (U.block b).round = r ∧ (U.block b).creator = P_k)).length ≤ 1

/-- **Integrity, Sui and Duan's form**: a validator delivers a block at most
once, and only a block some validator built. -/
def IntegritySD : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (N : ℕ),
    (deliverSeq p σ U V N).Nodup ∧ ∀ b ∈ deliverSeq p σ U V N, b ∈ U.ids

/-- **Total order, Sailfish's form**, at the rows the inequalities cover: if
a validator delivers `x` before `y`, no validator delivers `y` before
`x`. -/
def TotalOrder : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V_i V_j : U.View) (N_i N_j : ℕ)
    (x y : BlockId),
    p.Tolerates honest f q →
    Before (deliverSeq p σ U V_i N_i) x y → ¬ Before (deliverSeq p σ U V_j N_j) y x

/-- **Total order, Sui and Duan's form**, at the rows the inequalities
cover: if a validator delivers `x` before `y`, a validator that delivers
`y` has delivered `x` before it. -/
def TotalOrderSD : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V_i V_j : U.View) (N_i N_j : ℕ)
    (x y : BlockId),
    p.Tolerates honest f q →
    Before (deliverSeq p σ U V_i N_i) x y → y ∈ deliverSeq p σ U V_j N_j →
    Before (deliverSeq p σ U V_j N_j) x y

/-- **Agreement**, at the rows the inequalities cover: if a reliable
validator delivers `b`, every reliable validator delivers `b` from some
time on. -/
def Agreement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (M : ℕ),
    p.Tolerates honest f q →
    ∀ (P_i : Validator) (hi : P_i ∈ T) (t : ℕ) (b : BlockId), b ∈ ap.deliverAt p σ hi M t →
      ∀ (P_j : Validator) (hj : P_j ∈ T), ∃ t', ∀ t'', t' ≤ t'' → b ∈ ap.deliverAt p σ hj M t''

/-- **Validity, Sailfish's form**, partially synchronous, at the rows the
inequalities cover: in a reactive run past GST whose reliable set meets
the certificate and commit thresholds, a block `m` by a reliable validator
`P_k` is eventually delivered by every reliable validator, when `P_k`
leads a slot `k` past GST at or above `m`'s round and the `d` slots from
`b₀ > k` are led by reliable validators within the horizon. -/
def ValidityPS : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N R qr d : ℕ)
    (rs : SchemeReactive qr p σ U T N),
    p.Tolerates honest f q → p.CertFits qr → p.commitThreshold ≤ T.card →
    T ⊆ honest → qr ≤ T.card → rs.gst ≤ R →
    (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    (∀ blk b, P blk b → Clause.selfParent blk b) →
    0 < d → (schemeAnchored p σ).SpansEligible (S := S) d →
    ∀ (P_k : Validator) (m : BlockId) (k b₀ : ℕ),
      P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k →
      S.leader k = P_k → R ≤ S.slotRound k → (U.block m).round ≤ S.slotRound k → k < b₀ →
      (∀ i, i < d → S.leader (b₀ + i) ∈ T) →
      S.slotRound (b₀ + d - 1) + (p.waveLength - 1) ≤ N →
      ∀ (P_j : Validator) (hj : P_j ∈ T), rs.toAsyncPace.Delivers p σ hj m

/-- **Liveness, Sui and Duan's form**, partially synchronous, under
`ValidityPS`'s conditions: the author `P_k` eventually delivers its own
block `m`. -/
def LivenessPS : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N R qr d : ℕ)
    (rs : SchemeReactive qr p σ U T N),
    p.Tolerates honest f q → p.CertFits qr → p.commitThreshold ≤ T.card →
    T ⊆ honest → qr ≤ T.card → rs.gst ≤ R →
    (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    (∀ blk b, P blk b → Clause.selfParent blk b) →
    0 < d → (schemeAnchored p σ).SpansEligible (S := S) d →
    ∀ (P_k : Validator) (hk : P_k ∈ T) (m : BlockId) (k b₀ : ℕ),
      m ∈ U.ids → (U.block m).creator = P_k →
      S.leader k = P_k → R ≤ S.slotRound k → (U.block m).round ≤ S.slotRound k → k < b₀ →
      (∀ i, i < d → S.leader (b₀ + i) ∈ T) →
      S.slotRound (b₀ + d - 1) + (p.waveLength - 1) ≤ N →
      rs.toAsyncPace.Delivers p σ hk m

/-- **Validity under round-robin**, partially synchronous, at the rows
the inequalities cover: on `n` validators led in turn, one slot per round,
when the reliable set leaves fewer than `n` slots of each rotation to a
wave of the others (`waveLength · (n − |T|) < n`), a reliable validator's
block `m` is eventually delivered by every reliable validator once two
rotations past GST and past `m`'s round, and a wave each way, lie below
the horizon. -/
def ValidityRoundRobin : Prop :=
  ∀ (n : ℕ) [NeZero n] (BlockId Payload : Type) [LinearOrder BlockId]
    (P : Validity (Fin n) BlockId Payload) [P.Mechanised] (q : ℕ) [P.Quorate q]
    (honest : Finset (Fin n)) (f : ℕ) (p : Params)
    (σ : VoteSel (Fin n) BlockId Payload P honest)
    (U : BlockRecord (Fin n) BlockId Payload P honest) (T : Finset (Fin n)) (N R qr : ℕ)
    (rs : SchemeReactive (S := roundRobinSlots n) qr p σ U T N),
    p.Tolerates honest f q → p.CertFits qr → p.commitThreshold ≤ T.card →
    T ⊆ honest → qr ≤ T.card → rs.gst ≤ R →
    (∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) →
    (∀ blk b, P blk b → Clause.selfParent blk b) →
    p.waveLength * (n - T.card) < n →
    ∀ (P_k : Fin n) (m : BlockId), P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k →
      n * (max R (U.block m).round + 2) + 2 * p.waveLength ≤ N →
      ∀ (P_j : Fin n) (hj : P_j ∈ T),
        (rs.toAsyncPace (S := roundRobinSlots n)).Delivers (S := roundRobinSlots n) p σ hj m

/-- **Validity, Sailfish's form**, asynchronous, at the rows the
inequalities cover, against an adversary that does not see the coin: in an
asynchronous run whose reliable set meets the commit threshold and, with
the quorum, exceeds the committee, when the block `x` of a reliable
validator `P_k` at round `r` is referenced by every reliable block of
round `r + 1`, a block `m` of `P_k` at or below round `r` fails to be
eventually delivered by every reliable validator with probability at most
`badBlockBoundAt c d ^ M`, over `M` blocks of `d` coins from a slot `s₀`
at round `r + 2` or above. -/
def ValidityAsync : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    (dflt : Validator) (s₀ d M c : ℕ),
    p.Tolerates honest f q → p.CertFits q → p.commitThreshold ≤ T.card → qp ≤ T.card →
    T ⊆ honest → Fintype.card Validator < q + T.card → 0 < d →
    (schemeAnchored p σ).SpansEligible (S := S₀) d →
    S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N →
    (∀ s, s₀ ≤ s → s < s₀ + M * d → c ≤ (safeAt p U (S₀.slotRound s)).card) →
    (∀ blk b, P blk b → Clause.selfParent blk b) →
    ∀ (P_k : Validator) (m x : BlockId) (r : ℕ),
      P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k → (U.block m).round ≤ r →
      x ∈ U.ids → (U.block x).creator = P_k → (U.block x).round = r →
      (∀ c ∈ U.ids, (U.block c).creator ∈ T → (U.block c).round = r + 1 →
        x ∈ (U.block c).refs) →
      r + 2 ≤ S₀.slotRound s₀ →
      (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
          {g | ¬ ∀ (P_j : Validator) (hj : P_j ∈ T),
            ap.Delivers (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt)) p σ hj m} ≤
        Steelhead.Coin.badBlockBoundAt Validator c d ^ M

/-- **Liveness, Sui and Duan's form**, asynchronous, under
`ValidityAsync`'s conditions: the author `P_k` fails to eventually deliver
its own block `m` with probability at most `badBlockBoundAt c d ^ M`. -/
def LivenessAsync : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    (dflt : Validator) (s₀ d M c : ℕ),
    p.Tolerates honest f q → p.CertFits q → p.commitThreshold ≤ T.card → qp ≤ T.card →
    T ⊆ honest → Fintype.card Validator < q + T.card → 0 < d →
    (schemeAnchored p σ).SpansEligible (S := S₀) d →
    S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N →
    (∀ s, s₀ ≤ s → s < s₀ + M * d → c ≤ (safeAt p U (S₀.slotRound s)).card) →
    (∀ blk b, P blk b → Clause.selfParent blk b) →
    ∀ (P_k : Validator) (hk : P_k ∈ T) (m x : BlockId) (r : ℕ),
      m ∈ U.ids → (U.block m).creator = P_k → (U.block m).round ≤ r →
      x ∈ U.ids → (U.block x).creator = P_k → (U.block x).round = r →
      (∀ c ∈ U.ids, (U.block c).creator ∈ T → (U.block c).round = r + 1 →
        x ∈ (U.block c).refs) →
      r + 2 ≤ S₀.slotRound s₀ →
      (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
          {g | ¬ ap.Delivers (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
            p σ hk m} ≤
        Steelhead.Coin.badBlockBoundAt Validator c d ^ M

/-- The atomic-broadcast claims. -/
def Statement : Prop :=
  Grows ∧ RunGrows ∧ Integrity ∧ IntegritySD ∧ TotalOrder ∧ TotalOrderSD ∧ Agreement ∧
    ValidityPS ∧ LivenessPS ∧ ValidityRoundRobin ∧ ValidityAsync ∧ LivenessAsync

end AtomicBroadcast

end Scheme

end LeanDag
