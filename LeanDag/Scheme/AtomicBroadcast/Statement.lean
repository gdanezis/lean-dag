import LeanDag.Scheme.Model.Deliver
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

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace AtomicBroadcast

/-- **A delivered sequence only grows** as the view grows and the scan
reaches further, at the rows the inequalities cover. -/
def Grows : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V₁ V₂ : U.View) (N₁ N₂ : ℕ),
    p.Tolerates honest f q → V₁.ids ⊆ V₂.ids → N₁ ≤ N₂ →
    deliverSeq p σ U V₁ N₁ <+: deliverSeq p σ U V₂ N₂

/-- **A reliable validator's delivered sequence only grows** along a run,
at the rows the inequalities cover. -/
def RunGrows : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
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
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (N : ℕ)
    (r : ℕ) (P_k : Validator),
    ((deliverSeq p σ U V N).filter
      (fun b => (U.block b).round = r ∧ (U.block b).creator = P_k)).length ≤ 1

/-- **Integrity, Sui and Duan's form**: a validator delivers a block at most
once, and only a block some validator built. -/
def IntegritySD : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (N : ℕ),
    (deliverSeq p σ U V N).Nodup ∧ ∀ b ∈ deliverSeq p σ U V N, b ∈ U.ids

/-- **Total order, Sailfish's form**, at the rows the inequalities cover: if
a validator delivers `x` before `y`, no validator delivers `y` before
`x`. -/
def TotalOrder : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
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
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
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
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (M : ℕ),
    p.Tolerates honest f q →
    ∀ (P_i : Validator) (hi : P_i ∈ T) (t : ℕ) (b : BlockId), b ∈ ap.deliverAt p σ hi M t →
      ∀ (P_j : Validator) (hj : P_j ∈ T), ∃ t', ∀ t'', t' ≤ t'' → b ∈ ap.deliverAt p σ hj M t''

/-- The atomic-broadcast claims proved so far. -/
def Statement : Prop :=
  Grows ∧ RunGrows ∧ Integrity ∧ IntegritySD ∧ TotalOrder ∧ TotalOrderSD ∧ Agreement

end AtomicBroadcast

end Scheme

end LeanDag
