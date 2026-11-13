import LeanDag.Scheme.Model.Local
import LeanDag.Barnacle.Model.Anchored
import LeanDag.Barnacle.Model.Schedule
import LeanDag.Timed.Silent
import LeanDag.Scheme.Model.Reactive
import LeanDag.Scheme.Model.Async
import LeanDag.Scheme.Model.Deliver
/-!
# The decider as a Barnacle live rule

`schemeLive p σ rel` is the decider at `p` and `σ` read by Barnacle's runs
(`LeanDag/Barnacle/`), with the DAG good from a round at the reliability
`rel` (`Timed.Good`). HammerHead's runs are Barnacle's at
`Boundary.atThreshold` and read the same rule.

`p.Scheduled n slack` is what Barnacle's round-robin liveness asks of a
row on `n` validators of which at most `slack` are unreliable.

`schemeLiveSilent p σ rel fb` is the same rule with the DAG good when, in
addition, the validators outside a synchronised quorum are silent or among
`fb` others (`Timed.SilentGood`). `p.SkipScheduled n slack fb` is what
round-robin liveness asks there, on one slot per round.

`schemeLiveReactive p σ rel` is the same rule with the DAG good under a
schedule `S` when a quorum of `rel` runs it responsively under `S`
(`reactiveGood`): past GST, its timeout clearing `2Δ + proc`, its
validators waiting for `S`'s leaders up to the horizon. A responsive
validator waits only for the leaders it knows, so this goodness, unlike
the timed ones, reads the schedule.

`schemeLiveAsync p σ rel c₀` is the same rule run asynchronously, its
leaders elected by a coin: the DAG is good under `S` when a quorum of `rel`
populates every round up to the horizon and, from every round, `c₀` rounds
hold a wave of consecutive rounds whose first slot under `S` is led by a
safe validator (`asyncGood`). No validator waits for a leader, so the
goodness reads the schedule only through who leads each round's first slot.

Definitions only; the theorems are `Scheme/Schedules/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

/-- **The decider as a live rule**, at reliability `rel`. -/
def schemeLive (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) : Barnacle.LiveRule Validator BlockId Payload :=
  Barnacle.liveOfAnchored (schemeAnchored p σ) (fun _ => rfl) rel

/-- **The row fits round-robin scheduling** on `n` validators, at most
`slack` unreliable: `n − slack` meets the certificate and commit
thresholds, and `waveLength · slack + 1 ≤ n`. -/
def Params.Scheduled (p : Params) (n slack : ℕ) : Prop :=
  p.certThreshold ≤ n - slack ∧ p.commitThreshold ≤ n - slack ∧ p.waveLength * slack + 1 ≤ n

/-- **The decider as a live rule whose crashed validators are silent**, at
reliability `rel` with at most `fb` validators neither synchronised nor
silent. -/
def schemeLiveSilent (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (fb : ℕ) : Barnacle.LiveRule Validator BlockId Payload :=
  { Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl) with
    Good := fun _ => Timed.SilentGood (schemeAnchored p σ).toDagRule rel fb }

/-- **The row fits round-robin scheduling on one slot per round with silent
crashes**, on `n` validators with at most `slack` unreliable and `fb`
neither reliable nor silent: `n − slack` meets the certificate, commit and
skip thresholds, the vote round is one above the proposal, and
`(waveLength − 1)·fb + slack + 1 ≤ n`. -/
def Params.SkipScheduled (p : Params) (n slack fb : ℕ) : Prop :=
  p.certThreshold ≤ n - slack ∧ p.commitThreshold ≤ n - slack ∧ p.skipThreshold ≤ n - slack ∧
    p.voteOffset = 1 ∧ (p.waveLength - 1) * fb + slack + 1 ≤ n

/-- **The heads of `C` are a permutation of round-robin.** -/
def PermRR {n : ℕ} (hn : 0 < n) (C : Barnacle.Config (Fin n)) : Prop :=
  ∃ π : Equiv.Perm (Fin n), C.head = fun ρ => π (Barnacle.roundRobin n hn ρ)

/-- **One slot per round, its heads a permutation of round-robin.** -/
def SinglePermRR {n : ℕ} (hn : 0 < n) (C : Barnacle.Config (Fin n)) : Prop :=
  (∀ r, C.slotsAt r = 1) ∧ PermRR hn C

attribute [local instance] noFaults in
/-- **Good under `S`, responsively**: a quorum `T` of `rel` of honest
validators runs the family responsively under `S` past GST at `Rnd`, the
timeout clearing `2Δ + proc` from `Rnd`, and waits for `S`'s leaders up to
`N`. -/
def reactiveGood [Nonempty Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator)
    (S : Slots Validator) (U : BlockRecord Validator BlockId Payload P honest) (Rnd N : ℕ) :
    Prop :=
  ∃ T : Finset Validator, rel.IsQuorum T ∧ T ⊆ honest ∧
    ∃ (N' : ℕ) (rs : SchemeReactive (S := S) (Fintype.card Validator - rel.slack) p σ U T N'),
      rs.gst ≤ Rnd ∧ (∀ n, Rnd ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) ∧ N ≤ rs.waits

/-- **The decider as a live rule, run responsively**, at reliability
`rel`. -/
def schemeLiveReactive [Nonempty Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator) :
    Barnacle.LiveRule Validator BlockId Payload :=
  { Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl) with
    Good := fun S U Rnd N => reactiveGood p σ rel S U Rnd N }

/-- **Good under `S`, asynchronously**: a quorum `T` of `rel` of honest
validators populates every round up to `N`, and from every round `r` past
`Rnd`, within `c₀` rounds, the first slots of a wave of consecutive rounds
are led by safe validators. -/
def asyncGood (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (c₀ : ℕ) (S : Slots Validator)
    (U : BlockRecord Validator BlockId Payload P honest) (Rnd N : ℕ) : Prop :=
  ∃ T : Finset Validator, rel.IsQuorum T ∧ T ⊆ honest ∧ (∀ r ≤ N, PopulatedOn U T r) ∧
    ∀ r, Rnd ≤ r → r + c₀ + (p.waveLength - 1 + 1) ≤ N + 1 →
      ∃ ρ, r ≤ ρ ∧ ρ + (p.waveLength - 1 + 1) ≤ r + c₀ ∧
        ∀ i, i < p.waveLength - 1 + 1 → ∀ κ, S.slotRound κ = ρ + i →
          (∀ κ', κ' < κ → S.slotRound κ' < ρ + i) → S.leader κ ∈ safeAt p U (ρ + i)

/-- **The decider as a live rule, run asynchronously**, at reliability `rel`
and gap `c₀`. -/
def schemeLiveAsync (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (rel : Reliability Validator) (c₀ : ℕ) : Barnacle.LiveRule Validator BlockId Payload :=
  { Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl) with
    Good := fun S U Rnd N => asyncGood p σ rel c₀ S U Rnd N }

/-- **Safe heads come in runs**: from every round `r` past `Rnd`, within
`c₀` rounds, the heads `h` names for a wave of consecutive rounds are safe. -/
def SafeHeadRuns (p : Params) (U : BlockRecord Validator BlockId Payload P honest)
    (h : ℕ → Validator) (c₀ Rnd N : ℕ) : Prop :=
  ∀ r, Rnd ≤ r → r + c₀ + (p.waveLength - 1 + 1) ≤ N + 1 →
    ∃ ρ, r ≤ ρ ∧ ρ + (p.waveLength - 1 + 1) ≤ r + c₀ ∧
      ∀ i, i < p.waveLength - 1 + 1 → h (ρ + i) ∈ safeAt p U (ρ + i)

/-- **The heads a coin draw names**: `J · M` blocks of `w` coins, the head of
round `ρ` the coin of block `ρ / w` at `ρ mod w`, and `dflt` past them. -/
def coinHead {J M w : ℕ} (dflt : Validator) (g : Fin (J * M) → Fin w → Validator) (ρ : ℕ) :
    Validator :=
  if h : ρ / w < J * M ∧ 0 < w then g ⟨ρ / w, h.1⟩ ⟨ρ % w, Nat.mod_lt _ h.2⟩ else dflt

/-- **A table supports `k` validators with weight `e`**: at least `k`
validators each fill at least `e` of its entries. A reputation distribution
over leaders, read by a uniform index into the table. -/
def Supports {m : ℕ} (tbl : Fin m → Validator) (k e : ℕ) : Prop :=
  ∃ D : Finset Validator, k ≤ D.card ∧ ∀ v ∈ D, e ≤ (Finset.univ.filter fun j => tbl j = v).card

/-- **The delivered sequence of a scheduled run** to height `K'`: the
blocks delivered for the committed leaders of its ledger, through
references and weak references. -/
noncomputable def runDeliver {p : Params} {σ : VoteSel Validator BlockId Payload P honest}
    {Par : Barnacle.Params} {B : Barnacle.Boundary Validator}
    {upd : Barnacle.UpdateRule (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl))}
    {C₀ : Barnacle.Config Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {K : ℕ}
    (Rn : Barnacle.Run (Barnacle.ofAnchored (schemeAnchored p σ) (fun _ => rfl)) Par B upd C₀ U V K)
    (wk : BlockId → Finset BlockId) (K' : ℕ) : List BlockId :=
  deliverLeaders U wk (Rn.ledgerUpto K')

end Scheme

end LeanDag
