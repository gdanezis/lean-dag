import LeanDag.BlackMarlin.Model.Round
/-!
# Black Marlin — the reactive schedule, stated

What the round rule of L38–L41 yields when a validator builds as soon as
it can conclude the round rather than waiting out every timeout
(`black-marlin.md` §10). BMR1 says every reliable round-above block
references a reliable anchor, past GST; BMR2 is the resulting commit,
with no coverage hypothesis. BMR3 says a validator holding the two
rounds below can conclude the round, given three consecutive reliable
anchors — one more than the commit rule needs — and BMR4 says only
entering costs that, not staying. BMR5 bounds the round-entry latency
and BMR6 says it can undercut the timeout entirely.

**Where this differs from the core's reactive arc.** The exit clause is
the same, `anchor_or_wait`, but the core's fires once the leader's block
is held while Black Marlin's fires once the round rule's three further
clauses are satisfied — BMR3's cost, paid once per BMR4.

`δ` is the actual per-block propagation bound of the execution, a
premise about this run rather than an assumption about the network in
general, so the bounds degrade continuously as it approaches the
timeout.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Reactive

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
  {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {N : ℕ}

/-- **BMR1, the fallback route.** Past GST, every reliable block at the
round above a reliable anchor references it: the exit route holds it by
construction, and convergence within `Δ` carries it to the fallback
route before its timeout builds. -/
def Votes (pc : Pace U T N) : Prop :=
  ∀ (R r : ℕ) (A : BlockId),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    R ≤ r → r + 1 ≤ N →
    Rot.anchor r ∈ T → IsAnchor U r A →
    VotesAt U T r A

/-- **BMR2, reactive liveness.** A run of two reliable anchors past GST
is committed — the premise of BML1 with `SynchronisedOn` removed, since
the reactive discipline supplies the references the rule counts and the
trunk supplies the production. -/
def ReactiveCommit (pc : Pace U T N) : Prop :=
  ∀ (R r : ℕ),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    R ≤ r → r + 2 ≤ N →
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T →
    ∃ L, IsAnchor U r L ∧ Committed U L r

/-- **BMR3, the exit fires — at a run of three.** A validator holding
every reliable block of rounds `r + 1` and `r + 2` can conclude round
`r + 2`, given reliable anchors at `r`, `r + 1` and `r + 2` — three
rounds of anchors, against the commit rule's two. -/
def Exit (pc : Pace U T N) : Prop :=
  ∀ (r : ℕ) (v : Validator) (t : ℕ),
    quorumCard Validator ≤ T.card → v ∈ T → r + 2 ≤ N →
    (∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n → b ∈ pc.holds v t) →
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T → Rot.anchor (r + 2) ∈ T →
    (∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A) →
    ConcludesAt U (pc.toPaceCore.viewAt v t) (r + 2)

/-- **BMR4, and a run of two to stay.** A validator that already saw the
round-`r` anchor supported needs neither that anchor reliable nor the
references at round `r`: what the round rule checked once it never
checks again, since holdings only grow. So the run of three is the cost
of entering the fast path, not of remaining on it. -/
def ExitSustained (pc : Pace U T N) : Prop :=
  ∀ (r : ℕ) (v : Validator) (t₀ t : ℕ),
    quorumCard Validator ≤ T.card → v ∈ T → r + 2 ≤ N →
    (∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n → b ∈ pc.holds v t) →
    SuppAnchorIn U (pc.toPaceCore.viewAt v t₀) r → t₀ ≤ t →
    Rot.anchor (r + 1) ∈ T → Rot.anchor (r + 2) ∈ T →
    (∀ A, IsAnchor U (r + 1) A → VotesAt U T (r + 1) A) →
    ConcludesAt U (pc.toPaceCore.viewAt v t) (r + 2)

/-- **BMR5, latency.** With reliable blocks propagating within `δ`, the
round above is entered within `D + δ + proc` of round entry — drift to
the last builder, `δ` to arrive, `proc` to conclude — and past GST the
spread needs no supplying, catch-up collapsing it to `Δ + proc`. The
timeout appears in neither bound. -/
def Latency (pc : Pace U T N) : Prop :=
  ∀ (r : ℕ) (v : Validator) (δ D R : ℕ),
    quorumCard Validator ≤ T.card → v ∈ T → r + 3 ≤ N →
    (∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (pc.built ((U.block b).creator) n + δ)) →
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T → Rot.anchor (r + 2) ∈ T →
    (∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A) →
    ((∀ u ∈ T, ∀ w ∈ T, pc.built u (r + 2) ≤ pc.built w (r + 2) + D) →
      pc.built v (r + 3) ≤ pc.built v (r + 2) + D + δ + pc.proc) ∧
    (pc.gst ≤ R → R ≤ r + 2 →
      pc.built v (r + 3) ≤ pc.built v (r + 2) + pc.delay + δ + 2 * pc.proc)

/-- **BMR6, the timeout never fires.** When delivery, drift and
processing together undercut the timeout, every reliable validator
concludes strictly before its deadline and the protocol runs at network
speed. -/
def NoTimeout (pc : Pace U T N) : Prop :=
  ∀ (r : ℕ) (v : Validator) (δ R : ℕ),
    quorumCard Validator ≤ T.card → v ∈ T → r + 3 ≤ N →
    pc.gst ≤ R → R ≤ r + 2 →
    (∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (pc.built ((U.block b).creator) n + δ)) →
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T → Rot.anchor (r + 2) ∈ T →
    (∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A) →
    pc.delay + δ + 2 * pc.proc < pc.timeout (r + 2) →
    pc.built v (r + 3) < pc.built v (r + 2) + pc.timeout (r + 2)

/-- The reactive schedule of Black Marlin, over every fault
configuration, rotation, block universe and pacing structure the model
admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (N : ℕ)
    (pc : Pace U T N),
    Votes pc ∧ ReactiveCommit pc ∧ Exit pc ∧ ExitSustained pc ∧
      Latency pc ∧ NoTimeout pc

end Reactive

end BlackMarlin

end LeanDag
