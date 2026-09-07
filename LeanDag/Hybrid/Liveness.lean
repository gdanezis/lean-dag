import LeanDag.Hybrid.Decision
import LeanDag.Mysticeti.Liveness
import Mathlib.Data.Finset.Max

/-!
# Hybrid liveness

H7: the Odontoceti liveness chain at the hybrid quorum, over the
`T`-relativised interface consumed exactly as the base development
states it — `T ⊆ Correct` now excludes the crash-prone through the
derived instance, `q ≤ T.card` is satisfiable because the fully-correct
class numbers at least `q`, and coverage (`SynchronisedOn`) and
production (`Populated`) never mention a leader or a fault class.

Note what liveness does *not* need: `HonestNoEquiv` appears nowhere —
no liveness argument counts an equivocator — and the indirect threshold
`k` is unconstrained, every step below holding at *any* `k`. Only
agreement prices the threshold; the committed-run descent merely
selects the least candidate passing whatever test is in force, which is
exactly what the canonicity premise asks for.

At the tight committee `n = 5·fb + 3·fc + 1` the correct class is
exactly `q`: the reliable set must be *all* of it, the hybrid analogue
of the base development's remark that at `f = 1` every correct
validator is needed for a quorum.

Every decision-valued statement concludes on a validator's own view,
caught up to the horizon it reads (the core `View.CoversUpto` — the
arc shares the core's `View`): the supporters sit one round above the
leader, so a caught-up view holds them
(`directCommitIn_of_coversUpto`), and the descent is view-parametric.
The full view is caught up to every horizon (`View.coversUpto_full`),
so the whole-universe reading is the special case (`liveness.md` §4.2).
-/

namespace LeanDag

namespace Hybrid

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {L : BlockId} {s R N k : ℕ}

/-- The fully-correct class carries the hybrid quorum: liveness's card
hypothesis is satisfiable at `T := Correct`, with equality at the tight
committee. -/
theorem q_le_card_correct : q Validator ≤ (Correct : Finset Validator).card := by
  have h1 := card_correct_add_byzantine (Validator := Validator)
  have h2 : (Faults.byzantine (Validator := Validator)).card ≤ H.fb + H.fc :=
    Faults.card_byzantine
  unfold q
  omega

/-! ## H7a — a reliable leader commits directly, in one step -/

/-- **H7, commit half (O7's mirror).** Post-`R`, a `T`-led slot is
directly committed: coverage makes every `T` block at the decision
round reference the leader's block, and `T` carries the quorum. Two
populated rounds — propose and decide. -/
theorem directCommit_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ DirectCommit U L (S.slotRound s) := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader s) hlead
  refine ⟨L, ⟨hL, hLr, hLc⟩, ?_⟩
  have hsub : T ⊆ supporters U L (S.slotRound s + 1) := by
    intro w hw
    obtain ⟨b, hb, hbc, hbr⟩ := hpop1 w hw
    refine mem_supporters.mpr ⟨b, hb, hbr, ?_, hbc⟩
    exact hs (S.slotRound s) hR b hb hbr (by rw [hbc]; exact hw)
      L hL hLr (by rw [hLc]; exact hlead)
  exact le_trans hcard (Finset.card_le_card hsub)

/-- A view caught up to the decision round sees every supporter, so a
direct commit in the universe is a direct commit in the view. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U} {r : ℕ}
    (h : DirectCommit U L r) (hcov : V.CoversUpto (r + 1)) :
    DirectCommitIn U V L r :=
  HoldsAtLeast.of_coversUpto
    (fun p hp => ⟨(mem_votesFor.mp hp).1, (mem_votesFor.mp hp).2.1.le⟩) hcov h

/-- **H7, as a decision** — at every threshold `k`, on any view caught
up to the decision round. -/
theorem decided_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (V : View Validator BlockId Payload U)
    (hcov : V.CoversUpto (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided k U V s (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_of_coversUpto hdc hcov)⟩

/-- H7 against a horizon: two rounds read off it. -/
theorem decided_of_leader_of_populated (_hT : T ⊆ (Correct : Finset Validator))
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hN : S.slotRound s + 1 ≤ N)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N)
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided k U V s (some L) :=
  decided_of_leader_mem hcard hs hR
    (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega))
    V (hcov.mono hN) hlead

/-! ## H7b, H7c — spanning and the descent

A run of `c` slots spanning eligibility is the relation's
`AnchoredRule.SpansEligible`; under a pipelined identity-round schedule
`c = 2` spans (`spansEligible_of_identity`), two consecutive reliable
leaders, exactly as in the pure-Byzantine two-round development. The
committed-run descent (O9's mirror) is the relation's
`decided_below_of_committed_run` at `Hybrid.exists_least`, at every
threshold `k`. -/

/-- **H7 (O10's mirror).** Under post-`R` coverage, growth to the
horizon, and a recurring run of `c` reliable-led slots, every slot
below the run is decided on any view caught up to the horizon — at
every threshold `k`, the run placed past both the target and `R` by
fairness. The reliable set excludes the crash-prone by construction:
`T ⊆ Correct` reads through the derived instance. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : q Validator ≤ T.card)
    (hspan : (hybridAnchored Validator BlockId Payload k).SpansEligible c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided k U V i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨b, hb, hrunT⟩ := fair (max s k₀)
  have hRb : R ≤ S.slotRound b :=
    le_trans hk₀ (S.mono (le_trans (le_max_right s k₀) hb))
  refine ⟨b, le_trans (le_max_left _ _) hb, hRb, ?_⟩
  intro U N V hpop hs hN hcov
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B, Decided k U V j (some B) := by
    intro j hj1 hj2
    have hlead : S.leader j ∈ T := by
      have := hrunT (j - b) (by omega)
      rwa [Nat.add_sub_cancel' hj1] at this
    have hRj : R ≤ S.slotRound j := le_trans hRb (S.mono hj1)
    have hjr : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono (by omega)
    obtain ⟨L, _, hdec⟩ :=
      decided_of_leader_of_populated hT hcard hs hRj hpop (by omega) V hcov hlead
    exact ⟨L, hdec⟩
  exact AnchoredRule.decided_below_of_committed_run (fun hi h => exists_least hi h) (by omega)
    (fun i hi => hspan b i hi) hrun

/-- **H7 at `T := Correct`** — the whole fully-correct class, which the
tight committee requires exactly. -/
theorem all_decided_below_of_fairRun_correct {c : ℕ} (hc : 0 < c)
    (hspan : (hybridAnchored Validator BlockId Payload k).SpansEligible c)
    (fair : FairRunOn (Correct : Finset Validator) c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r, R ≤ r → r ≤ N → Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided k U V i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl q_le_card_correct hspan
    fair R s

end Hybrid

end LeanDag
