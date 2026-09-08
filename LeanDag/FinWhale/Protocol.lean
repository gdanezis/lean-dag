import LeanDag.FinWhale.Holdings
import LeanDag.FinWhale.Model.Protocol
import LeanDag.FinWhale.Validity
import LeanDag.FinWhale.View
/-!
# FinWhale — what the protocol guarantees

`Run` collects one execution — the blocks, schedule and network that
carried them — and the four properties below are stated over it, with
hypotheses about the run alone: which validators are correct, and how
far the horizon reaches. Each is a corollary of a theorem proved
elsewhere, restated to no longer mention verdict assignments, views,
well-formedness or bounds.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type}

namespace Run

variable (run : Run Validator BlockId Payload) {v w : Validator}

/-- And what it holds is a view: part of the run, closed under
references. -/
def viewOf (hv : v ∈ (Correct : Finset Validator)) : run.dag.View :=
  holdsView run.pace run.ids_eq run.block_eq hv (settled run.pace)

/-- **The verdicts a validator reaches**, by running the reverse pass on
its own view. -/
noncomputable def verdicts (hv : v ∈ (Correct : Finset Validator)) : ℕ → Verdict BlockId :=
  decOf run.sched (EligibleAt (S := run.sched) 2) (run.viewOf hv).toRecord
    (chooseLeast run.sched run.dag) run.horizon

/-- **And what it delivers**: the causal histories of its committed
leader blocks, in order, each block once. -/
noncomputable def delivers (hv : v ∈ (Correct : Finset Validator)) (k : ℕ) : List BlockId :=
  linearise (histOf run.dag) (commitSeq (run.verdicts hv) k)

/-! ## What each validator's pass amounts to

Five facts the four properties below are assembled from, none of them
a hypothesis of a run. -/

/-- The blocks a validator holds sit below the run's horizon. -/
theorem view_rounds_le (hv : v ∈ (Correct : Finset Validator)) :
    ∀ b ∈ run.view v, (run.dag.block b).round ≤ run.horizon :=
  fun b hb => run.rounds_le b ((run.viewOf hv).subset_ids hb)

/-- A run's schedule is the identity, so eligibility is the pass's
`r + 2 < a` — three rounds up is three slots up. -/
theorem elig_iff {r a : ℕ} : EligibleAt (S := run.sched) 2 r a ↔ r + 2 < a := by
  simp only [EligibleAt, run.roundId]

/-- The pass's slot horizon is its round horizon, because the two agree
under the identity schedule. -/
theorem slot_le : ∀ r, run.sched.slotRound r ≤ run.horizon → r ≤ run.horizon := by
  intro r h; rwa [run.roundId] at h

/-- Its verdicts follow the reverse pass. -/
theorem wellFormed (hv : v ∈ (Correct : Finset Validator)) :
    WellFormed (EligibleAt (S := run.sched) 2) (viewCommit run.sched run.dag (run.viewOf hv))
      (viewSkip run.sched run.dag (run.viewOf hv)) (chooseLeast run.sched run.dag)
      (run.verdicts hv) :=
  wellFormed_decOf (run.view_rounds_le hv) (fun _ _ => lt_of_eligibleAt (S := run.sched)) run.slot_le
    (chooseLeast run.sched run.dag)

/-- A committed verdict names a block of its slot. -/
theorem slot_of_verdicts (hv : v ∈ (Correct : Finset Validator)) {r : ℕ} {A : BlockId}
    (h : run.verdicts hv r = Verdict.commit A) : A ∈ slotBlocks run.sched run.dag r :=
  mem_slotBlocks_of_decOf (fun _ => slotBlocks_restrict) chooseSound_least
    (fun _ _ => lt_of_eligibleAt (S := run.sched)) h

/-- Nothing above the horizon is decided. -/
theorem undecided_of_gt (hv : v ∈ (Correct : Finset Validator)) {s : ℕ}
    (hs : run.horizon < s) : run.verdicts hv s = Verdict.undecided :=
  decOf_of_gt hs

/-- Past the stable round, a validator holds every reliable block of
every round below the horizon. -/
theorem held (hv : v ∈ (Correct : Finset Validator)) :
    ∀ n, run.stable ≤ n → n ≤ run.liveHorizon → ∀ b ∈ blocksAt run.dag n,
      (run.dag.block b).creator ∈ (Correct : Finset Validator) → b ∈ run.view v :=
  fun n hRn hnN b hb hbc => held_of_pace run.pace run.ids_eq run.block_eq
    run.rounds_advance card_correct run.gst_le hv n hRn
    (by have := run.live_le; omega) b hb hbc

/-! ## The four properties -/

/-- **Every slot below the horizon is decided**: Lemma 23 over a run,
the rotation's three consecutive correct leaders giving a committed
triple the reverse pass reads every slot below off. -/
theorem decided (hv : v ∈ (Correct : Finset Validator)) {r : ℕ}
    (hr : max r run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    run.verdicts hv r ≠ Verdict.undecided :=
  all_decided_of_view (V := run.viewOf hv) (run.wellFormed hv) (run.held hv) run.commits
    run.roundRobin (fun _ _ => run.elig_iff) run.roundId hr

/-- Below a decided horizon a validator's sequence is complete. -/
theorem decidedBelow (hv : v ∈ (Correct : Finset Validator)) {k : ℕ}
    (hk : max k run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    ∀ s, s < k → run.verdicts hv s ≠ Verdict.undecided := by
  intro s hs
  refine run.decided hv ?_
  have : max s run.stable ≤ max k run.stable := max_le_max (by omega) le_rfl
  omega

/-- Every verdict a validator reaches is a derivation of the relation:
its pass is well formed and stops at the horizon. -/
theorem decided_of_verdicts (hv : v ∈ (Correct : Finset Validator)) {r : ℕ}
    (h : run.verdicts hv r ≠ Verdict.undecided) :
    Decided (S := run.sched) run.dag (run.viewOf hv) r (run.verdicts hv r).optOf :=
  decided_of_wellFormed (run.wellFormed hv) (N := run.horizon + 1)
    (fun _ hs => run.undecided_of_gt hv (by omega)) r h

/-- **Two validators never disagree**: the relation's agreement, at
whatever slot both have decided. -/
theorem verdicts_agree (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {s : ℕ}
    (h1 : run.verdicts hv s ≠ Verdict.undecided) (h2 : run.verdicts hw s ≠ Verdict.undecided) :
    run.verdicts hv s = run.verdicts hw s :=
  Verdict.optOf_inj h1 h2 (AnchoredRule.decided_agree (S := run.sched) finWhaleLaws trivial
    (run.decided_of_verdicts hv h1) (run.decided_of_verdicts hw h2))

/-- **Agreement.** Two correct validators deliver the same sequence —
Theorem 24, with the verdicts computed from each validator's own view
rather than assumed. -/
theorem agreement (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {k : ℕ}
    (hk : max k run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    run.delivers hv k = run.delivers hw k :=
  agreement_of_commits (V := run.viewOf hv) (V' := run.viewOf hw) (run.wellFormed hv)
    (run.wellFormed hw)
    (fun s (hs : run.horizon + 1 ≤ s) =>
      ⟨run.undecided_of_gt hv (by omega), run.undecided_of_gt hw (by omega)⟩)
    (sees_of_commits_of_held (V := run.viewOf hv) run.commits (run.held hv))
    (sees_of_commits_of_held (V := run.viewOf hw) run.commits (run.held hw))
    run.roundRobin run.roundId hk (histOf run.dag)

/-- **Total order**: one validator's sequence is a prefix of another's,
at any two horizons — Theorem 14 over Lemma 13. -/
theorem totalOrder (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {k k' : ℕ}
    (hk : max k run.stable + (3 * F.f + 5) ≤ run.liveHorizon)
    (hk' : max k' run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    run.delivers hv k <+: run.delivers hw k' ∨ run.delivers hw k' <+: run.delivers hv k := by
  rcases lemma13 (fun _ h1 h2 => run.verdicts_agree hv hw h1 h2)
    (run.decidedBelow hv hk) (run.decidedBelow hw hk') with h | h
  · exact Or.inl (theorem14 _ h)
  · exact Or.inr (theorem14 _ h)

/-- **Integrity.** No block is delivered twice — Theorem 15 at the
concrete order, asking nothing of the run. -/
theorem integrity (hv : v ∈ (Correct : Finset Validator)) (k : ℕ) :
    (run.delivers hv k).Nodup :=
  nodup_delivery _

/-- **Validity.** A correct validator's block is delivered — Theorem 26:
it lies in its author's next leader block's history, by the
self-parent chain. -/
theorem validity (hv : v ∈ (Correct : Finset Validator)) {b : BlockId} {k : ℕ}
    (hb : b ∈ run.dag.ids)
    (hbc : (run.dag.block b).creator ∈ (Correct : Finset Validator))
    (hbound : max ((run.dag.block b).round) run.stable + Fintype.card Validator + 2 ≤
      run.liveHorizon)
    (hk : max ((run.dag.block b).round) run.stable + Fintype.card Validator < k) :
    b ∈ run.delivers hv k :=
  theorem26_of_selfParent run.selfParented (run.wellFormed hv)
    (sees_of_commits_of_held (V := run.viewOf hv) run.commits (run.held hv))
    run.roundRobin run.roundId hb hbc hbound hk

end Run

end FinWhale

end LeanDag
