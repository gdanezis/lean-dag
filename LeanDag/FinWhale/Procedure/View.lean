import LeanDag.FinWhale.Procedure.Decided
import LeanDag.FinWhale.Model.View
import LeanDag.FinWhale.Procedure.Consistency
import LeanDag.FinWhale.View
/-!
# FinWhale — verdict assignments over a view

Procedure side: these mention a verdict assignment or the reverse pass.
-/

namespace LeanDag
namespace FinWhale
variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {Elig : ℕ → ℕ → Prop}
variable {D : Dag Validator BlockId Payload} {V : D.View}
variable {S : Slots Validator}
variable [LinearOrder BlockId]

/-- **Lemma 23, on a view**: holding the blocks up to the horizon decides
every slot below it, `hsees` discharged by `directCommit_of_holds`. -/
theorem all_decided_of_view {V : D.View}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed Elig (viewCommit S D V ) (viewSkip S D V ) choose dec) {R N r : ℕ}
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V.ids)
    (hcommits : CommitsCorrectLeaders S D R N)
    (hrr : RoundRobin S.leader) (hEl : ∀ r a, Elig r a ↔ r + 2 < a) (hid : ∀ s, S.slotRound s = s)
    (hN : max r R + (3 * F.f + 5) ≤ N) :
    dec r ≠ Verdict.undecided :=
  all_decided hwf (sees_of_commits_of_held  hcommits hheld) hrr hEl hid hN

open scoped Classical in
/-- **And so does the tie-break.** -/
theorem chooseLeast_congr [LinearOrder BlockId] {S S' : Slots Validator}
    {D : Dag Validator BlockId Payload} {A : BlockId} {r : ℕ}
    (hr : S.slotRound r = S'.slotRound r) (hl : S.leader r = S'.leader r) :
    chooseLeast S D A r = chooseLeast S' D A r := by
  have hset : (slotBlocks S D r).filter (fun b => IndirectCommit S D A r b) =
      (slotBlocks S' D r).filter (fun b => IndirectCommit S' D A r b) := by
    rw [slotBlocks_congr hr hl]
    exact Finset.filter_congr fun b _ => by
      simp [indirectCommit_congr (D := D) (A := A) (b := b) hr hl]
  unfold chooseLeast
  simp only [hset]

/-- **The reverse pass lands in the relation.** Every slot a well-formed
assignment decides, it decides as the relation does: direct verdicts by
the direct constructor, indirect ones by the induction hypothesis at
the nearest eligible committed anchor. -/
theorem decided_of_wellFormed {V : D.View} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed (EligibleAt (S := S) 2) (viewCommit S D V) (viewSkip S D V)
      (chooseLeast S D) dec)
    {N : ℕ} (hN : ∀ s, N ≤ s → dec s = Verdict.undecided) :
    ∀ r, dec r ≠ Verdict.undecided → Decided D V r (dec r).optOf := by
  suffices h : ∀ d r, N ≤ r + d → dec r ≠ Verdict.undecided → Decided D V r (dec r).optOf by
    intro r; exact h N r (by omega)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro r hNr hr
    have hd0 : d ≠ 0 := by rintro rfl; exact hr (hN r (by omega))
    have IH : ∀ s, r < s → dec s ≠ Verdict.undecided → Decided D V s (dec s).optOf :=
      fun s hs hd => ih (d - 1) (by omega) s (by omega) hd
    by_cases hdc : ∃ l, viewCommit S D V r l
    · obtain ⟨l, hslot, hcom⟩ := hdc
      rw [hwf.direct_commit r l ⟨hslot, hcom⟩]
      exact Decided.directCommit (mem_slotBlocks.1 (slotBlocks_restrict hslot)) hcom
    · by_cases hds : viewSkip S D V r
      · rw [hwf.direct_skip r hds]
        exact Decided.directSkip hds
      · obtain ⟨a, hanc⟩ := hwf.has_anchor r hdc hds hr
        rcases hva : dec a with A | - | -
        · have hra : r < a := lt_of_eligibleAt hanc.1
          have hA : Decided D V a (some A) := by
            have := IH a hra (by rw [hva]; simp)
            rwa [hva] at this
          have hmid : ∀ m, r < m → m < a → EligibleAt (S := S) 2 r m → Decided D V m none := by
            intro m h1 h2 h3
            have hsk := hanc.2.2 m h3 h2
            have := IH m h1 (by rw [hsk]; simp)
            rwa [hsk] at this
          have hval := hwf.indirect_commit r a A hdc hds hanc hva
          rcases hch : chooseLeast S D A r with - | b
          · rw [hch] at hval
            rw [hval]
            refine Decided.indirectSkip hra hanc.1 hA hmid (fun i hi L hL hlink => ?_)
            have : i = 0 := by change i < 1 at hi; omega
            subst this
            exact absurd (chooseSound_least.total A r ⟨L, hlink⟩) (by rw [hch]; simp)
          · rw [hch] at hval
            rw [hval]
            have hind := chooseSound_least.sound A r b hch
            exact Decided.indirectCommit (i := 0) hra hanc.1 hA hmid Nat.one_pos
              (fun _ h => absurd h (Nat.not_lt_zero _)) (mem_slotBlocks.1 hind.1) hind
              (chooseLeast_least hch)
        · exact absurd hva hanc.2.1
        · exact absurd (hwf.indirect_undecided r a hdc hds hanc hva) hr

/-! ## The two theorems, end to end -/

/-- **Theorem 24 (Agreement), end to end.** Two validators running the
reverse pass on their own views deliver the same sequence at every
horizon: the relation's agreement settles verdicts both have decided,
and Lemma 23 (via `hsees`) makes them decided. -/
theorem agreement_of_commits [LinearOrder BlockId] {V V' : D.View}
    {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed (EligibleAt (S := S) 2) (viewCommit S D V) (viewSkip S D V)
      (chooseLeast S D) dec)
    (hwf' : WellFormed (EligibleAt (S := S) 2) (viewCommit S D V') (viewSkip S D V')
      (chooseLeast S D) dec')
    {M : ℕ} (hbound : ∀ s, M ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {R N : ℕ} (hsees : SeesCommits S D (viewCommit S D V) R N)
    (hsees' : SeesCommits S D (viewCommit S D V') R N)
    (hrr : RoundRobin S.leader) (hid : ∀ s, S.slotRound s = s)
    {k : ℕ} (hkN : max k R + (3 * F.f + 5) ≤ N)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  have hEl : ∀ r a, EligibleAt (S := S) 2 r a ↔ r + 2 < a := fun r a => by
    simp only [EligibleAt, hid]
  have hagree : ∀ s, dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided →
      dec s = dec' s := by
    intro s h1 h2
    exact Verdict.optOf_inj h1 h2 (AnchoredRule.decided_agree finWhaleLaws trivial
      (decided_of_wellFormed hwf (fun s hs => (hbound s hs).1) s h1)
      (decided_of_wellFormed hwf' (fun s hs => (hbound s hs).2) s h2))
  refine theorem24 hagree
    (fun s hs => all_decided hwf hsees hrr hEl hid (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    (fun s hs => all_decided hwf' hsees' hrr hEl hid (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    hist

end FinWhale

end LeanDag
