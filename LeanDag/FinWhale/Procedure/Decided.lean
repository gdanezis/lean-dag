import LeanDag.FinWhale.Procedure.Order
import LeanDag.FinWhale.Model.Liveness
import Mathlib.Data.Finset.Sort
import LeanDag.FinWhale.Rotation
/-!
# FinWhale — every slot is decided, and what follows

Lemma 23 and Theorems 24 and 26: the relation's agreement says two
validators never disagree, these say they eventually agree about
everything. `lemma23` is a statement about one DAG, not about time — it
takes a committed triple above a slot and concludes the slot is
decided; growth enters through the hypothesis, since a larger DAG
carries a triple further up. The end-to-end form,
`agreement_of_commits`, is in `View.lean`, where the views are.
-/

namespace LeanDag

namespace FinWhale

variable {BlockId : Type} [DecidableEq BlockId]
variable {Elig : ℕ → ℕ → Prop}

omit [DecidableEq BlockId] in
/-- **Lemma 23.** Every slot below a committed triple is decided: taking
the highest undecided slot below it, the first non-skipped slot above
it is a commit and serves as its anchor. -/
theorem lemma23 {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hEl : ∀ r a, Elig r a ↔ r + 2 < a)
    (hwf : WellFormed Elig dc ds choose dec) {r a : ℕ} (hra : r < a)
    (htri : ∀ s, a ≤ s → s ≤ a + 2 → dec s ≠ Verdict.undecided ∧ dec s ≠ Verdict.skip) :
    dec r ≠ Verdict.undecided := by
  classical
  intro hru
  -- the highest undecided slot at or below the triple's top
  have hrle : r ≤ a + 2 := by omega
  have hm : dec (Nat.findGreatest (fun s => dec s = Verdict.undecided) (a + 2)) =
      Verdict.undecided :=
    Nat.findGreatest_spec (P := fun s => dec s = Verdict.undecided) hrle hru
  set m := Nat.findGreatest (fun s => dec s = Verdict.undecided) (a + 2) with hmdef
  have hmle : m ≤ a + 2 := Nat.findGreatest_le _
  have hgreat : ∀ n, m < n → n ≤ a + 2 → dec n ≠ Verdict.undecided :=
    fun n h1 h2 => Nat.findGreatest_is_greatest h1 h2
  have hma : m < a := by
    rcases Nat.lt_or_ge m a with h | h
    · exact h
    · exact absurd hm (htri m h hmle).1
  -- one of the triple lies above `m + 2` and is not skipped
  obtain ⟨w, hwle, hwskip⟩ : ∃ w, m + 3 + w ≤ a + 2 ∧ dec (m + 3 + w) ≠ Verdict.skip := by
    rcases Nat.lt_or_ge (m + 2) a with h | h
    · exact ⟨a - (m + 3), by omega,
        by rw [show m + 3 + (a - (m + 3)) = a by omega]; exact (htri a le_rfl (by omega)).2⟩
    · exact ⟨a + 2 - (m + 3), by omega,
        by rw [show m + 3 + (a + 2 - (m + 3)) = a + 2 by omega]
           exact (htri (a + 2) (by omega) le_rfl).2⟩
  have hex : ∃ k, dec (m + 3 + k) ≠ Verdict.skip := ⟨w, hwskip⟩
  -- the first such slot is the anchor of `m`
  have hfind : Nat.find hex ≤ w := Nat.find_le hwskip
  have hanchor : Anchor Elig dec m (m + 3 + Nat.find hex) := by
    refine ⟨(hEl _ _).mpr (by omega), Nat.find_spec hex, ?_⟩
    intro t ht1' ht2
    have ht1 := (hEl _ _).mp ht1'
    have hlt : t - (m + 3) < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    rw [show m + 3 + (t - (m + 3)) = t by omega] at hmin
    exact not_not.1 hmin
  have hdec : dec (m + 3 + Nat.find hex) ≠ Verdict.undecided :=
    hgreat _ (by omega) (by omega)
  -- so the anchor is committed, and the reverse pass decides `m`
  by_cases hdcm : ∃ l, dc m l
  · obtain ⟨l, hl⟩ := hdcm
    exact absurd (hwf.direct_commit m l hl) (by rw [hm]; simp)
  · by_cases hdsm : ds m
    · exact absurd (hwf.direct_skip m hdsm) (by rw [hm]; simp)
    · rcases hva : dec (m + 3 + Nat.find hex) with A | - | -
      · have := hwf.indirect_commit m _ A hdcm hdsm hanchor hva
        rw [hm] at this
        rcases hch : choose A m with - | b
        · rw [hch] at this; simp at this
        · rw [hch] at this; simp at this
      · exact absurd hva hanchor.2.1
      · exact absurd hva hdec

/-! ## Committed anchors, from §10's liveness

`lemma23` asks for a committed triple, which the rotation supplies
(Lemma 22, three consecutive correct leaders) and coverage commits
(Lemma 20). `hsees` carries the growth: a validator's view holds what
the universe holds. -/

section Triple

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type} {D : Dag Validator BlockId Payload} {S : Slots Validator}

/-- **A committed triple above every round.** -/
theorem committed_triple {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed Elig dc ds choose dec) {R N t : ℕ}
    (hsees : SeesCommits S D dc R N)
    (hrr : RoundRobin S.leader) (hid : ∀ s, S.slotRound s = s)
    (hR : R ≤ t) (hN : t + (3 * F.f + 5) ≤ N) :
    ∃ a, t < a ∧ a + 4 ≤ N ∧
      ∀ s, a ≤ s → s ≤ a + 2 →
        dec s ≠ Verdict.undecided ∧ dec s ≠ Verdict.skip := by
  obtain ⟨a, hlo, hhi, h0, h1, h2⟩ := lemma22 hrr (t + 1)
  refine ⟨a, by omega, by omega, fun s hs1 hs2 => ?_⟩
  have hsc : S.leader s ∈ (Correct : Finset Validator) := by
    rcases (by omega : s = a ∨ s = a + 1 ∨ s = a + 2) with rfl | rfl | rfl
    exacts [h0, h1, h2]
  obtain ⟨l, -, hdcl⟩ := hsees s (by rw [hid]; omega) (by rw [hid]; omega) hsc
  rw [hwf.direct_commit s l hdcl]
  exact ⟨by simp, by simp⟩

/-- **Lemma 23, composed.** Every slot below the horizon is decided,
including those before GST, decided from an anchor above them; only the
triple must sit past the coverage round, hence the maximum. -/
theorem all_decided {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed Elig dc ds choose dec) {R N r : ℕ}
    (hsees : SeesCommits S D dc R N)
    (hrr : RoundRobin S.leader) (hEl : ∀ r a, Elig r a ↔ r + 2 < a) (hid : ∀ s, S.slotRound s = s)
    (hN : max r R + (3 * F.f + 5) ≤ N) :
    dec r ≠ Verdict.undecided := by
  obtain ⟨a, hlo, -, htri⟩ :=
    committed_triple hwf hsees hrr hid (le_max_right r R) hN
  exact lemma23 hEl hwf (lt_of_le_of_lt (le_max_left r R) hlo) htri

end Triple

/-! ## From decided slots to delivered blocks -/

omit [DecidableEq BlockId] in
/-- A committed slot's block is in the commit sequence, once the sequence
reaches that slot. -/
theorem mem_commitSeq {dec : ℕ → Verdict BlockId} {r : ℕ} {l : BlockId} :
    ∀ k, r < k → dec r = Verdict.commit l → l ∈ commitSeq dec k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hr hcom
    rcases Nat.lt_or_ge r k with h | h
    · exact List.mem_append_left _ (ih h hcom)
    · have hrk : r = k := by omega
      subst hrk
      simp [commitSeq, hcom]

/-- The accumulator survives the fold. -/
theorem subset_foldl (hist : BlockId → List BlockId) (ls acc : List BlockId) :
    ∀ b ∈ acc, b ∈ ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc := by
  obtain ⟨t, ht⟩ := linearise_foldl_append hist ls acc
  intro b hb
  rw [ht]
  exact List.mem_append_left _ hb

/-- **Everything in a committed leader's history is delivered**, by an
earlier leader or this one. -/
theorem mem_linearise (hist : BlockId → List BlockId) :
    ∀ (ls : List BlockId) (acc : List BlockId) (l : BlockId), l ∈ ls → ∀ b ∈ hist l,
      b ∈ ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc := by
  intro ls
  induction ls with
  | nil => intro acc l hl; simp at hl
  | cons x xs ih =>
    intro acc l hl b hb
    rcases List.mem_cons.1 hl with rfl | hl'
    · by_cases hba : b ∈ acc
      · exact subset_foldl hist xs _ b (List.mem_append_left _ hba)
      · refine subset_foldl hist xs _ b (List.mem_append_right _ ?_)
        refine List.mem_filter.2 ⟨hb, ?_⟩
        simpa using hba
    · exact ih _ l hl' b hb

omit [DecidableEq BlockId] in
/-- **Lemma 25.** A committed leader block is in the commit sequence. -/
theorem lemma25 {dec : ℕ → Verdict BlockId} {r k : ℕ} {l : BlockId}
    (hr : r < k) (hcom : dec r = Verdict.commit l) : l ∈ commitSeq dec k :=
  mem_commitSeq k hr hcom

/-- **Theorem 24 (Agreement)**: two validators that have decided every
slot below `k` deliver the same sequence, from Lemma 12's agreement
through `commitSeq_congr`. -/
theorem theorem24 {dec dec' : ℕ → Verdict BlockId} {k : ℕ}
    (hagree : ∀ s, dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided → dec s = dec' s)
    (hdec : ∀ s, s < k → dec s ≠ Verdict.undecided)
    (hdec' : ∀ s, s < k → dec' s ≠ Verdict.undecided)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  rw [commitSeq_congr k fun s hs => hagree s (hdec s hs) (hdec' s hs)]

/-- **Theorem 26 (Validity), at the list layer**: a block in the causal
history of a committed leader is delivered. -/
theorem theorem26 {dec : ℕ → Verdict BlockId} {hist : BlockId → List BlockId} {r k : ℕ}
    {l b : BlockId} (hr : r < k) (hcom : dec r = Verdict.commit l) (hb : b ∈ hist l) :
    b ∈ linearise hist (commitSeq dec k) :=
  mem_linearise hist _ [] l (lemma25 hr hcom) b hb

/-! ## The delivery order, concretely -/

section Order

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type} {D : Dag Validator BlockId Payload} {S : Slots Validator}

/-- `histOf` is the causal history, discharging the faithfulness
condition Theorem 26 asks for. -/
theorem mem_histOf [LinearOrder BlockId] {l c : BlockId} (hl : l ∈ D.ids)
    (h : ReachesFrom D.block l c) : c ∈ histOf D l :=
  (Finset.mem_sort _).2 (((causalStructure D).mem_history_iff hl).2 h)

/-- And it lists each block once, which is the condition Theorem 15 asks
for. -/
theorem nodup_histOf [LinearOrder BlockId] {l : BlockId} : (histOf D l).Nodup :=
  Finset.sort_nodup _ _

/-- **Theorem 15 at the concrete order.** No block is delivered twice. -/
theorem nodup_delivery [LinearOrder BlockId] (ls : List BlockId) :
    (linearise (histOf D) ls).Nodup :=
  theorem15 _ (fun _ => nodup_histOf) ls

end Order

end FinWhale

end LeanDag
