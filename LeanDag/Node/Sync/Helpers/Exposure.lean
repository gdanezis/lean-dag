import LeanDag.Node.Sync.Helpers.Net
import LeanDag.Common.Exclusion
/-!
# Sync by causal streams — the exposure bound

`docs/sync.md` §4, S5. A node's targets are admitted blocks of their
announcers, and its detected authors include those its disk catches and
have twins (`Good`, `run_good`). An admitted history is a causal structure
whose blocks are quorate and DoS-valid for `Exposes`, so once every honest
admitted block of round `n + 1` exposes `X`, a block of `X` at round
`n + 1` or above lies in an admitted history only at its top
(`eq_of_mem_admitted`, by D27). A stream is taken in only from the
target's history, so it brings at most the target itself among such
blocks, and only while its author is not detected: each exposed author
holds at most two blocks a round on the disk (`run_count`). An author not
detected holds at most one (`Good.caught`), which gives the bound
(`card_round_le`).
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable {blk : BlockId → Block Validator BlockId Payload}
variable {ev : Payload → Finset (BlockId × BlockId)} [Fintype Validator] {f : ℕ}

omit [Fintype Validator] in
theorem mem_caught_of_twins {S : Finset BlockId} {i j : BlockId} (hi : i ∈ S) (hj : j ∈ S)
    (h : Twins blk i j) : (blk i).creator ∈ caught blk ev S :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, j, hj, h⟩, rfl⟩)

omit [Fintype Validator] in
theorem exists_twins_of_mem_caught {S : Finset BlockId} {X : Validator}
    (h : X ∈ caught blk ev S) : ∃ i j, Twins blk i j ∧ (blk i).creator = X := by
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨-, j, -, hij⟩ := Finset.mem_filter.mp hi
    exact ⟨i, j, hij, rfl⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, rfl⟩

omit [Fintype Validator] in
theorem exists_twins_of_mem_exposes {S : Finset BlockId} {L : List BlockId} {X : Validator}
    (h : X ∈ exposes blk S L) : ∃ i j, Twins blk i j ∧ (blk i).creator = X := by
  unfold exposes at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  have hi' := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hi'
  obtain ⟨-, j, -, hij⟩ := hi'
  exact ⟨i, j, hij, rfl⟩

/-- **A good state**: clean, with admitted targets by their announcers, and
detected authors that include those the disk catches and have twins. -/
structure Good (me : Validator) (s : State Validator BlockId) : Prop where
  clean : Clean me s
  admitted : ∀ a t, s.target a = some t → Admits blk ev f t ∧ (blk t).creator = a
  caught : caught blk ev s.disk ⊆ s.detected
  twins : ∀ X ∈ s.detected, ∃ i j, Twins blk i j ∧ (blk i).creator = X

theorem init_good (me : Validator) : Good (blk := blk) (ev := ev) (f := f) me State.init where
  clean := init_clean me
  admitted := fun _ _ h => by simp [State.init] at h
  caught := by simp [caught, State.init]
  twins := fun _ h => by simp [State.init] at h

theorem good_settle {me : Validator} {s : State Validator BlockId}
    (hs : Good (blk := blk) (ev := ev) (f := f) me s) {S : Finset BlockId} {D : Finset Validator}
    (hD : caught blk ev S ⊆ D) (hDt : ∀ X ∈ D, ∃ i j, Twins blk i j ∧ (blk i).creator = X) :
    Good (blk := blk) (ev := ev) (f := f) me (settle s S D) where
  clean := settle_clean hs.clean S D
  admitted := by
    intro a t ht
    by_cases hD' : a ∈ D
    · simp [settle, hD'] at ht
    · simp only [settle, hD', if_false, Option.filter_eq_some_iff] at ht
      exact hs.admitted a t ht.1
  caught := hD
  twins := hDt

theorem step_good {me : Validator} {s : State Validator BlockId}
    (hs : Good (blk := blk) (ev := ev) (f := f) me s) (inp : Input Validator BlockId) :
    Good (blk := blk) (ev := ev) (f := f) me (step blk ev f me s inp) := by
  cases inp with
  | announce u t =>
    have hcl := step_clean (blk := blk) (ev := ev) (f := f) hs.clean (.announce u t)
    simp only [step] at hcl ⊢
    split_ifs at hcl ⊢ with h
    · refine ⟨hcl, ?_, hs.caught, hs.twins⟩
      intro a c hc
      by_cases hau : a = u
      · subst hau
        simp only [Function.update_self, Option.some.injEq] at hc
        subst hc
        exact ⟨h.2.2.2.2.2, h.2.2.1⟩
      · simp only [Function.update_of_ne hau] at hc
        exact hs.admitted a c hc
    · exact hs
  | chunk u L =>
    refine good_settle hs Finset.subset_union_right fun X hX => ?_
    rcases Finset.mem_union.mp hX with hX | hX
    · rcases Finset.mem_union.mp hX with hX | hX
      · exact hs.twins X hX
      · exact exists_twins_of_mem_exposes hX
    · exact exists_twins_of_mem_caught hX
  | build x =>
    simp only [step]
    split_ifs
    · refine good_settle hs Finset.subset_union_right fun X hX => ?_
      rcases Finset.mem_union.mp hX with hX | hX
      · exact hs.twins X hX
      · exact exists_twins_of_mem_caught hX
    · exact hs
  | report i j =>
    simp only [step]
    split_ifs with h
    · refine good_settle hs (hs.caught.trans (Finset.subset_insert _ _)) fun X hX => ?_
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact ⟨i, j, h, rfl⟩
      · exact hs.twins X hX
    · exact hs

theorem run_good {me : Validator} :
    ∀ (s : State Validator BlockId) (ins : List (Input Validator BlockId)),
      Good (blk := blk) (ev := ev) (f := f) me s →
        Good (blk := blk) (ev := ev) (f := f) me (run blk ev f me s ins)
  | _, [], hs => hs
  | s, inp :: ins, hs => run_good (step blk ev f me s inp) ins (step_good hs inp)

/-- **Above the exposure, an admitted history holds an exposed author's
block only at its top.** -/
theorem eq_of_mem_admitted {H : Finset Validator} (hHc : Hᶜ.card ≤ f)
    (hmin : 2 * f < Fintype.card Validator) {X : Validator} {n : ℕ}
    (hexp : ∀ c, Admits blk ev f c → (blk c).round = n + 1 → (blk c).creator ∈ H →
      Exposes blk ev c X)
    {t i : BlockId} (ht : Admits blk ev f t) (hi : i ∈ historyFrom blk t)
    (hir : n + 1 ≤ (blk i).round) (hic : (blk i).creator = X) : i = t := by
  let rel : Reliability Validator := ⟨H, f, hHc, hmin⟩
  have C : CausalStructure blk (historyFrom blk t) :=
    causalStructure_historyFrom fun x hx => (ht x hx).1
  have hq : QuorateOn blk (historyFrom blk t) rel := fun b hb hr => (ht b hb).2.1 hr
  have hdos : DoSValidOn blk (historyFrom blk t) (Exposes blk ev) :=
    fun b hb j hj => (ht b hb).2.2 j hj
  have hup : InheritedOn blk (historyFrom blk t) (Exposes blk ev) := by
    intro b hb j hj Y hY
    obtain ⟨x, hx, hxY⟩ := hY
    exact ⟨x, C.history_subset_of_reaches hb (ReachesFrom.single hj) hx, hxY⟩
  have hexp' : ∀ c ∈ historyFrom blk t, (blk c).round = n + 1 →
      (blk c).creator ∈ rel.correct → Exposes blk ev c X :=
    fun c hc hcr hcH => hexp c (fun x hx => ht x (C.history_subset_ids hc hx)) hcr hcH
  by_contra hne
  exact creator_ne_of_correct_exposed C hq hdos hup hexp' mem_historyFrom_self hi hne hir hic

omit [Fintype Validator] in
/-- An author not detected holds at most one block a round on the disk of a
good state. -/
theorem card_le_one_of_not_detected {s : State Validator BlockId}
    (hcaught : caught blk ev s.disk ⊆ s.detected) {X : Validator} (hX : X ∉ s.detected) (k : ℕ) :
    (s.disk.filter fun i => (blk i).creator = X ∧ (blk i).round = k).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  by_contra hab
  obtain ⟨ha, hac, har⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbc, hbr⟩ := Finset.mem_filter.mp hb
  exact hX (hac ▸ hcaught (mem_caught_of_twins ha hb ⟨hab, hac.trans hbc.symm, har.trans hbr.symm⟩))

/-- **Each exposed author holds at most two blocks a round on the disk**,
from the round at which its exposure is complete. -/
theorem step_count {H : Finset Validator} (hHc : Hᶜ.card ≤ f)
    (hmin : 2 * f < Fintype.card Validator) {E : Finset Validator} {n : ℕ}
    (hexp : ∀ X ∈ E, ∀ c, Admits blk ev f c → (blk c).round = n + 1 → (blk c).creator ∈ H →
      Exposes blk ev c X)
    {me : Validator} (hme : me ∉ E) {s : State Validator BlockId}
    (hs : Good (blk := blk) (ev := ev) (f := f) me s)
    (hc : ∀ X ∈ E, ∀ k, n + 1 ≤ k →
      (s.disk.filter fun i => (blk i).creator = X ∧ (blk i).round = k).card ≤ 2)
    (inp : Input Validator BlockId) :
    ∀ X ∈ E, ∀ k, n + 1 ≤ k →
      ((step blk ev f me s inp).disk.filter fun i =>
        (blk i).creator = X ∧ (blk i).round = k).card ≤ 2 := by
  intro X hX k hk
  cases inp with
  | announce u t =>
    simp only [step]
    split_ifs
    · exact hc X hX k hk
    · exact hc X hX k hk
  | report i j =>
    simp only [step]
    split_ifs
    · exact hc X hX k hk
    · exact hc X hX k hk
  | build x =>
    simp only [step]
    split_ifs with h
    · simp only [settle]
      rw [Finset.filter_insert, if_neg (fun hx => hme (by rw [← h.1, hx.1]; exact hX))]
      exact hc X hX k hk
    · exact hc X hX k hk
  | chunk u L =>
    simp only [step, settle]
    set old := s.disk.filter fun i => (blk i).creator = X ∧ (blk i).round = k
    cases htu : s.target u with
    | none =>
      have hL : (L.filter fun i =>
          (none : Option BlockId).any fun t => decide (i ∈ historyFrom blk t)) = [] := by
        simp
      simp only [hL, absorb]
      exact hc X hX k hk
    | some t =>
      obtain ⟨ht, htc⟩ := hs.admitted u t htu
      have hsub : ((absorb blk s.disk (L.filter fun i =>
          (some t).any fun t => decide (i ∈ historyFrom blk t))).filter fun i =>
            (blk i).creator = X ∧ (blk i).round = k) ⊆ insert t old := by
        intro i hi
        obtain ⟨hi, hic, hir⟩ := Finset.mem_filter.mp hi
        rcases Finset.mem_union.mp (absorb_sub _ _ hi) with hd | hl
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hd, hic, hir⟩)
        · have hmem := (List.mem_filter.mp (List.mem_toFinset.mp hl)).2
          simp only [Option.any_some, decide_eq_true_eq] at hmem
          rw [eq_of_mem_admitted hHc hmin (hexp X hX) ht hmem (by omega) hic]
          exact Finset.mem_insert_self t old
      by_cases htX : (blk t).creator = X
      · have hu : u ∉ s.detected := (hs.clean u (by simp [htu])).2
        have hold : old.card ≤ 1 :=
          card_le_one_of_not_detected hs.caught (by rw [← htX, htc]; exact hu) k
        exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))
      · refine (Finset.card_le_card fun i hi => ?_).trans (hc X hX k hk)
        rcases Finset.mem_insert.mp (hsub hi) with rfl | h
        · exact absurd (Finset.mem_filter.mp hi).2.1 htX
        · exact h

theorem run_count {H : Finset Validator} (hHc : Hᶜ.card ≤ f)
    (hmin : 2 * f < Fintype.card Validator) {E : Finset Validator} {n : ℕ}
    (hexp : ∀ X ∈ E, ∀ c, Admits blk ev f c → (blk c).round = n + 1 → (blk c).creator ∈ H →
      Exposes blk ev c X)
    {me : Validator} (hme : me ∉ E) :
    ∀ (s : State Validator BlockId) (ins : List (Input Validator BlockId)),
      Good (blk := blk) (ev := ev) (f := f) me s →
      (∀ X ∈ E, ∀ k, n + 1 ≤ k →
        (s.disk.filter fun i => (blk i).creator = X ∧ (blk i).round = k).card ≤ 2) →
      ∀ X ∈ E, ∀ k, n + 1 ≤ k →
        ((run blk ev f me s ins).disk.filter fun i =>
          (blk i).creator = X ∧ (blk i).round = k).card ≤ 2
  | _, [], _, hc => hc
  | s, inp :: ins, hs, hc =>
    run_count hHc hmin hexp hme (step blk ev f me s inp) ins (step_good hs inp)
      (step_count hHc hmin hexp hme hs hc inp)

/-- **The exposure bound.** -/
theorem card_round_le {H : Finset Validator} (hHc : Hᶜ.card ≤ f)
    (hmin : 2 * f < Fintype.card Validator) {me : Validator} (hme : me ∈ H)
    (hhon : ∀ i j, Twins blk i j → (blk i).creator ∉ H) {ins : List (Input Validator BlockId)}
    {n k : ℕ}
    (hexp : ∀ c, Admits blk ev f c → (blk c).round = n + 1 → (blk c).creator ∈ H →
      ∀ X ∈ (run blk ev f me State.init ins).detected, Exposes blk ev c X)
    (hk : n + 1 ≤ k) :
    ((run blk ev f me State.init ins).disk.filter fun i => (blk i).round = k).card ≤
      Fintype.card Validator + (run blk ev f me State.init ins).detected.card := by
  set s := run blk ev f me State.init ins with hsdef
  set E := s.detected
  have hs : Good (blk := blk) (ev := ev) (f := f) me s := run_good _ ins (init_good me)
  have hmeE : me ∉ E := by
    intro h
    obtain ⟨i, j, hij, hic⟩ := hs.twins me h
    exact hhon i j hij (hic ▸ hme)
  have hcount := run_count hHc hmin (E := E) (fun X hX c hc hcr hcH => hexp c hc hcr hcH X hX)
    hmeE State.init ins (init_good me) (fun _ _ _ _ => by simp [State.init])
  have hsplit : (s.disk.filter fun i => (blk i).round = k) ⊆
      ((s.disk.filter fun i => (blk i).round = k).filter fun i => (blk i).creator ∉ E) ∪
        E.biUnion fun X => s.disk.filter fun i => (blk i).creator = X ∧ (blk i).round = k := by
    intro i hi
    by_cases hiE : (blk i).creator ∈ E
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, hiE,
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, rfl, (Finset.mem_filter.mp hi).2⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hiE⟩)
  have hfree : ((s.disk.filter fun i => (blk i).round = k).filter
      fun i => (blk i).creator ∉ E).card ≤ Fintype.card Validator - E.card := by
    rw [← Finset.card_compl]
    refine Finset.card_le_card_of_injOn (fun i => (blk i).creator) ?_ ?_
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      exact Finset.mem_coe.mpr (Finset.mem_compl.mpr hi.2)
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter] at ha hb
      by_contra hne
      exact ha.2 (hs.caught (mem_caught_of_twins ha.1.1 hb.1.1
        ⟨hne, hab, ha.1.2.trans hb.1.2.symm⟩))
  have hexposed : (E.biUnion fun X =>
      s.disk.filter fun i => (blk i).creator = X ∧ (blk i).round = k).card ≤ 2 * E.card :=
    Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun X hX => hcount X hX k hk).trans
      (by rw [Finset.sum_const, smul_eq_mul, mul_comm]))
  have hE : E.card ≤ Fintype.card Validator := Finset.card_le_univ E
  exact (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans (by omega))

end Sync

end Node

end LeanDag
