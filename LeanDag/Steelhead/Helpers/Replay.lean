import LeanDag.Steelhead.Replay.Statement
import LeanDag.Steelhead.Helpers.Coin
/-!
# Helpers — the replay

Generated lemma infrastructure for `Replay/Statement.lean`; not part of
the audit surface. The selection is a fold that keeps a candidate and
never raises the score; the window's evidence is Mahi-Mahi's predicates
intersected with the window; and the window's committed candidates are
the counting lemma's, read on the anchor's causal history as a record,
whose votes and certificates are the universe's restricted to it.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

/-! ## The selection -/

/-- A step of the selection fold keeps the incumbent among the allowed candidates. -/
theorem fold_mem (allowed xs : List ℕ) (scores : ℕ → ℚ) (current incumbent : ℕ)
    (hinc : incumbent ∈ allowed) (hxs : ∀ x ∈ xs, x ∈ allowed) :
    xs.foldl (fun inc x => if prefer scores current x inc then x else inc) incumbent ∈ allowed := by
  induction xs generalizing incumbent with
  | nil => exact hinc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · split
      · exact hxs x (by simp)
      · exact hinc
    · intro y hy
      exact hxs y (by simp [hy])

/-- The best candidate is a candidate, the current period being one. -/
theorem best_mem (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ)
    (hc : current ∈ candidates) : best candidates scores current ∈ candidates :=
  fold_mem candidates candidates scores current current hc fun _ h => h

/-- A preferred candidate scores no worse than the incumbent. -/
theorem score_le_of_prefer {scores : ℕ → ℚ} {current x incumbent : ℕ}
    (h : prefer scores current x incumbent = true) : scores x ≤ scores incumbent := by
  simp only [prefer, decide_eq_true_eq] at h
  rcases h with h | ⟨h, _, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- The selection fold never raises the incumbent's score. -/
theorem fold_score_le (xs : List ℕ) (scores : ℕ → ℚ) (current incumbent : ℕ) :
    scores (xs.foldl (fun inc x => if prefer scores current x inc then x else inc) incumbent) ≤
      scores incumbent := by
  induction xs generalizing incumbent with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · exact le_trans (ih x) (score_le_of_prefer ‹_›)
    · exact ih incumbent

/-- **SH18a.** The winner is a candidate, and so is the current period. -/
theorem select_mem (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ)
    (hc : current ∈ candidates) : select candidates scores current epsilon ∈ candidates := by
  dsimp only [select]
  split
  · exact best_mem candidates scores current hc
  · exact hc

/-- **SH18b.** The winner scores no worse than the current period, which the fold started from. -/
theorem select_score_le (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ) :
    scores (select candidates scores current epsilon) ≤ scores current := by
  dsimp only [select]
  split
  · exact fold_score_le candidates scores current current
  · exact le_rfl

/-! ## The evidence -/

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [LinearOrder BlockId]

/-- A quorum of certificates within the window is at least one. -/
theorem certified_of_commits (U : BlockUniverse Validator BlockId Payload) (A : BlockId)
    (I r w : ℕ) (a : Validator) (h : (ofAnchor U A I).commits r w a = true) :
    (ofAnchor U A I).certified r w a = true := by
  simp only [ofAnchor, decide_eq_true_eq] at h ⊢
  obtain ⟨L, hL, hc⟩ := h
  refine ⟨L, hL, ?_⟩
  intro he
  rw [he] at hc
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at hc
  have := F.card_validators
  omega

/-- A quorum of blames within the window is one in the universe, and MM1a then leaves no
certificate at all. -/
theorem not_certified_of_skips (U : BlockUniverse Validator BlockId Payload) (A : BlockId)
    (I r w : ℕ) (a : Validator) (hw : 2 ≤ w) (h : (ofAnchor U A I).skips r w a = true) :
    (ofAnchor U A I).certified r w a = false := by
  simp only [ofAnchor, decide_eq_true_eq] at h
  simp only [ofAnchor, decide_eq_false_iff_not, not_exists, not_and, not_not]
  intro L hL
  have hglobal : MahiMahi.DirectSkip U w a r :=
    le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))
  obtain ⟨hLr, hLa, _⟩ := Finset.mem_filter.mp hL
  have he := MahiMahi.certificates_eq_empty_of_directSkip hw hglobal hLa (mem_blocksAt.mp hLr).2
  rw [he]
  simp

/-! ## The window as a record -/

variable {U : BlockUniverse Validator BlockId Payload}

/-- The candidates a block of a view sees are the universe's: the histories coincide, and a
view is closed under references. -/
theorem candidatesAt_toRecord {V : View Validator BlockId Payload U} {q : BlockId}
    (hq : q ∈ V.ids) (a : Validator) (r : ℕ) :
    MahiMahi.candidatesAt V.toRecord q a r = MahiMahi.candidatesAt U q a r := by
  ext L
  simp only [MahiMahi.candidatesAt, Finset.mem_filter, mem_blocksAt, BlockRecord.View.toRecord_ids,
    BlockRecord.View.toRecord_block]
  constructor
  · rintro ⟨⟨hL, hLr⟩, hLa, hLh⟩
    exact ⟨⟨V.subset_ids hL, hLr⟩, hLa, hLh⟩
  · rintro ⟨⟨hL, hLr⟩, hLa, hLh⟩
    refine ⟨⟨?_, hLr⟩, hLa, hLh⟩
    exact mem_of_reaches_of_closed V.complete hq ((mem_history_iff (V.subset_ids hq)).mp hLh)

/-- A vote read in a view is a vote in the universe. -/
theorem votes_toRecord {V : View Validator BlockId Payload U} {q L : BlockId} (hq : q ∈ V.ids) :
    MahiMahi.Votes V.toRecord q L ↔ MahiMahi.Votes U q L := by
  unfold MahiMahi.Votes
  simp only [BlockRecord.View.toRecord_block, candidatesAt_toRecord hq]

/-- The certificates a view holds are the universe's within it. -/
theorem certificates_toRecord {V : View Validator BlockId Payload U} {w : ℕ} {L : BlockId}
    {r : ℕ} :
    MahiMahi.certificates V.toRecord w L r = MahiMahi.certificates U w L r ∩ V.ids := by
  ext C
  simp only [MahiMahi.certificates, mem_certificatesAt, BlockRecord.View.toRecord_ids,
    BlockRecord.View.toRecord_block, Finset.mem_inter]
  constructor
  · rintro ⟨hC, hCr, hcar⟩
    refine ⟨⟨V.subset_ids hC, hCr, ?_⟩, hC⟩
    unfold CarriesVotes at hcar ⊢
    refine le_trans hcar (Finset.card_le_card (Finset.image_subset_image ?_))
    intro q hq
    rw [mem_carriedVotes] at hq ⊢
    exact ⟨hq.1, (votes_toRecord (V.complete C hC q hq.1)).mp hq.2⟩
  · rintro ⟨⟨hC, hCr, hcar⟩, hCV⟩
    refine ⟨hCV, hCr, ?_⟩
    unfold CarriesVotes at hcar ⊢
    refine le_trans hcar (Finset.card_le_card (Finset.image_subset_image ?_))
    intro q hq
    rw [mem_carriedVotes] at hq ⊢
    exact ⟨hq.1, (votes_toRecord (V.complete C hCV q hq.1)).mpr hq.2⟩

/-- **SH18d.** The counting lemma on the anchor's history as a record, whose committed candidates
the window's evidence marks: their certificates are the universe's within the history, at a
round the window retains. -/
theorem window_count {wa I : ℕ} {A : BlockId} (hA : A ∈ U.ids) {T : Finset Validator} {r : ℕ}
    (hwa : 5 ≤ wa) (hcard : quorumCard Validator ≤ T.card) (hr : windowBottom U A I ≤ r)
    (hpop3 : PopulatedOn (U.historyView A hA).toRecord T (r + 3))
    (hpopd : PopulatedOn (U.historyView A hA).toRecord T (MahiMahi.decisionRoundAt wa r)) :
    Fintype.card Validator - F.f - F.byzantine.card ≤
      (Finset.univ.filter fun a => (ofAnchor U A I).commits r wa a = true).card := by
  refine le_trans (card_goodAt_of_populated hwa hcard hpop3 hpopd)
    (Finset.card_le_card fun a ha => ?_)
  obtain ⟨L, hLW, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp ha
  change L ∈ history U A at hLW
  rw [BlockRecord.View.toRecord_block] at hLr hLc
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [ofAnchor, decide_eq_true_eq]
  have hLwin : L ∈ windowIds U A I := by
    refine Finset.mem_filter.mpr ⟨hLW, ?_, round_le_of_mem_history hA hLW⟩
    rw [hLr]
    exact hr
  refine ⟨L, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨history_subset_ids hA hLW, hLr⟩, hLc,
    hLwin⟩, ?_⟩
  unfold MahiMahi.DirectCommit at hdc
  rw [certificates_toRecord] at hdc
  refine le_trans hdc (Finset.card_le_card (Finset.image_subset_image ?_))
  intro C hC
  obtain ⟨hCU, hCW⟩ := Finset.mem_inter.mp hC
  refine Finset.mem_inter.mpr ⟨hCU, ?_⟩
  change C ∈ history U A at hCW
  refine Finset.mem_filter.mpr ⟨hCW, ?_, round_le_of_mem_history hA hCW⟩
  rw [(mem_certificatesAt.mp hCU).2.1]
  exact le_trans hr (by unfold MahiMahi.decisionRoundAt; omega)

end Replay

end Steelhead

end LeanDag
