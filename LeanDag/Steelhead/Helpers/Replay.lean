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

open scoped ENNReal

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

/-- The selection answers the current period or a candidate: the fold starts from the current
period and only ever moves to a candidate. -/
theorem select_eq_or_mem (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ) :
    select candidates scores current epsilon = current ∨
      select candidates scores current epsilon ∈ candidates := by
  dsimp only [select]
  split
  · exact List.mem_cons.mp (fold_mem (current :: candidates) candidates scores current current
      (by simp) fun x hx => by simp [hx])
  · exact Or.inl rfl

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [LinearOrder BlockId]

/-- **SH18h.** The failover answers `1`, or the selection's answer, which is the current period or
a candidate. -/
theorem failover_anchorUpdate_range [S : Slots Validator]
    {U : BlockUniverse Validator BlockId Payload} {I : ℕ} (w : ℕ → ℕ) (C : Config Validator)
    (candidates : List ℕ) (epsilon : ℚ) {K j k : ℕ} (A : BlockId) (hK : 1 ≤ K)
    (hc : ∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) (h1 : 1 ≤ k) (hk : k ≤ K) :
    1 ≤ failover U w I (anchorUpdate U I C candidates epsilon) j A k ∧
      failover U w I (anchorUpdate U I C candidates epsilon) j A k ≤ K := by
  unfold failover
  split
  · exact ⟨le_rfl, hK⟩
  · simp only [anchorUpdate, update]
    rcases select_eq_or_mem candidates (score (ofAnchor U A I) C) k epsilon with h | h
    · rw [h]; exact ⟨h1, hk⟩
    · exact hc _ h

/-! ## The evidence -/

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
    Fintype.card Validator - F.f - F.byzantine.card ≤ committedCount (ofAnchor U A I) r wa := by
  unfold committedCount
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

/-- **SH18g.** A quorum of certificates within the window is a quorum of certificates on the DAG,
for a block of the author at the round. -/
theorem commits_sound {A : BlockId} {I r w : ℕ} {a : Validator}
    (h : (ofAnchor U A I).commits r w a = true) :
    ∃ L ∈ blocksAt U r, (U.block L).creator = a ∧ MahiMahi.DirectCommit U w L r := by
  simp only [ofAnchor, decide_eq_true_eq] at h
  obtain ⟨L, hL, hc⟩ := h
  obtain ⟨hLr, hLa, -⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hLr, hLa, ?_⟩
  unfold MahiMahi.DirectCommit
  exact le_trans hc (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-- The window marks committed exactly the authors whose round-`r` block the anchor's history,
read as a record, directly commits: a candidate at a round the window retains lies in the history,
and its certificates within the window are its certificates within the history, whose round the
window retains too. -/
theorem committedCount_eq_card_goodAt {wa I : ℕ} (hwa : 1 ≤ wa) {A : BlockId} (hA : A ∈ U.ids)
    {r : ℕ} (hr : windowBottom U A I ≤ r) :
    committedCount (ofAnchor U A I) r wa =
      (MahiMahi.goodAt (U.historyView A hA).toRecord wa r).card := by
  unfold committedCount
  congr 1
  ext a
  rw [Finset.mem_filter, MahiMahi.mem_goodAt]
  simp only [Finset.mem_univ, true_and, ofAnchor, decide_eq_true_eq,
    BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
  constructor
  · rintro ⟨L, hL, hc⟩
    obtain ⟨hLr, hLa, hLw⟩ := Finset.mem_filter.mp hL
    obtain ⟨-, hLround⟩ := mem_blocksAt.mp hLr
    obtain ⟨hLh, -, -⟩ := Finset.mem_filter.mp hLw
    refine ⟨L, hLh, hLround, hLa, ?_⟩
    unfold MahiMahi.DirectCommit
    rw [certificates_toRecord]
    refine le_trans hc (Finset.card_le_card (Finset.image_subset_image ?_))
    intro C hC
    obtain ⟨hCU, hCw⟩ := Finset.mem_inter.mp hC
    exact Finset.mem_inter.mpr ⟨hCU, (Finset.mem_filter.mp hCw).1⟩
  · rintro ⟨L, hLh, hLround, hLa, hdc⟩
    change L ∈ history U A at hLh
    have hLw : L ∈ windowIds U A I :=
      Finset.mem_filter.mpr ⟨hLh, by rw [hLround]; exact hr, round_le_of_mem_history hA hLh⟩
    refine ⟨L, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨history_subset_ids hA hLh, hLround⟩, hLa,
      hLw⟩, ?_⟩
    unfold MahiMahi.DirectCommit at hdc
    rw [certificates_toRecord] at hdc
    refine le_trans hdc (Finset.card_le_card (Finset.image_subset_image ?_))
    intro C hC
    obtain ⟨hCU, hCh⟩ := Finset.mem_inter.mp hC
    change C ∈ history U A at hCh
    refine Finset.mem_inter.mpr
      ⟨hCU, Finset.mem_filter.mpr ⟨hCh, ?_, round_le_of_mem_history hA hCh⟩⟩
    rw [(mem_certificatesAt.mp hCU).2.1]
    exact le_trans hr (by unfold MahiMahi.decisionRoundAt; omega)

/-- **SH18i.** The count, over `n`, is the uniform coin's measure of the committed set. -/
theorem commitWeight_eq_commitProb {wa I : ℕ} (hwa : 1 ≤ wa) {A : BlockId} (hA : A ∈ U.ids)
    {r : ℕ} (hr : windowBottom U A I ≤ r) :
    (committedCount (ofAnchor U A I) r wa : ℝ≥0∞) / Fintype.card Validator =
      commitProb (U.historyView A hA).toRecord wa r := by
  rw [committedCount_eq_card_goodAt hwa hA hr, commitProb_eq]

/-! ## The passes -/

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- A round of the window lies between its bottom and its top. -/
theorem mem_rounds {E : Evidence Validator} {j : ℕ} :
    j ∈ rounds E ↔ E.bottom ≤ j ∧ j ≤ E.top := by
  unfold rounds
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨j - E.bottom, by omega, by omega⟩

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- The probes' successes are at most the probes. -/
theorem probeRate_fst_le (E : Evidence Validator) (C : Config Validator) (period : ℕ) :
    (probeRate E C period).1 ≤ (probeRate E C period).2 :=
  List.length_filter_le _ _

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- **SH18j.** The first multiple of the canary spacing at or above the window's bottom and the
next one both lie in the probe range, and the period, coprime to the spacing, divides at most one
of them. -/
theorem probe_exists {E : Evidence Validator} {C : Config Validator} {period : ℕ}
    (hcop : Nat.Coprime C.canary period) (hp : 2 ≤ period) (hws : 1 ≤ C.ws)
    (hwin : E.bottom + 2 * C.canary + C.ws ≤ E.top + 2) :
    0 < (probeRate E C period).2 := by
  have hc : 1 ≤ C.canary := by
    rcases Nat.eq_zero_or_pos C.canary with h | h
    · rw [h, Nat.coprime_zero_left] at hcop; omega
    · exact h
  -- the first multiple of the canary at or above the bottom
  set q := (E.bottom + C.canary - 1) / C.canary with hq
  have hdm := Nat.div_add_mod (E.bottom + C.canary - 1) C.canary
  have hml := Nat.mod_lt (E.bottom + C.canary - 1) (by omega : 0 < C.canary)
  rw [← hq] at hdm
  have hlo : E.bottom ≤ C.canary * q := by omega
  have hhi : C.canary * q < E.bottom + C.canary := by omega
  -- it or the next multiple is a probe
  have key : ∃ r, E.bottom ≤ r ∧ r + C.ws - 1 ≤ E.top ∧ r % C.canary = 0 ∧ r % period ≠ 0 := by
    by_cases h₁ : C.canary * q % period = 0
    · refine ⟨C.canary * q + C.canary, by omega, by omega, ?_, ?_⟩
      · rw [← Nat.mul_succ]; exact Nat.mul_mod_right _ _
      · intro h₂
        have hd : period ∣ C.canary :=
          (Nat.dvd_add_right (Nat.dvd_of_mod_eq_zero h₁)).mp (Nat.dvd_of_mod_eq_zero h₂)
        have := Nat.Coprime.eq_one_of_dvd hcop.symm hd
        omega
    · exact ⟨C.canary * q, hlo, by omega, Nat.mul_mod_right _ _, h₁⟩
  obtain ⟨r, hr₁, hr₂, hr₃, hr₄⟩ := key
  refine List.length_pos_of_mem (a := r) ?_
  rw [List.mem_filter, mem_rounds]
  refine ⟨⟨hr₁, by omega⟩, ?_⟩
  simp [hr₂, hr₃, hr₄]

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- A mean over a nonempty set is at least a common lower bound of its terms. -/
theorem le_mean {α : Type} {s : Finset α} (hs : s.Nonempty) {g : α → ℚ} {lo : ℚ}
    (h : ∀ v ∈ s, lo ≤ g v) : lo ≤ (∑ v ∈ s, g v) / s.card := by
  rw [le_div_iff₀ (by exact_mod_cast hs.card_pos)]
  calc lo * s.card = ∑ _v ∈ s, lo := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ v ∈ s, g v := Finset.sum_le_sum h

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- A mean over a nonempty set is at most a common upper bound of its terms. -/
theorem mean_le {α : Type} {s : Finset α} (hs : s.Nonempty) {g : α → ℚ} {hi : ℚ}
    (h : ∀ v ∈ s, g v ≤ hi) : (∑ v ∈ s, g v) / s.card ≤ hi := by
  rw [div_le_iff₀ (by exact_mod_cast hs.card_pos)]
  calc ∑ v ∈ s, g v ≤ ∑ _v ∈ s, hi := Finset.sum_le_sum h
    _ = hi * s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- Means are monotone in their terms. -/
theorem mean_le_mean {α : Type} {s : Finset α} {g g' : α → ℚ} (h : ∀ v ∈ s, g v ≤ g' v) :
    (∑ v ∈ s, g v) / s.card ≤ (∑ v ∈ s, g' v) / s.card :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

/-- The bounds a timing carries: its decision at or above a round, its commit at or above its
decision, both at or below the window's top. -/
def Bounded (E : Evidence Validator) (r : ℕ) (t : Timing) : Prop :=
  (r : ℚ) ≤ t.decision ∧ t.decision ≤ t.commit ∧ t.commit ≤ E.top

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- The clipped timing is bounded at every round up to the top. -/
theorem bounded_clipped {E : Evidence Validator} {r : ℕ} (hr : r ≤ E.top) :
    Bounded E r (clipped E.top) :=
  ⟨by simp only [clipped]; exact_mod_cast hr, le_rfl, le_rfl⟩

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- A bound at a round is a bound at every round below it. -/
theorem Bounded.mono {E : Evidence Validator} {r j : ℕ} {t : Timing} (hrj : r ≤ j)
    (h : Bounded E j t) : Bounded E r t :=
  ⟨le_trans (by exact_mod_cast hrj) h.1, h.2.1, h.2.2⟩

omit [Fintype Validator] [DecidableEq Validator] F [LinearOrder BlockId] in
/-- A candidate's timing is bounded when its anchor's is and its decision round lies in the
window. -/
theorem bounded_candidateTiming {E : Evidence Validator} {r wave : ℕ} {v : Validator}
    {anchor : Timing} (hwave : 2 ≤ wave) (hdec : r + wave - 1 ≤ E.top)
    (ha : Bounded E r anchor) : Bounded E r (candidateTiming E r wave v anchor) := by
  have hw : (2 : ℚ) ≤ wave := by exact_mod_cast hwave
  have htop : (r : ℚ) + wave - 1 ≤ E.top := by
    have h1 : ((r + wave - 1 : ℕ) : ℚ) ≤ E.top := by exact_mod_cast hdec
    rwa [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at h1
  unfold candidateTiming
  split_ifs with h1 h2 h3
  · refine ⟨?_, ?_, le_rfl⟩ <;> dsimp only <;> linarith
  · refine ⟨?_, le_rfl, ?_⟩ <;> dsimp only <;> linarith
  · exact ⟨ha.1, ha.2.1, ha.2.2⟩
  · exact ⟨ha.1, le_trans ha.2.1 ha.2.2, le_rfl⟩

/-- A round's timing is bounded when the timings of the rounds above it are, and the probes'
successes are at most the probes. -/
theorem bounded_roundTiming {E : Evidence Validator} {C : Config Validator} {period : ℕ}
    {probes : ℕ × ℕ} (hs : probes.1 ≤ probes.2) (hws : 2 ≤ C.ws) (hwa : 2 ≤ C.wa)
    {higher : ℕ → Timing} {r : ℕ} (hr : r ≤ E.top)
    (hh : ∀ j, r < j → j ≤ E.top → Bounded E r (higher j)) :
    Bounded E r (roundTiming E C period probes higher r) := by
  unfold roundTiming
  dsimp only
  have hwave : 2 ≤ if r % period = 0 then C.wa else C.ws := by split_ifs <;> assumption
  generalize (if r % period = 0 then C.wa else C.ws) = wave at hwave ⊢
  have hne : (if wave = C.ws then ({C.known r} : Finset Validator) else Finset.univ).Nonempty := by
    split_ifs
    · exact Finset.singleton_nonempty _
    · exact Finset.univ_nonempty
  generalize (if wave = C.ws then ({C.known r} : Finset Validator) else Finset.univ) = authors
    at hne ⊢
  split_ifs with hclip hprobe
  · exact bounded_clipped hr
  · -- the unprobed synchronous slot: a mean of two rounds inside the window
    obtain ⟨hwws, -, ht⟩ := hprobe
    subst hwws
    have ht' : (0 : ℚ) < probes.2 := by exact_mod_cast ht
    have hs' : (probes.1 : ℚ) ≤ probes.2 := by exact_mod_cast hs
    have hs0 : (0 : ℚ) ≤ probes.1 := Nat.cast_nonneg _
    have ha1 : (r : ℚ) ≤ ((r + C.ws - 1 : ℕ) : ℚ) := by
      exact_mod_cast (show r ≤ r + C.ws - 1 by omega)
    have ha2 : (r : ℚ) ≤ ((r + C.ws - 2 : ℕ) : ℚ) := by
      exact_mod_cast (show r ≤ r + C.ws - 2 by omega)
    have hb1 : ((r + C.ws - 1 : ℕ) : ℚ) ≤ E.top := by
      exact_mod_cast (show r + C.ws - 1 ≤ E.top by omega)
    have hb2 : ((r + C.ws - 2 : ℕ) : ℚ) ≤ E.top := by
      exact_mod_cast (show r + C.ws - 2 ≤ E.top by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [le_div_iff₀ ht']
      nlinarith
    · exact div_le_div_of_nonneg_right (by nlinarith) ht'.le
    · rw [div_le_iff₀ ht']
      nlinarith
  · -- the mean over the candidates, each bounded by its anchor's bound
    have hanchor : Bounded E r ((((rounds E).find? fun j =>
        r + wave ≤ j && decide ((higher j).commit < E.top)).map higher).getD (clipped E.top)) := by
      cases hfind : (rounds E).find? fun j =>
          r + wave ≤ j && decide ((higher j).commit < E.top) with
      | none => exact bounded_clipped hr
      | some j =>
        have hj := mem_rounds.mp (List.mem_of_find?_eq_some hfind)
        have hp := List.find?_some hfind
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        exact hh j (by omega) hj.2
    exact ⟨le_mean hne fun v _ => (bounded_candidateTiming hwave (by omega) hanchor).1,
      mean_le_mean fun v _ => (bounded_candidateTiming hwave (by omega) hanchor).2.1,
      mean_le hne fun v _ => (bounded_candidateTiming hwave (by omega) hanchor).2.2⟩

/-- **SH18e.** Every round's timing is bounded, from the top of the window down. -/
theorem bounded_timingAt {E : Evidence Validator} {C : Config Validator} {period : ℕ}
    {probes : ℕ × ℕ} (hs : probes.1 ≤ probes.2) (hws : 2 ≤ C.ws) (hwa : 2 ≤ C.wa) :
    ∀ r, r ≤ E.top → Bounded E r (timingAt E C period probes r) := by
  -- one step: the round's timing from the timings above it
  have step : ∀ r, r ≤ E.top →
      (∀ j, r < j → j ≤ E.top → Bounded E j (timingAt E C period probes j)) →
      Bounded E r (timingAt E C period probes r) := by
    intro r hr hh
    rw [timingAt]
    split_ifs with hin
    · refine bounded_roundTiming hs hws hwa hr fun j hj hjt => ?_
      rw [dif_pos hj]
      exact (hh j hj hjt).mono hj.le
    · exact bounded_clipped hr
  suffices H : ∀ n r, E.top - r ≤ n → r ≤ E.top → Bounded E r (timingAt E C period probes r) from
    fun r hr => H _ r le_rfl hr
  intro n
  induction n with
  | zero => exact fun r hn hr => step r hr fun j hj hjt => absurd hjt (by omega)
  | succ n ih => exact fun r hn hr => step r hr fun j hj hjt => ih j (by omega) hjt

omit F in
/-- At an asynchronous round every candidate is scored by the rule's own case, a committed one at
the decision round and every other at or below the window's top, when the timings above the round
are bounded. -/
theorem roundTiming_async_commit_le {E : Evidence Validator} {C : Config Validator} {period : ℕ}
    {probes : ℕ × ℕ} {higher : ℕ → Timing} {r : ℕ} (hws : 2 ≤ C.ws) (hlt : C.ws < C.wa)
    (hr : r % period = 0) (hdec : r + C.wa - 1 ≤ E.top)
    (hh : ∀ j, r < j → j ≤ E.top → Bounded E r (higher j))
    (hcons : ∀ a, E.commits r C.wa a = true → E.skips r C.wa a = false) :
    (roundTiming E C period probes higher r).commit ≤
      ((committedCount E r C.wa * (r + C.wa - 1) +
        (Fintype.card Validator - committedCount E r C.wa) * E.top : ℕ) : ℚ) /
        Fintype.card Validator := by
  have hwa : 2 ≤ C.wa := by omega
  unfold roundTiming
  dsimp only
  rw [if_pos hr, if_neg (by omega), if_neg (fun h => absurd h.1 (by omega)), if_neg (by omega)]
  dsimp only
  -- the anchor is bounded, so every uncommitted candidate commits at or below the top
  have hanchor : Bounded E r ((((rounds E).find? fun j =>
      r + C.wa ≤ j && decide ((higher j).commit < E.top)).map higher).getD (clipped E.top)) := by
    cases hfind : (rounds E).find? fun j => r + C.wa ≤ j && decide ((higher j).commit < E.top) with
    | none => exact bounded_clipped (by omega)
    | some j =>
      have hj := mem_rounds.mp (List.mem_of_find?_eq_some hfind)
      have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact hh j (by omega) hj.2
  have hcast : ((r + C.wa - 1 : ℕ) : ℚ) = (r : ℚ) + C.wa - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  -- each candidate's commit is at most its case's value
  refine le_trans (mean_le_mean (g' := fun v =>
    if E.commits r C.wa v = true then ((r + C.wa - 1 : ℕ) : ℚ) else (E.top : ℚ))
    fun v _ => ?_) (le_of_eq ?_)
  · by_cases hc : E.commits r C.wa v = true
    · rw [if_pos hc]
      unfold candidateTiming
      rw [if_neg (by rw [hcons v hc]; decide), if_pos hc, hcast]
    · rw [if_neg hc]
      exact (bounded_candidateTiming hwa hdec hanchor).2.2
  · rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.card_univ]
    have hle : committedCount E r C.wa ≤ Fintype.card Validator := Finset.card_filter_le _ _
    have hneg : (Finset.univ.filter fun v => ¬ E.commits r C.wa v = true).card =
        Fintype.card Validator - committedCount E r C.wa := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset Validator)) (fun v => E.commits r C.wa v = true)
      rw [Finset.card_univ] at this
      unfold committedCount
      omega
    rw [hneg]
    unfold committedCount
    unfold committedCount at hle
    push_cast [Nat.cast_sub hle, nsmul_eq_mul]
    rfl

/-- **SH18f.** Pass one at an asynchronous round of the window, the timings above it bounded by
SH18e. -/
theorem async_term_bound {E : Evidence Validator} {C : Config Validator} {period r : ℕ}
    (hws : 2 ≤ C.ws) (hlt : C.ws < C.wa) (hb : E.bottom ≤ r) (hr : r % period = 0)
    (hdec : r + C.wa - 1 ≤ E.top)
    (hcons : ∀ a, E.commits r C.wa a = true → E.skips r C.wa a = false) :
    (timingAt E C period (probeRate E C period) r).commit ≤
      ((committedCount E r C.wa * (r + C.wa - 1) +
        (Fintype.card Validator - committedCount E r C.wa) * E.top : ℕ) : ℚ) /
        Fintype.card Validator := by
  have hwa : 2 ≤ C.wa := by omega
  have hbound := bounded_timingAt (E := E) (period := period) (probeRate_fst_le E C period) hws hwa
  rw [timingAt, dif_pos ⟨hb, by omega⟩]
  refine roundTiming_async_commit_le hws hlt hr hdec (fun j hj hjt => ?_) hcons
  rw [dif_pos hj]
  exact (hbound j hjt).mono hj.le

end Replay

end Steelhead

end LeanDag
